/-
  Elaborator & Compiler

  Translates Lean expressions into hardware netlists using metaprogramming.
  This bridges the gap between high-level Signal code and low-level IR.
-/

import Sparkle.Compiler.ExprDecEq
import Lean
import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.IR.Specialize
import Sparkle.Data.BitPack
import Sparkle.Backend.Verilog
import Sparkle.Backend.CSim
import Sparkle.Backend.CudaSim
import Sparkle.Backend.CudaIntra
import Sparkle.IR.Optimize
import Sparkle.IR.ZeroWidth
import Sparkle.IR.RegDedup
import Sparkle.IR.OptCheck
import Sparkle.IR.RefineCheck
import Sparkle.IR.Machine
import Sparkle.IR.MachineInstG
import Sparkle.IR.ModuleNameCheck
import Sparkle.Compiler.DRC
import Sparkle.Compiler.InlineAttr
import Sparkle.Core.Signal
import Sparkle.Core.Vector
import Sparkle.Core.CircuitMonad
import Sparkle.Compiler.MachRawSurface
import Sparkle.Compiler.MachTupleIn
import Sparkle.Compiler.MachSignOps
import Sparkle.Display.Mime

namespace Sparkle.Compiler.Elab

open Lean Lean.Elab Lean.Elab.Command Lean.Meta
open Sparkle.IR.Builder
open Sparkle.IR.AST (Operator Port Module Expr Stmt)
open Sparkle.IR.Type
open Sparkle.Backend.Verilog

initialize registerTraceClass `sparkle.compiler

instance : Inhabited Sparkle.IR.AST.Port := ⟨{ name := "default", ty := .bit }⟩


/-- Compiler state tracking variable mappings and context -/
structure CompilerState where
  varMap : List (FVarId × String) := []  -- Map Lean variables to wire names
  dimVarMap : List (FVarId × DimExpr) := [] -- Retained Nat binders to symbolic dimensions
  clockWire : Option String := none       -- Name of clock wire (if any)
  symbolicMode : Bool := false -- Fail closed even when no binder was retained
  resetWire : Option String := none       -- Name of reset wire (if any)
  -- Expression-keyed memoization for `translateExprToWire`.
  -- When the ρ-generic synthesis splits a multi-output return
  -- into N leaves, each leaf's expression shares the same
  -- sub-structure (the body's `Signal.loop` chain), so caching
  -- by Expr key keeps the cost O(body) instead of O(N × body).
  -- Optional so `CompilerState.default` (used by the test
  -- harness via `{}` literals) stays trivially constructible;
  -- `synthesizeCombinational` populates it before the first
  -- translate call.
  -- Content-addressed expression cache.
  -- Key type: `Lean.ExprStructEq` — Lean stdlib's wrapper that
  -- uses `Expr.equal` (structural equality on the AST,
  -- inclusive of binder names) for BEq, and `Expr.hash` for
  -- Hashable.  Both are pure DAG-content fns, so two
  -- structurally-identical expressions emitted by separate
  -- elaboration paths (e.g. `kvHw a b c d e` re-elaborated
  -- once per register-write) collide on the same key
  -- regardless of pointer identity.
  --
  -- The original cache used `Std.HashMap Lean.Expr String`,
  -- which via `Expr.eqv` / `BEq Expr` was effectively pointer-
  -- equal cache lookup with fast-path-only structural fallback.
  -- That cache hit < 10% on FSM-shape circuits because Lean's
  -- elaborator routinely re-elaborates the same sub-tree into
  -- fresh Expr objects with identical hash but distinct
  -- pointer identity.  Switching to `ExprStructMap` collapses
  -- those duplicates onto the same wire.
  exprCache : Option (IO.Ref (Lean.ExprStructMap String)) := none

/-- Compiler monad: combines CircuitM builder with MetaM -/
abbrev CompilerM := ReaderT CompilerState (StateT CircuitState MetaM)

namespace CompilerM

/-- Get the current compiler state (from ReaderT) -/
def getCompilerState : CompilerM CompilerState :=
  read

end CompilerM

namespace CompilerM

/-- Lookup a variable mapping.  Consults the reader-scoped
    `varMap` first, then the synthesis-local builder table. Later return
    leaves can revisit loop binders after their reader scope has ended. -/
def lookupVar (fvarId : FVarId) : CompilerM (Option String) :=
  fun context s => pure (CircuitM.lookupSourceBinding
    (context.varMap.lookup fvarId) fvarId.name s)

/-- Persistent within one synthesis, automatically isolated from nested ones. -/
def bindSourceVariable (fvarId : FVarId) (wire : String) : CompilerM Unit :=
  fun _ s => pure (CircuitM.bindSourceVariable fvarId.name wire s)

/-- Lookup a retained symbolic dimension variable. -/
def lookupDimVar (fvarId : FVarId) : CompilerM (Option DimExpr) := do
  let s ← getCompilerState
  return s.dimVarMap.lookup fvarId

/-- Execute an action with a retained Nat binder in scope. -/
def withDimVarMapping {α : Type} (fvarId : FVarId) (dimension : DimExpr)
    (k : CompilerM α) : CompilerM α := do
  let oldState ← getCompilerState
  let newState := { oldState with dimVarMap := (fvarId, dimension) :: oldState.dimVarMap }
  withReader (fun _ => newState) k

/-- Execute an action with an additional variable mapping in scope -/
def withVarMapping {α : Type} (fvarId : FVarId) (wireName : String) (k : CompilerM α) : CompilerM α := do
  let oldState ← getCompilerState
  let newState := { oldState with varMap := (fvarId, wireName) :: oldState.varMap }
  withReader (fun _ => newState) k

/-- Execute an action with a new local declaration in MetaM scope -/
def withLocalDecl {α : Type} (name : Name) (type : Lean.Expr) (k : Lean.Expr → CompilerM α) : CompilerM α := do
  let ctx ← read
  let s ← get
  let (res, newS) ← liftMetaM <| withLocalDeclD name type fun fvar => do
    (k fvar ctx).run s
  set newS
  return res

/-- Execute an action with a new let declaration in MetaM scope (for logic values) -/
def withLetDecl {α : Type} (name : Name) (type : Lean.Expr) (value : Lean.Expr) (k : Lean.Expr → CompilerM α) : CompilerM α := do
  let ctx ← read
  let s ← get
  let (res, newS) ← liftMetaM <| Lean.Meta.withLetDecl name type value fun fvar => do
    (k fvar ctx).run s
  set newS
  return res

/-- Lift MetaM into CompilerM -/
def liftMetaM {α : Type} (m : MetaM α) : CompilerM α :=
  liftM m

end CompilerM

/-- Wire-width cache: `wireName → bit width`.  Populated by
    `makeWire`, `addInput`, `addOutput`; consumed by `getWireWidth`.
    Avoids the O(n) linear scan that dominated runtime on FSM-
    shape circuits (handleTupleProjections / handleMux call
    getWireWidth in their hot loops, turning a ~5000-wire design
    into an O(n²) walk). -/
private initialize sparkleWireWidthCache :
    IO.Ref (Std.HashMap String Nat) ← IO.mkRef {}

namespace CompilerM

/-- Lift CircuitM operations by modifying the circuit state -/
private def legacyCacheWidth? : HWType → Option Nat
  | .bitVector width => some width
  | .bit => some 1
  | .array _ _ => some 8
  | .bitVectorDim _ => none

def makeWire (hint : String) (ty : HWType) (named : Bool := false) : CompilerM String := do
  let cs ← get
  let (name, cs') := CircuitM.makeWire hint ty named cs
  set cs'
  -- Populate the wire-width cache so subsequent `getWireWidth name`
  -- is O(1) instead of an O(n) module.wires scan.
  if let some width := legacyCacheWidth? ty then
    liftMetaM (sparkleWireWidthCache.modify (·.insert name width))
  return name

def freshName (hint : String) (named : Bool := false) : CompilerM String := do
  let cs ← get
  let (name, cs') := CircuitM.freshName hint named cs
  set cs'
  return name

def emitAssign (lhs : String) (rhs : Sparkle.IR.AST.Expr) : CompilerM Unit := do
  let cs ← get
  let ((), cs') := CircuitM.emitAssign lhs rhs cs
  set cs'

def addInput (name : String) (ty : HWType) : CompilerM Unit := do
  let cs ← get
  let ((), cs') := CircuitM.addInput name ty cs
  set cs'
  if let some width := legacyCacheWidth? ty then
    liftMetaM (sparkleWireWidthCache.modify (·.insert name width))


def addOutput (name : String) (ty : HWType) : CompilerM Unit := do
  let cs ← get
  let ((), cs') := CircuitM.addOutput name ty cs
  set cs'
  if let some width := legacyCacheWidth? ty then
    liftMetaM (sparkleWireWidthCache.modify (·.insert name width))

/-- Look up the HW width of a wire by name (from wires, inputs, or outputs) -/
def getWireWidth (wireName : String) : CompilerM Nat := do
  -- Hot path: O(1) lookup via the per-synth wire-width cache,
  -- populated by `makeWire` and `addInput` / `addOutput`.  The
  -- old implementation scanned `cs.module.wires ++ inputs ++
  -- outputs` linearly, which is O(n) per call and O(n^2)
  -- overall on FSM-shape circuits with thousands of wires.
  let cache ← liftMetaM (sparkleWireWidthCache.get : IO _)
  match cache.get? wireName with
  | some w => return w
  | none =>
    -- Fallback: linear scan of the module's ports.  This only
    -- happens for wires that bypass the cache-populating helpers
    -- (e.g. external bindings, or `clk`/`rst` ports added without
    -- going through our IO.Ref-tracked path).
    let cs ← get
    let allPorts := cs.module.wires ++ cs.module.inputs ++ cs.module.outputs
    match allPorts.find? (fun p => p.name == wireName) with
    | some p =>
      let w ← match legacyCacheWidth? p.ty with
        | some width => pure width
        | none => liftMetaM $ throwError
            s!"Wire '{wireName}' has a symbolic width; this operation requires a concrete width"
      liftMetaM (sparkleWireWidthCache.modify (·.insert wireName w))
      return w
    | none => return 8

def emitRegister (hint : String) (clk : String) (rst : String)
    (input : Sparkle.IR.AST.Expr) (initVal : Nat) (ty : HWType)
    (named : Bool := false)
    (resetKind : Sparkle.IR.Type.ResetKind := .asynchronous)
    : CompilerM String := do
  let cs ← get
  let (name, cs') := CircuitM.emitRegister hint clk rst input initVal ty
                       (named := named) (resetKind := resetKind) cs
  set cs'
  -- Register the output wire width so downstream `getWireWidth`
  -- lookups hit the cache instead of falling back to a linear
  -- scan over `module.wires` (which dominates wall time when
  -- the wire list grows into the thousands — Issue #67).
  if let some width := legacyCacheWidth? ty then
    liftMetaM (sparkleWireWidthCache.modify (·.insert name width))
  return name

/-- Statement-only register emission for a pre-allocated output wire. -/
def emitRegisterStmt (out clk rst : String) (input : Sparkle.IR.AST.Expr) (initVal : Nat)
    (resetKind : Sparkle.IR.Type.ResetKind := .asynchronous) : CompilerM Unit := do
  let cs ← get
  let ((), cs') := CircuitM.emitRegisterStmt out clk rst input initVal resetKind cs
  set cs'

/-- Look up a wire width without forcing retained dimensions to concrete Nats. -/
def getWireWidthDim (wireName : String) : CompilerM DimExpr := do
  let cs ← get
  let allPorts := cs.module.wires ++ cs.module.inputs ++ cs.module.outputs
  match allPorts.find? (fun p => p.name == wireName) with
  | some port => return port.ty.bitWidthDim
  | none => liftMetaM $ throwError s!"Cannot determine hardware width for wire '{wireName}'"


def emitMemory (hint : String) (addrWidth dataWidth : Nat) (clk : String)
    (writeAddr writeData writeEnable readAddr : Sparkle.IR.AST.Expr) (named : Bool := false) : CompilerM String := do
  let cs ← get
  let (name, cs') := CircuitM.emitMemory hint addrWidth dataWidth clk writeAddr writeData writeEnable readAddr named cs
  set cs'
  liftMetaM (sparkleWireWidthCache.modify (·.insert name dataWidth))
  return name

def emitMemoryComboRead (hint : String) (addrWidth dataWidth : Nat) (clk : String)
    (writeAddr writeData writeEnable readAddr : Sparkle.IR.AST.Expr) (named : Bool := false) : CompilerM String := do
  let cs ← get
  let (name, cs') := CircuitM.emitMemoryComboRead hint addrWidth dataWidth clk writeAddr writeData writeEnable readAddr named cs
  set cs'
  liftMetaM (sparkleWireWidthCache.modify (·.insert name dataWidth))
  return name

def emitInstance (moduleName : String) (instName : String) (connections : List (String × Sparkle.IR.AST.Expr)) : CompilerM Unit := do
  let cs ← get
  let ((), cs') := CircuitM.emitInstance moduleName instName connections cs
  set cs'

def addModuleToDesign (m : Sparkle.IR.AST.Module) : CompilerM Unit := do
  let cs ← get
  let ((), cs') := CircuitM.addModuleToDesign m cs
  set cs'

/-- Add a retained parameter, rejecting duplicate module declarations. -/
def addParameter (name : String) (defaultValue : Nat) : CompilerM Unit := do
  let cs ← get
  if cs.module.parameters.any (fun parameter => parameter.name == name) then
    liftMetaM $ throwError s!"Duplicate retained hardware parameter '{name}'"
  let ((), cs') := CircuitM.addParameter name defaultValue cs
  set cs'

end CompilerM

/-- Library instances the Signal operator intercept may lower directly, with the
    operand kinds each one fixes: `(method, instance, lhsIsSignal, rhsIsSignal)`.

    The source meaning of `a + b` is decided by the INSTANCE, not by the method
    name. Dispatching on `HAdd.hAdd` alone compiled a user instance whose `+` is
    subtraction as an adder: source 3 + 10 = 249, emitted RTL 13 (measured
    2026-09-25). An application whose instance is not listed here is left to
    the general unfolding path, which lowers the instance's actual body. -/
def canonicalSignalBinInsts : List (Name × Name × Bool × Bool) :=
  [ (``HAdd.hAdd, ``Sparkle.Core.Signal.instHAddSignalBitVec, true, true),
    (``HAdd.hAdd, ``Sparkle.Core.Signal.instHAddSignalBitVec_1, true, false),
    (``HAdd.hAdd, ``Sparkle.Core.Signal.instHAddBitVecSignal, false, true),
    (``HSub.hSub, ``Sparkle.Core.Signal.instHSubSignalBitVec, true, true),
    (``HSub.hSub, ``Sparkle.Core.Signal.instHSubSignalBitVec_1, true, false),
    (``HSub.hSub, ``Sparkle.Core.Signal.instHSubBitVecSignal, false, true),
    (``HMul.hMul, ``Sparkle.Core.Signal.instHMulSignalBitVec, true, true),
    (``HMul.hMul, ``Sparkle.Core.Signal.instHMulSignalBitVec_1, true, false),
    (``HMul.hMul, ``Sparkle.Core.Signal.instHMulBitVecSignal, false, true),
    (``HAnd.hAnd, ``Sparkle.Core.Signal.instHAndSignalBitVec, true, true),
    (``HAnd.hAnd, ``Sparkle.Core.Signal.instHAndSignalBitVec_1, true, false),
    (``HAnd.hAnd, ``Sparkle.Core.Signal.instHAndBitVecSignal, false, true),
    (``HAnd.hAnd, ``Sparkle.Core.Signal.instHAndSignalBool, true, true),
    (``HOr.hOr, ``Sparkle.Core.Signal.instHOrSignalBitVec, true, true),
    (``HOr.hOr, ``Sparkle.Core.Signal.instHOrSignalBitVec_1, true, false),
    (``HOr.hOr, ``Sparkle.Core.Signal.instHOrBitVecSignal, false, true),
    (``HOr.hOr, ``Sparkle.Core.Signal.instHOrSignalBool, true, true),
    (``HXor.hXor, ``Sparkle.Core.Signal.instHXorSignalBitVec, true, true),
    (``HXor.hXor, ``Sparkle.Core.Signal.instHXorSignalBitVec_1, true, false),
    (``HXor.hXor, ``Sparkle.Core.Signal.instHXorBitVecSignal, false, true),
    (``HXor.hXor, ``Sparkle.Core.Signal.instHXorSignalBool, true, true),
    (``HShiftLeft.hShiftLeft, ``Sparkle.Core.Signal.instHShiftLeftSignalBitVec_1, true, true),
    (``HShiftLeft.hShiftLeft, ``Sparkle.Core.Signal.instHShiftLeftSignalBitVec, true, false),
    (``HShiftLeft.hShiftLeft, ``Sparkle.Core.Signal.instHShiftLeftBitVecSignal, false, true),
    (``HShiftRight.hShiftRight, ``Sparkle.Core.Signal.instHShiftRightSignalBitVec_1, true, true),
    (``HShiftRight.hShiftRight, ``Sparkle.Core.Signal.instHShiftRightSignalBitVec, true, false),
    (``HShiftRight.hShiftRight, ``Sparkle.Core.Signal.instHShiftRightBitVecSignal, false, true),
    (``HAppend.hAppend, ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat, true, true),
    (``HAppend.hAppend, ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat_1, true, false),
    (``HAppend.hAppend, ``Sparkle.Core.Signal.instHAppendBitVecSignalHAddNat, false, true) ]

/-- The operand kinds of a canonical Signal operator application, read from its
    instance argument (index `size - 3` of `method α β γ inst a b`). `none` when
    the instance is not a listed library instance. Pure: no MetaM oracle. -/
def canonicalSignalBinKinds (method : Name) (args : Array Lean.Expr) : Option (Bool × Bool) :=
  if args.size < 3 then none else
  match args[args.size - 3]!.getAppFn with
  | .const inst _ =>
    (canonicalSignalBinInsts.find? fun (m, i, _, _) => m == method && i == inst).map
      fun (_, _, s1, s2) => (s1, s2)
  | _ => none

/-- Core (scalar) instances the primitive registry may lower by method name:
    `(method, outerInstance, innerInstance?)`. Generic core wrappers such as
    `instHAdd` take the real instance as their last argument, so a user
    `Add (BitVec n)` arrives as `instHAdd _ userAdd` and must be checked there.
    `instBEqOfDecidableEq` needs no inner check: any `DecidableEq` instance
    decides propositional equality, because it carries the proof. -/
def canonicalScalarMethodInsts : List (Name × Name × Option Name) :=
  [ (``HAdd.hAdd, ``instHAdd, some ``BitVec.instAdd),
    (``HSub.hSub, ``instHSub, some ``BitVec.instSub),
    (``HMul.hMul, ``instHMul, some ``BitVec.instMul),
    (``HAnd.hAnd, ``instHAndOfAndOp, some ``BitVec.instAndOp),
    (``HOr.hOr, ``instHOrOfOrOp, some ``BitVec.instOrOp),
    (``HXor.hXor, ``instHXorOfXorOp, some ``BitVec.instXorOp),
    (``HShiftLeft.hShiftLeft, ``BitVec.instHShiftLeft, none),
    (``HShiftLeft.hShiftLeft, ``BitVec.instHShiftLeftNat, none),
    (``HShiftRight.hShiftRight, ``BitVec.instHShiftRight, none),
    (``HShiftRight.hShiftRight, ``BitVec.instHShiftRightNat, none),
    (``HAppend.hAppend, ``BitVec.instHAppendHAddNat, none),
    (``Neg.neg, ``BitVec.instNeg, none),
    (``Complement.complement, ``BitVec.instComplement, none),
    -- Signal-level unary instances (library): `(!·) <$> a`, `(~~~·) <$> a`, `(-·) <$> a`
    (``Complement.complement, ``Sparkle.Core.Signal.instComplementSignalBool, none),
    (``Complement.complement, ``Sparkle.Core.Signal.instComplementSignalBitVec, none),
    (``Neg.neg, ``Sparkle.Core.Signal.instNegSignalBitVec, none),
    (``BEq.beq, ``instBEqOfDecidableEq, none),
    (``LT.lt, ``instLTBitVec, none),
    (``LE.le, ``instLEBitVec, none) ]

/-- Typeclass METHODS in the primitive registry: their meaning depends on the
    instance, so they may only be lowered by name when the instance is canonical.
    Concrete functions (`BitVec.add`, `Bool.and`, ...) are unaffected. -/
def overloadedPrimitiveMethods : List Name :=
  [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HAnd.hAnd, ``HOr.hOr, ``HXor.hXor,
   ``HShiftLeft.hShiftLeft, ``HShiftRight.hShiftRight, ``ShiftLeft.shiftLeft,
   ``ShiftRight.shiftRight, ``HAppend.hAppend, ``Neg.neg, ``Complement.complement,
   ``BEq.beq, ``LT.lt, ``LE.le]

/-- Is this application of an overloaded method using an instance whose meaning
    the IR operator matches? Pure; reads only the instance argument. Unknown
    methods and unlisted instances answer `false`, so the caller falls back to
    unfolding the instance's actual definition. -/
def canonicalMethodInst (method : Name) (args : Array Lean.Expr) : Bool :=
  let unary := method == ``Neg.neg || method == ``Complement.complement
  let k := if unary then 2 else 3
  if args.size < k then false else
  let inst := args[args.size - k]!
  match inst.getAppFn with
  | .const c _ =>
    (canonicalSignalBinInsts.any fun (m, i, _, _) => m == method && i == c) ||
    (canonicalScalarMethodInsts.any fun (m, outer, inner?) =>
      m == method && outer == c &&
      match inner? with
      | none => true
      | some inner =>
        match inst.getAppArgs.back? with
        | some ia => ia.getAppFn.isConstOf inner
        | none => false)
  | _ => false

/--
  Primitive Registry: Maps Lean function names to IR operators
-/
def primitiveRegistry : List (Name × Sparkle.IR.AST.Operator) :=
  [
    -- Logical operations
    (``BitVec.and, .and),
    (``HAnd.hAnd, .and),
    (``BitVec.or, .or),
    (``HOr.hOr, .or),
    (``BitVec.xor, .xor),
    (``HXor.hXor, .xor),
    -- Arithmetic operations
    (``BitVec.add, .add),
    (``HAdd.hAdd, .add),
    (``BitVec.sub, .sub),
    (``HSub.hSub, .sub),
    (``BitVec.mul, .mul),
    (``HMul.hMul, .mul),
    -- Comparison operations (unsigned)
    (``BitVec.ult, .lt_u),
    (``BitVec.ule, .le_u),
    (``LT.lt, .lt_u),
    (``LE.le, .le_u),
    (``BEq.beq, .eq),
    -- Comparison operations (signed)
    (``BitVec.slt, .lt_s),
    (``BitVec.sle, .le_s),
    -- Shift operations (BitVec × BitVec via typeclass operators <<<, >>>)
    (``HShiftLeft.hShiftLeft, .shl),
    (``ShiftLeft.shiftLeft, .shl),
    (``HShiftRight.hShiftRight, .shr),
    (``ShiftRight.shiftRight, .shr),
    -- Negation (unary: -x)
    (``Neg.neg, .neg),
    (``BitVec.neg, .neg),
    -- Bitwise NOT (unary: ~~~x)
    (``Complement.complement, .not),
    (``BitVec.not, .not),
    -- Arithmetic shift right (BitVec × BitVec wrapper for sshiftRight)
    (``Sparkle.Core.Signal.ashr, .asr),
    -- Boolean operations (for Signal dom Bool combinators)
    (``Bool.not, .not),
    (``not, .not),
    (``Bool.and, .and),
    (``Bool.or, .or),
    (``Bool.xor, .xor)
  ]

def isPrimitive (name : Name) : Bool :=
  primitiveRegistry.any (fun (n, _) => n == name)

def getOperator (name : Name) : Option Operator :=
  primitiveRegistry.lookup name

partial def inferHWType (type : Lean.Expr) : MetaM (Option HWType) := do
  -- Use `.all` transparency so reducible defs like `HList`
  -- (which unfolds to a nested `Prod`/`Unit` chain via
  -- pattern-match) are reduced past their match head.
  let type ← withTransparency TransparencyMode.all $ whnf type
  match type with
  | .app (.const ``BitVec _) width =>
    -- Width can be direct literal or OfNat wrapper
    let w ← extractWidth width
    return some (if w == 1 then .bit else .bitVector w)
  | .const ``Bool _ =>
    return some .bit
  | .const ``Unit _ =>
    -- `Unit` / `PUnit` are the terminator of an `HList` Prod
    -- chain; they carry no bits.  Returning `.bitVector 0`
    -- lets `Prod` chains ending in `Unit` keep accumulating
    -- widths correctly.
    return some (.bitVector 0)
  | .const ``PUnit _ =>
    return some (.bitVector 0)
  | .app (.app (.const ``Prod _) ty1) ty2 =>
    -- Product type: concatenate the two types.  Zero-width
    -- components (from a `Unit`/`PUnit` terminator at the end
    -- of an `HList` chain) are handled by the bitVector match
    -- arm — `bitVector 0 + bitVector w = bitVector w`.
    match ← inferHWType ty1, ← inferHWType ty2 with
    | some (.bitVector w1), some (.bitVector w2) => return some (.bitVector (w1 + w2))
    | some .bit, some (.bitVector w2) => return some (.bitVector (1 + w2))
    | some (.bitVector w1), some .bit => return some (.bitVector (w1 + 1))
    | some .bit, some .bit => return some (.bitVector 2)
    | _, _ => return none
  | .app (.app (.const ``Sparkle.Core.Vector.HWVector _) elemType) size =>
    -- HWVector α n: extract element type and size
    let n ← extractWidth size
    match ← inferHWType elemType with
    | some hwElemType => return some (.array n hwElemType)
    | none => return none
  | _ =>
    -- User structure type (e.g. KvHwOut dom).  If the type is
    -- a constant application to a structure whose fields are all
    -- `Signal dom <hw type>`, treat the whole struct as the
    -- concatenation of its field HW widths.  This lets
    -- @[hardware_module] defs with user-defined output records
    -- (Ethernet.RxOut, MemcachedHW.KvHwOut) be inferred without
    -- a manual `Wireable` instance.
    let env ← getEnv
    let fn := type.getAppFn
    match fn with
    | .const structName _ =>
      if let some _ := env.find? structName then
        if isStructure env structName then
          let fields := getStructureFieldsFlattened env structName
          let typeArgs := type.getAppArgs
          let mut totalW : Nat := 0
          let mut allOk := true
          for fieldName in fields do
            let projName := structName ++ fieldName
            match env.find? projName with
            | none => allOk := false; break
            | some _ =>
              let projExpr := mkAppN (.const projName []) typeArgs
              let fieldType ← inferType projExpr
              -- field type is `<struct> → α`; we want the codomain
              let codomain ← match fieldType with
                | .forallE _ _ body _ => pure body
                | _ => pure fieldType
              -- codomain is typically `Signal dom α`; strip Signal.
              let codomain ← whnf codomain
              let inner := match codomain with
                | .app (.app sf _) a =>
                  match sf with
                  | .const sname _ =>
                    if sname.toString.endsWith "Signal" then a else codomain
                  | _ => codomain
                | _ => codomain
              match ← inferHWType inner with
              | some (.bitVector w) => totalW := totalW + w
              | some .bit => totalW := totalW + 1
              | _ => allOk := false; break
          if allOk && totalW > 0 then
            return some (.bitVector totalW)
      return none
    | _ => return none
where
  extractWidth (e : Lean.Expr) : MetaM Nat := do
    let e ← whnf e
    match e with
    | .lit (.natVal n) => return n
    | .app _ _ =>
      let fnConst := e.getAppFn
      let args := e.getAppArgs
      if fnConst.isConstOf ``OfNat.ofNat && args.size >= 2 then
        -- OfNat.ofNat Type n inst -> extract n
        extractWidth args[1]!
      -- Closed Nat arithmetic: widths of width-generic IP (`BitVec (w + f)`,
      -- `BitVec (W + 1)`, …) reach here as `Nat.succ`/`Nat.add`/… applications
      -- after `whnf` — `whnf` only exposes the head.  Evaluate structurally.
      --
      -- ⚠ Previously these fell into the silent `return 8` default below,
      -- which MISCOMPILES: a 49-bit signal gets an 8-bit wire and the mux
      -- feeding a 49-bit register truncates to zero.  Caught by iverilog
      -- simulation of the emitted `IP/Control/DividerQ` RTL (the divisor
      -- register never latched); invisible to every Lean-side test.
      else if fnConst.isConstOf ``Nat.succ && args.size == 1 then
        return (← extractWidth args[0]!) + 1
      else if fnConst.isConstOf ``Nat.add && args.size == 2 then
        return (← extractWidth args[0]!) + (← extractWidth args[1]!)
      else if fnConst.isConstOf ``Nat.sub && args.size == 2 then
        return (← extractWidth args[0]!) - (← extractWidth args[1]!)
      else if fnConst.isConstOf ``Nat.mul && args.size == 2 then
        return (← extractWidth args[0]!) * (← extractWidth args[1]!)
      else if fnConst.isConstOf ``Nat.pow && args.size == 2 then
        return (← extractWidth args[0]!) ^ (← extractWidth args[1]!)
      else if fnConst.isConstOf ``Nat.mod && args.size == 2 then
        return (← extractWidth args[0]!) % (← extractWidth args[1]!)
      else if fnConst.isConstOf ``Nat.div && args.size == 2 then
        return (← extractWidth args[0]!) / (← extractWidth args[1]!)
      else if (fnConst.isConstOf ``HAdd.hAdd || fnConst.isConstOf ``HSub.hSub ||
               fnConst.isConstOf ``HMul.hMul || fnConst.isConstOf ``HPow.hPow)
              && args.size >= 6 then
        let a ← extractWidth args[4]!
        let b ← extractWidth args[5]!
        if fnConst.isConstOf ``HAdd.hAdd then return a + b
        else if fnConst.isConstOf ``HSub.hSub then return a - b
        else if fnConst.isConstOf ``HMul.hMul then return a * b
        else return a ^ b
      else
        return 8
    | _ => return 8

/-- Preserve a retained top-level Nat binder as a closed symbolic dimension. -/
partial def extractDimExpr (expr : Lean.Expr) : CompilerM DimExpr := do
  let expr ← CompilerM.liftMetaM (whnf expr)
  match expr with
  | .lit (.natVal value) => return .literal value
  | .fvar fvarId =>
    match ← CompilerM.lookupDimVar fvarId with
    | some dimension => return dimension
    | none =>
      let declaration ← CompilerM.liftMetaM fvarId.getDecl
      CompilerM.liftMetaM $ throwError
        (s!"Symbolic Nat binder '{declaration.userName}' is used as a hardware dimension " ++
         "but was not retained as a module parameter.\n" ++
         "Use the parameterized synthesis API and provide a default for this binder.")
  | _ =>
    let fn := expr.getAppFn
    let args := expr.getAppArgs
    match fn with
    | .const name _ =>
      let binary (constructor : DimExpr → DimExpr → DimExpr) : CompilerM DimExpr := do
        if args.size < 2 then
          CompilerM.liftMetaM $ throwError s!"Malformed symbolic dimension operation {name}"
        let lhs ← extractDimExpr args[args.size - 2]!
        let rhs ← extractDimExpr args[args.size - 1]!
        return constructor lhs rhs
      if name == ``Nat.add then binary DimExpr.mkAdd
      else if name == ``Nat.sub then binary DimExpr.mkSub
      else if name == ``Nat.mul then binary DimExpr.mkMul
      else if name == ``Nat.div then binary .div
      else if name == ``Nat.mod then binary .mod
      else if name == ``Nat.pow then binary .pow
      else if name == ``Nat.min then binary .min
      else if name == ``Nat.max then binary .max
      else if name == ``Nat.succ && !args.isEmpty then
        return DimExpr.mkAdd (← extractDimExpr args.back!) (.literal 1)
      else if name == ``OfNat.ofNat && args.size >= 2 then
        extractDimExpr args[1]!
      else if (name == ``HAdd.hAdd || name == ``HSub.hSub ||
               name == ``HMul.hMul || name == ``HPow.hPow ||
               name == ``HMod.hMod || name == ``HDiv.hDiv) && args.size >= 6 then
        let lhs ← extractDimExpr args[4]!
        let rhs ← extractDimExpr args[5]!
        if name == ``HAdd.hAdd then return DimExpr.mkAdd lhs rhs
        else if name == ``HSub.hSub then return DimExpr.mkSub lhs rhs
        else if name == ``HMul.hMul then return DimExpr.mkMul lhs rhs
        else if name == ``HPow.hPow then return .pow lhs rhs
        else if name == ``HMod.hMod then return .mod lhs rhs
        else return .div lhs rhs
      else
        let rendered ← CompilerM.liftMetaM (ppExpr expr)
        CompilerM.liftMetaM $ throwError
          (s!"Unsupported symbolic hardware dimension '{rendered}'.\n" ++
           "Supported operations: retained parameters, literals, +, -, *, /, %, ^, min, and max.")
    | _ =>
      let rendered ← CompilerM.liftMetaM (ppExpr expr)
      CompilerM.liftMetaM $ throwError s!"Unsupported symbolic hardware dimension '{rendered}'"

/-- Infer hardware types with retained dimensions when parameter synthesis is active.
    The established concrete inference path remains untouched for ordinary APIs. -/
partial def inferHWTypeWithDimensions (type : Lean.Expr) : CompilerM (Option HWType) := do
  let state ← CompilerM.getCompilerState
  if !state.symbolicMode then
    return ← CompilerM.liftMetaM (inferHWType type)
  let type ← CompilerM.liftMetaM
    (withTransparency TransparencyMode.all $ whnf type)
  match type with
  | .app (.const ``BitVec _) width =>
    return some (hwTypeFromDim (← extractDimExpr width))
  | .const ``Bool _ => return some .bit
  | .const ``Unit _ | .const ``PUnit _ => return some (.bitVector 0)
  | .app (.app (.const ``Prod _) lhsType) rhsType =>
    match ← inferHWTypeWithDimensions lhsType, ← inferHWTypeWithDimensions rhsType with
    | some lhs, some rhs =>
      return some (hwTypeFromDim (DimExpr.mkAdd lhs.bitWidthDim rhs.bitWidthDim))
    | _, _ => return none
  | .app (.app (.const ``Sparkle.Core.Vector.HWVector _) _) _ =>
    CompilerM.liftMetaM $ throwError
      "Parameterized HWVector/array dimensions are not supported by native symbolic-width synthesis"
  | _ =>
    let rendered ← CompilerM.liftMetaM (ppExpr type)
    CompilerM.liftMetaM $ throwError
      s!"Parameterized synthesis currently supports packed BitVec/Bool/Prod payloads; unsupported type '{rendered}'"


/-- Extract `ResetKind` from a `Signal dom α` expression.

    We `whnf`-reduce the `dom` argument and then use Lean's
    `evalExpr` to evaluate it as a `DomainConfig`, reading the
    `resetKind` field directly.  Falls back to `.asynchronous`
    (the historical default) if the expression doesn't reduce
    to a literal `DomainConfig`. -/
def inferResetKindFromSignal (signalType : Lean.Expr) :
    CompilerM Sparkle.IR.Type.ResetKind := do
  let signalType ← CompilerM.liftMetaM (whnf signalType)
  match signalType with
  | .app (.app _signalConstr dom) _innerType =>
    -- Try to evaluate `(dom : DomainConfig).resetKind`.  If anything
    -- about the expression resists reduction (e.g. a metavariable
    -- in scope), fall back to async — it's what the codegen used
    -- before this field existed, so the default is conservative.
    try
      let domType :=
        Lean.Expr.const ``Sparkle.Core.Domain.DomainConfig []
      let dom' ← CompilerM.liftMetaM (whnf dom)
      let _ : Lean.Expr := domType        -- force domType into scope
      let kindExpr := Lean.mkApp
        (Lean.Expr.const ``Sparkle.Core.Domain.DomainConfig.resetKind [])
        dom'
      let kindReduced ← CompilerM.liftMetaM (whnf kindExpr)
      match kindReduced with
      | .const ``Sparkle.IR.Type.ResetKind.synchronous _ =>
        return .synchronous
      | .const ``Sparkle.IR.Type.ResetKind.asynchronous _ =>
        return .asynchronous
      | _ =>
        return .asynchronous
    catch _ =>
      return .asynchronous
  | _ =>
    return .asynchronous

private initialize sparkleHWInferCalls : IO.Ref Nat ← IO.mkRef 0
private initialize sparkleHWInferMs    : IO.Ref Nat ← IO.mkRef 0

def inferHWTypeFromSignal (signalType : Lean.Expr) : CompilerM HWType := do
  let t0 ← CompilerM.liftMetaM IO.monoMsNow
  let signalType ← CompilerM.liftMetaM (whnf signalType)
  match signalType with
  | .app (.app signalConstr _dom) innerType =>
    match signalConstr with
    | .const name _ =>
      if name.toString.endsWith "Signal" then
        match ← inferHWTypeWithDimensions innerType with
        | some hwType => return hwType
        | none => CompilerM.liftMetaM $ throwError s!"Cannot infer hardware type from {innerType}"
      else
        match ← inferHWTypeWithDimensions signalType with
        | some hwType => return hwType
        | none => CompilerM.liftMetaM $ throwError s!"Cannot infer hardware type from {signalType}"
    | _ =>
      match ← inferHWTypeWithDimensions signalType with
      | some hwType => return hwType
      | none => CompilerM.liftMetaM $ throwError s!"Cannot infer hardware type from {signalType}"
  | _ =>
    match ← inferHWTypeWithDimensions signalType with
    | some hwType => return hwType
    | none => CompilerM.liftMetaM $ throwError s!"Cannot infer hardware type from {signalType}"

/-- Syntactically identify Signal binders so symbolic-width diagnostics are not
    swallowed by the fallback path for erased configuration arguments. -/
def isSignalBinderType (type : Lean.Expr) : CompilerM Bool := do
  let type ← CompilerM.liftMetaM (whnf type)
  match type.getAppFn with
  | .const name _ => return name.toString.endsWith "Signal"
  | _ => return false

/-- Helper to extract a Nat literal or OfNat.ofNat wrap. -/
partial def extractNat (e : Lean.Expr) : CompilerM Nat := do
  let e ← CompilerM.liftMetaM (whnf e)
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const name _ =>
    if name == ``OfNat.ofNat && args.size >= 2 then
       -- Usually a raw literal, but width arithmetic can leave a closed
       -- term here — recurse instead of insisting on `.lit`.
       extractNat args[1]!
    else if name == ``Fin.mk && args.size >= 2 then
       extractNat args[1]!
    -- Closed Nat arithmetic.  Width expressions of width-generic IP
    -- (`BitVec (w + f)`, `extractLsb' (w - 1) 1`, `BitVec.ofNat (W + 1) …`)
    -- reach this point as `Nat.succ`/`Nat.add`/… applications after `whnf`,
    -- not as literals — `whnf` only exposes the head.  Evaluate them
    -- structurally.  (Previously a hard error "Expected Nat literal, got
    -- constant: Nat.succ", which made any width-generic module fail to
    -- synthesize once instantiated; see IP/Control/DividerQ.lean.)
    else if name == ``Nat.succ && args.size == 1 then
       return (← extractNat args[0]!) + 1
    else if name == ``Nat.add && args.size == 2 then
       return (← extractNat args[0]!) + (← extractNat args[1]!)
    else if name == ``Nat.sub && args.size == 2 then
       return (← extractNat args[0]!) - (← extractNat args[1]!)
    else if name == ``Nat.mul && args.size == 2 then
       return (← extractNat args[0]!) * (← extractNat args[1]!)
    else if name == ``Nat.pow && args.size == 2 then
       return (← extractNat args[0]!) ^ (← extractNat args[1]!)
    else if name == ``Nat.mod && args.size == 2 then
       return (← extractNat args[0]!) % (← extractNat args[1]!)
    else if name == ``Nat.div && args.size == 2 then
       return (← extractNat args[0]!) / (← extractNat args[1]!)
    else if (name == ``HAdd.hAdd || name == ``HSub.hSub || name == ``HMul.hMul ||
             name == ``HPow.hPow || name == ``HMod.hMod || name == ``HDiv.hDiv)
            && args.size >= 6 then
       -- Heterogeneous wrappers, in case `whnf` left the instance unpeeled.
       let a ← extractNat args[4]!
       let b ← extractNat args[5]!
       if name == ``HAdd.hAdd then return a + b
       else if name == ``HSub.hSub then return a - b
       else if name == ``HMul.hMul then return a * b
       else if name == ``HPow.hPow then return a ^ b
       else if name == ``HMod.hMod then return a % b
       else return a / b
    else
       CompilerM.liftMetaM $ throwError s!"Expected Nat literal, got constant: {name}"
  | .lit (.natVal n) => return n
  | _ => CompilerM.liftMetaM $ throwError s!"Expected Nat, got: {e}"

/-- Build a concrete or symbolic IR slice without freezing either bound. -/
def makeSliceExpr (source : Sparkle.IR.AST.Expr) (hi lo : DimExpr) :
    Sparkle.IR.AST.Expr :=
  match hi.toNat?, lo.toNat? with
  | some hiValue, some loValue => .slice source hiValue loValue
  | _, _ => .sliceDim source hi lo

def makeSliceFromStartLength (source : Sparkle.IR.AST.Expr)
    (start length : DimExpr) : Sparkle.IR.AST.Expr :=
  let hi := DimExpr.mkSub (DimExpr.mkAdd start length) (.literal 1)
  makeSliceExpr source hi start

/-- Lower unsigned extension/truncation while retaining parameter expressions.
    SystemVerilog assignment performs both operations correctly for symbolic
    vector widths; the established concat/slice lowering remains for concrete IR. -/
def lowerZeroExtendWire (hint sourceWire : String) (targetWidth : DimExpr)
    (isNamed : Bool := false) : CompilerM String := do
  let sourceWidth ← CompilerM.getWireWidthDim sourceWire
  let resultWire ← CompilerM.makeWire hint (hwTypeFromDim targetWidth) (named := isNamed)
  match targetWidth.toNat?, sourceWidth.toNat? with
  | some target, some source =>
    if target > source then
      let padWidth := target - source
      let padWire ← CompilerM.makeWire "zext_pad" (.bitVector padWidth)
      CompilerM.emitAssign padWire (.const 0 padWidth)
      CompilerM.emitAssign resultWire (.concat [.ref padWire, .ref sourceWire])
    else
      let hi := if target == 0 then 0 else target - 1
      CompilerM.emitAssign resultWire (.slice (.ref sourceWire) hi 0)
  | _, _ =>
    CompilerM.emitAssign resultWire (.ref sourceWire)
  return resultWire

def extractBitVecLiteral (expr : Lean.Expr) : CompilerM (Nat × Nat) := do
  let expr ← CompilerM.liftMetaM (whnf expr)
  let fn := expr.getAppFn
  let args := expr.getAppArgs
  match fn with
  | .const name _ =>
    if name == ``BitVec.ofNat && args.size >= 3 then
      let w ← extractNat args[0]!
      let v ← extractNat args[2]!
      return (v, w)
    else if name == ``BitVec.ofFin && args.size >= 2 then
      let w ← extractNat args[0]!
      let v ← extractNat args[1]!
      return (v, w)
    else if name == ``Bool.false then
      return (0, 1)
    else if name == ``Bool.true then
      return (1, 1)
    else
      CompilerM.liftMetaM $ throwError s!"Expected BitVec literal, got application of {name}"
  | _ =>
    CompilerM.liftMetaM $ throwError s!"Expected BitVec literal, got: {expr}"

/-- Extract a Nat literal from an expression -/
def extractNatLiteral (expr : Lean.Expr) : CompilerM (Nat × Unit) := do
  let n ← extractNat expr
  return (n, ())

/-- Extract values from a List (BitVec n) expression into an array of (value, width) pairs -/
partial def extractBitVecList (expr : Lean.Expr) : CompilerM (Array (Nat × Nat)) := do
  let expr ← CompilerM.liftMetaM (whnf expr)
  let fn := expr.getAppFn
  let args := expr.getAppArgs
  match fn with
  | .const name _ =>
    if name == ``List.cons && args.size >= 3 then
      let head := args[1]!
      let tail := args[2]!
      let (val, width) ← extractBitVecLiteral head
      let rest ← extractBitVecList tail
      return #[(val, width)] ++ rest
    else if name == ``List.nil then
      return #[]
    else
      CompilerM.liftMetaM $ throwError s!"Expected List.cons or List.nil, got: {name}"
  | _ =>
    CompilerM.liftMetaM $ throwError s!"Expected List expression, got: {expr}"

/-- Extract values from an Array (BitVec n) expression -/
def extractBitVecArray (expr : Lean.Expr) : CompilerM (Array (Nat × Nat)) := do
  let expr ← CompilerM.liftMetaM (Lean.Meta.reduce expr (skipTypes := true) (skipProofs := true))
  let fn := expr.getAppFn
  let args := expr.getAppArgs
  match fn with
  | .const name _ =>
    if name == ``Array.mk && args.size >= 2 then
      extractBitVecList args[1]!
    else if name == ``List.toArray && args.size >= 2 then
      extractBitVecList args[1]!
    else
      CompilerM.liftMetaM $ throwError s!"Expected Array.mk, got: {name} with {args.size} args"
  | _ =>
    CompilerM.liftMetaM $ throwError s!"Expected Array expression, got: {expr}"

/-- Global call counters for `translateExprToWire` profiling.
    Populated only when `SPARKLE_PROFILE=1`. -/
private initialize sparkleCallCounter : IO.Ref Nat ← IO.mkRef 0
private initialize sparkleCacheHits   : IO.Ref Nat ← IO.mkRef 0
/-- Nested-synth depth counter.  `synthesizeCombinational` only
    resets the per-synth caches when entering at depth 0 (the
    outermost user-triggered `#synthesizeVerilog`).  When the
    parent synth recursively invokes child synths (via
    `@[hardware_module]` sub-module instances), the child must
    NOT clobber the parent's caches — doing so makes the parent
    re-walk every previously-translated expression after the
    child returns, which trivially turns sub-module-instance
    synth into an O(n²) walk. -/
private initialize sparkleSynthDepth : IO.Ref Nat ← IO.mkRef 0

/-- Set of fvar names currently being zeta-reduced.  If we see
    the same fvar twice on the stack, the fvar's value contains
    a reference back to itself — typical of Signal.loop bodies
    that bind the loop state to an fvar whose definition then
    transitively references that fvar through the loop's
    memoize chain.  Use this to detect and abort cleanly. -/
private initialize sparkleFvarZetaVisited : IO.Ref (Std.HashSet Lean.Name) ← IO.mkRef {}

/-- Map from `let`-bound HW fvar names back to their defining
    expressions.  Populated by the HW-let branch of
    handleDefinitionUnfold when it sees `let engine := kvHw …`,
    consumed by the multi-output sub-module projection shortcut
    so `engine.replyValid` can recover the underlying `kvHw …`
    call and instantiate it as a sub-module. -/
private initialize sparkleFvarValueMap : IO.Ref (Std.HashMap Lean.Name Lean.Expr) ← IO.mkRef {}

/-- Hardware-`let` wire cache, keyed by the value's structure PLUS the wires its
    free variables denote.  See the `.letE` handler for why the plain
    expression cache is insufficient (intermediate bindings are re-instantiated
    with fresh fvars once per consumer of a `circuit do` body).  Reset per
    top-level synth alongside the other caches. -/
private initialize sparkleLetWireCache : IO.Ref (Std.HashMap String String) ← IO.mkRef {}

/-- `Signal.loop` expression cache, keyed like `sparkleLetWireCache` (the loop
    lambda's structure plus the wires its free variables denote).

    `runCircuitH` evaluates the user's body TWICE — once inside its own
    `Signal.loop` for the register next-state, once outside for the returned
    value — and `@[reducible]` unfolding zeta-reduces its `let`s, so a NESTED
    circuit's `Signal.loop` reaches the loop handler as a bare expression in
    each pass, and the hardware-`let` cache never sees it.  Without this
    cache every nested `circuit do` was emitted twice (measured: 3 registers
    for a 2-register design, 5 for `closedLoopCircuit`'s 3), the second copy
    read only by the returned value.  The two passes differ only in how they
    name the enclosing loop's live signal — the loop binder's fvar versus the
    `let stateLoop := Signal.loop …` binder — which `sparkleWireCanon`
    identifies, so the canonical keys coincide and the second pass reuses
    the first pass's wire.  Reset per synth alongside the other caches. -/
private initialize sparkleLoopWireCache : IO.Ref (Std.HashMap String String) ← IO.mkRef {}

/-- Wire aliases for canonical-key purposes: a `Signal.loop`'s result wire
    is the same hardware as the loop wire its body binder denotes
    (`assign loopWire = resultWire`), so keys built from either name must
    agree.  Maps `resultWire ↦ loopWire`. -/
private initialize sparkleWireCanon : IO.Ref (Std.HashMap String String) ← IO.mkRef {}

/-- Cache of previously-synthesised sub-modules.  Without this,
    the multi-output sub-module projection shortcut would re-
    invoke `synthesizeCombinational` once per `<call>.<field>`
    access (multiple fields per sub-module instance × multiple
    instances per design).  Cleared at the top of each
    `synthesizeCombinational` invocation. -/
private initialize sparkleSubModuleCache :
    IO.Ref (Std.HashMap Lean.Name (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) ←
    IO.mkRef {}

/-- Per top-level synthesis, the full-entry result of every child a call
    site synthesised (`Rec.synthesizeCombinational`): a child projected at
    several fields, or called from several places, is synthesised once.
    Cleared with the other per-synth caches at depth 0. -/
private initialize sparkleChildCache :
    IO.Ref (Std.HashMap Lean.Name (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) ←
    IO.mkRef {}

/-- The synthesis entry a state machine uses for the `@[hardware_module]`
    children its body calls (`closeInsts`): the real entry
    `synthesizeCombinational`, set once it is defined (the machine synthesis
    is defined before the translator block that closes the knot). -/
initialize sparkleChildSynth :
    IO.Ref (Option (Name → MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design))) ←
    IO.mkRef none

/-- Per-call output port wire mapping.  Keyed by
    `(call-expression hash, field name)`, returns the wire bound
    to that field of the sub-module instance.  Populated by the
    multi-output sub-module instance emitter (handleDefinitionUnfold
    line 2249); consumed by the projection handler when a struct-
    typed sub-module call result is projected (`engine.replyValid`).

    Hash key (UInt64) is used instead of full Expr identity
    because Lean re-elaborates structurally equal expressions
    into objects that fail pointer equality but share `Expr.hash`. -/
private initialize sparkleSubInstanceOutputs :
    IO.Ref (Std.HashMap (UInt64 × String) String) ← IO.mkRef {}

/-- Idempotency cache for SINGLE-output sub-module instances
    (Issue #107).  The synth elaborator walks a `circuit do` body
    once per register next-state leaf plus once for the output
    leaf; a `let t := toggle en` binding is re-translated on every
    pass because named translations bypass the structural
    `exprCache` (see `cacheable` in `translateExprToWire`), so
    each pass emitted a fresh instance — E = I · (D + 1) instead
    of I.  The multi-output path has its own guard keyed on
    `sparkleSubInstanceOutputs`; this covers the scalar path.

    Key: `parent module name # child module name # port
    connections (canonical wire names)`.  The connection wires
    make the key fine enough to keep `toggle e0` / `toggle e1`
    distinct (keying on name + arity alone would FOLD distinct
    instances — a miscompile, not a cleanup).  The parent module
    name scopes the cached output wire to the module that
    actually declared it.  Folding same-key instances is sound:
    two structurally identical calls denote the same signal in
    Sparkle's pure semantics, stateful or not (same module, same
    inputs, same reset ⇒ same state trajectory).

    Value: the instance's output wire.  Cleared at depth 0 with
    the other per-synth caches. -/
private initialize sparkleSingleOutInstanceCache :
    IO.Ref (Std.HashMap String String) ← IO.mkRef {}

/-- Type-of-Expr cache.  `Lean.Meta.inferType` is the dominant
    cost in handleTupleProjections / handleApplicative / handleMux
    (typeclass-instance search fires per call); the same `e` is
    revisited many times when ρ-generic returns push the same
    sub-expression through multiple projections.  Memoising the
    inferred type by Expr identity collapses the hottest path. -/
private initialize sparkleTypeCache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr) ← IO.mkRef {}

/-- Memoised `Lean.Meta.inferType`.  Pure compiler-side cache;
    correctness relies on the cache being scoped per `synth*`
    invocation (we reset it at the start of `synthesizeCombinational`). -/
private initialize sparkleTypeCacheHits : IO.Ref Nat ← IO.mkRef 0
private initialize sparkleTypeCacheMiss : IO.Ref Nat ← IO.mkRef 0

/-- Counters for the Lean.Meta operations the compiler issues
    *directly*.  When SPARKLE_PROFILE=1 the tick log reports
    each total — gives a direct read on which Meta call is
    the actual hot spot rather than guessing from handler
    inclusive times. -/
private initialize sparkleWhnfCalls       : IO.Ref Nat ← IO.mkRef 0
private initialize sparkleInferCalls      : IO.Ref Nat ← IO.mkRef 0
private initialize sparkleUnfoldDefCalls  : IO.Ref Nat ← IO.mkRef 0
private initialize sparkleWhnfMs          : IO.Ref Nat ← IO.mkRef 0
private initialize sparkleInferMs         : IO.Ref Nat ← IO.mkRef 0
private initialize sparkleUnfoldDefMs     : IO.Ref Nat ← IO.mkRef 0

/-- Wrap a MetaM `whnf` with counters. -/
def countedWhnf (e : Lean.Expr) : CompilerM Lean.Expr := do
  let t0 ← CompilerM.liftMetaM IO.monoMsNow
  let r ← CompilerM.liftMetaM (Lean.Meta.whnf e)
  let t1 ← CompilerM.liftMetaM IO.monoMsNow
  CompilerM.liftMetaM (sparkleWhnfCalls.modify (· + 1))
  CompilerM.liftMetaM (sparkleWhnfMs.modify (· + (t1 - t0)))
  return r

/-- Wrap `Lean.Meta.unfoldDefinition?` with counters. -/
def countedUnfoldDefinition? (e : Lean.Expr) : CompilerM (Option Lean.Expr) := do
  let t0 ← CompilerM.liftMetaM IO.monoMsNow
  let r ← CompilerM.liftMetaM (Lean.Meta.unfoldDefinition? e)
  let t1 ← CompilerM.liftMetaM IO.monoMsNow
  CompilerM.liftMetaM (sparkleUnfoldDefCalls.modify (· + 1))
  CompilerM.liftMetaM (sparkleUnfoldDefMs.modify (· + (t1 - t0)))
  return r

def cachedInferType (e : Lean.Expr) : CompilerM Lean.Expr := do
  let cache ← CompilerM.liftMetaM sparkleTypeCache.get
  match cache.get? e with
  | some ty =>
    CompilerM.liftMetaM (sparkleTypeCacheHits.modify (· + 1))
    return ty
  | none =>
    CompilerM.liftMetaM (sparkleTypeCacheMiss.modify (· + 1))
    let t0 ← CompilerM.liftMetaM IO.monoMsNow
    let ty ← CompilerM.liftMetaM (Lean.Meta.inferType e)
    let t1 ← CompilerM.liftMetaM IO.monoMsNow
    CompilerM.liftMetaM (sparkleInferCalls.modify (· + 1))
    CompilerM.liftMetaM (sparkleInferMs.modify (· + (t1 - t0)))
    CompilerM.liftMetaM (sparkleTypeCache.modify (·.insert e ty))
    return ty

/-- Per-handler invocation counters + cumulative ms.  Index is
    fixed by `sparkleProfHandlerNames` below. -/
private initialize sparkleHandlerCalls : IO.Ref (Array Nat) ← IO.mkRef (Array.replicate 11 0)
private initialize sparkleHandlerMs    : IO.Ref (Array Nat) ← IO.mkRef (Array.replicate 11 0)

private def sparkleProfHandlerNames : Array String :=
  #["handleErrorPatterns", "handleCircuitMonad", "handleTupleProjections",
    "handleApplicative", "handleBitVecOps", "handleRegister",
    "handleMux", "handleMemory", "handleLoop", "handleDefinitionUnfold",
    "fallback"]

/-- Wrap a handler call: bump the per-handler counter + ms when
    SPARKLE_PROFILE=1, otherwise just delegate.  `idx` matches
    `sparkleProfHandlerNames`. -/
private def profHandler {α} (_idx : Nat) (k : CompilerM α) : CompilerM α := do
  -- Profile disabled by default; the wrapper inlines to just `k`
  -- when SPARKLE_PROFILE is unset.  We avoid checking the env on
  -- every handler call (that itself shows up in the hot loop) by
  -- relying on the IO.Ref counters being cheap when nobody reads
  -- them.  `tInit ms`-tracking still happens unconditionally but
  -- is a single `IO.monoMsNow` pair around `k` — comparable to a
  -- handful of arithmetic ops on x86_64.
  let t0 ← CompilerM.liftMetaM IO.monoMsNow
  let r ← k
  let t1 ← CompilerM.liftMetaM IO.monoMsNow
  CompilerM.liftMetaM (sparkleHandlerCalls.modify (fun arr =>
    arr.setIfInBounds _idx ((arr.getD _idx 0) + 1)))
  CompilerM.liftMetaM (sparkleHandlerMs.modify (fun arr =>
    arr.setIfInBounds _idx ((arr.getD _idx 0) + (t1 - t0))))
  return r

/-- The declared width of a parent name: a wire, else an input port. -/
def instNameWidth? (m : Sparkle.IR.AST.Module) (w : String) : Option Nat :=
  match m.wires.find? (fun p => p.name == w) with
  | some p => some p.ty.bitWidth
  | none => (m.inputs.find? (fun p => p.name == w)).map (fun p => p.ty.bitWidth)

/-- WIDTH LINKAGE of one instance statement: every connection reads or
    drives a parent name declared with exactly the child port's width.
    A hardware module is compiled once, not per call site, so a
    width-generic child instantiated at another width would otherwise be
    connected across mismatching widths — silently truncating. -/
def instLinked (m : Sparkle.IR.AST.Module) (child : Sparkle.IR.AST.Module)
    (conns : List (String × Sparkle.IR.AST.Expr)) : Bool :=
  conns.all fun c =>
    match c.2 with
    | .ref w =>
      match (child.inputs ++ child.outputs).find? (fun p => p.name == c.1),
          instNameWidth? m w with
      | some p, some width => width == p.ty.bitWidth
      | _, _ => false
    | _ => false

/-- The linkage guard, hoisted so its callers stay join-point free. -/
def instLinkGuard (recName : Name) (ok : Bool) : CompilerM Unit :=
  if ok then pure ()
  else throw (Exception.error .missing
    m!"Instance of {recName}: a connected wire's width differs from the port's width. A hardware module is compiled once, not per call site; a width-generic module cannot be instantiated at a width other than the one it was compiled at.")

/-- Refuse to emit an instance statement that is not width-linked. -/
def instLinkCheck (recName : Name) (child : Sparkle.IR.AST.Module)
    (conns : List (String × Sparkle.IR.AST.Expr)) : CompilerM Unit := do
  let cs ← get
  instLinkGuard recName (instLinked cs.module child conns)

/-- Canonical, pass-stable key for a hardware-denoting expression: abstract
    every free variable to a constant named after the WIRE it denotes (wire
    names are stable within a module synth — they are what the emitted
    Verilog/C refers to), then hash the abstracted expression.

    Hashing the expression directly does not work: fvars are fresh per
    traversal, so two occurrences denoting the same hardware hash differently
    (measured 2079038327 vs 1490760256 for two `let num` occurrences whose
    fvars both mapped to `_gen_pS`, `_gen_y`).  After abstraction the key is
    equal exactly when the denoted hardware is the same — which also makes it
    the correct INSTANCE identity for multi-output sub-modules: calls with
    different argument wires get different keys (issue #120), while repeated
    projections of one `let engine := …` binder share one key (issue #71). -/
partial def canonHardwareExpr (value : Lean.Expr) : CompilerM Lean.Expr := do
  let canon ← CompilerM.liftMetaM (sparkleWireCanon.get : IO _)
  let canonOf (w : String) : String := Id.run do
    let mut w := w
    -- a loop's result wire and its loop wire are one piece of hardware
    for _ in [0:8] do
      match canon.get? w with
      | some w' => w := w'
      | none => break
    return w
  -- Logic `let`s (`runCircuitH`'s `idRead`/`idLift`, a `circuit do`'s
  -- non-hardware bindings) are opened as let-bound fvars, FRESH per
  -- traversal, with no wire.  Left in the key they would make the two
  -- evaluations of one body hash differently; substitute their values.
  let mut value := value
  for _ in [0:16] do
    let mut repl : Std.HashMap Lean.Name Lean.Expr := {}
    for fv in (Lean.collectFVars {} value).fvarIds do
      if (← CompilerM.lookupVar fv).isSome then continue
      if let some decl ← CompilerM.liftMetaM fv.findDecl? then
        if let some v := decl.value? then repl := repl.insert fv.name v
    if repl.isEmpty then break
    value := value.replace fun sub =>
      match sub with
      | .fvar fid => repl.get? fid.name
      | _ => none
  -- An enclosing loop's live signal reaches the two evaluations of a body
  -- as the loop binder's fvar (mapped to the loop wire) in one and as the
  -- `Signal.loop …` expression itself (zeta-reduced `stateLoop`) in the
  -- other.  Every already-translated `Signal.loop` sub-expression is
  -- therefore replaced by the wire it denotes, canonicalised — the key
  -- then agrees with the fvar form.  (Proper sub-expressions only; the
  -- loop handler keys the loop expression itself.)
  let loops : Array Lean.Expr := Id.run do
    let mut acc : Array Lean.Expr := #[]
    let mut seen : Std.HashSet Lean.Expr := {}
    let mut work : List Lean.Expr := [value]
    let mut fuel := 200000
    while fuel > 0 do
      fuel := fuel - 1
      match work with
      | [] => break
      | e :: rest =>
        work := rest
        if seen.contains e then continue
        seen := seen.insert e
        if e != value && e.isAppOf ``Sparkle.Core.Signal.Signal.loop
            && e.getAppNumArgs ≥ 1 then
          acc := acc.push e
          continue
        match e with
        | .app f a => work := f :: a :: work
        | .lam _ t b _ | .forallE _ t b _ => work := t :: b :: work
        | .letE _ t v b _ => work := t :: v :: b :: work
        | .mdata _ b | .proj _ _ b => work := b :: work
        | _ => pure ()
    return acc
  if !loops.isEmpty then
    let cache ← CompilerM.liftMetaM (sparkleLoopWireCache.get : IO _)
    let mut loopRepl : Std.HashMap Lean.Expr Lean.Expr := {}
    for l in loops do
      let k := toString (← canonHardwareExpr l).hash
      if let some w := cache.get? k then
        loopRepl := loopRepl.insert l
          (Lean.mkConst (Lean.Name.mkSimple s!"«wire:{canonOf w}»"))
    if !loopRepl.isEmpty then
      value := value.replace fun sub => loopRepl.get? sub
  let mut repl : Std.HashMap Lean.Name Lean.Expr := {}
  for fv in (Lean.collectFVars {} value).fvarIds do
    let w := canonOf ((← CompilerM.lookupVar fv).getD s!"?{fv.name}")
    repl := repl.insert fv.name (Lean.mkConst (Lean.Name.mkSimple s!"«wire:{w}»"))
  return value.replace fun sub =>
    match sub with
    | .fvar fid => repl.get? fid.name
    | _ => none

def canonHardwareKey (value : Lean.Expr) : CompilerM String := do
  return toString (← canonHardwareExpr value).hash

/-- The IR operator the Signal intercept emits for a method name (shipping
    dispatch table, formerly an inline `match` in `translateExprToWireImpl`). -/
def signalBinOpOf : Name → Option Operator
  | ``HAdd.hAdd => some .add
  | ``HSub.hSub => some .sub
  | ``HMul.hMul => some .mul
  | ``HAnd.hAnd => some .and
  | ``HOr.hOr => some .or
  | ``HXor.hXor => some .xor
  | ``HShiftLeft.hShiftLeft => some .shl
  | ``HShiftRight.hShiftRight => some .shr
  | _ => none

/-- A natural-number literal, recognised purely: a raw literal or
    `OfNat.ofNat Nat (lit k) _`. -/
def natLitValue? : Lean.Expr → Option Nat
  | .lit (.natVal k) => some k
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal k))) _ => some k
  | _ => none

/-- The `Bool` instances of `canonicalSignalBinInsts` (no width argument).
    Listed rather than tested by name suffix so the check reduces in proofs. -/
def canonicalSignalBoolInsts : List Name :=
  [``Sparkle.Core.Signal.instHAndSignalBool, ``Sparkle.Core.Signal.instHOrSignalBool,
   ``Sparkle.Core.Signal.instHXorSignalBool]

/-- The width `n` of a canonical `BitVec`-valued Signal operator instance
    (`@inst dom n`), when it is a literal. Pure; `none` for the `Bool`
    instances and for symbolic widths, which keep the oracle path. -/
def canonicalSignalBitVecWidth (args : Array Lean.Expr) : Option Nat :=
  if args.size < 3 then none else
  let inst := args[args.size - 3]!
  match inst.getAppFn with
  | .const c _ =>
    if canonicalSignalBinInsts.any (fun (_, i, _, _) => i == c) &&
        !(canonicalSignalBoolInsts.contains c) then
      (inst.getAppArgs.back?).bind natLitValue?
    else none
  | _ => none

/-- A `BitVec` literal recognised purely: `BitVec.ofNat w v`, or
    `OfNat.ofNat (BitVec w) v inst` whose instance is the LIBRARY
    `BitVec.instOfNat` (a user `OfNat (BitVec w)` instance is not a literal).
    Returns `(width, value)` only when `value < 2 ^ width`, the case in which
    the oracle path emits the same `.const value width`. -/
def bitVecLitValue? : Lean.Expr → Option (Nat × Nat)
  | .app (.app (.const ``BitVec.ofNat _) wE) vE =>
    match natLitValue? wE, natLitValue? vE with
    | some w, some v => if v < 2 ^ w then some (w, v) else none
    | _, _ => none
  | .app (.app (.app (.const ``OfNat.ofNat _) (.app (.const ``BitVec _) wE)) (.lit (.natVal v))) inst =>
    if inst.getAppFn.isConstOf ``BitVec.instOfNat then
      match natLitValue? wE with
      | some w => if v < 2 ^ w then some (w, v) else none
      | none => none
    else none
  | _ => none

/-- `Signal.pure` of a pure-recognised `BitVec` literal. SHIPPING code: tried by
    `translateExprToWireImpl` before the `whnf`-based constant path, which it
    leaves in place for every other payload. Non-recursive and oracle-free. -/
def translateSignalPureLiteral? (args : Array Lean.Expr) (hint : String) (isNamed : Bool) :
    CompilerM (Option String) := do
  match args.back?.bind bitVecLitValue? with
  | some (w, v) =>
    let resWire ← CompilerM.makeWire hint (.bitVector w) (named := isNamed)
    CompilerM.emitAssign resWire (.const v w)
    return some resWire
  | none => return none

/-- The translator's recursive entry, as a first-class argument. -/
abbrev TranslateFn := Lean.Expr → String → Bool → Bool → CompilerM String

/-- Emit the result of the shipping mux handler after its operands and result
    type have been translated. Kept non-recursive so allocation and emission
    can be proved independently of recursive operand translation/type inference. -/
def emitMuxResult (cond thenWire elseWire hint : String) (isNamed : Bool)
    (hwType : HWType) : CompilerM String := do
  let result ← CompilerM.makeWire hint hwType (named := isNamed)
  CompilerM.emitAssign result (.op .mux [.ref cond, .ref thenWire, .ref elseWire])
  return result

/-- A Nat literal whose meaning does not depend on a user `OfNat` instance.
    Used for type arguments in the canonical mux path. -/
def canonicalNatLitValue? : Lean.Expr → Option Nat
  | .lit (.natVal n) => some n
  | .app (.app (.app (.const ``OfNat.ofNat _) (.const ``Nat _)) (.lit (.natVal n)))
      (.app (.const ``instOfNatNat _) (.lit (.natVal k))) =>
    if n == k then some n else none
  | _ => none

/-- Read the result type only from an exact library mux application. Aliases,
    symbolic widths and other result types retain the existing inference path. -/
def canonicalMuxType? : Lean.Expr → Option HWType
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.mux _) _dom)
      ty) _cond) _thenSig) _elseSig =>
    match ty with
    | .const ``Bool _ => some .bit
    | .app (.const ``BitVec _) width => (canonicalNatLitValue? width).map HWType.bitVector
    | _ => none
  | _ => none

/-- Canonical width-changing map: `Signal.map (BitVec.setWidth wt) s` (or the
    `zeroExtend` alias) with literal, positive and mutually consistent widths.
    Returns `(source width, target width, child)`. Symbolic widths and other
    map forms keep the existing fallback path. -/
def canonicalSetWidth? : Lean.Expr → Option (Nat × Nat × Lean.Expr)
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map _) _)
      (.app (.const ``BitVec _) wsE)) (.app (.const ``BitVec _) wtE))
      (.app (.app (.const f _) wsE') wtE')) a =>
    if f == ``BitVec.setWidth || f == ``BitVec.zeroExtend then
      match canonicalNatLitValue? wsE, canonicalNatLitValue? wtE,
          canonicalNatLitValue? wsE', canonicalNatLitValue? wtE' with
      | some ws, some wt, some ws', some wt' =>
        if 0 < ws && 0 < wt && ws' == ws && wt' == wt then some (ws, wt, a) else none
      | _, _, _, _ => none
    else none
  | _ => none

/-- Canonical slice map: `Signal.map (fun x => BitVec.extractLsb' start len x) s`
    with literal widths, a positive length and the whole range inside the
    source (`start + len ≤ ws`).  Returns `(source width, start, length,
    child)`.  The binder name is not read. -/
def canonicalSlice? : Lean.Expr → Option (Nat × Nat × Nat × Lean.Expr)
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map _) _)
      (.app (.const ``BitVec _) wsE)) (.app (.const ``BitVec _) lenE))
      (.lam _ _ (.app (.app (.app (.app (.const ``BitVec.extractLsb' _) wsE') startE) lenE')
        (.bvar 0)) _)) a =>
    match canonicalNatLitValue? wsE, canonicalNatLitValue? lenE, canonicalNatLitValue? wsE',
        canonicalNatLitValue? startE, canonicalNatLitValue? lenE' with
    | some ws, some len, some ws', some start, some len' =>
      if 0 < len && ws' == ws && len' == len && decide (start + len ≤ ws) then
        some (ws, start, len, a)
      else none
    | _, _, _, _, _ => none
  | _ => none

/-- Canonical concatenation: `a ++ b` of two Signals at the library instance,
    with literal positive operand widths and the result width written as the
    literal of their sum — the form the front end folds `m + n` to
    (`inlFoldNat`).  Returns `(high width, low width, high operand, low
    operand)`. -/
def canonicalConcat? : Lean.Expr → Option (Nat × Nat × Lean.Expr × Lean.Expr)
  | .app (.app (.app (.app (.app (.app (.const ``HAppend.hAppend _)
      (.app (.app (.const ``Sparkle.Core.Signal.Signal _) _) (.app (.const ``BitVec _) mE)))
      (.app (.app (.const ``Sparkle.Core.Signal.Signal _) _) (.app (.const ``BitVec _) nE)))
      (.app (.app (.const ``Sparkle.Core.Signal.Signal _) _) (.app (.const ``BitVec _) rE)))
      (.app (.app (.app (.const ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat _) _) mE')
        nE')) a) b =>
    match canonicalNatLitValue? mE, canonicalNatLitValue? nE, canonicalNatLitValue? rE,
        canonicalNatLitValue? mE', canonicalNatLitValue? nE' with
    | some m, some n, some r, some m', some n' =>
      if 0 < m && 0 < n && r == m + n && m' == m && n' == n then some (m, n, a, b) else none
    | _, _, _, _, _ => none
  | _ => none

/-- Canonical concatenation with a LITERAL operand: `v#k ++ b` or `a ++ v#k`
    at the library's mixed instances, the literal written `BitVec.ofNat k v`
    with `v < 2 ^ k`, literal positive widths, the result width the literal of
    the sum.  Returns `(literal is the high operand, k, v, the Signal
    operand's width, domain, Signal operand)`. -/
def canonicalConcatLit? :
    Lean.Expr → Option (Bool × Nat × Nat × Nat × Lean.Expr × Lean.Expr)
  | .app (.app (.app (.app (.app (.app (.const ``HAppend.hAppend _)
      (.app (.const ``BitVec _) kE))
      (.app (.app (.const ``Sparkle.Core.Signal.Signal _) _) (.app (.const ``BitVec _) wE)))
      (.app (.app (.const ``Sparkle.Core.Signal.Signal _) dom) (.app (.const ``BitVec _) rE)))
      (.app (.app (.app (.const ``Sparkle.Core.Signal.instHAppendBitVecSignalHAddNat _) kE') _)
        wE')) (.app (.app (.const ``BitVec.ofNat _) kL) vL)) x =>
    match canonicalNatLitValue? kE, canonicalNatLitValue? wE, canonicalNatLitValue? rE,
        canonicalNatLitValue? kE', canonicalNatLitValue? wE', canonicalNatLitValue? kL,
        canonicalNatLitValue? vL with
    | some k, some w, some r, some k', some w', some kl, some v =>
      if 0 < k && 0 < w && r == k + w && k' == k && w' == w && kl == k && decide (v < 2 ^ k)
      then some (true, k, v, w, dom, x) else none
    | _, _, _, _, _, _, _ => none
  | .app (.app (.app (.app (.app (.app (.const ``HAppend.hAppend _)
      (.app (.app (.const ``Sparkle.Core.Signal.Signal _) _) (.app (.const ``BitVec _) wE)))
      (.app (.const ``BitVec _) kE))
      (.app (.app (.const ``Sparkle.Core.Signal.Signal _) dom) (.app (.const ``BitVec _) rE)))
      (.app (.app (.app (.const ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat_1 _) _) wE')
        kE')) x) (.app (.app (.const ``BitVec.ofNat _) kL) vL) =>
    match canonicalNatLitValue? kE, canonicalNatLitValue? wE, canonicalNatLitValue? rE,
        canonicalNatLitValue? kE', canonicalNatLitValue? wE', canonicalNatLitValue? kL,
        canonicalNatLitValue? vL with
    | some k, some w, some r, some k', some w', some kl, some v =>
      if 0 < k && 0 < w && r == w + k && k' == k && w' == w && kl == k && decide (v < 2 ^ k)
      then some (false, k, v, w, dom, x) else none
    | _, _, _, _, _, _, _ => none
  | _ => none

/-- Canonical zero-extension by a literal prefix inside a map:
    `Signal.map (fun v => BitVec.append (0#k) v) s` at literal positive
    widths, the result width the literal of `k + ws`.  Returns `(source
    width, prefix width, child)`.  Its lowering is the width cast's. -/
def canonicalZextMap? : Lean.Expr → Option (Nat × Nat × Lean.Expr)
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map _) _)
      (.app (.const ``BitVec _) wsE)) (.app (.const ``BitVec _) wtE))
      (.lam _ _ (.app (.app (.app (.app (.const ``BitVec.append _) kE) wsE')
        (.app (.app (.const ``BitVec.ofNat _) kL) zL)) (.bvar 0)) _)) a =>
    match canonicalNatLitValue? wsE, canonicalNatLitValue? wtE, canonicalNatLitValue? kE,
        canonicalNatLitValue? wsE', canonicalNatLitValue? kL, canonicalNatLitValue? zL with
    | some ws, some wt, some k, some ws', some kl, some z =>
      if 0 < ws && 0 < k && wt == k + ws && ws' == ws && kl == k && z == 0 then
        some (ws, k, a) else none
    | _, _, _, _, _, _ => none
  | _ => none

/-- Canonical slice written with `<$>`: `(fun x => BitVec.extractLsb' start
    len x) <$> s` at the library's `Functor` instance — the form the front
    end leaves a bare `f <$> a` in, because the legacy lowers it under its
    own child hint (`a`).  Same conditions and result as `canonicalSlice?`. -/
def canonicalSliceF? : Lean.Expr → Option (Nat × Nat × Nat × Lean.Expr)
  | .app (.app (.app (.app (.app (.app (.const ``Functor.map _)
      (.app (.const ``Sparkle.Core.Signal.Signal _) _))
      (.app (.const ``Sparkle.Core.Signal.instFunctorSignal _) _))
      (.app (.const ``BitVec _) wsE)) (.app (.const ``BitVec _) lenE))
      (.lam _ _ (.app (.app (.app (.app (.const ``BitVec.extractLsb' _) wsE') startE) lenE')
        (.bvar 0)) _)) a =>
    match canonicalNatLitValue? wsE, canonicalNatLitValue? lenE, canonicalNatLitValue? wsE',
        canonicalNatLitValue? startE, canonicalNatLitValue? lenE' with
    | some ws, some len, some ws', some start, some len' =>
      if 0 < len && ws' == ws && len' == len && decide (start + len ≤ ws) then
        some (ws, start, len, a)
      else none
    | _, _, _, _, _ => none
  | _ => none

/-- The six-argument shapes beside the canonical operators — a constant
    applied to three types, an instance and two operands: the result width,
    and for each of the two operands the width the gates require of it when
    it is a Signal they recurse into (a literal operand, and the function of
    a `<$>`, are not).  Concatenations, and the `<$>` slice. -/
def sixArgShape? (e : Lean.Expr) : Option (Nat × Option Nat × Option Nat) :=
  match canonicalConcat? e with
  | some (m, n, _, _) => some (m + n, some m, some n)
  | none =>
    match canonicalConcatLit? e with
    | some (true, k, _, w, _, _) => some (k + w, none, some w)
    | some (false, k, _, w, _, _) => some (w + k, some w, none)
    | none =>
      match canonicalSliceF? e with
      | some (ws, _, len, _) => some (len, none, some ws)
      | none => none

/-- The target width of a canonical width-changing root: a `setWidth` cast,
    a slice, or a literal-prefix zero-extension. -/
def canonicalSetWidthTop? (e : Lean.Expr) : Option Nat :=
  match canonicalSetWidth? e with
  | some (_, wt, _) => some wt
  | none =>
    match canonicalSlice? e with
    | some (_, _, len, _) => some len
    | none =>
      match canonicalZextMap? e with
      | some (ws, k, _) => some (k + ws)
      | none => none

/-- Canonical register: `Signal.register initLit s` at a literal positive
    width, restricted to a POLYMORPHIC domain binder (`.fvar`/`.bvar`). A
    concrete domain keeps the legacy handler, whose reset kind comes from
    evaluating the domain — the polymorphic fallback there is asynchronous,
    which is exactly what the total lowering emits. Returns
    `(width, init value, input)`. -/
def canonicalRegister? : Lean.Expr → Option (Nat × Nat × Lean.Expr)
  | .app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.register _) dom)
      (.app (.const ``BitVec _) wE)) initE) a =>
    if dom.isFVar || dom.isBVar then
      match canonicalNatLitValue? wE, bitVecLitValue? initE with
      | some w, some (wi, v) => if 0 < w && wi == w then some (w, v, a) else none
      | _, _ => none
    else none
  | _ => none

/-- Canonical feedback register: `Signal.loop (fun s => Signal.register
    initLit cone)` over a polymorphic domain at a literal positive width.
    Returns `(width, init value, cone)`; the cone is the under-binder body,
    reading the register output as `.bvar 0`. -/
def canonicalLoopRegister? : Lean.Expr → Option (Nat × Nat × Lean.Expr)
  | .app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.loop _) dom)
      (.app (.const ``BitVec _) wE)) _inst)
      (.lam _ _ (.app (.app (.app (.app
        (.const ``Sparkle.Core.Signal.Signal.register _) _)
        (.app (.const ``BitVec _) wE2)) initE) cone) _) =>
    if dom.isFVar || dom.isBVar then
      match canonicalNatLitValue? wE, canonicalNatLitValue? wE2, bitVecLitValue? initE with
      | some w, some w2, some (wi, v) =>
        if 0 < w && w2 == w && wi == w then some (w, v, cone) else none
      | _, _, _ => none
    else none
  | _ => none

/-- Canonical single-port sync-read memory: `Signal.memory wa wd wen ra`
    over a polymorphic domain at literal positive widths. Returns
    `(addrWidth, dataWidth)`; the four operands stay in the application. -/
def canonicalMemory? : Lean.Expr → Option (Nat × Nat)
  | .app (.app (.app (.app (.app (.app (.app
      (.const ``Sparkle.Core.Signal.Signal.memory _) dom) awE) dwE) _wa) _wd) _wen) _ra =>
    if dom.isFVar || dom.isBVar then
      match canonicalNatLitValue? awE, canonicalNatLitValue? dwE with
      | some aw, some dw => if 0 < aw && 0 < dw then some (aw, dw) else none
      | _, _ => none
    else none
  | _ => none

/-- Rewrite the canonical single-slot `circuit do` cone into the loop-binder
    form: every coerced register read `Prod.fst _ _ r` becomes the binder
    itself, and the vanished `RegList` binder's index is squeezed out.
    Fails if the register handle or the handle tuple is used any other
    way (`d` is the current index of the handle binder). -/
def cdoConeToLoop : Nat → Lean.Expr → Option Lean.Expr
  | d, .app (.app (.app (.const ``Prod.fst us) tyA) tyB) (.bvar i) =>
    if i == d then some (.bvar d)
    else if i == d + 1 then none
    else do
      let tyA' ← cdoConeToLoop d tyA
      let tyB' ← cdoConeToLoop d tyB
      some (mkApp3 (.const ``Prod.fst us) tyA' tyB'
        (.bvar (if i > d + 1 then i - 1 else i)))
  | d, .bvar i =>
    if i == d || i == d + 1 then none
    else some (.bvar (if i > d + 1 then i - 1 else i))
  | d, .app f a => do some (.app (← cdoConeToLoop d f) (← cdoConeToLoop d a))
  | d, .lam n t b bi => do
    some (.lam n (← cdoConeToLoop d t) (← cdoConeToLoop (d + 1) b) bi)
  | d, .forallE n t b bi => do
    some (.forallE n (← cdoConeToLoop d t) (← cdoConeToLoop (d + 1) b) bi)
  | d, .letE n t v b nd => do
    some (.letE n (← cdoConeToLoop d t) (← cdoConeToLoop d v)
      (← cdoConeToLoop (d + 1) b) nd)
  | d, .mdata m b => do some (.mdata m (← cdoConeToLoop d b))
  | d, .proj st i b => do some (.proj st i (← cdoConeToLoop d b))
  | _, e => some e

/-- Canonical single-slot `circuit do`: `runCircuitH` at one `BitVec w` slot
    over a polymorphic domain, the projection-destructured handle, exactly
    one register write, and the register's own read returned. Yields
    `(width, init value, cone)` with the cone already in the loop-binder
    form (`.bvar 0` = the register read), so the certified feedback-register
    lowering applies unchanged. -/
def canonicalCircuitDo? : Lean.Expr → Option (Nat × Nat × Lean.Expr)
  | .app (.app (.app (.app (.app (.app (.app (.app
      (.const ``Sparkle.Core.runCircuitH _) dom)
      (.app (.app (.app (.const ``List.cons _) _) (.app (.const ``BitVec _) wE))
        (.app (.const ``List.nil _) _))) _) _) _) _)
      (.app (.app (.app (.app (.const ``Prod.mk _) _) _) initE) (.const ``Unit.unit _)))
      (.lam _ _ (.letE _ _
        (.app (.app (.app (.const ``Prod.fst _) _) _) (.bvar 0))
        (.app (.app (.app (.app (.app (.app
            (.const ``Sparkle.Core.Circuit.bind _) _) _) _) _)
          (.app (.app (.app (.app (.app (.app
            (.const ``Sparkle.Core.Circuit.next _) _) _) _) _) (.bvar 0)) rhs))
          (.lam _ _
            (.app (.app (.app (.app (.const ``Sparkle.Core.Circuit.pure' _) _) _) _)
              (.app (.app (.app (.const ``Prod.fst _) _) _) (.bvar 1))) _)) _) _) =>
    if dom.isFVar || dom.isBVar then
      match canonicalNatLitValue? wE, bitVecLitValue? initE with
      | some w, some (wi, v) =>
        if 0 < w && wi == w then
          match cdoConeToLoop 0 rhs with
          | some cone => some (w, v, cone)
          | none => none
        else none
      | _, _ => none
    else none
  | _ => none

/-- Rewrite a two-slot `circuit do` cone into the two-state form: coerced
    reads of the first/second register handle become `.bvar 1`/`.bvar 0`,
    the `K` machinery binders (handle tuple, projected handles, spent
    continuations) vanish, and outer references shift accordingly. Fails if
    any machinery binder is used another way. -/
def cdo2ConeToLoop (dx dy K : Nat) : Nat → Lean.Expr → Option Lean.Expr
  | d, .app (.app (.app (.const ``Prod.fst us) tyA) tyB) (.bvar i) =>
    if i == dx + d then some (.bvar (d + 1))
    else if i == dy + d then some (.bvar d)
    else if d ≤ i && i < d + K then none
    else do
      let tyA' ← cdo2ConeToLoop dx dy K d tyA
      let tyB' ← cdo2ConeToLoop dx dy K d tyB
      some (mkApp3 (.const ``Prod.fst us) tyA' tyB'
        (.bvar (if i ≥ d + K then i - K + 2 else i)))
  | d, .bvar i =>
    if d ≤ i && i < d + K then none
    else some (.bvar (if i ≥ d + K then i - K + 2 else i))
  | d, .app f a => do some (.app (← cdo2ConeToLoop dx dy K d f) (← cdo2ConeToLoop dx dy K d a))
  | d, .lam n t b bi => do
    some (.lam n (← cdo2ConeToLoop dx dy K d t) (← cdo2ConeToLoop dx dy K (d + 1) b) bi)
  | d, .forallE n t b bi => do
    some (.forallE n (← cdo2ConeToLoop dx dy K d t) (← cdo2ConeToLoop dx dy K (d + 1) b) bi)
  | d, .letE n t v b nd => do
    some (.letE n (← cdo2ConeToLoop dx dy K d t) (← cdo2ConeToLoop dx dy K d v)
      (← cdo2ConeToLoop dx dy K (d + 1) b) nd)
  | d, .mdata m b => do some (.mdata m (← cdo2ConeToLoop dx dy K d b))
  | d, .proj st i b => do some (.proj st i (← cdo2ConeToLoop dx dy K d b))
  | _, e => some e

/-- The two-slot handle chain: `bind (next x rhs0) (fun _ => bind (next y
    rhs1) (fun _ => pure' (read (x|y))))`, with the handles at the fixed
    de-Bruijn indices the projection-destructuring produces. -/
def cdo2Chain? : Lean.Expr → Option (Nat × Lean.Expr × Lean.Expr)
  | .app (.app (.app (.app (.app (.app
      (.const ``Sparkle.Core.Circuit.bind _) _) _) _) _)
      (.app (.app (.app (.app (.app (.app
        (.const ``Sparkle.Core.Circuit.next _) _) _) _) _) (.bvar 2)) rhs0))
      (.lam _ _
        (.app (.app (.app (.app (.app (.app
            (.const ``Sparkle.Core.Circuit.bind _) _) _) _) _)
          (.app (.app (.app (.app (.app (.app
            (.const ``Sparkle.Core.Circuit.next _) _) _) _) _) (.bvar 1)) rhs1))
          (.lam _ _
            (.app (.app (.app (.app (.const ``Sparkle.Core.Circuit.pure' _) _) _) _)
              (.app (.app (.app (.const ``Prod.fst _) _) _) (.bvar outIdx))) _)) _) =>
    some (outIdx, rhs0, rhs1)
  | _ => none

/-- The two projected handles and the write/return chain under them. -/
def cdo2Body? : Lean.Expr → Option (Nat × Lean.Expr × Lean.Expr)
  | .lam _ _ (.letE _ _
      (.app (.app (.app (.const ``Prod.fst _) _) _) (.bvar 0))
      (.letE _ _
        (.app (.app (.app (.const ``Prod.snd _) _) _) (.bvar 1))
        (.letE _ _
          (.app (.app (.app (.const ``Prod.fst _) _) _) (.bvar 0))
          chain _) _) _) _ => cdo2Chain? chain
  | _ => none

/-- The nested two-slot initial-value pair. -/
def cdo2Inits? : Lean.Expr → Option (Lean.Expr × Lean.Expr)
  | .app (.app (.app (.app (.const ``Prod.mk _) _) _) init0E)
      (.app (.app (.app (.app (.const ``Prod.mk _) _) _) init1E)
        (.const ``Unit.unit _)) => some (init0E, init1E)
  | _ => none

/-- The two-slot type list `[BitVec w, BitVec w2]`. -/
def cdo2Slots? : Lean.Expr → Option (Lean.Expr × Lean.Expr)
  | .app (.app (.app (.const ``List.cons _) _) (.app (.const ``BitVec _) wE))
      (.app (.app (.app (.const ``List.cons _) _) (.app (.const ``BitVec _) wE2))
        (.app (.const ``List.nil _) _)) => some (wE, wE2)
  | _ => none

/-- Canonical two-slot `circuit do`: `runCircuitH` at two same-width
    `BitVec w` slots over a polymorphic domain, projection-destructured
    handles, one write per register, and one of the registers' own reads
    returned. Yields `(width, init0, init1, returned slot, cone0, cone1)`
    with both cones in the two-state form (`.bvar 1` = first register's
    read, `.bvar 0` = the second's). -/
def canonicalCircuitDo2? : Lean.Expr → Option (Nat × Nat × Nat × Nat × Lean.Expr × Lean.Expr)
  | .app (.app (.app (.app (.app (.app (.app (.app
      (.const ``Sparkle.Core.runCircuitH _) dom) slots) _) _) _) _) inits) body =>
    if !(dom.isFVar || dom.isBVar) then none else
    (match cdo2Slots? slots, cdo2Inits? inits, cdo2Body? body with
     | some (wE, wE2), some (init0E, init1E), some (outIdx, rhs0, rhs1) =>
       let retSlot := if outIdx == 4 then some 0 else if outIdx == 2 then some 1 else none
       (match retSlot with
        | none => none
        | some ret =>
          match canonicalNatLitValue? wE, canonicalNatLitValue? wE2,
              bitVecLitValue? init0E, bitVecLitValue? init1E with
          | some w, some w2, some (wi0, v0), some (wi1, v1) =>
            if !(0 < w && w2 == w && wi0 == w && wi1 == w) then none else
            (match cdo2ConeToLoop 2 0 4 0 rhs0, cdo2ConeToLoop 3 1 5 0 rhs1 with
             | some cone0, some cone1 => some (w, v0, v1, ret, cone0, cone1)
             | _, _ => none)
          | _, _, _, _ => none)
     | _, _, _ => none)
  | _ => none

/-- Canonical enabled register: `Signal.registerWithEnable initLit en input`
    over a polymorphic domain at a literal positive width. Returns
    `(width, init value, enable, input)`. -/
def canonicalRegisterEnable? : Lean.Expr → Option (Nat × Nat × Lean.Expr × Lean.Expr)
  | .app (.app (.app (.app (.app
      (.const ``Sparkle.Core.Signal.Signal.registerWithEnable _) dom)
      (.app (.const ``BitVec _) wE)) initE) enE) inpE =>
    if dom.isFVar || dom.isBVar then
      match canonicalNatLitValue? wE, bitVecLitValue? initE with
      | some w, some (wi, v) => if 0 < w && wi == w then some (w, v, enE, inpE) else none
      | _, _ => none
    else none
  | _ => none

/-- Exact canonical muxes need no MetaM result-type oracle. Kept as an action
    so the fallback inference still occurs after recursive child translation. -/
def muxResultType (e : Lean.Expr) : CompilerM HWType :=
  match canonicalMuxType? e with
  | some ty => pure ty
  | none => do
    let exprType ← cachedInferType e
    inferHWTypeFromSignal exprType

/-- The shipping mux sequence, with recursion and result-type inference exposed
    as arguments. Type inference runs after all three children, as in the
    original handler; in particular it observes their cache updates. -/
def translateMuxWith (translate : TranslateFn) (resultType : CompilerM HWType)
    (cond thenSig elseSig : Lean.Expr) (hint : String) (isNamed : Bool) : CompilerM String := do
  let cW ← translate cond "mux_cond" false false
  let tW ← translate thenSig "mux_then" false false
  let eW ← translate elseSig "mux_else" false false
  let hwType ← resultType
  emitMuxResult cW tW eW hint isNamed hwType

/-- Lower a canonical library Signal operator application. SHIPPING code:
    `translateExprToWireImpl` calls this with the real translator as
    `translate`. It is a plain (non-`partial`) definition so its behaviour can
    be proved about; the recursion it depends on is the `translate` argument.
    The result width comes from the instance's literal width argument when
    there is one (no MetaM oracle), else from the inferred type. -/
def translateCanonicalSignalBinary (translate : TranslateFn) (e : Lean.Expr)
    (op : Operator) (args : Array Lean.Expr) (isSignal1 isSignal2 : Bool)
    (hint : String) (isNamed : Bool) : CompilerM String := do
  let arg1 := args[args.size - 2]!
  let arg2 := args[args.size - 1]!
  let hwType ← match canonicalSignalBitVecWidth args with
    | some n => pure (HWType.bitVector n)
    | none => do
      let exprType ← cachedInferType e
      inferHWTypeFromSignal exprType
  let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
  -- For mixed Signal/BitVec: use extractBitVecLiteral for the constant arg
  let wireA ← if isSignal1 then
    translate arg1 "op_a" false false
  else do
    let (cVal, cWidth) ← extractBitVecLiteral arg1
    let constWire ← CompilerM.makeWire "op_const" (.bitVector cWidth)
    CompilerM.emitAssign constWire (.const (Int.ofNat cVal) cWidth)
    pure constWire
  let wireB ← if isSignal2 then
    translate arg2 "op_b" false false
  else do
    let (cVal, cWidth) ← extractBitVecLiteral arg2
    let constWire ← CompilerM.makeWire "op_const" (.bitVector cWidth)
    CompilerM.emitAssign constWire (.const (Int.ofNat cVal) cWidth)
    pure constWire
  CompilerM.emitAssign resWire (.op op [.ref wireA, .ref wireB])
  return resWire

/-- Split a return value of type ρ into a list of
    `(suggested-port-name, leaf-Lean-expr)` pairs at the
    Lean-expression level — one entry per `Signal dom τ` leaf
    under ρ.

    Handled shapes:
      * `Signal dom τ`     → one anonymous leaf carrying the
                             original expression.
      * `Prod α β`         → recursively split `Prod.fst e` /
                             `Prod.snd e` (positional names
                             `out_0`, `out_1`, …).
      * single-constructor inductive (i.e. user record) →
                             for each field, recurse on
                             `e.field` and prefix the field
                             name so each leaf gets a
                             human-readable port (`dmac`,
                             `payloadValid`, …).

    Falls back to `[(none, e)]` if the type doesn't match any
    of the above — that keeps non-Signal payloads round-
    tripping through the legacy single-wire path. -/
partial def splitReturnLeaves
    (e : Lean.Expr) (prefix? : Option String := none) :
    MetaM (Array (String × Lean.Expr)) := do
  -- If the body is still wrapped in lambdas (e.g. the top-
  -- level `def f (x : ...) : RxOut dom := …` whose params
  -- weren't opened by `openRecordInputs` because they were
  -- already flat Signals), peel through them so the per-leaf
  -- splitting sees the actual record value.  We re-wrap each
  -- leaf in the SAME lambda binders (one telescope, shared
  -- across leaves) so all leaves reference the same parameter
  -- fvars — otherwise downstream port-collection would see one
  -- input set per leaf (e.g. 6 leaves × 4 params = 24 ports).
  if e.isLambda then
    return ← Lean.Meta.lambdaTelescope e fun xs innerBody => do
      let innerLeaves ← splitReturnLeaves innerBody prefix?
      innerLeaves.mapM fun (n, leafE) => do
        let wrapped ← Lean.Meta.mkLambdaFVars xs leafE
        return (n, wrapped)
  let ty ← inferType e
  let tyN ← whnf ty
  -- For multi-output (Prod / record) returns, reduce `e`
  -- once at the top of the recursion so the per-field arms
  -- below see a concrete `Prod.mk` / ctor application
  -- instead of paying the body-whnf cost per leaf.  Skip
  -- the whnf for single-Signal returns to avoid peeling
  -- past `Signal.mk` and leaking its Stream binder into
  -- the wire context.
  let needsReduce :=
    (tyN.isAppOf ``Prod && tyN.getAppNumArgs == 2) ||
    (match tyN.getAppFn with
      | .const indName _ =>
        indName != ``Sparkle.Core.Signal.Signal
      | _ => false)
  let e ← if needsReduce then whnf e else pure e
  -- Signal dom τ — base case, one leaf.
  if tyN.isAppOf ``Sparkle.Core.Signal.Signal then
    let portName := prefix?.getD "out"
    return #[(portName, e)]
  -- Prod α β — recurse on .fst / .snd.
  if tyN.isAppOf ``Prod && tyN.getAppNumArgs == 2 then
    let lhsName := (prefix?.getD "out") ++ "_0"
    let rhsName := (prefix?.getD "out") ++ "_1"
    -- Cheap pre-reduce: when `e` is *literally* `Prod.mk a b
    -- c d` already (no whnf needed), hand `c` / `d` directly
    -- to the recursion.  Otherwise leave the `Prod.fst` /
    -- `Prod.snd` wrapper in place — the cost of `whnf` is
    -- O(body) at every leaf, which scales catastrophically
    -- for 6+ output records.  The Expr cache in
    -- translateExprToWire still memoises the body's wire so
    -- the wrapper case stays correct, just slower than the
    -- literal case.
    let lhsExpr ← if e.isAppOfArity ``Prod.mk 4
                  then pure (e.getArg! 2)
                  else mkAppM ``Prod.fst #[e]
    let rhsExpr ← if e.isAppOfArity ``Prod.mk 4
                  then pure (e.getArg! 3)
                  else mkAppM ``Prod.snd #[e]
    let lhsLeaves ← splitReturnLeaves lhsExpr (some lhsName)
    let rhsLeaves ← splitReturnLeaves rhsExpr (some rhsName)
    return lhsLeaves ++ rhsLeaves
  -- Single-ctor inductive (records like `RxOut dom`) —
  -- recurse on each field, prefixing the field name so the
  -- emitted Verilog ports are human-readable.
  if let .const indName _ := tyN.getAppFn then
    if let some indVal ← (try some <$> getConstInfoInduct indName catch _ => pure none) then
      if indVal.ctors.length == 1 && !indVal.isRec then
        let ctorName := indVal.ctors.head!
        let ctorInfo ← getConstInfoCtor ctorName
        let nParams := indVal.numParams
        let mut acc : Array (String × Lean.Expr) := #[]
        let fieldNames ← forallTelescopeReducing ctorInfo.type fun args _ => do
          let mut ns : Array Name := #[]
          for f in args.toList.drop nParams do
            ns := ns.push (← f.fvarId!.getUserName)
          return ns
        -- `e` is already whnf'd at the top of splitReturnLeaves
        -- (above), so check the ctor head directly.
        let ctorArgs? :=
          if e.isAppOf ctorName then
            some (e.getAppArgs.toList.drop nParams |>.toArray)
          else
            none
        for (fName, idx) in fieldNames.zipIdx do
          let fieldExpr ← match ctorArgs? with
            | some args =>
              if h : idx < args.size then
                pure args[idx]
              else
                pure e   -- shouldn't happen; defensive
            | none =>
              let projName := indName ++ fName
              try
                mkAppM projName #[e]
              catch _ =>
                pure e
          let combinedPrefix :=
            match prefix? with
            | none => fName.toString
            | some p => p ++ "_" ++ fName.toString
          let sub ← splitReturnLeaves fieldExpr (some combinedPrefix)
          acc := acc ++ sub
        return acc
  -- Anything else: treat as a single leaf with whatever name.
  return #[(prefix?.getD "out", e)]

/-- "Open" record-typed parameters at the synth boundary.

    For a function `body = fun (p₁ : T₁) (rec : MyRec) (p₂) => …`
    where `MyRec` is a single-constructor inductive whose
    fields are all `Signal …`, rewrite to
      `fun (p₁) (f₁ : F₁) (f₂ : F₂) … (p₂) =>
            body p₁ { f₁, f₂, … } p₂`
    so the IR elaborator sees per-field Signal inputs instead
    of an unsplittable record argument.

    Records with no Signal fields (or with non-Signal mixed
    in) are left untouched.  Recursion is one-level — a record
    whose fields are themselves records is partially opened
    (the outer record is unwrapped; inner records pass
    through).  Good enough for the common HFT-NIC case where
    each layer's `RxIn` is a flat record of Signals.

    Implementation: walk params with a worker that recurses
    *inside* successive `forallTelescopeReducing` callbacks so
    every fvar stays in scope when `mkLambdaFVars` runs at
    the deepest layer.  No IO.Ref shenanigans — the worker
    threads state purely. -/
partial def openRecordInputs (body : Lean.Expr) : MetaM Lean.Expr := do
  let bodyType ← inferType body
  forallTelescopeReducing bodyType fun params _ => do
    let inner := mkAppN body params
    -- Worker: walk the param list with accumulators for the
    -- output binders (in source order), substitution pairs
    -- (orig fvar → rebuilt record value), and an "anything
    -- opened?" flag.  We need to stay *inside* every
    -- `forallTelescopeReducing` cb we open so the field
    -- fvars remain in the local context when we finally call
    -- `mkLambdaFVars`.
    let rec walk
        (idx : Nat)
        (binders : Array Lean.Expr)
        (subst   : Array (Lean.FVarId × Lean.Expr))
        (opened  : Bool) : MetaM Lean.Expr := do
      if h : idx < params.size then
        let p := params[idx]
        let pType ← whnf (← inferType p)
        match pType.getAppFn with
        | .const indName _ =>
          let some indVal ← (try some <$> getConstInfoInduct indName catch _ => pure none)
            | walk (idx + 1) (binders.push p) subst opened
          unless indVal.ctors.length == 1 && !indVal.isRec do
            return ← walk (idx + 1) (binders.push p) subst opened
          let ctorName := indVal.ctors.head!
          let ctorInfo ← getConstInfoCtor ctorName
          let nParams := indVal.numParams
          let paramArgs := pType.getAppArgs.toList.take nParams |>.toArray
          let ctorType ← instantiateForall ctorInfo.type paramArgs
          forallTelescopeReducing ctorType fun fields _ => do
            -- Guard: only open records whose every field is
            -- `Signal _ _`.  Reg, Slot, Prod-as-state, etc.
            -- are technically single-ctor but opening them
            -- would split a register handle into its internal
            -- (Signal, Slot) pair and break the rest of the
            -- elaborator.  HFT-NIC `RxIn` / `RxOut` / similar
            -- shapes are all "flat Signal record"; that's
            -- exactly what we want to catch.
            let allSignalFields ← fields.allM fun f => do
              let fT ← whnf (← inferType f)
              return fT.isAppOf ``Sparkle.Core.Signal.Signal
            if !allSignalFields then
              walk (idx + 1) (binders.push p) subst opened
            else
              let recVal := mkAppN (.const ctorName (ctorInfo.levelParams.map Level.param))
                              (paramArgs ++ fields)
              walk (idx + 1)
                (binders ++ fields)
                (subst.push (p.fvarId!, recVal))
                true
        | _ => walk (idx + 1) (binders.push p) subst opened
      else
        -- Reached the end of the param list.  If nothing was
        -- opened, return the original `body` as-is; otherwise
        -- apply the accumulated substitution and close.
        if !opened then return body
        let mut substituted := inner
        for (origFvarId, recVal) in subst do
          substituted := substituted.replaceFVarId origFvarId recVal
        mkLambdaFVars binders substituted
    walk 0 #[] #[] false

/-- Deep-strip every `Signal.memoize x` sub-expression to `x`
    in a Lean expression tree.  `Signal.memoize` is a sim-only
    identity wrapper used by Compiler C2 to cache per-cycle
    register reads; for synthesis it serves no purpose and
    causes infinite-loop hangs in FSM-shaped circuits where
    register-read → register-write → memoize chain re-enters
    via Signal.loop body inlining.  Stripping them once at
    the synth entry point breaks the cycle definitively.

    Implementation: post-order traversal — strip children
    first, then check if THIS node is `Signal.memoize` and
    unwrap if so.  Does not recurse under binders (lambdas)
    because BVars under a binder have no fvar-binding yet and
    the memoize wrap there will be handled by Signal.loop's
    handler when it instantiates the binder. -/
partial def stripMemoizeWrappers (e : Lean.Expr) : Lean.Expr := Id.run do
  let e' ← match e with
    | .app f a => pure (.app (stripMemoizeWrappers f) (stripMemoizeWrappers a))
    | .lam binderName binderTy body binderInfo =>
        pure (.lam binderName (stripMemoizeWrappers binderTy) body binderInfo)
    | .forallE binderName binderTy body binderInfo =>
        pure (.forallE binderName (stripMemoizeWrappers binderTy) body binderInfo)
    | .letE declName declTy declVal body nondep =>
        pure (.letE declName (stripMemoizeWrappers declTy) (stripMemoizeWrappers declVal) body nondep)
    | .mdata md sub => pure (.mdata md (stripMemoizeWrappers sub))
    | _ => pure e
  let fn := e'.getAppFn
  match fn with
  | .const constName _ =>
      if constName.toString.endsWith ".memoize" then
        let cArgs := e'.getAppArgs
        if cArgs.size >= 1 then
          return cArgs[cArgs.size - 1]!
      return e'
  | _ => return e'

/-! ### Building blocks of the synthesis entry

Plain (non-`partial`) definitions, shared by the two front ends below, so the
entry's behaviour can be proved about (Tools/ShippingEntrySoundness.lean). -/

/-- Bind one Signal-typed source binder to a fresh input port. -/
def bindInputPort {α : Type} (fvarId : FVarId) (binderName : String) (hwType : HWType)
    (k : CompilerM α) : CompilerM α := do
  let w ← CompilerM.makeWire binderName hwType (named := true)
  CompilerM.addInput w hwType
  CompilerM.withVarMapping fvarId w k

/-- Walk the telescope's fvars and wire each Signal-typed argument to a fresh
    input port; non-Signal binders (e.g. type-class instances) stay as local
    decls in the Meta context but don't become hardware ports. -/
def bindInputsLegacy (parameters : List (String × Nat)) (symbolicMode : Bool)
    (xs : Array Lean.Expr) (i : Nat) (k : CompilerM String) : CompilerM String := do
  if h : i < xs.size then
    let x := xs[i]
    let fvarId := x.fvarId!
    let decl ← CompilerM.liftMetaM fvarId.getDecl
    let binderName := decl.userName
    let binderType := decl.type
    let parameterDefault? :=
      (parameters.find? fun (name, _) => name == binderName.toString).map (·.2)
    match parameterDefault? with
    | some defaultValue =>
      CompilerM.addParameter binderName.toString defaultValue
      CompilerM.withDimVarMapping fvarId (.parameter binderName.toString)
        (bindInputsLegacy parameters symbolicMode xs (i + 1) k)
    | none =>
      let isSignalArg ← isSignalBinderType binderType
      if symbolicMode && isSignalArg then
        -- Do not catch failures here: an unretained width must report
        -- its symbolic-parameter diagnostic instead of disappearing.
        let hwType ← inferHWTypeFromSignal binderType
        bindInputPort fvarId binderName.toString hwType
          (bindInputsLegacy parameters symbolicMode xs (i + 1) k)
      else
        -- Preserve the legacy fallback for unusual concrete HW args.
        let isHWArg ← try
          let _ ← inferHWTypeFromSignal binderType
          pure true
        catch _ => pure false
        if isHWArg then
          let hwType ← inferHWTypeFromSignal binderType
          bindInputPort fvarId binderName.toString hwType
            (bindInputsLegacy parameters symbolicMode xs (i + 1) k)
        else
          bindInputsLegacy parameters symbolicMode xs (i + 1) k
  else
    k
termination_by xs.size - i

/-- Translate each return leaf and drive its output port.  A port name that is
    already a name of this module is refused: the port's `assign` would
    otherwise overwrite that wire. -/
def emitLeaves (translate : TranslateFn) (cacheRef : IO.Ref (Lean.ExprStructMap String))
    (logProf : String → IO Unit) :
    List (String × Lean.Expr) → Option String → Nat → CompilerM String
  | [], firstWire, _ => return firstWire.getD "out"
  | (portName, leafExpr) :: rest, firstWire, leafIdx => do
    let tLeaf0 ← CompilerM.liftMetaM IO.monoMsNow
    let callsBefore ← CompilerM.liftMetaM sparkleCallCounter.get
    let hitsBefore  ← CompilerM.liftMetaM sparkleCacheHits.get
    CompilerM.liftMetaM (logProf s!"[profile] leaf {leafIdx} ({portName}) translate starting (calls={callsBefore} hits={hitsBefore})")
    -- isTopLevel := false because the input ports are
    -- already declared by the binder walk — the per-leaf
    -- translator must NOT re-create them.
    let leafWire ← translate leafExpr portName false true
    let tLeaf1 ← CompilerM.liftMetaM IO.monoMsNow
    let callsAfter ← CompilerM.liftMetaM sparkleCallCounter.get
    let hitsAfter  ← CompilerM.liftMetaM sparkleCacheHits.get
    CompilerM.liftMetaM (logProf s!"[profile] leaf {leafIdx} ({portName}) translate {tLeaf1 - tLeaf0} ms (calls Δ={callsAfter - callsBefore} hits Δ={hitsAfter - hitsBefore})")
    -- Record the leaf-expr → wire mapping so subsequent
    -- leaves that share sub-expressions (the common
    -- `Signal.loop` body in a multi-output return) reuse
    -- the wire instead of re-walking the whole tree.
    if !leafExpr.isFVar then
      CompilerM.liftMetaM (cacheRef.modify (·.insert ⟨leafExpr⟩ leafWire))
    let cs ← get
    if cs.usedNames.contains portName then
      throw (Exception.error .missing
        m!"output port name '{portName}' is already a name of this module")
    let wireDecl := cs.module.wires.find? (fun (p : Port) => p.name == leafWire)
    let outputType := match wireDecl with
      | some decl => decl.ty
      | none =>
        match cs.module.inputs.find? (fun p => p.name == leafWire) with
        | some inputPort => inputPort.ty
        | none => .bitVector 8
    CompilerM.addOutput portName outputType
    CompilerM.emitAssign portName (.ref leafWire)
    emitLeaves translate cacheRef logProf rest
      (if firstWire.isNone then some leafWire else firstWire) (leafIdx + 1)

/-- A sequential body needs clock and reset ports.  Idempotent: a sub-module
    instance handler may have already declared clk/rst (a
    `@[hardware_module]` sub-module requires the parent to expose the same
    clock/reset). -/
def addClockResetIfSequential (module : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  let hasRegisters := module.body.any (fun stmt =>
    match stmt with
    | .register .. => true
    | .memory .. => true
    | _ => false)
  if hasRegisters then
    let module :=
      if !module.inputs.any (·.name == "clk") then module.addInput { name := "clk", ty := .bit }
      else module
    if !module.inputs.any (·.name == "rst") then module.addInput { name := "rst", ty := .bit }
    else module
  else module

/-- Close the builder's module: retained-parameter checks, clock/reset, then
    `finalize` (addInput / addOutput / addWire / addStmt all use O(1)
    head-prepend during the synth loop; `finalize` reverses each list once so
    downstream consumers see the natural forward order). -/
def finishSynth (declName : Name) (parameters : List (String × Nat)) (symbolicMode : Bool)
    (finalCircuitState : CircuitState) :
    MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
  let module := finalCircuitState.module
  if symbolicMode then
    if module.body.any fun stmt => match stmt with
        | .register .. | .memory .. | .inst .. => true
        | _ => false then
      throwError
        "Native symbolic-width synthesis currently supports combinational modules only"
    for (parameterName, _) in parameters do
      if !module.parameters.any (fun parameter => parameter.name == parameterName) then
        throwError
          s!"Requested retained hardware parameter '{parameterName}' was not added to module {declName}"
  if Sparkle.IR.ModuleNameCheck.check (module :: finalCircuitState.design.modules) then
    return ((addClockResetIfSequential module).finalize, finalCircuitState.design)
  else
    throw (Exception.error .missing
      m!"Invalid or colliding Verilog module names while synthesizing {declName}; names after Verilog normalization must be legal non-keyword identifiers and distinct raw names must remain distinct")

/-! ### The certified front end

For a declaration whose value is a lambda telescope of `DomainConfig` and
`Signal dom (BitVec n)` binders over a body built from those binders,
`Signal.pure` BitVec literals and the canonical library Signal operators that
`translateCore` lowers (`signalBinOpOf`: `+ - * &&& ||| ^^^ <<< >>>`) at one
literal width, the entry computes the telescope
PURELY instead of through `openRecordInputs` / `stripMemoizeWrappers` /
`lambdaTelescope` / `splitReturnLeaves`.  Those are `partial`, or rest on
`extern` primitives (`instantiateRev`), so nothing can be proved about them;
on this shape they compute the same thing (checked against the legacy front
end in Tests/Compiler/ShippingEntrySoundnessTest.lean and the Verilog corpus).
The binder walk, the translator and the leaf/port emission are the SAME code
as the legacy path. -/

/-- A binder the certified front end accepts. -/
inductive GateBinder where
  | domain
  | signal (width : Nat)
  deriving DecidableEq, Repr

/-- `DomainConfig`, or `Signal _ (BitVec n)` with a literal `n`. -/
def gateBinderKind? (ty : Lean.Expr) : Option GateBinder :=
  if ty.isConstOf ``Sparkle.Core.Domain.DomainConfig then some .domain
  else match ty with
    | .app (.app (.const ``Sparkle.Core.Signal.Signal _) _) (.app (.const ``BitVec _) wE) =>
      (natLitValue? wE).map GateBinder.signal
    | _ => none

/-- The declaration's lambda telescope: binders in source order, and the body
    with loose bound variables (`.bvar i` = the `i`-th binder from the end). -/
def gatePeel : Lean.Expr → Option (List (Name × GateBinder) × Lean.Expr)
  | .lam nm ty b _ =>
    match gateBinderKind? ty, gatePeel b with
    | some k, some (bs, body) => some ((nm, k) :: bs, body)
    | _, _ => none
  | e => some ([], e)

/-- The binder a loose bound variable refers to. -/
def gateBVar? (kinds : Array GateBinder) (i : Nat) : Option GateBinder :=
  if i < kinds.size then kinds[kinds.size - 1 - i]? else none

/-- The width of the body's top node, read syntactically. -/
def gateTopWidth? (kinds : Array GateBinder) (e : Lean.Expr) : Option Nat :=
  match e with
  | .bvar i =>
    match gateBVar? kinds i with
    | some (.signal n) => some n
    | _ => none
  | _ =>
    match e.getAppFn with
    | .const m _ =>
      if m == ``Sparkle.Core.Signal.Signal.pure then
        (e.getAppArgs.back?.bind bitVecLitValue?).map (·.1)
      else canonicalSignalBitVecWidth e.getAppArgs
    | _ => none

/-- The body shape: every node is a width-`n` Signal binder, a width-`n`
    `Signal.pure` literal, or a canonical width-`n` operator on two such
    nodes.  Exactly the forms `translateCore` handles without its fallback. -/
def gateBody (kinds : Array GateBinder) (n : Nat) : Lean.Expr → Bool
  | .bvar i => gateBVar? kinds i == some (.signal n)
  | e@(.app (.app _ a) b) =>
    match e.getAppFn with
    | .const m _ =>
      if m == ``Sparkle.Core.Signal.Signal.pure then
        match bitVecLitValue? b with
        | some (w, _) => w == n
        | none => false
      else
        match signalBinOpOf m, canonicalSignalBinKinds m e.getAppArgs,
            canonicalSignalBitVecWidth e.getAppArgs with
        | some _, some (true, true), some w => w == n && gateBody kinds n a && gateBody kinds n b
        | _, _, _ => false
    | _ => false
  | _ => false

/-- The certified front end's acceptance test: binders, body and top width. -/
def certifiedShape? (symbolicMode : Bool) (parameters : List (String × Nat)) :
    ConstantInfo → Option (List (Name × GateBinder) × Lean.Expr)
  | .defnInfo d =>
    if symbolicMode || !parameters.isEmpty then none else
    match gatePeel d.value with
    | some (bs, body) =>
      let kinds := (bs.map (·.2)).toArray
      match gateTopWidth? kinds body with
      | some n => if gateBody kinds n body then some (bs, body) else none
      | none => none
    | none => none
  | _ => none

/-- Scalar input kinds for the mixed Bool/BitVec certified entry. Kept separate
    from `GateBinder` so the existing uniform-width entry contract is unchanged. -/
inductive MixedGateBinder where
  | domain
  | bool
  | bits (width : Nat)
  deriving DecidableEq, Repr

def mixedGateBinderKind? (ty : Lean.Expr) : Option MixedGateBinder :=
  if ty.isConstOf ``Sparkle.Core.Domain.DomainConfig then some .domain
  else match ty with
    | .app (.app (.const ``Sparkle.Core.Signal.Signal _) _) (.const ``Bool _) => some .bool
    | .app (.app (.const ``Sparkle.Core.Signal.Signal _) _) (.app (.const ``BitVec _) wE) =>
      (canonicalNatLitValue? wE).bind fun n => if 0 < n then some (.bits n) else none
    | _ => none

def mixedGatePeel : Lean.Expr → Option (List (Name × MixedGateBinder) × Lean.Expr)
  | .lam nm ty body _ =>
    match mixedGateBinderKind? ty, mixedGatePeel body with
    | some kind, some (binders, e) => some ((nm, kind) :: binders, e)
    | _, _ => none
  | e => some ([], e)

def mixedGateBVar? (kinds : Array MixedGateBinder) (i : Nat) : Option MixedGateBinder :=
  if i < kinds.size then kinds[kinds.size - 1 - i]? else none

/-- Bool binders cannot be used as arithmetic inputs, including at width one. -/
def mixedBitKinds (kinds : Array MixedGateBinder) : Array GateBinder :=
  kinds.map fun k => match k with
    | .bits n => .signal n
    | _ => .domain

/-- Canonical same-width Signal comparisons returning Bool. -/
inductive SignalCompareKind where
  | ult | ule | slt | sle | eq
  deriving DecidableEq, BEq, Repr

/-- Preserve the existing unsigned comparison API. -/
instance : Coe Bool SignalCompareKind where
  coe le := if le then .ule else .ult

/-- Recognize equality derived from decidable equality on BitVec, rather than
an arbitrary user BEq. All DecidableEq inhabitants decide the same proposition. -/
def bitVecEqualityWidth? : Lean.Expr → Lean.Expr → Option Lean.Expr
  | .app (.const ``BitVec _) w,
      .app (.app (.const ``instBEqOfDecidableEq _) _) _ => some w
  | _, _ => none

/-- The standard Bool equality instance; custom BEq keeps its legacy meaning. -/
def isBoolEquality : Lean.Expr → Lean.Expr → Bool
  | .const ``Bool _, .app (.app (.const ``instBEqOfDecidableEq _) _) _ => true
  | _, _ => false

inductive SignalBoolBinKind where
  | band | bor | bxor
  deriving DecidableEq, BEq, Repr

def signalBoolBinName : SignalBoolBinKind → Name
  | .band => ``HAnd.hAnd
  | .bor => ``HOr.hOr
  | .bxor => ``HXor.hXor

def signalBoolBinInst : SignalBoolBinKind → Name
  | .band => ``Sparkle.Core.Signal.instHAndSignalBool
  | .bor => ``Sparkle.Core.Signal.instHOrSignalBool
  | .bxor => ``Sparkle.Core.Signal.instHXorSignalBool

def signalBoolBinOp : SignalBoolBinKind → Operator
  | .band => .and
  | .bor => .or
  | .bxor => .xor

/-- Only canonical Bool instances select the direct Boolean lowering. -/
def signalBoolBinKind? (method : Name) : Lean.Expr → Option SignalBoolBinKind
  | .app (.const inst _) _ =>
    if method == ``HAnd.hAnd && inst == ``Sparkle.Core.Signal.instHAndSignalBool then some .band
    else if method == ``HOr.hOr && inst == ``Sparkle.Core.Signal.instHOrSignalBool then some .bor
    else if method == ``HXor.hXor && inst == ``Sparkle.Core.Signal.instHXorSignalBool then some .bxor
    else none
  | _ => none

/-- The two-level Bool bodies of a lifted function the IP library writes:
    one operator applied to the two variables with one negation. -/
inductive AppBool2 where
  /-- `fun x y => x && !y` -/
  | andNot
  /-- `fun x y => !x && y` -/
  | notAnd
  /-- `fun x y => !(x || y)` -/
  | nor
  deriving DecidableEq, Repr

/-- A Bool-result binary operator lifted through the Signal applicative:
    `(BitVec.ule · ·) <$> a <*> b`, `(· && ·) <$> a <*> b`, …, or one of the
    two-level Bool bodies. -/
inductive AppBoolOp where
  | compare (k : SignalCompareKind) (n : Nat)
  | bool (k : SignalBoolBinKind)
  | two (f : AppBool2)
  deriving DecidableEq, Repr

/-- The two-argument lambda body of an applicative-lifted operator, read
    purely: its operands are exactly the two bound variables, in order.
    `αE` is the element type of the first operand. -/
def appBoolBody? : Lean.Expr → Lean.Expr → Option AppBoolOp
  | .app (.const ``BitVec _) wE, .app (.app (.app (.const m _) wE') (.bvar 1)) (.bvar 0) =>
    match canonicalNatLitValue? wE, canonicalNatLitValue? wE' with
    | some n, some n' =>
      if n' == n then
        if m == ``BitVec.ult then some (.compare .ult n)
        else if m == ``BitVec.ule then some (.compare .ule n)
        else if m == ``BitVec.slt then some (.compare .slt n)
        else if m == ``BitVec.sle then some (.compare .sle n)
        else none
      else none
    | _, _ => none
  | .app (.const ``BitVec _) wE,
      .app (.app (.app (.app (.const ``BEq.beq _) ty) inst) (.bvar 1)) (.bvar 0) =>
    match canonicalNatLitValue? wE, (bitVecEqualityWidth? ty inst).bind canonicalNatLitValue? with
    | some n, some n' => if n' == n then some (.compare .eq n) else none
    | _, _ => none
  | .const ``Bool _, .app (.app (.const m _) (.bvar 1)) (.bvar 0) =>
    if m == ``Bool.and then some (.bool .band)
    else if m == ``Bool.or then some (.bool .bor)
    else if m == ``Bool.xor then some (.bool .bxor)
    else none
  | .const ``Bool _, .app (.app (.const ``Bool.and _) (.bvar 1))
      (.app (.const ``Bool.not _) (.bvar 0)) => some (.two .andNot)
  | .const ``Bool _, .app (.app (.const ``Bool.and _) (.app (.const ``Bool.not _) (.bvar 1)))
      (.bvar 0) => some (.two .notAnd)
  | .const ``Bool _, .app (.const ``Bool.not _)
      (.app (.app (.const ``Bool.or _) (.bvar 1)) (.bvar 0)) => some (.two .nor)
  | _, _ => none

/-- An applicative-lifted Bool-result binary operator in the form the front
    end normalises `f <$> a <*> b` to — `Signal.ap (Signal.map f a) b`, which
    is also what the legacy translator reduces it to before lowering.
    Returns the operator and the two Signal operands. -/
def appBoolOp? : Lean.Expr → Option (AppBoolOp × Lean.Expr × Lean.Expr)
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.ap _) _) αE)
      (.const ``Bool _))
      (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map _) _) _) _)
        (.lam _ _ (.lam _ _ body _) _)) a)) b =>
    (appBoolBody? αE body).map (·, a, b)
  | _ => none

/-- Total, syntax-only recognition of the mixed Bool-output source fragment.
    Recursion follows actual expression subterms; type inference is not called. -/
def mixedGateBoolBody (kinds : Array MixedGateBinder) : Lean.Expr → Bool
  | .bvar i => mixedGateBVar? kinds i == some .bool
  | .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.pure _) _) (.const ``Bool _))
      (.const ``Bool.true _) => true
  | .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.pure _) _) (.const ``Bool _))
      (.const ``Bool.false _) => true
  | .app (.app (.app (.const ``Complement.complement _) _)
      (.app (.const ``Sparkle.Core.Signal.instComplementSignalBool _) _)) a =>
      mixedGateBoolBody kinds a
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.mux _) _) (.const ``Bool _)) c) a) b =>
      mixedGateBoolBody kinds c && mixedGateBoolBody kinds a && mixedGateBoolBody kinds b
  | .app (.app (.app (.app (.app (.app (.const m _) _) _) _) inst) a) b =>
      (signalBoolBinKind? m inst).isSome && mixedGateBoolBody kinds a && mixedGateBoolBody kinds b
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.beq _) ty) _) inst) a) b =>
      if isBoolEquality ty inst then mixedGateBoolBody kinds a && mixedGateBoolBody kinds b else
      match bitVecEqualityWidth? ty inst with
      | some wE => match canonicalNatLitValue? wE with
        | some n => 0 < n && gateBody (mixedBitKinds kinds) n a && gateBody (mixedBitKinds kinds) n b
        | none => false
      | none => false
  | .app (.app (.app (.app (.const m _) _) wE) a) b =>
      if m == ``Sparkle.Core.Signal.Signal.ult || m == ``Sparkle.Core.Signal.Signal.ule ||
          m == ``Sparkle.Core.Signal.Signal.slt || m == ``Sparkle.Core.Signal.Signal.sle then
        match canonicalNatLitValue? wE with
        | some n => 0 < n && gateBody (mixedBitKinds kinds) n a && gateBody (mixedBitKinds kinds) n b
        | none => false
      else false
  | _ => false

/-- Same-width BitVec mux trees with the existing arithmetic leaves and Bool
conditions. Arithmetic/comparison parents of vector muxes need a later mutually
recursive source extension. -/
def mixedGateVectorBody (kinds : Array MixedGateBinder) (n : Nat) : Lean.Expr → Bool
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.mux _) _)
      (.app (.const ``BitVec _) w)) c) a) b =>
    canonicalNatLitValue? w == some n && mixedGateBoolBody kinds c &&
      mixedGateVectorBody kinds n a && mixedGateVectorBody kinds n b
  | e => gateBody (mixedBitKinds kinds) n e

mutual

/-- Unified mutually recursive source recognition: vector muxes may sit under
    canonical arithmetic/comparison parents and vice versa. Purely syntactic,
    total, and recursing on actual subterms; type inference is not called. -/
def unifiedGateBoolBody (kinds : Array MixedGateBinder) : Lean.Expr → Bool
  | .bvar i => mixedGateBVar? kinds i == some .bool
  | .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.pure _) _) (.const ``Bool _))
      (.const ``Bool.true _) => true
  | .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.pure _) _) (.const ``Bool _))
      (.const ``Bool.false _) => true
  | .app (.app (.app (.const ``Complement.complement _) _)
      (.app (.const ``Sparkle.Core.Signal.instComplementSignalBool _) _)) a =>
      unifiedGateBoolBody kinds a
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.mux _) _) (.const ``Bool _)) c) a) b =>
      unifiedGateBoolBody kinds c && unifiedGateBoolBody kinds a && unifiedGateBoolBody kinds b
  | .app (.app (.app (.app (.app (.app (.const m _) _) _) _) inst) a) b =>
      (signalBoolBinKind? m inst).isSome && unifiedGateBoolBody kinds a && unifiedGateBoolBody kinds b
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.beq _) ty) _) inst) a) b =>
      if isBoolEquality ty inst then unifiedGateBoolBody kinds a && unifiedGateBoolBody kinds b else
      match bitVecEqualityWidth? ty inst with
      | some wE => match canonicalNatLitValue? wE with
        | some n => 0 < n && unifiedGateBitsBody kinds n a && unifiedGateBitsBody kinds n b
        | none => false
      | none => false
  | .app (.app (.app (.app (.const m _) _) wE) a) b =>
      if m == ``Sparkle.Core.Signal.Signal.ult || m == ``Sparkle.Core.Signal.Signal.ule ||
          m == ``Sparkle.Core.Signal.Signal.slt || m == ``Sparkle.Core.Signal.Signal.sle then
        match canonicalNatLitValue? wE with
        | some n => 0 < n && unifiedGateBitsBody kinds n a && unifiedGateBitsBody kinds n b
        | none => false
      else false
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.ap _) _) αE)
      (.const ``Bool _))
      (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map _) _) _) _)
        (.lam _ _ (.lam _ _ body _) _)) a)) b =>
      match appBoolBody? αE body with
      | some (.compare _ n) =>
        0 < n && unifiedGateBitsBody kinds n a && unifiedGateBitsBody kinds n b
      | some (.bool _) => unifiedGateBoolBody kinds a && unifiedGateBoolBody kinds b
      | some (.two _) => unifiedGateBoolBody kinds a && unifiedGateBoolBody kinds b
      | none => false
  | _ => false

def unifiedGateBitsBody (kinds : Array MixedGateBinder) (n : Nat) : Lean.Expr → Bool
  | .bvar i => mixedGateBVar? kinds i == some (.bits n)
  | .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.pure _) _) _) c =>
      match bitVecLitValue? c with
      | some (w, _) => w == n
      | none => false
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.mux _) _)
      (.app (.const ``BitVec _) w)) c) a) b =>
      canonicalNatLitValue? w == some n && unifiedGateBoolBody kinds c &&
        unifiedGateBitsBody kinds n a && unifiedGateBitsBody kinds n b
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map _) _)
      (.app (.const ``BitVec _) wsE)) (.app (.const ``BitVec _) wtE))
      (.app (.app (.const ``BitVec.setWidth _) wsE') wtE')) a =>
      canonicalNatLitValue? wtE == some n && canonicalNatLitValue? wtE' == some n &&
      (match canonicalNatLitValue? wsE, canonicalNatLitValue? wsE' with
       | some ws, some ws' => ws' == ws && 0 < ws && unifiedGateBitsBody kinds ws a
       | _, _ => false)
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map _) _)
      (.app (.const ``BitVec _) wsE)) (.app (.const ``BitVec _) lenE))
      (.lam _ _ (.app (.app (.app (.app (.const ``BitVec.extractLsb' _) wsE') startE) lenE')
        (.bvar 0)) _)) a =>
      canonicalNatLitValue? lenE == some n && canonicalNatLitValue? lenE' == some n &&
      (match canonicalNatLitValue? wsE, canonicalNatLitValue? wsE',
          canonicalNatLitValue? startE with
       | some ws, some ws', some start =>
         ws' == ws && 0 < n && decide (start + n ≤ ws) && unifiedGateBitsBody kinds ws a
       | _, _, _ => false)
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map _) _)
      (.app (.const ``BitVec _) wsE)) (.app (.const ``BitVec _) wtE))
      (.lam _ _ (.app (.app (.app (.app (.const ``BitVec.append _) kE) wsE')
        (.app (.app (.const ``BitVec.ofNat _) kL) zL)) (.bvar 0)) _)) a =>
      canonicalNatLitValue? wtE == some n &&
      (match canonicalNatLitValue? wsE, canonicalNatLitValue? kE, canonicalNatLitValue? wsE',
          canonicalNatLitValue? kL, canonicalNatLitValue? zL with
       | some ws, some k, some ws', some kl, some z =>
         0 < ws && 0 < k && n == k + ws && ws' == ws && kl == k && z == 0 &&
           unifiedGateBitsBody kinds ws a
       | _, _, _, _, _ => false)
  | e@(.app (.app (.app (.app (.app (.app (.const m _) _) _) _) _) a) b) =>
      match signalBinOpOf m, canonicalSignalBinKinds m e.getAppArgs,
          canonicalSignalBitVecWidth e.getAppArgs with
      | some _, some (true, true), some w =>
        w == n && unifiedGateBitsBody kinds n a && unifiedGateBitsBody kinds n b
      | _, _, _ =>
        -- The other six-argument shapes: the Signal operands at their own
        -- widths.
        match sixArgShape? e with
        | some (r, ga, gb) =>
          n == r &&
            (match ga with | some m => unifiedGateBitsBody kinds m a | none => true) &&
            (match gb with | some k => unifiedGateBitsBody kinds k b | none => true)
        | none => false
  | _ => false

end

/-- Root acceptance for the unified fragment; the width comes from the same
    syntactic sources as the established vector gate, and for a concatenation
    root from its two operand widths. -/
def unifiedGateRoot (kinds : Array MixedGateBinder) (e : Lean.Expr) : Bool :=
  unifiedGateBoolBody kinds e ||
    (match sixArgShape? e with
      | some (r, _, _) => unifiedGateBitsBody kinds r e
      | none => false) ||
    (match canonicalMuxType? e with
      | some (.bitVector n) => 0 < n && unifiedGateBitsBody kinds n e
      | _ =>
        match gateTopWidth? (mixedBitKinds kinds) e with
        | some n => 0 < n && unifiedGateBitsBody kinds n e
        | none =>
          match canonicalSetWidthTop? e with
          | some n => 0 < n && unifiedGateBitsBody kinds n e
          | none => false)

def mixedGateVectorWidth? (kinds : Array MixedGateBinder) (e : Lean.Expr) : Option Nat :=
  match canonicalMuxType? e with
  | some (.bitVector n) => some n
  | _ => gateTopWidth? (mixedBitKinds kinds) e

def mixedGateVectorRoot (kinds : Array MixedGateBinder) (e : Lean.Expr) : Bool :=
  match mixedGateVectorWidth? kinds e with
  | some n => 0 < n && mixedGateVectorBody kinds n e
  | none => false

/-- Root acceptance for a canonical register over the unified combinational
    fragment: the whole declaration body is one register whose input is a
    recognized width-`w` source. -/
def unifiedRegisterRoot (kinds : Array MixedGateBinder) (e : Lean.Expr) : Bool :=
  match canonicalRegister? e with
  | some (w, _, a) =>
    -- A recognized width-`w` source, or one more cascaded register stage
    -- (a shift chain of depth two) over such a source.
    0 < w && (unifiedGateBitsBody kinds w a ||
      match canonicalRegister? a with
      | some (w2, _, a2) => w2 == w && unifiedGateBitsBody kinds w a2
      | none => false)
  | none =>
    match canonicalRegisterEnable? e with
    | some (w, _, en, a) =>
      0 < w && unifiedGateBoolBody kinds en && unifiedGateBitsBody kinds w a
    | none =>
      match canonicalLoopRegister? e with
      | some (w, _, cone) =>
        -- The loop binder is one more width-`w` input, at `.bvar 0`.
        0 < w && unifiedGateBitsBody (kinds.push (.bits w)) w cone
      | none =>
        match canonicalCircuitDo? e with
        | some (w, _, cone) =>
          -- The single-slot circuit-do cone, already in loop-binder form.
          0 < w && unifiedGateBitsBody (kinds.push (.bits w)) w cone
        | none =>
          match canonicalCircuitDo2? e with
          | some (w, _, _, _, cone0, cone1) =>
            -- Two more width-`w` inputs: slot 0 at `.bvar 1`, slot 1 at `.bvar 0`.
            0 < w && unifiedGateBitsBody ((kinds.push (.bits w)).push (.bits w)) w cone0 &&
              unifiedGateBitsBody ((kinds.push (.bits w)).push (.bits w)) w cone1
          | none => false

/-- The canonical memory root: `Signal.memory` whose four operands are
    bare input binders of the matching kinds. -/
def unifiedMemoryRoot (kinds : Array MixedGateBinder) (e : Lean.Expr) : Bool :=
  match e with
  | .app (.app (.app (.app (.app (.app (.app
      (.const ``Sparkle.Core.Signal.Signal.memory _) dom) awE) dwE)
      wa) wd) wen) ra =>
    (dom.isFVar || dom.isBVar) &&
    (match canonicalNatLitValue? awE, canonicalNatLitValue? dwE with
     | some aw, some dw =>
       0 < aw && 0 < dw &&
       unifiedGateBitsBody kinds aw wa && unifiedGateBitsBody kinds dw wd &&
       unifiedGateBoolBody kinds wen && unifiedGateBitsBody kinds aw ra
     | _, _ => false)
  | _ => false

/-- The application spine of a canonical instance call: a constant head
    applied to input binders only (each a `.bvar` of a recognized kind,
    the domain binder included). Structural recursion keeps shape lemmas
    definitional. -/
def unifiedInstanceSpine (kinds : Array MixedGateBinder) : Lean.Expr → Bool
  | .const _ _ => true
  | .app f (.bvar i) => (mixedGateBVar? kinds i).isSome && unifiedInstanceSpine kinds f
  | _ => false

/-- The projection form of the instance root: a structure projection
    (constant head, the domain binder, then the record) applied to a
    canonical instance call. -/
def unifiedProjSpine (kinds : Array MixedGateBinder) : Lean.Expr → Bool
  | .app (.app (.const _ _) (.bvar i)) call =>
    (mixedGateBVar? kinds i).isSome && call.isApp && unifiedInstanceSpine kinds call
  | _ => false

/-- The application spine of an instance call whose arguments are input
    binders or, recursively, designated calls themselves (module pipelines:
    `stage2 (stage1 a) b`), after an optional closed-constant domain
    argument. Structural recursion. -/
def hierInstSpine (isInst : Lean.Expr → Bool) (kinds : Array MixedGateBinder) :
    Lean.Expr → Bool
  | .const _ _ => true
  -- A closed constant as the FIRST argument: the concrete clock domain of a
  -- wrapper written at a fixed domain (`childHW (dom := defaultDomain) a b`).
  | .app (.const _ _) (.const _ _) => true
  | .app f (.bvar i) => (mixedGateBVar? kinds i).isSome && hierInstSpine isInst kinds f
  | .app f a =>
    isInst a && a.isApp && hierInstSpine isInst kinds a && hierInstSpine isInst kinds f
  | _ => false

/-- A designated call whose arguments are binders or nested designated
    calls, as the whole declaration body. -/
def hierInstRoot (isInst : Lean.Expr → Bool) (kinds : Array MixedGateBinder)
    (e : Lean.Expr) : Bool :=
  isInst e && e.isApp && hierInstSpine isInst kinds e

/-- The canonical sub-module instance root: a call to a designated
(`@[hardware_module]`) constant whose arguments are all input binders, or
a structure projection of such a call (a multi-output child). The
designation predicate comes from the caller — the attribute and the
projection table live in the environment, which the pure gate cannot read. -/
def unifiedInstanceRoot (isInst : Lean.Expr → Bool)
    (kinds : Array MixedGateBinder) (e : Lean.Expr) : Bool :=
  isInst e && e.isApp && (unifiedInstanceSpine kinds e || unifiedProjSpine kinds e)

mutual

/-- The unified recognizer over cones whose BitVec LEAVES may also be
    canonical instance calls (a designated constant applied to input
    binders). Same structure as the unified Bool/BitVec recognizers; the
    designation predicate comes from the caller. -/
def hierGateBoolBody (isInst : Lean.Expr → Bool) (kinds : Array MixedGateBinder) :
    Lean.Expr → Bool
  | .bvar i => mixedGateBVar? kinds i == some .bool
  | .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.pure _) _) (.const ``Bool _))
      (.const ``Bool.true _) => true
  | .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.pure _) _) (.const ``Bool _))
      (.const ``Bool.false _) => true
  | .app (.app (.app (.const ``Complement.complement _) _)
      (.app (.const ``Sparkle.Core.Signal.instComplementSignalBool _) _)) a =>
      hierGateBoolBody isInst kinds a
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.mux _) _) (.const ``Bool _)) c) a) b =>
      hierGateBoolBody isInst kinds c && hierGateBoolBody isInst kinds a && hierGateBoolBody isInst kinds b
  | .app (.app (.app (.app (.app (.app (.const m _) _) _) _) inst) a) b =>
      (signalBoolBinKind? m inst).isSome && hierGateBoolBody isInst kinds a && hierGateBoolBody isInst kinds b
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.beq _) ty) _) inst) a) b =>
      if isBoolEquality ty inst then hierGateBoolBody isInst kinds a && hierGateBoolBody isInst kinds b else
      match bitVecEqualityWidth? ty inst with
      | some wE => match canonicalNatLitValue? wE with
        | some n => 0 < n && hierGateBitsBody isInst kinds n a && hierGateBitsBody isInst kinds n b
        | none => false
      | none => false
  | .app (.app (.app (.app (.const m _) _) wE) a) b =>
      if m == ``Sparkle.Core.Signal.Signal.ult || m == ``Sparkle.Core.Signal.Signal.ule ||
          m == ``Sparkle.Core.Signal.Signal.slt || m == ``Sparkle.Core.Signal.Signal.sle then
        match canonicalNatLitValue? wE with
        | some n => 0 < n && hierGateBitsBody isInst kinds n a && hierGateBitsBody isInst kinds n b
        | none => false
      else false
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.ap _) _) αE)
      (.const ``Bool _))
      (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map _) _) _) _)
        (.lam _ _ (.lam _ _ body _) _)) a)) b =>
      match appBoolBody? αE body with
      | some (.compare _ n) =>
        0 < n && hierGateBitsBody isInst kinds n a && hierGateBitsBody isInst kinds n b
      | some (.bool _) => hierGateBoolBody isInst kinds a && hierGateBoolBody isInst kinds b
      | some (.two _) => hierGateBoolBody isInst kinds a && hierGateBoolBody isInst kinds b
      | none => false
  | _ => false

def hierGateBitsBody (isInst : Lean.Expr → Bool) (kinds : Array MixedGateBinder) (n : Nat) :
    Lean.Expr → Bool
  | .bvar i => mixedGateBVar? kinds i == some (.bits n)
  | .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.pure _) _) _) c =>
      match bitVecLitValue? c with
      | some (w, _) => w == n
      | none => false
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.mux _) _)
      (.app (.const ``BitVec _) w)) c) a) b =>
      canonicalNatLitValue? w == some n && hierGateBoolBody isInst kinds c &&
        hierGateBitsBody isInst kinds n a && hierGateBitsBody isInst kinds n b
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map _) _)
      (.app (.const ``BitVec _) wsE)) (.app (.const ``BitVec _) wtE))
      (.app (.app (.const ``BitVec.setWidth _) wsE') wtE')) a =>
      canonicalNatLitValue? wtE == some n && canonicalNatLitValue? wtE' == some n &&
      (match canonicalNatLitValue? wsE, canonicalNatLitValue? wsE' with
       | some ws, some ws' => ws' == ws && 0 < ws && hierGateBitsBody isInst kinds ws a
       | _, _ => false)
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map _) _)
      (.app (.const ``BitVec _) wsE)) (.app (.const ``BitVec _) lenE))
      (.lam _ _ (.app (.app (.app (.app (.const ``BitVec.extractLsb' _) wsE') startE) lenE')
        (.bvar 0)) _)) a =>
      canonicalNatLitValue? lenE == some n && canonicalNatLitValue? lenE' == some n &&
      (match canonicalNatLitValue? wsE, canonicalNatLitValue? wsE',
          canonicalNatLitValue? startE with
       | some ws, some ws', some start =>
         ws' == ws && 0 < n && decide (start + n ≤ ws) && hierGateBitsBody isInst kinds ws a
       | _, _, _ => false)
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map _) _)
      (.app (.const ``BitVec _) wsE)) (.app (.const ``BitVec _) wtE))
      (.lam _ _ (.app (.app (.app (.app (.const ``BitVec.append _) kE) wsE')
        (.app (.app (.const ``BitVec.ofNat _) kL) zL)) (.bvar 0)) _)) a =>
      canonicalNatLitValue? wtE == some n &&
      (match canonicalNatLitValue? wsE, canonicalNatLitValue? kE, canonicalNatLitValue? wsE',
          canonicalNatLitValue? kL, canonicalNatLitValue? zL with
       | some ws, some k, some ws', some kl, some z =>
         0 < ws && 0 < k && n == k + ws && ws' == ws && kl == k && z == 0 &&
           hierGateBitsBody isInst kinds ws a
       | _, _, _, _, _ => false)
  | e@(.app (.app (.app (.app (.app (.app (.const m _) _) _) _) _) a) b) =>
      match signalBinOpOf m, canonicalSignalBinKinds m e.getAppArgs,
          canonicalSignalBitVecWidth e.getAppArgs with
      | some _, some (true, true), some w =>
        w == n && hierGateBitsBody isInst kinds n a && hierGateBitsBody isInst kinds n b
      | _, _, _ =>
        match sixArgShape? e with
        | some (r, ga, gb) =>
          n == r &&
            (match ga with | some m => hierGateBitsBody isInst kinds m a | none => true) &&
            (match gb with | some k => hierGateBitsBody isInst kinds k b | none => true)
        | none => isInst e && hierInstSpine isInst kinds e
  | e => isInst e && e.isApp && hierInstSpine isInst kinds e

end



/-- Root acceptance for cones over instance leaves: the same width sources
    as `unifiedGateRoot`. -/
def hierGateRoot (isInst : Lean.Expr → Bool) (kinds : Array MixedGateBinder)
    (e : Lean.Expr) : Bool :=
  hierGateBoolBody isInst kinds e ||
    (match sixArgShape? e with
      | some (r, _, _) => hierGateBitsBody isInst kinds r e
      | none => false) ||
    (match canonicalMuxType? e with
      | some (.bitVector n) => 0 < n && hierGateBitsBody isInst kinds n e
      | _ =>
        match gateTopWidth? (mixedBitKinds kinds) e with
        | some n => 0 < n && hierGateBitsBody isInst kinds n e
        | none =>
          match canonicalSetWidthTop? e with
          | some n => 0 < n && hierGateBitsBody isInst kinds n e
          | none => false)

/-- The declaration's result is one scalar Signal (Bool or positive-width
    BitVec).  The certified single-output harness only covers these;
    record/multi-output parents stay on the legacy front end (which splits
    the return leaves), so the instance disjunct must not capture them. -/
def mixedGateResultScalar : Lean.Expr → Bool
  | .forallE _ _ b _ => mixedGateResultScalar b
  | e =>
    match mixedGateBinderKind? e with
    | some .bool => true
    | some (.bits _) => true
    | _ => false

def mixedCertifiedShape? (symbolicMode : Bool) (parameters : List (String × Nat))
    (ci : ConstantInfo)
    (isInst : Lean.Expr → Bool := fun _ => false) :
    Option (List (Name × MixedGateBinder) × Lean.Expr) :=
  match ci with
  | .defnInfo d =>
    if symbolicMode || !parameters.isEmpty then none else
    match mixedGatePeel d.value with
    | some (bs, body) =>
      if (unifiedInstanceRoot isInst (bs.map (·.2)).toArray body &&
            mixedGateResultScalar d.type) ||
          mixedGateBoolBody (bs.map (·.2)).toArray body ||
          mixedGateVectorRoot (bs.map (·.2)).toArray body ||
          unifiedGateRoot (bs.map (·.2)).toArray body ||
          unifiedRegisterRoot (bs.map (·.2)).toArray body ||
          unifiedMemoryRoot (bs.map (·.2)).toArray body ||
          (hierGateRoot isInst (bs.map (·.2)).toArray body &&
            mixedGateResultScalar d.type) ||
          (hierInstRoot isInst (bs.map (·.2)).toArray body &&
            mixedGateResultScalar d.type) then some (bs, body) else none
    | none => none
  | _ => none

/-- Replace the loose bound variables `≥ d` by `xs` (in `instantiateRev`
    order: `.bvar d` is the LAST element).  A pure twin of the `extern`
    `Expr.instantiateRev`, used only on certified-shape bodies (trees of the
    source's size). -/
def instFVars (xs : Array Lean.Expr) : Nat → Lean.Expr → Lean.Expr
  | d, .bvar i =>
    if i < d then .bvar i
    else if i - d < xs.size then xs[xs.size - 1 - (i - d)]!
    else .bvar (i - xs.size)
  | d, .app f a => .app (instFVars xs d f) (instFVars xs d a)
  | d, .lam n t b bi => .lam n (instFVars xs d t) (instFVars xs (d + 1) b) bi
  | d, .forallE n t b bi => .forallE n (instFVars xs d t) (instFVars xs (d + 1) b) bi
  | d, .letE n t v b nd =>
    .letE n (instFVars xs d t) (instFVars xs d v) (instFVars xs (d + 1) b) nd
  | d, .mdata m e => .mdata m (instFVars xs d e)
  | d, .proj s i e => .proj s i (instFVars xs d e)
  | _, e => e

/-- Bind the certified binders: a `DomainConfig` binder is not hardware, a
    `Signal dom (BitVec n)` binder becomes an `n`-bit input port. -/
def bindCertifiedInputs {α : Type} (k : CompilerM α) :
    List ((Name × GateBinder) × FVarId) → CompilerM α
  | [] => k
  | ((_, .domain), _) :: rest => bindCertifiedInputs k rest
  | ((nm, .signal n), id) :: rest =>
    bindInputPort id nm.toString (.bitVector n) (bindCertifiedInputs k rest)

/-- The compiler context a synthesis starts in. -/
def entryCompilerState (symbolicMode : Bool) (cacheRef : IO.Ref (Lean.ExprStructMap String)) :
    CompilerState :=
  { varMap := [], dimVarMap := [], symbolicMode := symbolicMode
  , clockWire := none, resetWire := none
  , exprCache := some cacheRef }

/-- The synthesis of a certified-shape declaration: fresh fvars for the
    binders (checked distinct), the body instantiated purely, then the shared
    binder walk, translator, leaf emission and module finish. -/
def synthesizeCertified (translate : TranslateFn) (logProf : String → IO Unit)
    (declName : Name) (bs : List (Name × GateBinder)) (body : Lean.Expr) :
    MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
  let ids ← bs.mapM fun _ => mkFreshFVarId
  if hids : ids.Nodup ∧ ids.length = bs.length then
    let innerBody := instFVars (ids.map Lean.Expr.fvar).toArray 0 body
    let cacheRef ← IO.mkRef ({} : Lean.ExprStructMap String)
    let compiler := bindCertifiedInputs
      (emitLeaves translate cacheRef logProf [("out", innerBody)] none 0) (bs.zip ids)
    let (_, finalCircuitState) ←
      (compiler.run (entryCompilerState false cacheRef)).run (CircuitM.init declName.toString)
    finishSynth declName [] false finalCircuitState
  else
    throw (Exception.error .missing "fresh free variables are not distinct")

/-- The mixed entry uses the same actual input binder as the legacy entry. -/
def bindMixedCertifiedInputs {α : Type} (k : CompilerM α) :
    List ((Name × MixedGateBinder) × FVarId) → CompilerM α
  | [] => k
  | ((_, .domain), _) :: rest => bindMixedCertifiedInputs k rest
  | ((nm, .bool), id) :: rest =>
    bindInputPort id nm.toString .bit (bindMixedCertifiedInputs k rest)
  | ((nm, .bits n), id) :: rest =>
    bindInputPort id nm.toString (.bitVector n) (bindMixedCertifiedInputs k rest)

def synthesizeMixedCertified (translate : TranslateFn) (logProf : String → IO Unit)
    (declName : Name) (bs : List (Name × MixedGateBinder)) (body : Lean.Expr) :
    MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
  let ids ← bs.mapM fun _ => mkFreshFVarId
  if hids : ids.Nodup ∧ ids.length = bs.length then
    let innerBody := instFVars (ids.map Lean.Expr.fvar).toArray 0 body
    let cacheRef ← IO.mkRef ({} : Lean.ExprStructMap String)
    let compiler := bindMixedCertifiedInputs
      (emitLeaves translate cacheRef logProf [("out", innerBody)] none 0) (bs.zip ids)
    let (_, finalCircuitState) ←
      (compiler.run (entryCompilerState false cacheRef)).run (CircuitM.init declName.toString)
    finishSynth declName [] false finalCircuitState
  else
    throw (Exception.error .missing "fresh free variables are not distinct")

/-! ## Front-end normalisation: unfolding user definitions

The legacy translator inlines a call to an untagged user definition at the
call site (`handleDefinitionUnfold`: `unfoldDefinition?`, then translate the
result).  The certified gates only read the declaration's own value, so a
declaration written with helpers misses them even when the unfolded body is a
certified shape.  The functions below unfold such calls PURELY — delta and
beta against the definitions of the run's environment — so the entry can
offer the unfolded value to the same gates.  They are total (fuel) and
budgeted (a node budget; exhaustion keeps the declaration on the legacy
route), and nothing here is used unless a gate accepts the result. -/

/-- Lift the loose bound variables `≥ c` by `k` (budgeted). -/
def inlLift (k : Nat) : Nat → Lean.Expr → Nat → Option (Lean.Expr × Nat)
  | _, _, 0 => none
  | c, .bvar i, b + 1 => some (if i < c then .bvar i else .bvar (i + k), b)
  | c, .app f a, b + 1 =>
    match inlLift k c f b with
    | some (f', b) =>
      match inlLift k c a b with
      | some (a', b) => some (.app f' a', b)
      | none => none
    | none => none
  | c, .lam n t body bi, b + 1 =>
    match inlLift k c t b with
    | some (t', b) =>
      match inlLift k (c + 1) body b with
      | some (body', b) => some (.lam n t' body' bi, b)
      | none => none
    | none => none
  | c, .letE n t v body nd, b + 1 =>
    match inlLift k c t b with
    | some (t', b) =>
      match inlLift k c v b with
      | some (v', b) =>
        match inlLift k (c + 1) body b with
        | some (body', b) => some (.letE n t' v' body' nd, b)
        | none => none
      | none => none
    | none => none
  | c, .forallE n t body bi, b + 1 =>
    match inlLift k c t b with
    | some (t', b) =>
      match inlLift k (c + 1) body b with
      | some (body', b) => some (.forallE n t' body' bi, b)
      | none => none
    | none => none
  | _, .mdata .., _ + 1 => none
  | _, .proj .., _ + 1 => none
  | _, e, b + 1 => some (e, b)

/-- Replace the loose bound variables `≥ d` by `xs` (`instantiateRev` order:
    `.bvar d` is the LAST element), lifting an argument placed under `d`
    binders.  Budgeted; metadata and primitive projections are refused. -/
def inlSubst (xs : Array Lean.Expr) : Nat → Lean.Expr → Nat → Option (Lean.Expr × Nat)
  | _, _, 0 => none
  | d, .bvar i, b + 1 =>
    if i < d then some (.bvar i, b)
    else if i - d < xs.size then
      (if d = 0 then some (xs[xs.size - 1 - (i - d)]!, b)
       else inlLift d 0 xs[xs.size - 1 - (i - d)]! b)
    else some (.bvar (i - xs.size), b)
  | d, .app f a, b + 1 =>
    match inlSubst xs d f b with
    | some (f', b) =>
      match inlSubst xs d a b with
      | some (a', b) => some (.app f' a', b)
      | none => none
    | none => none
  | d, .lam n t body bi, b + 1 =>
    match inlSubst xs d t b with
    | some (t', b) =>
      match inlSubst xs (d + 1) body b with
      | some (body', b) => some (.lam n t' body' bi, b)
      | none => none
    | none => none
  | d, .letE n t v body nd, b + 1 =>
    match inlSubst xs d t b with
    | some (t', b) =>
      match inlSubst xs d v b with
      | some (v', b) =>
        match inlSubst xs (d + 1) body b with
        | some (body', b) => some (.letE n t' v' body' nd, b)
        | none => none
      | none => none
    | none => none
  | d, .forallE n t body bi, b + 1 =>
    match inlSubst xs d t b with
    | some (t', b) =>
      match inlSubst xs (d + 1) body b with
      | some (body', b) => some (.forallE n t' body' bi, b)
      | none => none
    | none => none
  | _, .mdata .., _ + 1 => none
  | _, .proj .., _ + 1 => none
  | _, e, b + 1 => some (e, b)

/-- Beta: peel one `fun` per argument, substitute, apply what is left over. -/
def inlBeta (acc : Array Lean.Expr) : Lean.Expr → List Lean.Expr → Nat →
    Option (Lean.Expr × Nat)
  | .lam _ _ body _, a :: rest, b => inlBeta (acc.push a) body rest b
  | f, rest, b =>
    match inlSubst acc 0 f b with
    | some (f', b) => some (rest.foldl Lean.Expr.app f', b)
    | none => none

/-- Head and arguments of an application spine. -/
def inlSpine : Lean.Expr → List Lean.Expr → Lean.Expr × List Lean.Expr
  | .app f a, acc => inlSpine f (a :: acc)
  | h, acc => (h, acc)

/-- Map a budgeted rewrite over a list, threading the budget. -/
def inlMap (f : Lean.Expr → Nat → Option (Lean.Expr × Nat)) :
    List Lean.Expr → Nat → Option (List Lean.Expr × Nat)
  | [], b => some ([], b)
  | a :: rest, b =>
    match f a b with
    | some (a', b) =>
      match inlMap f rest b with
      | some (rest', b) => some (a' :: rest', b)
      | none => none
    | none => none

/-- Remove one binder from around an expression that does not use it: the
    loose bound variables above `c` drop by one; `none` when variable `c`
    itself occurs. -/
def inlDropBinder : Nat → Lean.Expr → Option Lean.Expr
  | c, .bvar i => if i < c then some (.bvar i) else if i = c then none else some (.bvar (i - 1))
  | c, .app f a =>
    match inlDropBinder c f, inlDropBinder c a with
    | some f', some a' => some (.app f' a')
    | _, _ => none
  | c, .lam n t body bi =>
    match inlDropBinder c t, inlDropBinder (c + 1) body with
    | some t', some body' => some (.lam n t' body' bi)
    | _, _ => none
  | c, .forallE n t body bi =>
    match inlDropBinder c t, inlDropBinder (c + 1) body with
    | some t', some body' => some (.forallE n t' body' bi)
    | _, _ => none
  | _, .letE .. => none
  | _, .mdata .. => none
  | _, .proj .. => none
  | _, e => some e

/-- Canonical binder names for the function of an applicative lift: its
    leading `fun` binders become `x1`, `x2`, …  (They are hygienic macro names
    in the elaborated term, different in every declaration.) -/
def inlCanonLam : Nat → Lean.Expr → Lean.Expr
  | k, .lam _ t body bi => .lam (Name.mkSimple ("x" ++ toString (k + 1))) t (inlCanonLam (k + 1) body) bi
  | _, e => e

/-- Canonical binder name `a` for every arrow of a function type. -/
def inlCanonPi : Lean.Expr → Lean.Expr
  | .forallE _ t body bi => .forallE `a t (inlCanonPi body) bi
  | e => e

/-- `f <$> a` at the library's `Functor (Signal dom)` instance, as the
    `Signal.map` application it is by definition, with canonical binder names.
    Used only for the function position of `<*>`: a bare `f <$> a` has its own
    legacy handler (other child hints) and is left as written. -/
def inlSignalMapOfFunctor : Lean.Expr → Option Lean.Expr
  | .app (.app (.app (.app (.app (.app (.const ``Functor.map (u :: _))
      (.app (.const ``Sparkle.Core.Signal.Signal _) dom))
      (.app (.const ``Sparkle.Core.Signal.instFunctorSignal _) dom')) α) β) f) a =>
    if dom' == dom then
      some (mkApp5 (.const ``Sparkle.Core.Signal.Signal.map [u]) dom α (inlCanonPi β)
        (inlCanonLam 0 f) a)
    else none
  | _ => none

/-- `mf <*> mx` at the library's own `Signal` instances, as the `Signal.ap`
    application it is by definition — the form the legacy translator reduces
    it to (`whnfUntil`) before lowering.  The `Unit` thunk around the second
    operand is removed, and an `f <$> a` in function position becomes
    `Signal.map f a`. -/
def inlSignalApplicative (n : Name) (ls : List Level) (args : List Lean.Expr) :
    Option Lean.Expr :=
  match ls, args with
  | u :: _, [.app (.const ``Sparkle.Core.Signal.Signal _) dom,
      .app (.app (.const ``Applicative.toSeq _) (.app (.const ``Sparkle.Core.Signal.Signal _) dom''))
        (.app (.const ``Sparkle.Core.Signal.instApplicativeSignal _) dom'),
      α, β, mf, .lam _ _ mx _] =>
    if n == ``Seq.seq && dom' == dom && dom'' == dom then
      (inlDropBinder 0 mx).map fun mx' =>
        mkApp5 (.const ``Sparkle.Core.Signal.Signal.ap [u]) dom α β
          ((inlSignalMapOfFunctor mf).getD mf) mx'
    else none
  | _, _ => none

/-- Head-normalise a record expression until an application of the
    constructor `ctor` appears, and return its arguments: zeta of the lets in
    front, delta-beta of the definitions `defs` names, beta of a `fun` head.
    This is what the legacy projection handler's `unfoldDefinition?` / `whnf`
    loop does to `(f a b).field` when `f` is a user definition ending in a
    structure instance. -/
def inlHeadCtor (defs : Name → Option Lean.Expr) (ctor : Name) :
    Nat → Lean.Expr → Nat → Option (List Lean.Expr × Nat)
  | 0, _, _ => none
  | _, _, 0 => none
  | fuel + 1, .letE _ _ v body _, b + 1 =>
    match inlSubst #[v] 0 body b with
    | some (e', b) => inlHeadCtor defs ctor fuel e' b
    | none => none
  | fuel + 1, e, b + 1 =>
    match inlSpine e [] with
    | (.const n ls, args) =>
      if n == ctor then some (args, b)
      else match (if ls.isEmpty then defs n else none) with
        | some v =>
          match inlBeta #[] v args b with
          | some (e', b) => inlHeadCtor defs ctor fuel e' b
          | none => none
        | none => none
    | (.lam n t body bi, a :: rest) =>
      match inlBeta #[] (.lam n t body bi) (a :: rest) b with
      | some (e', b) => inlHeadCtor defs ctor fuel e' b
      | none => none
    | _ => none

/-- Unfold every call whose head `defs` names: delta against the definition's
    value, beta against the call's arguments, then continue in the result.
    A projection `projs` names, applied to exactly its record, is replaced by
    the field of the constructor its record head-normalises to
    (`inlHeadCtor`); when the record does not reach a constructor the
    projection is kept.  `f <$> a <*> b` at the library's Signal instances
    becomes `Signal.ap (Signal.map f a) b` (`inlSignalApplicative`).  Descends
    through applications, `fun` bodies, and the value and body of a `let`. -/
def inlineDefs (defs : Name → Option Lean.Expr) (projs : Name → Option (Name × Nat × Nat)) :
    Nat → Lean.Expr → Nat → Option (Lean.Expr × Nat)
  | 0, _, _ => none
  | _, _, 0 => none
  | fuel + 1, .lam n t body bi, b + 1 =>
    match inlineDefs defs projs fuel body b with
    | some (body', b) => some (.lam n t body' bi, b)
    | none => none
  | fuel + 1, .letE n t v body nd, b + 1 =>
    match inlineDefs defs projs fuel v b with
    | some (v', b) =>
      match inlineDefs defs projs fuel body b with
      | some (body', b) => some (.letE n t v' body' nd, b)
      | none => none
    | none => none
  | fuel + 1, e, b + 1 =>
    match inlSpine e [] with
    | (.const n [], args) =>
      match defs n with
      | some v =>
        match inlBeta #[] v args b with
        | some (e', b) => inlineDefs defs projs fuel e' b
        | none => none
      | none =>
        let field? : Option (Lean.Expr × Nat) :=
          match projs n with
          | some (ctor, numParams, idx) =>
            if args.length = numParams + 1 then
              match args.getLast? with
              | some record =>
                match inlHeadCtor defs ctor fuel record b with
                | some (ctorArgs, b) => (ctorArgs[numParams + idx]?).map (·, b)
                | none => none
              | none => none
            else none
          | none => none
        match field? with
        | some (field, b) => inlineDefs defs projs fuel field b
        | none =>
          match inlMap (inlineDefs defs projs fuel) args b with
          | some (args', b) => some (args'.foldl Lean.Expr.app (.const n []), b)
          | none => none
    | (.const n ls, args) =>
      match inlMap (inlineDefs defs projs fuel) args b with
      | some (args', b) =>
        match inlSignalApplicative n ls args' with
        | some e' => some (e', b)
        | none => some (args'.foldl Lean.Expr.app (.const n ls), b)
      | none => none
    | (.lam n t body bi, args) =>
      match inlineDefs defs projs fuel body b with
      | some (body', b) =>
        match inlMap (inlineDefs defs projs fuel) args b with
        | some (args', b) => some (args'.foldl Lean.Expr.app (.lam n t body' bi), b)
        | none => none
      | none => none
    | (h, args) =>
      match inlMap (inlineDefs defs projs fuel) args b with
      | some (args', b) => some (args'.foldl Lean.Expr.app h, b)
      | none => none

/-- The literal `n : Nat` as the elaborator writes it. -/
def inlNatLit (n : Nat) : Lean.Expr :=
  mkApp3 (.const ``OfNat.ofNat [.zero]) (.const ``Nat []) (.lit (.natVal n))
    (mkApp (.const ``instOfNatNat []) (.lit (.natVal n)))

/-- `a + b` / `a - b` of two literals at the core `Nat` operations, as the
    literal of the result. -/
def inlNatSum? : Lean.Expr → Option Lean.Expr
  | .app (.app (.app (.app (.app (.app (.const ``HAdd.hAdd _) (.const ``Nat _))
      (.const ``Nat _)) (.const ``Nat _))
      (.app (.app (.const ``instHAdd _) (.const ``Nat _)) (.const ``instAddNat _))) a) b =>
    match canonicalNatLitValue? a, canonicalNatLitValue? b with
    | some m, some n => some (inlNatLit (m + n))
    | _, _ => none
  | .app (.app (.app (.app (.app (.app (.const ``HSub.hSub _) (.const ``Nat _))
      (.const ``Nat _)) (.const ``Nat _))
      (.app (.app (.const ``instHSub _) (.const ``Nat _)) (.const ``instSubNat _))) a) b =>
    match canonicalNatLitValue? a, canonicalNatLitValue? b with
    | some m, some n => some (inlNatLit (m - n))
    | _, _ => none
  | _ => none

/-- Fold every sum and difference of `Nat` literals, bottom-up, everywhere in the expression
    (type arguments and binder types included).  The result type of `a ++ b`
    is `BitVec (m + n)`, and that sum is what every parent's type arguments
    then carry; folded, the width is a literal like every other width the
    gates read. -/
def inlFoldNat : Lean.Expr → Lean.Expr
  | .app f a =>
    let e := Lean.Expr.app (inlFoldNat f) (inlFoldNat a)
    (inlNatSum? e).getD e
  | .lam n t b bi => .lam n (inlFoldNat t) (inlFoldNat b) bi
  | .forallE n t b bi => .forallE n (inlFoldNat t) (inlFoldNat b) bi
  | .letE n t v b nd => .letE n (inlFoldNat t) (inlFoldNat v) (inlFoldNat b) nd
  | .mdata d e => .mdata d (inlFoldNat e)
  | .proj s i e => .proj s i (inlFoldNat e)
  | e => e

/-- Names the legacy dispatcher intercepts by their LAST component before it
    would unfold the definition (`handleRegister`, `handleMux`, …). -/
def inlReservedSuffixes : List String :=
  ["register", "registerWithEnable", "mux", "memory", "memoryComboRead", "memoize",
   "lutMuxTree", "loop", "ofNat", "toNat", "ofFin"]

/-- A declaration from outside the Lean and Sparkle libraries. -/
def inlUserModule (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => true
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | some m =>
      let r := m.getRoot
      !(r == `Init || r == `Lean || r == `Std || r == `Sparkle)
    | none => false

/-- The last component of a name, when it is a string. -/
def inlLastComponent : Name → String
  | .str _ s => s
  | _ => ""

/-- The definitions the front end may unfold: an ordinary, universe-monomorphic
    user definition from outside the Lean and Sparkle libraries that the legacy
    translator would inline at the call site — not tagged `@[hardware_module]`,
    not a projection, matcher or instance, not irreducible (a `@[reducible]`
    helper such as `dividerQ15_16` unfolds too), no smart unfolding (no
    recursion), and no name the legacy dispatcher intercepts.  A pure function
    of the run's environment. -/
def userDefinition? (env : Environment) (n : Name) : Option Lean.Expr :=
  match env.find? n with
  | some (.defnInfo d) =>
    if inlUserModule env n && d.levelParams.isEmpty &&
        !inlReservedSuffixes.contains (inlLastComponent n) &&
        !Sparkle.Compiler.isHardwareModule env n &&
        (env.getProjectionFnInfo? n).isNone &&
        !Lean.Meta.isMatcherCore env n &&
        !Lean.Meta.isInstanceCore env n &&
        Lean.getReducibilityStatusCore env n != .irreducible &&
        !env.contains (Lean.Meta.mkSmartUnfoldingNameFor n) &&
        d.safety == .safe && !isPrimitive n
    then some d.value else none
  | _ => none

/-- The projections the front end may resolve: a field accessor of a user
    structure (not a class), from outside the Lean and Sparkle libraries, whose
    name the legacy dispatcher does not intercept.  Returns the constructor,
    the number of structure parameters and the field index. -/
def userProjection? (env : Environment) (n : Name) : Option (Name × Nat × Nat) :=
  match env.getProjectionFnInfo? n with
  | some info =>
    if !info.fromClass && inlUserModule env n &&
        !inlReservedSuffixes.contains (inlLastComponent n) && !isPrimitive n
    then some (info.ctorName, info.numParams, info.i) else none
  | none => none

/-- Recursion depth and node budget of the front-end unfolding. -/
def inlineDepth : Nat := 4096
def inlineBudget : Nat := 16000000

/-- A user type alias (`abbrev S : Type := …`, no universe parameters): its value. Type aliases
    such as `abbrev S := Signal defaultDomain (BitVec 4)` in binder types are
    what the gates' binder reading needs unfolded. -/
def userAbbrev? (env : Environment) (n : Name) : Option Lean.Expr :=
  match env.find? n with
  | some (.defnInfo d) =>
    -- type aliases only: a reducible constant whose type is a sort (not an
    -- instance, not a function)
    if inlUserModule env n && d.levelParams.isEmpty && d.type.isSort &&
        Lean.getReducibilityStatusCore env n == .reducible &&
        !Lean.Meta.isInstanceCore env n && !d.value.hasLooseBVars
    then some d.value else none
  | _ => none

/-- Every user `abbrev` replaced by its value (delta-beta), `n` rounds. -/
def inlAbbrevs (env : Environment) : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, e =>
    let e' := e.replace fun x => match x with
      | .const c [] => userAbbrev? env c
      | _ => none
    if e' == e then e else inlAbbrevs env n e'.headBeta

/-- The run's unfolding: user definitions and structure projections of
    `env`, within the budget (the expression itself when the budget is
    exhausted or a refused form is met), then literal `Nat` sums folded. -/
def userInliner (env : Environment) : Lean.Expr → Lean.Expr := fun e =>
  inlFoldNat
    (match inlineDefs (userDefinition? env) (userProjection? env) inlineDepth e inlineBudget with
     | some (e', _) => inlAbbrevs env 4 e'
     | none => inlAbbrevs env 4 e)

/-- A definition with its value rewritten. -/
def inlinedConst (inl : Lean.Expr → Lean.Expr) : ConstantInfo → ConstantInfo
  | .defnInfo d => .defnInfo { d with value := inl d.value, type := inl d.type }
  | ci => ci

/-! ### State machines: a general `circuit do` on the certified route

`runCircuitH inits (fun regs => …)` with any number of register slots is, by
its definition, a TRANSITION function closed by registers: each slot's next
value and the result are combinational functions of the inputs and of the
slots' current values.  `machineShape?` reads that transition off the
declaration's value PURELY — the handles of the slots, the `Circuit.next`
writes in order, the result of the final `pure` — and writes it as one
ordinary combinational body over the declaration's binders plus one binder
per slot, whose value is the result and every next value PACKED into one bit
vector (`result ++ next₀ ++ … ++ nextₙ₋₁`, a Bool as one bit).

That body is offered to the unified gate like any other declaration; when
the gate accepts it the transition is compiled by the SAME certified
combinational harness (`synthesizeMixedCertified`), and
`Sparkle.IR.Machine.closeMachine` — a pure function on the IR — turns the
slot ports into registers.  The emitted text differs from the legacy
lowering of `circuit do` (one register per slot there too, but other wire
names and no packed wire); the function is the same, and that is what
`Tools/ShippingMachine*.lean` prove. -/

/-- The kind of a register slot's type: `Bool`, or `BitVec n` with a literal
    positive `n`. -/
def machSlotKind? : Lean.Expr → Option MixedGateBinder
  | .const ``Bool _ => some .bool
  | .app (.const ``BitVec _) wE =>
    (canonicalNatLitValue? wE).bind fun n => if 0 < n then some (.bits n) else none
  | _ => none

/-- The slot types of a `runCircuitH`: a literal list of slot types. -/
def machSlotKinds : Lean.Expr → Option (List MixedGateBinder)
  | .app (.const ``List.nil _) _ => some []
  | .app (.app (.app (.const ``List.cons _) _) ty) rest =>
    match machSlotKind? ty, machSlotKinds rest with
    | some k, some ks => some (k :: ks)
    | _, _ => none
  | _ => none

/-- A slot's reset value: a Bool constructor, or a BitVec literal of the
    slot's width. -/
def machInit? (natOf : Lean.Expr → Option Nat) : MixedGateBinder → Lean.Expr → Option Nat
  | .bool, .const ``Bool.true _ => some 1
  | .bool, .const ``Bool.false _ => some 0
  | .bool, e =>
    -- a reset value computed in Lean: its value, by the kernel's reduction
    match natOf (mkApp (.const ``Bool.toNat []) e) with
    | some 0 => some 0
    | some 1 => some 1
    | _ => none
  | .bits n, e =>
    match bitVecLitValue? e with
    | some (w, v) => if w == n then some v else none
    | none =>
      natOf (mkApp2 (.const ``BitVec.toNat [])
        (mkApp3 (.const ``OfNat.ofNat [.zero]) (.const ``Nat []) (.lit (.natVal n))
          (mkApp (.const ``instOfNatNat []) (.lit (.natVal n)))) e)
  | _, _ => none

/-- The reset values: the nested pair `(init₀, (init₁, … ()))`. -/
def machInits (natOf : Lean.Expr → Option Nat) :
    List MixedGateBinder → Lean.Expr → Option (List Nat)
  | [], .const ``Unit.unit _ => some []
  | k :: ks, .app (.app (.app (.app (.const ``Prod.mk _) _) _) v) rest =>
    match machInit? natOf k v, machInits natOf ks rest with
    | some i, some is => some (i :: is)
    | _, _ => none
  | _, _ => none

/-- What a bound variable of the `circuit do` body stands for while the body
    is read. -/
inductive MachVal where
  /-- `regs.2.2…` (`p` times): the handles from slot `p` on. -/
  | regs (p : Nat)
  /-- The handle of slot `i`. -/
  | handle (i : Nat)
  /-- The `Unit` a `Circuit.bind` continuation receives. -/
  | unit
  /-- A Signal expression of the transition (in placeholder form). -/
  | val (e : Lean.Expr)
  /-- The state of a hand-written `Signal.loop` over the slots
      `base … base+n-1`: a right-nested tuple read by `Signal.fst`/`Signal.snd`. -/
  | state (base n : Nat)

/-- Placeholders for the transition's variables while its size is not known:
    the declaration's binder `i` (from the end), slot `i`, hardware `let` `j`.
    They are closed terms, so they move under binders unchanged; `machClose`
    turns them into the bound variables of the final telescope. -/
def machIn (i : Nat) : Lean.Expr := .fvar ⟨.num (.str .anonymous "_machIn") i⟩
def machSlot (i : Nat) : Lean.Expr := .fvar ⟨.num (.str .anonymous "_machSlot") i⟩
def machLet (j : Nat) : Lean.Expr := .fvar ⟨.num (.str .anonymous "_machLet") j⟩
/-- The output of the `k`-th `@[hardware_module]` call of the body: an input
    of the transition (the open-module view), tied to the instance by
    `closeInsts`. -/
def machInstOut (k : Nat) : Lean.Expr := .fvar ⟨.num (.str .anonymous "_machInst") k⟩

/-- `regs.2.2…`: a bound variable standing for a tail, or `Prod.snd` of one. -/
def machTailV (env : List MachVal) (d : Nat) : Lean.Expr → Option Nat
  | .bvar j =>
    if j < d then none else
    match env[j - d]? with
    | some (.regs p) => some p
    | _ => none
  | .app (.app (.app (.const ``Prod.snd _) _) _) t => (machTailV env d t).map (· + 1)
  | _ => none

/-- The handle of a slot: a bound variable standing for one, or `(tail).1`. -/
def machHandleV (env : List MachVal) (d : Nat) : Lean.Expr → Option Nat
  | .bvar j =>
    if j < d then none else
    match env[j - d]? with
    | some (.handle i) => some i
    | _ => none
  | .app (.app (.app (.const ``Prod.fst _) _) _) t => machTailV env d t
  | _ => none

/-- The live read of a slot: `handle.1`. -/
def machReadV (env : List MachVal) (d : Nat) : Lean.Expr → Option Nat
  | .app (.app (.app (.const ``Prod.fst _) _) _) h => machHandleV env d h
  | _ => none

/-- What the state-machine front end reads of the run's environment about
    user structures: the field accessors (`userProjection?`), and for a
    structure whose fields are all Bool or positive-width BitVec Signals its
    constructor and the fields' names and kinds (`userStructure?`). -/
structure StructEnv where
  proj : Name → Option (Name × Nat × Nat)
  fields : Name → Option (Name × List (String × MixedGateBinder))
  /-- The value of a closed `Nat` term (`kernelNat`). -/
  natOf : Lean.Expr → Option Nat := fun _ => none
  /-- A `@[hardware_module]` declaration with one Signal result: the kinds
      of its binders (the domain included) and of its result
      (`instSignature?`). -/
  inst : Name → Option (List MixedGateBinder × MixedGateBinder) := fun _ => none
  /-- A `@[hardware_module]` declaration with hardware binders and any other
      result (a structure of Signals): the kinds of its binders and its type
      (`instSignatureS?`). -/
  instS : Name → Option (List MixedGateBinder × Lean.Expr) := fun _ => none
  /-- A matcher destructuring one right-nested pair: its arity
      (`MachRawSurface.prodMatcherArity?`). -/
  prodMatch : Name → Option Nat := fun _ => none

/-- The hardware `let`s met so far: binder name, kind, value (placeholder
    form; it mentions earlier `let`s only). -/
abbrev MachLets := Array (Name × MixedGateBinder × Lean.Expr)

/-- What the reader of a `circuit do` accumulates: the slots of every
    machine met so far (the enclosing machine's first, then each nested
    `runCircuitH` in reading order), their reset values and handle names,
    the writes in order, the hardware `let`s, the domain (every machine
    must be in the same one), and where each nested machine's slots start. -/
structure MachRead where
  kinds : Array MixedGateBinder := #[]
  inits : Array Nat := #[]
  names : Array Name := #[]
  ws : Array (Nat × Lean.Expr) := #[]
  lets : MachLets := #[]
  dom : Option Lean.Expr := none
  /-- `(first slot, slot count)` of every machine, the enclosing one first. -/
  runs : Array (Nat × Nat) := #[]
  /-- Every nested machine read so far — its first slot, domain, slot types,
      reset values, writes and result in placeholder form — so a second
      occurrence of the SAME machine (`circuit do` copies its `let`s into
      every write and into the result) is read as that machine. -/
  nested : Array (Nat × Lean.Expr × Lean.Expr × Lean.Expr × List (Nat × Lean.Expr) × Lean.Expr) :=
    #[]
  /-- Every `@[hardware_module]` call read: the module, the `let`s holding
      its arguments (in port order), the kind of its result. -/
  insts : Array (Name × List Nat × MixedGateBinder) := #[]
  /-- The child output port each `insts` entry reads (`out` for a one-Signal
      result, the field for a structure's), and whether a structure call was
      read (then the shape's `instFields` are these). -/
  instFields : Array String := #[]
  instStruct : Bool := false
  /-- Reading a nested machine's chain (a sub-machine met there — one
      reading another's result — is refused: the endpoint's sub-machines
      read the enclosing handles only). -/
  inInner : Bool := false
  /-- `(first slot, slot count)` of every hand-written `Signal.loop`. -/
  loops : Array (Nat × Nat) := #[]
  /-- Every hand-written loop read: `(first slot, slot count, its writes)` —
      a later copy of the same loop (`circuit do` copies its `let`s) is that
      loop when its body reads to the same writes. -/
  loopWs : Array (Nat × Nat × List (Nat × Lean.Expr)) := #[]

/-- A placeholder (a variable of the transition), as opposed to a compound
    expression. -/
def machIsVar : Lean.Expr → Bool
  | .fvar _ => true
  | _ => false

/-- Bind a `let` value that is not a handle: a hardware value (its type a
    Bool or positive-width BitVec Signal) becomes a `let` of the transition —
    the one already met with the SAME value, if any: `circuit do` copies its
    `let`s into every write and into the result — unless it is a bare
    variable; any other value is substituted. -/
def machBindLet (nm : Name) (ty v' : Lean.Expr) (lets : MachLets) : Lean.Expr × MachLets :=
  match mixedGateBinderKind? ty with
  | some .domain => (v', lets)
  | none => (v', lets)
  | some k =>
    if machIsVar v' then (v', lets) else
    match lets.findIdx? (fun l => l.2.2 == v') with
    | some j => (machLet j, lets)
    | none => (machLet lets.size, lets.push (nm.eraseMacroScopes, k, v'))

/-- A `runCircuitH` application: `(domain, slot types, reset values, body
    under the regs binder)`. -/
def machRunApp? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) :=
  match inlSpine e [] with
  | (.const ``Sparkle.Core.runCircuitH _, [dom, αs, _, _, _, _, inits, .lam _ _ body _]) =>
    some (dom, αs, inits, body)
  | _ => none

/-- The names the body gives its register handles: the leading
    `let h := (…).1` bindings, in order. -/
def machLetNames : Lean.Expr → List Name
  | .letE nm _ (.app (.app (.app (.const ``Prod.fst _) _) _) _) body _ =>
    nm.eraseMacroScopes :: machLetNames body
  | .letE _ _ _ body _ => machLetNames body
  | _ => []

/-- The handle names of a machine's slots: the body's names when it names
    all of them, `reg<i>` otherwise; a nested machine's names carry its
    ordinal so the slots of two machines never share a name. -/
def machSlotNames (ordinal : Nat) (body : Lean.Expr) (kinds : List MixedGateBinder)
    (base : Nat) : List Name :=
  let names := machLetNames body
  let raw := if kinds.length ≤ names.length then names.take kinds.length
    else (List.range kinds.length).map fun i => Name.mkSimple s!"reg{base + i}"
  if ordinal = 0 then raw else raw.map fun nm => nm.appendAfter s!"_{ordinal}"

/-- Reserve the slots of a machine: its slot kinds, reset values and handle
    names are appended; `none` when a slot type or a reset value is not
    accepted, or the machine is in another domain than the ones before (the
    domain in placeholder form, `dom'`). -/
def machReserve (natOf : Lean.Expr → Option Nat) (dom' αs initsE body : Lean.Expr)
    (st : MachRead) : Option (Nat × MachRead) := do
  let kinds ← machSlotKinds (Sparkle.Compiler.MachRawSurface.zetaAll αs)
  if kinds.isEmpty then none else
  let inits ← machInits natOf kinds (Sparkle.Compiler.MachRawSurface.zetaAll initsE)
  match st.dom with
  | some d => if d != dom' then none else pure ()
  | none => pure ()
  let base := st.kinds.size
  some (base, { st with
    kinds := st.kinds ++ kinds.toArray
    inits := st.inits ++ inits.toArray
    names := st.names ++ (machSlotNames st.runs.size body kinds base).toArray
    dom := some dom'
    runs := st.runs.push (base, kinds.length) })

/-- A full application of a `@[hardware_module]` with one Signal result:
    the module, the kinds of its binders and result, the arguments. -/
def machInstCall? (senv : StructEnv) (e : Lean.Expr) :
    Option (Name × List MixedGateBinder × MixedGateBinder × List Lean.Expr) :=
  match inlSpine e [] with
  | (.const c _, args) =>
    match senv.inst c with
    | some (kinds, res) => if args.length == kinds.length then some (c, kinds, res, args) else none
    | none => none
  | _ => none

/-- A full application of a `@[hardware_module]` with a structure result:
    the module, the kinds of its binders, its type, the arguments. -/
def machInstCallS? (senv : StructEnv) (e : Lean.Expr) :
    Option (Name × List MixedGateBinder × Lean.Expr × List Lean.Expr) :=
  match inlSpine e [] with
  | (.const c _, args) =>
    match senv.instS c with
    | some (kinds, ty) => if args.length == kinds.length then some (c, kinds, ty, args) else none
    | none => none
  | _ => none

/-- Bind a converted value as a hardware `let` of the given kind (the one
    already met with the same value, if any) and return its index. -/
def machLetIndex (nm : Name) (k : MixedGateBinder) (v' : Lean.Expr) (lets : MachLets) :
    Nat × MachLets :=
  match v' with
  | .fvar ⟨.num (.str .anonymous "_machLet") j⟩ => (j, lets)
  | _ =>
    match lets.findIdx? (fun l => l.2.2 == v') with
    | some j => (j, lets)
    | none => (lets.size, lets.push (nm, k, v'))

/-- `Signal.snd` applied `k` times: `(k, the innermost expression)`. -/
def machSndChain : Lean.Expr → Nat × Lean.Expr
  | .app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.snd _) _) _) _) s =>
    let (k, x) := machSndChain s
    (k + 1, x)
  | e => (0, e)

/-- A read of a `Signal.loop` state: `Signal.fst (Signal.snd^k s)` is slot
    `base + k`, `Signal.snd^(n-1) s` the last slot. -/
def machLoopRead? (env : List MachVal) (d : Nat) (e : Lean.Expr) : Option Nat :=
  let state? (x : Lean.Expr) : Option (Nat × Nat) := match x with
    | .bvar j =>
      if j < d then none else
      match env[j - d]? with
      | some (.state b n) => some (b, n)
      | _ => none
    | _ => none
  match e with
  | .app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.fst _) _) _) _) s =>
    let (k, x) := machSndChain s
    match state? x with
    | some (b, n) => if k + 1 < n then some (b + k) else none
    | none => none
  | _ =>
    let (k, x) := machSndChain e
    if k = 0 then none else
    match state? x with
    | some (b, n) => if k + 1 = n then some (b + k) else none
    | none => none

/-- `Signal.register init next`: `(type, init, next)`. -/
def machLoopReg? : Lean.Expr → Option (Lean.Expr × Lean.Expr × Lean.Expr)
  | .app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.register _) _) ty) init) next =>
    some (ty, init, next)
  | _ => none

/-- The registers a loop body returns, `bundle2 r₀ (bundle2 r₁ … rₙ₋₁)`, in
    order. -/
def machLoopRegs : Lean.Expr → Option (List (Lean.Expr × Lean.Expr × Lean.Expr))
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.bundle2 _) _) _) _) a) b => do
    let r ← machLoopReg? a
    let rs ← machLoopRegs b
    some (r :: rs)
  | e => (machLoopReg? e).map fun r => [r]

/-- An expression under its `let`s. -/
def machLetTail : Lean.Expr → Lean.Expr
  | .letE _ _ _ b _ => machLetTail b
  | e => e

/-- The components of `bundle2 a₀ (bundle2 a₁ … aₙ₋₁)` (`n` of them). -/
def machBundleParts? : Nat → Lean.Expr → Option (List Lean.Expr)
  | 0, _ => none
  | 1, e => some [e]
  | n + 1, .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.bundle2 _) _) _) _) a) b =>
    (machBundleParts? n b).map (a :: ·)
  | _, _ => none

/-- The component kinds of a right-nested tuple of Bool / positive-width
    BitVec types. -/
def machProdKinds : Lean.Expr → Option (List MixedGateBinder)
  | .app (.app (.const ``Prod _) a) b => do
    let k ← machSlotKind? a
    let ks ← machProdKinds b
    some (k :: ks)
  | e => (machSlotKind? e).map ([·])

/-- The domain of a declaration's result type `∀ binders, Signal dom τ` (or a
    structure of Signals in `dom`), in placeholder form: a domain binder is
    `machIn` of its position from the end. -/
def machTypeDom? : Lean.Expr → Option Lean.Expr
  | .forallE _ _ b _ => machTypeDom? b
  | e =>
    match e.getAppFn, e.getAppArgs.toList with
    | .const ``Sparkle.Core.Signal.Signal _, [dom, _] =>
      match dom with
      | .bvar j => some (machIn j)
      | d => if d.hasLooseBVars then none else some d
    | _, _ => none

/-- A result of type `Signal dom (A × B × …)`: the components' kinds. The
    module has ONE output port `out` holding them packed, the first in the
    high bits, a Bool as one bit (the legacy lowering's interface). -/
def machTupleKinds? : Lean.Expr → Option (List MixedGateBinder)
  | .forallE _ _ b _ => machTupleKinds? b
  | .app (.app (.const ``Sparkle.Core.Signal.Signal _) _) ty@(.app (.app (.const ``Prod _) _) _) =>
    machProdKinds ty
  | _ => none

/-- A projection of a user structure applied to its constructor: the field. -/
def machProjIota (projs : Name → Option (Name × Nat × Nat)) (e : Lean.Expr) : Lean.Expr :=
  match inlSpine e [] with
  | (.const p _, args) =>
    match projs p, args.getLast? with
    | some (ctor, numParams, idx), some r =>
      if args.length = numParams + 1 then
        match inlSpine r [] with
        | (.const c _, cargs) =>
          if c == ctor then (cargs[numParams + idx]?).getD e else e
        | _ => e
      else e
    | _, _ => e
  | _ => e

/-- The output ports of a result type: one, `out`, for a Signal; one per
    field, named after it, for a structure of Signals.  With the structure's
    constructor in the second case. -/
def machOuts? (senv : StructEnv) :
    Lean.Expr → Option (Option Name × List (String × MixedGateBinder))
  | .forallE _ _ b _ => machOuts? senv b
  -- a pair of Signals: two ports `out_0`, `out_1` (the legacy interface)
  | .app (.app (.const ``Prod _) a) b =>
    match mixedGateBinderKind? a, mixedGateBinderKind? b with
    | some ka, some kb =>
      if ka == .domain || kb == .domain then none
      else some (some ``Prod.mk, [("out_0", ka), ("out_1", kb)])
    | _, _ => none
  | e =>
    match mixedGateBinderKind? e with
    | some .bool => some (none, [("out", .bool)])
    | some (.bits n) => some (none, [("out", .bits n)])
    | _ =>
      match e.getAppFn with
      | .const s _ => (senv.fields s).map fun (ctor, fs) => (some ctor, fs)
      | _ => none

mutual
/-- Rewrite a Signal expression of the `circuit do` body into the transition
    (placeholder form).  A bound variable of the body is replaced by what it
    stands for; a live read of slot `i` becomes that slot; a hardware `let`
    becomes a `let` of the transition (`machBindLet`); a nested
    `runCircuitH` becomes a machine of its own — its slots reserved after the
    ones met so far, its writes added, its result the value — or the machine
    already met that it repeats (`machNested`).
    Any other use of a handle, and a `let` or a nested machine under a
    `fun`, is refused. -/
partial def machConv (senv : StructEnv) : List MachVal → Nat → Lean.Expr → MachRead →
    Option (Lean.Expr × MachRead)
  | env, d, .bvar j, st =>
    if j < d then some (.bvar j, st) else
    match env[j - d]? with
    | some (.val v) => some (v, st)
    | some (.state b 1) => some (machSlot b, st)
    -- a whole loop state of several slots: the bundle of its slots (equal to
    -- the state signal by structure eta)
    | some (.state b n) => do
      let dom ← st.dom
      let tyOf (k : MixedGateBinder) : Option Lean.Expr := match k with
        | .bits w => some (mkApp (.const ``BitVec []) (inlNatLit w))
        | .bool => some (.const ``Bool [])
        | .domain => none
      let tys ← ((List.range n).map (b + ·)).mapM fun i => st.kinds[i]? >>= tyOf
      let rec bundle : List Nat → List Lean.Expr → Option (Lean.Expr × Lean.Expr)
        | [i], [t] => some (machSlot i, t)
        | i :: is, t :: ts => do
          let (rest, restT) ← bundle is ts
          some (mkApp5 (.const ``Sparkle.Core.Signal.bundle2 [.zero]) dom t restT (machSlot i) rest,
            mkApp2 (.const ``Prod [.zero, .zero]) t restT)
        | _, _ => none
      let (e, _) ← bundle ((List.range n).map (b + ·)) tys
      some (e, st)
    | some _ => none
    | none => some (machIn (j - d - env.length), st)
  | env, d, .app f a, st =>
    match machLoopRead? env d (.app f a) with
    | some i => if i < st.kinds.size then some (machSlot i, st) else none
    | none =>
    match machRunApp? (.app f a) with
    | some (dom, αs, initsE, body) =>
      if d != 0 then none else machNested senv env dom αs initsE body st
    | none =>
    match machInstCall? senv (.app f a) with
    | some (c, kinds, res, args) =>
      if d != 0 then none else machInstance senv env c kinds res args st
    | none =>
    match machInstCallS? senv (.app f a) with
    | some (c, kinds, ty, args) =>
      if d != 0 then none else machInstanceS senv env c kinds ty args st
    | none =>
    match machReadV env d (.app f a) with
    | some i => if i < st.kinds.size then some (machSlot i, st) else none
    | none =>
      match machConv senv env d f st with
      | some (f', st) =>
        match machConv senv env d a st with
        | some (a', st) =>
          some (Sparkle.Compiler.MachRawSurface.bundleIota
            (machProjIota senv.proj (.app f' a')), st)
        | none => none
      | none => none
  | env, d, .lam nm t b bi, st =>
    match machConv senv env d t st with
    | some (t', st) =>
      match machConv senv env (d + 1) b st with
      | some (b', st) => some (.lam nm t' b' bi, st)
      | none => none
    | none => none
  | env, d, .forallE nm t b bi, st =>
    match machConv senv env d t st with
    | some (t', st) =>
      match machConv senv env (d + 1) b st with
      | some (b', st) => some (.forallE nm t' b' bi, st)
      | none => none
    | none => none
  | env, d, .letE nm ty v b nd, st =>
    if d != 0 then none else
    -- a `let` block in the value: its `let`s first
    match Sparkle.Compiler.MachRawSurface.rootFloat v with
    | .letE n2 t2 v2 w nd2 =>
      machConv senv env 0
        (.letE n2 t2 v2 (.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2) st
    | v =>
    -- a hand-written loop: a sub-machine of its own
    if v.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then
      match machLoopRoot senv env v st with
      | some (mv, st) => machConv senv (mv :: env) 0 b st
      | none => none
    else
    match machTailV env 0 v with
    | some p => machConv senv (.regs p :: env) 0 b st
    | none =>
      match machHandleV env 0 v with
      | some i => machConv senv (.handle i :: env) 0 b st
      | none =>
        match machConv senv env 0 v st with
        | some (v', st) =>
          let (x, lets) := machBindLet nm ty v' st.lets
          machConv senv (.val x :: env) 0 b { st with lets := lets }
        | none => none
  | _, _, .mdata .., _ => none
  | _, _, .proj .., _ => none
  | _, _, e, st => some (e, st)

/-- A nested `runCircuitH`: a machine of its own.  Its slots are reserved
    after the ones met so far, its chain is read with its regs binder
    standing for them, its writes are added to the transition, and the
    value is its result. -/
partial def machNested (senv : StructEnv) (env : List MachVal) (dom αs initsE body : Lean.Expr)
    (st : MachRead) : Option (Lean.Expr × MachRead) := do
  -- a sub-machine read inside another one's body (a chain of sub-machines,
  -- one reading another's result) is not what the endpoint covers
  if st.inInner then none else
  let (dom', st) ← machConv senv env 0 dom st
  -- the same machine met before: the same domain, slots and reset values,
  -- and the same writes and result when its chain is read with that
  -- machine's slots
  let shared := st.nested.findSome? fun (base, d, a, ini, ws, v) =>
    if d == dom' && a == αs && ini == initsE then
      match machChain senv (.regs base :: env) body st with
      | some (ws', v', st') => if ws' == ws && v' == v then some (v, st') else none
      | none => none
    else none
  match shared with
  | some r => some r
  | none =>
    let (base, st) ← machReserve senv.natOf dom' αs initsE body st
    let outer := st.inInner
    let (ws, v, st) ← machChain senv (.regs base :: env) body { st with inInner := true }
    -- a sub-machine may read an EARLIER sub-machine's state (a chain: the
    -- HFT emitter reads the parser's result; the endpoint's `TeleT`)
    some (v, { st with ws := st.ws ++ ws.toArray, inInner := outer,
                       nested := st.nested.push (base, dom', αs, initsE, ws, v) })

/-- A `@[hardware_module]` call: its result is an input of the transition
    (`machInstOut`), its arguments hardware `let`s (so each has a wire), its
    domain the machine's; `closeInsts` ties the input to the instance. -/
partial def machInstance (senv : StructEnv) (env : List MachVal) (c : Name)
    (kinds : List MixedGateBinder) (res : MixedGateBinder) (args : List Lean.Expr)
    (st : MachRead) : Option (Lean.Expr × MachRead) := do
  -- a BitVec result (what the endpoint covers), in the enclosing body or in
  -- a sub-machine's (its value then reads that machine's state)
  match res with
  | .bits _ => pure ()
  | _ => none
  let k := st.insts.size
  let (js, st) ← (kinds.zip args).foldlM (init := (([] : List Nat), st))
    fun (js, st) (kind, arg) => do
      let (v', st) ← machConv senv env 0 arg st
      match kind with
      | .domain =>
        match st.dom with
        | some d => if d != v' then none else some (js, st)
        | none => some (js, { st with dom := some v' })
      | _ =>
        let (j, lets) := machLetIndex (Name.mkSimple s!"inst{k}_arg{js.length}") kind v' st.lets
        some (js ++ [j], { st with lets := lets })
  -- the same call met before (`circuit do` copies its `let`s): its output
  match st.insts.findIdx? (fun i => i.1 == c && i.2.1 == js) with
  | some k' => some (machInstOut k', st)
  | none => some (machInstOut k, { st with insts := st.insts.push (c, js, res),
                                           instFields := st.instFields.push "out" })

/-- A `@[hardware_module]` call whose result is a structure of Signals: ONE
    call, one transition input per field (`machInstOut`, in field order), the
    value the structure's constructor on them (a field projection of it is
    the field's input, `machProjIota`). Its arguments are hardware `let`s;
    the same call met again is the same entries. -/
partial def machInstanceS (senv : StructEnv) (env : List MachVal) (c : Name)
    (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr)
    (st : MachRead) : Option (Lean.Expr × MachRead) := do
  -- in the enclosing body (what the endpoint covers)
  if st.inInner then none else
  -- the result type at the call
  let rec inst : Lean.Expr → List Lean.Expr → Option Lean.Expr
    | e, [] => some e
    | .forallE _ _ b _, a :: as => inst (b.instantiate1 a) as
    | _, _ => none
  let resTy ← inst ty args
  let (some ctor, fields) ← machOuts? senv resTy | none
  if fields.isEmpty || fields.any (fun f => f.2 == .domain) then none else
  let (js, st) ← (kinds.zip args).foldlM (init := (([] : List Nat), st))
    fun (js, st) (kind, arg) => do
      let (v', st) ← machConv senv env 0 arg st
      match kind with
      | .domain =>
        match st.dom with
        | some d => if d != v' then none else some (js, st)
        | none => some (js, { st with dom := some v' })
      | _ =>
        let (j, lets) := machLetIndex (Name.mkSimple s!"inst{st.insts.size}_arg{js.length}")
          kind v' st.lets
        some (js ++ [j], { st with lets := lets })
  -- the structure's parameters (its domain), read like the arguments
  let (params, st) ← resTy.getAppArgs.toList.foldlM (init := (([] : List Lean.Expr), st))
    fun (ps, st) p => do
      let (p', st) ← machConv senv env 0 p st
      some (ps ++ [p'], st)
  let lvls := resTy.getAppFn.constLevels!
  let (k0, st) := match st.insts.findIdx? (fun i => i.1 == c && i.2.1 == js) with
    | some k0 => (k0, st)
    | none =>
      (st.insts.size, { st with
        insts := st.insts ++ (fields.map fun f => (c, js, f.2)).toArray
        instFields := st.instFields ++ (fields.map (·.1)).toArray
        instStruct := true })
  some (mkAppN (.const ctor lvls)
    (params.toArray ++ ((List.range fields.length).map fun i => machInstOut (k0 + i)).toArray), st)

/-- The statements of a `circuit do` body: the writes `handle <~ rhs` in
    order as `(slot, next value)`, and the final `pure` value, both in
    placeholder form, with everything they use added to the reader's
    state. -/
partial def machChain (senv : StructEnv) : List MachVal → Lean.Expr → MachRead →
    Option (List (Nat × Lean.Expr) × Lean.Expr × MachRead)
  | env, .app (.app (.app (.app (.const ``Sparkle.Core.Circuit.pure' _) _) _) _) v, st =>
    match machConv senv env 0 v st with
    | some (v', st) => some ([], v', st)
    | none => none
  | env, .app (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Circuit.bind _) _) _) _) _)
      (.app (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Circuit.next _) _) _) _) _)
        h) rhs)) (.lam _ _ rest _), st =>
    match machHandleV env 0 h, machConv senv env 0 rhs st with
    | some i, some (rhs', st) =>
      if i < st.kinds.size then
        match machChain senv (.unit :: env) rest st with
        | some (ws, v, st) => some ((i, rhs') :: ws, v, st)
        | none => none
      else none
    | _, _ => none
  | env, .letE nm ty v b nd, st =>
    -- a `let` block in the value (an unfolded engine, `Signal.fst (let s :=
    -- Signal.loop …; …)`): its `let`s first
    match Sparkle.Compiler.MachRawSurface.rootFloat v with
    | .letE n2 t2 v2 w nd2 =>
      machChain senv env
        (.letE n2 t2 v2 (.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2) st
    | v =>
    -- a hand-written loop: a sub-machine of its own (`machLoopRoot`)
    if v.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then
      match machLoopRoot senv env v st with
      | some (mv, st) => machChain senv (mv :: env) b st
      | none => none
    else
    match machTailV env 0 v with
    | some p => machChain senv (.regs p :: env) b st
    | none =>
      match machHandleV env 0 v with
      | some i => machChain senv (.handle i :: env) b st
      | none =>
        match machConv senv env 0 v st with
        | some (v', st) =>
          let (x, lets) := machBindLet nm ty v' st.lets
          machChain senv (.val x :: env) b { st with lets := lets }
        | none => none
  | _, _, _ => none

/-- The body of a hand-written `Signal.loop`: its `let`s (the state bound to
    `.state base n`), then the registers it returns; their next values are
    the writes of slots `base, base+1, …`. -/
partial def machLoopBody (senv : StructEnv) (base : Nat) :
    List MachVal → Lean.Expr → MachRead → Option MachRead
  | env, .letE nm ty v b _, st => do
    let (v', st) ← machConv senv env 0 v st
    let (x, lets) := machBindLet nm ty v' st.lets
    machLoopBody senv base (.val x :: env) b { st with lets := lets }
  | env, tail, st => do
    let regs ← machLoopRegs tail
    let (ws, st) ← regs.foldlM (init := (([] : List (Nat × Lean.Expr)), st))
      fun (ws, st) (_, _, nx) => do
        let (nx', st) ← machConv senv env 0 nx st
        pure (ws ++ [(base + ws.length, nx')], st)
    some { st with ws := st.ws ++ ws.toArray }

/-- A hand-written state machine `Signal.loop (fun s => lets; bundle2
    (Signal.register init₀ next₀) …)`: its slots reserved after the ones met
    so far (kinds from the registers' types, reset values from their initial
    values), its body read with `s` standing for the state. Returns what the
    variable bound to the loop stands for. -/
partial def machLoopRoot (senv : StructEnv) (env : List MachVal) (e : Lean.Expr) (st : MachRead) :
    Option (MachVal × MachRead) := do
  let (.const ``Sparkle.Core.Signal.Signal.loop _, [dom, _, _, .lam _ _ body _]) := inlSpine e []
    | none
  -- a loop inside a sub-machine's body is not what the endpoint covers
  if st.inInner then none else
  let regs ← machLoopRegs (machLetTail body)
  if regs.any (fun (ty, init, _) => ty.hasLooseBVars || init.hasLooseBVars) then none else
  let kinds ← regs.mapM fun (ty, _, _) => machSlotKind? ty
  let inits ← (kinds.zip regs).mapM fun (k, (_, init, _)) => machInit? senv.natOf k init
  let (dom', st) ← machConv senv env 0 dom st
  match st.dom with
  | some d0 => if d0 != dom' then none else pure ()
  | none => pure ()
  let n := kinds.length
  -- the same loop met before: its body reads to the same writes there
  let shared := st.loopWs.findSome? fun (b0, n0, ws0) =>
    if n0 != n then none else
    match machLoopBody senv b0 (.state b0 n :: env) body { st with ws := #[] } with
    | some st' => if st'.ws.toList == ws0 then some (b0, { st' with ws := st.ws }) else none
    | none => none
  match shared with
  | some (b0, st') => some (.state b0 n, st')
  | none =>
  let base := st.kinds.size
  let st := { st with
    kinds := st.kinds ++ kinds.toArray
    inits := st.inits ++ inits.toArray
    names := st.names ++ ((List.range n).map fun i =>
      Name.mkSimple s!"loop{st.loops.size}_r{i}").toArray
    dom := some dom'
    loops := st.loops.push (base, n) }
  let before := st.ws.size
  let st ← machLoopBody senv base (.state base n :: env) body st
  some (.state base n,
    { st with loopWs := st.loopWs.push (base, n, (st.ws.toList.drop before)) })

end

/-- The next value of slot `i`: its LAST write (`Circuit.next` replaces the
    pending value), or the slot itself when the body never writes it. -/
def machNext (i : Nat) (ws : List (Nat × Lean.Expr)) : Lean.Expr :=
  match ws.reverse.find? (·.1 == i) with
  | some (_, e) => e
  | none => machSlot i

/-- Close the placeholders: the transition's telescope is the declaration's
    binders, then `kI` instance outputs, `n` slots and `k` hardware `let`s. -/
def machClose (kI n k : Nat) : Nat → Lean.Expr → Lean.Expr
  | d, .fvar ⟨.num (.str .anonymous "_machIn") i⟩ => .bvar (kI + n + k + i + d)
  | d, .fvar ⟨.num (.str .anonymous "_machInst") j⟩ => .bvar (kI - 1 - j + n + k + d)
  | d, .fvar ⟨.num (.str .anonymous "_machSlot") i⟩ => .bvar (n - 1 - i + k + d)
  | d, .fvar ⟨.num (.str .anonymous "_machLet") j⟩ => .bvar (k - 1 - j + d)
  | d, .app f a => .app (machClose kI n k d f) (machClose kI n k d a)
  | d, .lam nm t b bi => .lam nm (machClose kI n k d t) (machClose kI n k (d + 1) b) bi
  | d, .forallE nm t b bi => .forallE nm (machClose kI n k d t) (machClose kI n k (d + 1) b) bi
  | _, e => e

/-- The domain (in placeholder form) in the transition's context, with the
    reset kind the registers take: synchronous in `defaultDomain`,
    asynchronous (the legacy fallback for a domain that is not a literal)
    for a domain binder. -/
def machDom? (n : Nat) : Lean.Expr → Option (Lean.Expr × Sparkle.IR.Type.ResetKind)
  | .fvar ⟨.num (.str .anonymous "_machIn") i⟩ => some (.bvar (i + n), .asynchronous)
  | .const ``Sparkle.Core.Domain.defaultDomain ls =>
    some (.const ``Sparkle.Core.Domain.defaultDomain ls, .synchronous)
  | _ => none

/-- `Signal dom (BitVec n)`. -/
def machSigT (dom : Lean.Expr) (n : Nat) : Lean.Expr :=
  mkApp2 (.const ``Sparkle.Core.Signal.Signal [.zero]) dom (mkApp (.const ``BitVec []) (inlNatLit n))

/-- `a ++ b` at the library's Signal instance, widths `m` and `n`. -/
def machConcatE (dom : Lean.Expr) (m n : Nat) (a b : Lean.Expr) : Lean.Expr :=
  mkApp6 (.const ``HAppend.hAppend [.zero, .zero, .zero]) (machSigT dom m) (machSigT dom n)
    (machSigT dom (m + n))
    (mkApp3 (.const ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat []) dom (inlNatLit m)
      (inlNatLit n)) a b

/-- `Signal.pure v#k`. -/
def machLitE (dom : Lean.Expr) (k v : Nat) : Lean.Expr :=
  mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom
    (mkApp (.const ``BitVec []) (inlNatLit k))
    (mkApp2 (.const ``BitVec.ofNat []) (inlNatLit k) (inlNatLit v))

/-- A Bool Signal as one bit: `Signal.mux b 1#1 0#1`. -/
def machBoolBits (dom b : Lean.Expr) : Lean.Expr :=
  mkApp5 (.const ``Sparkle.Core.Signal.Signal.mux [.zero]) dom
    (mkApp (.const ``BitVec []) (inlNatLit 1)) b (machLitE dom 1 1) (machLitE dom 1 0)

/-- A field of the packed value: its width and its bits. -/
def machField (dom : Lean.Expr) : MixedGateBinder → Lean.Expr → Option (Nat × Lean.Expr)
  | .bool, e => some (1, machBoolBits dom e)
  | .bits n, e => some (n, e)
  | .domain, _ => none

/-- The fields concatenated, the first in the high bits. -/
def machPack (dom : Lean.Expr) : List (Nat × Lean.Expr) → Option (Nat × Lean.Expr)
  | [] => none
  | [f] => some f
  | (m, a) :: rest =>
    match machPack dom rest with
    | some (n, b) => some (m + n, machConcatE dom m n a b)
    | none => none

/-- The width of a slot or result kind. -/
def machWidth : MixedGateBinder → Nat
  | .bool => 1
  | .bits n => n
  | .domain => 0

/-- The slot fields of the packed value: slot `i` sits above the later slots. -/
def machSlotFields : List (Nat × Nat) → List Sparkle.IR.Machine.SlotField
  | [] => []
  | (w, init) :: rest =>
    { lo := (rest.map (·.1)).sum, width := w, init := init } :: machSlotFields rest

/-- The kind of a Signal type under any telescope: one Bool or
    positive-width BitVec Signal. -/
def machResultKind? : Lean.Expr → Option MixedGateBinder
  | .forallE _ _ b _ => machResultKind? b
  | e =>
    match mixedGateBinderKind? e with
    | some .bool => some .bool
    | some (.bits n) => some (.bits n)
    | _ => none

/-- The value of a closed `Nat` term, by the KERNEL's own reduction (a pure
    function of the environment; no `MetaM`): `none` when the term has
    variables or does not reduce to a literal.  This is how the state-machine
    front end reads a constant computed in Lean — `BitVec.ofInt 32 (64 * 2 ^ 16)`,
    `2 ^ 256 - 2 ^ 32 - 977`, a user constant such as a state encoding — so
    the meaning of such a constant is Lean's, not a second evaluator's. -/
def kernelNat (env : Environment) (e : Lean.Expr) : Option Nat :=
  if e.hasLooseBVars || e.hasFVar || e.hasMVar then none else
  match Lean.Kernel.whnf env {} e with
  | .ok (.lit (.natVal n)) => some n
  | _ => none

/-- A user structure (not a class) all of whose fields are hardware Signals:
    its constructor, and the fields in order. -/
def userStructure? (env : Environment) (s : Name) :
    Option (Name × List (String × MixedGateBinder)) :=
  match Lean.getStructureInfo? env s with
  | some info =>
    if Lean.isClass env s || !inlUserModule env s then none else
    match env.find? s with
    | some (.inductInfo ind) =>
      match ind.ctors with
      | [ctor] =>
        (info.fieldNames.toList.mapM fun f =>
          match env.find? (s ++ f) with
          | some ci => (machResultKind? ci.type).map fun k => (f.toString, k)
          | none => none).map fun fs => (ctor, fs)
      | _ => none
    | _ => none
  | none => none

/-- The kinds of the binders of a type (`none` when one is not a hardware
    binder). -/
def telescopeKinds : Lean.Expr → Option (List MixedGateBinder)
  | .forallE _ ty b _ => (mixedGateBinderKind? ty).bind fun k => (telescopeKinds b).map (k :: ·)
  | _ => some []

/-- A `@[hardware_module]` declaration whose binders are hardware binders
    and whose result is one Signal: their kinds. -/
def instSignature? (env : Environment) (n : Name) :
    Option (List MixedGateBinder × MixedGateBinder) :=
  if !Sparkle.Compiler.isHardwareModule env n then none else
  match env.find? n with
  | some ci => do
    let kinds ← telescopeKinds ci.type
    let res ← machResultKind? ci.type
    some (kinds, res)
  | none => none

/-- A `@[hardware_module]` declaration with hardware binders whose result is
    not one Signal (a structure of Signals): their kinds, and its type. -/
def instSignatureS? (env : Environment) (n : Name) : Option (List MixedGateBinder × Lean.Expr) :=
  if !Sparkle.Compiler.isHardwareModule env n then none else
  match env.find? n with
  | some ci =>
    if (machResultKind? ci.type).isSome || !ci.levelParams.isEmpty then none else
    (telescopeKinds ci.type).map fun kinds => (kinds, ci.type)
  | none => none

/-- The structure facts of an environment. -/
def structEnv (env : Environment) : StructEnv :=
  { proj := userProjection? env, fields := userStructure? env, natOf := kernelNat env,
    inst := instSignature? env, instS := instSignatureS? env,
    prodMatch := Sparkle.Compiler.MachRawSurface.prodMatcherArity? env }

/-- The `let`s in front of an expression, prepended (innermost first) to `acc`. -/
def machRootLets : Lean.Expr → List (Name × Lean.Expr × Lean.Expr) →
    List (Name × Lean.Expr × Lean.Expr) × Lean.Expr
  | .letE nm ty v b _, acc => machRootLets b ((nm, ty, v) :: acc)
  | e, acc => (acc, e)

/-- The root of a declaration's value, after its binders: `let`s in front
    (sub-machines bound before the `circuit do`, constants), then either a
    `runCircuitH` — directly or under ONE field projection of a user
    structure (with `let`s under the projection counted as root `let`s) —
    which is the ENCLOSING machine, or any other expression (a structure of
    sub-machines' results, a projection of one): `(the root lets, field
    selector, the enclosing run, the root expression)`. -/
def machRoot (projs : Name → Option (Name × Nat × Nat)) :
    Lean.Expr → List (Name × Lean.Expr × Lean.Expr) →
      List (Name × Lean.Expr × Lean.Expr) × Option (Name × Nat × Nat) × Option Lean.Expr ×
        Lean.Expr
  | .letE nm ty v b _, acc => machRoot projs b ((nm, ty, v) :: acc)
  | e, acc =>
    if (machRunApp? e).isSome then (acc.reverse, none, some e, e) else
    match inlSpine e [] with
    | (.const p _, args) =>
      match projs p, args.getLast? with
      | some (ctor, numParams, idx), some r =>
        -- `let`s under the projection are root `let`s too (a projection
        -- binds nothing: `proj (let x := v; r)` is `let x := v; proj r`)
        let (acc', r') := machRootLets r acc
        if args.length = numParams + 1 && (machRunApp? r').isSome then
          (acc'.reverse, some (ctor, numParams, idx), some r', e)
        else (acc.reverse, none, none, e)
      | _, _ => (acc.reverse, none, none, e)
    | _ => (acc.reverse, none, none, e)

/-- The result the body returns: the final `pure` value, or its selected
    field when the declaration projects a structure result. -/
def machResult? (sel : Option (Name × Nat × Nat)) (v : Lean.Expr) : Option Lean.Expr :=
  match sel with
  | none => some v
  | some (ctor, numParams, idx) =>
    match inlSpine v [] with
    | (.const c _, args) => if c == ctor then args[numParams + idx]? else none
    | _ => none

/-- The results the body returns, one per output port: the final `pure`
    value (or its selected field) for a Signal result, the constructor's
    field arguments for a structure result. -/
def machResults? (sel : Option (Name × Nat × Nat)) (ctor? : Option Name) (m : Nat)
    (v : Lean.Expr) : Option (List Lean.Expr) :=
  match ctor? with
  | none => (machResult? sel v).map fun e => [e]
  | some ctor =>
    if sel.isSome then none else
    match inlSpine v [] with
    | (.const c _, args) =>
      if c == ctor && m ≤ args.length then some (args.drop (args.length - m)) else none
    | _ => none

/-- The hardware type of a kind. -/
def machHWType : MixedGateBinder → Sparkle.IR.Type.HWType
  | .bool => .bit
  | k => .bitVector (machWidth k)

/-- The output fields of the packed value: output `i` sits above the later
    outputs, and all of them above the slots (`slotsW` bits). -/
def machOutFields (slotsW : Nat) :
    List (String × MixedGateBinder) → List Sparkle.IR.Machine.OutField
  | [] => []
  | (nm, k) :: rest =>
    { name := nm, lo := slotsW + (rest.map fun o => machWidth o.2).sum, width := machWidth k,
      ty := machHWType k } :: machOutFields slotsW rest

/-! ### Normal forms on the state-machine route

A `circuit do` writes the same hardware in several ways: a constant as a
literal or as a Lean computation, an operator at the Signal instance or
lifted through `map` / `<$>` / `<*>`, one operand a plain `BitVec`.  The
gates accept ONE form of each; `machNorm` rewrites the others to it, on
this route only.  Every rewrite is an equation Lean proves by unfolding
(the two sides have the same value at every cycle), and for a declaration
it is checked by the kernel when its endpoint is generated
(`Tools/ShippingMachineCommand.lean`: the body as WRITTEN against the terms
read off the normalised transition). -/

/-- `BitVec w` with a literal width. -/
def machBits? : Lean.Expr → Option Nat
  | .app (.const ``BitVec _) wE => canonicalNatLitValue? wE
  | _ => none

/-- `Signal dom (BitVec w)` with a literal width: the domain and the width. -/
def machSigBits? : Lean.Expr → Option (Lean.Expr × Nat)
  | .app (.app (.const ``Sparkle.Core.Signal.Signal _) dom) ty => (machBits? ty).map fun w => (dom, w)
  | _ => none

/-- The literal `v#w`, as the gates read it. -/
def machBVLit (w v : Nat) : Lean.Expr :=
  mkApp2 (.const ``BitVec.ofNat []) (inlNatLit w) (inlNatLit v)

/-- A closed `BitVec w` value as a literal: itself when it is one, its value
    by the kernel's reduction otherwise. -/
def machLitOf (senv : StructEnv) (w : Nat) (c : Lean.Expr) : Option Lean.Expr :=
  match bitVecLitValue? c with
  | some (w', _) => if w' == w then some c else none
  | none =>
    (senv.natOf (mkApp2 (.const ``BitVec.toNat []) (inlNatLit w) c)).map fun v => machBVLit w v

/-- `Signal.pure c` at `BitVec w`. -/
def machPureE (dom : Lean.Expr) (w : Nat) (c : Lean.Expr) : Lean.Expr :=
  mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom
    (mkApp (.const ``BitVec []) (inlNatLit w)) c

/-- The library's instance of a binary operator on two `BitVec` Signals. -/
def machSigInst : Name → Option Name
  | ``HAdd.hAdd => some ``Sparkle.Core.Signal.instHAddSignalBitVec
  | ``HSub.hSub => some ``Sparkle.Core.Signal.instHSubSignalBitVec
  | ``HMul.hMul => some ``Sparkle.Core.Signal.instHMulSignalBitVec
  | ``HAnd.hAnd => some ``Sparkle.Core.Signal.instHAndSignalBitVec
  | ``HOr.hOr => some ``Sparkle.Core.Signal.instHOrSignalBitVec
  | ``HXor.hXor => some ``Sparkle.Core.Signal.instHXorSignalBitVec
  | ``HShiftLeft.hShiftLeft => some ``Sparkle.Core.Signal.instHShiftLeftSignalBitVec_1
  | ``HShiftRight.hShiftRight => some ``Sparkle.Core.Signal.instHShiftRightSignalBitVec_1
  | _ => none

/-- `a op b` on two `BitVec w` Signals, at the library's instance `inst`. -/
def machSigBin (m inst : Name) (dom : Lean.Expr) (w : Nat) (a b : Lean.Expr) : Lean.Expr :=
  mkApp6 (.const m [.zero, .zero, .zero]) (machSigT dom w) (machSigT dom w) (machSigT dom w)
    (mkApp2 (.const inst []) dom (inlNatLit w)) a b

/-- The canonical instance of a binary operator on `BitVec w` VALUES:
    `instHAdd (BitVec w) (BitVec.instAdd w)`, …, `BitVec.instHShiftLeft w w`
    (a shift by a `BitVec` of the same width). -/
def machScalarInst (m : Name) (w : Nat) : Lean.Expr → Bool
  | .app (.app (.const outer _) a1) a2 =>
    if m == ``HShiftLeft.hShiftLeft then
      outer == ``BitVec.instHShiftLeft && canonicalNatLitValue? a1 == some w &&
        canonicalNatLitValue? a2 == some w
    else if m == ``HShiftRight.hShiftRight then
      outer == ``BitVec.instHShiftRight && canonicalNatLitValue? a1 == some w &&
        canonicalNatLitValue? a2 == some w
    else
      machBits? a1 == some w &&
        (match a2 with
         | .app (.const inner _) wE =>
           canonicalNatLitValue? wE == some w &&
             canonicalScalarMethodInsts.any fun (m', o', i') =>
               m' == m && o' == outer && i' == some inner
         | _ => false)
  | _ => false

/-- A canonical binary operator on `BitVec w` values: the operator and its
    two operands. -/
def machScalarBin? (w : Nat) : Lean.Expr → Option (Name × Lean.Expr × Lean.Expr)
  | .app (.app (.app (.app (.app (.app (.const m _) t1) t2) t3) inst) x) y =>
    if (machSigInst m).isSome && machBits? t1 == some w && machBits? t2 == some w &&
        machBits? t3 == some w && machScalarInst m w inst then some (m, x, y) else none
  | _ => none

/-- `Signal.pure c` with `c` computed in Lean: `c` as a literal. -/
def machNormPure (senv : StructEnv) (e : Lean.Expr) : Lean.Expr :=
  match e with
  | .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.pure ls) dom) ty) c =>
    match ty with
    | .const ``Bool _ =>
      (match c with
       | .const ``Bool.true _ => e
       | .const ``Bool.false _ => e
       | _ =>
         match senv.natOf (mkApp (.const ``Bool.toNat []) c) with
         | some 0 => mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure ls) dom ty (.const ``Bool.false [])
         | some 1 => mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure ls) dom ty (.const ``Bool.true [])
         | _ => e)
    | _ =>
      match machBits? ty with
      | some w =>
        if (bitVecLitValue? c).isSome then e else
        (match machLitOf senv w c with
         | some l => machPureE dom w l
         | none => e)
      | none => e
  | _ => e

/-- A binary operator with one operand a plain `BitVec` (`sig + c`, `c ^^^ sig`):
    the operator on two Signals, the constant as `Signal.pure` of its literal;
    and a concatenation with a computed constant operand: the constant as a
    literal. -/
def machNormMixed (senv : StructEnv) (e : Lean.Expr) : Lean.Expr :=
  match e with
  | .app (.app (.app (.app (.app (.app (.const m ls) α) β) γ) inst) a) b =>
    match canonicalSignalBinKinds m e.getAppArgs with
    | some (true, false) =>
      if m == ``HAppend.hAppend then
        (match machBits? β with
         | some k =>
           if (bitVecLitValue? b).isSome then e else
           (match machLitOf senv k b with
            | some l => mkApp6 (.const m ls) α β γ inst a l
            | none => e)
         | none => e)
      else
        (match machSigBits? γ, machSigInst m with
         | some (dom, w), some si =>
           (match machLitOf senv w b with
            | some l => machSigBin m si dom w a (machPureE dom w l)
            | none => e)
         | _, _ => e)
    | some (false, true) =>
      if m == ``HAppend.hAppend then
        (match machBits? α with
         | some k =>
           if (bitVecLitValue? a).isSome then e else
           (match machLitOf senv k a with
            | some l => mkApp6 (.const m ls) α β γ inst l b
            | none => e)
         | none => e)
      else
        (match machSigBits? γ, machSigInst m with
         | some (dom, w), some si =>
           (match machLitOf senv w a with
            | some l => machSigBin m si dom w (machPureE dom w l) b
            | none => e)
         | _, _ => e)
    | _ => e
  | _ => e

/-- A binary `BitVec` operator lifted through the applicative,
    `Signal.ap (Signal.map (fun x y => x op y) a) b`: the operator on the two
    Signals. -/
def machNormAp (e : Lean.Expr) : Lean.Expr :=
  match e with
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.ap _) dom) tyA) tyB)
      (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map _) _) _) _)
        (.lam _ _ (.lam _ _ body _) _)) a)) b =>
    match machBits? tyA, machBits? tyB with
    | some w, some w' =>
      if w != w' then e else
      (match machScalarBin? w body with
       | some (m, .bvar 1, .bvar 0) =>
         (match machSigInst m with
          | some si => machSigBin m si dom w a b
          | none => e)
       | some (m, .bvar 0, .bvar 1) =>
         (match machSigInst m with
          | some si => machSigBin m si dom w b a
          | none => e)
       | _ => e)
    | _, _ => e
  | _ => e

/-- A `BitVec` expression over the bound variable of a `map` lambda
    (`.bvar 0`, standing for the Signal `a` of width `wa`), with literal or
    computed constants: the same expression on Signals — the Signal
    operators, a concatenation, a slice as a `map` of `extractLsb'`, `not` as
    `allOnes ^^^ ·`, constants as `Signal.pure` of their literal. Returns the
    width and the Signal expression. -/
partial def machLiftScalarN (senv : StructEnv) (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) :
    Lean.Expr → Option (Nat × Lean.Expr)
  | .bvar i => vars[i]?
  | e@(.app (.app (.app (.app (.app (.app (.const m _) t1) t2) t3) inst) x) y) =>
    -- a width written as a computation (`8 + 8`) is read by the kernel
    let bitsW (t : Lean.Expr) : Option Nat := machBits? t <|> (match t with
      | .app (.const ``BitVec _) wE => senv.natOf wE
      | _ => none)
    if m == ``HAppend.hAppend then do
      let mw ← bitsW t1
      let nw ← bitsW t2
      unless inst.getAppFn.isConstOf ``BitVec.instHAppendHAddNat do none
      let (mx, x') ← machLiftScalarN senv dom vars x
      let (ny, y') ← machLiftScalarN senv dom vars y
      if mx != mw || ny != nw then none else
      some (mw + nw, machConcatE dom mw nw x' y')
    else
    match machSigInst m, bitsW t1 with
    | some si, some w =>
      if bitsW t2 == some w && bitsW t3 == some w && machScalarInst m w inst then do
        let (wx, x') ← machLiftScalarN senv dom vars x
        let (wy, y') ← machLiftScalarN senv dom vars y
        if wx != w || wy != w then none else
        some (w, machSigBin m si dom w x' y')
      else machLiftConst senv dom e
    | _, _ => machLiftConst senv dom e
  | e@(.app (.app (.app (.app (.const ``BitVec.extractLsb' ls) nE) sE) lE) x) => do
    let n ← canonicalNatLitValue? nE <|> senv.natOf nE
    let st ← canonicalNatLitValue? sE <|> senv.natOf sE
    let l ← canonicalNatLitValue? lE <|> senv.natOf lE
    if !x.hasLooseBVars then machLiftConst senv dom e else
    let (wx, x') ← machLiftScalarN senv dom vars x
    if wx != n then none else
    let f := Lean.Expr.lam `x (mkApp (.const ``BitVec []) (inlNatLit n))
      (mkApp4 (.const ``BitVec.extractLsb' ls) (inlNatLit n) (inlNatLit st) (inlNatLit l) (.bvar 0))
      .default
    some (l, mkApp5 (.const ``Sparkle.Core.Signal.Signal.map [.zero, .zero]) dom
      (mkApp (.const ``BitVec []) (inlNatLit n)) (mkApp (.const ``BitVec []) (inlNatLit l)) f x')
  | e@(.app (.app (.const ``BitVec.not _) nE) x) => do
    if !x.hasLooseBVars then machLiftConst senv dom e else
    let n ← canonicalNatLitValue? nE
    let (wx, x') ← machLiftScalarN senv dom vars x
    if wx != n then none else
    some (n, machSigBin ``HXor.hXor ``Sparkle.Core.Signal.instHXorSignalBitVec dom n
      (machPureE dom n (machBVLit n (2 ^ n - 1))) x')
  -- sign extension and arithmetic right shift: their derived forms
  -- (`MachSignOps`, the right-hand sides of `ShippingSignOps.map_signExtend`
  -- / `ashr_eq` / `map_sshiftRight`)
  | e@(.app (.app (.app (.const ``BitVec.signExtend _) wE) vE) x) => do
    if !x.hasLooseBVars then machLiftConst senv dom e else
    let w ← canonicalNatLitValue? wE
    let v ← canonicalNatLitValue? vE <|> senv.natOf vE
    let (wx, x') ← machLiftScalarN senv dom vars x
    if wx != w || w == 0 || v ≤ w then none else
    some (v, Sparkle.Compiler.MachSignOps.sextE inlNatLit (machConcatE dom) dom (v - w) w x')
  | e@(.app (.app (.app (.const ``BitVec.sshiftRight _) nE) x) s) => do
    if !x.hasLooseBVars then machLiftConst senv dom e else
    let n ← canonicalNatLitValue? nE
    if n == 0 then none else
    let (wx, x') ← machLiftScalarN senv dom vars x
    if wx != n then none else
    let y' ← match s with
      | .app (.app (.const ``BitVec.toNat _) mE) y => do
        if canonicalNatLitValue? mE != some n then none else
        let (wy, y') ← machLiftScalarN senv dom vars y
        if wy != n then none else some y'
      | _ => do
        if s.hasLooseBVars then none else
        let k ← canonicalNatLitValue? s <|> senv.natOf s
        if k ≥ 2 ^ n then none else some (machPureE dom n (machBVLit n k))
    some (n, Sparkle.Compiler.MachSignOps.ashrE inlNatLit
      (fun m a b => machSigBin m ((machSigInst m).getD .anonymous) dom n a b) dom n x' y')
  -- `-x` is `0 - x` (by the definitions of `BitVec.neg` and `BitVec.sub`)
  | e@(.app (.app (.app (.const ``Neg.neg _) (.app (.const ``BitVec _) nE)) _) x) => do
    if !x.hasLooseBVars then machLiftConst senv dom e else
    let n ← canonicalNatLitValue? nE
    let (wx, x') ← machLiftScalarN senv dom vars x
    if wx != n then none else
    some (n, machSigBin ``HSub.hSub ``Sparkle.Core.Signal.instHSubSignalBitVec dom n
      (machPureE dom n (machBVLit n 0)) x')
  | e@(.app (.app (.app (.const ``Complement.complement _) (.app (.const ``BitVec _) nE)) _) x) => do
    if !x.hasLooseBVars then machLiftConst senv dom e else
    let n ← canonicalNatLitValue? nE
    let (wx, x') ← machLiftScalarN senv dom vars x
    if wx != n then none else
    some (n, machSigBin ``HXor.hXor ``Sparkle.Core.Signal.instHXorSignalBitVec dom n
      (machPureE dom n (machBVLit n (2 ^ n - 1))) x')
  | e => machLiftConst senv dom e
where
  /-- A closed constant: its literal, as `Signal.pure`. -/
  machLiftConst (senv : StructEnv) (dom e : Lean.Expr) : Option (Nat × Lean.Expr) :=
    if e.hasLooseBVars then none else
    match bitVecLitValue? e with
    | some (w, _) => some (w, machPureE dom w e)
    | none => none

/-- `machLiftScalarN` over the one variable of a `map` lambda. -/
def machLiftScalar (senv : StructEnv) (dom a : Lean.Expr) (wa : Nat) (e : Lean.Expr) :
    Option (Nat × Lean.Expr) :=
  machLiftScalarN senv dom [(wa, a)] e

/-- The spine of a lifted application `Signal.ap (… (Signal.ap (Signal.map f
    a₁) a₂) …) aₙ`: the domain, `f`, and the arguments with their element
    types, first to last. -/
def machApSpine : Lean.Expr → List (Lean.Expr × Lean.Expr) →
    Option (Lean.Expr × Lean.Expr × List (Lean.Expr × Lean.Expr))
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.ap _) _) α) _) f) x, acc =>
    machApSpine f ((α, x) :: acc)
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map _) dom) α) _) f) a, acc =>
    some (dom, f, (α, a) :: acc)
  | _, _ => none

/-- The body under `n` lambdas. -/
def machLamBody : Nat → Lean.Expr → Option Lean.Expr
  | 0, e => some e
  | n + 1, .lam _ _ b _ => machLamBody n b
  | _, _ => none

/-- A lifted function of any arity over `BitVec` Signals,
    `f <$> a₁ <*> … <*> aₙ`: its body on Signals (`machLiftScalarN`, the
    variables standing for the arguments). A comparison body becomes the
    canonical lifted comparison of the two lifted operands. -/
def machNormApLift (senv : StructEnv) (e : Lean.Expr) : Lean.Expr :=
  match e with
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.ap _) _) _) β) _) _ =>
    ((do
      let (dom, f, args) ← machApSpine e []
      let n := args.length
      if n < 2 then none else
      let body ← machLamBody n f
      let vars ← args.reverse.mapM fun (p : Lean.Expr × Lean.Expr) =>
        (machBits? p.1).map fun w => (w, p.2)
      match machBits? β with
      | some wb =>
        let (w, r) ← machLiftScalarN senv dom vars body
        if w == wb then some r else none
      | none =>
        if !β.isConstOf ``Bool then none else
        match body with
        | .app (.app (.app (.const c lsC) wE) x) y =>
          if !(c == ``BitVec.ult || c == ``BitVec.ule || c == ``BitVec.slt ||
              c == ``BitVec.sle) then none else do
          let w ← canonicalNatLitValue? wE
          let (wx, x') ← machLiftScalarN senv dom vars x
          let (wy, y') ← machLiftScalarN senv dom vars y
          if wx != w || wy != w then none else
          let bv := mkApp (.const ``BitVec []) (inlNatLit w)
          -- the canonical binder names of the `<$>`/`<*>` normaliser
          let fn := Lean.Expr.lam `x1 bv (.lam `x2 bv
            (mkApp3 (.const c lsC) (inlNatLit w) (.bvar 1) (.bvar 0)) .default) .default
          let fnT := Lean.Expr.forallE `a bv (.const ``Bool []) .default
          some (mkApp5 (.const ``Sparkle.Core.Signal.Signal.ap [.zero]) dom bv (.const ``Bool [])
            (mkApp5 (.const ``Sparkle.Core.Signal.Signal.map [.zero]) dom bv fnT fn x') y')
        | _ => none) : Option Lean.Expr).getD e
  | _ => e

/-- A `Bool`-valued lambda over a `BitVec` Signal `a` of width `wa`: an
    equality of lifted operands (`x == y`, `Signal.beq`), under `!`
    (`~~~`, the Signal's Bool complement). -/
partial def machBoolMap (senv : StructEnv) (dom a : Lean.Expr) (wa : Nat) :
    Lean.Expr → Option Lean.Expr
  | .app (.const c _) x =>
    if c == ``Bool.not || c == ``not then do
      let x' ← machBoolMap senv dom a wa x
      some (mkApp3 (.const ``Complement.complement [.zero])
        (mkApp2 (.const ``Sparkle.Core.Signal.Signal [.zero]) dom (.const ``Bool []))
        (mkApp (.const ``Sparkle.Core.Signal.instComplementSignalBool []) dom) x')
    else none
  | .app (.app (.app (.app (.const ``BEq.beq _) ty) inst) x) y => do
    let w ← machBits? ty
    unless inst.isAppOf ``instBEqOfDecidableEq do none
    let (wx, x') ← machLiftScalarN senv dom [(wa, a)] x
    let (wy, y') ← machLiftScalarN senv dom [(wa, a)] y
    if wx != w || wy != w then none else
    some (mkApp5 (.const ``Sparkle.Core.Signal.Signal.beq []) ty dom
      (mkApp2 (.const ``instBEqOfDecidableEq [.zero]) ty
        (mkApp (.const ``instDecidableEqBitVec []) (inlNatLit w))) x' y')
  | _ => none

/-- A map over a `BitVec` Signal, `Signal.map f a` or `f <$> a`:
    * `fun x => x op c` / `fun x => c op x` with a constant `c`: the operator
      on `a` and `Signal.pure` of the literal;
    * a slice whose start is computed in Lean (`5 * 8`): the start as a
      literal.
    * any other `BitVec` lambda: lifted to Signals (`machLiftScalar`).
    `mk` rebuilds the node around another function. -/
def machNormMap (senv : StructEnv) (dom tyA tyB f a : Lean.Expr) (mk : Lean.Expr → Lean.Expr)
    (e : Lean.Expr) : Lean.Expr :=
  match f with
  | .lam nm t (.app (.app (.app (.app (.const ``BitVec.extractLsb' ls) wsE) startE) lenE)
      (.bvar 0)) bi =>
    (match canonicalNatLitValue? startE with
     | some _ => e
     | none =>
       match senv.natOf startE with
       | some start =>
         mk (.lam nm t (mkApp4 (.const ``BitVec.extractLsb' ls) wsE (inlNatLit start) lenE
           (.bvar 0)) bi)
       | none => e)
  -- `map (fun x => ~~~x)` / `map BitVec.not` is `allOnes ^^^ a`
  | .lam _ _ (.app (.app (.const ``BitVec.not _) _) (.bvar 0)) _ =>
    (match machBits? tyA, machBits? tyB with
     | some w, some w' =>
       if w != w' then e else
       machSigBin ``HXor.hXor ``Sparkle.Core.Signal.instHXorSignalBitVec dom w
         (machPureE dom w (machBVLit w (2 ^ w - 1))) a
     | _, _ => e)
  | .lam _ _ (.app (.app (.app (.const ``Complement.complement _) _)
      (.app (.const ``BitVec.instComplement _) _)) (.bvar 0)) _ =>
    (match machBits? tyA, machBits? tyB with
     | some w, some w' =>
       if w != w' then e else
       machSigBin ``HXor.hXor ``Sparkle.Core.Signal.instHXorSignalBitVec dom w
         (machPureE dom w (machBVLit w (2 ^ w - 1))) a
     | _, _ => e)
  | .lam _ _ body _ =>
    (match machBits? tyA, machBits? tyB with
     | some w, some w' =>
       if w != w' then machNormLift senv dom tyA tyB a body e else
       (match machScalarBin? w body with
        | some (m, .bvar 0, c) =>
          if c.hasLooseBVars then e else
          (match machSigInst m, machLitOf senv w c with
           | some si, some l => machSigBin m si dom w a (machPureE dom w l)
           | _, _ => e)
        | some (m, c, .bvar 0) =>
          if c.hasLooseBVars then e else
          (match machSigInst m, machLitOf senv w c with
           | some si, some l => machSigBin m si dom w (machPureE dom w l) a
           | _, _ => e)
        | _ => machNormLift senv dom tyA tyB a body e)
     | some wa, none =>
       if tyB.isConstOf ``Bool then (machBoolMap senv dom a wa body).getD e else e
     | _, _ => e)
  | _ => e
where
  /-- Any other `BitVec` lambda: lifted to Signals (`machLiftScalar`). -/
  machNormLift (senv : StructEnv) (dom tyA tyB a body e : Lean.Expr) : Lean.Expr :=
    match machBits? tyA, machBits? tyB with
    | some wa, some wb =>
      match machLiftScalar senv dom a wa body with
      -- the lambda's variable became `a`; every other leaf is a closed
      -- constant (`machLiftConst`), so `r` lives in the node's context
      | some (w, r) => if w == wb then r else e
      | none => e
    | _, _ => e

/-- One node of `machNorm`. -/
def machNormNode (senv : StructEnv) (e : Lean.Expr) : Lean.Expr :=
  match e with
  -- `Signal.lit dom x` is `Signal.pure x`
  | .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.lit ls) ty) dom) x =>
    machNormPure senv (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure ls) dom ty x)
  | .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.pure _) _) _) _ => machNormPure senv e
  -- `~~~a` on a `BitVec` Signal is `allOnes ^^^ a` (`BitVec.not`, by definition)
  | .app (.app (.app (.const ``Complement.complement _) sigTy)
      (.app (.app (.const ``Sparkle.Core.Signal.instComplementSignalBitVec _) _) _)) a =>
    (match machSigBits? sigTy with
     | some (dom, w) =>
       machSigBin ``HXor.hXor ``Sparkle.Core.Signal.instHXorSignalBitVec dom w
         (machPureE dom w (machBVLit w (2 ^ w - 1))) a
     | none => e)
  -- `-a` on a `BitVec` Signal is `pure 0 - a` (pointwise `0 - x = -x`)
  | .app (.app (.app (.const ``Neg.neg _) sigTy)
      (.app (.app (.const ``Sparkle.Core.Signal.instNegSignalBitVec _) _) _)) a =>
    (match machSigBits? sigTy with
     | some (dom, w) =>
       machSigBin ``HSub.hSub ``Sparkle.Core.Signal.instHSubSignalBitVec dom w
         (machPureE dom w (machBVLit w 0)) a
     | none => e)
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.ap _) _) _) _) _) _ =>
    let e' := machNormAp e
    if e' == e then machNormApLift senv e else e'
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map ls) dom) tyA) tyB) f)
      a =>
    machNormMap senv dom tyA tyB f a
      (fun f' => mkApp5 (.const ``Sparkle.Core.Signal.Signal.map ls) dom tyA tyB f' a) e
  | .app (.app (.app (.app (.app (.app (.const ``Functor.map ls)
      (.app (.const ``Sparkle.Core.Signal.Signal us) dom))
      (.app (.const ``Sparkle.Core.Signal.instFunctorSignal is) dom')) tyA) tyB) f) a =>
    machNormMap senv dom tyA tyB f a
      (fun f' => mkApp6 (.const ``Functor.map ls)
        (.app (.const ``Sparkle.Core.Signal.Signal us) dom)
        (.app (.const ``Sparkle.Core.Signal.instFunctorSignal is) dom') tyA tyB f' a) e
  | .app (.app (.app (.app (.app (.app (.const _ _) _) _) _) _) _) _ => machNormMixed senv e
  | _ => e

/-- The body of a `circuit do` with every node in the form the gates accept
    (see the section comment).  Types of binders are left as written. -/
partial def machNorm (senv : StructEnv) : Lean.Expr → Lean.Expr
  | e@(.app f a) =>
    -- `Signal.ashr a b`: its derived form (`MachSignOps`, `ShippingSignOps.ashr_eq`)
    match e.getAppFn, e.getAppArgs with
    | .const ``Sparkle.Core.Signal.Signal.ashr _, #[dom, nE, x, y] =>
      match canonicalNatLitValue? nE with
      | some n =>
        if n == 0 then e else
        Sparkle.Compiler.MachSignOps.ashrE inlNatLit
          (fun m a b => machSigBin m ((machSigInst m).getD .anonymous) dom n a b)
          dom n (machNorm senv x) (machNorm senv y)
      | none => e
    | _, _ =>
    -- the raw `runCircuitH` surface first (`MachRawSurface`)
    match Sparkle.Compiler.MachRawSurface.rawNode senv.prodMatch e with
    | some e' => machNorm senv e'
    | none => machNormNode senv (.app (machNorm senv f) (machNorm senv a))
  | .lam n t b bi => .lam n t (machNorm senv b) bi
  -- a `Nat` `let` (a slice position computed in Lean): substituted, so the
  -- position is a closed term the kernel reduces
  | .letE n t v b nd =>
    if t.isConstOf ``Nat then machNorm senv (b.instantiate1 v)
    -- a closed `BitVec` value `let` (a constant computed in Lean): substituted,
    -- so its uses are closed terms the kernel reduces to literals
    else if (machBits? t).isSome && !v.hasLooseBVars then machNorm senv (b.instantiate1 v)
    else .letE n t (machNorm senv v) (machNorm senv b) nd
  | e => e

/-- One node of `machCanonAp`: `Signal.ap (Signal.map f a) b` with the
    canonical binder names of the `<$>`/`<*>` normaliser (`inlCanonLam`,
    `inlCanonPi`). -/
def machCanonApNode : Lean.Expr → Lean.Expr
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.ap ls) dom) α) β)
      (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map ls') dom') α') γ)
        fn) x)) b =>
    mkApp5 (.const ``Sparkle.Core.Signal.Signal.ap ls) dom α β
      (mkApp5 (.const ``Sparkle.Core.Signal.Signal.map ls') dom' α' (inlCanonPi γ)
        (inlCanonLam 0 fn) x) b
  | e => e

/-- Canonical binder names in every `Signal.ap (Signal.map f a) b` of a
    transition body.  A lift written directly in this form — as `circuit do`
    writes the tests of its `match` — carries hygienic macro names, different
    in every declaration; binder names have no meaning, and with the canonical
    ones the body is the quotation of a source term. -/
def machCanonAp : Lean.Expr → Lean.Expr
  | .app f a => machCanonApNode (.app (machCanonAp f) (machCanonAp a))
  | e => e

/-- A hand-written `Signal.loop f` as the WHOLE value (after its `let`s): read
    as `let s := Signal.loop f; s`, the form the loop reader takes. -/
def machLoopAsLet : Lean.Expr → Lean.Expr
  | .letE n t v b nd => .letE n t v (machLoopAsLet b) nd
  | e@(.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.loop ls) dom) α) _) _) =>
    .letE `loop (mkApp2 (.const ``Sparkle.Core.Signal.Signal ls) dom α) e (.bvar 0) false
  | e => e

/-- A state machine on the certified route: the transition's binders (the
    declaration's, then one per slot), its packed body under them, and where
    the pieces of the packed value sit. -/
structure MachineShape where
  binders : List (Name × MixedGateBinder)
  body : Lean.Expr
  layout : Sparkle.IR.Machine.Layout
  /-- `(first slot, slot count)` of every machine read: the enclosing
      machine first (none when the root is an expression of sub-machines),
      then each nested `runCircuitH` in reading order. -/
  runs : List (Nat × Nat) := []
  /-- The `@[hardware_module]` calls of the body, in reading order: the
      module, the `let`s holding its arguments, the kind of its result. Their
      outputs are the binders right after the declaration's. -/
  insts : List (Name × List Nat × MixedGateBinder) := []
  /-- `(first slot, slot count)` of every hand-written `Signal.loop`. -/
  loops : List (Nat × Nat) := []
  /-- For calls with several outputs or of sequential children: the child's
      output port each `insts` entry reads (entries of one call share its
      module and argument `let`s: one instance, `closeInstsG`). Empty: every
      call is a one-output combinational child (`closeInsts`). -/
  instFields : List String := []

/-- The acceptance test of the state-machine route: the declaration's value
    is a lambda telescope of hardware binders over `let`s and a
    `runCircuitH` (possibly under one structure-field projection), or over an
    expression of `runCircuitH`s; every body is a chain of `Circuit.next`
    writes ending in `pure`, every slot a Bool or a positive-width BitVec
    with a literal reset value, the result one Signal or a structure of
    Signals (one output port per field, named after it), and the packed
    transition a body the unified gate accepts.

    A `runCircuitH` inside a body or a root `let` — a sub-machine whose
    result the body uses — is read as part of ONE machine: its slots follow
    the enclosing machine's (`MachRead.runs` says where each starts), its
    writes join the transition, and the uses of its result see the result
    terms.  `Tools/ShippingMachineNest.lean` proves that this machine is the
    declaration.

    The transition's telescope is the declaration's binders, one binder per
    slot, and one binder per hardware `let` of the bodies; its packed value is
    `let₀ ++ … ++ letₖ₋₁ ++ result₀ ++ … ++ next₀ ++ … ++ nextₙ₋₁`, where a `let`
    value mentions earlier `let`s only.  `Sparkle.IR.Machine.closeLets` ties
    each `let` binder to its field, so a `let` used many times is compiled
    once. -/
def machineShape? (symbolicMode : Bool) (parameters : List (String × Nat)) (ci : ConstantInfo)
    (senv : StructEnv) (allowInsts : Bool := true) : Option MachineShape :=
  match ci with
  | .defnInfo d =>
    if symbolicMode || !parameters.isEmpty then none else do
    -- a tuple-typed input is one packed port (`MachTupleIn`)
    let (bs, e) ← mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value)
    -- a tuple result is ONE port `out`, the components packed
    let tup? := machTupleKinds? d.type
    let (ctor?, outs) ← match tup? with
      | some ks => some (none, [("out", MixedGateBinder.bits (ks.map machWidth).sum)])
      | none => machOuts? senv d.type
    if outs.isEmpty || !outs.all (fun o => Sparkle.IR.Machine.outNameOk o.1) ||
        !decide (outs.map (·.1)).Nodup then none else
    -- (literal `Nat` sums folded again: a width `W + 1` whose `W` was a
    -- `let` is a literal sum only after `machNorm` substituted it)
    let e := machLoopAsLet (Sparkle.Compiler.MachRawSurface.rootFloat
      (Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue?
        (inlFoldNat (machNorm senv e))))
    let (rootLets, sel, run?, root) := machRoot senv.proj e []
    -- the enclosing machine's slots come first
    let st : MachRead := {}
    let run? := run?.bind machRunApp?
    let st ← match run? with
      | some (dom, αs, initsE, body) => do
        -- the domain in the root context: binders then root lets, so its
        -- placeholder is read with the root lets as (unused) context
        let (dom', _) ← machConv senv (rootLets.map fun _ => .unit) 0 dom st
        let (_, st) ← machReserve senv.natOf dom' αs initsE body st
        pure st
      | none => pure st
    -- the root lets, in order
    let (env, st) ← rootLets.foldlM (init := (([] : List MachVal), st)) fun (env, st) (nm, ty, v) => do
      if v.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then
        -- a hand-written state machine
        let (mv, st) ← machLoopRoot senv env v st
        pure (mv :: env, st)
      else
      match machTailV env 0 v, machHandleV env 0 v with
      | none, none =>
        let (v', st) ← machConv senv env 0 v st
        let (x, lets) := machBindLet nm ty v' st.lets
        pure (.val x :: env, { st with lets := lets })
      | _, _ => none
    -- the enclosing machine's chain, or the root expression
    let (st, v) ← match run? with
      | some (_, _, _, body) => do
        let (ws, v, st) ← machChain senv (.regs 0 :: env) body st
        pure ({ st with ws := st.ws ++ ws.toArray }, v)
      | none => do
        let (v, st) ← machConv senv env 0 root st
        pure (st, v)
    let n := st.kinds.size
    -- no slot: a combinational body with `let`s (no clock); only through the
    -- unfolded entry constant, never instead of a combinational gate
    if n = 0 && (!st.insts.isEmpty || !st.loops.isEmpty || !st.runs.isEmpty) then none else
    if !allowInsts && !st.insts.isEmpty then none else
    -- a hand-written loop alone, or loops as sub-machines of a `circuit do`
    -- (the endpoint's telescope, `TeleT.loop`); several loops alone or a loop
    -- with calls and no enclosing machine are not read
    if !st.loops.isEmpty && st.runs.isEmpty && (!st.insts.isEmpty || st.loops.size != 1) then
      none else
    let kinds := st.kinds.toList
    let k := st.lets.size
    let kI := st.insts.size
    let domE ← st.dom <|> machTypeDom? d.type
    let (dom', resetKind) ← machDom? (kI + n + k) domE
    let letFields ← st.lets.toList.mapM fun (_, kind, value) =>
      machField dom' kind (machClose kI n k 0 value)
    let outFields ← match tup? with
      | some ks => do
        let parts ← machBundleParts? ks.length v
        let fs ← (ks.zip parts).mapM fun (kind, p) => machField dom' kind (machClose kI n k 0 p)
        let packed ← machPack dom' fs
        pure [packed]
      | none => do
        let outEs ← machResults? sel ctor? outs.length v
        if outEs.length != outs.length then none else
        (outs.zip outEs).mapM fun ((_, kind), outE) =>
          machField dom' kind (machClose kI n k 0 outE)
    let slotFields ← ((List.range n).zip kinds).mapM fun (i, kind) =>
      machField dom' kind (machClose kI n k 0 (machNext i st.ws.toList))
    let (_, packed) ← machPack dom' (letFields ++ outFields ++ slotFields)
    let body := machCanonAp packed
    let instBinders := (List.range kI).zip (st.insts.toList.map (·.2.2)) |>.map
      fun (j, kind) => (Name.mkSimple s!"inst{j}", kind)
    let binders : List (Name × MixedGateBinder) := bs ++ instBinders ++
      (st.names.toList.zip kinds) ++ st.lets.toList.map fun (nm, kind, _) => (nm, kind)
    if unifiedGateRoot (binders.map (·.2)).toArray body then
      some
        { binders := binders
          body := body
          layout :=
            { slots := machSlotFields ((kinds.map machWidth).zip st.inits.toList)
              outs := machOutFields (kinds.map machWidth).sum outs
              resetKind := resetKind
              lets := k }
          runs := st.runs.toList
          insts := st.insts.toList
          instFields := if st.instStruct then st.instFields.toList else []
          loops := st.loops.toList }
    else none
  | _ => none

/-- The `@[hardware_module]` calls of a closed machine module: each child
    compiled by the real entry (`sparkleChildSynth`), its output port of the
    transition tied to an instance (`Sparkle.IR.Machine.closeInsts`). `t` is
    the transition module as the harness returned it (its port names). -/
def closeInstsM (shape : MachineShape) (t m : Sparkle.IR.AST.Module)
    (design : Sparkle.IR.AST.Design) :
    MetaM (Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) := do
  let some synth ← sparkleChildSynth.get | return none
  let children ← shape.insts.mapM fun (c, _, _) => synth c
  let kI := shape.insts.length
  let n := shape.layout.slots.length
  -- `t.inputs` has one port per binder EXCEPT a domain binder: count the
  -- declaration's ports, not its binders (the call outputs and `let`s come
  -- after them, and are never domains)
  let nDecl := shape.binders.length - kI - n - shape.layout.lets
  let nIn := ((shape.binders.take nDecl).filter (fun b => b.2 != .domain)).length
  return Sparkle.IR.Machine.closeInsts nIn kI n (t.inputs.map (·.name))
    (shape.insts.map (·.2.1)) children (m, design)

/-- `closeInstsM` for calls with several outputs or of sequential children
(`Sparkle.IR.Machine.closeInstsG`). -/
def closeInstsGM (shape : MachineShape) (t m : Sparkle.IR.AST.Module)
    (design : Sparkle.IR.AST.Design) :
    MetaM (Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) := do
  let some synth ← sparkleChildSynth.get | return none
  let children ← shape.insts.mapM fun (c, _, _) => synth c
  let kI := shape.insts.length
  let n := shape.layout.slots.length
  let nDecl := shape.binders.length - kI - n - shape.layout.lets
  let nIn := ((shape.binders.take nDecl).filter (fun b => b.2 != .domain)).length
  return Sparkle.IR.Machine.closeInstsG nIn kI n (t.inputs.map (·.name))
    (shape.insts.map (·.2.1)) shape.instFields children (m, design)

/-- The synthesis of a state machine: the transition through the certified
    combinational harness, the `let` ports tied to their fields, then the
    slot ports closed into registers, and the `@[hardware_module]` calls
    tied to instances. `none` when the `let`s cannot be tied (`closeLets`)
    or a call cannot (`closeInsts`); the caller then takes the legacy
    route. -/
def synthesizeMachineCertified (translate : TranslateFn) (logProf : String → IO Unit)
    (declName : Name) (shape : MachineShape) :
    MetaM (Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) := do
  let (t, design) ← synthesizeMixedCertified translate logProf declName shape.binders shape.body
  match Sparkle.IR.Machine.closeLets shape.layout.lets t with
  | some t' =>
    match shape.insts with
    | [] => return some (Sparkle.IR.Machine.closeMachine shape.layout t', design)
    | _ :: _ =>
      if shape.instFields.isEmpty then
        closeInstsM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') design
      else closeInstsGM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') design
  | none => return none

/-- The constant the entry hands to `synthesizeFromConst`: the declaration as
    read when a certified gate accepts it (nothing changes for those), or when
    no gate accepts its unfolding either (the legacy route sees the original);
    the UNFOLDED declaration exactly when the original misses both gates and
    the unfolding passes one, or is a state machine (`machineShape?`, with
    the structure facts `projs` of the run's environment). -/
def entryConst (certifiedFrontEnd symbolicMode : Bool) (parameters : List (String × Nat))
    (ci : ConstantInfo) (isInst : Lean.Expr → Bool) (inl : Lean.Expr → Lean.Expr)
    (projs : StructEnv) : ConstantInfo :=
  if certifiedFrontEnd && !symbolicMode && parameters.isEmpty &&
      (certifiedShape? symbolicMode parameters ci).isNone &&
      (mixedCertifiedShape? symbolicMode parameters ci isInst).isNone then
    if (certifiedShape? symbolicMode parameters (inlinedConst inl ci)).isSome ||
        (mixedCertifiedShape? symbolicMode parameters (inlinedConst inl ci) isInst).isSome ||
        (machineShape? symbolicMode parameters (inlinedConst inl ci) projs).isSome
    then inlinedConst inl ci else ci
  else ci

/-- Everything the entry does AFTER reading the declaration, as a function of the
    `ConstantInfo` it read.  `synthesizeCombinationalCoreWith` calls it with the
    result of `getConstInfo declName`, so a theorem about this function applies to
    the constant that the SAME run read (Tools/ShippingEntrySoundness.lean). -/
def synthesizeFromConst (translate : TranslateFn) (logProf : String → IO Unit)
    (declName : Name) (parameters : List (String × Nat)) (symbolicMode : Bool)
    (certifiedFrontEnd : Bool) (constInfo : ConstantInfo)
    (isInst : Lean.Expr → Bool := fun _ => false) :
    MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
  match (if certifiedFrontEnd then certifiedShape? symbolicMode parameters constInfo else none) with
  | some (bs, body) =>
    logProf s!"[profile] synthesizeCombinational {declName} certified front end"
    let result ← synthesizeCertified translate logProf declName bs body
    sparkleSubModuleCache.modify (·.insert declName result)
    return result
  | none =>
  match (if certifiedFrontEnd then mixedCertifiedShape? symbolicMode parameters constInfo isInst else none) with
  | some (bs, body) =>
    logProf s!"[profile] synthesizeCombinational {declName} mixed certified front end"
    let result ← synthesizeMixedCertified translate logProf declName bs body
    sparkleSubModuleCache.modify (·.insert declName result)
    return result
  | none =>
  -- A general `circuit do`: its transition through the certified
  -- combinational harness, then closed into registers.  The entry constant
  -- is the unfolded declaration when that is a machine shape (`entryConst`),
  -- so the shape is read off the constant as handed over.
  let machine? ←
    if certifiedFrontEnd && !symbolicMode && parameters.isEmpty then do
      let env ← getEnv
      pure (machineShape? symbolicMode parameters constInfo (structEnv env))
    else pure none
  let machineResult? ←
    match machine? with
    | some shape => synthesizeMachineCertified translate logProf declName shape
    | none => pure none
  match machineResult? with
  | some result =>
    logProf s!"[profile] synthesizeCombinational {declName} machine certified front end"
    sparkleSubModuleCache.modify (·.insert declName result)
    return result
  | none =>
  -- Issue #67: memoise the (Module × Design) result by declName
  -- for the duration of one outermost synth.  A `@[hardware_module]`
  -- projected across many output fields (e.g. Keccak's 25 lane
  -- fields, each a leaf of the parent's return) otherwise re-walks
  -- this whole body once per projection — and its own sub-modules
  -- (e.g. keccakRcHW) O(N) times on top, giving the O(N²) blow-up.
  -- The cache is reset at depth==0 alongside the other per-synth
  -- caches, so it can't alias across independent top-level synths.
  if !symbolicMode then
    let memo ← sparkleSubModuleCache.get
    if let some cached := memo.get? declName then
      logProf s!"[profile] synthesizeCombinational {declName} MEMO HIT"
      return cached
  logProf s!"[profile] getConstInfo done"
  match constInfo with
  | .defnInfo defnInfo =>
    logProf s!"[profile] synthesizeCombinational {declName} starting (defnInfo)"
    let t0 ← IO.monoMsNow
    logProf s!"[profile] calling openRecordInputs"
    let body0 ← openRecordInputs defnInfo.value
    -- Strip sim-only Signal.memoize wrappers from the body
    -- BEFORE translation.  This breaks the FSM memoize-cycle
    -- root cause (see stripMemoizeWrappers doc).
    let body := stripMemoizeWrappers body0
    let t1 ← IO.monoMsNow
    logProf s!"[profile] openRecordInputs done ({t1 - t0} ms)"
    -- Open the lambda telescope ONCE so every leaf sees the
    -- same fresh fvars.  Previously each leaf re-entered
    -- `withLocalDecl` independently, giving the same source
    -- argument fresh fvars per leaf — distinct enough that
    -- `Expr.equal` rejected structurally identical sub-trees
    -- and the per-synth cache missed across leaf boundaries
    -- (Issue #67).
    Lean.Meta.lambdaTelescope body fun xs innerBody => do
      logProf s!"[profile] calling splitReturnLeaves"
      if symbolicMode then
        for (parameterName, _) in parameters do
          let mut foundNatBinder := false
          for x in xs do
            let decl ← x.fvarId!.getDecl
            if decl.userName.toString == parameterName then
              let binderType ← whnf decl.type
              if binderType.isConstOf ``Nat then
                foundNatBinder := true
          if !foundNatBinder then
            throwError
              s!"Requested retained hardware parameter '{parameterName}' is not a top-level Nat binder of {declName}"

      let leaves ← splitReturnLeaves innerBody
      let t2 ← IO.monoMsNow
      logProf s!"[profile] splitReturnLeaves done ({t2 - t1} ms, leaves={leaves.size})"
      let cacheRef ← IO.mkRef ({} : Lean.ExprStructMap String)
      let compilerBody :=
        emitLeaves translate cacheRef logProf leaves.toList none 0
      let compiler := bindInputsLegacy parameters symbolicMode xs 0 compilerBody
      let circuitState := CircuitM.init declName.toString
      let (_, finalCircuitState) ←
        (compiler.run (entryCompilerState symbolicMode cacheRef)).run circuitState
      let result ← finishSynth declName parameters symbolicMode finalCircuitState
      -- Issue #67: cache the result by declName for reuse by
      -- later projections/instantiations within this synth.
      if !symbolicMode then
        sparkleSubModuleCache.modify (·.insert declName result)
      return result
  | _ =>
    throwError s!"Cannot synthesize {declName}: not a definition"

/-- The instance predicate the real dispatch feeds the certified gate: the
    expression is a call whose head constant is tagged `@[hardware_module]`.
    Computed from the run's environment — the gate itself stays a pure
    function of the `ConstantInfo` and this predicate. -/
def instancePredicate (env : Environment) : Lean.Expr → Bool := fun e =>
  match e.getAppFn with
  | .const n _ =>
    Sparkle.Compiler.isHardwareModule env n ||
      (match env.getProjectionStructureName? n, e with
       | some _, .app _ record =>
         (match record.getAppFn with
          | .const rn _ => Sparkle.Compiler.isHardwareModule env rn
          | _ => false)
       | _, _ => false)
  | _ => false

/-- The synthesis entry, with the translator's recursive entry as a parameter
    (`synthesizeCombinationalCore` after the translator block passes the real
    one).  A plain definition: it is not recursive itself — nested synthesis
    reaches it again only through `translate`. -/
def synthesizeCombinationalCoreWith (translate : TranslateFn) (declName : Name)
    (parameters : List (String × Nat)) (symbolicMode : Bool)
    (certifiedFrontEnd : Bool := true) :
    MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
  if symbolicMode then
    let hasDuplicate := parameters.any fun (name, _) =>
      (parameters.filter fun (other, _) => other == name).length > 1
    if hasDuplicate then
      throwError "Retained hardware parameter names must be unique"
    for (name, defaultValue) in parameters do
      if defaultValue == 0 then
        throwError s!"Retained hardware parameter '{name}' must have a positive default"
  let profile := (← IO.getEnv "SPARKLE_PROFILE").isSome
  let logProf (msg : String) : IO Unit := do
    if profile then
      IO.eprintln msg
      (← IO.getStderr).flush
      let h ← IO.FS.Handle.mk "/tmp/sparkle-profile.log" .append
      h.putStrLn msg
      h.flush
  logProf s!"[profile] synthesizeCombinational {declName} entering"
  -- Depth-gated cache reset (Issue #67).
  --
  -- The per-synth caches must be wiped at the start of every
  -- *outermost* `#synthesizeVerilog` invocation so Expr identity
  -- from one decl doesn't alias into the next, BUT they must
  -- NOT be wiped on recursive re-entry — when a `circuit do`
  -- body projects multiple fields off a single
  -- `@[hardware_module]` call (e.g. `engine.replyValid`,
  -- `engine.replyKind`, ...), each projection triggers a fresh
  -- `synthesizeCombinational kvHw` nested call.  Resetting
  -- `sparkleSubModuleCache` / `sparkleSubInstanceOutputs` at
  -- that point forces every later projection of the same call
  -- to re-walk `kvHw` from scratch, which is the O(N²)
  -- behaviour memcached server top-level synth hits today
  -- (kvHw walked 8× per top-level synth, ~17 min total).
  --
  -- `sparkleSynthDepth` tracks recursion depth; we only clear
  -- when entering at depth 0 and bump+release the counter
  -- around the body via `try ... finally` so it stays
  -- balanced across throwError / panic exits.
  let depth ← sparkleSynthDepth.get
  -- Snapshot the fvar-value and sub-instance maps so nested
  -- `synthesizeCombinational` calls (e.g. memcachedServer
  -- inside memcachedServerTop) don't pollute their parent's
  -- view of `let stReg := …` fvar bindings.  Without this,
  -- the parent's `sparkleFvarValueMap` entries from a
  -- previously-translated sub-module get reused when the
  -- parent later translates its OWN register fvars that
  -- happen to share user names — collapsing distinct
  -- `stReg` / `valueReg` references onto the wrong wire.
  --
  -- The per-`(callKey, fieldName)` instance dedupe relies on
  -- `sparkleSubInstanceOutputs` persisting across nested
  -- synths (it's how the cross-module wire-reuse cache hit
  -- in commit ae779e5 fires), so we ONLY snapshot the
  -- fvar-value map.
  let savedFvarMap ← if depth == 0 then pure ({} : Std.HashMap Lean.Name Lean.Expr)
                     else sparkleFvarValueMap.get
  -- `sparkleWireWidthCache` is keyed by wire NAME (e.g.
  -- `_tmp_loop_0`).  Wire names are allocated per-`CircuitM`
  -- (i.e. per-module) so a parent module and a nested
  -- sub-module can both have a wire named `_tmp_loop_0`
  -- with DIFFERENT widths.  If we let the cache persist
  -- across nested synth boundaries, the second module's
  -- insert overwrites the first's — and any later
  -- `getWireWidth "_tmp_loop_0"` from the parent context
  -- gets the child's width.  This was the root cause of
  -- Issue #67-step-2's `_gen_stSig_N = slice (_tmp_loop_0)
  -- 242 239` bug in memcachedServer: the slice handler
  -- read `_tmp_loop_0`'s width as 243 (kvHw's loop wire)
  -- while it should have been 340 (memcachedServer's).
  let savedWireWidthCache ←
    if depth == 0 then pure ({} : Std.HashMap String Nat)
    else sparkleWireWidthCache.get
  if depth == 0 then
    sparkleTypeCache.set {}
    sparkleTypeCacheHits.set 0
    sparkleTypeCacheMiss.set 0
    sparkleSubModuleCache.set {}
    sparkleChildCache.set {}
    sparkleSubInstanceOutputs.set {}
    sparkleSingleOutInstanceCache.set {}
    sparkleFvarValueMap.set {}
    sparkleWireWidthCache.set {}
    sparkleLetWireCache.set {}
    sparkleLoopWireCache.set {}
    sparkleWireCanon.set {}
  else
    -- Nested synth: fresh fvar map (the parent's fvars are
    -- scoped to the parent's body and can't be visible
    -- inside the child's body either) and fresh wire-width
    -- cache (wire names are per-module).
    sparkleFvarValueMap.set {}
    sparkleWireWidthCache.set {}
    sparkleLetWireCache.set {}
    sparkleLoopWireCache.set {}
    sparkleWireCanon.set {}
  sparkleSynthDepth.set (depth + 1)
  -- Extract the body into a local closure so `try ... finally`
  -- can wrap the entire synthesis path (including the
  -- `throwError` arm) with one balanced decrement, regardless
  -- of which return path or exception fires.
  let doSynth : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
    let constInfo ← getConstInfo declName
    let env ← getEnv
    synthesizeFromConst translate logProf declName parameters symbolicMode
      certifiedFrontEnd
      (entryConst certifiedFrontEnd symbolicMode parameters constInfo
        (instancePredicate env) (userInliner env) (structEnv env))
      (instancePredicate env)
  try
    doSynth
  finally
    sparkleSynthDepth.modify (· - 1)
    -- Restore parent's per-module caches after a nested synth.
    if depth != 0 then
      sparkleFvarValueMap.set savedFvarMap
      sparkleWireWidthCache.set savedWireWidthCache

/-- `#synthesizeVerilog`'s synthesis: the entry, then zero-width cleanup, then
    the merge of the duplicate hardware the two-pass body evaluation leaves
    behind (see Sparkle/IR/RegDedup.lean; `SPARKLE_NO_REGDEDUP=1` skips the
    merge, for A/B diagnosis).  A plain definition, like the entry. -/
def synthesizeCombinationalWith (translate : TranslateFn) (declName : Name) :
    MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
  let (m, d) ← synthesizeCombinationalCoreWith translate declName [] false
  let m := Sparkle.IR.ZeroWidth.dropZeroWidthModule m
  let d := Sparkle.IR.ZeroWidth.dropZeroWidthDesign d
  if (← IO.getEnv "SPARKLE_NO_REGDEDUP").isSome then return (m, d)
  -- the merge is result-checked on assign + register modules
  -- (`Sparkle.IR.RefineCheck.mergeChecked`): kept only if `refineCheck`
  -- accepts it
  return (Sparkle.IR.RefineCheck.mergeChecked m,
    Sparkle.IR.RefineCheck.mergeCheckedDesign d)

/-! The translator block below takes its recursive entry as a PARAMETER
(`translateExprToWire`, a section variable), so it no longer ties its own knot.
The knot is `translateExprToWire` after the block: an ordinary definition,
`fuelFix translateStep translateFuelLimit`, whose every recursive call goes
through the fuel. `partial` handlers remain, but only as the fallback of that
step — which is what lets the recursion be discharged by induction
(Tools/ShippingTranslateSoundness.lean). -/
section TranslatorBlock
variable (translateExprToWire : (e : Lean.Expr) → (hint : String := "wire") →
  (isTopLevel : Bool := false) → (isNamed : Bool := false) → CompilerM String)
namespace Rec
mutual
  /-- Caching shim around `translateExprToWireImpl`.  All early-
      intercept handlers (Signal HAdd/HSub/etc., OfNat literals,
      ...) currently `return` straight from the inner impl, which
      means they never write back to the cache.  Wrapping here
      means **every** successful translate caches its result —
      so subsequent identical sub-trees become a HashMap lookup
      instead of a full re-walk through ~10 handlers + Meta. -/
  partial def translateExprToWireCached (e : Lean.Expr) (hint : String := "wire") (isTopLevel : Bool := false) (isNamed : Bool := false) : CompilerM String := do
    let cacheRef? := (← CompilerM.getCompilerState).exprCache
    -- Cache only when there's no fresh wire name to emit
    -- (`isNamed` would force a specific user-facing name) and
    -- when the expression isn't a free variable (those resolve
    -- against the lexically-scoped varMap, not by Expr identity).
    let cacheable := !isNamed && !e.isFVar && !isTopLevel
    if cacheable then
      if let some ref := cacheRef? then
        -- Lookup: don't bind `cache` to a let — that creates
        -- a second reference that survives until the end of
        -- the function, forcing `ref.modify` below to
        -- copy-on-write the entire HashMap (O(n) per insert,
        -- O(n²) overall on FSM-shape circuits).  Use the
        -- short-lived expression form so the read result is
        -- dropped immediately on cache miss.
        let lookupResult ← CompilerM.liftMetaM do
          let cache ← (ref.get : IO _)
          match cache.get? ⟨e⟩ with
          | some w => return some w
          | none =>
            let eStripped := e.consumeMData
            if !(eStripped == e) then
              return cache.get? ⟨eStripped⟩
            else
              return none
        match lookupResult with
        | some w =>
          CompilerM.liftMetaM (sparkleCacheHits.modify (· + 1))
          return w
        | none => pure ()
    let r ← translateExprToWireImpl e hint isTopLevel isNamed
    if cacheable then
      if let some ref := cacheRef? then
        CompilerM.liftMetaM (ref.modify (·.insert ⟨e⟩ r))
    return r

  partial def translateExprToWireImpl (e : Lean.Expr) (hint : String := "wire") (isTopLevel : Bool := false) (isNamed : Bool := false) : CompilerM String := do
    trace[sparkle.compiler] "translateExprToWire hint={hint} isTopLevel={isTopLevel}"
    let callN ← CompilerM.liftMetaM (sparkleCallCounter.modifyGet fun n => (n + 1, n + 1))
    -- Infinite-loop / runaway-walk backstop.  If the elaborator
    -- ever exceeds 500k recursive translate calls on a single
    -- top-level synth attempt, abort with a diagnostic rather
    -- than hanging silently.  Tunable via SPARKLE_TRANSLATE_LIMIT.
    let limit ← CompilerM.liftMetaM do
      let envS ← IO.getEnv "SPARKLE_TRANSLATE_LIMIT"
      -- Default raised from 500_000 to 32_000_000 after empirical
      -- observation that legitimate large IPs (memcached server
      -- top-level with kvHw sub-module + 8-register FSM + 37-entry
      -- response mux) need ~1-10M recursive translate calls.
      -- The lower cap was creating false "hang" diagnoses.
      return envS.bind String.toNat? |>.getD 32_000_000
    if callN > limit then
      CompilerM.liftMetaM $ throwError
        s!"Sparkle synth elaborator exceeded {limit} recursive translateExprToWire calls (likely runaway inline loop on hint={hint}).\n\nSet SPARKLE_TRANSLATE_LIMIT to raise the cap, or set `set_option trace.sparkle.compiler true` and grep for the deepest cycle to find the offending sub-expression."
    if callN % 10000 == 0 then
      CompilerM.liftMetaM do
        if (← IO.getEnv "SPARKLE_PROFILE").isSome then
          let hits ← sparkleCacheHits.get
          let calls ← sparkleHandlerCalls.get
          let msArr ← sparkleHandlerMs.get
          let typeHits ← sparkleTypeCacheHits.get
          let typeMiss ← sparkleTypeCacheMiss.get
          let wCalls ← sparkleWhnfCalls.get
          let wMs    ← sparkleWhnfMs.get
          let iCalls ← sparkleInferCalls.get
          let iMs    ← sparkleInferMs.get
          let uCalls ← sparkleUnfoldDefCalls.get
          let uMs    ← sparkleUnfoldDefMs.get
          let mut tickLines : Array String :=
            #[s!"[profile] tick {callN} (cache hits {hits}, typeCache hits={typeHits} miss={typeMiss})",
              s!"  Meta whnf:       {wCalls} calls / {wMs} ms",
              s!"  Meta inferType:  {iCalls} calls / {iMs} ms",
              s!"  Meta unfoldDef?: {uCalls} calls / {uMs} ms"]
          for h in [:sparkleProfHandlerNames.size] do
            let n := calls.getD h 0
            let m := msArr.getD h 0
            if n > 0 then
              tickLines := tickLines.push s!"  {sparkleProfHandlerNames.getD h "?"}: {n} calls / {m} ms"
          let body := String.intercalate "\n" tickLines.toList
          IO.eprintln body
          (← IO.getStderr).flush
          let fh ← IO.FS.Handle.mk "/tmp/sparkle-profile.log" .append
          fh.putStrLn body
          fh.flush
    -- Cache lookup is now handled by the `translateExprToWire`
    -- wrapper above; this impl runs only on misses.
    -- 0. Handle free variables first (before any whnf)
    if let .fvar fvarId := e then
      match ← CompilerM.lookupVar fvarId with
      | some wireName => return wireName
      | none =>
        -- Check if this is a non-HW fvar (typeclass instance, config, etc.)
        -- with a value in the local context that we can inline (zeta-reduce)
        let inlinedVal ← CompilerM.liftMetaM do
          let lctx ← getLCtx
          match lctx.find? fvarId with
          | some decl => return decl.value?
          | none => return none
        match inlinedVal with
        | some val =>
          -- Cycle break: if we're already zeta-reducing this same
          -- fvar deeper in the stack, the value we'd unfold is
          -- the very expression we're inside (= circular let
          -- binding loop produced by Signal.loop's memoize
          -- chain).  Throw rather than recurse.
          let visited ← CompilerM.liftMetaM (sparkleFvarZetaVisited.get : IO _)
          if visited.contains fvarId.name then
            CompilerM.liftMetaM $ throwError
              s!"Sparkle synth: circular zeta-reduction on fvar {fvarId.name} (hint={hint}). \
                 This usually means a `Signal.loop` register is being walked twice via \
                 its memoize chain. Common cause: an FSM where a register read feeds a \
                 register write through `Signal.memoize` and a sub-`circuit do` (e.g. \
                 nested kvHw inside memcachedServer)."
          CompilerM.liftMetaM (sparkleFvarZetaVisited.modify (·.insert fvarId.name))
          let r ← translateExprToWire val hint isTopLevel isNamed
          CompilerM.liftMetaM (sparkleFvarZetaVisited.modify (·.erase fvarId.name))
          return r
        | none =>
          -- Try full reduction for type-level fvars (Nat widths, erased params).
          -- Same cycle-break as above: track which fvars we're currently
          -- reducing to avoid infinite zeta loops.
          let visited ← CompilerM.liftMetaM (sparkleFvarZetaVisited.get : IO _)
          if visited.contains fvarId.name then
            CompilerM.liftMetaM $ throwError
              s!"Sparkle synth: circular reduction on fvar {fvarId.name} (hint={hint})."
          CompilerM.liftMetaM (sparkleFvarZetaVisited.modify (·.insert fvarId.name))
          let reduced ← CompilerM.liftMetaM (try Lean.Meta.reduce e catch _ => pure e)
          CompilerM.liftMetaM (sparkleFvarZetaVisited.modify (·.erase fvarId.name))
          if reduced != e then
            return ← translateExprToWire reduced hint isTopLevel isNamed
          let ty ← CompilerM.liftMetaM (try Lean.Meta.inferType e catch _ => pure (.const `unknown []))
          let tyPP ← CompilerM.liftMetaM (try ppExpr ty catch _ => pure s!"{ty}")
          let userName ← CompilerM.liftMetaM do
            let lctx ← getLCtx
            match lctx.find? fvarId with
            | some decl => return s!"{decl.userName}"
            | none => return "not_in_lctx"
          let st ← CompilerM.getCompilerState
          let known := st.varMap.map (fun (k,_) => k.name)
          CompilerM.liftMetaM $ throwError s!"Unbound variable: {fvarId.name} (userName={userName})\n  type: {tyPP}\n  hint: {hint}\n  known: {known}"

    let fn := e.getAppFn
    let args := e.getAppArgs


    -- 0. Early interception for Signal operators (before WHNF)
    -- When HAdd/HSub/HMul/HAnd/HOr/HXor/HShiftLeft/HShiftRight/HAppend instances
    -- are applied to Signals (or mixed Signal/BitVec), intercept before WHNF
    -- to avoid OfNat.ofNat expansion failures and domain metavariable stalls.
    if let .const instName _ := fn then
      -- General binary operator interception (canonical instances only)
      if let some op := signalBinOpOf instName then
        if let some (isSignal1, isSignal2) := canonicalSignalBinKinds instName args then
          if isSignal1 || isSignal2 then
            return ← translateCanonicalSignalBinary
              (fun e' h t n => translateExprToWire e' h t n) e op args isSignal1 isSignal2 hint isNamed

      -- HAppend (concat) — separate because it uses .concat not .op
      if let some (isSignal1, isSignal2) :=
          (if instName == ``HAppend.hAppend then canonicalSignalBinKinds instName args else none) then
        let arg1 := args[args.size - 2]!
        let arg2 := args[args.size - 1]!
        -- Both Signal case: translate directly to concat
        if isSignal1 && isSignal2 then
          let exprType ← cachedInferType e
          let hwType ← inferHWTypeFromSignal exprType
          let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
          let wireA ← translateExprToWire arg1 "concat_hi" (isTopLevel := false)
          let wireB ← translateExprToWire arg2 "concat_lo" (isTopLevel := false)
          CompilerM.emitAssign resWire (.concat [.ref wireA, .ref wireB])
          return resWire
        -- Mixed case: one is Signal, one is BitVec constant
        if isSignal1 != isSignal2 then
          let exprType ← cachedInferType e
          let hwType ← inferHWTypeFromSignal exprType
          let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
          if isSignal1 then
            -- Signal ++ BitVec: arg1 is signal, arg2 is constant
            let wireA ← translateExprToWire arg1 "concat_hi" (isTopLevel := false)
            let (cVal, cWidth) ← extractBitVecLiteral arg2
            let constWire ← CompilerM.makeWire "concat_const" (.bitVector cWidth)
            CompilerM.emitAssign constWire (.const (Int.ofNat cVal) cWidth)
            CompilerM.emitAssign resWire (.concat [.ref wireA, .ref constWire])
          else
            -- BitVec ++ Signal: arg1 is constant, arg2 is signal
            let (cVal, cWidth) ← extractBitVecLiteral arg1
            let constWire ← CompilerM.makeWire "concat_const" (.bitVector cWidth)
            CompilerM.emitAssign constWire (.const (Int.ofNat cVal) cWidth)
            let wireB ← translateExprToWire arg2 "concat_lo" (isTopLevel := false)
            CompilerM.emitAssign resWire (.concat [.ref constWire, .ref wireB])
          return resWire

    -- 1. High-priority Signal Recognition (Avoid premature unfolding)
    if let .const name _ := fn then
        -- OfNat.ofNat: numeric literal (e.g., 0#4, 0xFFFFF#20, 35)
        -- Must be checked BEFORE `.endsWith ".ofNat"` which would take args.back! (the instance)
        if name == ``OfNat.ofNat && args.size >= 3 then
          let type ← CompilerM.liftMetaM (whnf args[0]!)
          if let .app (.const ``BitVec _) widthExpr := type then
            let w ← extractNat widthExpr
            let v ← extractNat args[1]!
            let resWire ← CompilerM.makeWire hint (if w == 1 then .bit else .bitVector w) (named := isNamed)
            CompilerM.emitAssign resWire (.const v w)
            return resWire

        -- Bool constants
        if name == ``Bool.true then
          let resWire ← CompilerM.makeWire hint .bit (named := isNamed)
          CompilerM.emitAssign resWire (.const 1 1)
          return resWire
        if name == ``Bool.false then
          let resWire ← CompilerM.makeWire hint .bit (named := isNamed)
          CompilerM.emitAssign resWire (.const 0 1)
          return resWire

        -- OfNat.mk: unwrap the constructor to its value
        if name == ``OfNat.mk && args.size >= 1 then
          return ← translateExprToWire args.back! hint (isNamed := isNamed)

        -- Signal wrappers & identity casts
        -- Note: exclude OfNat.ofNat from .endsWith ".ofNat" (already handled above)
        if name == ``Sparkle.Core.Signal.Signal.mk || name == ``Sparkle.Core.Signal.Signal.val ||
           name == ``BitVec.ofFin || name == ``Fin.mk || name == ``BitVec.ofNat || name == ``BitVec.toNat ||
           name.toString.endsWith ".ofFin" ||
           (name.toString.endsWith ".ofNat" && name != ``OfNat.ofNat) ||
           name.toString.endsWith ".toNat" then
          if args.size >= 1 then
            let payload := if name == ``Fin.mk && args.size >= 2 then args[args.size-2]! else args.back!
            return ← translateExprToWire payload hint (isNamed := isNamed)

        -- Signal.pure / Signal.lit (constant signals)
        if (name == ``Sparkle.Core.Signal.Signal.pure || name == ``Sparkle.Core.Signal.Signal.lit) && args.size >= 1 then
           if name == ``Sparkle.Core.Signal.Signal.pure then
             if let some w ← translateSignalPureLiteral? args hint isNamed then
               return w
           let constValue := args[args.size-1]!
           -- Check for Bool constants first
           let constReduced ← CompilerM.liftMetaM (whnf constValue)
           if let .const boolName _ := constReduced then
             if boolName == ``Bool.true then
               let resWire ← CompilerM.makeWire hint .bit (named := isNamed)
               CompilerM.emitAssign resWire (.const 1 1)
               return resWire
             if boolName == ``Bool.false then
               let resWire ← CompilerM.makeWire hint .bit (named := isNamed)
               CompilerM.emitAssign resWire (.const 0 1)
               return resWire
             -- `Signal.pure ()` — the `Unit`/`PUnit` terminator
             -- of an `HList` Prod chain.  Zero-width constant
             -- (no actual wire emitted).  Used by
             -- `packRegister []` to close out the chain.
             if boolName == ``Unit.unit || boolName == ``PUnit.unit then
               let resWire ← CompilerM.makeWire hint (.bitVector 0) (named := isNamed)
               CompilerM.emitAssign resWire (.const 0 0)
               return resWire
           -- Check if argument is an fvar with wire mapping (let-bound constant)
           if let .fvar fvarId := constValue then
             match ← CompilerM.lookupVar fvarId with
             | some wireName => return wireName
             | none => pure ()
           -- Try to extract the BitVec literal value
           let (value, width) ← try
             extractBitVecLiteral constValue
           catch _ =>
             -- If not a BitVec literal, try to reduce and check again
             let reduced ← CompilerM.liftMetaM (reduce constValue)
             try
               extractBitVecLiteral reduced
             catch _ =>
               -- Last resort: try translateExprToWire (handles OfNat.ofNat, etc.)
               return ← translateExprToWire constValue hint (isNamed := isNamed)
           let resWire ← CompilerM.makeWire hint (.bitVector width) (named := isNamed)
           CompilerM.emitAssign resWire (.const value width)
           return resWire

        -- bundle2
        if name == ``Sparkle.Core.Signal.bundle2 && args.size >= 2 then
           let wireA ← translateExprToWire args[args.size-2]! "a"
           let wireB ← translateExprToWire args[args.size-1]! "b"
           let exprType ← cachedInferType e
           let hwType ← inferHWTypeFromSignal exprType
           let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
           CompilerM.emitAssign resWire (.concat [.ref wireA, .ref wireB])
           return resWire

        -- map Prod.fst/snd
        if name == ``Sparkle.Core.Signal.Signal.map && args.size >= 2 then
           let f := args[args.size-2]!
           let s := args[args.size-1]!
           let fFn := f.getAppFn
           if fFn.isConstOf ``Prod.fst then
               let wireS ← translateExprToWire s "s" (isTopLevel := false)
               let wireWidth ← CompilerM.getWireWidth wireS
               let exprType ← cachedInferType e
               let hwType ← inferHWTypeFromSignal exprType
               let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
               let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
               let sType ← cachedInferType s
               let sHWType ← inferHWTypeFromSignal sType
               let typeTotal := match sHWType with | .bitVector w => w | .bit => 1 | _ => 8
               -- Issue #67 step 2: clamp slice to wire's
               -- declared width (see the matching comment in
               -- `handleTupleProjections`).
               let totalWidth := min wireWidth typeTotal
               let lo : Nat := if totalWidth ≥ width then totalWidth - width else 0
               let hi : Nat := if totalWidth ≥ 1 then totalWidth - 1 else 0
               CompilerM.emitAssign resWire (.slice (.ref wireS) hi lo)
               return resWire
           if fFn.isConstOf ``Prod.snd then
               let wireS ← translateExprToWire s "s" (isTopLevel := false)
               let wireWidth ← CompilerM.getWireWidth wireS
               let exprType ← cachedInferType e
               let hwType ← inferHWTypeFromSignal exprType
               let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
               let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
               let actualWidth := min width wireWidth
               let hi : Nat := if actualWidth ≥ 1 then actualWidth - 1 else 0
               CompilerM.emitAssign resWire (.slice (.ref wireS) hi 0)
               return resWire

           -- Handle lambda functions in Signal.map (extractLsb', unary primitives)
           if let .lam _ _ body _ := f then
             let bodyFn := body.getAppFn
             if let .const opName _ := bodyFn then
               -- BitVec.extractLsb' → slice
               if opName == ``BitVec.extractLsb' then
                 let bodyArgs := body.getAppArgs
                 if bodyArgs.size >= 4 then
                   let start ← extractDimExpr bodyArgs[bodyArgs.size - 3]!
                   let len ← extractDimExpr bodyArgs[bodyArgs.size - 2]!
                   let wireS ← translateExprToWire s "s" (isTopLevel := false)
                   let resWire ← CompilerM.makeWire hint (hwTypeFromDim len) (named := isNamed)
                   CompilerM.emitAssign resWire
                     (makeSliceFromStartLength (.ref wireS) start len)
                   return resWire
               -- Unsigned extension/truncation with a retained target width.
               if (opName == ``BitVec.zeroExtend || opName == ``BitVec.setWidth) then
                 let bodyArgs := body.getAppArgs
                 if bodyArgs.size >= 2 then
                   let targetWidth ← extractDimExpr bodyArgs[bodyArgs.size - 2]!
                   let wireS ← translateExprToWire s "s" (isTopLevel := false)
                   return ← lowerZeroExtendWire hint wireS targetWidth (isNamed := isNamed)

               -- BitVec.signExtend → sign extension via concat of replicated MSB
               if opName == ``BitVec.signExtend then
                 let bodyArgs := body.getAppArgs
                 -- signExtend w val : args are [w, val] (w is target width)
                 if bodyArgs.size >= 2 then
                   let targetWidth ← extractNat bodyArgs[bodyArgs.size - 2]!
                   let wireS ← translateExprToWire s "s" (isTopLevel := false)
                   let srcWidth ← CompilerM.getWireWidth wireS
                   let extBits := targetWidth - srcWidth
                   let resWire ← CompilerM.makeWire hint (.bitVector targetWidth) (named := isNamed)
                   if extBits == 0 then
                     CompilerM.emitAssign resWire (.ref wireS)
                   else
                     -- MSB = signal[srcWidth-1 : srcWidth-1]
                     let msbWire ← CompilerM.makeWire "sext_msb" (.bitVector 1)
                     CompilerM.emitAssign msbWire (.slice (.ref wireS) (srcWidth - 1) (srcWidth - 1))
                     -- Replicate MSB extBits times via concat
                     let msbRefs := List.replicate extBits (.ref msbWire)
                     let extWire ← CompilerM.makeWire "sext_ext" (.bitVector extBits)
                     CompilerM.emitAssign extWire (.concat msbRefs)
                     -- Concat: {ext, original}
                     CompilerM.emitAssign resWire (.concat [.ref extWire, .ref wireS])
                   return resWire
               -- BitVec.sshiftRight → arithmetic shift right by constant
               if opName == ``BitVec.sshiftRight then
                 let bodyArgs := body.getAppArgs
                 if bodyArgs.size >= 2 then
                   let shiftAmt ← extractNat bodyArgs[bodyArgs.size - 1]!
                   let wireS ← translateExprToWire s "s" (isTopLevel := false)
                   let srcWidth ← CompilerM.getWireWidth wireS
                   let resWire ← CompilerM.makeWire hint (.bitVector srcWidth) (named := isNamed)
                   let shiftWire ← CompilerM.makeWire "ashr_amt" (.bitVector srcWidth)
                   CompilerM.emitAssign shiftWire (.const shiftAmt srcWidth)
                   CompilerM.emitAssign resWire (.op .asr [.ref wireS, .ref shiftWire])
                   return resWire
               -- Unary primitives (neg, not, etc.).  ONLY take
               -- this shortcut when the body is genuinely
               -- `op p` — single primitive applied to the
               -- lambda parameter.  Composite-body lambdas
               -- (e.g. `fun p => 0x4000 ||| ((0#8) ++ p)`,
               -- where the head is `HOr.hOr` but the body
               -- mixes a constant and a nested op) fall
               -- through to the composite-body path below
               -- (Issue #73).
               if let some op := getOperator opName then
                 let isUnary := op == .not || op == .neg
                 if isUnary then
                   let wireS ← translateExprToWire s "s" (isTopLevel := false)
                   let exprType ← cachedInferType e
                   let hwType ← inferHWTypeFromSignal exprType
                   let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
                   CompilerM.emitAssign resWire (.op op [.ref wireS])
                   return resWire

           -- Composite-body lambda fallback (Issue #73).
           -- Pattern-match on common composite shapes built
           -- from primitives + the lambda parameter + literals.
           -- This handles `proto.map (fun p => 0x4000 ||| ((0#8) ++ p))`
           -- and similar shallow trees.
           --
           -- General strategy: walk `body` recursively, emitting
           -- IR ops as we go.  Literals become `.const`, `p`
           -- becomes `.ref wireS`, primitive op apps become
           -- `.op` / `.concat`.
           if let .lam binderName binderType lamBody _ := f then
             let wireS ← translateExprToWire s "s" (isTopLevel := false)
             let srcWidth ← CompilerM.getWireWidth wireS
             let exprType ← cachedInferType e
             let hwType ← inferHWTypeFromSignal exprType
             let dstWidth := match hwType with
               | .bitVector w => w | .bit => 1 | _ => 8
             -- Bind `p` to wireS in varMap so a recursive
             -- walker can resolve it.  We then run a small
             -- bespoke body translator (not the main
             -- handler chain, which expects Signal-typed
             -- intermediates) that returns an IR `Expr`.
             let res? ← CompilerM.withLocalDecl binderName binderType fun fvar => do
               let fvarId := fvar.fvarId!
               CompilerM.withVarMapping fvarId wireS do
                 let body' := lamBody.instantiate1 fvar
                 -- Inline mini-translator: turn `body'` into an
                 -- IR `Expr`.  Recognises: fvar (= wireS),
                 -- BitVec literals, HOr/HAnd/HXor/HAdd/HSub,
                 -- HAppend.hAppend, and `BitVec.extractLsb'`.
                 let rec toIR (e : Lean.Expr) : CompilerM (Option Sparkle.IR.AST.Expr) := do
                   if e.isFVar then
                     if e.fvarId! == fvarId then
                       return some (.ref wireS)
                     else
                       return none
                   let fn := e.getAppFn
                   let args := e.getAppArgs
                   if let .const opNm _ := fn then
                     -- BitVec literal (`OfNat.ofNat n k` or
                     -- `BitVec.ofNat w n`).
                     if opNm == ``OfNat.ofNat ∨ opNm == ``BitVec.ofNat then
                       let valOpt ← try
                           let (v, w) ← extractBitVecLiteral e
                           pure (some (Sparkle.IR.AST.Expr.const (Int.ofNat v) w))
                         catch _ => pure none
                       return valOpt
                     -- HAppend / BitVec.append → concat
                     if (opNm == ``HAppend.hAppend ∨ opNm == ``BitVec.append) ∧ args.size ≥ 2 then
                       let a := args[args.size - 2]!
                       let b := args[args.size - 1]!
                       match (← toIR a), (← toIR b) with
                       | some ea, some eb => return some (.concat [ea, eb])
                       | _, _ => return none
                     -- Binary primitive op (HOr / HAnd / ...).
                     if let some op := getOperator opNm then
                       if args.size ≥ 2 then
                         let a := args[args.size - 2]!
                         let b := args[args.size - 1]!
                         match (← toIR a), (← toIR b) with
                         | some ea, some eb => return some (.op op [ea, eb])
                         | _, _ => return none
                   return none
                 toIR body'
             match res? with
             | some irExpr =>
               let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
               CompilerM.emitAssign resWire irExpr
               let _ := dstWidth; let _ := srcWidth
               return resWire
             | none => pure ()

        -- Detect if-then-else and match expressions that cannot be synthesized
        if name == ``ite || name == ``dite then
          let exprStr ← CompilerM.liftMetaM (ppExpr e)
          CompilerM.liftMetaM $ throwError
            "if-then-else expressions cannot be synthesized to hardware.\n\n\
            Expression: {exprStr}\n\n\
            Use Signal.mux instead:\n\
            ❌ WRONG: if cond then a else b\n\
            ✓ RIGHT:  Signal.mux cond a b\n\n\
            See Tests/TestConditionals.lean for examples."

        if name == ``Decidable.rec || name == ``Decidable.casesOn then
          CompilerM.liftMetaM $ throwError
            "Decidable.rec (from if-then-else) cannot be synthesized.\n\n\
            Use Signal.mux for hardware multiplexers:\n\
            ✓ Signal.mux (cond : Signal d Bool) (ifTrue ifFalse : Signal d α) : Signal d α\n\n\
            See Tests/TestConditionals.lean for examples."

        -- Note: unbundle pattern matching detection removed (see comment in translateExprToWireApp)

        -- Handle recursors by forcing reduction (use reduce for full beta reduction)
        if name == ``Prod.rec || name == ``Prod.casesOn then
          let e' ← CompilerM.liftMetaM (withTransparency TransparencyMode.all $ reduce e)

          -- Check if the result is: fvar proj1 proj2 (tuple destructuring continuation pattern)
          let handled ← match e' with
          | .app (.app cont arg1) arg2 =>
            if arg1.isProj && arg2.isProj then do
              -- Pattern: continuation applied to two projections
              -- Extract the base of the projections and the continuation
              let baseExpr := match arg1 with
                | .proj _ _ base => base
                | _ => arg1

              -- Translate the base expression to get the tuple wire
              let tupleWire ← translateExprToWire baseExpr "tuple" (isTopLevel := false)

              -- Infer component types from the continuation lambda types
              let (ty1, ty2) ← match cont with
                | .lam _ t1 (.lam _ t2 _ _) _ => pure (t1, t2)
                | .lam _ t1 _ _ =>
                  -- Single lambda, need to infer second type from first lambda body
                  pure (t1, t1) -- Fallback: assume same types
                | _ => CompilerM.liftMetaM $ throwError "Expected lambda in Prod.rec continuation"

              let hwType1 ← inferHWTypeFromSignal ty1
              let hwType2 ← inferHWTypeFromSignal ty2
              let width1 := match hwType1 with | .bitVector w => w | .bit => 1 | _ => 8
              let width2 := match hwType2 with | .bitVector w => w | .bit => 1 | _ => 8

              -- Extract the two components
              let wire1 ← CompilerM.makeWire (hint ++ "_fst") hwType1
              let wire2 ← CompilerM.makeWire (hint ++ "_snd") hwType2
              CompilerM.emitAssign wire1 (.slice (.ref tupleWire) (width1 + width2 - 1) width2)
              CompilerM.emitAssign wire2 (.slice (.ref tupleWire) (width2 - 1) 0)

              -- Now we need to apply the continuation with these wires
              -- The continuation should be a lambda (or nested lambdas)
              let result ← match cont with
              | .lam n1 ty1 body1 _ =>
                -- Single lambda - check if body is another lambda
                match body1 with
                | .lam n2 ty2 body2 _ =>
                  -- Nested lambdas: substitute both parameters
                  CompilerM.withLocalDecl n1 ty1 fun fvar1 => do
                    CompilerM.withVarMapping fvar1.fvarId! wire1 do
                      let body1Inst := body2.instantiate1 fvar1
                      CompilerM.withLocalDecl n2 ty2 fun fvar2 => do
                        CompilerM.withVarMapping fvar2.fvarId! wire2 do
                          let body2Inst := body1Inst.instantiate1 fvar2
                          translateExprToWire body2Inst hint isTopLevel isNamed
                | _ =>
                  -- Single lambda body - substitute just the first parameter
                  CompilerM.withLocalDecl n1 ty1 fun fvar1 => do
                    CompilerM.withVarMapping fvar1.fvarId! wire1 do
                      let bodyInst := body1.instantiate1 fvar1
                      translateExprToWire bodyInst hint isTopLevel isNamed
              | .fvar contId =>
                -- The continuation is an fvar - check if it has a value in the local context
                let contValue? ← CompilerM.liftMetaM do
                  let lctx ← getLCtx
                  match lctx.find? contId with
                  | some decl => return decl.value?
                  | none => return none

                match contValue? with
                | some contExpr =>
                  -- The fvar has a value - it should be a lambda
                  match contExpr with
                  | .lam n1 ty1 (.lam n2 ty2 body _) _ =>
                    CompilerM.withLocalDecl n1 ty1 fun fvar1 => do
                      CompilerM.withVarMapping fvar1.fvarId! wire1 do
                        let body1 := body.instantiate1 fvar1
                        CompilerM.withLocalDecl n2 ty2 fun fvar2 => do
                          CompilerM.withVarMapping fvar2.fvarId! wire2 do
                            let body2 := body1.instantiate1 fvar2
                            translateExprToWire body2 hint isTopLevel isNamed
                  | _ =>
                    CompilerM.liftMetaM $ throwError s!"Expected nested lambda in continuation, got: {contExpr}"
                | none =>
                  CompilerM.liftMetaM $ throwError s!"Continuation fvar {contId.name} has no value in context"
              | _ =>
                CompilerM.liftMetaM $ throwError s!"Unexpected continuation type: {cont}"
              pure (some result)
            else if e' != e then do
              let result ← translateExprToWire e' hint (isTopLevel := false) (isNamed := isNamed)
              pure (some result)
            else
              pure none
          | _ =>
            if e' != e then do
              let result ← translateExprToWire e' hint (isTopLevel := false) (isNamed := isNamed)
              pure (some result)
            else
              pure none

          -- If we successfully handled it, return the result
          match handled with
          | some wire => return wire
          | none => pure ()

        -- Signal applicative syntax must lower the actual function body.
        -- The outer-name shortcut below loses custom BEq instances (and
        -- operand rearrangements); reuse the Signal.ap normalization/handler.
        if name == ``Seq.seq && args.size >= 1 && args[0]!.isAppOf ``Sparkle.Core.Signal.Signal then
          return ← translateExprToWireApp e hint isNamed

        -- Handle Seq.seq and Functor.map which might appear if Signal.ap reduces
        if name == ``Seq.seq && args.size >= 2 then
            let sf := args[args.size-2]!
            let b := args[args.size-1]!
            let sfFn := sf.getAppFn
            if sfFn.isConstOf ``Functor.map && sf.getAppArgs.size >= 2 then
                let fmapArgs := sf.getAppArgs
                let f := fmapArgs[fmapArgs.size-2]!
                let a := fmapArgs[fmapArgs.size-1]!
                let wireA ← translateExprToWire a "a" (isTopLevel := false)
                let wireB ← translateExprToWire b "b" (isTopLevel := false)
                -- COMPOUND-body special case: `fun x y => !(x OP y)`.
                -- `getPrimitiveNameFromLambda` returns just the outer
                -- `not`, losing the inner `OP`, so the fast path below
                -- would emit `.op .not [a,b]` — a unary op with two
                -- args, rendered by the backends as
                -- `/* ERROR: not requires 1 argument */`.  This is the
                -- bit-serial engines' `busy = !(isIdle || isFinish)`.
                -- Emit the correct nested `not (a OP b)` instead.
                if let some innerOp := (
                    match f with
                    | .lam _ _ (.lam _ _ notBody _) _ =>
                      let nfn := notBody.getAppFn
                      let nargs := notBody.getAppArgs
                      if (nfn.isConstOf ``not || nfn.isConstOf ``Bool.not
                          || nfn.isConstOf ``Complement.complement
                          || nfn.isConstOf ``BitVec.not) && nargs.size >= 1 then
                        let inner := nargs[nargs.size-1]!
                        match inner.getAppFn with
                        | .const iname _ =>
                          let iargs := inner.getAppArgs
                          if iargs.size >= 2 && iargs[iargs.size-2]!.isBVar
                             && iargs[iargs.size-1]!.isBVar then getOperator iname
                          else none
                        | _ => none
                      else none
                    | _ => none) then
                  let exprType ← cachedInferType e
                  let hwType ← inferHWTypeFromSignal exprType
                  let innerWire ← CompilerM.makeWire s!"{hint}_inner" hwType (named := false)
                  CompilerM.emitAssign innerWire (.op innerOp [.ref wireA, .ref wireB])
                  let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
                  CompilerM.emitAssign resWire (.op .not [.ref innerWire])
                  return resWire
                -- Get op name from lambda body
                let opName ← getPrimitiveNameFromLambda f
                match getOperator opName with
                | some op =>
                   -- Infer result type from the expression type
                   let exprType ← cachedInferType e
                   let hwType ← inferHWTypeFromSignal exprType
                   let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
                   CompilerM.emitAssign resWire (.op op [.ref wireA, .ref wireB])
                   return resWire
                | none =>
                   -- Special: BitVec.append / HAppend → concat
                   if opName == ``HAppend.hAppend || opName == ``BitVec.append then
                     let exprType ← cachedInferType e
                     let hwType ← inferHWTypeFromSignal exprType
                     let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
                     CompilerM.emitAssign resWire (.concat [.ref wireA, .ref wireB])
                     return resWire
                   -- Special: BitVec.sshiftRight → asr
                   if opName == ``BitVec.sshiftRight then
                     let exprType ← cachedInferType e
                     let hwType ← inferHWTypeFromSignal exprType
                     let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
                     CompilerM.emitAssign resWire (.op .asr [.ref wireA, .ref wireB])
                     return resWire
                   pure ()

        if name == ``Functor.map && args.size >= 2 then
             let f := args[args.size-2]!
             let a := args[args.size-1]!

             -- Try to extract lambda body for partial application detection
             match f with
             | .lam _ _ body _ =>
               let bodyApp := body
               let bodyFn := bodyApp.getAppFn

               -- Check if it's a primitive operation
               if let .const opName _ := bodyFn then
                 -- Special: BitVec.extractLsb' → slice (unary on signal, start/len are constants)
                 if opName == ``BitVec.extractLsb' then
                   let bodyArgs := bodyApp.getAppArgs
                   if bodyArgs.size >= 4 then
                     let start ← extractDimExpr bodyArgs[bodyArgs.size - 3]!
                     let len ← extractDimExpr bodyArgs[bodyArgs.size - 2]!
                     let wireA ← translateExprToWire a "a" (isTopLevel := false)
                     let resWire ← CompilerM.makeWire hint (hwTypeFromDim len) (named := isNamed)
                     CompilerM.emitAssign resWire
                       (makeSliceFromStartLength (.ref wireA) start len)
                     return resWire

                 -- Simple unary map: NOT, NEG (may have extra typeclass/type args)
                 -- Unsigned extension/truncation with a retained target width.
                 if (opName == ``BitVec.zeroExtend || opName == ``BitVec.setWidth) then
                   let bodyArgs := bodyApp.getAppArgs
                   if bodyArgs.size >= 2 then
                     let targetWidth ← extractDimExpr bodyArgs[bodyArgs.size - 2]!
                     let wireA ← translateExprToWire a "a" (isTopLevel := false)
                     return ← lowerZeroExtendWire hint wireA targetWidth (isNamed := isNamed)

                 if let some op := getOperator opName then
                   if op == .not || op == .neg then
                     let wireA ← translateExprToWire a "a" (isTopLevel := false)
                     let exprType ← cachedInferType e
                     let hwType ← inferHWTypeFromSignal exprType
                     let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
                     CompilerM.emitAssign resWire (.op op [.ref wireA])
                     return resWire

                 -- Binary operation in lambda with one constant and one bvar:
                 -- e.g., (fun d => (0#24 ++ d)) <$> sig  or  (fun x => x + 1#8) <$> sig
                 let bodyArgs := bodyApp.getAppArgs
                 if bodyArgs.size >= 2 then
                   let arg1 := bodyArgs[bodyArgs.size - 2]!
                   let arg2 := bodyArgs[bodyArgs.size - 1]!
                   let arg1HasBVar := arg1.hasLooseBVars
                   let arg2HasBVar := arg2.hasLooseBVars
                   -- Exactly one argument should reference the lambda parameter
                   if arg1HasBVar != arg2HasBVar then
                     let wireA ← translateExprToWire a "a" (isTopLevel := false)
                     -- Check for concat (HAppend.hAppend / BitVec.append)
                     if opName == ``HAppend.hAppend || opName == ``BitVec.append then
                       let exprType ← cachedInferType e
                       let hwType ← inferHWTypeFromSignal exprType
                       if arg1HasBVar then
                         -- (fun d => d ++ const) — signal is high bits
                         let (cVal, cWidth) ← extractBitVecLiteral arg2
                         let constWire ← CompilerM.makeWire "lambda_const" (.bitVector cWidth)
                         CompilerM.emitAssign constWire (.const (Int.ofNat cVal) cWidth)
                         let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
                         CompilerM.emitAssign resWire (.concat [.ref wireA, .ref constWire])
                         return resWire
                       else
                         -- (fun d => const ++ d) — signal is low bits
                         let (cVal, cWidth) ← extractBitVecLiteral arg1
                         let constWire ← CompilerM.makeWire "lambda_const" (.bitVector cWidth)
                         CompilerM.emitAssign constWire (.const (Int.ofNat cVal) cWidth)
                         let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
                         CompilerM.emitAssign resWire (.concat [.ref constWire, .ref wireA])
                         return resWire
                     -- Other binary primitives (add, sub, and, or, xor, etc.)
                     if let some op := getOperator opName then
                       let exprType ← cachedInferType e
                       let hwType ← inferHWTypeFromSignal exprType
                       if arg1HasBVar then
                         -- (fun x => x + const)
                         let (cVal, cWidth) ← extractBitVecLiteral arg2
                         let constWire ← CompilerM.makeWire "lambda_const" (.bitVector cWidth)
                         CompilerM.emitAssign constWire (.const (Int.ofNat cVal) cWidth)
                         let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
                         CompilerM.emitAssign resWire (.op op [.ref wireA, .ref constWire])
                         return resWire
                       else
                         -- (fun x => const + x)
                         let (cVal, cWidth) ← extractBitVecLiteral arg1
                         let constWire ← CompilerM.makeWire "lambda_const" (.bitVector cWidth)
                         CompilerM.emitAssign constWire (.const (Int.ofNat cVal) cWidth)
                         let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
                         CompilerM.emitAssign resWire (.op op [.ref constWire, .ref wireA])
                         return resWire

                 -- Remaining unary primitives (non-NOT/NEG) handled here
                 if let some op := getOperator opName then
                   let bodyArgs := bodyApp.getAppArgs
                   -- Only if the body has exactly 1 loose-bvar arg (the lambda param)
                   let numBVarArgs := bodyArgs.toList.filter (·.hasLooseBVars) |>.length
                   if numBVarArgs ≤ 1 then
                     let wireA ← translateExprToWire a "a" (isTopLevel := false)
                     let exprType ← cachedInferType e
                     let hwType ← inferHWTypeFromSignal exprType
                     let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
                     CompilerM.emitAssign resWire (.op op [.ref wireA])
                     return resWire
             | _ => pure ()


    -- Check if expression contains any of our mapped fvars (skip whnf if so)
    let varMap ← CompilerM.getCompilerState
    let hasMappedFvar := e.find? (fun sub =>
      match sub with
      | .fvar fid => varMap.varMap.any (fun (vid, _) => vid == fid)
      | _ => false
    ) |>.isSome

    -- 2. Fallback to normal reduction (only if no mapped fvars)
    --    Exception: lambda applications (beta-redexes) are always reduced with
    --    reducible transparency, which beta-reduces without unfolding Signal
    --    primitives (mux, register, memory). This handles local function inlining
    --    (e.g., `let f := fun x => ... Signal.mux ...; f arg`).
    let isBetaRedex := e.isApp && e.getAppFn.isLambda
    let e ← if !hasMappedFvar || isBetaRedex then
              CompilerM.liftMetaM (withTransparency TransparencyMode.reducible $ whnf e)
            else pure e
    let fn := e.getAppFn


    match e with
    | .app .. =>
      if let .const _ _ := fn then
         translateExprToWireApp e hint isNamed
      else
         -- Manual Zeta Reduction: Check if head is a local definition (let-bound)
         let zetaE ← if let .fvar fvarId := fn then
             CompilerM.liftMetaM do
                let lctx ← getLCtx
                match lctx.find? fvarId with
                | some decl =>
                   match decl.value? with
                   | some val =>
                      return some (e.replaceFVarId fvarId val)
                   | none =>
                      return none
                | none => return none
           else pure none

         match zetaE with
         | some e' => translateExprToWire e' hint (isTopLevel := isTopLevel) (isNamed := isNamed)
         | none =>
            -- Fallback to general reduction (use default transparency to preserve
            -- Signal.pure and mixed operator instance structure)
            let e' ← CompilerM.liftMetaM (withTransparency TransparencyMode.default $ whnf e)
            if e' != e then translateExprToWire e' hint (isTopLevel := isTopLevel) (isNamed := isNamed)
            else translateExprToWireApp e hint isNamed

    | .proj _ idx eStruct => do
      -- Try iota reduction first: if `eStruct` reduces to a
      -- `Prod.mk a b`, replace `.proj idx (Prod.mk a b)` with
      -- the chosen component.  Without this, value-level Prods
      -- (e.g. `Reg.liveRead r` unfolds to `r.1` = `.proj 0 r`,
      -- and `r` is constructed via `Reg.mk live slot` which
      -- reduces to `Prod.mk live slot`) get slice-translated
      -- as if they were packed Signal-Prods, producing phantom
      -- bit ranges like `[15:8]` on an 8-bit register.
      let eReduced ← CompilerM.liftMetaM
        (withTransparency TransparencyMode.all $ whnf eStruct)
      if eReduced.isAppOf ``Prod.mk then
        let mkArgs := eReduced.getAppArgs
        if mkArgs.size >= 4 then
          let chosen := if idx == 0 then mkArgs[2]! else mkArgs[3]!
          return ← translateExprToWire chosen hint (isTopLevel := isTopLevel) (isNamed := isNamed)
      -- Same iota reduction for any other single-constructor structure
      -- (`KeccakFOut`, `RxOut`, …).  Taking field `idx` off the constructor
      -- application is exact for a record of any width; the bit-slice
      -- fallback below is not (see the note there).
      --
      -- Restricted to `idx ≥ 2`, i.e. exactly the cases the slice gets
      -- WRONG.  Fields 0 and 1 keep the old path: they were already correct,
      -- and routing them through here inlines the field's whole expression
      -- instead of emitting a slice, which blows the heartbeat budget on the
      -- BLS12-381 Fp12/G2 records.
      if idx >= 2 then
        if let some ctorName := eReduced.getAppFn.constName? then
          if let some (.ctorInfo ci) := (← CompilerM.liftMetaM Lean.getEnv).find? ctorName then
            let ctorArgs := eReduced.getAppArgs
            if ci.numFields > 0 ∧ ctorArgs.size == ci.numParams + ci.numFields
               ∧ idx < ci.numFields then
              return ← translateExprToWire ctorArgs[ci.numParams + idx]! hint
                (isTopLevel := isTopLevel) (isNamed := isNamed)
      -- The slice arithmetic below is only valid for a TWO-field
      -- packed product (`bundle2`): field 0 occupies the high half,
      -- field 1 the low half.  For a wider record `(1 - idx)`
      -- underflows in `Nat` — every field from index 1 up collapses to
      -- `lo = 0`, i.e. the LOW bits of the FIRST field.
      --
      -- That is a silently wrong wire, not a synthesis error.  It cost
      -- a long hunt via the Keccak sponge: `kfDonePrev <~ kf.done`
      -- (field 26 of 27 in `KeccakFOut`) lowered to `lane0 & 1`, so the
      -- sponge's `done` tracked a data bit, pulsed early, and the test
      -- read a mid-permutation digest.  It only became reachable when
      -- the elaborator stopped re-instantiating the sub-module per
      -- projection — before that, each projection got its own instance
      -- and the multi-output port map handled the lookup.
      --
      -- Refuse the guess instead: a >2-field record must be projected
      -- through the multi-output sub-module port map.
      -- Only fields 0 and 1 can be correct under the 2-field slice, so
      -- `idx ≤ 1` needs no check at all.  Guarding on that first keeps the
      -- `inferType`+`whnf` off the hot path — running it on every `.proj`
      -- blew the 200k-heartbeat budget on the BLS12-381 Fp12 records.
      let numFields ← if idx <= 1 then pure 2 else CompilerM.liftMetaM do
        let sTy ← Lean.Meta.inferType eStruct
        let sTy ← Lean.Meta.whnf sTy
        match sTy.getAppFn.constName? with
        | some sName =>
          match (← Lean.getEnv).find? sName with
          | some (.inductInfo iv) =>
            match iv.ctors with
            | [c] =>
              match (← Lean.getEnv).find? c with
              | some (.ctorInfo ci) => pure (ci.numFields)
              | _ => pure 2
            | _ => pure 2
          | _ => pure 2
        | none => pure 2
      if numFields > 2 then
        CompilerM.liftMetaM $ throwError
          s!"Cannot project field {idx} of a {numFields}-field record by bit-slicing: \
             the packed-product slice only covers 2-field bundles.  Project through \
             the sub-module's named output ports instead (call the \
             `@[hardware_module]` def directly, e.g. `let kf := wKeccakF …; kf.done`, \
             so the multi-output port map resolves the field by name)."
      let wireS ← translateExprToWire eStruct "s"
      -- Infer result type from the expression type
      let exprType ← cachedInferType e
      let hwType ← inferHWTypeFromSignal exprType
      let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
      let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
      let lo := (1 - idx) * width
      let hi := lo + width - 1
      CompilerM.emitAssign resWire (.slice (.ref wireS) hi lo)
      return resWire

    | .lit (.natVal n) => do
      -- Infer result type from the expression type
      let exprType ← cachedInferType e
      let hwType ← inferHWTypeFromSignal exprType
      let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
      let wire ← CompilerM.makeWire hint hwType (named := isNamed)
      CompilerM.emitAssign wire (.const (Int.ofNat n) width)
      return wire

    | .fvar fvarId => do
      match ← CompilerM.lookupVar fvarId with
      | some wireName => return wireName
      | none =>
        let st ← CompilerM.getCompilerState
        let known := st.varMap.map (fun (k,_) => k.name)
        CompilerM.liftMetaM $ throwError s!"Unbound variable: {fvarId.name}. Known: {known}"

    | .letE name type value body _ => do
      -- For any let binding, just use normal let handling
      let isHW ← try
        let _ ← inferHWTypeFromSignal type
        pure true
      catch _ =>
        pure false

      if isHW then
        -- Hardware let: translate value to wire.
        --
        -- NOTE ON #108: PR #108 solved this same problem by keying the
        -- `let` cache on the RAW `value` via `exprCache`.  That is kept
        -- here in the weaker-key form only as history: `canonKey` below
        -- subsumes it, because it survives an INTERMEDIATE binding.  Adding
        -- one `let num := y` between the module inputs and the engine takes
        -- a single `dividerQ` to FOUR under the raw-value key (7 → 27
        -- registers, measured) — the fvars are fresh per traversal, so the
        -- raw values are structurally different while the hardware is the
        -- same.  #108's instance-level caches (single-output guard + the IR
        -- CSE pass) are taken as-is; only this hunk differs.
        -- `isNamed := true` gives the wire the binder's readable name, but it
        -- also makes `translateExprToWire` bypass the expression cache in BOTH
        -- directions.  That matters because `runCircuitH` calls the user's
        -- `body` TWICE (once inside `Signal.loop` for the register next-state,
        -- once outside for the return value), so every `let e := <engine> …`
        -- in a `circuit do` was translated twice — emitting a SECOND COPY of
        -- the engine's registers each time, and once more per additional use
        -- of a projection.  Measured on `IP/Control/Observer.tvKalman`: one
        -- 6-register `dividerQ` engine became ELEVEN (76 registers instead of
        -- 16).  The two copies were structurally identical (same `Expr.hash`),
        -- so the cache would have collapsed them had `isNamed` not opted out.
        --
        -- Consult the cache first, and only fall back to a fresh named
        -- translation on a miss.  A cache hit returns the existing wire; it
        -- loses the pretty binder name for that occurrence, which is a
        -- cosmetic price for not duplicating hardware.
        -- Canonical cache key: the value with every already-translated fvar
        -- replaced by the WIRE it denotes.
        --
        -- Keying on `value` itself is not enough.  As soon as an intermediate
        -- binding sits between the module inputs and the engine —
        --     let num := y            -- ANY intermediate `let`, even an alias
        --     let e   := dividerQ … num …
        -- — the engine's `value` embeds `num`'s fvar, and each consumer of the
        -- `circuit do` body (every register write, plus the returned output)
        -- re-instantiates that binder with a FRESH fvar.  So the `value`s are
        -- structurally different per consumer and the cache never hits, while
        -- the hardware they denote is identical.  Measured: adding the single
        -- line `let num := y` to an otherwise-identical circuit took one
        -- `dividerQ` engine to FOUR (7 → 27 registers).
        --
        -- Wire names are stable within a module (they are what the emitted
        -- Verilog refers to), so substituting fvar → wire yields a key that is
        -- equal exactly when the denoted hardware is the same.
        let canonKey ← canonHardwareKey value
        let cachedValue? ← do
          if value.isFVar then pure none
          else CompilerM.liftMetaM do
            let m ← (sparkleLetWireCache.get : IO _)
            pure (m.get? canonKey)
        let valueWire ←
          match cachedValue? with
          | some w =>
            -- Cache hit: the hardware already exists, so do NOT translate
            -- again.  But emit an alias wire carrying this binder's name and
            -- return that.
            --
            -- Returning `w` directly (the original behaviour) silently drops
            -- the binder's name, which is only cosmetic until something reads
            -- a wire BY NAME at runtime.  The RV32 SoC does: `trap_taken` and
            -- `early_trap_taken` are the same expression, so the cache
            -- collapsed them onto the `early_` wire and `_gen_trap_taken`
            -- vanished from the emitted C — `JIT.resolveWires` then failed at
            -- run time on a name `SoCOutput.wireNames` still lists.
            --
            -- An alias costs one `assign` (which the backend's copy
            -- propagation folds away wherever the name is not needed) and
            -- keeps both names addressable.  The sharing — the whole point of
            -- the cache — is untouched: one instance, two names.
            let ty ← inferHWTypeFromSignal type
            let aliasW ← CompilerM.makeWire name.toString ty (named := true)
            CompilerM.emitAssign aliasW (.ref w)
            pure aliasW
          | none => translateExprToWire value name.toString
                      (isTopLevel := false) (isNamed := true)
        if !value.isFVar then
          CompilerM.liftMetaM
            (sparkleLetWireCache.modify (·.insert canonKey valueWire))
        CompilerM.withLocalDecl name type fun fvar => do
          let fvarId := fvar.fvarId!
          -- Also remember (fvar → defining expression) for
          -- downstream handlers that need to recover the original
          -- expression (e.g. struct-projection on a sub-module
          -- call result).  Done as a side-effect on a global map
          -- to avoid signature changes across the elaborator.
          CompilerM.liftMetaM (sparkleFvarValueMap.modify (·.insert fvarId.name value))
          CompilerM.withVarMapping fvarId valueWire do
            let bodyInst := body.instantiate1 fvar
            translateExprToWire bodyInst hint isTopLevel isNamed
      else
        -- Logic let: add to context for reduction (zeta)
        -- This allows let-bound values to be inlined when referenced
        CompilerM.withLetDecl name type value fun fvar => do
          let bodyInst := body.instantiate1 fvar
          translateExprToWire bodyInst hint isTopLevel isNamed

    | .lam binderName binderType body _ => do
      let isHWArg ← try
        let _ ← inferHWTypeFromSignal binderType
        pure true
      catch _ => pure false

      if isHWArg then
          let hwType ← inferHWTypeFromSignal binderType
          -- Reuse an existing input port if one already exists with
          -- this binder name — this matters for the multi-output
          -- record-return path where `splitReturnLeaves` emits one
          -- lambda per leaf sharing the same parameter binders.
          -- Without dedup, a 6-leaf 4-param function would emit
          -- 24 input ports instead of 4.
          let cs ← get
          let existingInput? :=
            if isTopLevel then
              cs.module.inputs.find? (fun p => p.name == "_gen_" ++ binderName.toString)
            else
              none
          let paramWire ←
            match existingInput? with
            | some p => pure p.name
            | none =>
              let w ← CompilerM.makeWire binderName.toString hwType (named := true)
              if isTopLevel then
                CompilerM.addInput w hwType
              pure w

          -- Process the lambda body within a proper local context
          CompilerM.withLocalDecl binderName binderType fun fvar => do
            let fvarId := fvar.fvarId!
            CompilerM.withVarMapping fvarId paramWire do
              let bodyInst := body.instantiate1 fvar
              -- Nested lambdas are also top-level if they're part of the function signature
              translateExprToWire bodyInst hint isTopLevel isNamed
      else
          -- Logic argument (e.g. config): add to context but no wire/input
          CompilerM.withLocalDecl binderName binderType fun fvar => do
            let bodyInst := body.instantiate1 fvar
            translateExprToWire bodyInst hint isTopLevel isNamed


    | _ =>
      -- App / Const fall-through.  Caching is handled by the
      -- `translateExprToWire` wrapper at the top of this mutual
      -- block — no need to duplicate the insert here.
      translateExprToWireApp e hint isNamed

  -- ===========================================================================
  -- Handler functions: each handles a category of expressions in translateExprToWireApp.
  -- Returns `some wireName` if handled, `none` if not applicable.
  -- ===========================================================================

  /-- Detect unsynthesizable patterns (if-then-else, Decidable) and throw errors -/
  partial def handleErrorPatterns (_e : Lean.Expr) (name : Name) (_args : Array Lean.Expr) (_hint : String) (_isNamed : Bool) : CompilerM Unit := do
    if name == ``ite || name == ``dite then
      let exprStr ← CompilerM.liftMetaM (ppExpr _e)
      CompilerM.liftMetaM $ throwError
        "if-then-else expressions cannot be synthesized to hardware.\n\n\
        Expression: {exprStr}\n\n\
        Use Signal.mux instead:\n\
        ❌ WRONG: if cond then a else b\n\
        ✓ RIGHT:  Signal.mux cond a b\n\n\
        See Tests/TestConditionals.lean for examples."
    if name == ``Decidable.rec || name == ``Decidable.casesOn then
      CompilerM.liftMetaM $ throwError
        "Decidable.rec (from if-then-else) cannot be synthesized.\n\n\
        Use Signal.mux for hardware multiplexers:\n\
        ✓ Signal.mux (cond : Signal d Bool) (ifTrue ifFalse : Signal d α) : Signal d α\n\n\
        See Tests/TestConditionals.lean for examples."

  /-- Handle Signal.fst, Signal.snd, Signal.map Prod.fst/Prod.snd -/
  partial def handleTupleProjections (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (isNamed : Bool) : CompilerM (Option String) := do
    -- Fast-path: most callers of handleTupleProjections hit a
    -- name that doesn't match any of the patterns below.  Bail
    -- out before calling `Lean.Meta.inferType` (which kicks off
    -- typeclass search / whnf and shows up as 75 ms / call on
    -- Ethernet's rxFramer body, dwarfing every other handler).
    -- The actual handler arms re-check the name as before.
    let isTupleName :=
      name == ``Sparkle.Core.Signal.Signal.fst ||
      name == ``Sparkle.Core.Signal.Signal.snd ||
      name == ``Sparkle.Core.Signal.bundle2 ||
      name == ``Sparkle.Core.Signal.Signal.map
    unless isTupleName do
      return none
    -- Signal.fst (new readable syntax)
    if name == ``Sparkle.Core.Signal.Signal.fst && args.size >= 1 then
      trace[sparkle.compiler] "→ tuple projection (fst)"
      let s := args[args.size-1]!
      let wireS ← translateExprToWire s "s" (isTopLevel := false)
      -- Slice index calc: prefer the WIRE'S declared width.
      -- The expression-type-derived total can drift from the
      -- realised concat width when the elaborator partially
      -- unfolds a `bundle2` chain (Issue #67 step 2), so always
      -- clamp to whichever is smaller — that's the bit-range
      -- the wire actually carries.
      let wireWidth ← CompilerM.getWireWidth wireS
      let exprType ← cachedInferType e
      let hwType ← inferHWTypeFromSignal exprType
      let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
      let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
      let sType ← cachedInferType s
      let sHWType ← inferHWTypeFromSignal sType
      let typeTotal := match sHWType with | .bitVector w => w | .bit => 1 | _ => 8
      let totalWidth := min wireWidth typeTotal
      let lo : Nat := if totalWidth ≥ width then totalWidth - width else 0
      let hi : Nat := if totalWidth ≥ 1 then totalWidth - 1 else 0
      CompilerM.emitAssign resWire (.slice (.ref wireS) hi lo)
      return some resWire

    -- Signal.snd (new readable syntax)
    if name == ``Sparkle.Core.Signal.Signal.snd && args.size >= 1 then
      trace[sparkle.compiler] "→ tuple projection (snd)"
      let s := args[args.size-1]!
      let wireS ← translateExprToWire s "s" (isTopLevel := false)
      let wireWidth ← CompilerM.getWireWidth wireS
      let exprType ← cachedInferType e
      let hwType ← inferHWTypeFromSignal exprType
      let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
      let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
      -- snd takes lower `width` bits, clamped to wire's declared width.
      let actualWidth := min width wireWidth
      let hi : Nat := if actualWidth ≥ 1 then actualWidth - 1 else 0
      CompilerM.emitAssign resWire (.slice (.ref wireS) hi 0)
      return some resWire

    -- Signal.bundle2 — pack two Signals into a Prod Signal.
    -- (Duplicates the early-interception rule above so paths
    -- that reach here via Bind/Pure reduction also work.)
    if name == ``Sparkle.Core.Signal.bundle2 && args.size >= 2 then
      let wireA ← translateExprToWire args[args.size-2]! "a"
      let wireB ← translateExprToWire args[args.size-1]! "b"
      let exprType ← cachedInferType e
      let hwType ← inferHWTypeFromSignal exprType
      let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
      CompilerM.emitAssign resWire (.concat [.ref wireA, .ref wireB])
      return some resWire

    -- Signal.map Prod.fst/snd (legacy syntax).
    -- Accept both bare `Prod.fst` and the partially-applied form
    -- `@Prod.fst α β` that Lean produces when the universe / type
    -- arguments are explicit.  We look at the head of `f`.
    if name == ``Sparkle.Core.Signal.Signal.map && args.size >= 2 then
      let f := args[args.size-2]!
      let s := args[args.size-1]!
      let fHead := f.getAppFn
      if fHead.isConstOf ``Prod.fst then
        trace[sparkle.compiler] "→ tuple projection (map fst)"
        let wireS ← translateExprToWire s "s" (isTopLevel := false)
        let wireWidth ← CompilerM.getWireWidth wireS
        let exprType ← cachedInferType e
        let hwType ← inferHWTypeFromSignal exprType
        let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
        let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
        let sType ← cachedInferType s
        let sHWType ← inferHWTypeFromSignal sType
        let typeTotal := match sHWType with | .bitVector w => w | .bit => 1 | _ => 8
        -- Issue #67 step 2: clamp slice to the wire's
        -- declared width.  When the elaborator partially
        -- unfolds a `bundle2` chain, `wireWidth` shrinks
        -- below the Prod-type-implied total — slicing
        -- `[typeTotal-1:typeTotal-width]` then points past
        -- the wire's last bit.
        let totalWidth := min wireWidth typeTotal
        let lo : Nat := if totalWidth ≥ width then totalWidth - width else 0
        let hi : Nat := if totalWidth ≥ 1 then totalWidth - 1 else 0
        CompilerM.emitAssign resWire (.slice (.ref wireS) hi lo)
        return some resWire
      if fHead.isConstOf ``Prod.snd then
        trace[sparkle.compiler] "→ tuple projection (map snd)"
        let wireS ← translateExprToWire s "s" (isTopLevel := false)
        let wireWidth ← CompilerM.getWireWidth wireS
        let exprType ← cachedInferType e
        let hwType ← inferHWTypeFromSignal exprType
        let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
        let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
        let actualWidth := min width wireWidth
        let hi : Nat := if actualWidth ≥ 1 then actualWidth - 1 else 0
        CompilerM.emitAssign resWire (.slice (.ref wireS) hi 0)
        return some resWire

    return none

  /-- Lower the actual applicative function body, preserving argument order,
      duplication, constants and nesting. Looking only at its outer operator
      is unsound: `fun x y => y - x` is not `fun x y => x - y`. -/
  partial def handleApplicative (e : Lean.Expr) (name : Name) (_args : Array Lean.Expr) (hint : String) (isNamed : Bool) : CompilerM (Option String) := do
    unless name == ``Sparkle.Core.Signal.Signal.ap do return none
    let rec collect (cur : Lean.Expr) (rest : List Lean.Expr) :
        Option (Lean.Expr × List Lean.Expr) :=
      let args := cur.getAppArgs
      if cur.isAppOf ``Sparkle.Core.Signal.Signal.ap && args.size >= 2 then
        collect args[args.size - 2]! (args.back! :: rest)
      else if cur.isAppOf ``Sparkle.Core.Signal.Signal.map && args.size >= 2 then
        some (args[args.size - 2]!, args.back! :: rest)
      else none
    let some (f, signals) := collect e [] | return none
    -- Every scalar binder and its wire mapping stays in scope until the
    -- complete body is lowered. No expression containing it escapes.
    let rec lower (f : Lean.Expr) (signals : List Lean.Expr) : CompilerM String := do
      match signals with
      | [] => translateExprToWire f hint (isNamed := isNamed)
      | sig :: rest =>
        let ty ← CompilerM.liftMetaM <| whnf (← inferType f)
        let .forallE binder argTy _ _ := ty
          | CompilerM.liftMetaM <| throwError "Applicative lowering: function arity mismatch"
        -- Seq.seq supplies its last argument through a Unit thunk. Expose
        -- that argument before early literal/Signal recognition runs.
        let wire ← translateExprToWire sig.headBeta "app_arg"
        CompilerM.withLocalDecl binder argTy fun scalar =>
          CompilerM.withVarMapping scalar.fvarId! wire do
            lower (Lean.mkApp f scalar).headBeta rest
    return some (← lower f signals)

  /-- Handle BitVec.extractLsb', shifts, concat, isPrimitive dispatch -/
  partial def handleBitVecOps (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (isNamed : Bool) : CompilerM (Option String) := do
    -- BitVec.extractLsb': bit slice extraction
    if name == ``BitVec.extractLsb' && args.size >= 4 then
      trace[sparkle.compiler] "→ extractLsb'"
      let start ← extractDimExpr args[args.size - 3]!
      let len ← extractDimExpr args[args.size - 2]!
      let bvWire ← translateExprToWire args[args.size - 1]! "slice_src"
      let resWire ← CompilerM.makeWire hint (hwTypeFromDim len) (named := isNamed)
      CompilerM.emitAssign resWire
        (makeSliceFromStartLength (.ref bvWire) start len)
      return some resWire

    -- BitVec.shiftLeft / BitVec.ushiftRight / BitVec.sshiftRight
    -- BitVec.zeroExtend / BitVec.setWidth: unsigned extension or truncation.
    if (name == ``BitVec.zeroExtend || name == ``BitVec.setWidth) && args.size >= 2 then
      trace[sparkle.compiler] "→ zeroExtend"
      let targetWidth ← extractDimExpr args[args.size - 2]!
      let sourceWire ← translateExprToWire args[args.size - 1]! "zext_src"
      return some (← lowerZeroExtendWire hint sourceWire targetWidth (isNamed := isNamed))

    if (name == ``BitVec.shiftLeft || name == ``BitVec.ushiftRight || name == ``BitVec.sshiftRight)
        && args.size >= 3 then
      trace[sparkle.compiler] "→ shift op {name}"
      let bvExpr := args[args.size - 2]!
      let natExpr := args[args.size - 1]!
      let wire1 ← translateExprToWire bvExpr "shift_a"
      let wire2 ← translateShiftAmount bvExpr natExpr "shift_b"
      let op := if name == ``BitVec.shiftLeft then Operator.shl
                else if name == ``BitVec.ushiftRight then Operator.shr
                else Operator.asr
      let exprType ← cachedInferType e
      let hwType ← inferHWTypeFromSignal exprType
      let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
      CompilerM.emitAssign resWire (.op op [.ref wire1, .ref wire2])
      return some resWire

    -- BitVec.append / HAppend.hAppend: concatenation
    if (name == ``BitVec.append ||
          (name == ``HAppend.hAppend && canonicalMethodInst name args)) && args.size >= 2 then
      trace[sparkle.compiler] "→ concat"
      let hiWire ← translateExprToWire args[args.size - 2]! "concat_hi"
      let loWire ← translateExprToWire args[args.size - 1]! "concat_lo"
      let exprType ← cachedInferType e
      let hwType ← inferHWTypeFromSignal exprType
      let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
      CompilerM.emitAssign resWire (.concat [.ref hiWire, .ref loWire])
      return some resWire

    -- BEq is a class projection. For a user instance, reduce that projection
    -- before primitive dispatch so its actual function body is preserved.
    if name == ``BEq.beq && args.size >= 4 && !canonicalMethodInst name args then
      let inst ← CompilerM.liftMetaM <| withTransparency TransparencyMode.all
        (whnf args[args.size - 3]!)
      if inst.isAppOf ``BEq.mk then
        -- Reduce the instance, not the applied comparison: whnf on the latter
        -- can unfold a supported BitVec primitive into an unsupported recursor.
        let body := (mkApp2 inst.getAppArgs.back! args[args.size - 2]! args.back!).headBeta
        return some (← translateExprToWire body hint (isNamed := isNamed))

    -- isPrimitive dispatch.  An overloaded method is lowered by name only when
    -- its instance is canonical; otherwise fall through to unfolding.
    if isPrimitive name &&
        (!overloadedPrimitiveMethods.contains name || canonicalMethodInst name args) then
      trace[sparkle.compiler] "→ primitive {name}"
      match getOperator name with
      | some op =>
        -- Unary operators: NOT, NEG, Complement.complement
        -- These may have extra typeclass/type args before the actual signal arg
        let isUnary := op == .not || op == .neg
        if isUnary && args.size >= 1 then
           let wire1 ← translateExprToWire args[args.size-1]! "arg1"
           let exprType ← cachedInferType e
           let hwType ← inferHWTypeFromSignal exprType
           let resultWire ← CompilerM.makeWire hint hwType (named := isNamed)
           CompilerM.emitAssign resultWire (.op op [.ref wire1])
           return some resultWire
        else if args.size >= 2 then
          let wire1 ← translateExprToWire args[args.size-2]! "arg1"
          let wire2 ← translateExprToWire args[args.size-1]! "arg2"
          let exprType ← cachedInferType e
          let hwType ← inferHWTypeFromSignal exprType
          let resultWire ← CompilerM.makeWire hint hwType (named := isNamed)
          CompilerM.emitAssign resultWire (.op op [.ref wire1, .ref wire2])
          return some resultWire
      | none =>
        CompilerM.liftMetaM $ throwError s!"Internal error: {name} is marked as primitive but has no operator"

    return none

  /-- Handle Signal.register, Signal.registerWithEnable -/
  partial def handleRegister (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (isNamed : Bool) : CompilerM (Option String) := do
    if name.toString.endsWith ".register" && args.size >= 2 then
      trace[sparkle.compiler] "→ register"
      let init := args[args.size-2]!
      let input := args[args.size-1]!
      let (initVal, _) ← extractBitVecLiteral init
      let inputWire ← translateExprToWire input "reg_input"
      let exprType ← CompilerM.liftMetaM (inferType e)
      let hwType ← inferHWTypeFromSignal exprType
      let resetKind ← inferResetKindFromSignal exprType
      let w ← CompilerM.emitRegister hint "clk" "rst" (.ref inputWire) initVal hwType
                (named := isNamed) (resetKind := resetKind)
      return some w

    -- Signal.registerWithEnable: register with conditional update
    if name.toString.endsWith ".registerWithEnable" && args.size >= 3 then
      trace[sparkle.compiler] "→ registerWithEnable"
      let init := args[args.size-3]!
      let en := args[args.size-2]!
      let input := args[args.size-1]!
      let (initVal, _) ← extractBitVecLiteral init
      let enWire ← translateExprToWire en "reg_en"
      let inputWire ← translateExprToWire input "reg_input"
      let exprType ← CompilerM.liftMetaM (inferType e)
      let hwType ← inferHWTypeFromSignal exprType
      let resetKind ← inferResetKindFromSignal exprType
      let muxWire ← CompilerM.makeWire (hint ++ "_mux") hwType
      let regWire ← CompilerM.emitRegister hint "clk" "rst" (.ref muxWire) initVal hwType
                     (named := isNamed) (resetKind := resetKind)
      CompilerM.emitAssign muxWire (.op .mux [.ref enWire, .ref inputWire, .ref regWire])
      return some regWire

    return none

  /-- Handle Signal.mux, lutMuxTree -/
  partial def handleMux (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (isNamed : Bool) : CompilerM (Option String) := do
    -- lutMuxTree: generate mux chain from concrete lookup table
    if name.toString.endsWith ".lutMuxTree" && args.size >= 5 then
      trace[sparkle.compiler] "→ lutMuxTree"
      let tableArg := args[args.size-2]!
      let indexArg := args[args.size-1]!
      let tableValues ← extractBitVecArray tableArg
      if tableValues.size > 0 then
        let exprType ← cachedInferType e
        let hwType ← inferHWTypeFromSignal exprType
        let (_, dataWidth) := tableValues[0]!
        let indexType ← CompilerM.liftMetaM (Lean.Meta.inferType indexArg)
        let indexHwType ← inferHWTypeFromSignal indexType
        let indexWidth := indexHwType.bitWidth
        let indexWire ← translateExprToWire indexArg "lut_idx"
        let mut resultWire ← CompilerM.makeWire (hint ++ "_d") hwType
        CompilerM.emitAssign resultWire (.const tableValues[0]!.1 dataWidth)
        for i in [:tableValues.size] do
          let (val, _) := tableValues[i]!
          let eqWire ← CompilerM.makeWire s!"{hint}_eq{i}" (.bitVector 1)
          CompilerM.emitAssign eqWire (.op .eq [.ref indexWire, .const i indexWidth])
          let muxWire ← CompilerM.makeWire s!"{hint}_m{i}" hwType
          CompilerM.emitAssign muxWire (.op .mux [.ref eqWire, .const val dataWidth, .ref resultWire])
          resultWire := muxWire
        return some resultWire

    -- Signal.mux
    if name.toString.endsWith ".mux" && args.size >= 3 then
      trace[sparkle.compiler] "→ mux"
      let cond := args[args.size-3]!
      let thenSig := args[args.size-2]!
      let elseSig := args[args.size-1]!
      return some (← translateMuxWith
        (fun e h t n => translateExprToWire e h t n)
        (muxResultType e)
        cond thenSig elseSig hint isNamed)

    return none

  /-- Handle Signal.memory, Signal.memoryComboRead -/
  partial def handleMemory (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (isNamed : Bool) : CompilerM (Option String) := do
    -- Signal.memory: synchronous RAM/BRAM
    if name.toString.endsWith ".memory" && !name.toString.endsWith ".memoryComboRead" && args.size >= 4 then
      trace[sparkle.compiler] "→ memory (sync)"
      -- Memory dedupe: a `Signal.memory ...` expression should
      -- emit ONE BRAM per synth pass, not one per
      -- splitReturnLeaves leaf.  The per-synth `exprCache`
      -- would handle this automatically — except `isNamed`
      -- bypasses the cache.  Maintain a separate
      -- memory-specific cache keyed on the Lean.Expr so
      -- repeat translations return the same readData wire
      -- and avoid re-emitting the memory statement.
      let addrWidthArg := args[args.size-6]!
      let dataWidthArg := args[args.size-5]!
      let (addrWidth, _) ← extractNatLiteral addrWidthArg
      let (dataWidth, _) ← extractNatLiteral dataWidthArg
      let writeAddr := args[args.size-4]!
      let writeData := args[args.size-3]!
      let writeEnable := args[args.size-2]!
      let readAddr := args[args.size-1]!
      let waW ← translateExprToWire writeAddr "mem_waddr"
      let wdW ← translateExprToWire writeData "mem_wdata"
      let weW ← translateExprToWire writeEnable "mem_we"
      let raW ← translateExprToWire readAddr "mem_raddr"
      -- Dedupe memory statements within a single module:
      -- if an existing `.memory` statement has identical
      -- (writeAddr, writeData, writeEnable, readAddr) wire
      -- refs, return its readData wire instead of emitting
      -- a new BRAM.  Required because per-leaf
      -- translations re-elaborate the same `Signal.memory
      -- writeSlot data we raddr` expression with fresh
      -- Lean.Expr identities — the structural exprCache
      -- misses, but the IR statement shape is identical.
      let parent := (← get).module
      let cachedRD : Option String := parent.body.findSome? fun stmt =>
        match stmt with
        | .memory _ aw dw _clk wa wd we ra rd _cr .. =>
          if aw == addrWidth ∧ dw == dataWidth then
            match wa, wd, we, ra with
            | .ref a, .ref d, .ref e, .ref r =>
              if a == waW ∧ d == wdW ∧ e == weW ∧ r == raW then
                some rd
              else none
            | _, _, _, _ => none
          else none
        | _ => none
      match cachedRD with
      | some rd => return some rd
      | none =>
        let w ← CompilerM.emitMemory hint addrWidth dataWidth "clk"
          (.ref waW) (.ref wdW) (.ref weW) (.ref raW) (named := isNamed)
        return some w

    -- Signal.memoryComboRead: memory with combinational (same-cycle) read
    if name.toString.endsWith ".memoryComboRead" && args.size >= 4 then
      trace[sparkle.compiler] "→ memory (combo read)"
      let addrWidthArg := args[args.size-6]!
      let dataWidthArg := args[args.size-5]!
      let (addrWidth, _) ← extractNatLiteral addrWidthArg
      let (dataWidth, _) ← extractNatLiteral dataWidthArg
      let writeAddr := args[args.size-4]!
      let writeData := args[args.size-3]!
      let writeEnable := args[args.size-2]!
      let readAddr := args[args.size-1]!
      let waW ← translateExprToWire writeAddr "mem_waddr"
      let wdW ← translateExprToWire writeData "mem_wdata"
      let weW ← translateExprToWire writeEnable "mem_we"
      let raW ← translateExprToWire readAddr "mem_raddr"
      let w ← CompilerM.emitMemoryComboRead hint addrWidth dataWidth "clk"
        (.ref waW) (.ref wdW) (.ref weW) (.ref raW) (named := isNamed)
      return some w

    return none

  /-- Handle Signal.loop, HWVector.get -/
  partial def handleLoop (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (isNamed : Bool) : CompilerM (Option String) := do
    -- HWVector.get: array indexing
    if name == ``Sparkle.Core.Vector.HWVector.get && args.size >= 2 then
      trace[sparkle.compiler] "→ HWVector.get"
      let vec := args[args.size-2]!
      let idx := args[args.size-1]!
      let vecWire ← translateExprToWire vec "vec"
      let idxWire ← translateExprToWire idx "idx"
      let exprType ← cachedInferType e
      let hwType ← inferHWTypeFromSignal exprType
      let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
      CompilerM.emitAssign resWire (.index (.ref vecWire) (.ref idxWire))
      return some resWire

    -- Signal.memoize: simulation-only cache wrapper.  It's
    -- functionally identity (returns its argument Signal
    -- unchanged) — `runCircuitH` adds it to break the
    -- Compiler C2 exponential evaluation cost.  Synthesis
    -- treats it as a pass-through so it never reaches Verilog.
    --
    -- IMPORTANT: when `inner` is a bound variable (BVar) — most
    -- commonly the `live` lambda binder of an enclosing
    -- `Signal.loop` — we must NOT recursively translate.  The
    -- BVar isn't bound in any local context yet (Signal.loop's
    -- handler binds it later), so naively translating it
    -- triggers an unfolder fallback that re-walks the *whole
    -- outer expression* — an infinite loop characteristic for
    -- FSM-shaped circuits where register reads feed register
    -- writes via memoize.  In this case we fall back to letting
    -- the caller's translation context handle the wrapper later
    -- (the Signal.loop handler that introduced the BVar will
    -- see the memoize chain after its own bind, where the BVar
    -- is replaced with a real wire).
    if name.toString.endsWith ".memoize" && args.size >= 1 then
      -- Peel ALL nested Signal.memoize wrappers iteratively.
      -- Each peel checks the head: if the application's head is
      -- ".memoize", pull the last arg as new "inner" and repeat.
      -- This is the same as stripMemoizeWrappers but at handler
      -- level, where we can run after Lean has resolved any
      -- aliases — the preprocessor at synth entry can't see
      -- memoize wrappers introduced by reducible/inline defs.
      let rec peelMemoize : Lean.Expr → Lean.Expr := fun ex =>
        let exFn := ex.getAppFn
        match exFn with
        | .const constName _ =>
          if constName.toString.endsWith ".memoize" then
            let exArgs := ex.getAppArgs
            if exArgs.size >= 1 then
              peelMemoize exArgs[exArgs.size - 1]!
            else ex
          else ex
        | _ => ex
      let inner := peelMemoize args.back!
      -- Special case: `Signal.memoize <fvar>` where the fvar is
      -- a known loop-state wire (registered in varMap by an
      -- enclosing Signal.loop).  Short-circuit directly without
      -- triggering the unfold path that loops back through the
      -- loop body.
      if let .fvar fvarId := inner then
        match ← CompilerM.lookupVar fvarId with
        | some wireName =>
          trace[sparkle.compiler] "→ memoize (resolved to loop-state wire {wireName})"
          return some wireName
        | none => pure ()
      trace[sparkle.compiler] "→ memoize (transparent for synth, peeled)"
      return some (← translateExprToWire inner "memoize_passthrough")

    -- Signal.loop
    if name.toString.endsWith ".loop" && args.size >= 1 then
      trace[sparkle.compiler] "→ loop"
      let f := args.back!
      let fReduced ← match f with
        | .lam .. => pure f
        | _ => CompilerM.liftMetaM (Lean.Meta.whnf f)
      match fReduced with
      | .lam binderName binderType body _ =>
        -- one `Signal.loop` per distinct hardware: the second evaluation
        -- of a `runCircuitH` body (see `sparkleLoopWireCache`) reaches
        -- the same loop expression modulo the enclosing live signal's
        -- name; canonicalised, it is a cache hit and NOT a second copy
        -- of the nested circuit's registers
        let loopKey ← canonHardwareKey e
        if (← IO.getEnv "SPARKLE_NO_LOOPCACHE").isNone then
         if let some w := (← CompilerM.liftMetaM (sparkleLoopWireCache.get : IO _)).get? loopKey then
          trace[sparkle.compiler] "→ loop (cache hit: {w})"
          return some w
        let exprType ← cachedInferType e
        let hwType ← inferHWTypeFromSignal exprType
        let loopWire ← CompilerM.makeWire "loop" hwType
        -- Use CompilerM.withLocalDecl to keep the fvar in scope for both
        -- MetaM (type checking) and CompilerM (wire mapping).
        let resultWire ← CompilerM.withLocalDecl binderName binderType fun fvar => do
          let bodyInst := body.instantiate1 fvar
          -- Register the loop fvar → loopWire mapping in BOTH
          -- the reader-scoped varMap (for the body's
          -- translation) and the persistent
          -- builder's sourceBindings (so later leaves that
          -- revisit body sub-expressions via the expression
          -- cache can still resolve the loop binder after
          -- `withVarMapping` scope has exited).
          CompilerM.bindSourceVariable fvar.fvarId! loopWire
          CompilerM.withVarMapping fvar.fvarId! loopWire do
            translateExprToWire bodyInst "loop_body"
        CompilerM.emitAssign loopWire (.ref resultWire)
        CompilerM.liftMetaM do
          sparkleWireCanon.modify (·.insert resultWire loopWire)
          sparkleLoopWireCache.modify (·.insert loopKey resultWire)
        return some resultWire
      | _ => CompilerM.liftMetaM $ throwError "Signal.loop argument must be a lambda"

    return none

  /-- Handle `Bind.bind` / `Pure.pure` specialised to the
      Sparkle Circuit monad.

      Lean's `do`-notation desugars to `Bind.bind m k` /
      `Pure.pure v` where Bind/Pure are typeclass projections.
      `unfoldDefinition?` (the default tryInline path) cannot
      reduce typeclass projections — it stops at the symbol with
      the instance still opaque, and the elaborator gives up.

      For Sparkle's Circuit monad the bind/pure unfold to pure
      value-level Prod manipulation that the existing Prod /
      Signal-map rules already lower.  We force a `.all`
      transparency `reduce` on the whole expression and recurse,
      mirroring how `Prod.rec` / `Prod.casesOn` are handled. -/
  partial def handleCircuitMonad (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (isNamed : Bool) : CompilerM (Option String) := do
    -- Recognize Bind.bind / Pure.pure when specialised to the
    -- Sparkle Circuit monad — typeclass projection that the
    -- default unfoldDefinition? path can't reduce.  We force a
    -- `.all`-transparency `whnf` to peel the typeclass projection,
    -- then recurse on the reduced expression.
    if name == ``Bind.bind || name == ``Pure.pure then
      if args.size >= 1 then
        let rec peelLambdas : Lean.Expr → Lean.Expr
          | .lam _ _ body _ => peelLambdas body
          | e => e
        let mHead := peelLambdas args[0]!
        if mHead.isAppOf ``Sparkle.Core.Circuit then
          let e' ← CompilerM.liftMetaM
            (withTransparency TransparencyMode.all $ whnf e)
          if e' != e then
            return some (← translateExprToWire e' hint (isNamed := isNamed))
    -- Value-level Prod.mk hit directly as the expression head.
    -- This shows up after `Bind.bind` peels and the user's `do`
    -- block reduces to `Prod.mk out_payload builder` (where
    -- `builder : Circuit.NextBuilder dom S`).  We're being asked
    -- for the wire of the whole Prod, but the only meaningful
    -- payload is the first component (the output: a Signal, a
    -- tuple of Signals, or a user-defined record packing
    -- Signals); the builder is a closure with no wire
    -- representation.
    --
    -- Detection: the second component's type is
    -- `Circuit.NextBuilder dom S` (= `Signal dom S → Signal
    -- dom S`).  When that pattern matches we treat the Prod as
    -- "circuit return + state-update accumulator" and only
    -- translate the first component.  This covers both the
    -- single-Signal case the original code handled and the
    -- ρ-generalised case (multi-output records / tuples).
    if name == ``Prod.mk && args.size >= 4 then
      let αType := args[0]!
      let βType := args[1]!
      -- Detection: either
      --   (a) α is a Signal (the legacy single-output case), OR
      --   (b) β is a `Circuit.NextBuilder` (or its η-expanded form
      --       `Signal _ S → Signal _ S`), meaning the Prod came
      --       from a `Circuit.pure'` and the second slot is the
      --       state-update accumulator that has no wire image.
      -- Either way, only the first component carries the wire(s);
      -- the second is discarded.
      let isNextBuilder :=
        βType.isAppOf ``Sparkle.Core.Circuit.NextBuilder ||
        βType.isAppOf ``Sparkle.Core.Circuit.SigList ||
        (match βType with
         | .forallE _ _ _ _ => true  -- η-expanded Signal _ S → Signal _ S
         | _ => false)
      if αType.isAppOf ``Sparkle.Core.Signal.Signal || isNextBuilder then
        let outExpr := args[2]!
        -- Force-reduce so any `Reg.liveRead r` (which unfolds to
        -- `r.1` = `Prod.fst (Prod.mk live slot)`) becomes `live`
        -- before we hand it off to translateExprToWire.  Without
        -- this the elaborator interprets the surviving `Prod.fst`
        -- expression as a Signal-Prod slice and emits a phantom
        -- `[totalWidth-1 : totalWidth - w]` Verilog range.
        let outReduced ← CompilerM.liftMetaM
          (withTransparency TransparencyMode.all $ whnf outExpr)
        return some (← translateExprToWire outReduced hint (isNamed := isNamed))
    -- Value-level Prod.fst / Prod.snd hitting a `Prod.mk a b`
    -- under `.all` transparency — iota-reduce to the chosen
    -- component.  Lean's default-transparency whnf doesn't
    -- always strip these (esp. when the Prod.mk has functions
    -- as components, as `runCircuit`'s `(out, builder)` does).
    if (name == ``Prod.fst || name == ``Prod.snd) && args.size >= 3 then
      -- `Prod.fst/snd` takes `[α, β, pair]` (3 explicit args).
      -- When the result is then applied further (e.g.
      -- `bResult.snd live` parses as `(Prod.snd pair) live`),
      -- `getAppArgs` still gives us `[α, β, pair, extra...]`.
      let pair := args[2]!
      let pairReduced ← CompilerM.liftMetaM
        (withTransparency TransparencyMode.all $ whnf pair)
      if pairReduced.isAppOf ``Prod.mk then
        let mkArgs := pairReduced.getAppArgs
        if mkArgs.size >= 4 then
          let chosen := if name == ``Prod.fst then mkArgs[2]! else mkArgs[3]!
          -- Re-apply any trailing args after the projection
          let trailing := args.toList.drop 3 |>.toArray
          let appliedExpr := mkAppN chosen trailing
          return some (← translateExprToWire appliedExpr hint (isNamed := isNamed))
    return none

  /-- Handle a Lean function call by either inlining the body
      (the **default**) or emitting a sub-module instance (only
      when the declaration is tagged `@[hardware_module]`).

      Default = inline keeps the generated Verilog flat, which is
      what most users want for alias-style helpers and small
      combinational functions: writing
      `def passthrough x := x` shouldn't multiply the module
      count of every caller.

      Opt INTO sub-module emission with `@[hardware_module]` for
      designs you want to see as their own Verilog `module foo`
      block — a CPU, an ALU you intend to re-use, an arbiter,
      etc.  Downstream tools (P&R, OOC synth, hierarchical
      timing) can then treat the boundary as a real compile
      unit.

      `@[inline_hardware]` is accepted as a self-documenting
      synonym for "always inline".  Today it has no effect over
      the default, but it stays binding if a future heuristic
      ever auto-promotes a definition to a module. -/
  partial def handleDefinitionUnfold (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (isNamed : Bool) : CompilerM (Option String) := do
    let isValidDef ← CompilerM.liftMetaM do
      try
        let constInfo ← getConstInfo name
        match constInfo with
        | .defnInfo _ => return true
        | _ => return false
      catch _ => return false

    if !isValidDef then return none

    let env ← CompilerM.liftMetaM getEnv

    -- Debugging hook: log hw-module call sites for cache-miss
    -- diagnosis.  Activated only when env var
    -- SPARKLE_DEBUG_HWCALL=1 to keep the normal trace clean.
    if Sparkle.Compiler.isHardwareModule env name then
      let dbg ← CompilerM.liftMetaM (do
        let s ← IO.getEnv "SPARKLE_DEBUG_HWCALL"
        return s.isSome)
      if dbg then
        let cache ← CompilerM.liftMetaM (sparkleSubInstanceOutputs.get : IO _)
        CompilerM.liftMetaM $ IO.eprintln
          s!"[hwcall-dbg] {name} eHash={e.hash} args.size={args.size} subInstanceMap.size={cache.size}"
        CompilerM.liftMetaM (← IO.getStderr).flush
    -- Structure field accessors (e.g. `RxOut.dmac`) are valid
    -- `defnInfo`s but they have a different calling convention
    -- than a hardware function: the value-level arg is the
    -- record itself, and `synthesizeCombinational` would try to
    -- open it into N fields (one per `Signal dom α` field).
    -- Always inline projections through `unfoldDefinition?` and
    -- never fall back to sub-module synthesis.
    if let some structName := env.getProjectionStructureName? name then
      -- Multi-output sub-module shortcut: if the projection's
      -- record argument is a direct call to an `@[hardware_module]`
      -- def whose return type is the same struct, we can avoid
      -- the whnf unfold (which is expensive and step-limited)
      -- by emitting a sub-module instance and pulling the field
      -- straight from the corresponding output port.
      -- Multi-output sub-module shortcut: if the projection's
      -- record argument is (after fvar resolution) a direct call
      -- to a `@[hardware_module]` def, translate the call first
      -- — that emits a sub-module instance and populates
      -- sparkleSubInstanceOutputs with one entry per output port.
      -- Then look up the wire for the projected field name.
      --
      -- This avoids the previous shortcut's duplicate sub-module
      -- synthesis and works whether the call site is a literal
      -- application or a `let engine := kvHw …` binding.
      if args.size >= 1 then
        let recordArgRaw := args.back!
        let mut recordArg := recordArgRaw
        if recordArg.isFVar then
          let fvarId := recordArg.fvarId!
          let fvarMap ← CompilerM.liftMetaM (sparkleFvarValueMap.get : IO _)
          match fvarMap.get? fvarId.name with
          | some val => recordArg := val
          | none =>
            let val? ← CompilerM.liftMetaM do
              let lctx ← getLCtx
              match lctx.find? fvarId with
              | some decl => return decl.value?
              | none => return none
            if let some val := val? then
              recordArg := val
        let recFn := recordArg.getAppFn
        if let .const recName _ := recFn then
          let envNow ← CompilerM.liftMetaM getEnv
          if Sparkle.Compiler.isHardwareModule envNow recName then
            -- Resolve the field name from the projection.
            let some projInfo := envNow.getProjectionFnInfo? name
              | pure ()
            let some indVal ← (try some <$> CompilerM.liftMetaM (getConstInfoInduct structName) catch _ => pure none)
              | pure ()
            let ctorName := indVal.ctors.head!
            let ctorInfo ← CompilerM.liftMetaM (getConstInfoCtor ctorName)
            let fieldName ← CompilerM.liftMetaM do
              Lean.Meta.forallTelescopeReducing ctorInfo.type fun fargs _ => do
                let allFields := fargs.toList.drop indVal.numParams
                if h : projInfo.i < allFields.length then
                  return (← allFields[projInfo.i].fvarId!.getUserName).toString
                else
                  return s!"field{projInfo.i}"
            -- Cache key.  We must agree with the sub-module
            -- instance emit handler below — both sides canonise
            -- the SAME call expression (the projection recovers
            -- the original app from `sparkleFvarValueMap`, and
            -- `translateExprToWire` hands that very object to the
            -- emit handler), so `canonHardwareKey` yields the same
            -- string at both sites.
            --
            -- Raw `arg.hash` cannot be used (fvar names regenerate
            -- per pass → per-leaf-distinct keys → one instance per
            -- projection, issue #71), and the previous
            -- `(recName, args.size)` key could not tell two calls
            -- with DIFFERENT arguments apart — a mesh of
            -- `pe a …`/`pe b …` silently collapsed onto the first
            -- instance (issue #120).  The fvar→wire abstraction
            -- distinguishes argument wires while staying stable
            -- within the pass.
            let callKey : UInt64 := hash (← canonHardwareKey recordArg)
            let portMap ← CompilerM.liftMetaM (sparkleSubInstanceOutputs.get : IO _)
            if let some w := portMap.get? (callKey, fieldName) then
              trace[sparkle.compiler] "→ projection: cached wire {w} for {fieldName}"
              return some w
            -- Not cached yet → translate the call once.  The
            -- multi-output sub-module instance path will populate
            -- sparkleSubInstanceOutputs as a side effect.
            let _ ← translateExprToWire recordArg s!"sub_call"
            let portMap' ← CompilerM.liftMetaM (sparkleSubInstanceOutputs.get : IO _)
            if let some w := portMap'.get? (callKey, fieldName) then
              trace[sparkle.compiler] "→ projection: wired sub-call, returning {w} for {fieldName}"
              return some w
            trace[sparkle.compiler] "→ projection: sub-call did not register {fieldName} (call hash {callKey})"
      -- Standard path (no multi-output shortcut): reduce the
      -- record arg until a `.mk` constructor appears, then pull
      -- the field directly.  Same as the original implementation.
      if args.size >= 1 then
        let recordArg := args.back!
        let mkName := structName ++ `mk
        let mut cur := recordArg
        let mut steps := 0
        while steps < 32 do
          -- Reduce the head: try unfoldDefinition? first, then
          -- whnf for the harder cases (typeclass dispatch under
          -- runCircuitH).  Stop as soon as the head is the
          -- expected ctor.
          let headName? := cur.getAppFn.constName?
          if headName? == some mkName then
            break
          let stepped ← CompilerM.liftMetaM do
            match ← Lean.Meta.unfoldDefinition? cur with
            | some e' => return e'
            | none => Lean.Meta.whnf cur
          if stepped == cur then break
          cur := stepped
          steps := steps + 1
        if cur != recordArg then
          -- Got the constructor — directly grab the projected
          -- field from the ctor's args rather than re-applying
          -- the projection definition (which would route back to
          -- this same code path).  The structure projection's
          -- `structureFieldIdx` field gives the position of the
          -- field within the constructor's value args.
          let headName? := cur.getAppFn.constName?
          let mkName := structName ++ `mk
          if headName? == some mkName then
            -- Find which field this projection targets.
            let some projInfo := env.getProjectionFnInfo? name
              | return none
            -- ctor args = [implicit params...] ++ [field values]
            let ctorArgs := cur.getAppArgs
            let fieldIdx := projInfo.numParams + projInfo.i
            if fieldIdx < ctorArgs.size then
              let fieldExpr := ctorArgs[fieldIdx]!
              let w ← translateExprToWire fieldExpr hint (isNamed := isNamed)
              return some w
          -- Couldn't pull out the field directly; fall back to
          -- re-assembling and hoping a later pass picks it up.
          let projHead := e.getAppFn
          let leadingArgs := args.pop
          let eReassembled := mkAppN (mkAppN projHead leadingArgs) #[cur]
          let w ← translateExprToWire eReassembled hint (isNamed := isNamed)
          return some w
      return none

    let optedIntoModule := Sparkle.Compiler.isHardwareModule env name

    -- Helper: try the "unfold and translate inline" path — the default.
    -- Returns the wire on success, or stashes the deepest captured
    -- inline failure for the outer error message.
    -- Hold the raw exception, NOT its rendered string.  Rendering a
    -- Lean exception (`toMessageData.toString`) pretty-prints the
    -- offending Expr and is expensive; on wide FSMs the inline path
    -- fails-then-recovers thousands of times, so eagerly stringifying
    -- every recoverable failure dominated synth wall-time.  We defer
    -- the render to the single terminal error site (line ~2548),
    -- which only runs when we actually throw.
    let lastInlineFail : IO.Ref (Option Lean.Exception) ← IO.mkRef none
    let tryInline : CompilerM (Option String) := do
      let eReduced ← CompilerM.liftMetaM do
        match ← Lean.Meta.unfoldDefinition? e with
          | some e' => return e'
          | none => return e
      if eReduced != e then
        try
          let w ← translateExprToWire eReduced hint (isNamed := isNamed)
          return some w
        catch ex1 =>
          lastInlineFail.set (some ex1)
          -- Inline expansion failed (often due to mixed Signal/BitVec operators
          -- inside the expanded body). Retry with reducible transparency to
          -- prevent over-expansion of Signal.pure and OfNat instances.
          try
            let eReduced2 ← CompilerM.liftMetaM do
              Lean.Meta.withTransparency .reducible do
                match ← Lean.Meta.unfoldDefinition? e with
                | some e' => return e'
                | none => return e
            if eReduced2 != e then
              let w ← translateExprToWire eReduced2 hint (isNamed := isNamed)
              return some w
            else
              return none
          catch ex2 =>
            lastInlineFail.set (some ex2)
            return none
      else
        return none

    -- Default: inline the body into the caller.  Only opt INTO a
    -- sub-module instance when the user tagged the definition
    -- `@[hardware_module]`, OR when inlining genuinely fails
    -- (typeclass dispatch, opaque dictionaries, …) and a fresh
    -- module synthesis can rescue the call.
    let subResult? : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) ←
      if optedIntoModule then
        trace[sparkle.compiler] "→ sub-module instance {name} (hardware_module)"
        try
          some <$> CompilerM.liftMetaM (synthesizeCombinational name)
        catch _ =>
          CompilerM.liftMetaM $ throwError
            s!"Sub-module synthesis failed for {name} (tagged @[hardware_module])"
      else
        -- Try inlining first.  If it succeeds we return immediately;
        -- if not, fall through to a sub-module synthesis attempt.
        trace[sparkle.compiler] "→ definition unfold {name} (inline by default)"
        match ← tryInline with
        | some w => return some w
        | none =>
          try
            some <$> CompilerM.liftMetaM (synthesizeCombinational name)
          catch _ => pure none
    match subResult? with
    | none =>
      let lastFail ← lastInlineFail.get
      let detail ←
        match lastFail with
        | some ex => do
          let msg ← CompilerM.liftMetaM ex.toMessageData.toString
          pure s!"\n\nInline expansion failed with:\n{msg}\n\nCommon causes (sim-pass but synth-fail patterns):\n  · `sig.map (fun _ => true)` / `(fun _ => false)` — lifts a Bool constant\n    the synth elaborator has no rule for.  Use Signal.pure or drop the\n    redundant `&& true`.\n  · `sig.map (fun b => if b then C1 else C2)` for BitVec constants —\n    replace with `Signal.mux sig (Signal.pure C1) (Signal.pure C2)`.\n  · `(· != ·) <$> a <*> b` or `Bool.not <$> sig` —\n    use `(fun a b => !(a == b)) <$> a <*> b` and `(fun b => !b) <$> sig`.\n  · Returning a tuple from `circuit do` — wrap in a structure with\n    `HasDomain` (see IP/Net/Ethernet.lean RxOut)."
        | none => pure ""
      CompilerM.liftMetaM $ throwError
        s!"Cannot synthesise {name}: not inlinable and not a hardware module.{detail}"
    | some (subModule, subDesign) =>

    trace[sparkle.compiler] "→ sub-module synthesis {name}"
    -- Add the child's transitive modules and the child itself to the
    -- design, but only if not already present.  Two calls to the same
    -- sub-module must produce *one* module definition + two
    -- instantiations, not two duplicate definitions.
    let existing := (← get).design.modules.map (·.name)
    for m in subDesign.modules do
      if !existing.contains m.name then
        CompilerM.addModuleToDesign m
    if !existing.contains subModule.name &&
       !((← get).design.modules.any (·.name == subModule.name)) then
      CompilerM.addModuleToDesign subModule

    let mut connections := []
    -- Wire the child's clk / rst to the parent's clk / rst port (if
    -- the child has them).  If the parent doesn't already declare
    -- the matching input port, add it: a sequential sub-module
    -- requires its parent to expose clk/rst at its own boundary.
    -- Otherwise nextpnr / Verilator will complain about an
    -- undriven clock.
    for p in subModule.inputs do
      if p.name == "clk" || p.name == "rst" then
        let parent := (← get).module
        if !parent.inputs.any (·.name == p.name) then
          CompilerM.addInput p.name p.ty
        connections := (p.name, Sparkle.IR.AST.Expr.ref p.name) :: connections

    let inputPorts := subModule.inputs.filter (fun p => p.name != "clk" && p.name != "rst")
    if args.size < inputPorts.length then
       CompilerM.liftMetaM $ throwError s!"Sub-module {name} requires {inputPorts.length} args, but got {args.size}"

    for i in [:inputPorts.length] do
       let argExpr := args[args.size - inputPorts.length + i]!
       let argWire ← translateExprToWire argExpr s!"arg{i}"
       connections := (inputPorts[i]!.name, Sparkle.IR.AST.Expr.ref argWire) :: connections

    -- Single-output sub-module: allocate one wire bound to "out".
    -- Multi-output (struct-returning) sub-module: allocate one
    -- wire per output port, remember each (call-expr-hash, field
    -- name) → wire mapping in the global sub-instance port map so
    -- subsequent projection handlers can recover them, and return
    -- the *first* wire as a placeholder (the projection handlers
    -- will normally resolve through the map and never look at it).
    let exprType ← cachedInferType e
    let resWire ← match subModule.outputs with
      | [singleOut] =>
        -- Bind to the sub-module's ACTUAL output port name
        -- rather than a hardcoded "out".  For scalar-Signal
        -- sub-modules `synthesizeCombinational` emits the
        -- port literally named "out" — those still work.  For
        -- a sub-module whose body is a single struct-field
        -- projection (e.g. `httpGotSig` wrapping
        -- `(httpRequestParser b v).gotRequest`), the realised
        -- single output keeps the field's name (`gotRequest`),
        -- and the previous hardcoded "out" produced C++ /
        -- Verilog that referenced a non-existent port.
        -- (Issue #74.)
        let hwType ← inferHWTypeFromSignal exprType
        -- Idempotency guard (Issue #107): if this exact instance
        -- (same parent module, same child module, same input
        -- connections) was already emitted during an earlier
        -- leaf pass of the current module synth, reuse its
        -- output wire instead of emitting a duplicate.  The
        -- connections list at this point holds clk/rst + all
        -- input-port wires, built in deterministic order, so it
        -- serialises into a stable key.
        let parentName := (← get).module.name
        let connKey := String.intercalate ";"
          (connections.reverse.map (fun (p, rhs) => s!"{p}={rhs}"))
        let instKey := s!"{parentName}#{subModule.name}#{connKey}"
        let instCache ← CompilerM.liftMetaM (sparkleSingleOutInstanceCache.get : IO _)
        if let some cachedW := instCache.get? instKey then
          return some cachedW
        let w ← CompilerM.makeWire hint hwType (named := isNamed)
        CompilerM.liftMetaM
          (sparkleSingleOutInstanceCache.modify (·.insert instKey w))
        -- Record the wire for this call expression, exactly as the certified
        -- instance arm does: the arm honours a later cache hit only when the
        -- builder's record names this expression (`instHitValid`), so a
        -- let-bound call first lowered HERE still dedupes when the named
        -- re-walk reaches the arm (Issue #107).
        modify fun s => { s with translateRecord := s.translateRecord.insert w e }
        connections := (singleOut.name, Sparkle.IR.AST.Expr.ref w) :: connections
        pure w
      | _multiOut =>
        -- IMPORTANT: the cache key must agree between this
        -- (sub-module instance emit) and the projection handler
        -- that later looks up `(callKey, fieldName) → wire`.
        -- The projection handler keys on `recordArg.hash` AFTER
        -- fvar resolution (`let engine := kvHw …; engine.foo`
        -- looks up `engine` in `sparkleFvarValueMap` to recover
        -- `kvHw …`).  We must mirror that here: use the call's
        -- **function-name-and-args** hash, not the raw `e.hash`
        -- — Lean re-elaborates structurally-identical apps into
        -- distinct Expr objects, so pointer-equal hashes won't
        -- match across the two handlers.
        --
        -- Match the projection handler's cache key: both sites
        -- run `canonHardwareKey` over the same call expression
        -- (see the projection arm in handleDefinitionUnfold), so
        -- every projection on a `let engine := kvHw …` resolves to
        -- the same emitted instance (issue #71) while calls with
        -- different argument wires get their own instances
        -- (issue #120).
        let keyHash : UInt64 := hash (← canonHardwareKey e)
        -- Idempotency check.  If we've already emitted this
        -- `(keyHash, _)` instance in the current synth, return
        -- the cached first-output wire and skip the emit step.
        -- Without this, every projection on the same
        -- `let engine := kvHw …` triggers a fresh emitInstance
        -- (Issue #71).
        let portMapNow ← CompilerM.liftMetaM (sparkleSubInstanceOutputs.get : IO _)
        let firstOutP? := subModule.outputs.head?
        let alreadyEmitted := match firstOutP? with
          | some firstOutP => portMapNow.contains (keyHash, firstOutP.name)
          | none => false
        if alreadyEmitted then
          -- Re-declare all the cached wires in the current
          -- module's wires list before returning the cached
          -- first-output wire.  Without this, the
          -- `sparkleSubInstanceOutputs` cache persists across
          -- nested `synthesizeCombinational` calls (e.g.
          -- `msvrByte` then `msvrValid` both inlining the same
          -- memcachedServer body) and the second module ends
          -- up referencing wire names it never declared,
          -- producing C++/Verilog where
          -- `_tmp_engine_replyValid_29` is used but never
          -- declared in the enclosing class/module.
          -- If this parent module ALREADY has the cached wires
          -- declared, the instance was emitted earlier in the
          -- same synth pass — just return the cached wire.
          -- Re-emitting the instance here would produce N copies
          -- of the sub-module in the parent (one per projection
          -- of `let engine := kvHw …; engine.foo`, which is
          -- exactly the over-instantiation Issue #71 step-2
          -- already tracks).
          let firstOutP := firstOutP?.get!
          let cachedW := portMapNow.get? (keyHash, firstOutP.name) |>.get!
          let parentNow := (← get).module
          let alreadyDeclared :=
            parentNow.wires.any (·.name == cachedW) ||
            parentNow.inputs.any (·.name == cachedW) ||
            parentNow.outputs.any (·.name == cachedW)
          if alreadyDeclared then
            return some cachedW
          -- New parent module that doesn't yet have the cached
          -- wires (cross-module reuse).  Declare them and emit
          -- the instance once.
          for outP in subModule.outputs do
            if let some cachedName := portMapNow.get? (keyHash, outP.name) then
              let parent := (← get).module
              if !parent.inputs.any (·.name == cachedName)
                 ∧ !parent.wires.any (·.name == cachedName)
                 ∧ !parent.outputs.any (·.name == cachedName) then
                let p : Port := { name := cachedName, ty := outP.ty }
                let cs ← get
                set { cs with module := cs.module.addWire p }
                CompilerM.liftMetaM
                  (sparkleWireWidthCache.modify
                    (·.insert cachedName (match outP.ty with
                      | .bitVector w => w | .bit => 1 | _ => 8)))
              connections := (outP.name, Sparkle.IR.AST.Expr.ref cachedName) :: connections
          let instName ← CompilerM.freshName s!"inst_{subModule.name}"
          instLinkCheck name subModule connections.reverse
          CompilerM.emitInstance subModule.name instName connections.reverse
          return some cachedW
        let mut firstW : Option String := none
        for outP in subModule.outputs do
          let w ← CompilerM.makeWire s!"{hint}_{outP.name}" outP.ty (named := false)
          connections := (outP.name, Sparkle.IR.AST.Expr.ref w) :: connections
          CompilerM.liftMetaM (sparkleSubInstanceOutputs.modify (·.insert (keyHash, outP.name) w))
          if firstW.isNone then firstW := some w
        pure (firstW.getD "")

    -- Generate a fresh, unique instance name.  Two calls to the same
    -- sub-module within a single parent must produce two distinct
    -- `inst_*` names — otherwise the emitted Verilog has a duplicate
    -- identifier.
    let instName ← CompilerM.freshName s!"inst_{subModule.name}"
    instLinkCheck name subModule connections.reverse
    CompilerM.emitInstance subModule.name instName connections.reverse
    return some resWire

  -- ===========================================================================
  -- Main dispatcher: routes expressions to the appropriate handler
  -- ===========================================================================

  partial def translateExprToWireApp (e : Lean.Expr) (hint : String) (isNamed : Bool := false) : CompilerM String := do
    let fn := e.getAppFn
    let args := e.getAppArgs

    match fn with
    | .const name _ =>
      trace[sparkle.compiler] "translateExprToWireApp name={name} args.size={args.size}"

      -- Note: We don't detect unbundle2 usage here because:
      -- 1. unbundle2 itself is fine (returns a tuple)
      -- 2. Pattern matching on unbundle2 gets compiled away before synthesis
      -- 3. We'd only catch non-problematic uses, creating false positives

      profHandler 0 (handleErrorPatterns e name args hint isNamed)  -- throws or returns ()

      -- `Circuit.SigList`'s chain terminator carries no data, so it lowers
      -- to a 0-width constant rather than a module instantiation.  It shows
      -- up either bare (`PUnit.unit`, which carries a universe argument and
      -- so arrives here as an application) or wrapped (`Signal.pure
      -- PUnit.unit`).
      --
      -- Both forms are gated on the argument's TYPE, never on a whnf'd
      -- payload value: `whnf` of a payload at some other type can reduce to
      -- `Unit.unit`, and collapsing on that basis silently rewrites a real
      -- output to constant zero.  That is what broke the Keccak sponge —
      -- the digest came out equal to the unpermuted padded input.
      if name == ``PUnit.unit || name == ``Unit.unit then
        let resWire ← CompilerM.makeWire hint (.bitVector 0) (named := isNamed)
        CompilerM.emitAssign resWire (.const 0 0)
        return resWire
      if (name == ``Sparkle.Core.Signal.Signal.pure ||
          name == ``Sparkle.Core.Signal.Signal.lit) && args.size >= 1 then
        -- Cheap syntactic pre-filter first: the terminator is literally
        -- `PUnit.unit` / `Unit.unit`.  Only then pay for inferType+whnf.
        -- Running those on every `Signal.pure` blew the heartbeat budget on
        -- the BLS12-381 Fp12/G2 modules.
        let a := args.back!
        let looksUnit := a.isConstOf ``PUnit.unit || a.isConstOf ``Unit.unit
        let argTy ← if !looksUnit then pure (Lean.mkConst ``Nat) else
          CompilerM.liftMetaM (whnf (← Lean.Meta.inferType a))
        if argTy.isConstOf ``Unit || argTy.isConstOf ``PUnit then
          let resWire ← CompilerM.makeWire hint (.bitVector 0) (named := isNamed)
          CompilerM.emitAssign resWire (.const 0 0)
          return resWire
      if (name == ``Seq.seq || name == ``Functor.map) && args.size >= 1 then
        if args[0]!.isAppOf ``Sparkle.Core.Signal.Signal then
          let rec normSpine (x : Lean.Expr) (fuel : Nat) : MetaM Lean.Expr := do
            match fuel with
            | 0 => return x
            | fuel + 1 =>
              let h := x.getAppFn
              if h.isConstOf ``Seq.seq then
                match ← withTransparency TransparencyMode.all
                    (Lean.Meta.whnfUntil x ``Sparkle.Core.Signal.Signal.ap) with
                | some x' => normSpine x' fuel
                | none => return x
              else if h.isConstOf ``Functor.map then
                match ← withTransparency TransparencyMode.all
                    (Lean.Meta.whnfUntil x ``Sparkle.Core.Signal.Signal.map) with
                | some x' =>
                  -- The lifted function's binders are hygienic macro names,
                  -- different at every occurrence of the same `(· op ·)`;
                  -- give them the canonical names the front end uses, so two
                  -- occurrences of one lifted expression are one cache key.
                  let xa := x'.getAppArgs
                  if x'.isAppOf ``Sparkle.Core.Signal.Signal.map && xa.size ≥ 3 then
                    normSpine (Lean.mkAppN x'.getAppFn
                      ((xa.set! (xa.size - 2) (inlCanonLam 0 xa[xa.size - 2]!)).set!
                        (xa.size - 3) (inlCanonPi xa[xa.size - 3]!))) fuel
                  else normSpine x' fuel
                | none => return x
              else if h.isConstOf ``Sparkle.Core.Signal.Signal.ap then
                let xargs := x.getAppArgs
                if xargs.size ≥ 2 then
                  let fpos ← normSpine xargs[xargs.size - 2]! fuel
                  -- `Seq.seq` supplies its operand through a `Unit` thunk;
                  -- expose it here (`handleApplicative` used to `headBeta`
                  -- it at the use site), so the operand a later arm receives
                  -- is the operand itself and not a beta-redex.
                  return Lean.mkAppN h
                    ((xargs.set! (xargs.size - 2) fpos).set! (xargs.size - 1)
                      xargs.back!.headBeta)
                else return x
              else return x
          let e' ← CompilerM.liftMetaM (normSpine e 32)
          if e' != e then
            return ← translateExprToWire e' hint (isNamed := isNamed)

      -- handleCircuitMonad must run before handleTupleProjections /
      -- handleDefinitionUnfold so that Bind.bind / Pure.pure get
      -- peeled, and value-level Prod.fst / Prod.snd / Prod.mk on
      -- Circuit-produced pairs reach our specialised path before
      -- the default unfold tries (and fails) to translate them.
      if let some w ← profHandler 1 (handleCircuitMonad e name args hint isNamed) then return w
      if let some w ← profHandler 2 (handleTupleProjections e name args hint isNamed) then return w
      if let some w ← profHandler 3 (handleApplicative e name args hint isNamed) then return w
      if let some w ← profHandler 4 (handleBitVecOps e name args hint isNamed) then return w
      if let some w ← profHandler 5 (handleRegister e name args hint isNamed) then return w
      if let some w ← profHandler 6 (handleMux e name args hint isNamed) then return w
      if let some w ← profHandler 7 (handleMemory e name args hint isNamed) then return w
      if let some w ← profHandler 8 (handleLoop e name args hint isNamed) then return w
      if let some w ← profHandler 9 (handleDefinitionUnfold e name args hint isNamed) then return w
      -- Not a valid module - throw error with debug info
      CompilerM.liftMetaM $ do
        if name.toString.contains "ite" || name.toString.contains "Decidable" then
          throwError s!"Detected problematic pattern {name}.\n\n\
            This might be from if-then-else which cannot be synthesized.\n\
            Use Signal.mux instead:\n\
            ❌ WRONG: if cond then a else b\n\
            ✓ RIGHT:  Signal.mux cond a b"
        else
          throwError s!"Cannot instantiate {name}: not a hardware module definition"

    | _ =>
      let fn := e.getAppFn
      CompilerM.liftMetaM $ throwError s!"Unsupported application: {e}\nHead: {fn} (ctor: {fn.ctorName})"

  /-- Translate a Nat shift amount argument to a hardware wire.
      Unwraps BitVec.toNat / Fin.val if the Nat came from a BitVec signal,
      otherwise treats it as a constant shift amount. -/
  partial def translateShiftAmount (bvExpr natExpr : Lean.Expr) (hint : String) : CompilerM String := do
    -- Preserve the BitVec source before whnf expands toNat into Fin.val.
    if natExpr.isAppOf ``BitVec.toNat && natExpr.getAppArgs.size >= 2 then
      return ← translateExprToWire natExpr.getAppArgs.back! hint
    let natExpr' ← CompilerM.liftMetaM (whnf natExpr)
    let natFn := natExpr'.getAppFn
    let natArgs := natExpr'.getAppArgs
    if let .const natName _ := natFn then
      if natName == ``BitVec.toNat && natArgs.size >= 2 then
        return ← translateExprToWire natArgs[natArgs.size - 1]! hint
      if natName == ``Fin.val && natArgs.size >= 2 then
        return ← translateExprToWire natArgs[natArgs.size - 1]! hint
    -- Fallback: treat as a constant shift amount
    let n ← extractNat natExpr'
    let exprType ← CompilerM.liftMetaM (Lean.Meta.inferType bvExpr)
    let bvHwType ← inferHWTypeFromSignal exprType
    let width := match bvHwType with | .bitVector w => w | .bit => 1 | _ => 32
    let constWire ← CompilerM.makeWire "shift_const" (.bitVector width)
    CompilerM.emitAssign constWire (.const (Int.ofNat n) width)
    return constWire

  partial def getPrimitiveNameFromLambda (e : Lean.Expr) : CompilerM Name := do
    match e with
    | .lam _ _ body _ => getPrimitiveNameFromLambda body
    | _ =>
      let fn := e.getAppFn
      match fn with
      | .const name _ => return name
      | _ => CompilerM.liftMetaM $ throwError s!"Could not identify primitive in lambda body: {e}"

  partial def synthesizeCombinational (declName : Name) :
      MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
    -- a child synthesised earlier in this top-level synthesis
    if let some r := (← sparkleChildCache.get).get? declName then return r
    let r ← synthesizeCombinationalWith (fun e h t n => translateExprToWire e h t n) declName
    sparkleChildCache.modify (·.insert declName r)
    return r

  partial def synthesizeCombinationalWithParameters (declName : Name)
      (parameters : List (String × Nat)) :
      MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
    let (m, d) ← synthesizeCombinationalCoreWith (fun e h t n => translateExprToWire e h t n)
      declName parameters true
    let m := Sparkle.IR.ZeroWidth.dropZeroWidthModule m
    let d := Sparkle.IR.ZeroWidth.dropZeroWidthDesign d
    if (← IO.getEnv "SPARKLE_NO_REGDEDUP").isSome then return (m, d)
    return (Sparkle.IR.RefineCheck.mergeChecked m,
      Sparkle.IR.RefineCheck.mergeCheckedDesign d)
end
end Rec
end TranslatorBlock


/-- A hit of the `IO.Ref` expression cache, accepted only if the pure record says
    the wire was produced for a structurally identical expression. -/
def cacheLookupValidated (e : Lean.Expr) : CompilerM (Option String) := do
  match (← CompilerM.getCompilerState).exprCache with
  | none => pure none
  | some ref =>
    let hit ← CompilerM.liftMetaM (do return (← (ref.get : IO _)).get? ⟨e⟩)
    match hit with
    | none => pure none
    | some w =>
      let s ← get
      match s.translateRecord.get? w with
      | some e' => pure (if @decide (e' = e) (Sparkle.Compiler.ExprDecEq.exprDecEq e' e) then some w else none)
      | none => pure none

/-- Record a core result (always), and insert it into the `IO.Ref` cache when the
    call is cacheable — exactly as the old caching wrapper did. -/
def recordTranslation (e : Lean.Expr) (w : String) (cacheable : Bool) : CompilerM Unit := do
  -- `modify`, not `get`/`set`: holding `s` while inserting would share the map
  -- and force a full copy per insert (O(n²) overall).
  modify fun s => { s with translateRecord := s.translateRecord.insert w e }
  if cacheable then
    if let some ref := (← CompilerM.getCompilerState).exprCache then
      CompilerM.liftMetaM (ref.modify (·.insert ⟨e⟩ w))

/-- Bool library controls whose fallback translations use the validated cache.
    Exact applications only: unrelated names and other forms keep their existing path. -/
def isBoolControl : Lean.Expr → Bool
  | .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.pure _) _)
      (.const ``Bool _)) _ => true
  | .app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.ult _) _) _) _) _ => true
  | .app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.ule _) _) _) _) _ => true
  | .app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.slt _) _) _) _) _ => true
  | .app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.sle _) _) _) _) _ => true
  | .app (.app (.app (.app (.app (.app (.const m _) _) _) _) inst) _) _ =>
      (signalBoolBinKind? m inst).isSome
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.beq _) ty) _) inst) _) _ =>
      isBoolEquality ty inst || (bitVecEqualityWidth? ty inst).isSome
  | .app (.app (.app (.const ``Complement.complement _) _)
      (.app (.const ``Sparkle.Core.Signal.instComplementSignalBool _) _)) _ => true
  | e => (appBoolOp? e).isSome ||
      (match canonicalMuxType? e with | some .bit => true | _ => false)

/-- The cache wrapper for Bool controls, exposed for simulation proofs. A miss
    calls the uncached handler and records its result before returning it. -/
def translateControlCachedWith (lower : TranslateFn) : TranslateFn :=
  fun e hint top named => do
    let cacheable := !named && !e.isFVar && !top
    if cacheable then
      if let some w ← cacheLookupValidated e then return w
    let w ← lower e hint top named
    recordTranslation e w cacheable
    return w

/-- Exact library comparisons have Bool results without type inference. -/
def signalCompareOp : SignalCompareKind → Operator
  | .ult => .lt_u
  | .ule => .le_u
  | .slt => .lt_s
  | .sle => .le_s
  | .eq => .eq

def emitBoolResult (rhs : Sparkle.IR.AST.Expr) (hint : String) (named : Bool) : CompilerM String := do
  let w ← CompilerM.makeWire hint .bit (named := named)
  CompilerM.emitAssign w rhs
  return w

def emitCompareResult (le : SignalCompareKind) (a b hint : String) (named : Bool) : CompilerM String :=
  emitBoolResult (.op (signalCompareOp le) [.ref a, .ref b]) hint named

def emitBoolLiteral (value : Bool) (hint : String) (named : Bool) : CompilerM String :=
  emitBoolResult (.const (if value then 1 else 0) 1) hint named

def translateBoolBinary (rec : TranslateFn) (kind : SignalBoolBinKind) (a b : Lean.Expr)
    (hint : String) (named : Bool) : CompilerM String := do
  let aw ← rec a "a" false false
  let bw ← rec b "b" false false
  emitBoolResult (.op (signalBoolBinOp kind) [.ref aw, .ref bw]) hint named

/-- Recursive comparison lowering, exposed to proofs. The child order and
    hints match the applicative lowering used before this direct route. -/
def translateSignalCompare (rec : TranslateFn) (le : SignalCompareKind) (a b : Lean.Expr)
    (hint : String) (named : Bool) : CompilerM String := do
  let aw ← rec a "a" false false
  let bw ← rec b "b" false false
  emitCompareResult le aw bw hint named

/-- Applicative-lifted comparison: both operands under the legacy applicative
    lowering's hint, then the comparison assignment of the direct route. -/
def translateAppCompare (rec : TranslateFn) (le : SignalCompareKind) (a b : Lean.Expr)
    (hint : String) (named : Bool) : CompilerM String := do
  let aw ← rec a "app_arg" false false
  let bw ← rec b "app_arg" false false
  emitCompareResult le aw bw hint named

/-- Applicative-lifted Bool operator, likewise. -/
def translateAppBoolBinary (rec : TranslateFn) (kind : SignalBoolBinKind) (a b : Lean.Expr)
    (hint : String) (named : Bool) : CompilerM String := do
  let aw ← rec a "app_arg" false false
  let bw ← rec b "app_arg" false false
  emitBoolResult (.op (signalBoolBinOp kind) [.ref aw, .ref bw]) hint named

/-- The inner assignment of a two-level Bool body, on the operand wires. -/
def appBool2Inner : AppBool2 → String → String → Sparkle.IR.AST.Expr
  | .andNot, _, b => .op .not [.ref b]
  | .notAnd, a, _ => .op .not [.ref a]
  | .nor, a, b => .op .or [.ref a, .ref b]

/-- The hint the legacy lowering gives the inner wire: the position of the
    inner application among the outer operator's arguments. -/
def appBool2Hint : AppBool2 → String
  | .andNot => "arg2"
  | .notAnd => "arg1"
  | .nor => "arg1"

/-- The result assignment, on the operand wires and the inner wire. -/
def appBool2Outer : AppBool2 → String → String → String → Sparkle.IR.AST.Expr
  | .andNot, a, _, n => .op .and [.ref a, .ref n]
  | .notAnd, _, b, n => .op .and [.ref n, .ref b]
  | .nor, _, _, n => .op .not [.ref n]

/-- Applicative-lifted two-level Bool body: the operands under the legacy
    applicative hint, the inner application on a wire of its own, then the
    result. -/
def translateAppBool2 (rec : TranslateFn) (f : AppBool2) (a b : Lean.Expr)
    (hint : String) (named : Bool) : CompilerM String := do
  let aw ← rec a "app_arg" false false
  let bw ← rec b "app_arg" false false
  let n ← emitBoolResult (appBool2Inner f aw bw) (appBool2Hint f) false
  emitBoolResult (appBool2Outer f aw bw n) hint named

def translateAppBool (rec : TranslateFn) (op : AppBoolOp) (a b : Lean.Expr)
    (hint : String) (named : Bool) : CompilerM String :=
  match op with
  | .compare k _ => translateAppCompare rec k a b hint named
  | .bool k => translateAppBoolBinary rec k a b hint named
  | .two f => translateAppBool2 rec f a b hint named

/-- Canonical literals, comparisons and Bool muxes use total lowering. Other Bool forms
    still use their existing handlers on a validated-cache miss. -/
def translateBoolUncachedWith (rec legacy : TranslateFn) : TranslateFn :=
  fun e hint top named =>
    match e with
    | .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.pure _) _) (.const ``Bool _))
        (.const ``Bool.true _) => emitBoolLiteral true hint named
    | .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.pure _) _) (.const ``Bool _))
        (.const ``Bool.false _) => emitBoolLiteral false hint named
    | .app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.ult _) _) _) a) b =>
      translateSignalCompare rec false a b hint named
    | .app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.ule _) _) _) a) b =>
      translateSignalCompare rec true a b hint named
    | .app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.slt _) _) _) a) b =>
      translateSignalCompare rec .slt a b hint named
    | .app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.sle _) _) _) a) b =>
      translateSignalCompare rec .sle a b hint named
    | .app (.app (.app (.app (.app (.app (.const m _) _) _) _) inst) a) b =>
      match signalBoolBinKind? m inst with
      | some kind => translateBoolBinary rec kind a b hint named
      | none => legacy e hint top named
    | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.beq _) ty) _) inst) a) b =>
      if isBoolEquality ty inst then translateSignalCompare rec .eq a b hint named else
      match bitVecEqualityWidth? ty inst with
      | some _ => translateSignalCompare rec .eq a b hint named
      | none => legacy e hint top named
    | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.mux _) _)
        (.const ``Bool _)) c) a) b =>
      translateMuxWith rec (pure .bit) c a b hint named
    | .app (.app (.app (.const ``Complement.complement _) _)
        (.app (.const ``Sparkle.Core.Signal.instComplementSignalBool _) dom)) a =>
      -- A one-bit equality with false is Boolean negation. Reuse the proved
      -- comparison pipeline, including its recursive constant allocation.
      translateSignalCompare rec .eq a
        (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom
          (.const ``Bool []) (.const ``Bool.false [])) hint named
    | e =>
      match appBoolOp? e with
      | some (op, a, b) => translateAppBool rec op a b hint named
      | none => legacy e hint top named

/-- The shapes `translateCore` handles (decides whether the validated lookup is
    tried before the core). -/
def translateCoreShape (e : Lean.Expr) : Bool :=
  match e.getAppFn with
  | .const m _ =>
    m == ``Sparkle.Core.Signal.Signal.pure ||
      (match signalBinOpOf m, canonicalSignalBinKinds m e.getAppArgs,
          canonicalSignalBitVecWidth e.getAppArgs with
       | some _, some (true, true), some _ => true
       | _, _, _ => false)
  | _ => false

/-- The shapes the proved core handles, tried before the `partial` fallback:
    an `fvar` bound by `lookupVar`, `Signal.pure` of a `BitVec` literal, and a
    canonical library Signal operator (both operands Signal, literal width).
    `none` means "not a core shape"; it never fails for those shapes. -/
def translateCore (translate : TranslateFn) (e : Lean.Expr) (hint : String)
    (_isTopLevel isNamed : Bool) : CompilerM (Option String) :=
  match e with
  | .fvar id => CompilerM.lookupVar id
  | _ =>
    match e.getAppFn with
    | .const m _ =>
      if m == ``Sparkle.Core.Signal.Signal.pure then
        translateSignalPureLiteral? e.getAppArgs hint isNamed
      else
        match signalBinOpOf m, canonicalSignalBinKinds m e.getAppArgs,
            canonicalSignalBitVecWidth e.getAppArgs with
        | some op, some (true, true), some _ => do
          let w ← translateCanonicalSignalBinary translate e op e.getAppArgs true true hint isNamed
          pure (some w)
        | _, _, _ => pure none
    | _ => pure none

/-- One step of the knot: the core, else `fallback` (given the same `rec`). -/
def translateStepWith (fallback : TranslateFn → TranslateFn) (rec : TranslateFn) : TranslateFn :=
  fun e hint top named => do
    let cacheable := !named && !e.isFVar && !top
    if cacheable && translateCoreShape e then
      if let some w ← cacheLookupValidated e then
        return w
    match ← translateCore rec e hint top named with
    | some w =>
      -- An `fvar` result is an EXISTING wire (the variable's binding), not one
      -- produced for `e`; recording it would overwrite what the wire was made
      -- for. `fvar`s are never cache keys (the old wrapper excluded them too).
      unless e.isFVar do recordTranslation e w cacheable
      pure w
    | none => fallback rec e hint top named

/-- A fuel-bounded fixpoint of a non-recursive step. Fuel exhaustion is a
    compile error, like the `SPARKLE_TRANSLATE_LIMIT` backstop. -/
def translateFuelFix (step : TranslateFn → TranslateFn) : Nat → TranslateFn
  | 0 => fun _ _ _ _ => throw (Exception.error .missing "translation fuel exhausted")
  | k + 1 => step (translateFuelFix step k)

/-- Uncached lowering for a canonical literal-width vector mux node. Exposed
    as a `TranslateFn` so the shared validated-cache wrapper applies to it. -/
def translateVectorMuxUncachedWith (rec : TranslateFn) (n : Nat) : TranslateFn :=
  fun e hint _top named =>
    translateMuxWith rec (pure (.bitVector n)) e.getAppArgs[e.getAppArgs.size - 3]!
      e.getAppArgs[e.getAppArgs.size - 2]! e.getAppArgs.back! hint named

/-- The width-cast right-hand side: a zero-extension concat, the canonical
    size-cast slice, or a plain alias at equal widths. -/
def setwRhs (ws wt : Nat) (sw : String) : Sparkle.IR.AST.Expr :=
  if ws < wt then .concat [.const 0 (wt - ws), .ref sw]
  else if wt < ws then .slice (.concat [.const 0 wt, .ref sw]) (wt - 1) 0
  else .ref sw

/-- Allocate the target-width result wire and assign one cast expression. -/
def emitCastResult (rhs : Sparkle.IR.AST.Expr) (wt : Nat) (hint : String)
    (named : Bool) : CompilerM String := do
  let r ← CompilerM.makeWire hint (.bitVector wt) (named := named)
  CompilerM.emitAssign r rhs
  return r

/-- Uncached lowering for the canonical width-changing map node: the child
    first, then one width-cast assignment. -/
def translateSetWidthUncachedWith (rec : TranslateFn) (ws wt : Nat) : TranslateFn :=
  fun e hint _top named => do
    let sw ← rec e.getAppArgs.back! "s" false false
    emitCastResult (setwRhs ws wt sw) wt hint named

/-- The part-select right-hand side of a slice: bits `start + len - 1 … start`
    of the child wire. -/
def sliceRhs (start len : Nat) (sw : String) : Sparkle.IR.AST.Expr :=
  .slice (.ref sw) (start + len - 1) start

/-- Allocate the slice's result wire — a scalar `logic` for one bit, as the
    legacy lowering declares it — and assign the part-select. -/
def emitSliceResult (rhs : Sparkle.IR.AST.Expr) (len : Nat) (hint : String)
    (named : Bool) : CompilerM String := do
  let r ← CompilerM.makeWire hint (hwTypeFromWidth len) (named := named)
  CompilerM.emitAssign r rhs
  return r

/-- Uncached lowering for the canonical slice map: the child first, then one
    part-select assignment. -/
def translateSliceUncachedWith (rec : TranslateFn) (start len : Nat) : TranslateFn :=
  fun e hint _top named => do
    let sw ← rec e.getAppArgs.back! "s" false false
    emitSliceResult (sliceRhs start len sw) len hint named

/-- The concatenation sequence of the legacy handler: the result wire FIRST,
    then the high and the low operand, then one `{hi, lo}` assignment.  The
    operand lowerings are actions: a recursive translation, or the constant
    wire of a literal operand. -/
def translateConcatActs (w : Nat) (hiAct loAct : CompilerM String) (hint : String)
    (named : Bool) : CompilerM String := do
  let r ← CompilerM.makeWire hint (.bitVector w) (named := named)
  let hi ← hiAct
  let lo ← loAct
  CompilerM.emitAssign r (.concat [.ref hi, .ref lo])
  return r

/-- Both operands Signals: each lowered under its legacy hint. -/
def translateConcatWith (rec : TranslateFn) (m n : Nat) (a b : Lean.Expr) (hint : String)
    (named : Bool) : CompilerM String :=
  translateConcatActs (m + n) (rec a "concat_hi" false false) (rec b "concat_lo" false false)
    hint named

/-- The constant wire of a literal operand, as the legacy mixed handler
    emits it: a fresh `concat_const` wire assigned the literal. -/
def emitConcatConst (k v : Nat) : CompilerM String :=
  emitCastResult (.const (Int.ofNat v) k) k "concat_const" false

/-- Uncached lowering for a concatenation with a literal operand: the
    result wire first, then the operands in source order — the constant
    wire in the literal's place. -/
def translateConcatLitUncachedWith (rec : TranslateFn) (hi : Bool) (k v w : Nat) : TranslateFn :=
  fun e hint _top named =>
    if hi then
      translateConcatActs (k + w) (emitConcatConst k v)
        (rec e.getAppArgs.back! "concat_lo" false false) hint named
    else
      translateConcatActs (w + k)
        (rec e.getAppArgs[e.getAppArgs.size - 2]! "concat_hi" false false)
        (emitConcatConst k v) hint named

/-- Uncached lowering for the canonical concatenation. -/
def translateConcatUncachedWith (rec : TranslateFn) (m n : Nat) : TranslateFn :=
  fun e hint _top named =>
    translateConcatWith rec m n e.getAppArgs[e.getAppArgs.size - 2]! e.getAppArgs.back!
      hint named

/-- Uncached lowering for the `<$>` slice: as the slice map, under the
    legacy `Functor.map` handler's child hint. -/
def translateSliceFUncachedWith (rec : TranslateFn) (start len : Nat) : TranslateFn :=
  fun e hint _top named => do
    let sw ← rec e.getAppArgs.back! "a" false false
    emitSliceResult (sliceRhs start len sw) len hint named

/-- Uncached lowering for the canonical polymorphic-domain register: the
    input first, then one register statement on the shared clock/reset
    names. The asynchronous kind matches the legacy handler's fallback for
    a polymorphic domain; the step semantics samples reset per cycle for
    either kind. -/
def translateRegisterUncachedWith (rec : TranslateFn) (w v : Nat) : TranslateFn :=
  fun e hint _top named => do
    let cw ← rec e.getAppArgs.back! "reg_in" false false
    CompilerM.emitRegister hint "clk" "rst" (.ref cw) v (.bitVector w) (named := named)

/-- Uncached lowering for the canonical feedback register: allocate the
    register output wire FIRST, bind the loop binder to it (guarded against
    a source-binder collision), translate the cone — which may read the
    register back — then add the register statement. -/
def translateLoopRegisterUncachedWith (rec : TranslateFn) (w v : Nat) : TranslateFn :=
  fun e hint _top named => do
    let cone := match e.getAppArgs.back! with
      | .lam _ _ (.app _ inner) _ => inner
      | f => f
    let selfId ← CompilerM.liftMetaM Lean.mkFreshFVarId
    if (← CompilerM.lookupVar selfId).isSome then
      throw (Exception.error .missing "loop binder id collision")
    let r ← CompilerM.makeWire hint (.bitVector w) (named := named)
    CompilerM.bindSourceVariable selfId r
    let cw ← rec (instFVars #[.fvar selfId] 0 cone) "loop_body" false false
    CompilerM.emitRegisterStmt r "clk" "rst" (.ref cw) v
    return r

/-- Uncached lowering for the canonical polymorphic-domain enabled register,
    in the legacy handler's exact order: both children, the hold mux wire,
    the register fed by the mux, then the mux assignment reading the register
    output back (the hold path). -/
def translateRegisterEnableUncachedWith (rec : TranslateFn) (w v : Nat) : TranslateFn :=
  fun e hint _top named => do
    let enW ← rec e.getAppArgs[e.getAppArgs.size - 2]! "reg_en" false false
    let inW ← rec e.getAppArgs.back! "reg_input" false false
    let muxW ← CompilerM.makeWire (hint ++ "_mux") (.bitVector w)
    let r ← CompilerM.emitRegister hint "clk" "rst" (.ref muxW) v (.bitVector w)
      (named := named)
    CompilerM.emitAssign muxW (.op .mux [.ref enW, .ref inW, .ref r])
    return r

/-- Uncached lowering for the canonical sync-read memory, in the legacy
    handler's exact order: the four operand wires, the module-body dedupe
    scan, then one `.memory` statement whose read latches into the fresh
    `rdata` wire. -/
def translateMemoryUncachedWith (rec : TranslateFn) (aw dw : Nat) : TranslateFn :=
  fun e hint _top named =>
    match e with
    | .app (.app (.app (.app (.app (.app (.app _ _) _) _) wa) wd) wen) ra => do
      let waW ← rec wa "mem_waddr" false false
      let wdW ← rec wd "mem_wdata" false false
      let weW ← rec wen "mem_we" false false
      let raW ← rec ra "mem_raddr" false false
      -- No module-body dedupe scan here: the certified root is a single
      -- output leaf, so the same memory is never re-translated within one
      -- synthesis (the legacy handler's scan exists for multi-leaf splits),
      -- and the validated cache wrapper already dedupes identical sources.
      CompilerM.emitMemory hint aw dw "clk" (.ref waW) (.ref wdW) (.ref weW)
        (.ref raW) (named := named)
    | _ => throw (Exception.error .missing "memory shape departed after the gate")

/-- Uncached lowering for the canonical single-slot `circuit do`: identical
    to the feedback-register lowering, with the cone taken from the
    recognizer's loop-form rewrite. -/
def translateCircuitDoUncachedWith (rec : TranslateFn) (w v : Nat) : TranslateFn :=
  fun e hint _top named => do
    let cone := match canonicalCircuitDo? e with
      | some (_, _, c) => c
      | none => e
    let selfId ← CompilerM.liftMetaM Lean.mkFreshFVarId
    if (← CompilerM.lookupVar selfId).isSome then
      throw (Exception.error .missing "circuit-do binder id collision")
    let r ← CompilerM.makeWire hint (.bitVector w) (named := named)
    CompilerM.bindSourceVariable selfId r
    let cw ← rec (instFVars #[.fvar selfId] 0 cone) "loop_body" false false
    CompilerM.emitRegisterStmt r "clk" "rst" (.ref cw) v
    return r

/-- Uncached lowering for the canonical two-slot `circuit do`: both register
    wires are allocated and bound before either cone translates (each cone
    may read both registers), then each register statement is emitted after
    its cone; the returned slot's wire is the result. -/
def translateCircuitDo2UncachedWith (rec : TranslateFn) (w v0 v1 ret : Nat) : TranslateFn :=
  fun e hint _top named => do
    let (cone0, cone1) := match canonicalCircuitDo2? e with
      | some (_, _, _, _, c0, c1) => (c0, c1)
      | none => (e, e)
    let self0 ← CompilerM.liftMetaM Lean.mkFreshFVarId
    let self1 ← CompilerM.liftMetaM Lean.mkFreshFVarId
    -- Fresh ids are distinct in practice; the guard makes it a proof fact.
    if self0 = self1 then
      throw (Exception.error .missing "circuit-do slot binder ids collide")
    if (← CompilerM.lookupVar self0).isSome then
      throw (Exception.error .missing "circuit-do slot-0 binder id collision")
    if (← CompilerM.lookupVar self1).isSome then
      throw (Exception.error .missing "circuit-do slot-1 binder id collision")
    let r0 ← CompilerM.makeWire hint (.bitVector w) (named := named && ret == 0)
    let r1 ← CompilerM.makeWire (hint ++ "_slot1") (.bitVector w) (named := named && ret == 1)
    CompilerM.bindSourceVariable self0 r0
    CompilerM.bindSourceVariable self1 r1
    -- Both cones translate BEFORE either register statement is emitted:
    -- the combinational contract machinery covers one assign-only segment,
    -- and the registers land after it (register order is semantically
    -- irrelevant — updates read the post-assignment environment).
    let cw0 ← rec (instFVars #[.fvar self0, .fvar self1] 0 cone0) "loop_body" false false
    let cw1 ← rec (instFVars #[.fvar self0, .fvar self1] 0 cone1) "loop_body" false false
    CompilerM.emitRegisterStmt r0 "clk" "rst" (.ref cw0) v0
    CompilerM.emitRegisterStmt r1 "clk" "rst" (.ref cw1) v1
    return (if ret == 0 then r0 else r1)

/-- The environment read the instance arm dispatches on. A named entry so
    the soundness layer can state its boundary predicate against exactly
    this action. -/
def instArmEnv : MetaM Environment := Lean.getEnv

/-- The single-out instance dedupe cache read, as a named MetaM entry for
    the same reason (the ref itself is private to this module). -/
def instArmCacheGet : MetaM (Std.HashMap String String) :=
  sparkleSingleOutInstanceCache.get

/-- The matching insert. -/
def instArmCachePut (key w : String) : MetaM Unit :=
  sparkleSingleOutInstanceCache.modify (·.insert key w)

/-- The multi-output instance port map read, as a named MetaM entry. -/
def instArmOutGet : MetaM (Std.HashMap (UInt64 × String) String) :=
  sparkleSubInstanceOutputs.get

/-- The matching insert: output port `out` of the call keyed `key` is wire `w`. -/
def instArmOutPut (key : UInt64) (out w : String) : MetaM Unit :=
  sparkleSubInstanceOutputs.modify (·.insert (key, out) w)

/-- The field name a structure projection selects, exactly as the legacy
    projection handler resolves it (projection info, the structure's
    constructor, the constructor's field binders). `none` when the name is
    not a resolvable projection of `structName`. -/
def projFieldName? (name structName : Name) : MetaM (Option String) := do
  let env ← getEnv
  let some projInfo := env.getProjectionFnInfo? name | return none
  let some indVal ← (try some <$> getConstInfoInduct structName catch _ => pure none)
    | return none
  let ctorName := indVal.ctors.head!
  let ctorInfo ← getConstInfoCtor ctorName
  let fieldName ← Lean.Meta.forallTelescopeReducing ctorInfo.type fun fargs _ => do
    let allFields := fargs.toList.drop indVal.numParams
    if h : projInfo.i < allFields.length then
      return (← allFields[projInfo.i].fvarId!.getUserName).toString
    else
      return s!"field{projInfo.i}"
  return some fieldName

/-- Register the child's transitive modules, skipping names already present
    (two calls to one sub-module produce ONE definition). Structural
    recursion, so the certified decomposition unfolds it definitionally. -/
def instAddModules (existing : List String) : List Sparkle.IR.AST.Module → CompilerM Unit
  | [] => pure ()
  | m :: ms => do
    if !existing.contains m.name then
      CompilerM.addModuleToDesign m
    instAddModules existing ms

/-- Wire the child's clk/rst ports to the parent's, adding the parent port
    when missing, in the legacy handler's order (prepending onto `acc`). -/
def instClkRst (acc : List (String × Sparkle.IR.AST.Expr)) :
    List Port → CompilerM (List (String × Sparkle.IR.AST.Expr))
  | [] => pure acc
  | p :: ps => do
    if p.name == "clk" || p.name == "rst" then
      let parent := (← get).module
      if !parent.inputs.any (·.name == p.name) then
        CompilerM.addInput p.name p.ty
      else
        pure ()
      instClkRst ((p.name, Sparkle.IR.AST.Expr.ref p.name) :: acc) ps
    else
      instClkRst acc ps

/-- Translate the argument operands against the child's input ports, in the
    legacy handler's order and with its `arg{i}` hints. -/
def instArgs (rec : TranslateFn) (acc : List (String × Sparkle.IR.AST.Expr)) :
    List (Port × Lean.Expr) → Nat → CompilerM (List (String × Sparkle.IR.AST.Expr))
  | [], _ => pure acc
  | (p, a) :: rest, i => do
    let argWire ← rec a s!"arg{i}" false false
    instArgs rec ((p.name, Sparkle.IR.AST.Expr.ref argWire) :: acc) rest (i + 1)

/-- The argument list of an application spine, left to right — the same
    list as `Expr.getAppArgs`, by structural recursion so the certified
    decomposition can induct over arbitrary arities. -/
def instSpineArgs : Lean.Expr → List Lean.Expr
  | .app f a => instSpineArgs f ++ [a]
  | _ => []

/-- Register the child itself unless a module of that name is already in the
    design (`existing` is the pre-walk snapshot, matching the legacy order). -/
def instRegisterChild (existing : List String)
    (subModule : Sparkle.IR.AST.Module) : CompilerM Unit := do
  let csNow ← get
  if !existing.contains subModule.name &&
      !(csNow.design.modules.any (·.name == subModule.name)) then
    CompilerM.addModuleToDesign subModule
  else
    pure ()

/-- The legacy arity guard, hoisted so the parent walk stays join-point free. -/
def instArityCheck (mn : Name) (need got : Nat) : CompilerM Unit :=
  if got < need then
    throw (Exception.error .missing
      s!"Sub-module {mn} requires {need} args, but got {got}")
  else
    pure ()

/-- A single-out cache hit is honoured only when the builder's own record
    says the cached wire was produced for THIS expression (the same check
    `cacheLookupValidated` applies to the expression cache). Every lowering
    through the arm records its result wire, so a repeat of the same call
    always validates; the check turns the reuse into a fact about the
    builder state instead of a fact about the mutable cache. -/
def instHitValid (record : Std.HashMap String Lean.Expr) (e : Lean.Expr)
    (cw : String) : Bool :=
  match record.get? cw with
  | some e' => @decide (e' = e) (Sparkle.Compiler.ExprDecEq.exprDecEq e' e)
  | none => false

/-- Uncached lowering for a single-output `@[hardware_module]` instance whose
    child compile is already in hand, in the legacy handler's exact order:
    register the child's transitive modules and the child (name-deduped),
    plumb clk/rst (adding parent ports when missing), translate the argument
    operands, consult the per-synth single-out instance dedupe cache, then
    allocate the result wire and emit one `.inst` statement. The result-wire
    type is the child's own single output port type (the legacy handler
    re-infers it from the call's Signal type; they agree on every scalar
    child, which the hierarchy test pins byte-for-byte). -/
def translateInstanceUncachedWith (rec : TranslateFn) (mn : Name)
    (subModule : Sparkle.IR.AST.Module) (subDesign : Sparkle.IR.AST.Design)
    (singleOut : Port) : TranslateFn :=
  fun e hint _top named => do
    let cs0 ← get
    let existing := cs0.design.modules.map (·.name)
    instAddModules existing subDesign.modules
    instRegisterChild existing subModule
    let connections0 ← instClkRst [] subModule.inputs
    let inputPorts := subModule.inputs.filter (fun p => p.name != "clk" && p.name != "rst")
    let args := instSpineArgs e
    instArityCheck mn inputPorts.length args.length
    let connections ← instArgs rec connections0
      (inputPorts.zip (args.drop (args.length - inputPorts.length))) 0
    let parentName := (← get).module.name
    let connKey := String.intercalate ";"
      (connections.reverse.map (fun (p, rhs) => s!"{p}={rhs}"))
    let instKey := s!"{parentName}#{subModule.name}#{connKey}"
    let instCache ← CompilerM.liftMetaM instArmCacheGet
    -- Validated against the record as it stood when this call started: a
    -- wire recorded for this very call cannot be produced by its operands.
    if let some cachedW := (instCache.get? instKey).filter
        (instHitValid cs0.translateRecord e) then
      return cachedW
    let w ← CompilerM.makeWire hint singleOut.ty (named := named)
    CompilerM.liftMetaM (instArmCachePut instKey w)
    let connectionsF := (singleOut.name, Sparkle.IR.AST.Expr.ref w) :: connections
    let instName ← CompilerM.freshName s!"inst_{subModule.name}"
    instLinkCheck mn subModule connectionsF.reverse
    CompilerM.emitInstance subModule.name instName connectionsF.reverse
    return w

/-- Allocate one result wire per child output port, in port order, recording
    each in the multi-output port map (the legacy handler's exact order:
    wire, connection, map entry). Returns the extended connection list and
    the output-name ↦ wire association. -/
def instOutWires (callKey : UInt64) (hint : String) :
    List Port → List (String × Sparkle.IR.AST.Expr) → List (String × String) →
    CompilerM (List (String × Sparkle.IR.AST.Expr) × List (String × String))
  | [], conns, ws => pure (conns, ws)
  | outP :: rest, conns, ws => do
    let w ← CompilerM.makeWire s!"{hint}_{outP.name}" outP.ty (named := false)
    CompilerM.liftMetaM (instArmOutPut callKey outP.name w)
    instOutWires callKey hint rest
      ((outP.name, Sparkle.IR.AST.Expr.ref w) :: conns) ((outP.name, w) :: ws)

/-- The canonical call key of a record-returning instance call. The
    canonicalizer only READS the builder state (variable bindings and the
    wire caches); restoring the saved state makes that a fact the certified
    decomposition can use without looking inside it. -/
def instCallKey (recordArg : Lean.Expr) : CompilerM UInt64 := do
  let s0 ← get
  let key ← canonHardwareKey recordArg
  set s0
  return hash key

/-- Uncached lowering for a projection `field (child args…)` of a
    MULTI-output `@[hardware_module]` call whose child compile is in hand,
    in the legacy handlers' exact order: consult the per-synth port map
    (a hit returns the recorded wire), otherwise register the child, plumb
    clk/rst, translate the argument operands, allocate one wire per output
    port, emit ONE `.inst` statement, and return the projected field's wire. -/
def translateProjInstanceUncachedWith (rec : TranslateFn) (recName : Name)
    (subModule : Sparkle.IR.AST.Module) (subDesign : Sparkle.IR.AST.Design)
    (fieldName : String) (recordArg : Lean.Expr)
    (legacy : TranslateFn) : TranslateFn :=
  fun e hint top named => do
    let callKey ← instCallKey recordArg
    let portMap ← CompilerM.liftMetaM instArmOutGet
    match portMap.get? (callKey, fieldName) with
    | some w => return w
    | none =>
    let alreadyEmitted := match subModule.outputs.head? with
      | some firstOutP => portMap.contains (callKey, firstOutP.name)
      | none => false
    if alreadyEmitted then
      legacy e hint top named
    else
    let existing := (← get).design.modules.map (·.name)
    instAddModules existing subDesign.modules
    instRegisterChild existing subModule
    let connections0 ← instClkRst [] subModule.inputs
    let inputPorts := subModule.inputs.filter (fun p => p.name != "clk" && p.name != "rst")
    let args := instSpineArgs recordArg
    instArityCheck recName inputPorts.length args.length
    let connections ← instArgs rec connections0
      (inputPorts.zip (args.drop (args.length - inputPorts.length))) 0
    let (connectionsF, outWires) ←
      instOutWires callKey "sub_call" subModule.outputs connections []
    let instName ← CompilerM.freshName s!"inst_{subModule.name}"
    instLinkCheck recName subModule connectionsF.reverse
    CompilerM.emitInstance subModule.name instName connectionsF.reverse
    match outWires.lookup fieldName with
    | some w => return w
    | none => throw (Exception.error .missing
        s!"Sub-module {recName} has no output port '{fieldName}'")

/-- The `@[hardware_module]` single-output instance arm at the end of the
    certified dispatch: a call whose head constant carries the tag
    synthesizes the child through the SAME entry the legacy handler uses
    (memoized per synth, so the probe is byte-invisible), and a
    single-output child takes the certified straight-line lowering under
    the shared validated cache wrapper. Untagged heads, non-applications
    and multi-output children fall through to the legacy chain unchanged. -/
def translateInstanceOrFallback (rec : TranslateFn) : TranslateFn :=
  fun e hint top named =>
    match e.getAppFn with
    | .const mn _ => do
      let env ← CompilerM.liftMetaM instArmEnv
      if Sparkle.Compiler.isHardwareModule env mn then
        let sub ← CompilerM.liftMetaM
          (Rec.synthesizeCombinational (fun e h t n => rec e h t n) mn)
        match sub.1.outputs with
        | [singleOut] =>
          translateControlCachedWith
            (translateInstanceUncachedWith rec mn sub.1 sub.2 singleOut)
            e hint top named
        | _ => Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint top named
      else
        -- A structure projection of a direct call to a tagged MULTI-output
        -- child: the provable projection arm (anything else stays legacy).
        match env.getProjectionStructureName? mn, (instSpineArgs e).getLast? with
        | some structName, some recordArg =>
          match recordArg.getAppFn with
          | .const recName _ =>
            if Sparkle.Compiler.isHardwareModule env recName then do
              match ← CompilerM.liftMetaM (projFieldName? mn structName) with
              | some fieldName =>
                let sub ← CompilerM.liftMetaM
                  (Rec.synthesizeCombinational (fun e h t n => rec e h t n) recName)
                if decide (2 ≤ sub.1.outputs.length) &&
                    sub.1.outputs.any (fun p => p.name == fieldName) then
                  translateControlCachedWith
                    (translateProjInstanceUncachedWith rec recName sub.1 sub.2 fieldName
                      recordArg
                      (fun e h t n =>
                        Rec.translateExprToWireCached (fun e h t n => rec e h t n) e h t n))
                    e hint top named
                else
                  Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint top named
              | none =>
                Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint top named
            else
              Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint top named
          | _ => Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint top named
        | _, _ => Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint top named
    | _ => Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint top named

/-- The arm of the fallback chain an expression takes, as data.  The chain is
    ordered: a recogniser is consulted only when every earlier one declined.
    New arms are appended just before `other`, so a shape that leaves the
    chain at an existing arm is unaffected by them, and a shape that reaches
    the end is characterised by ONE fact, `fallbackKind e = .other`. -/
inductive FallbackKind where
  | boolControl
  | vectorMux (n : Nat)
  | setWidth (ws wt : Nat)
  | register (w v : Nat)
  | registerEnable (w v : Nat)
  | loopRegister (w v : Nat)
  | circuitDo (w v : Nat)
  | circuitDo2 (w v0 v1 ret : Nat)
  | memory (aw dw : Nat)
  | slice (ws start len : Nat)
  | concat (m n : Nat)
  | concatLit (hi : Bool) (k v w : Nat)
  | zextMap (ws k : Nat)
  | sliceF (ws start len : Nat)
  | other
  deriving DecidableEq, Repr

def fallbackKind (e : Lean.Expr) : FallbackKind :=
  if isBoolControl e then .boolControl
  else
    match canonicalMuxType? e with
    | some (.bitVector n) => .vectorMux n
    | _ =>
      match canonicalSetWidth? e with
      | some (ws, wt, _) => .setWidth ws wt
      | none =>
        match canonicalRegister? e with
        | some (w, v, _) => .register w v
        | none =>
          match canonicalRegisterEnable? e with
          | some (w, v, _, _) => .registerEnable w v
          | none =>
            match canonicalLoopRegister? e with
            | some (w, v, _) => .loopRegister w v
            | none =>
              match canonicalCircuitDo? e with
              | some (w, v, _) => .circuitDo w v
              | none =>
                match canonicalCircuitDo2? e with
                | some (w, v0, v1, ret, _, _) => .circuitDo2 w v0 v1 ret
                | none =>
                  match canonicalMemory? e with
                  | some (aw, dw) => .memory aw dw
                  | none =>
                    match canonicalSlice? e with
                    | some (ws, start, len, _) => .slice ws start len
                    | none =>
                      match canonicalConcat? e with
                      | some (m, n, _, _) => .concat m n
                      | none =>
                        match canonicalConcatLit? e with
                        | some (hi, k, v, w, _, _) => .concatLit hi k v w
                        | none =>
                          match canonicalZextMap? e with
                          | some (ws, k, _) => .zextMap ws k
                          | none =>
                            match canonicalSliceF? e with
                            | some (ws, start, len, _) => .sliceF ws start len
                            | none => .other

/-- The existing handler chain (cache wrapper + dispatch) as the fallback:
    one lowering per `fallbackKind`. -/
def translateFallback (rec : TranslateFn) : TranslateFn :=
  fun e hint top named =>
    match fallbackKind e with
    | .boolControl =>
      translateControlCachedWith
        (translateBoolUncachedWith rec
          (fun e h t n => Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e h t n))
        e hint top named
    | .vectorMux n =>
      -- Vector mux nodes share the validated cache wrapper: a hit is checked
      -- against the recorded expression, a miss lowers and records.
      translateControlCachedWith (translateVectorMuxUncachedWith rec n) e hint top named
    | .setWidth ws wt =>
      -- Canonical width-changing maps take the total certified lowering.
      translateControlCachedWith (translateSetWidthUncachedWith rec ws wt) e hint top named
    | .register w v =>
      -- Canonical polymorphic-domain registers take the total lowering;
      -- concrete domains keep the legacy handler and its inferred kind.
      translateControlCachedWith (translateRegisterUncachedWith rec w v) e hint top named
    | .registerEnable w v =>
      translateControlCachedWith (translateRegisterEnableUncachedWith rec w v) e hint top named
    | .loopRegister w v =>
      translateControlCachedWith (translateLoopRegisterUncachedWith rec w v) e hint top named
    | .circuitDo w v =>
      translateControlCachedWith (translateCircuitDoUncachedWith rec w v) e hint top named
    | .circuitDo2 w v0 v1 ret =>
      translateControlCachedWith (translateCircuitDo2UncachedWith rec w v0 v1 ret)
        e hint top named
    | .memory aw dw =>
      translateControlCachedWith (translateMemoryUncachedWith rec aw dw) e hint top named
    | .slice _ start len =>
      translateControlCachedWith (translateSliceUncachedWith rec start len) e hint top named
    | .concat m n =>
      translateControlCachedWith (translateConcatUncachedWith rec m n) e hint top named
    | .concatLit hi k v w =>
      translateControlCachedWith (translateConcatLitUncachedWith rec hi k v w) e hint top named
    | .zextMap ws k =>
      -- A literal zero prefix inside a map is the zero-extending width cast.
      translateControlCachedWith (translateSetWidthUncachedWith rec ws (k + ws)) e hint top named
    | .sliceF _ start len =>
      translateControlCachedWith (translateSliceFUncachedWith rec start len) e hint top named
    | .other => translateInstanceOrFallback rec e hint top named

def translateStep : TranslateFn → TranslateFn := translateStepWith translateFallback

/-- Nesting depth bound of the translator's recursion. -/
def translateFuelLimit : Nat := 1 <<< 20

/-- The shipping translator: an ORDINARY definition (not `partial`), so it has
    equations and can be reasoned about. -/
def translateExprToWire (e : Lean.Expr) (hint : String := "wire") (isTopLevel : Bool := false)
    (isNamed : Bool := false) : CompilerM String :=
  translateFuelFix translateStep translateFuelLimit e hint isTopLevel isNamed

/-- `Rec.translateExprToWireImpl` with the real translator as its recursive entry. -/
def translateExprToWireImpl := Rec.translateExprToWireImpl (fun e h t n => translateExprToWire e h t n)
/-- `Rec.handleErrorPatterns` with the real translator as its recursive entry. -/
def handleErrorPatterns := Rec.handleErrorPatterns (fun e h t n => translateExprToWire e h t n)
/-- `Rec.handleTupleProjections` with the real translator as its recursive entry. -/
def handleTupleProjections := Rec.handleTupleProjections (fun e h t n => translateExprToWire e h t n)
/-- `Rec.handleApplicative` with the real translator as its recursive entry. -/
def handleApplicative := Rec.handleApplicative (fun e h t n => translateExprToWire e h t n)
/-- `Rec.handleBitVecOps` with the real translator as its recursive entry. -/
def handleBitVecOps := Rec.handleBitVecOps (fun e h t n => translateExprToWire e h t n)
/-- `Rec.handleRegister` with the real translator as its recursive entry. -/
def handleRegister := Rec.handleRegister (fun e h t n => translateExprToWire e h t n)
/-- `Rec.handleMux` with the real translator as its recursive entry. -/
def handleMux := Rec.handleMux (fun e h t n => translateExprToWire e h t n)
/-- `Rec.handleMemory` with the real translator as its recursive entry. -/
def handleMemory := Rec.handleMemory (fun e h t n => translateExprToWire e h t n)
/-- `Rec.handleLoop` with the real translator as its recursive entry. -/
def handleLoop := Rec.handleLoop (fun e h t n => translateExprToWire e h t n)
/-- `Rec.handleCircuitMonad` with the real translator as its recursive entry. -/
def handleCircuitMonad := Rec.handleCircuitMonad (fun e h t n => translateExprToWire e h t n)
/-- `Rec.handleDefinitionUnfold` with the real translator as its recursive entry. -/
def handleDefinitionUnfold := Rec.handleDefinitionUnfold (fun e h t n => translateExprToWire e h t n)
/-- `Rec.translateExprToWireApp` with the real translator as its recursive entry. -/
def translateExprToWireApp := Rec.translateExprToWireApp (fun e h t n => translateExprToWire e h t n)
/-- `Rec.translateShiftAmount` with the real translator as its recursive entry. -/
def translateShiftAmount := Rec.translateShiftAmount (fun e h t n => translateExprToWire e h t n)
/-- `Rec.getPrimitiveNameFromLambda` with the real translator as its recursive entry. -/
def getPrimitiveNameFromLambda := Rec.getPrimitiveNameFromLambda (fun e h t n => translateExprToWire e h t n)
/-- The synthesis entry with the real translator as its recursive entry. -/
def synthesizeCombinationalCore := synthesizeCombinationalCoreWith (fun e h t n => translateExprToWire e h t n)
/-- `#synthesizeVerilog`'s synthesis with the real translator (a plain
    definition, so the post-processing theorems apply to it directly). -/
def synthesizeCombinational := synthesizeCombinationalWith (fun e h t n => translateExprToWire e h t n)
/-- The memoised child entry (`Rec.synthesizeCombinational`). -/
def synthesizeChild (n : Name) : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) :=
  Rec.synthesizeCombinational (fun e h t n => translateExprToWire e h t n) n
initialize sparkleChildSynth.set (some synthesizeChild)
/-- `Rec.synthesizeCombinationalWithParameters` with the real translator as its recursive entry. -/
def synthesizeCombinationalWithParameters := Rec.synthesizeCombinationalWithParameters (fun e h t n => translateExprToWire e h t n)


def printModule (m : Sparkle.IR.AST.Module) : MetaM Unit := do
  IO.println s!"Module: {m.name}"
  IO.println s!"Inputs: {m.inputs.length}"
  for input in m.inputs do
    IO.println s!"  - {input.name}: {input.ty}"
  IO.println s!"Outputs: {m.outputs.length}"
  for output in m.outputs do
    IO.println s!"  - {output.name}: {output.ty}"
  IO.println s!"Wires: {m.wires.length}"
  for wire in m.wires do
    IO.println s!"  - {wire.name}: {wire.ty}"
  IO.println s!"Statements: {m.body.length}"
  for stmt in m.body do
    IO.println s!"  {stmt}"

elab "#synthesize" id:ident : command => do
  let declName ← Lean.Elab.Command.liftCoreM do
    Lean.resolveGlobalConstNoOverload id
  Lean.Elab.Command.liftTermElabM do
    let (module, _) ← synthesizeCombinational declName
    printModule module
    IO.println "\n-- IR successfully generated!"

def runDesignDRC (design : Sparkle.IR.AST.Design) : MetaM Unit := do
  for m in design.modules do
    let warnings := Sparkle.Compiler.DRC.checkRegisteredOutputs m
    for w in warnings do
      Lean.logWarning m!"{w}"

/-- The text `#synthesizeVerilog` / `#showVerilog` print for a synthesized
    module: the IR optimizer (result-checked on small combinational modules
    and on assign + register modules, `Sparkle.IR.OptCheck.checkedOptimize`),
    then the Verilog printer. -/
def verilogOf (module : Sparkle.IR.AST.Module) : String :=
  toVerilog (Sparkle.IR.OptCheck.checkedOptimize module)

/-- Plain-text Verilog elaborator.

    `#synthesizeVerilog id` synthesises `id` and prints the resulting
    SystemVerilog to stdout.  Output is **plain text** — no MIME wrapper,
    no highlighting — so it works identically under `lake build`,
    `lake env lean`, CI, and any Jupyter kernel.

    For a syntax-highlighted view inside JupyterLab use `#showVerilog`
    instead; for writing to a file use `#writeVerilogDesign id "path"`. -/
elab "#synthesizeVerilog" id:ident : command => do
  -- Profile breadcrumbs.  When SPARKLE_PROFILE=1 is set, write
  -- to *both* stderr and /tmp/sparkle-profile.log so the timing
  -- survives even when `timeout` SIGKILLs the process before
  -- stdio buffers flush.  The log is append-mode so consecutive
  -- runs accumulate (delete it yourself between runs if you
  -- want a clean slate).
  let profile := (← IO.getEnv "SPARKLE_PROFILE").isSome
  let logProf (msg : String) : IO Unit := do
    if profile then
      IO.eprintln msg
      (← IO.getStderr).flush
      let h ← IO.FS.Handle.mk "/tmp/sparkle-profile.log" .append
      h.putStrLn msg
      h.flush
  logProf s!"[profile] #synthesizeVerilog entry id={id}"
  let declName ← Lean.Elab.Command.liftCoreM do
    Lean.resolveGlobalConstNoOverload id
  logProf s!"[profile] declName resolved: {declName}"
  Lean.Elab.Command.liftTermElabM do
    logProf s!"[profile] entering liftTermElabM, calling synthesizeCombinational"
    let (module, _) ← synthesizeCombinational declName
    let warnings := Sparkle.Compiler.DRC.checkRegisteredOutputs module
    for w in warnings do
      Lean.logWarning m!"{w}"
    -- Run the IR optimizer so 0-bit shapes (from `runCircuitH` /
    -- `bundle2 _ (Signal.pure ())`) are stripped before emission —
    -- without this we'd output `assign x = 0'd0;`, an invalid
    -- 0-width SystemVerilog literal that yosys/iverilog reject.
    let verilog := verilogOf module
    -- NB: `IO.println`, not `logInfo`.  This command's primary role
    -- is CLI / `lake build` smoke-testing — the synthesis check is
    -- what matters; the printed Verilog is for terminal use only.
    -- Inside the xeus-lean WASM notebook stdout is swallowed by
    -- the browser DevTools console — use `#showVerilog` (which
    -- emits via `logInfo`) for notebook display.
    IO.println verilog
    IO.println "\n-- Verilog successfully generated!"

declare_syntax_cat sparkleParameterBinding
syntax ident " := " num : sparkleParameterBinding
syntax (name := synthesizeParameterizedVerilog)
  "#synthesizeParameterizedVerilog " ident " [" sparkleParameterBinding,* "]" : command

/-- Emit one native parameterized module. Defaults validate the contract and
    serve downstream tools; widths remain symbolic in the emitted module. -/
elab_rules : command
  | `(#synthesizeParameterizedVerilog $id:ident [$bindings:sparkleParameterBinding,*]) => do
    let mut parameters : List (String × Nat) := []
    for binding in bindings.getElems do
      match binding with
      | `(sparkleParameterBinding| $name:ident := $value:num) =>
        parameters := parameters ++ [(name.getId.toString, value.getNat)]
      | _ => throwUnsupportedSyntax
    let declName ← Lean.Elab.Command.liftCoreM do
      Lean.resolveGlobalConstNoOverload id
    Lean.Elab.Command.liftTermElabM do
      let (module, _) ← synthesizeCombinationalWithParameters declName parameters
      let warnings := Sparkle.Compiler.DRC.checkRegisteredOutputs module
      for warning in warnings do
        Lean.logWarning m!"{warning}"
      IO.println (toVerilog module)
      IO.println "\n// Native parameterized Verilog successfully generated."

/-- Highlighted Verilog viewer for JupyterLab.

    `#showVerilog id` synthesises `id` and renders the SystemVerilog
    output inside an HTML `<pre><code class="language-verilog">` block,
    routed through xeus-lean's `text/html` MIME channel so JupyterLab's
    bundled highlight.js paints the source.

    Outside Jupyter (plain `lake env lean`, CI) the MIME marker bytes
    are still emitted but ESC / RS aren't visible, so the listing reads
    as the raw HTML.  In that case prefer `#synthesizeVerilog` for a
    clean text dump or `#writeVerilogDesign` to land the SV on disk. -/
elab "#showVerilog" id:ident : command => do
  let declName ← Lean.Elab.Command.liftCoreM do
    Lean.resolveGlobalConstNoOverload id
  Lean.Elab.Command.liftTermElabM do
    let (module, _) ← synthesizeCombinational declName
    let warnings := Sparkle.Compiler.DRC.checkRegisteredOutputs module
    for w in warnings do
      Lean.logWarning m!"{w}"
    -- Optimize before emission — same rationale as #synthesizeVerilog.
    let src := verilogOf module
    let escSrc := src
      |>.replace "&" "&amp;"
      |>.replace "<" "&lt;"
      |>.replace ">" "&gt;"
    let elemId := s!"sv-{(hash src).toUSize.toNat}"
    let html := String.intercalate "" [
      "<div class='xlean-verilog' style='margin:0'>",
      "<pre id='", elemId, "' style=\"background:#f6f8fa;padding:8px 12px;border-radius:4px;border:1px solid #e1e4e8;font-size:12px;line-height:1.4;overflow:auto;margin:0\">",
      "<code class='language-verilog'>", escSrc, "</code></pre></div>",
      "<script>(function(){",
      "var el=document.querySelector('#", elemId, " code');",
      "if(!el||el.dataset.hlPainted)return;",
      "function paint(){if(window.hljs){window.hljs.highlightElement(el);el.dataset.hlPainted='1';}}",
      "if(window.hljs){paint();return;}",
      "var s=document.createElement('script');",
      "s.src='https://cdn.jsdelivr.net/npm/highlight.js@11.9.0/lib/core.min.js';",
      "s.onload=function(){var v=document.createElement('script');",
      "v.src='https://cdn.jsdelivr.net/npm/highlight.js@11.9.0/lib/languages/verilog.min.js';",
      "v.onload=function(){window.hljs.registerLanguage('verilog', window.hljsVerilog||(()=>({})));paint();};",
      "document.head.appendChild(v);};document.head.appendChild(s);})();</script>"
    ]
    -- Route through Lean's info-message log (not raw IO.println).
    -- The xeus-lean WASM kernel does NOT capture stdout (its
    -- `withIsolatedStreams`-based stdout pipe was disabled when
    -- the kernel was ported to WASM), so `IO.println` lands in
    -- the browser DevTools console and never reaches the cell.
    -- `logInfo`-routed MIME markers go through the
    -- `messages[severity=info]` channel, which xinterpreter_wasm
    -- DOES scan with `extract_mime_payloads`, so the HTML payload
    -- is published as `text/html` rich output.
    -- Native (`lake env lean` / xeus native) sees the marker
    -- bytes the same way it did before.
    Sparkle.Display.Mime.logHtml html

/-- The final design boundary checks definition multiplicity as well as
normalized names of every definition and instance target. -/
def validateDesignNames (design : Sparkle.IR.AST.Design) : MetaM Sparkle.IR.AST.Design :=
  if Sparkle.IR.ModuleNameCheck.checkDesign design then pure design
  else throw (Exception.error .missing
    "Invalid, duplicate or colliding Verilog module names in synthesized design")

def synthesizeHierarchicalWithParameters (declName : Name)
    (parameters : List (String × Nat)) : MetaM Sparkle.IR.AST.Design := do
  let (module, design) ← synthesizeCombinationalWithParameters declName parameters
  let design' := if (design.modules.any (·.name == module.name)) then design else design.addModule module
  validateDesignNames design'

def synthesizeHierarchical (declName : Name) : MetaM Sparkle.IR.AST.Design := do
  let (module, design) ← synthesizeCombinational declName
  let design' := if (design.modules.any (·.name == module.name)) then design else design.addModule module
  validateDesignNames design'

elab "#synthesizeDesign" id:ident : command => do
  let declName ← Lean.Elab.Command.liftCoreM do
    Lean.resolveGlobalConstNoOverload id
  Lean.Elab.Command.liftTermElabM do
    let design ← synthesizeHierarchical declName
    for m in design.modules do
      printModule m
    IO.println "\n-- Hierarchical IR successfully generated!"

elab "#synthesizeVerilogDesign" id:ident : command => do
  let declName ← Lean.Elab.Command.liftCoreM do
    Lean.resolveGlobalConstNoOverload id
  Lean.Elab.Command.liftTermElabM do
    let design ← synthesizeHierarchical declName
    runDesignDRC design
    let verilog := toVerilogDesign design
    IO.println verilog
    IO.println "\n-- Hierarchical Verilog successfully generated!"

elab "#writeVerilogDesign" id:ident str:str : command => do
  let declName ← Lean.Elab.Command.liftCoreM do
    Lean.resolveGlobalConstNoOverload id
  Lean.Elab.Command.liftTermElabM do
    let design ← synthesizeHierarchical declName
    runDesignDRC design
    let verilog := toVerilogDesign design
    let path := str.getString
    if let some dir := (System.FilePath.mk path).parent then
      IO.FS.createDirAll dir
    IO.FS.writeFile path verilog
    IO.println s!"Written {design.modules.length} modules to {path}"

elab "#writeCppSimDesign" id:ident str:str : command => do
  let declName ← Lean.Elab.Command.liftCoreM do
    Lean.resolveGlobalConstNoOverload id
  Lean.Elab.Command.liftTermElabM do
    let design ← synthesizeHierarchical declName
    let optimized := Sparkle.IR.Optimize.optimizeDesign design
    let cSrc := Sparkle.Backend.CSim.toCDesign optimized
    let path := str.getString
    if let some dir := (System.FilePath.mk path).parent then
      IO.FS.createDirAll dir
    IO.FS.writeFile path cSrc
    IO.println s!"Written C simulation ({optimized.modules.length} modules) to {path}"

syntax (name := writeParameterizedCppSimDesign)
  "#writeParameterizedCppSimDesign " ident " [" sparkleParameterBinding,* "]" str : command

/-- Emit one fixed-ABI CSim model after specializing all retained dimensions
    for an explicit parameter configuration. -/
elab_rules : command
  | `(#writeParameterizedCppSimDesign $id:ident [$bindings:sparkleParameterBinding,*]
      $path:str) => do
    let mut parameters : List (String × Nat) := []
    for binding in bindings.getElems do
      match binding with
      | `(sparkleParameterBinding| $name:ident := $value:num) =>
        parameters := parameters ++ [(name.getId.toString, value.getNat)]
      | _ => throwUnsupportedSyntax
    let declName ← Lean.Elab.Command.liftCoreM do
      Lean.resolveGlobalConstNoOverload id
    Lean.Elab.Command.liftTermElabM do
      let design ← synthesizeHierarchicalWithParameters declName parameters
      let concrete ←
        match Sparkle.IR.Specialize.specializeDesign design parameters with
        | .ok specialized => pure specialized
        | .error message => throwError message
      -- CSim has a fixed ABI.  Optimize only after every symbolic dimension
      -- has become concrete because the optimizer itself queries bit widths.
      let optimized := Sparkle.IR.Optimize.optimizeDesign concrete
      let cSrc := Sparkle.Backend.CSim.toCDesign optimized
      let outputPath := path.getString
      if let some dir := (System.FilePath.mk outputPath).parent then
        IO.FS.createDirAll dir
      IO.FS.writeFile outputPath cSrc
      IO.println s!"Written specialized C simulation to {outputPath}"

/-- Emit the CUDA **batch** backend (`.cu`): N independent instances of the
    design, one GPU thread each — Monte-Carlo / fuzzing / test-vector sweeps.
    Compile: `nvcc -O2 -std=c++17 -shared -Xcompiler -fPIC -o lib<top>.so <top>.cu`.
    See `docs/CudaSim.md`. -/
elab "#writeCudaDesign" id:ident str:str : command => do
  let declName ← Lean.Elab.Command.liftCoreM do
    Lean.resolveGlobalConstNoOverload id
  Lean.Elab.Command.liftTermElabM do
    let design ← synthesizeHierarchical declName
    let optimized := Sparkle.IR.Optimize.optimizeDesign design
    let cu := Sparkle.Backend.CudaSim.toCudaSimDesign optimized
    let path := str.getString
    if let some dir := (System.FilePath.mk path).parent then
      IO.FS.createDirAll dir
    IO.FS.writeFile path cu
    IO.println s!"Written CUDA batch simulation ({optimized.modules.length} modules) to {path}"

syntax (name := writeParameterizedCudaDesign)
  "#writeParameterizedCudaDesign " ident " [" sparkleParameterBinding,* "]" str : command

/-- Emit one fixed-layout CUDA batch model after specializing every retained
    dimension for an explicit parameter configuration. -/
elab_rules : command
  | `(#writeParameterizedCudaDesign $id:ident [$bindings:sparkleParameterBinding,*]
      $path:str) => do
    let mut parameters : List (String × Nat) := []
    for binding in bindings.getElems do
      match binding with
      | `(sparkleParameterBinding| $name:ident := $value:num) =>
        parameters := parameters ++ [(name.getId.toString, value.getNat)]
      | _ => throwUnsupportedSyntax
    let declName ← Lean.Elab.Command.liftCoreM do
      Lean.resolveGlobalConstNoOverload id
    Lean.Elab.Command.liftTermElabM do
      -- CUDA shares CSim's fixed data layout.  Retain dimensions during Lean
      -- synthesis, specialize the whole design, and only then run passes that
      -- query concrete bit widths.
      let design ← synthesizeHierarchicalWithParameters declName parameters
      let concrete ←
        match Sparkle.IR.Specialize.specializeDesign design parameters with
        | .ok specialized => pure specialized
        | .error message => throwError message
      let optimized := Sparkle.IR.Optimize.optimizeDesign concrete
      let cu := Sparkle.Backend.CudaSim.toCudaSimDesign optimized
      let outputPath := path.getString
      if let some dir := (System.FilePath.mk outputPath).parent then
        IO.FS.createDirAll dir
      IO.FS.writeFile outputPath cu
      IO.println s!"Written specialized CUDA batch simulation to {outputPath}"

/-- Emit the CUDA **intra** backend (`.cu`): ONE design instance with one GPU
    thread per top-level sub-module instance (PE-per-thread) — makes a single
    large design (systolic array, core bank) simulate faster.  Analysis
    failures (Mealy boundaries, unsupported connections, …) surface here as
    build errors with the offender named.  Compile with `-rdc=true`.
    See `docs/CudaIntraSim-design.md`. -/
elab "#writeCudaIntraDesign" id:ident str:str : command => do
  let declName ← Lean.Elab.Command.liftCoreM do
    Lean.resolveGlobalConstNoOverload id
  Lean.Elab.Command.liftTermElabM do
    let design ← synthesizeHierarchical declName
    let optimized := Sparkle.IR.Optimize.optimizeDesign design
    match Sparkle.Backend.CudaIntra.toCudaIntraDesign optimized with
    | .error e => throwError "CUDA intra backend: {e}"
    | .ok cu =>
      let path := str.getString
      if let some dir := (System.FilePath.mk path).parent then
        IO.FS.createDirAll dir
      IO.FS.writeFile path cu
      IO.println s!"Written CUDA intra simulation to {path}"

/-- Evaluate an Array String constant at elaboration time -/
private unsafe def evalStringArrayImpl (name : Name) : TermElabM (Array String) :=
  Lean.Meta.evalExpr (Array String)
    (mkApp (mkConst ``Array [.zero]) (mkConst ``String []))
    (mkConst name [])

@[implemented_by evalStringArrayImpl]
private opaque evalStringArray (name : Name) : TermElabM (Array String)

/-- Core implementation for #writeDesign -/
private def writeDesignCore (declName : Name) (svPath cppPath : String)
    (observableWires : Option (List String)) : TermElabM Unit := do
  let design ← synthesizeHierarchical declName
  runDesignDRC design
  -- Ensure output directories exist
  if let some svDir := (System.FilePath.mk svPath).parent then
    IO.FS.createDirAll svDir
  if let some cppDir := (System.FilePath.mk cppPath).parent then
    IO.FS.createDirAll cppDir
  -- Verilog (unoptimized)
  let verilog := toVerilogDesign design
  IO.FS.writeFile svPath verilog
  IO.println s!"Written {design.modules.length} modules to {svPath}"
  -- CSim (optimized, no observableWires — keep all _gen_ as members for header)
  let optimized := Sparkle.IR.Optimize.optimizeDesign design
  let cSrc := Sparkle.Backend.CSim.toCDesign optimized
  IO.FS.writeFile cppPath cSrc
  IO.println s!"Written C simulation ({optimized.modules.length} modules) to {cppPath}"
  -- JIT wrapper (optimized with observableWires — demote non-observable to locals)
  let jitOptimized := Sparkle.IR.Optimize.optimizeDesign design observableWires
  let jitC := Sparkle.Backend.CSim.toCJIT jitOptimized observableWires
  let jitPath :=
    (cppPath.replace "_cppsim.h" "_jit.c").replace "_jit.c" "_jit.c"
  IO.FS.writeFile jitPath jitC
  IO.println s!"Written JIT wrapper to {jitPath}"

/-- Combined command: synthesize once, emit both Verilog and optimized C++ simulation -/
elab "#writeDesign" id:ident svPath:str cppPath:str : command => do
  let declName ← Lean.Elab.Command.liftCoreM do
    Lean.resolveGlobalConstNoOverload id
  Lean.Elab.Command.liftTermElabM do
    writeDesignCore declName svPath.getString cppPath.getString none

/-- Combined command with observable wires: emit both Verilog and optimized C++ simulation,
    with JIT code restricted to only the specified observable wires -/
elab "#writeDesign" id:ident svPath:str cppPath:str wiresId:ident : command => do
  let declName ← Lean.Elab.Command.liftCoreM do
    Lean.resolveGlobalConstNoOverload id
  Lean.Elab.Command.liftTermElabM do
    let wiresName ← Lean.resolveGlobalConstNoOverload wiresId
    let wiresArr ← evalStringArray wiresName
    writeDesignCore declName svPath.getString cppPath.getString (some wiresArr.toList)

/-- Helper: elaborate a string as a Lean command -/
private def elabSimStr (s : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command s with
  | .error err => throwError "#sim parse error:\n{err}\n\nSource:\n{s}"
  | .ok stx => elabCommand stx

/-- Names treated as clock/reset (excluded from SimInput) -/
private def isSimClkRst (name : String) : Bool :=
  ["clk", "clock", "CLK", "rst", "reset", "RST", "rst_n", "resetn", "RESETN"].any (· == name)
  || name.endsWith "_clk" || name.endsWith "_rst"

/-- Sanitize a name to valid Lean identifier -/
private def simLeanIdent (s : String) : String :=
  s.map fun c => if c.isAlphanum || c == '_' then c else '_'

/-- #sim — Generate typed JIT simulator from a Signal DSL definition.

    Usage:
      def counter : Signal Domain (BitVec 8) := ...
      #sim counter

    Generates:
      counter.Sim.SimInput, SimOutput, Simulator, load, jitCppPath
-/
elab "#sim" id:ident : command => do
  let declName ← Lean.Elab.Command.liftCoreM do
    Lean.resolveGlobalConstNoOverload id
  -- Phase 1: Synthesize + generate JIT C++ AND Verilog .sv (in TermElabM)
  let (ns, jitPath, svPath, topName, userInputs, outputs) ← Lean.Elab.Command.liftTermElabM do
    let design ← synthesizeHierarchical declName
    let optimized := Sparkle.IR.Optimize.optimizeDesign design
    let jitC := Sparkle.Backend.CSim.toCJIT optimized
    let verilog := Sparkle.Backend.Verilog.toVerilogDesign optimized
    let ns := simLeanIdent (toString declName.components.getLast!)
    let jitPath := s!".lake/build/gen/sim/{ns}_jit.c"
    let svPath  := s!".lake/build/gen/sim/{ns}.sv"
    try
      IO.FS.createDirAll ".lake/build/gen/sim"
      IO.FS.writeFile jitPath jitC
      IO.FS.writeFile svPath  verilog
    catch _ => pure ()
    -- Locate the TOP module by declName.  `synthesizeHierarchical`
    -- appends top last, but each sub-module (`@[hardware_module]`)
    -- was registered first via the synth-time submodule cache, so
    -- `modules.head?` picks up the sub-module instead of the top.
    -- Match by name (the synthesizeCombinational result uses
    -- `declName.toString` as the module name).
    let topModName := toString declName
    let m ← match optimized.modules.find? (·.name == topModName) with
      | some m => pure m
      | none =>
        -- Fallback: last module (which is what addModule appends).
        -- Should never fire in practice; better than throwing.
        match optimized.modules.getLast? with
        | some m => pure m
        | none => throwError "#sim: no module in design"
    let userInputs := m.inputs.filter fun p => !isSimClkRst p.name
    let outputs := m.outputs
    pure (ns, jitPath, svPath, m.name, userInputs, outputs)
  -- Phase 2: Generate typed wrappers (in CommandElabM)
  let lb := "{"
  let rb := "}"
  elabSimStr s!"namespace {ns}.Sim"
  elabSimStr "open Sparkle.Core.JIT"
  elabSimStr s!"def jitCppPath : String := \"{jitPath}\""
  if userInputs.isEmpty then
    elabSimStr "structure SimInput where\n  deriving Repr, BEq, Inhabited"
  else
    let fields := String.intercalate "\n" <|
      userInputs.map fun p => s!"  {simLeanIdent p.name} : BitVec {p.ty.bitWidth}"
    elabSimStr s!"structure SimInput where\n{fields}\n  deriving Repr, BEq, Inhabited"
  if outputs.isEmpty then
    elabSimStr "structure SimOutput where\n  deriving Repr, BEq, Inhabited"
  else
    let fields := String.intercalate "\n" <|
      outputs.map fun p => s!"  {simLeanIdent p.name} : BitVec {p.ty.bitWidth}"
    elabSimStr s!"structure SimOutput where\n{fields}\n  deriving Repr, BEq, Inhabited"
  elabSimStr "structure Simulator where\n  handle : JITHandle"
  let inputsIdx := (List.range userInputs.length).zip userInputs
  let setCalls := inputsIdx.map fun (idx, p) =>
    s!"  JIT.setInput sim.handle {idx} i.{simLeanIdent p.name}.toNat.toUInt64"
  let stepBody := String.intercalate "\n" setCalls
  elabSimStr s!"def Simulator.step (sim : Simulator) (i : SimInput) : IO Unit := do\n{stepBody}\n  JIT.evalTick sim.handle"
  -- For each output port: when the port width is > 64 bits,
  -- emit multiple `JIT.getOutput` calls reading 32-bit chunks
  -- (the C-side `jit_get_output` already exposes wide ports
  -- as N consecutive switch cases of `uint32_t` slot reads —
  -- see `emitGetOutputSwitch` in Sparkle/Backend/CSim.lean).
  -- Then OR-shift them into the BitVec.  Fixes Issue #75
  -- (silent truncation of > 64-bit JIT output ports).
  let (readLines, _) := outputs.foldl
    (fun (acc : List String × Nat) (p : Port) =>
      let w := p.ty.bitWidth
      let nameId := simLeanIdent p.name
      if w ≤ 64 then
        let line :=
          s!"  let v_{nameId} ← JIT.getOutput sim.handle {acc.2}\n" ++
          s!"  let {nameId} := BitVec.ofNat {w} v_{nameId}.toNat"
        (acc.1 ++ [line], acc.2 + 1)
      else
        -- Wide port: read ⌈w/32⌉ 32-bit slots and OR-shift.
        let nWords := (w + 31) / 32
        let slotIdxs := List.range nWords
        let reads := slotIdxs.map fun j =>
          s!"  let v_{nameId}_{j} ← JIT.getOutput sim.handle {acc.2 + j}"
        -- Assemble: each slot j contributes
        --   (BitVec.ofNat w v_<nameId>_j.toNat) <<< (32 * j)
        -- and we fold them with `|||`.
        let combineTerm (j : Nat) : String :=
          s!"(BitVec.ofNat {w} (v_{nameId}_{j}.toNat &&& 0xFFFFFFFF) <<< {32 * j})"
        let combined :=
          match slotIdxs with
          | [] => s!"(BitVec.ofNat {w} 0)"
          | j :: rest =>
            rest.foldl (fun s k => s ++ " ||| " ++ combineTerm k) (combineTerm j)
        let assemble :=
          s!"  let {nameId} : BitVec {w} := {combined}"
        (acc.1 ++ reads ++ [assemble], acc.2 + nWords))
    ([], 0)
  let readBody := String.intercalate "\n" readLines
  let readReturn := String.intercalate ", " <| outputs.map fun p => simLeanIdent p.name
  elabSimStr s!"def Simulator.read (sim : Simulator) : IO SimOutput := do\n{readBody}\n  pure {lb} {readReturn} {rb}"
  elabSimStr "def Simulator.reset (sim : Simulator) : IO Unit :=\n  JIT.reset sim.handle"
  elabSimStr "def Simulator.destroy (sim : Simulator) : IO Unit :=\n  JIT.destroy sim.handle"
  elabSimStr s!"def load : IO Simulator := do\n  let h ← JIT.compileAndLoad jitCppPath\n  pure {lb} handle := h {rb}"
  -- Opt the generated wrapper into the unified `Sparkle.Core.Sim.Sim`
  -- typeclass so call-sites can write `sim.step inp` / `sim.read`
  -- against any backend (pure-Lean / JIT / Verilator) without
  -- knowing which one produced `sim`.
  elabSimStr <|
    "instance : Sparkle.Core.Sim.Sim Simulator SimInput SimOutput where\n" ++
    "  reset   := Simulator.reset\n" ++
    "  step    := Simulator.step\n" ++
    "  read    := Simulator.read\n" ++
    "  destroy := Simulator.destroy"
  -- Verilator backend.  Reuses the same `Simulator` shape because
  -- the Verilator wrapper exposes the JIT C ABI; only `load`
  -- differs (it builds a `.so` from the `.sv` instead of from
  -- the JIT `.cpp`).
  elabSimStr s!"def svPath : String := \"{svPath}\""
  elabSimStr s!"def topModuleName : String := \"{topName}\""
  let portSpec (p : Sparkle.IR.AST.Port) : String :=
    "{ name := \"" ++ p.name ++ "\", width := " ++ toString p.ty.bitWidth ++ " : Sparkle.Core.Sim.Verilator.PortSpec }"
  let inputPortSpecs := String.intercalate ", " (userInputs.map portSpec)
  let outputPortSpecs := String.intercalate ", " (outputs.map portSpec)
  elabSimStr <|
    "def loadVerilator : IO Sparkle.Core.Sim.Verilator.Simulator :=\n" ++
    "  Sparkle.Core.Sim.Verilator.of svPath topModuleName\n" ++
    "    [" ++ inputPortSpecs ++ "]\n" ++
    "    [" ++ outputPortSpecs ++ "]"
  elabSimStr s!"end {ns}.Sim"

end Sparkle.Compiler.Elab
