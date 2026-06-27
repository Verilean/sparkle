/-
  Elaborator & Compiler

  Translates Lean expressions into hardware netlists using metaprogramming.
  This bridges the gap between high-level Signal code and low-level IR.
-/

import Lean
import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.Data.BitPack
import Sparkle.Backend.Verilog
import Sparkle.Backend.CppSim
import Sparkle.IR.Optimize
import Sparkle.Compiler.DRC
import Sparkle.Compiler.InlineAttr
import Sparkle.Core.Signal
import Sparkle.Core.Vector
import Sparkle.Core.CircuitMonad
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
  clockWire : Option String := none       -- Name of clock wire (if any)
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
  exprCache : Option (IO.Ref (Std.HashMap Lean.Expr String)) := none

/-- Compiler monad: combines CircuitM builder with MetaM -/
abbrev CompilerM := ReaderT CompilerState (StateT CircuitState MetaM)

namespace CompilerM

/-- Get the current compiler state (from ReaderT) -/
def getCompilerState : CompilerM CompilerState :=
  read

/-- Lookup a variable mapping -/
def lookupVar (fvarId : FVarId) : CompilerM (Option String) := do
  let s ← getCompilerState
  return s.varMap.lookup fvarId

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

/-- Lift CircuitM operations by modifying the circuit state -/
def makeWire (hint : String) (ty : HWType) (named : Bool := false) : CompilerM String := do
  let cs ← get
  let (name, cs') := CircuitM.makeWire hint ty named cs
  set cs'
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


def addOutput (name : String) (ty : HWType) : CompilerM Unit := do
  let cs ← get
  let ((), cs') := CircuitM.addOutput name ty cs
  set cs'

/-- Look up the HW width of a wire by name (from wires, inputs, or outputs) -/
def getWireWidth (wireName : String) : CompilerM Nat := do
  let cs ← get
  let allPorts := cs.module.wires ++ cs.module.inputs ++ cs.module.outputs
  match allPorts.find? (fun p => p.name == wireName) with
  | some p => return match p.ty with | .bitVector w => w | .bit => 1 | _ => 8
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
  return name

def emitMemory (hint : String) (addrWidth dataWidth : Nat) (clk : String)
    (writeAddr writeData writeEnable readAddr : Sparkle.IR.AST.Expr) (named : Bool := false) : CompilerM String := do
  let cs ← get
  let (name, cs') := CircuitM.emitMemory hint addrWidth dataWidth clk writeAddr writeData writeEnable readAddr named cs
  set cs'
  return name

def emitMemoryComboRead (hint : String) (addrWidth dataWidth : Nat) (clk : String)
    (writeAddr writeData writeEnable readAddr : Sparkle.IR.AST.Expr) (named : Bool := false) : CompilerM String := do
  let cs ← get
  let (name, cs') := CircuitM.emitMemoryComboRead hint addrWidth dataWidth clk writeAddr writeData writeEnable readAddr named cs
  set cs'
  return name

def emitInstance (moduleName : String) (instName : String) (connections : List (String × Sparkle.IR.AST.Expr)) : CompilerM Unit := do
  let cs ← get
  let ((), cs') := CircuitM.emitInstance moduleName instName connections cs
  set cs'

def addModuleToDesign (m : Sparkle.IR.AST.Module) : CompilerM Unit := do
  let cs ← get
  let ((), cs') := CircuitM.addModuleToDesign m cs
  set cs'

end CompilerM

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
    | .app fn _arg =>
      let fnConst := fn.getAppFn
      if fnConst.isConstOf ``OfNat.ofNat then
        -- OfNat.ofNat Type n inst -> extract n
        let args := e.getAppArgs
        if args.size >= 2 then
          extractWidth args[1]!
        else
          return 8
      else
        return 8
    | _ => return 8


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
        match ← CompilerM.liftMetaM (inferHWType innerType) with
        | some hwType => return hwType
        | none => CompilerM.liftMetaM $ throwError s!"Cannot infer hardware type from {innerType}"
      else
        match ← CompilerM.liftMetaM (inferHWType signalType) with
        | some hwType => return hwType
        | none => CompilerM.liftMetaM $ throwError s!"Cannot infer hardware type from {signalType}"
    | _ =>
      match ← CompilerM.liftMetaM (inferHWType signalType) with
      | some hwType => return hwType
      | none => CompilerM.liftMetaM $ throwError s!"Cannot infer hardware type from {signalType}"
  | _ =>
    match ← CompilerM.liftMetaM (inferHWType signalType) with
    | some hwType => return hwType
    | none => CompilerM.liftMetaM $ throwError s!"Cannot infer hardware type from {signalType}"

/-- Helper to extract a Nat literal or OfNat.ofNat wrap. -/
partial def extractNat (e : Lean.Expr) : CompilerM Nat := do
  let e ← CompilerM.liftMetaM (whnf e)
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const name _ =>
    if name == ``OfNat.ofNat && args.size >= 2 then
       match args[1]! with
       | .lit (.natVal n) => return n
       | _ => CompilerM.liftMetaM $ throwError s!"Expected Nat literal in OfNat, got: {args[1]!}"
    else if name == ``Fin.mk && args.size >= 2 then
       extractNat args[1]!
    else
       CompilerM.liftMetaM $ throwError s!"Expected Nat literal, got constant: {name}"
  | .lit (.natVal n) => return n
  | _ => CompilerM.liftMetaM $ throwError s!"Expected Nat, got: {e}"

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

mutual
  /-- Caching shim around `translateExprToWireImpl`.  All early-
      intercept handlers (Signal HAdd/HSub/etc., OfNat literals,
      ...) currently `return` straight from the inner impl, which
      means they never write back to the cache.  Wrapping here
      means **every** successful translate caches its result —
      so subsequent identical sub-trees become a HashMap lookup
      instead of a full re-walk through ~10 handlers + Meta. -/
  partial def translateExprToWire (e : Lean.Expr) (hint : String := "wire") (isTopLevel : Bool := false) (isNamed : Bool := false) : CompilerM String := do
    let cacheRef? := (← CompilerM.getCompilerState).exprCache
    -- Cache only when there's no fresh wire name to emit
    -- (`isNamed` would force a specific user-facing name) and
    -- when the expression isn't a free variable (those resolve
    -- against the lexically-scoped varMap, not by Expr identity).
    let cacheable := !isNamed && !e.isFVar && !isTopLevel
    if cacheable then
      if let some ref := cacheRef? then
        let cache ← CompilerM.liftMetaM (ref.get : IO _)
        if let some w := cache.get? e then
          CompilerM.liftMetaM (sparkleCacheHits.modify (· + 1))
          return w
        let eStripped := e.consumeMData
        if !(eStripped == e) then
          if let some w := cache.get? eStripped then
            CompilerM.liftMetaM (sparkleCacheHits.modify (· + 1))
            return w
    let r ← translateExprToWireImpl e hint isTopLevel isNamed
    if cacheable then
      if let some ref := cacheRef? then
        CompilerM.liftMetaM (ref.modify (·.insert e r))
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
      return envS.bind String.toNat? |>.getD 500000
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
      -- General binary operator interception
      let binOp? : Option Operator := match instName with
        | ``HAdd.hAdd => some .add
        | ``HSub.hSub => some .sub
        | ``HMul.hMul => some .mul
        | ``HAnd.hAnd => some .and
        | ``HOr.hOr   => some .or
        | ``HXor.hXor => some .xor
        | ``HShiftLeft.hShiftLeft => some .shl
        | ``HShiftRight.hShiftRight => some .shr
        | _ => none
      if let some op := binOp? then
        if args.size >= 2 then
          let arg1 := args[args.size - 2]!
          let arg2 := args[args.size - 1]!
          let type1 ← CompilerM.liftMetaM (Lean.Meta.inferType arg1)
          let type2 ← CompilerM.liftMetaM (Lean.Meta.inferType arg2)
          let isSignal1 := type1.isAppOf ``Sparkle.Core.Signal.Signal
          let isSignal2 := type2.isAppOf ``Sparkle.Core.Signal.Signal
          if isSignal1 || isSignal2 then
            let exprType ← cachedInferType e
            let hwType ← inferHWTypeFromSignal exprType
            let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
            -- For mixed Signal/BitVec: use extractBitVecLiteral for the constant arg
            let wireA ← if isSignal1 then
              translateExprToWire arg1 "op_a" (isTopLevel := false)
            else
              let (cVal, cWidth) ← extractBitVecLiteral arg1
              let constWire ← CompilerM.makeWire "op_const" (.bitVector cWidth)
              CompilerM.emitAssign constWire (.const (Int.ofNat cVal) cWidth)
              pure constWire
            let wireB ← if isSignal2 then
              translateExprToWire arg2 "op_b" (isTopLevel := false)
            else
              let (cVal, cWidth) ← extractBitVecLiteral arg2
              let constWire ← CompilerM.makeWire "op_const" (.bitVector cWidth)
              CompilerM.emitAssign constWire (.const (Int.ofNat cVal) cWidth)
              pure constWire
            CompilerM.emitAssign resWire (.op op [.ref wireA, .ref wireB])
            return resWire

      -- HAppend (concat) — separate because it uses .concat not .op
      if instName == ``HAppend.hAppend && args.size >= 2 then
        let arg1 := args[args.size - 2]!
        let arg2 := args[args.size - 1]!
        let type1 ← CompilerM.liftMetaM (Lean.Meta.inferType arg1)
        let type2 ← CompilerM.liftMetaM (Lean.Meta.inferType arg2)
        let isSignal1 := type1.isAppOf ``Sparkle.Core.Signal.Signal
        let isSignal2 := type2.isAppOf ``Sparkle.Core.Signal.Signal
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
               let totalWidth ← CompilerM.getWireWidth wireS
               let exprType ← cachedInferType e
               let hwType ← inferHWTypeFromSignal exprType
               let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
               let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
               CompilerM.emitAssign resWire (.slice (.ref wireS) (totalWidth - 1) (totalWidth - width))
               return resWire
           if fFn.isConstOf ``Prod.snd then
               let wireS ← translateExprToWire s "s" (isTopLevel := false)
               let exprType ← cachedInferType e
               let hwType ← inferHWTypeFromSignal exprType
               let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
               let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
               CompilerM.emitAssign resWire (.slice (.ref wireS) (width - 1) 0)
               return resWire

           -- Handle lambda functions in Signal.map (extractLsb', unary primitives)
           if let .lam _ _ body _ := f then
             let bodyFn := body.getAppFn
             if let .const opName _ := bodyFn then
               -- BitVec.extractLsb' → slice
               if opName == ``BitVec.extractLsb' then
                 let bodyArgs := body.getAppArgs
                 if bodyArgs.size >= 4 then
                   let start ← extractNat bodyArgs[bodyArgs.size - 3]!
                   let len ← extractNat bodyArgs[bodyArgs.size - 2]!
                   let wireS ← translateExprToWire s "s" (isTopLevel := false)
                   let resWire ← CompilerM.makeWire hint (.bitVector len) (named := isNamed)
                   CompilerM.emitAssign resWire (.slice (.ref wireS) (start + len - 1) start)
                   return resWire
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
               -- Unary primitives (neg, not, etc.)
               if let some op := getOperator opName then
                 let wireS ← translateExprToWire s "s" (isTopLevel := false)
                 let exprType ← cachedInferType e
                 let hwType ← inferHWTypeFromSignal exprType
                 let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
                 CompilerM.emitAssign resWire (.op op [.ref wireS])
                 return resWire

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
                     let start ← extractNat bodyArgs[bodyArgs.size - 3]!
                     let len ← extractNat bodyArgs[bodyArgs.size - 2]!
                     let wireA ← translateExprToWire a "a" (isTopLevel := false)
                     let resWire ← CompilerM.makeWire hint (.bitVector len) (named := isNamed)
                     CompilerM.emitAssign resWire (.slice (.ref wireA) (start + len - 1) start)
                     return resWire

                 -- Simple unary map: NOT, NEG (may have extra typeclass/type args)
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
        -- Hardware let: translate value to wire
        let valueWire ← translateExprToWire value name.toString (isTopLevel := false) (isNamed := true)
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
      let totalWidth ← CompilerM.getWireWidth wireS
      let exprType ← cachedInferType e
      let hwType ← inferHWTypeFromSignal exprType
      let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
      let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
      CompilerM.emitAssign resWire (.slice (.ref wireS) (totalWidth - 1) (totalWidth - width))
      return some resWire

    -- Signal.snd (new readable syntax)
    if name == ``Sparkle.Core.Signal.Signal.snd && args.size >= 1 then
      trace[sparkle.compiler] "→ tuple projection (snd)"
      let s := args[args.size-1]!
      let wireS ← translateExprToWire s "s" (isTopLevel := false)
      let exprType ← cachedInferType e
      let hwType ← inferHWTypeFromSignal exprType
      let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
      let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
      CompilerM.emitAssign resWire (.slice (.ref wireS) (width - 1) 0)
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
        let totalWidth ← CompilerM.getWireWidth wireS
        let exprType ← cachedInferType e
        let hwType ← inferHWTypeFromSignal exprType
        let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
        let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
        CompilerM.emitAssign resWire (.slice (.ref wireS) (totalWidth - 1) (totalWidth - width))
        return some resWire
      if fHead.isConstOf ``Prod.snd then
        trace[sparkle.compiler] "→ tuple projection (map snd)"
        let wireS ← translateExprToWire s "s" (isTopLevel := false)
        let exprType ← cachedInferType e
        let hwType ← inferHWTypeFromSignal exprType
        let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
        let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
        CompilerM.emitAssign resWire (.slice (.ref wireS) (width - 1) 0)
        return some resWire

    return none

  /-- Handle Signal.ap — binary op lifting, concat/sshiftRight special cases -/
  partial def handleApplicative (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (isNamed : Bool) : CompilerM (Option String) := do
    if name == ``Sparkle.Core.Signal.Signal.ap && args.size >= 2 then
      let sf := args[args.size-2]!
      let b := args[args.size-1]!
      let sfFn := sf.getAppFn
      let sfArgs := sf.getAppArgs
      if sfFn.isConstOf ``Sparkle.Core.Signal.Signal.map && sfArgs.size >= 2 then
        trace[sparkle.compiler] "→ applicative (Signal.ap)"
        let f := sfArgs[sfArgs.size-2]!
        let a := sfArgs[sfArgs.size-1]!
        let wireA ← translateExprToWire a "a"
        let wireB ← translateExprToWire b "b"
        let opName ← getPrimitiveNameFromLambda f
        match getOperator opName with
        | some op =>
          let exprType ← cachedInferType e
          let hwType ← inferHWTypeFromSignal exprType
          let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
          CompilerM.emitAssign resWire (.op op [.ref wireA, .ref wireB])
          return some resWire
        | none =>
          -- Special: BitVec.append / HAppend → concat
          if opName == ``HAppend.hAppend || opName == ``BitVec.append then
            let exprType ← cachedInferType e
            let hwType ← inferHWTypeFromSignal exprType
            let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
            CompilerM.emitAssign resWire (.concat [.ref wireA, .ref wireB])
            return some resWire
          -- Special: BitVec.sshiftRight → asr (Nat arg handled via signal wire)
          if opName == ``BitVec.sshiftRight then
            let exprType ← cachedInferType e
            let hwType ← inferHWTypeFromSignal exprType
            let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
            CompilerM.emitAssign resWire (.op .asr [.ref wireA, .ref wireB])
            return some resWire
          CompilerM.liftMetaM $ throwError s!"Complex lift of {opName} not yet supported: operator not found"
    return none

  /-- Handle BitVec.extractLsb', shifts, concat, isPrimitive dispatch -/
  partial def handleBitVecOps (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (isNamed : Bool) : CompilerM (Option String) := do
    -- BitVec.extractLsb': bit slice extraction
    if name == ``BitVec.extractLsb' && args.size >= 4 then
      trace[sparkle.compiler] "→ extractLsb'"
      let start ← extractNat args[args.size - 3]!
      let len ← extractNat args[args.size - 2]!
      let bvWire ← translateExprToWire args[args.size - 1]! "slice_src"
      let resWire ← CompilerM.makeWire hint (.bitVector len) (named := isNamed)
      CompilerM.emitAssign resWire (.slice (.ref bvWire) (start + len - 1) start)
      return some resWire

    -- BitVec.shiftLeft / BitVec.ushiftRight / BitVec.sshiftRight
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
    if (name == ``HAppend.hAppend || name == ``BitVec.append) && args.size >= 2 then
      trace[sparkle.compiler] "→ concat"
      let hiWire ← translateExprToWire args[args.size - 2]! "concat_hi"
      let loWire ← translateExprToWire args[args.size - 1]! "concat_lo"
      let exprType ← cachedInferType e
      let hwType ← inferHWTypeFromSignal exprType
      let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
      CompilerM.emitAssign resWire (.concat [.ref hiWire, .ref loWire])
      return some resWire

    -- isPrimitive dispatch
    if isPrimitive name then
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
      let cW ← translateExprToWire cond "mux_cond"
      let tW ← translateExprToWire thenSig "mux_then"
      let eW ← translateExprToWire elseSig "mux_else"
      let exprType ← cachedInferType e
      let hwType ← inferHWTypeFromSignal exprType
      let rW ← CompilerM.makeWire hint hwType (named := isNamed)
      CompilerM.emitAssign rW (.op .mux [.ref cW, .ref tW, .ref eW])
      return some rW

    return none

  /-- Handle Signal.memory, Signal.memoryComboRead -/
  partial def handleMemory (_e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (isNamed : Bool) : CompilerM (Option String) := do
    -- Signal.memory: synchronous RAM/BRAM
    if name.toString.endsWith ".memory" && !name.toString.endsWith ".memoryComboRead" && args.size >= 4 then
      trace[sparkle.compiler] "→ memory (sync)"
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
        let exprType ← cachedInferType e
        let hwType ← inferHWTypeFromSignal exprType
        let loopWire ← CompilerM.makeWire "loop" hwType
        -- Use CompilerM.withLocalDecl to keep the fvar in scope for both
        -- MetaM (type checking) and CompilerM (wire mapping).
        let resultWire ← CompilerM.withLocalDecl binderName binderType fun fvar => do
          let bodyInst := body.instantiate1 fvar
          CompilerM.withVarMapping fvar.fvarId! loopWire do
            translateExprToWire bodyInst "loop_body"
        CompilerM.emitAssign loopWire (.ref resultWire)
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
      if args.size >= 1 then
        -- The record arg might be:
        --   • a literal application like `kvHw a b c d e`
        --   • an fvar (`engine`) introduced by a `let engine := kvHw …`
        --     binding.  Sparkle's HW-let elaborator binds these
        --     with `withLocalDecl` (no value in lctx) but records
        --     the defining expression in sparkleFvarValueMap.
        -- Try the global value map first; fall back to lctx.value?
        -- for non-Sparkle let bindings.
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
        trace[sparkle.compiler] "→ projection {name}: recordArg head = {recFn}"
        if let .const recName _ := recFn then
          let isHW := Sparkle.Compiler.isHardwareModule env recName
          trace[sparkle.compiler] "→ projection: recName={recName} isHardwareModule={isHW}"
          if isHW then
            -- Synthesise the sub-module (cached internally), look
            -- up the field name on the projection, and bind a
            -- wire that's connected to the sub-module instance's
            -- matching output port.
            try
              let (subModule, subDesign) ← CompilerM.liftMetaM (synthesizeCombinational recName)
              let env' ← getEnv
              let some projInfo := env'.getProjectionFnInfo? name
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
              -- Add the child's transitive modules + child itself.
              let existing := (← get).design.modules.map (·.name)
              for m in subDesign.modules do
                if !existing.contains m.name then
                  CompilerM.addModuleToDesign m
              if !existing.contains subModule.name &&
                 !((← get).design.modules.any (·.name == subModule.name)) then
                CompilerM.addModuleToDesign subModule
              -- Connect inputs (= recordArg's args, after the
              -- structure's type-class implicits).
              let recArgs := recordArg.getAppArgs
              let mut connections := []
              for p in subModule.inputs do
                if p.name == "clk" || p.name == "rst" then
                  let parent := (← get).module
                  if !parent.inputs.any (·.name == p.name) then
                    CompilerM.addInput p.name p.ty
                  connections := (p.name, Sparkle.IR.AST.Expr.ref p.name) :: connections
              let inputPorts := subModule.inputs.filter (fun p => p.name != "clk" && p.name != "rst")
              if recArgs.size >= inputPorts.length then
                for i in [:inputPorts.length] do
                  let argExpr := recArgs[recArgs.size - inputPorts.length + i]!
                  let argWire ← translateExprToWire argExpr s!"arg{i}"
                  connections := (inputPorts[i]!.name, Sparkle.IR.AST.Expr.ref argWire) :: connections
              -- Allocate one wire per output port; remember the
              -- one matching `fieldName`.
              let mut targetWire : Option String := none
              for outP in subModule.outputs do
                let w ← CompilerM.makeWire s!"{hint}_{outP.name}" outP.ty (named := false)
                connections := (outP.name, Sparkle.IR.AST.Expr.ref w) :: connections
                if outP.name == fieldName then
                  targetWire := some w
              let instName ← CompilerM.freshName s!"inst_{subModule.name}"
              CompilerM.emitInstance subModule.name instName connections.reverse
              match targetWire with
              | some w => return some w
              | none => pure ()
            catch _ => pure ()
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
    let lastInlineFail : IO.Ref (Option String) ← IO.mkRef none
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
          lastInlineFail.set (some (← ex1.toMessageData.toString))
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
            lastInlineFail.set (some (← ex2.toMessageData.toString))
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
      let detail :=
        match lastFail with
        | some msg => s!"\n\nInline expansion failed with:\n{msg}\n\nCommon causes (sim-pass but synth-fail patterns):\n  · `sig.map (fun _ => true)` / `(fun _ => false)` — lifts a Bool constant\n    the synth elaborator has no rule for.  Use Signal.pure or drop the\n    redundant `&& true`.\n  · `sig.map (fun b => if b then C1 else C2)` for BitVec constants —\n    replace with `Signal.mux sig (Signal.pure C1) (Signal.pure C2)`.\n  · `(· != ·) <$> a <*> b` or `Bool.not <$> sig` —\n    use `(fun a b => !(a == b)) <$> a <*> b` and `(fun b => !b) <$> sig`.\n  · Returning a tuple from `circuit do` — wrap in a structure with\n    `HasDomain` (see IP/Net/Ethernet.lean RxOut)."
        | none => ""
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

    let exprType ← cachedInferType e
    let hwType ← inferHWTypeFromSignal exprType
    let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
    connections := ("out", Sparkle.IR.AST.Expr.ref resWire) :: connections

    -- Generate a fresh, unique instance name.  Two calls to the same
    -- sub-module within a single parent must produce two distinct
    -- `inst_*` names — otherwise the emitted Verilog has a duplicate
    -- identifier.
    let instName ← CompilerM.freshName s!"inst_{subModule.name}"
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

  partial def synthesizeCombinational (declName : Name) : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
    let profile := (← IO.getEnv "SPARKLE_PROFILE").isSome
    let logProf (msg : String) : IO Unit := do
      if profile then
        IO.eprintln msg
        (← IO.getStderr).flush
        let h ← IO.FS.Handle.mk "/tmp/sparkle-profile.log" .append
        h.putStrLn msg
        h.flush
    logProf s!"[profile] synthesizeCombinational {declName} entering"
    -- Reset per-synth caches so each #synthesizeVerilog starts
    -- clean (Expr identity from one decl shouldn't alias another).
    sparkleTypeCache.set {}
    sparkleTypeCacheHits.set 0
    sparkleTypeCacheMiss.set 0
    let constInfo ← getConstInfo declName
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
      -- Split the return value into per-leaf Lean expressions
      -- BEFORE entering CompilerM.  This lets us reuse the
      -- existing single-Signal translation path on each leaf,
      -- yielding one Verilog output port per leaf rather than a
      -- single packed wire.
      logProf s!"[profile] calling splitReturnLeaves"
      let leaves ← splitReturnLeaves body
      let t2 ← IO.monoMsNow
      logProf s!"[profile] splitReturnLeaves done ({t2 - t1} ms, leaves={leaves.size})"
      let cacheRef ← IO.mkRef ({} : Std.HashMap Lean.Expr String)
      let compiler : CompilerM String := do
        let mut firstWire : Option String := none
        let mut leafIdx := 0
        for (portName, leafExpr) in leaves do
          let tLeaf0 ← CompilerM.liftMetaM IO.monoMsNow
          let callsBefore ← CompilerM.liftMetaM sparkleCallCounter.get
          let hitsBefore  ← CompilerM.liftMetaM sparkleCacheHits.get
          CompilerM.liftMetaM (logProf s!"[profile] leaf {leafIdx} ({portName}) translate starting (calls={callsBefore} hits={hitsBefore})")
          let leafWire ← translateExprToWire leafExpr portName (isTopLevel := true)
          let tLeaf1 ← CompilerM.liftMetaM IO.monoMsNow
          let callsAfter ← CompilerM.liftMetaM sparkleCallCounter.get
          let hitsAfter  ← CompilerM.liftMetaM sparkleCacheHits.get
          CompilerM.liftMetaM (logProf s!"[profile] leaf {leafIdx} ({portName}) translate {tLeaf1 - tLeaf0} ms (calls Δ={callsAfter - callsBefore} hits Δ={hitsAfter - hitsBefore})")
          leafIdx := leafIdx + 1
          if firstWire.isNone then firstWire := some leafWire
          -- Record the leaf-expr → wire mapping so subsequent
          -- leaves that share sub-expressions (the common
          -- `Signal.loop` body in a multi-output return) reuse
          -- the wire instead of re-walking the whole tree.
          if !leafExpr.isFVar then
            CompilerM.liftMetaM (cacheRef.modify (·.insert leafExpr leafWire))
          let cs ← get
          let wireDecl := cs.module.wires.find? (fun (p : Port) => p.name == leafWire)
          let outputType := match wireDecl with
            | some decl => decl.ty
            | none =>
              match cs.module.inputs.find? (fun p => p.name == leafWire) with
              | some inputPort => inputPort.ty
              | none => .bitVector 8
          CompilerM.addOutput portName outputType
          CompilerM.emitAssign portName (.ref leafWire)
        return firstWire.getD "out"
      let circuitState := CircuitM.init declName.toString
      let compilerState : CompilerState :=
        { varMap := [], clockWire := none, resetWire := none
        , exprCache := some cacheRef }
      let (_, finalCircuitState) ← (compiler.run compilerState).run circuitState
      let mut module := finalCircuitState.module
      let hasRegisters := module.body.any (fun stmt =>
        match stmt with
        | .register .. => true
        | .memory .. => true
        | _ => false
      )
      if hasRegisters then
        module := module.addInput { name := "clk", ty := .bit }
        module := module.addInput { name := "rst", ty := .bit }
      return (module, finalCircuitState.design)
    | _ =>
      throwError s!"Cannot synthesize {declName}: not a definition"
end

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
    let optimized := Sparkle.IR.Optimize.optimizeModule module
    let verilog := toVerilog optimized
    -- NB: `IO.println`, not `logInfo`.  This command's primary role
    -- is CLI / `lake build` smoke-testing — the synthesis check is
    -- what matters; the printed Verilog is for terminal use only.
    -- Inside the xeus-lean WASM notebook stdout is swallowed by
    -- the browser DevTools console — use `#showVerilog` (which
    -- emits via `logInfo`) for notebook display.
    IO.println verilog
    IO.println "\n-- Verilog successfully generated!"

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
    let optimized := Sparkle.IR.Optimize.optimizeModule module
    let src := toVerilog optimized
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

def synthesizeHierarchical (declName : Name) : MetaM Sparkle.IR.AST.Design := do
  let (module, design) ← synthesizeCombinational declName
  let design' := if (design.modules.any (·.name == module.name)) then design else design.addModule module
  return design'

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
    let cpp := Sparkle.Backend.CppSim.toCppSimDesign optimized
    let path := str.getString
    if let some dir := (System.FilePath.mk path).parent then
      IO.FS.createDirAll dir
    IO.FS.writeFile path cpp
    IO.println s!"Written C++ simulation ({optimized.modules.length} modules) to {path}"

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
  -- CppSim (optimized, no observableWires — keep all _gen_ as members for header)
  let optimized := Sparkle.IR.Optimize.optimizeDesign design
  let cpp := Sparkle.Backend.CppSim.toCppSimDesign optimized
  IO.FS.writeFile cppPath cpp
  IO.println s!"Written C++ simulation ({optimized.modules.length} modules) to {cppPath}"
  -- JIT wrapper (optimized with observableWires — demote non-observable to locals)
  let jitOptimized := Sparkle.IR.Optimize.optimizeDesign design observableWires
  let jitCpp := Sparkle.Backend.CppSim.toCppSimJIT jitOptimized observableWires
  let jitPath := cppPath.replace "_cppsim.h" "_jit.cpp"
  IO.FS.writeFile jitPath jitCpp
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
    let jitCpp := Sparkle.Backend.CppSim.toCppSimJIT optimized
    let verilog := Sparkle.Backend.Verilog.toVerilogDesign optimized
    let ns := simLeanIdent (toString declName.components.getLast!)
    let jitPath := s!".lake/build/gen/sim/{ns}_jit.cpp"
    let svPath  := s!".lake/build/gen/sim/{ns}.sv"
    try
      IO.FS.createDirAll ".lake/build/gen/sim"
      IO.FS.writeFile jitPath jitCpp
      IO.FS.writeFile svPath  verilog
    catch _ => pure ()
    let m ← match optimized.modules.head? with
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
  let outputsIdx := (List.range outputs.length).zip outputs
  let readLines := outputsIdx.map fun (idx, p) =>
    s!"  let v{idx} ← JIT.getOutput sim.handle {idx}\n  let {simLeanIdent p.name} := BitVec.ofNat {p.ty.bitWidth} v{idx}.toNat"
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
