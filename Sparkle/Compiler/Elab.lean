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
import Sparkle.Core.Signal
import Sparkle.Core.Vector

namespace Sparkle.Compiler.Elab

open Lean Lean.Elab Lean.Elab.Command Lean.Meta
open Sparkle.IR.Builder
open Sparkle.IR.AST (Operator Port Module Expr Stmt)
open Sparkle.IR.Type
open Sparkle.Backend.Verilog

instance : Inhabited Sparkle.IR.AST.Port := ⟨{ name := "default", ty := .bit }⟩


/-- Compiler state tracking variable mappings and context -/
structure CompilerState where
  varMap : List (FVarId × String) := []  -- Map Lean variables to wire names
  clockWire : Option String := none       -- Name of clock wire (if any)
  resetWire : Option String := none       -- Name of reset wire (if any)

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
def makeWire (hint : String) (ty : HWType) : CompilerM String := do
  let cs ← get
  let (name, cs') := CircuitM.makeWire hint ty cs
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

def emitRegister (hint : String) (clk : String) (rst : String) (input : Sparkle.IR.AST.Expr) (initVal : Nat) (ty : HWType) : CompilerM String := do
  let cs ← get
  let (name, cs') := CircuitM.emitRegister hint clk rst input initVal ty cs
  set cs'
  return name

def emitMemory (hint : String) (addrWidth dataWidth : Nat) (clk : String)
    (writeAddr writeData writeEnable readAddr : Sparkle.IR.AST.Expr) : CompilerM String := do
  let cs ← get
  let (name, cs') := CircuitM.emitMemory hint addrWidth dataWidth clk writeAddr writeData writeEnable readAddr cs
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
    (``BitVec.sle, .le_s)
  ]

def isPrimitive (name : Name) : Bool :=
  primitiveRegistry.any (fun (n, _) => n == name)

def getOperator (name : Name) : Option Operator :=
  primitiveRegistry.lookup name

partial def inferHWType (type : Lean.Expr) : MetaM (Option HWType) := do
  let type ← whnf type
  match type with
  | .app (.const ``BitVec _) width =>
    -- Width can be direct literal or OfNat wrapper
    let w ← extractWidth width
    return some (if w == 1 then .bit else .bitVector w)
  | .const ``Bool _ =>
    return some .bit
  | .app (.app (.const ``Prod _) ty1) ty2 =>
    -- Product type: concatenate the two types
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
    return none
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


def inferHWTypeFromSignal (signalType : Lean.Expr) : CompilerM HWType := do
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
    else
      CompilerM.liftMetaM $ throwError s!"Expected BitVec literal, got application of {name}"
  | _ =>
    CompilerM.liftMetaM $ throwError s!"Expected BitVec literal, got: {expr}"

/-- Extract a Nat literal from an expression -/
def extractNatLiteral (expr : Lean.Expr) : CompilerM (Nat × Unit) := do
  let n ← extractNat expr
  return (n, ())

mutual
  partial def translateExprToWire (e : Lean.Expr) (hint : String := "wire") (isTopLevel : Bool := false) : CompilerM String := do
    -- IO.println s!"DEBUG: translateExprToWire {hint}, isTopLevel={isTopLevel}"
    -- 0. Handle free variables first (before any whnf)
    if let .fvar fvarId := e then
      match ← CompilerM.lookupVar fvarId with
      | some wireName => return wireName
      | none =>
        CompilerM.liftMetaM $ throwError s!"Unbound variable: {fvarId.name}"

    let fn := e.getAppFn
    let args := e.getAppArgs


    -- 1. High-priority Signal Recognition (Avoid premature unfolding)
    if let .const name _ := fn then
        -- Signal wrappers & identity casts
        if name == ``Sparkle.Core.Signal.Signal.mk || name == ``Sparkle.Core.Signal.Signal.val ||
           name == ``BitVec.ofFin || name == ``Fin.mk || name == ``BitVec.ofNat || name == ``BitVec.toNat ||
           name.toString.endsWith ".ofFin" || name.toString.endsWith ".ofNat" || name.toString.endsWith ".toNat" then
          if args.size >= 1 then
            let payload := if name == ``Fin.mk && args.size >= 2 then args[args.size-2]! else args.back!
            return ← translateExprToWire payload hint

        -- Signal.pure (constant signals)
        if name == ``Sparkle.Core.Signal.Signal.pure && args.size >= 1 then
           let constValue := args[args.size-1]!
           -- Try to extract the BitVec literal value
           let (value, width) ← try
             extractBitVecLiteral constValue
           catch _ =>
             -- If not a BitVec literal, try to reduce and check again
             let reduced ← CompilerM.liftMetaM (reduce constValue)
             try
               extractBitVecLiteral reduced
             catch _ =>
               throwError "Signal.pure: expected BitVec constant, got: {constValue}"
           let resWire ← CompilerM.makeWire hint (.bitVector width)
           CompilerM.emitAssign resWire (.const value width)
           return resWire

        -- bundle2
        if name == ``Sparkle.Core.Signal.bundle2 && args.size >= 2 then
           let wireA ← translateExprToWire args[args.size-2]! "a"
           let wireB ← translateExprToWire args[args.size-1]! "b"
           let resWire ← CompilerM.makeWire hint (.bitVector 16)
           CompilerM.emitAssign resWire (.concat [.ref wireA, .ref wireB])
           return resWire

        -- map Prod.fst/snd
        if name == ``Sparkle.Core.Signal.Signal.map && args.size >= 2 then
           let f := args[args.size-2]!
           let s := args[args.size-1]!
           let fFn := f.getAppFn
           if fFn.isConstOf ``Prod.fst then
               let wireS ← translateExprToWire s "s" (isTopLevel := false)
               let exprType ← CompilerM.liftMetaM (Lean.Meta.inferType e)
               let hwType ← inferHWTypeFromSignal exprType
               let resWire ← CompilerM.makeWire hint hwType
               let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
               CompilerM.emitAssign resWire (.slice (.ref wireS) (width * 2 - 1) width)
               return resWire
           if fFn.isConstOf ``Prod.snd then
               let wireS ← translateExprToWire s "s" (isTopLevel := false)
               let exprType ← CompilerM.liftMetaM (Lean.Meta.inferType e)
               let hwType ← inferHWTypeFromSignal exprType
               let resWire ← CompilerM.makeWire hint hwType
               let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
               CompilerM.emitAssign resWire (.slice (.ref wireS) (width - 1) 0)
               return resWire

        -- Detect if-then-else and match expressions that cannot be synthesized
        if name == ``ite || name == ``dite then
          CompilerM.liftMetaM $ throwError
            "if-then-else expressions cannot be synthesized to hardware.\n\n\
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
                          translateExprToWire body2Inst hint isTopLevel
                | _ =>
                  -- Single lambda body - substitute just the first parameter
                  CompilerM.withLocalDecl n1 ty1 fun fvar1 => do
                    CompilerM.withVarMapping fvar1.fvarId! wire1 do
                      let bodyInst := body1.instantiate1 fvar1
                      translateExprToWire bodyInst hint isTopLevel
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
                            translateExprToWire body2 hint isTopLevel
                  | _ =>
                    CompilerM.liftMetaM $ throwError s!"Expected nested lambda in continuation, got: {contExpr}"
                | none =>
                  CompilerM.liftMetaM $ throwError s!"Continuation fvar {contId.name} has no value in context"
              | _ =>
                CompilerM.liftMetaM $ throwError s!"Unexpected continuation type: {cont}"
              pure (some result)
            else if e' != e then do
              let result ← translateExprToWire e' hint (isTopLevel := false)
              pure (some result)
            else
              pure none
          | _ =>
            if e' != e then do
              let result ← translateExprToWire e' hint (isTopLevel := false)
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
                   let exprType ← CompilerM.liftMetaM (Lean.Meta.inferType e)
                   let hwType ← inferHWTypeFromSignal exprType
                   let resWire ← CompilerM.makeWire hint hwType
                   CompilerM.emitAssign resWire (.op op [.ref wireA, .ref wireB])
                   return resWire
                | none => pure ()

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
                 if let some op := getOperator opName then
                   -- For now, only handle the simple case: unary map (no constants in lambda)
                   -- The more complex case with constants needs better handling
                   let wireA ← translateExprToWire a "a" (isTopLevel := false)
                   -- Infer result type from the expression type
                   let exprType ← CompilerM.liftMetaM (Lean.Meta.inferType e)
                   let hwType ← inferHWTypeFromSignal exprType
                   let resWire ← CompilerM.makeWire hint hwType
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
    let e ← if hasMappedFvar then pure e
            else CompilerM.liftMetaM (withTransparency TransparencyMode.reducible $ whnf e)
    let fn := e.getAppFn


    match e with
    | .app .. =>
      if let .const _ _ := fn then
         translateExprToWireApp e hint
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
         | some e' => translateExprToWire e' hint (isTopLevel := isTopLevel)
         | none =>
            -- Fallback to general reduction
            let e' ← CompilerM.liftMetaM (withTransparency TransparencyMode.all $ whnf e)
            if e' != e then translateExprToWire e' hint (isTopLevel := isTopLevel)
            else translateExprToWireApp e hint

    | .proj _ idx eStruct => do
      let wireS ← translateExprToWire eStruct "s"
      -- Infer result type from the expression type
      let exprType ← CompilerM.liftMetaM (Lean.Meta.inferType e)
      let hwType ← inferHWTypeFromSignal exprType
      let resWire ← CompilerM.makeWire hint hwType
      let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
      let lo := (1 - idx) * width
      let hi := lo + width - 1
      CompilerM.emitAssign resWire (.slice (.ref wireS) hi lo)
      return resWire

    | .lit (.natVal n) => do
      -- Infer result type from the expression type
      let exprType ← CompilerM.liftMetaM (Lean.Meta.inferType e)
      let hwType ← inferHWTypeFromSignal exprType
      let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
      let wire ← CompilerM.makeWire hint hwType
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
        let valueWire ← translateExprToWire value name.toString (isTopLevel := false)
        CompilerM.withLocalDecl name type fun fvar => do
          let fvarId := fvar.fvarId!
          CompilerM.withVarMapping fvarId valueWire do
            let bodyInst := body.instantiate1 fvar
            translateExprToWire bodyInst hint isTopLevel
      else
        -- Logic let: add to context for reduction (zeta)
        -- This allows let-bound values to be inlined when referenced
        CompilerM.withLetDecl name type value fun fvar => do
          let bodyInst := body.instantiate1 fvar
          translateExprToWire bodyInst hint isTopLevel

    | .lam binderName binderType body _ => do
      let isHWArg ← try
        let _ ← inferHWTypeFromSignal binderType
        pure true
      catch _ => pure false

      if isHWArg then
          let hwType ← inferHWTypeFromSignal binderType
          let paramWire ← CompilerM.makeWire binderName.toString hwType
          -- Only add as input if this is a top-level function parameter
          if isTopLevel then
            CompilerM.addInput paramWire hwType

          -- Process the lambda body within a proper local context
          CompilerM.withLocalDecl binderName binderType fun fvar => do
            let fvarId := fvar.fvarId!
            CompilerM.withVarMapping fvarId paramWire do
              let bodyInst := body.instantiate1 fvar
              -- Nested lambdas are also top-level if they're part of the function signature
              translateExprToWire bodyInst hint isTopLevel
      else
          -- Logic argument (e.g. config): add to context but no wire/input
          CompilerM.withLocalDecl binderName binderType fun fvar => do
            let bodyInst := body.instantiate1 fvar
            translateExprToWire bodyInst hint isTopLevel


    | _ =>
      translateExprToWireApp e hint

  partial def translateExprToWireApp (e : Lean.Expr) (hint : String) : CompilerM String := do
    let fn := e.getAppFn
    let args := e.getAppArgs

    match fn with
    | .const name _ =>
      -- ============================================================================
      -- Error detection for problematic patterns that cannot be synthesized
      -- ============================================================================

      -- Detect if-then-else expressions (compile to Decidable.rec)
      if name == ``ite || name == ``dite then
        CompilerM.liftMetaM $ throwError
          "if-then-else expressions cannot be synthesized to hardware.\n\n\
          Use Signal.mux instead:\n\
          ❌ WRONG: if cond then a else b\n\
          ✓ RIGHT:  Signal.mux cond a b\n\n\
          See Tests/TestConditionals.lean for examples."

      -- Detect Decidable recursors (from if-then-else compilation)
      if name == ``Decidable.rec || name == ``Decidable.casesOn then
        CompilerM.liftMetaM $ throwError
          "Decidable.rec (from if-then-else) cannot be synthesized.\n\n\
          Use Signal.mux for hardware multiplexers:\n\
          ✓ Signal.mux (cond : Signal d Bool) (ifTrue ifFalse : Signal d α) : Signal d α\n\n\
          See Tests/TestConditionals.lean for examples."

      -- Note: We don't detect unbundle2 usage here because:
      -- 1. unbundle2 itself is fine (returns a tuple)
      -- 2. Pattern matching on unbundle2 gets compiled away before synthesis
      -- 3. We'd only catch non-problematic uses, creating false positives
      -- The pattern matching problem is documented in Tests/TestUnbundle2.lean and README

      -- ============================================================================
      -- Normal synthesis cases
      -- ============================================================================

      -- Special case: Signal.fst for tuple extraction (new readable syntax)
      if name == ``Sparkle.Core.Signal.Signal.fst && args.size >= 1 then
        let s := args[args.size-1]!
        let wireS ← translateExprToWire s "s" (isTopLevel := false)
        let exprType ← CompilerM.liftMetaM (Lean.Meta.inferType e)
        let hwType ← inferHWTypeFromSignal exprType
        let resWire ← CompilerM.makeWire hint hwType
        let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
        CompilerM.emitAssign resWire (.slice (.ref wireS) (width * 2 - 1) width)
        return resWire

      -- Special case: Signal.snd for tuple extraction (new readable syntax)
      if name == ``Sparkle.Core.Signal.Signal.snd && args.size >= 1 then
        let s := args[args.size-1]!
        let wireS ← translateExprToWire s "s" (isTopLevel := false)
        let exprType ← CompilerM.liftMetaM (Lean.Meta.inferType e)
        let hwType ← inferHWTypeFromSignal exprType
        let resWire ← CompilerM.makeWire hint hwType
        let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
        CompilerM.emitAssign resWire (.slice (.ref wireS) (width - 1) 0)
        return resWire

      -- Special case: Signal.map Prod.fst/snd for tuple extraction (legacy syntax)
      if name == ``Sparkle.Core.Signal.Signal.map && args.size >= 2 then
        let f := args[args.size-2]!
        let s := args[args.size-1]!
        if f.isConstOf ``Prod.fst then
          let wireS ← translateExprToWire s "s" (isTopLevel := false)
          -- Infer result type from the expression type
          let exprType ← CompilerM.liftMetaM (Lean.Meta.inferType e)
          let hwType ← inferHWTypeFromSignal exprType
          let resWire ← CompilerM.makeWire hint hwType
          let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
          CompilerM.emitAssign resWire (.slice (.ref wireS) (width * 2 - 1) width)
          return resWire
        if f.isConstOf ``Prod.snd then
          let wireS ← translateExprToWire s "s" (isTopLevel := false)
          -- Infer result type from the expression type
          let exprType ← CompilerM.liftMetaM (Lean.Meta.inferType e)
          let hwType ← inferHWTypeFromSignal exprType
          let resWire ← CompilerM.makeWire hint hwType
          let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
          CompilerM.emitAssign resWire (.slice (.ref wireS) (width - 1) 0)
          return resWire

      if name == ``Sparkle.Core.Signal.Signal.ap && args.size >= 2 then
        let sf := args[args.size-2]!
        let b := args[args.size-1]!
        let sfFn := sf.getAppFn
        let sfArgs := sf.getAppArgs
        if sfFn.isConstOf ``Sparkle.Core.Signal.Signal.map && sfArgs.size >= 2 then
          let f := sfArgs[sfArgs.size-2]!
          let a := sfArgs[sfArgs.size-1]!
          let wireA ← translateExprToWire a "a"
          let wireB ← translateExprToWire b "b"
          let opName ← getPrimitiveNameFromLambda f
          match getOperator opName with
          | some op =>
            -- Infer result type from the expression type
            let exprType ← CompilerM.liftMetaM (Lean.Meta.inferType e)
            let hwType ← inferHWTypeFromSignal exprType
            let resWire ← CompilerM.makeWire hint hwType
            CompilerM.emitAssign resWire (.op op [.ref wireA, .ref wireB])
            return resWire
          | none =>
            CompilerM.liftMetaM $ throwError s!"Complex lift of {opName} not yet supported: operator not found"

      if isPrimitive name then
        match getOperator name with
        | some op =>
          if args.size >= 2 then
            let wire1 ← translateExprToWire args[args.size-2]! "arg1"
            let wire2 ← translateExprToWire args[args.size-1]! "arg2"
            -- Infer result type from the expression type
            let exprType ← CompilerM.liftMetaM (Lean.Meta.inferType e)
            let hwType ← inferHWTypeFromSignal exprType
            let resultWire ← CompilerM.makeWire hint hwType
            CompilerM.emitAssign resultWire (.op op [.ref wire1, .ref wire2])
            return resultWire
          else if args.size == 1 then
             let wire1 ← translateExprToWire args[0]! "arg1"
             -- Infer result type from the expression type
             let exprType ← CompilerM.liftMetaM (Lean.Meta.inferType e)
             let hwType ← inferHWTypeFromSignal exprType
             let resultWire ← CompilerM.makeWire hint hwType
             CompilerM.emitAssign resultWire (.op op [.ref wire1])
             return resultWire
        | none =>
          CompilerM.liftMetaM $ throwError s!"Internal error: {name} is marked as primitive but has no operator"

      if name.toString.endsWith ".register" && args.size >= 2 then
        let init := args[args.size-2]!
        let input := args[args.size-1]!
        let (initVal, _) ← extractBitVecLiteral init
        let inputWire ← translateExprToWire input "reg_input"
        let exprType ← CompilerM.liftMetaM (inferType e)
        let hwType ← inferHWTypeFromSignal exprType
        return ← CompilerM.emitRegister hint "clk" "rst" (.ref inputWire) initVal hwType

      if name.toString.endsWith ".mux" && args.size >= 3 then
        let cond := args[args.size-3]!
        let thenSig := args[args.size-2]!
        let elseSig := args[args.size-1]!
        let cW ← translateExprToWire cond "mux_cond"
        let tW ← translateExprToWire thenSig "mux_then"
        let eW ← translateExprToWire elseSig "mux_else"
        -- Infer result type from the expression type
        let exprType ← CompilerM.liftMetaM (Lean.Meta.inferType e)
        let hwType ← inferHWTypeFromSignal exprType
        let rW ← CompilerM.makeWire hint hwType
        CompilerM.emitAssign rW (.op .mux [.ref cW, .ref tW, .ref eW])
        return rW

      -- Signal.memory: synchronous RAM/BRAM
      if name.toString.endsWith ".memory" && args.size >= 4 then
        -- Extract addrWidth and dataWidth from explicit arguments
        let addrWidthArg := args[args.size-6]!
        let dataWidthArg := args[args.size-5]!
        let (addrWidth, _) ← extractNatLiteral addrWidthArg
        let (dataWidth, _) ← extractNatLiteral dataWidthArg
        -- Extract signal arguments
        let writeAddr := args[args.size-4]!
        let writeData := args[args.size-3]!
        let writeEnable := args[args.size-2]!
        let readAddr := args[args.size-1]!
        -- Translate to wires
        let waW ← translateExprToWire writeAddr "mem_waddr"
        let wdW ← translateExprToWire writeData "mem_wdata"
        let weW ← translateExprToWire writeEnable "mem_we"
        let raW ← translateExprToWire readAddr "mem_raddr"
        -- Emit memory and return read data wire
        return ← CompilerM.emitMemory hint addrWidth dataWidth "clk"
          (.ref waW) (.ref wdW) (.ref weW) (.ref raW)

      -- HWVector.get: array indexing
      if name == ``Sparkle.Core.Vector.HWVector.get && args.size >= 2 then
        let vec := args[args.size-2]!
        let idx := args[args.size-1]!
        let vecWire ← translateExprToWire vec "vec"
        let idxWire ← translateExprToWire idx "idx"
        -- Infer result type from the expression type
        let exprType ← CompilerM.liftMetaM (Lean.Meta.inferType e)
        let hwType ← inferHWTypeFromSignal exprType
        let resWire ← CompilerM.makeWire hint hwType
        CompilerM.emitAssign resWire (.index (.ref vecWire) (.ref idxWire))
        return resWire

      if name.toString.endsWith ".loop" && args.size >= 1 then
        let f := args.back!
        match f with
        | .lam binderName binderType body _ =>
          -- Infer result type from the expression type
          let exprType ← CompilerM.liftMetaM (Lean.Meta.inferType e)
          let hwType ← inferHWTypeFromSignal exprType
          let loopWire ← CompilerM.makeWire "loop" hwType
          let (fvarId, bodyInst) ← CompilerM.liftMetaM do
            withLocalDeclD binderName binderType fun fvar => do
              return (fvar.fvarId!, body.instantiate1 fvar)
          let resultWire ← CompilerM.withVarMapping fvarId loopWire do
            translateExprToWire bodyInst "loop_body"
          CompilerM.emitAssign loopWire (.ref resultWire)
          return resultWire
        | _ => CompilerM.liftMetaM $ throwError "Signal.loop argument must be a lambda"

      -- Check if this is a valid definition (not a type constructor or builtin)
      let isValidDef ← CompilerM.liftMetaM do
        try
          let constInfo ← getConstInfo name
          match constInfo with
          | .defnInfo _ => return true
          | _ => return false
        catch _ => return false

      if isValidDef then
        let (subModule, subDesign) ← CompilerM.liftMetaM $ synthesizeCombinational name
        for m in subDesign.modules do CompilerM.addModuleToDesign m
        CompilerM.addModuleToDesign subModule

        let mut connections := []
        let inputPorts := subModule.inputs.filter (fun p => p.name != "clk" && p.name != "rst")
        if args.size < inputPorts.length then
           CompilerM.liftMetaM $ throwError s!"Sub-module {name} requires {inputPorts.length} args, but got {args.size}"

        for i in [:inputPorts.length] do
           let argExpr := args[args.size - inputPorts.length + i]!
           let argWire ← translateExprToWire argExpr s!"arg{i}"
           connections := (inputPorts[i]!.name, Sparkle.IR.AST.Expr.ref argWire) :: connections

        -- Infer result type from the expression type
        let exprType ← CompilerM.liftMetaM (Lean.Meta.inferType e)
        let hwType ← inferHWTypeFromSignal exprType
        let resWire ← CompilerM.makeWire hint hwType
        connections := ("out", Sparkle.IR.AST.Expr.ref resWire) :: connections

        CompilerM.emitInstance subModule.name s!"inst_{subModule.name}" connections.reverse
        return resWire
      else
        -- Not a valid module - throw error with debug info
        CompilerM.liftMetaM $ do
          -- Check if this is a known problematic pattern that should have been caught
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

  partial def getPrimitiveNameFromLambda (e : Lean.Expr) : CompilerM Name := do
    match e with
    | .lam _ _ body _ => getPrimitiveNameFromLambda body
    | _ =>
      let fn := e.getAppFn
      match fn with
      | .const name _ => return name
      | _ => CompilerM.liftMetaM $ throwError s!"Could not identify primitive in lambda body: {e}"

  partial def synthesizeCombinational (declName : Name) : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
    let constInfo ← getConstInfo declName
    match constInfo with
    | .defnInfo defnInfo =>
      let body := defnInfo.value
      let compiler : CompilerM String := do
        let resultWire ← translateExprToWire body "result" (isTopLevel := true)
        -- Look up the actual wire type that was created
        let cs ← get
        let resultWireDecl := cs.module.wires.find? (fun (p : Port) => p.name == resultWire)
        let outputType := match resultWireDecl with
          | some decl =>
            -- DEBUG: Found wire with correct type
            decl.ty
          | none =>
            -- DEBUG: Wire not found, using fallback
            -- This happens when result is input wire, not internal wire
            -- Try to infer from inputs
            match cs.module.inputs.find? (fun p => p.name == resultWire) with
            | some inputPort => inputPort.ty
            | none => .bitVector 8  -- True fallback
        CompilerM.addOutput "out" outputType
        CompilerM.emitAssign "out" (.ref resultWire)
        return resultWire
      let circuitState := CircuitM.init declName.toString
      let compilerState : CompilerState := { varMap := [], clockWire := none, resetWire := none }
      let (_, finalCircuitState) ← (compiler.run compilerState).run circuitState
      let mut module := finalCircuitState.module
      let hasRegisters := module.body.any (fun stmt =>
        match stmt with
        | .register .. => true
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
  let declName := id.getId
  Lean.Elab.Command.liftTermElabM do
    let (module, _) ← synthesizeCombinational declName
    printModule module
    IO.println "\n-- IR successfully generated!"

elab "#synthesizeVerilog" id:ident : command => do
  let declName := id.getId
  Lean.Elab.Command.liftTermElabM do
    let (module, _) ← synthesizeCombinational declName
    let verilog := toVerilog module
    IO.println verilog
    IO.println "\n-- Verilog successfully generated!"

def synthesizeHierarchical (declName : Name) : MetaM Sparkle.IR.AST.Design := do
  let (module, design) ← synthesizeCombinational declName
  let design' := if (design.modules.any (·.name == module.name)) then design else design.addModule module
  return design'

elab "#synthesizeDesign" id:ident : command => do
  let declName := id.getId
  Lean.Elab.Command.liftTermElabM do
    let design ← synthesizeHierarchical declName
    for m in design.modules do
      printModule m
    IO.println "\n-- Hierarchical IR successfully generated!"

elab "#synthesizeVerilogDesign" id:ident : command => do
  let declName := id.getId
  Lean.Elab.Command.liftTermElabM do
    let design ← synthesizeHierarchical declName
    let verilog := toVerilogDesign design
    IO.println verilog
    IO.println "\n-- Hierarchical Verilog successfully generated!"

end Sparkle.Compiler.Elab
