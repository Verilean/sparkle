import Tools.ShippingMachineAuto
import Tools.ShippingMachineNest
import Tools.ShippingMachineTeleNest
import Tools.ShippingMachineLoop
import Tools.ShippingMachineShipping
import Tools.ShippingSignOps
import Tools.ShippingMachineCausalCtx

/-! # The machine endpoint of a declaration, generated

`#machine_endpoint f` computes, for a `circuit do` declaration `f` on the
machine route, the data of `Tools.ShippingMachineAuto.MachineData` — it reads
the typed terms off the transition's body (`unq`, the inverse of `quote`) —
and adds

* `f.machineData`, `f.machineInits`, `f.machineBody`, `f.machineResult`,
  `f.machineSource`;
* six facts, each an `Eq.refl` the KERNEL checks: `f.machine_ok` (all the
  side conditions), `f.machine_body` (the body is the quotation of the
  terms), `f.machine_inits`, `f.machine_writes` and `f.machine_result` (on
  any state signal, the body's pending writes and its result are the typed
  values of the next-value and result terms), `f.machine_source` (the
  declaration is the result of its body on the state loop);
* `f.machine_sound`: a run of the real synthesis entry on `f` at the machine
  boundary returns a module that shows, on every output port and at every
  cycle, the SOURCE declaration `f`;
* `f.machine_ships`: the same at the FULL entry, for the module the printer
  is given (`checkedOptimize`) and its emitted Verilog
  (`Tools.ShippingMachineShipping.machine_ships_checked`): the merge and
  the optimizer are checked by the compiler itself, so what remains are
  structural facts about the run's modules and the emitted-Verilog check.

Nothing here is trusted: a wrong reading of the body makes a kernel check
fail, and the command then adds no theorem. -/
namespace Tools.ShippingMachineCommand
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingScalarSoundness
open Tools.ShippingMachineEntry Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingMachineFuse Tools.ShippingMachineNest
open Tools.ShippingMixedSourceBridge Tools.ShippingEntrySoundness

initialize registerTraceClass `Sparkle.machine

/-! ## Reading terms off an expression -/

abbrev AnyTerm := Σ s : SType, Term s
abbrev BitsTerm := Σ w : Nat, Term (.bits w)

def asBool : AnyTerm → Option (Term .bool)
  | ⟨.bool, t⟩ => some t
  | _ => none

def asBits (w : Nat) : AnyTerm → Option (Term (.bits w))
  | ⟨.bits w', t⟩ => if h : w' = w then some (h ▸ t) else none
  | _ => none

/-- The binders of a transition, as the reader needs them: the kind of every
position, and the rank of a position among the Bool / BitVec binders. -/
structure Binders where
  kinds : Array MixedGateBinder
  rankB : Array Nat
  rankV : Array Nat

def Binders.ofKinds (kinds : List MixedGateBinder) : Binders := Id.run do
  let mut rb : Array Nat := #[]
  let mut rv : Array Nat := #[]
  let mut nb := 0
  let mut nv := 0
  for k in kinds do
    rb := rb.push nb
    rv := rv.push nv
    match k with
    | .bool => nb := nb + 1
    | .bits _ => nv := nv + 1
    | .domain => pure ()
  return { kinds := kinds.toArray, rankB := rb, rankV := rv }

def binaryOfInst (n : Name) : Option Binary :=
  [Binary.add, .sub, .mul, .and, .or, .xor, .shr, .shl].find? fun op => binInst op == n

/-- The typed term an expression is the quotation of (the inverse of
`quote`, by the head of each node). The result is CHECKED afterwards, so
this function carries no obligation. -/
partial def unq (c : Binders) (e : Lean.Expr) : Option AnyTerm :=
  match e with
  | .bvar i =>
    let n := c.kinds.size
    if i < n then
      let p := n - 1 - i
      match c.kinds[p]? with
      | some .bool => some ⟨.bool, .boolInput c.rankB[p]!⟩
      | some (.bits w) => some ⟨.bits w, .bitsInput w c.rankV[p]!⟩
      | _ => none
    else none
  | _ =>
  let args := e.getAppArgs
  match e.getAppFn with
  | .const f _ =>
    if f == ``Sparkle.Core.Signal.Signal.pure && args.size == 3 then
      match args[2]! with
      | .const ``Bool.true _ => some ⟨.bool, .boolLit true⟩
      | .const ``Bool.false _ => some ⟨.bool, .boolLit false⟩
      | .app (.app (.const ``BitVec.ofNat _) wE) vE => do
        let w ← canonicalNatLitValue? wE
        let v ← canonicalNatLitValue? vE
        some ⟨.bits w, .bitsLit w v⟩
      | .app (.app (.app (.const ``OfNat.ofNat _) (.app (.const ``BitVec _) wE))
          (.lit (.natVal v))) _ => do
        let w ← canonicalNatLitValue? wE
        some ⟨.bits w, .bitsNum w v⟩
      | _ => none
    else if f == ``Complement.complement && args.size == 3 then do
      let a ← asBool (← unq c args[2]!)
      some ⟨.bool, .boolNot a⟩
    else if f == ``Sparkle.Core.Signal.Signal.mux && args.size == 5 then do
      let cnd ← asBool (← unq c args[2]!)
      let a ← unq c args[3]!
      let b ← unq c args[4]!
      match a with
      | ⟨.bool, a⟩ => do
        let b ← asBool b
        some ⟨.bool, .mux cnd a b⟩
      | ⟨.bits w, a⟩ => do
        let b ← asBits w b
        some ⟨.bits w, .mux cnd a b⟩
    else if f == ``Sparkle.Core.Signal.Signal.beq && args.size == 5 then do
      let a ← unq c args[3]!
      let b ← unq c args[4]!
      match a with
      | ⟨.bool, a⟩ => do
        let b ← asBool b
        some ⟨.bool, .boolEq a b⟩
      | ⟨.bits w, a⟩ => do
        let b ← asBits w b
        some ⟨.bool, .compare .eq a b⟩
    else if (f == ``Sparkle.Core.Signal.Signal.ult || f == ``Sparkle.Core.Signal.Signal.ule ||
        f == ``Sparkle.Core.Signal.Signal.slt || f == ``Sparkle.Core.Signal.Signal.sle) &&
        args.size == 4 then do
      let op : SignalCompareKind :=
        if f == ``Sparkle.Core.Signal.Signal.ult then .ult
        else if f == ``Sparkle.Core.Signal.Signal.ule then .ule
        else if f == ``Sparkle.Core.Signal.Signal.slt then .slt else .sle
      let a ← unq c args[2]!
      match a with
      | ⟨.bits w, a⟩ => do
        let b ← asBits w (← unq c args[3]!)
        some ⟨.bool, .compare op a b⟩
      | _ => none
    else if f == ``Sparkle.Core.Signal.Signal.ap && args.size == 5 then
      match args[3]! with
      | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map _) _) _) _)
          (.lam _ _ (.lam _ _ body _) _)) a =>
        match appBoolBody? args[1]! body with
        | some (.compare op n) => do
          let a ← asBits n (← unq c a)
          let b ← asBits n (← unq c args[4]!)
          some ⟨.bool, .appCompare op a b⟩
        | some (.bool op) => do
          let a ← asBool (← unq c a)
          let b ← asBool (← unq c args[4]!)
          some ⟨.bool, .appBool op a b⟩
        | some (.two g) => do
          let a ← asBool (← unq c a)
          let b ← asBool (← unq c args[4]!)
          some ⟨.bool, .appBool2 g a b⟩
        | none => none
      | _ => none
    else if f == ``Sparkle.Core.Signal.Signal.map && args.size == 5 then do
      let a ← unq c args[4]!
      match a with
      | ⟨.bits w, a⟩ =>
        match args[3]! with
        | .app (.app (.const ``BitVec.setWidth _) _) wtE => do
          let w' ← canonicalNatLitValue? wtE
          some ⟨.bits w', .setw w' a⟩
        | .lam nm _ (.app (.app (.app (.app (.const ``BitVec.extractLsb' _) _) startE) lenE)
            (.bvar 0)) _ => do
          let start ← canonicalNatLitValue? startE
          let len ← canonicalNatLitValue? lenE
          some ⟨.bits len, .slice nm start len a⟩
        | .lam nm _ (.app (.app (.app (.app (.const ``BitVec.append _) kE) _) _) (.bvar 0)) _ => do
          let k ← canonicalNatLitValue? kE
          some ⟨.bits (k + w), .zextMap nm k a⟩
        | _ => none
      | _ => none
    else if f == ``Functor.map && args.size == 6 then do
      let a ← unq c args[5]!
      match a, args[4]! with
      | ⟨.bits _, a⟩, .lam nm _ (.app (.app (.app (.app (.const ``BitVec.extractLsb' _) _) startE)
          lenE) (.bvar 0)) _ => do
        let start ← canonicalNatLitValue? startE
        let len ← canonicalNatLitValue? lenE
        some ⟨.bits len, .sliceF nm start len a⟩
      | _, _ => none
    else if args.size == 6 then
      let inst := args[3]!.getAppFn.constName?.getD .anonymous
      if f == ``HAppend.hAppend then
        if inst == ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat then do
          let a ← unq c args[4]!
          let b ← unq c args[5]!
          match a, b with
          | ⟨.bits _, a⟩, ⟨.bits _, b⟩ => some ⟨.bits _, .concat a b⟩
          | _, _ => none
        else if inst == ``Sparkle.Core.Signal.instHAppendBitVecSignalHAddNat then do
          let b ← unq c args[5]!
          match args[4]!, b with
          | .app (.app (.const ``BitVec.ofNat _) kE) vE, ⟨.bits _, b⟩ => do
            let k ← canonicalNatLitValue? kE
            let v ← canonicalNatLitValue? vE
            some ⟨.bits _, .concatLitHi k v b⟩
          | _, _ => none
        else if inst == ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat_1 then do
          let a ← unq c args[4]!
          match a, args[5]! with
          | ⟨.bits _, a⟩, .app (.app (.const ``BitVec.ofNat _) kE) vE => do
            let k ← canonicalNatLitValue? kE
            let v ← canonicalNatLitValue? vE
            some ⟨.bits _, .concatLitLo a k v⟩
          | _, _ => none
        else none
      else
        match signalBoolBinKind? f args[3]! with
        | some op => do
          let a ← asBool (← unq c args[4]!)
          let b ← asBool (← unq c args[5]!)
          some ⟨.bool, .boolBinary op a b⟩
        | none =>
          match binaryOfInst inst with
          | some op => do
            let a ← unq c args[4]!
            match a with
            | ⟨.bits w, a⟩ => do
              let b ← asBits w (← unq c args[5]!)
              some ⟨.bits w, .binary op a b⟩
            | _ => none
          | none => none
    else none
  | _ => none

/-- The first `n` operands of a right-nested concatenation, and the rest. -/
def splitLets : Nat → BitsTerm → Option (List BitsTerm × BitsTerm)
  | 0, t => some ([], t)
  | n + 1, ⟨_, .concat a rest⟩ =>
    (splitLets n ⟨_, rest⟩).map fun (fs, core) => (⟨_, a⟩ :: fs, core)
  | _, _ => none

/-- The `n` operands of a right-nested concatenation. -/
def splitFields : Nat → BitsTerm → Option (List BitsTerm)
  | 0, _ => none
  | 1, t => some [t]
  | n + 2, ⟨_, .concat a rest⟩ => (splitFields (n + 1) ⟨_, rest⟩).map fun fs => ⟨_, a⟩ :: fs
  | _, _ => none

/-- The typed term a packed field is the field of: a Bool is packed as
`mux b 1#1 0#1`. -/
def unField : MixedGateBinder → BitsTerm → Option AnyTerm
  | .bool, ⟨_, .mux c _ _⟩ => some ⟨.bool, c⟩
  | .bits _, ⟨w, t⟩ => some ⟨.bits w, t⟩
  | _, _ => none

/-! ## Data as expressions -/

def natL (n : Nat) : Lean.Expr := mkRawNatLit n

def listE (ty : Lean.Expr) (xs : List Lean.Expr) (u : Level := .zero) : Lean.Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [u]) ty x acc)
    (mkApp (mkConst ``List.nil [u]) ty)

def stypeE : SType → Lean.Expr
  | .bool => mkConst ``SType.bool
  | .bits w => mkApp (mkConst ``SType.bits) (natL w)

def binaryE : Binary → Lean.Expr
  | .add => mkConst ``Binary.add | .sub => mkConst ``Binary.sub | .mul => mkConst ``Binary.mul
  | .and => mkConst ``Binary.and | .or => mkConst ``Binary.or | .xor => mkConst ``Binary.xor
  | .shr => mkConst ``Binary.shr | .shl => mkConst ``Binary.shl

def compareKindE : SignalCompareKind → Lean.Expr
  | .ult => mkConst ``SignalCompareKind.ult | .ule => mkConst ``SignalCompareKind.ule
  | .slt => mkConst ``SignalCompareKind.slt | .sle => mkConst ``SignalCompareKind.sle
  | .eq => mkConst ``SignalCompareKind.eq

def boolBinKindE : SignalBoolBinKind → Lean.Expr
  | .band => mkConst ``SignalBoolBinKind.band | .bor => mkConst ``SignalBoolBinKind.bor
  | .bxor => mkConst ``SignalBoolBinKind.bxor

def appBool2E' : AppBool2 → Lean.Expr
  | .andNot => mkConst ``AppBool2.andNot | .notAnd => mkConst ``AppBool2.notAnd
  | .nor => mkConst ``AppBool2.nor

def termE : {s : SType} → Term s → Lean.Expr
  | _, .boolInput j => mkApp (mkConst ``Term.boolInput) (natL j)
  | _, .bitsInput w j => mkApp2 (mkConst ``Term.bitsInput) (natL w) (natL j)
  | _, .boolLit b => mkApp (mkConst ``Term.boolLit) (toExpr b)
  | _, .bitsLit w v => mkApp2 (mkConst ``Term.bitsLit) (natL w) (natL v)
  | _, .bitsNum w v => mkApp2 (mkConst ``Term.bitsNum) (natL w) (natL v)
  | _, .binary op (w := w) a b =>
    mkApp4 (mkConst ``Term.binary) (binaryE op) (natL w) (termE a) (termE b)
  | _, .compare op (w := w) a b =>
    mkApp4 (mkConst ``Term.compare) (compareKindE op) (natL w) (termE a) (termE b)
  | _, .boolBinary op a b =>
    mkApp3 (mkConst ``Term.boolBinary) (boolBinKindE op) (termE a) (termE b)
  | _, .boolNot a => mkApp (mkConst ``Term.boolNot) (termE a)
  | _, .boolEq a b => mkApp2 (mkConst ``Term.boolEq) (termE a) (termE b)
  | s, .mux c a b => mkApp4 (mkConst ``Term.mux) (stypeE s) (termE c) (termE a) (termE b)
  | _, .setw (w := w) w' a => mkApp3 (mkConst ``Term.setw) (natL w) (natL w') (termE a)
  | _, .slice nm start len (w := w) a =>
    mkApp5 (mkConst ``Term.slice) (toExpr nm) (natL start) (natL len) (natL w) (termE a)
  | _, .concat (m := m) (n := n) a b =>
    mkApp4 (mkConst ``Term.concat) (natL m) (natL n) (termE a) (termE b)
  | _, .concatLitHi k v (n := n) b =>
    mkApp4 (mkConst ``Term.concatLitHi) (natL k) (natL v) (natL n) (termE b)
  | _, .concatLitLo (m := m) a k v =>
    mkApp4 (mkConst ``Term.concatLitLo) (natL m) (termE a) (natL k) (natL v)
  | _, .zextMap nm k (n := n) a =>
    mkApp4 (mkConst ``Term.zextMap) (toExpr nm) (natL k) (natL n) (termE a)
  | _, .sliceF nm start len (w := w) a =>
    mkApp5 (mkConst ``Term.sliceF) (toExpr nm) (natL start) (natL len) (natL w) (termE a)
  | _, .appCompare op (w := w) a b =>
    mkApp4 (mkConst ``Term.appCompare) (compareKindE op) (natL w) (termE a) (termE b)
  | _, .appBool op a b => mkApp3 (mkConst ``Term.appBool) (boolBinKindE op) (termE a) (termE b)
  | _, .appBool2 f a b => mkApp3 (mkConst ``Term.appBool2) (appBool2E' f) (termE a) (termE b)

def stypeT : Lean.Expr := mkConst ``SType
/-- `fun s => Term s`. -/
def termFam : Lean.Expr :=
  .lam `s stypeT (mkApp (mkConst ``Tools.ShippingUnifiedSource.Term) (.bvar 0)) .default
/-- `Σ s : SType, Term s`. -/
def anyTermT : Lean.Expr := mkApp2 (mkConst ``Sigma [.zero, .zero]) stypeT termFam

def anyTermE (t : AnyTerm) : Lean.Expr :=
  mkApp4 (mkConst ``Sigma.mk [.zero, .zero]) stypeT termFam (stypeE t.1) (termE t.2)

def termsE : List AnyTerm → Lean.Expr
  | [] => mkConst ``Terms.nil
  | t :: rest =>
    mkApp4 (mkConst ``Terms.cons) (stypeE t.1) (listE stypeT (rest.map fun r => stypeE r.1))
      (termE t.2) (termsE rest)

def binderKindE : MixedGateBinder → Lean.Expr
  | .domain => mkConst ``MixedGateBinder.domain
  | .bool => mkConst ``MixedGateBinder.bool
  | .bits w => mkApp (mkConst ``MixedGateBinder.bits) (natL w)

def binderE (b : Name × MixedGateBinder) : Lean.Expr :=
  mkApp4 (mkConst ``Prod.mk [.zero, .zero]) (mkConst ``Lean.Name) (mkConst ``MixedGateBinder)
    (toExpr b.1) (binderKindE b.2)

def binderT : Lean.Expr :=
  mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Lean.Name) (mkConst ``MixedGateBinder)

def hwTypeE : Sparkle.IR.Type.HWType → Option Lean.Expr
  | .bit => some (mkConst ``Sparkle.IR.Type.HWType.bit)
  | .bitVector w => some (mkApp (mkConst ``Sparkle.IR.Type.HWType.bitVector) (natL w))
  | _ => none

def resetKindE : Sparkle.IR.Type.ResetKind → Lean.Expr
  | .synchronous => mkConst ``Sparkle.IR.Type.ResetKind.synchronous
  | .asynchronous => mkConst ``Sparkle.IR.Type.ResetKind.asynchronous

def layoutE (l : Layout) : Option Lean.Expr := do
  let outs ← l.outs.mapM fun o => do
    let ty ← hwTypeE o.ty
    some (mkApp4 (mkConst ``OutField.mk) (toExpr o.name) (natL o.lo) (natL o.width) ty)
  let slots := l.slots.map fun f =>
    mkApp3 (mkConst ``SlotField.mk) (natL f.lo) (natL f.width) (natL f.init)
  some (mkApp4 (mkConst ``Layout.mk) (listE (mkConst ``SlotField) slots)
    (listE (mkConst ``OutField) outs) (resetKindE l.resetKind) (natL l.lets))

def natListE (xs : List Nat) : Lean.Expr := listE (mkConst ``Nat) (xs.map natL)

/-- The kind of an output port. -/
def outKind (o : OutField) : MixedGateBinder :=
  match o.ty with
  | .bit => .bool
  | _ => .bits o.width

/-! ## The command -/

/-- The data read off a declaration. -/
structure Read where
  shape : MachineShape
  entry : ConstantInfo
  nIn : Nat
  dom : Lean.Expr
  srcDom : Lean.Expr
  bposL : List Nat
  vposL : List Nat
  vwL : List Nat
  ls : List AnyTerm
  outs : List AnyTerm
  nexts : List AnyTerm
  ctor? : Option Name
  sel? : Option (Name × Nat × Nat)
  outNames : List String
  /-- The declaration's own binders (the data's inputs are these plus one
  per `@[hardware_module]` call). -/
  nDecl : Nat
  /-- `let`s in front of the root (sub-machines bound before the `circuit do`). -/
  rootLets : Nat
  /-- The root is a `runCircuitH` (possibly under one projection): the enclosing machine. -/
  hasOuter : Bool
  /-- The result is a tuple: its components' kinds (one port `out`, packed). -/
  tuple : Option (List MixedGateBinder) := none

/-- A declaration with sub-machines, or whose root is not one `runCircuitH`:
the endpoint goes through `machine_trace_of_nested`. -/
def Read.nested (r : Read) : Bool :=
  r.shape.runs.length != 1 || r.rootLets != 0 || !r.hasOuter

def readMachine (declName : Name) : MetaM Read := do
  let env ← getEnv
  let ci ← getConstInfo declName
  unless ci.levelParams.isEmpty do throwError "{declName}: universe parameters"
  let senv := structEnv env
  let entry := entryConst true false [] ci (instancePredicate env) (userInliner env) senv
  -- the real entry takes the machine route only when both combinational
  -- gates miss (`synthesizeFromConst`; the `MachineDefines` boundary)
  if (certifiedShape? false [] entry).isSome ||
      (mixedCertifiedShape? false [] entry (instancePredicate env)).isSome then
    throwError "{declName}: a combinational gate takes it, not the machine route"
  let some shape := machineShape? false [] entry senv
    | throwError "{declName}: not a machine shape"
  let some entryV := entry.value? | throwError "{declName}: no value"
  -- a tuple-typed input is its packed port, as the reader reads it (`MachTupleIn`)
  let some (bsIn, entryBody) := mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV)
    | throwError "{declName}: binders"
  -- the root's `let`s floated out of a projection, as the reader does
  let entryBody := Sparkle.Compiler.MachRawSurface.rootFloat entryBody
  let nDecl := bsIn.length
  let nIn := nDecl + shape.insts.length
  let nSlots := shape.layout.slots.length
  let nLets := shape.layout.lets
  let binders := shape.binders
  unless binders.length == nIn + nSlots + nLets do throwError "{declName}: binder count"
  let (rootLets, sel?, run?, _) := machRoot senv.proj entryBody []
  -- the domain: the enclosing machine's, else the first sub-machine's
  -- the domain, and how many root `let`s enclose the expression it is read from
  let (srcDom, depth) ← match run? with
    | some run => pure (run.getAppArgs[0]!, rootLets.length)
    | none =>
      match entryBody.find? fun t => t.isAppOfArity ``Sparkle.Core.runCircuitH 8 with
      | some run => pure (run.getAppArgs[0]!, rootLets.length)
      | none =>
        -- a hand-written `Signal.loop`, bound by the `k`-th root `let`
        let rec loopLet (k : Nat) : Lean.Expr → Option (Lean.Expr × Nat)
          | .letE _ _ v b _ =>
            if v.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then some (v.getAppArgs[0]!, k)
            else loopLet (k + 1) b
          | _ => none
        match loopLet 0 entryBody with
        | some r => pure r
        | none =>
          -- no state at all: the domain of the result type
          let rec resDom : Lean.Expr → Nat → Option (Lean.Expr × Nat)
            | .forallE _ _ b _, k => resDom b (k + 1)
            | e, _ => match e.getAppFn, e.getAppArgs.toList with
              | .const ``Sparkle.Core.Signal.Signal _, [d, _] => some (d, 0)
              -- a structure of Signals over its one parameter, the domain
              | .const s _, [d] =>
                if (senv.fields s).isSome then some (d, 0) else none
              | _, _ => none
          match resDom entry.type 0 with
          | some r => pure r
          | none => throwError "{declName}: no state and no Signal result type"
  -- a domain binder is a bound variable at the root; the placeholder the
  -- reader gives it is the binder's position from the end
  let srcDom' ← match srcDom with
    | .bvar j =>
      if j < depth then throwError "{declName}: the domain is a root let"
      else pure (machIn (j - depth))
    | e => pure e
  let some (dom, _) := machDom? (shape.insts.length + nSlots + nLets) srcDom'
    | throwError "{declName}: domain"
  let tup? := machTupleKinds? entry.type
  let some (ctor?, outKinds) := (match tup? with
      | some ks => some (none, [("out", MixedGateBinder.bits (ks.map machWidth).sum)])
      | none => machOuts? senv entry.type) | throwError "{declName}: outputs"
  let kinds := binders.map (·.2)
  let c := Binders.ofKinds kinds
  let idx := (List.range kinds.length).zip kinds
  let bposL := idx.filterMap fun (p, k) => if k == .bool then some p else none
  let vposL := idx.filterMap fun (p, k) => match k with | .bits _ => some p | _ => none
  let vwL := idx.filterMap fun (_, k) => match k with | .bits w => some w | _ => none
  let some whole := unq c shape.body | throwError "{declName}: the body is not read as a term"
  let ⟨.bits W, whole⟩ := whole | throwError "{declName}: the body is a Bool"
  let some (letFs, core) := splitLets nLets ⟨W, whole⟩ | throwError "{declName}: let fields"
  let nOuts := shape.layout.outs.length
  let some fs := splitFields (nOuts + nSlots) core | throwError "{declName}: core fields"
  let typed (ks : List MixedGateBinder) (fs : List BitsTerm) : MetaM (List AnyTerm) :=
    (ks.zip fs).mapM fun (k, f) =>
      match unField k f with
      | some t => pure t
      | none => throwError "{declName}: a field does not have its binder's kind"
  let ls ← typed (kinds.drop (nIn + nSlots)) letFs
  let outs ← typed (shape.layout.outs.map outKind) (fs.take nOuts)
  let nexts ← typed ((kinds.drop nIn).take nSlots) (fs.drop nOuts)
  -- the reading, checked here already (the kernel checks it again)
  let packed := (packLets (ls.map fun l => toField l.1 l.2)
    (packAll ((outs.map fun t => toField t.1 t.2) ++ nexts.map fun t => toField t.1 t.2)).2).2
  let q := quote dom (fun j => inputExpr binders.length (bposL.getD j 0))
    (fun j => inputExpr binders.length (vposL.getD j 0)) packed
  unless q.equal shape.body do
    throwError "{declName}: the terms read off the body do not quote back to it"
  return { shape, entry, nIn, dom, srcDom, bposL, vposL, vwL, ls, outs, nexts, ctor?, sel?,
           outNames := outKinds.map (·.1), nDecl, rootLets := rootLets.length,
           hasOuter := run?.isSome, tuple := tup? }

def dataE (r : Read) : MetaM Lean.Expr := do
  let body ← match reflExpr r.shape.body with
    | .ok b => pure b
    | .error msg => throwError msg
  let dom ← match reflExpr r.dom with
    | .ok b => pure b
    | .error msg => throwError msg
  let some layout := layoutE r.shape.layout | throwError "an output type is not a bit vector"
  let natPairT := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Nat) (mkConst ``Nat)
  let runs := listE natPairT (r.shape.runs.map fun (a, b) =>
    mkApp4 (mkConst ``Prod.mk [.zero, .zero]) (mkConst ``Nat) (mkConst ``Nat) (natL a) (natL b))
  let instT := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Lean.Name)
    (mkApp2 (mkConst ``Prod [.zero, .zero]) (mkApp (mkConst ``List [.zero]) (mkConst ``Nat))
      (mkConst ``MixedGateBinder))
  let insts := listE instT (r.shape.insts.map fun (c, js, k) =>
    mkApp4 (mkConst ``Prod.mk [.zero, .zero]) (mkConst ``Lean.Name)
      (mkApp2 (mkConst ``Prod [.zero, .zero]) (mkApp (mkConst ``List [.zero]) (mkConst ``Nat))
        (mkConst ``MixedGateBinder))
      (toExpr c)
      (mkApp4 (mkConst ``Prod.mk [.zero, .zero]) (mkApp (mkConst ``List [.zero]) (mkConst ``Nat))
        (mkConst ``MixedGateBinder) (natListE js) (binderKindE k)))
  let loops := listE natPairT (r.shape.loops.map fun (a, b) =>
    mkApp4 (mkConst ``Prod.mk [.zero, .zero]) (mkConst ``Nat) (mkConst ``Nat) (natL a) (natL b))
  let shape := mkApp7 (mkConst ``MachineShape.mk) (listE binderT (r.shape.binders.map binderE))
    body layout runs insts loops (listE (mkConst ``String) (r.shape.instFields.map toExpr))
  return mkAppN (mkConst ``MachineData.mk)
    #[shape, natL r.nIn, dom, natListE r.bposL, natListE r.vposL, natListE r.vwL,
      listE stypeT (r.nexts.map fun t => stypeE t.1), listE anyTermT (r.ls.map anyTermE),
      listE anyTermT (r.outs.map anyTermE), termsE r.nexts]

/-- Progress lines, to the file `SPARKLE_MACHINE_PROGRESS` names (a command's
own output is shown only when it ends). -/
def progress (msg : String) : MetaM Unit := do
  if let some path ← IO.getEnv "SPARKLE_MACHINE_PROGRESS" then
    let h ← IO.FS.Handle.mk path .append
    h.putStrLn s!"{← IO.monoMsNow} {msg}"
    h.flush

def addDef (name : Name) (type value : Lean.Expr) : MetaM Unit :=
  addDecl (.defnDecl
    { name, levelParams := [], type, value, hints := .abbrev, safety := .safe })

/-- A proof of an equation (under binders) by `Eq.refl`, on the side `side`
selects. -/
def reflProof (stmt : Lean.Expr) (left : Bool) : MetaM Lean.Expr :=
  forallTelescope stmt fun xs eq => do
    let some (α, lhs, rhs) := eq.eq? | throwError "not an equation: {eq}"
    let u ← getLevel α
    mkLambdaFVars xs (mkApp2 (mkConst ``Eq.refl [u]) α (if left then lhs else rhs))

/-- One observation per output port of a Signal / structure value `v` of
kinds `ks`: `fun t => encodeBool (field.val t)` or `BitVec.toNat (field.val t)`. -/
def observations (declName : Name) (D v : Lean.Expr) (fields : List (Option Name))
    (ks : List MixedGateBinder) : MetaM (List Lean.Expr) := do
  let nat := mkConst ``Nat
  (fields.zip ks).mapM fun (fn, k) => do
    let field ← match fn with
      | none => pure v
      | some f => mkProjection v f
    withLocalDeclD `t nat fun t => do
      let val (α : Lean.Expr) :=
        mkApp (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.val [.zero]) D α field) t
      let e ← match k with
        | .bool => pure (mkApp (mkConst ``Tools.ShippingMuxLoweringSoundness.encodeBool)
            (val (mkConst ``Bool)))
        | .bits w =>
          let wE := mkNatLit w
          pure (mkApp2 (mkConst ``BitVec.toNat) wE (val (mkApp (mkConst ``BitVec) wE)))
        | .domain => throwError "{declName}: an output is a domain"
      mkLambdaFVars #[t] e

/-- The structure field behind output `nm` (a pair result's ports are
`out_0`/`out_1`, its fields `fst`/`snd`). -/
def outFieldName (r : Read) (nm : String) : Name :=
  if r.ctor? == some ``Prod.mk then (if nm == "out_0" then `fst else `snd)
  else Name.mkSimple nm

/-- The fields of the result type `rho` the output ports read: none for a
Signal, every field for a structure result, the selected field under a
projection. -/
def resultFields (declName : Name) (r : Read) (rho : Lean.Expr) : MetaM (List (Option Name)) := do
  let env ← getEnv
  let rhoHead := rho.getAppFn.constName?.getD .anonymous
  if rhoHead == ``Sparkle.Core.Signal.Signal then pure [none]
  else if r.ctor?.isSome then pure (r.outNames.map fun nm => some (outFieldName r nm))
  else match r.sel? with
    | some (_, _, idx) =>
      match (getStructureFields env rhoHead)[idx]? with
      | some f => pure [some f]
      | none => throwError "{declName}: the selected field of {rhoHead}"
    | none => throwError "{declName}: the result type {rhoHead}"

/-- `fun i r => [observations of r]`: what `src` observes of a result. -/
def resultObs (declName : Name) (r : Read) (i D rho : Lean.Expr) : MetaM Lean.Expr := do
  let nat := mkConst ``Nat
  let fieldNames ← resultFields declName r rho
  withLocalDeclD `r rho fun res => do
    let fs ← observations declName D res fieldNames (r.shape.layout.outs.map outKind)
    mkLambdaFVars #[i, res] (listE (← mkArrow nat nat) fs)

/-! ### `@[hardware_module]` calls

The transition reads a call's output as an input (position `nDecl + k`);
the source reads the call. The endpoint's extension (`extendBits`, one per
call) puts the call — over the state signal `S`, and the sub-machines'
results over their state signals `Ss` — at that position; `machine_inst_k`
checks (by `rfl`) that the call is pointwise in the states, which gives the
theorems' `hext`. -/

/-- Walk `e` in the reader's order, applying `onCall` to every full
application of a `@[hardware_module]` with one Signal result. -/
partial def walkInsts (senv : StructEnv) (onCall : Lean.Expr → MetaM Lean.Expr) :
    Lean.Expr → MetaM Lean.Expr
  | e@(.app ..) => do
    if (machInstCall? senv e).isSome then onCall e else
    let f ← walkInsts senv onCall e.appFn!
    let a ← walkInsts senv onCall e.appArg!
    return .app f a
  | .letE nm ty v b _ => do
    let ty' ← walkInsts senv onCall ty
    let v' ← walkInsts senv onCall v
    withLetDecl nm ty' v' fun x => do
      let b' ← walkInsts senv onCall (b.instantiate1 x)
      mkLetFVars #[x] b' (usedLetOnly := false)
  | .lam nm ty b bi => do
    let ty' ← walkInsts senv onCall ty
    withLocalDecl nm bi ty' fun x => do
      let b' ← walkInsts senv onCall (b.instantiate1 x)
      mkLambdaFVars #[x] b'
  | .forallE nm ty b bi => do
    let ty' ← walkInsts senv onCall ty
    withLocalDecl nm bi ty' fun x => do
      let b' ← walkInsts senv onCall (b.instantiate1 x)
      mkForallFVars #[x] b'
  | .mdata m b => do return .mdata m (← walkInsts senv onCall b)
  | .proj n k b => do return .proj n k (← walkInsts senv onCall b)
  | e => pure e

/-- The calls of `e` in reading order, each once (a repeat — `circuit do`
copies its `let`s — is the same call), with the outer `let`s substituted. -/
def collectInsts (senv : StructEnv) (e : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let acc ← IO.mkRef (#[] : Array Lean.Expr)
  let _ ← walkInsts senv (fun c => do
    let cZ ← zetaReduce c
    unless (← acc.get).contains cZ do acc.modify (·.push cZ)
    pure c) e
  acc.get

/-- The extension and its pointwiseness proof for the calls `calls` (over the
free variables `frees`, which `subst` maps to their value over the state
signals and `substC` to their value over the constant state signals):
`ext := fun i bools bits S [Ss] => extendBits (… bits …) (nDecl + k) w_k (call_k)`,
`machine_inst_k : ∀ i bools bits S [Ss] t, (call_k over S).val t = (call_k over
the constants).val t` by `rfl`, and `hext` from `extendBits_val`. Returns the
extension (closed over the given binders) and the `hext` proof. -/
def instExtension (declName : Name) (r : Read) (D : Lean.Expr) (binders : Array Lean.Expr)
    (t : Lean.Expr) (bits : Lean.Expr) (calls : Array Lean.Expr)
    (subst substC : Nat → Lean.Expr → Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  unless calls.size == r.shape.insts.length do
    throwError "{declName}: {calls.size} hardware-module calls found, the compiler read {r.shape.insts.length}"
  let sigBV (w : Nat) := mkApp2 (mkConst ``Sparkle.Core.Signal.Signal [.zero]) D
    (mkApp (mkConst ``BitVec) (mkNatLit w))
  let valAt (w : Nat) (c tt : Lean.Expr) :=
    mkApp (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.val [.zero]) D
      (mkApp (mkConst ``BitVec) (mkNatLit w)) c) tt
  -- binders without `t` (the extension) and with `t` (the facts)
  let bindersT := binders.push t
  let mut extS := bits
  let mut extC := bits
  let mut hext : Lean.Expr := ← withLocalDeclD `j (mkConst ``Nat) fun j =>
    withLocalDeclD `n (mkConst ``Nat) fun n => do
      let v := mkApp (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.val [.zero]) D
        (mkApp (mkConst ``BitVec) n) (mkApp2 bits j n)) t
      mkLambdaFVars #[j, n] (mkApp2 (mkConst ``Eq.refl [.one]) (mkApp (mkConst ``BitVec) n) v)
  for k in [0:calls.size] do
    let some (_, _, kind) := r.shape.insts[k]? | throwError "{declName}: call {k}"
    let .bits w := kind | throwError "{declName}: call {k} is not a BitVec"
    let c := calls[k]!
    let cS := subst k c
    let cC := substC k c
    let pos := r.nDecl + k
    -- the call over the state signal(s), for the linked composition
    let callV ← mkLambdaFVars binders cS
    addDef (declName ++ Name.mkSimple s!"machineCall_{k}") (← inferType callV) callV
    -- the pointwiseness fact, checked by the kernel
    let stmt ← mkForallFVars bindersT
      (mkApp3 (mkConst ``Eq [.one]) (mkApp (mkConst ``BitVec) (mkNatLit w)) (valAt w cS t)
        (valAt w cC t))
    let name := declName ++ (Name.mkSimple s!"machine_inst_{k}")
    let proof ← reflProof stmt true
    try
      addDecl (.thmDecl { name, levelParams := [], type := stmt, value := proof })
    catch ex =>
      throwError "{declName}: the call {k} is not pointwise in the state (kernel): {ex.toMessageData}"
    let fact := mkAppN (mkConst name) bindersT
    hext := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits_val)
      #[D, extS, extC, mkNatLit pos, mkNatLit w, cS, cC, t, hext, fact]
    extS := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits) #[D, extS, mkNatLit pos, mkNatLit w, cS]
    extC := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits) #[D, extC, mkNatLit pos, mkNatLit w, cC]
    let _ := sigBV
  return (extS, hext)

/-! ### Sub-machines

A `runCircuitH` inside the root — in a `let` in front of the `circuit do`,
in a `let` of its body, in an argument — is a sub-machine. The enclosing
body is written as a function of the tuple of their results (`body₂ regs
rs`, each sub-machine replaced by its component of `rs`), each sub-machine
as a function of the enclosing handles (`InnerT`), in the order the compiler
reads them: the root `let`s' values in order, then the body, left to right. -/

/-- A sub-machine: a `runCircuitH`, or a hand-written `Signal.loop`. -/
def isSubApp (e : Lean.Expr) : Bool :=
  e.isAppOfArity ``Sparkle.Core.runCircuitH 8 || e.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4

/-- Walk an expression in the compiler's reading order (a `let`'s value
before its body, a function before its argument), with the local context
extended at every binder, applying `onRun` to every `runCircuitH`
application (which is not entered). -/
partial def walkRuns (onRun : Lean.Expr → MetaM Lean.Expr) : Lean.Expr → MetaM Lean.Expr
  | e@(.app ..) => do
    if isSubApp e then onRun e else
    let f ← walkRuns onRun e.appFn!
    let a ← walkRuns onRun e.appArg!
    return .app f a
  | .letE nm ty v b nd => do
    let ty' ← walkRuns onRun ty
    let v' ← walkRuns onRun v
    -- the value is kept visible (`zetaReduce` substitutes it in a sub-machine)
    let _ := nd
    withLetDecl nm ty' v' fun x => do
      let b' ← walkRuns onRun (b.instantiate1 x)
      mkLetFVars #[x] b' (usedLetOnly := false)
  | .lam nm ty b bi => do
    let ty' ← walkRuns onRun ty
    withLocalDecl nm bi ty' fun x => do
      let b' ← walkRuns onRun (b.instantiate1 x)
      mkLambdaFVars #[x] b'
  | .forallE nm ty b bi => do
    let ty' ← walkRuns onRun ty
    withLocalDecl nm bi ty' fun x => do
      let b' ← walkRuns onRun (b.instantiate1 x)
      mkForallFVars #[x] b'
  | .mdata m b => do return .mdata m (← walkRuns onRun b)
  | .proj n k b => do return .proj n k (← walkRuns onRun b)
  | e => pure e

/-- `walkRuns` and `walkInsts` in one pass, in the compiler's reading order:
a `runCircuitH` goes to `onRun` (not entered), a `@[hardware_module]` call
first has the sub-machines in its arguments replaced (`onRun`, the compiler
reads the arguments before the call) and then goes to `onCall`. -/
partial def walkInstsRuns (senv : StructEnv) (onRun onCall : Lean.Expr → MetaM Lean.Expr) :
    Lean.Expr → MetaM Lean.Expr
  | e@(.app ..) => do
    if isSubApp e then onRun e else
    if (machInstCall? senv e).isSome then onCall (← walkRuns onRun e) else
    let f ← walkInstsRuns senv onRun onCall e.appFn!
    let a ← walkInstsRuns senv onRun onCall e.appArg!
    return .app f a
  | .letE nm ty v b _ => do
    let ty' ← walkInstsRuns senv onRun onCall ty
    let v' ← walkInstsRuns senv onRun onCall v
    withLetDecl nm ty' v' fun x => do
      let b' ← walkInstsRuns senv onRun onCall (b.instantiate1 x)
      mkLetFVars #[x] b' (usedLetOnly := false)
  | .lam nm ty b bi => do
    let ty' ← walkInstsRuns senv onRun onCall ty
    withLocalDecl nm bi ty' fun x => do
      let b' ← walkInstsRuns senv onRun onCall (b.instantiate1 x)
      mkLambdaFVars #[x] b'
  | .forallE nm ty b bi => do
    let ty' ← walkInstsRuns senv onRun onCall ty
    withLocalDecl nm bi ty' fun x => do
      let b' ← walkInstsRuns senv onRun onCall (b.instantiate1 x)
      mkForallFVars #[x] b'
  | .mdata m b => do return .mdata m (← walkInstsRuns senv onRun onCall b)
  | .proj n k b => do return .proj n k (← walkInstsRuns senv onRun onCall b)
  | e => pure e

/-- The slot sorts of a `runCircuitH`'s slot types, as an expression. -/
def slotSortsE (declName : Name) (αs : Lean.Expr) : MetaM (List SType × Lean.Expr) := do
  let some kinds := machSlotKinds (Sparkle.Compiler.MachRawSurface.zetaAll αs) | throwError "{declName}: a sub-machine's slot types"
  let ss ← kinds.mapM fun k => match sortOf k with
    | some s => pure s
    | none => throwError "{declName}: a sub-machine's slot kind"
  return (ss, listE stypeT (ss.map stypeE))

/-- Component `j` of a right-nested tuple. -/
def tupleProj (rs : Lean.Expr) (j : Nat) : Lean.Expr :=
  .proj ``Prod 0 ((List.range j).foldl (fun acc _ => .proj ``Prod 1 acc) rs)

/-- The machine's typed tuple from a loop state tuple `x` of `n` components. -/
def loopSigma (x : Lean.Expr) (n : Nat) : MetaM Lean.Expr := do
  let mut comps : Array Lean.Expr := #[]
  let mut cur := x
  for k in [0:n] do
    if k + 1 == n then comps := comps.push cur
    else
      comps := comps.push (← mkAppM ``Prod.fst #[cur])
      cur ← mkAppM ``Prod.snd #[cur]
  let mut hl := mkConst ``Unit.unit
  for c in comps.reverse do
    hl ← mkAppM ``Prod.mk #[c, hl]
  return hl

/-- The loop state a typed state tuple stands for: the inverse of `loopSigma`
(`(h.1, (h.2.1, … h.2…2.1))`). -/
def loopDec (h : Lean.Expr) (n : Nat) : MetaM Lean.Expr := do
  let mut comps : Array Lean.Expr := #[]
  let mut cur := h
  for _ in [0:n] do
    comps := comps.push (← mkAppM ``Prod.fst #[cur])
    cur ← mkAppM ``Prod.snd #[cur]
  let mut acc := comps.back!
  for c in comps.pop.reverse do
    acc ← mkAppM ``Prod.mk #[c, acc]
  return acc

/-- A proof of `∀ i bools bits, Tele.InitOk (l.at i bools bits)`: every
loop's body at cycle 0 is its reset tuple, by evaluation. -/
partial def initOkProof (T : Lean.Expr) : MetaM Lean.Expr :=
  forallTelescope T fun xs body => do
    let rec go (P : Lean.Expr) : MetaM Lean.Expr := do
      let P ← whnf P
      if P.isConstOf ``True then return mkConst ``True.intro
      match P.and? with
      | some (A, B) =>
        let a ← forallTelescope A fun ys eq => do
          let some (_, _, rhs) := eq.eq? | throwError "InitOk: not an equation"
          mkLambdaFVars ys (← mkExpectedTypeHint (← mkEqRefl rhs) eq)
        return mkApp4 (mkConst ``And.intro) A B a (← go B)
      | none => throwError "InitOk: unexpected {P}"
    mkLambdaFVars xs (← go body)

/-- The reset tuple of a loop, from its registers' initial values. -/
def loopInitsE (regs : List (Lean.Expr × Lean.Expr × Lean.Expr)) : MetaM Lean.Expr := do
  let mut hl := mkConst ``Unit.unit
  for (_, init, _) in regs.reverse do
    hl ← mkAppM ``Prod.mk #[init, hl]
  return hl

/-- The endpoint of a declaration with sub-machines, through
`machine_trace_of_nested`: the theorem applied to the data, the enclosing
machine, the sub-machines, the body with the sub-machines abstracted, the
observations — the hypotheses left are the kernel checks. Returns the
partial application and the checks (name suffix, side of the `rfl`). -/
def nestedProof (declName : Name) (r : Read) (data ι i D bools bits src inst : Lean.Expr) :
    MetaM (Lean.Expr × Name × List (Name × Bool) × Option Lean.Expr) := do
  let env ← getEnv
  let senv := structEnv env
  let (rootLets, _, run?, root) := machRoot senv.proj inst []
  let nat := mkConst ``Nat
  let domF ← mkLambdaFVars #[i] D
  let tysE (ss : Lean.Expr) := mkApp (mkConst ``Tools.ShippingMachineDenote.tys) ss
  let hlistE (ts : Lean.Expr) := mkApp (mkConst ``HList) ts
  let sigListE (ts : Lean.Expr) := mkApp2 (mkConst ``Sparkle.Core.Circuit.SigList) D ts
  let regListE (ts : Lean.Expr) :=
    mkApp4 (mkConst ``Sparkle.Core.RegList) D (hlistE ts) (sigListE ts) ts
  -- the enclosing machine
  let (ss₂E, inhab₂, inits₂, regsTy, rho, chain?) ← match run? with
    | some run =>
      let a := run.getAppArgs
      let (_, ss₂E) ← slotSortsE declName a[1]!
      if a[6]!.hasFVar || a[5]!.hasFVar then
        throwError "{declName}: the reset values depend on a binder"
      pure (ss₂E, a[5]!, a[6]!, a[7]!.bindingDomain!, a[2]!, some a[7]!.bindingBody!)
    | none =>
      let ss₂E := listE stypeT []
      pure (ss₂E, mkConst ``instInhabitedPUnit [.one], mkConst ``Unit.unit,
        regListE (tysE ss₂E), ← inferType inst, none)
  -- the root lets and the body, as one expression under the regs binder
  -- (the body's `regs` variable becomes the binder, the root lets move
  -- inside it)
  withLocalDeclD `regs regsTy fun regsF => do
  let core : Lean.Expr := match chain? with
    | some chain => chain.instantiate1 regsF
    | none => root
  let e0 := rootLets.foldr (fun (nm, ty, v) acc => Lean.Expr.letE nm ty v acc false) core
  -- pass A: the sub-machines, in reading order; a `runCircuitH` that repeats
  -- an earlier one (the same term once the `let`s are substituted — `circuit
  -- do` copies its `let`s into every write and into the result) is that
  -- machine, as the compiler reads it
  let runsRef ← IO.mkRef (#[] : Array (Lean.Expr × Lean.Expr))
  let occRef ← IO.mkRef (#[] : Array Nat)
  let _ ← walkRuns (fun run => do
    let runZ ← zetaReduce run
    let known ← runsRef.get
    match known.findIdx? (fun (z, _) => z == runZ) with
    | some j => occRef.modify (·.push j)
    | none =>
      let inner ← if runZ.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then
          pure (mkConst ``Unit.unit)
        else do
          let a := runZ.getAppArgs
          let (_, ssE) := (← slotSortsE declName a[1]!)
          if a[6]!.hasFVar || a[5]!.hasFVar then
            throwError "{declName}: a sub-machine's reset values depend on a binder"
          let ρE ← mkLambdaFVars #[i] a[2]!
          let bodyE ← mkLambdaFVars #[i, bools, bits, regsF] a[7]!
          pure (mkAppN (mkConst ``InnerT.mk) #[ι, domF, ss₂E, ssE, ρE, a[5]!, a[6]!, bodyE])
      occRef.modify (·.push known.size)
      runsRef.modify (·.push (runZ, inner))
    pure run) e0
  let inners := (← runsRef.get).map (·.2)
  let occ ← occRef.get
  let innerT := mkApp3 (mkConst ``InnerT) ι domF ss₂E
  let lE := listE innerT inners.toList .one
  let nSubs := r.shape.runs.length - (if run?.isSome then 1 else 0) + r.shape.loops.length
  unless inners.size == nSubs do
    throwError "{declName}: {inners.size} sub-machines found, the compiler read {nSubs}"
  -- a CHAIN: a sub-machine reading an earlier one's result (its body holds
  -- the earlier `runCircuitH`): the sub-machines are a telescope (`TeleT`),
  -- each body over the earlier results (`prev`, latest first)
  let runsZ0 := (← runsRef.get).map (·.1)
  let isLoopZ (k : Nat) : Bool := runsZ0[k]!.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4
  -- a chain, or a hand-written loop among the sub-machines: the telescope
  let chain := (List.range runsZ0.size).any (fun j =>
    (List.range j).any fun k => runsZ0[k]!.occurs runsZ0[j]!) ||
    (List.range runsZ0.size).any isLoopZ
  let resultT (k : Nat) : Lean.Expr :=
    if isLoopZ k then mkApp2 (mkConst ``Sparkle.Core.Signal.Signal [.zero]) D runsZ0[k]!.getAppArgs[1]!
    else runsZ0[k]!.getAppArgs[2]!
  let typeT := mkSort (.succ .zero)
  let preList (j : Nat) : Lean.Expr :=
    listE typeT ((List.range j).reverse.map resultT) .one
  let preE (j : Nat) : MetaM Lean.Expr := mkLambdaFVars #[i] (preList j)
  -- each body with the earlier sub-machines replaced by `prev`'s components
  let bodiesC ← (List.range runsZ0.size).mapM fun j =>
    withLocalDeclD `prev (hlistE (preList j)) fun pv => do
      let b := if isLoopZ j then runsZ0[j]!.getAppArgs[3]! else runsZ0[j]!.getAppArgs[7]!
      let b' := if !chain then b else b.replace fun e =>
        (List.range j).findSome? fun k => if e == runsZ0[k]! then some (tupleProj pv (j - 1 - k)) else none
      for k in List.range j do
        if runsZ0[k]!.occurs b' then
          throwError "{declName}: sub-machine {j} reads sub-machine {k} other than by its result"
      mkLambdaFVars #[pv] b'
  let teleE ← if !chain then pure (mkConst ``Unit.unit) else do
    let n := runsZ0.size
    let mut tE := mkAppN (mkConst ``Tools.ShippingMachineTeleNest.TeleT.nil) #[ι, domF, ss₂E, ← preE n]
    for j in (List.range n).reverse do
      let a := runsZ0[j]!.getAppArgs
      if isLoopZ j then
        -- a hand-written loop: its registers read off the zeta-reduced body
        let (α, inhα, f) := (a[1]!, a[2]!, a[3]!)
        let fZ ← zetaReduce f
        let .lam _ _ fb _ := fZ | throwError "{declName}: a loop body is not a function"
        let some regs := machLoopRegs (machLetTail fb) | throwError "{declName}: a loop's registers"
        if regs.any (fun (ty, init, _) => ty.hasLooseBVars || init.hasLooseBVars) then
          throwError "{declName}: a loop's register types or reset values read its state"
        let (_, ssE) ← slotSortsE declName (listE typeT (regs.map (·.1)) .one)
        let n' := regs.length
        let hlT := hlistE (tysE ssE)
        let initsV ← loopInitsE regs
        let inh := mkApp2 (mkConst ``Inhabited.mk [.succ .zero]) hlT initsV
        let encE ← withLocalDeclD `x α fun x => do mkLambdaFVars #[i, x] (← loopSigma x n')
        let decE ← withLocalDeclD `h hlT fun h => do mkLambdaFVars #[i, h] (← loopDec h n')
        let hedE ← withLocalDeclD `h hlT fun h => do
          let lhs := (encE.beta #[i, decE.beta #[i, h]]).headBeta
          mkLambdaFVars #[i, h] (← mkExpectedTypeHint (← mkEqRefl h) (← mkEq lhs h))
        let ρE ← mkLambdaFVars #[i] (resultT j)
        let fE ← mkLambdaFVars #[i, bools, bits, regsF] bodiesC[j]!
        let resE ← withLocalDeclD `prev (hlistE (preList j)) fun pv =>
          withLocalDeclD `L (resultT j) fun L => mkLambdaFVars #[i, bools, bits, regsF, pv, L] L
        tE := mkAppN (mkConst ``Tools.ShippingMachineTeleNest.TeleT.loop)
          #[ι, domF, ss₂E, ← preE j, ssE, inh, ← mkLambdaFVars #[i] α, ← mkLambdaFVars #[i] inhα,
            ρE, encE, decE, hedE, initsV, fE, resE, tE]
        continue
      let (_, ssE) ← slotSortsE declName a[1]!
      let ρE ← mkLambdaFVars #[i] a[2]!
      let bodyE ← mkLambdaFVars #[i, bools, bits, regsF] bodiesC[j]!
      tE := mkAppN (mkConst ``Tools.ShippingMachineTeleNest.TeleT.cons)
        #[ι, domF, ss₂E, ← preE j, ssE, a[5]!, ρE, a[6]!, bodyE, tE]
    pure tE
  -- pass B: the enclosing body, each sub-machine its component of `rs`
  let atsE ← if chain then
      pure (mkAppN (mkConst ``Tools.ShippingMachineTeleNest.TeleT.at)
        #[ι, domF, ss₂E, ← preE 0, teleE, i, bools, bits])
    else pure (mkAppN (mkConst ``ats) #[ι, domF, ss₂E, lE, i, bools, bits])
  let rsTy ← if chain then pure (hlistE (← mkAppM ``Tools.ShippingMachineTele.Tele.ρs #[atsE]))
    else pure (hlistE (mkApp3 (mkConst ``ρs) D (tysE ss₂E) atsE))
  withLocalDeclD `rs rsTy fun rsF => do
  let counter ← IO.mkRef 0
  -- the calls in the compiler's reading order: a call in the enclosing body
  -- (over the handles and `rs`), and at the first occurrence of a
  -- sub-machine the calls of its body (closed over its own handles: `some j`)
  let callsRef ← IO.mkRef (#[] : Array (Option Nat × Lean.Expr))
  let seenRef ← IO.mkRef (#[] : Array Nat)
  let runsZ := (← runsRef.get).map (·.1)
  let senv0 := structEnv env
  let onRun : Lean.Expr → MetaM Lean.Expr := fun _ => do
    let k ← counter.get
    counter.set (k + 1)
    let j := occ[k]!
    unless (← seenRef.get).contains j do
      seenRef.modify (·.push j)
      -- the body with the earlier sub-machines as `prev` (a call reading
      -- `prev` is refused below: `prev` is not a variable the endpoint covers)
      withLocalDeclD `prev (hlistE (preList j)) fun pv => do
      let bodyJ := bodiesC[j]!.bindingBody!.instantiate1 pv
      withLocalDeclD `regsI bodyJ.bindingDomain! fun rI => do
        for c in ← collectInsts senv0 (bodyJ.bindingBody!.instantiate1 rI) do
          if c.containsFVar pv.fvarId! then
            throwError "{declName}: a hardware-module call in sub-machine {j} reads an earlier sub-machine"
          let cl ← mkLambdaFVars #[rI] c
          unless (← callsRef.get).contains (some j, cl) do callsRef.modify (·.push (some j, cl))
    pure (tupleProj rsF j)
  let eB ← walkInstsRuns senv0 onRun (fun c => do
    let cZ ← zetaReduce c
    unless (← callsRef.get).contains (none, cZ) do callsRef.modify (·.push (none, cZ))
    pure c) e0
  let eB ← match chain? with
    | some _ => pure eB
    | none => pure (mkApp4 (mkConst ``Sparkle.Core.Circuit.pure') D (sigListE (tysE ss₂E)) rho eB)
  let body₂ ← mkLambdaFVars #[i, bools, bits, regsF, rsF] eB
  -- the `@[hardware_module]` calls (over the handles and the results), their
  -- extension of the inputs and its pointwiseness
  let hasInsts := !r.shape.insts.isEmpty
  let ctxCalls ← callsRef.get
  let calls := if hasInsts then ctxCalls.map (·.2) else #[]
  let nat := mkConst ``Nat
  let hasExt := hasInsts || chain
  let sigsT ← if chain then mkAppM ``Tools.ShippingMachineTele.Tele.Sigs #[atsE]
    else pure (mkApp3 (mkConst ``Tools.ShippingMachineFuse.Sigs) D (tysE ss₂E) atsE)
  let resultsOnE (regs Ss : Lean.Expr) : MetaM Lean.Expr :=
    if chain then mkAppM ``Tools.ShippingMachineTele.Tele.resultsOn #[regs, atsE, mkConst ``Unit.unit, Ss]
    else pure (mkApp5 (mkConst ``Tools.ShippingMachineFuse.resultsOn) D (tysE ss₂E) regs atsE Ss)
  let (extE, hextE) ← withLocalDeclD `S (mkApp2 (mkConst ``Sparkle.Core.Signal.Signal [.zero]) D
      (hlistE (tysE ss₂E))) fun S =>
    withLocalDeclD `Ss sigsT fun Ss => withLocalDeclD `t nat fun t => do
      let regsS := mkApp3 (mkConst ``Tools.ShippingMachineFuse.regsOf) D (tysE ss₂E) S
      let constS := mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.mk [.zero]) D (hlistE (tysE ss₂E))
        (.lam `u nat (mkApp (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.val [.zero]) D
          (hlistE (tysE ss₂E)) S) t) .default)
      let regsC := mkApp3 (mkConst ``Tools.ShippingMachineFuse.regsOf) D (tysE ss₂E) constS
      let SsC ← if chain then
          mkAppM ``Tools.ShippingMachineTele.Tele.constOf
            #[atsE, ← mkAppM ``Tools.ShippingMachineTele.Tele.valsOf #[atsE, Ss, t]]
        else pure (mkApp4 (mkConst ``Tools.ShippingMachineFuse.constOf) D (tysE ss₂E) atsE
          (mkApp5 (mkConst ``Tools.ShippingMachineFuse.valsOf) D (tysE ss₂E) atsE Ss t))
      -- a sub-machine's call reads its own handles: over its state signal
      let innerRegs (j : Nat) (Ss' : Lean.Expr) : MetaM Lean.Expr := do
        -- a loop's body reads its state signal itself
        if runsZ[j]!.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then return tupleProj Ss' j
        let some (_, ssJ) := runsZ[j]? |>.map (fun z => ((), z.getAppArgs[1]!)) | throwError "{declName}: sub-machine {j}"
        let (_, ssE) ← slotSortsE declName ssJ
        pure (mkApp3 (mkConst ``Tools.ShippingMachineFuse.regsOf) D (tysE ssE) (tupleProj Ss' j))
      let mut opened : Array Lean.Expr := #[]
      let mut openedC : Array Lean.Expr := #[]
      for (ctx, c) in ctxCalls do
        match ctx with
        | none => opened := opened.push c; openedC := openedC.push c
        | some j =>
          opened := opened.push (c.beta #[← innerRegs j Ss])
          openedC := openedC.push (c.beta #[← innerRegs j SsC])
      let resS ← resultsOnE regsS Ss
      let resC ← resultsOnE regsC SsC
      let subst (k : Nat) (_ : Lean.Expr) := (opened[k]!.replaceFVar regsF regsS).replaceFVar rsF resS
      let substC (k : Nat) (_ : Lean.Expr) := (openedC[k]!.replaceFVar regsF regsC).replaceFVar rsF resC
      for c in calls do
        if c.hasAnyFVar (fun id => id != regsF.fvarId! && id != rsF.fvarId! && id != i.fvarId! &&
            id != bools.fvarId! && id != bits.fvarId!) then
          throwError "{declName}: a hardware-module call reads a variable the endpoint does not cover"
      let (extS, hext) ← instExtension declName r D #[i, bools, bits, S, Ss] t bits calls subst substC
      pure (← mkLambdaFVars #[i, bools, bits, S, Ss] extS, ← mkLambdaFVars #[i, bools, bits, S, Ss, t] hext)
  -- the generic theorem, applied step by step; the binder types name the facts
  let mut p := if chain then
      mkAppN (mkConst ``Tools.ShippingMachineTeleNest.machine_trace_of_tele_ext)
        #[ι, toExpr declName, data, domF, ss₂E, inhab₂, teleE]
    else mkAppN (mkConst (if hasInsts then ``machine_trace_of_nested_ext else ``machine_trace_of_nested))
      #[ι, toExpr declName, data, domF, ss₂E, inhab₂, lE]
  -- the slots are the enclosing machine's then the sub-machines'
  let slotsStmt := (← inferType p).bindingDomain!
  let some (α, lhs, _) := slotsStmt.eq? | throwError "{declName}: the slot equation"
  p := mkApp p (mkApp2 (mkConst ``Eq.refl [.one]) α lhs)
  p := mkApp p (← mkLambdaFVars #[i] rho)
  let initsName := declName ++ `machineInits
  addDef initsName (← inferType p).bindingDomain! inits₂
  p := mkApp p (mkConst initsName)
  let innersName := declName ++ `machineInners
  if chain then
    addDef innersName (← inferType teleE) teleE
  else
    addDef innersName (mkApp (mkConst ``List [.one]) innerT) lE
  let bodyName := declName ++ `machineBody
  addDef bodyName (← inferType p).bindingDomain! body₂
  p := mkApp p (mkConst bodyName)
  let resName := declName ++ `machineResult
  addDef resName (← inferType p).bindingDomain! (← resultObs declName r i D rho)
  p := mkApp p (mkConst resName)
  if hasExt then
    let extName := declName ++ `machineExt
    addDef extName (← inferType p).bindingDomain! extE
    p := mkApp p (mkConst extName)
  let srcName := declName ++ `machineSource
  let fieldNames : List (Option Name) :=
    if r.ctor?.isNone then [none] else r.outNames.map fun nm => some (outFieldName r nm)
  let obs ← observations declName D src fieldNames (r.shape.layout.outs.map outKind)
  addDef srcName (← inferType p).bindingDomain!
    (← mkLambdaFVars #[i, bools, bits] (listE (← mkArrow nat nat) obs))
  p := mkApp p (mkConst srcName)
  return (p, srcName, [(`machine_ok, false), (`machine_body, true), (`machine_inits, false),
    (`machine_writes, true), (`machine_result, true), (`machine_source, true)],
    if hasExt then some hextE else none)

/-! ### Calls with several outputs, calls of sequential children

The entries of the calls (a structure call, one per field it has), their
extension of BOTH input families, and the causality of every entry: a
combinational child's value is pointwise in the state (a `rfl`); a
sequential child's is causal by the child's own trace theorem
(`src_causal_of_trace`, through `field_causal`). -/

/-- `walkInsts` for calls with one Signal result or a structure result. -/
partial def walkInstsG (senv : StructEnv) (onCall : Lean.Expr → MetaM Lean.Expr) :
    Lean.Expr → MetaM Lean.Expr
  | e@(.app ..) => do
    if (machInstCall? senv e).isSome || (machInstCallS? senv e).isSome then onCall e else
    let f ← walkInstsG senv onCall e.appFn!
    let a ← walkInstsG senv onCall e.appArg!
    return .app f a
  | .letE nm ty v b _ => do
    let ty' ← walkInstsG senv onCall ty
    let v' ← walkInstsG senv onCall v
    withLetDecl nm ty' v' fun x => do
      let b' ← walkInstsG senv onCall (b.instantiate1 x)
      mkLetFVars #[x] b' (usedLetOnly := false)
  | .lam nm ty b bi => do
    let ty' ← walkInstsG senv onCall ty
    withLocalDecl nm bi ty' fun x => do
      let b' ← walkInstsG senv onCall (b.instantiate1 x)
      mkLambdaFVars #[x] b'
  | .forallE nm ty b bi => do
    let ty' ← walkInstsG senv onCall ty
    withLocalDecl nm bi ty' fun x => do
      let b' ← walkInstsG senv onCall (b.instantiate1 x)
      mkForallFVars #[x] b'
  | .mdata m b => do return .mdata m (← walkInstsG senv onCall b)
  | .proj n k b => do return .proj n k (← walkInstsG senv onCall b)
  | e => pure e

/-- The call entries in reading order, each call once: `(call, entry term,
index of the child output it reads)`. -/
def callEntriesG (senv : StructEnv) (e : Lean.Expr) :
    MetaM (Array (Lean.Expr × Lean.Expr × Nat)) := do
  let acc ← IO.mkRef (#[] : Array (Lean.Expr × Lean.Expr × Nat))
  let seen ← IO.mkRef (#[] : Array Lean.Expr)
  let env ← getEnv
  let _ ← walkInstsG senv (fun c => do
    let cZ ← zetaReduce c
    unless (← seen.get).contains cZ do
      seen.modify (·.push cZ)
      if (machInstCall? senv cZ).isSome then acc.modify (·.push (cZ, cZ, 0))
      else
        let ty ← whnfR (← inferType cZ)
        let some sn := ty.getAppFn.constName? | throwError "a call's result type {ty}"
        let fields := getStructureFields env sn
        for k in [0:fields.size] do
          acc.modify (·.push (cZ, ← mkProjection cZ fields[k]!, k))
    pure c) e
  acc.get

/-- The calls' extension `machineExt` of a child is pointwise in its inputs
and its state: `∀ i bools bits S t p w, (ext i bools bits S p w).val t =
(ext i (bools at t) (bits at t) (S at t) p w).val t`. The extension is a
chain of `extendBits` over `bits`; each call in it is pointwise (`rfl`),
and the chain is walked with `extendBits_val`. -/
def extPointwiseProof (declName : Name) (extC : Lean.Expr) : MetaM Lean.Expr := do
  let some c := extC.constName? | throwError "{declName}: a child's extension is not a constant"
  let some v := (← getConstInfo c).value? | throwError "{declName}: {c} has no value"
  let nat := mkConst ``Nat
  lambdaBoundedTelescope v 4 fun xs chain => do
    unless xs.size == 4 do throwError "{declName}: {c} is not a 4-argument extension"
    let (i, bools, bits, S) := (xs[0]!, xs[1]!, xs[2]!, xs[3]!)
    -- the chain, innermost first
    let mut calls : Array (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := #[]
    let mut e := chain
    while e.isAppOfArity ``Tools.ShippingMachineAuto.extendBits 5 do
      let a := e.getAppArgs
      calls := calls.push (a[2]!, a[3]!, a[4]!, a[0]!)
      e := a[1]!
    unless e == bits do throwError "{declName}: {c}'s chain does not end in the inputs"
    calls := calls.reverse
    let D ← match calls[0]? with
      | some (_, _, _, D) => pure D
      | none => throwError "{declName}: {c} has no calls"
    withLocalDeclD `t nat fun t => withLocalDeclD `p nat fun p => withLocalDeclD `w nat fun w => do
      let sig (α : Lean.Expr) := mkApp2 (mkConst ``Sparkle.Core.Signal.Signal [.zero]) D α
      let valE (α s : Lean.Expr) := mkApp (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.val [.zero]) D α s) t
      let mkC (α v : Lean.Expr) := mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.mk [.zero]) D α
        (.lam `u nat v .default)
      let bvN (n : Lean.Expr) := mkApp (mkConst ``BitVec) n
      let cB ← withLocalDeclD `q nat fun q => mkLambdaFVars #[q]
        (mkC (mkConst ``Bool) (valE (mkConst ``Bool) (mkApp bools q)))
      let cV ← withLocalDeclD `q nat fun q => withLocalDeclD `n nat fun n => mkLambdaFVars #[q, n]
        (mkC (bvN n) (valE (bvN n) (mkApp2 bits q n)))
      let Sty ← inferType S
      let σ := Sty.getAppArgs[1]!
      let cS := mkC σ (valE σ S)
      let subst (x : Lean.Expr) : Lean.Expr := x.replaceFVars #[bools, bits, S] #[cB, cV, cS]
      let mut cur ← withLocalDeclD `j nat fun j => withLocalDeclD `n nat fun n => do
        mkLambdaFVars #[j, n] (← mkEqRefl (valE (bvN n) (mkApp2 bits j n)))
      let mut f := bits
      let mut f' := cV
      for (pos, wd, sg, _) in calls do
        let fact ← mkEqRefl (valE (bvN wd) sg)
        let fact ← mkExpectedTypeHint fact (← mkEq (valE (bvN wd) sg) (valE (bvN wd) (subst sg)))
        cur := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits_val)
          #[D, f, f', pos, wd, sg, subst sg, t, cur, fact]
        f := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits) #[D, f, pos, wd, sg]
        f' := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits) #[D, f', pos, wd, subst sg]
      mkLambdaFVars #[i, bools, bits, S, t, p, w] (mkApp2 cur p w)

/-- The causality of a call entry (its term over the handles `regsF` and the
inputs `bools`/`bits`), over CONTEXTS (`Ctx`: the inputs and the state):
`∀ i x x' t, CtxAgree x x' t → (entry x).val t = (entry x').val t`. The
EARLIER entries (`earlier`: term, input position, kind; their causality
`earlierFacts`) may occur in the term and in the call's arguments: they are
read from input families (`B`, `V`, over the context's inputs) at their
positions, so what is left is pointwise in the state and those families
(`causal_of_pointwise_ctx`), and the equation back to the entry as written
is `extendBits_self`/`_ne` (`causal_congr_ctx`). A combinational child's
entry is then causal; a sequential child's from the child's endpoint facts
(`src_causal_of_data`, its `_ext` twin, or for a child with sequential calls
of its own `src_causal_of_data_causal` with its `machine_ext_causal`) on
argument families causal the same way. -/
def causalFactE (declName : Name) (D αs i bools bits regsF cl term : Lean.Expr) (cidx : Nat)
    (kind : MixedGateBinder) (earlier : Array (Lean.Expr × Nat × MixedGateBinder))
    (earlierFacts : Array Lean.Expr) (callName : Name) (combChild : Bool) :
    MetaM Lean.Expr := do
  let nat := mkConst ``Nat
  let hlistT := mkApp (mkConst ``HList) αs
  let sig (α : Lean.Expr) := mkApp2 (mkConst ``Sparkle.Core.Signal.Signal [.zero]) D α
  let sigS := sig hlistT
  let ctxT := mkApp2 (mkConst ``Tools.ShippingMachineCausal.Ctx) D hlistT
  let xB (x : Lean.Expr) := mkApp3 (mkConst ``Tools.ShippingMachineCausal.Ctx.B) D hlistT x
  let xV (x : Lean.Expr) := mkApp3 (mkConst ``Tools.ShippingMachineCausal.Ctx.V) D hlistT x
  let xS (x : Lean.Expr) := mkApp3 (mkConst ``Tools.ShippingMachineCausal.Ctx.S) D hlistT x
  let valE (α s t : Lean.Expr) := mkApp (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.val [.zero]) D α s) t
  let regsOf (S : Lean.Expr) := mkApp3 (mkConst ``Tools.ShippingMachineFuse.regsOf) D αs S
  -- a term over a context
  let over (e x : Lean.Expr) : Lean.Expr :=
    e.replaceFVars #[regsF, bools, bits] #[regsOf (xS x), xB x, xV x]
  let mkConstSig (α v : Lean.Expr) : Lean.Expr :=
    mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.mk [.zero]) D α (.lam `u nat v .default)
  let boolsT ← mkArrow nat (sig (mkConst ``Bool))
  let bitsT := Lean.Expr.forallE `j nat
    (.forallE `n nat (sig (mkApp (mkConst ``BitVec) (.bvar 0))) .default) .default
  let bvT (w : Nat) := mkApp (mkConst ``BitVec) (mkNatLit w)
  -- the earlier entries, read from the families `B`, `V`
  let abstract (e B V : Lean.Expr) : Lean.Expr := e.replace fun x =>
    match earlier.findIdx? (fun (t, _, _) => t == x) with
    | some j =>
      let (_, pos, kd) := earlier.getD j (x, 0, .bool)
      match (kd : MixedGateBinder) with
      | .bits w => some (mkApp2 V (mkNatLit pos) (mkNatLit w))
      | _ => some (mkApp B (mkNatLit pos))
    | none => none
  -- the inputs extended by the earlier entries, over a context
  let famsOver (x : Lean.Expr) : Lean.Expr × Lean.Expr := Id.run do
    let mut fb := xB x
    let mut fv := xV x
    for (t, pos, kd) in earlier do
      match kd with
      | .bits w => fv := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits) #[D, fv, mkNatLit pos, mkNatLit w, over t x]
      | _ => fb := mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBools) #[D, fb, mkNatLit pos, over t x]
    return (fb, fv)
  let FB ← withLocalDeclD `x ctxT fun x => mkLambdaFVars #[x] (famsOver x).1
  let FV ← withLocalDeclD `x ctxT fun x => mkLambdaFVars #[x] (famsOver x).2
  let agreeT (x x' t : Lean.Expr) : Lean.Expr :=
    mkAppN (mkConst ``Tools.ShippingMachineCausal.CtxAgree) #[D, hlistT, x, x', t]
  let hFam (isB : Bool) : MetaM Lean.Expr :=
    withLocalDeclD `x ctxT fun x => withLocalDeclD `x' ctxT fun x' => withLocalDeclD `t nat fun t => do
    withLocalDeclD `h (agreeT x x' t) fun h => do
      let mut cur := mkAppN (mkConst (if isB then ``Tools.ShippingMachineCausal.CtxAgree.b
        else ``Tools.ShippingMachineCausal.CtxAgree.v)) #[D, hlistT, x, x', t, h]
      let mut fS := if isB then xB x else xV x
      let mut fS' := if isB then xB x' else xV x'
      for q in [0:earlier.size] do
        let (tq, pos, kd) := earlier.getD q (bools, 0, .bool)
        let fact := mkAppN earlierFacts[q]! #[i, x, x', t, h]
        match (kd : MixedGateBinder), isB with
        | .bits w, false =>
          cur := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits_val)
            #[D, fS, fS', mkNatLit pos, mkNatLit w, over tq x, over tq x', t, cur, fact]
          fS := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits) #[D, fS, mkNatLit pos, mkNatLit w, over tq x]
          fS' := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits) #[D, fS', mkNatLit pos, mkNatLit w, over tq x']
        | .bool, true =>
          cur := mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBools_val)
            #[D, fS, fS', mkNatLit pos, over tq x, over tq x', t, cur, fact]
          fS := mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBools) #[D, fS, mkNatLit pos, over tq x]
          fS' := mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBools) #[D, fS', mkNatLit pos, over tq x']
        | _, _ => pure ()
      mkLambdaFVars #[x, x', t, h] cur
  let hFB ← hFam true
  let hFV ← hFam false
  -- reading an earlier entry back from the families: `lookup = entry` over `x`
  let lookupEq (x : Lean.Expr) (q : Nat) : MetaM Lean.Expr := do
    let (_, posq, kq) := earlier.getD q (bools, 0, .bool)
    let isB := match (kq : MixedGateBinder) with | .bits _ => false | _ => true
    -- the family before each earlier entry of the same kind
    let mut before : Array (Nat × Lean.Expr) := #[]
    let mut f := if isB then xB x else xV x
    for r in [0:earlier.size] do
      let (tr, posr, kr) := earlier.getD r (bools, 0, .bool)
      match (kr : MixedGateBinder), isB with
      | .bits w, false =>
        before := before.push (r, f)
        f := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits) #[D, f, mkNatLit posr, mkNatLit w, over tr x]
      | .bool, true =>
        before := before.push (r, f)
        f := mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBools) #[D, f, mkNatLit posr, over tr x]
      | _, _ => pure ()
    let mut pf : Option Lean.Expr := none
    for (r, fr) in before.reverse do
      if r < q then break
      let (tr, posr, kr) := earlier.getD r (bools, 0, .bool)
      let step := if r == q then
          match (kr : MixedGateBinder) with
          | .bits w => mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBits_self)
              #[D, fr, mkNatLit posr, mkNatLit w, over tr x]
          | _ => mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBools_self)
              #[D, fr, mkNatLit posr, over tr x]
        else
          let ne := mkApp3 (mkConst ``Tools.ShippingMachineCausal.ne_of_beq) (mkNatLit posq) (mkNatLit posr)
            (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.false))
          match (kr : MixedGateBinder), (kq : MixedGateBinder) with
          | .bits w, .bits wq => mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBits_ne)
              #[D, fr, mkNatLit posr, mkNatLit w, over tr x, mkNatLit posq, mkNatLit wq, ne]
          | _, _ => mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBools_ne)
              #[D, fr, mkNatLit posr, over tr x, mkNatLit posq, ne]
      pf ← match pf with
        | none => pure (some step)
        | some p => pure (some (← mkEqTrans p step))
    match pf with
    | some p => pure p
    | none => throwError "{declName}: no earlier entry {q}"
  -- the entry as written equals the entry read through the families
  -- (`∀ x, over e x = g x.S (FB x) (FV x)`), and the causality moves along it
  let transport (e α gS pfAbs : Lean.Expr) : MetaM Lean.Expr := do
    let hits := (List.range earlier.size).filter fun q =>
      (e.find? (· == (earlier.getD q (bools, 0, .bool)).1)).isSome
    let f ← withLocalDeclD `x ctxT fun x => mkLambdaFVars #[x] (over e x)
    let he ← withLocalDeclD `x ctxT fun x => do
      let types ← hits.mapM fun q => do
        let (tq, _, kq) := earlier.getD q (bools, 0, .bool)
        pure (tq, match (kq : MixedGateBinder) with | .bits w => sig (bvT w) | _ => sig (mkConst ``Bool))
      let F ← withLocalDecls (types.toArray.map fun (_, ty) => (`y, .default, fun _ => pure ty)) fun ys => do
        let body := e.replace fun y =>
          match types.findIdx? (fun (t, _) => t == y) with
          | some j => some ys[j]!
          | none => none
        mkLambdaFVars ys (over body x)
      let mut acc ← mkEqRefl F
      for q in hits do
        acc ← mkCongr acc (← mkEqSymm (← lookupEq x q))
      -- the inputs read directly are the families' base: the kernel reduces
      -- the extension at an input position
      let ty ← mkEq (over e x) (gS.beta #[x])
      mkLambdaFVars #[x] (← mkExpectedTypeHint acc ty)
    pure (mkAppN (mkConst ``Tools.ShippingMachineCausal.causal_congr_ctx) #[D, hlistT, α, f, gS, he, pfAbs])
  -- a value over the state and the families: pointwise (a `rfl`), so causal
  let causalOf (e α : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
    let g ← withLocalDeclD `S sigS fun S => withLocalDeclD `B boolsT fun B =>
      withLocalDeclD `V bitsT fun V => mkLambdaFVars #[S, B, V]
        ((abstract e B V).replaceFVars #[regsF, bools, bits] #[regsOf S, B, V])
    let stmt ← withLocalDeclD `S sigS fun S => withLocalDeclD `B boolsT fun B =>
      withLocalDeclD `V bitsT fun V => withLocalDeclD `t nat fun t => do
        let Sc := mkConstSig hlistT (valE hlistT S t)
        let Bc ← withLocalDeclD `p nat fun pv => mkLambdaFVars #[pv]
          (mkConstSig (mkConst ``Bool) (valE (mkConst ``Bool) (mkApp B pv) t))
        let Vc ← withLocalDeclD `p nat fun pv => withLocalDeclD `n nat fun n => mkLambdaFVars #[pv, n]
          (mkConstSig (mkApp (mkConst ``BitVec) n) (valE (mkApp (mkConst ``BitVec) n) (mkApp2 V pv n) t))
        mkForallFVars #[S, B, V, t] (← mkEq (valE α (g.beta #[S, B, V]) t) (valE α (g.beta #[Sc, Bc, Vc]) t))
    let hpt ← reflProof stmt true
    let pf := mkAppN (mkConst ``Tools.ShippingMachineCausal.causal_of_pointwise_ctx)
      #[D, hlistT, α, g, FB, FV, hpt, hFB, hFV]
    -- the value over a context
    let gS ← withLocalDeclD `x ctxT fun x =>
      mkLambdaFVars #[x] (g.beta #[xS x, FB.beta #[x], FV.beta #[x]])
    pure (gS, pf)
  let α := match kind with
    | .bits w => bvT w
    | _ => mkConst ``Bool
  let child := cl.getAppFn.constName!
  if combChild then
    let (gS, pf) ← causalOf term α
    return ← mkLambdaFVars #[i] (← transport term α gS pf)
  -- a sequential child: its endpoint's facts
  let some (.thmInfo th) := (← getEnv).find? (child ++ `machine_sound)
    | throwError "{declName}: the child {child} has no endpoint"
  -- without calls: `src_causal_of_data`; with combinational calls: its
  -- `_ext` twin, the extension pointwise in the inputs and state; with
  -- sequential calls: `src_causal_of_data_causal` and the child's
  -- `machine_ext_causal`
  let isExt := th.value.isAppOf ``Tools.ShippingMachineAuto.machine_trace_of_data_ext
  let isCausal := th.value.isAppOf ``Tools.ShippingMachineCausal.machine_trace_of_data_causal
  let isLoop := th.value.isAppOf ``Tools.ShippingMachineLoop.machine_trace_of_loop
  unless th.value.isAppOf ``Tools.ShippingMachineAuto.machine_trace_of_data || isExt || isCausal ||
      isLoop do
    throwError "{declName}: the child {child}'s endpoint is not machine_trace_of_data(_ext/_causal) or _of_loop"
  let cargs := th.value.getAppArgs
  let ιC := cargs[2]!
  let iC ← if ιC.isConstOf ``Sparkle.Core.Domain.DomainConfig then pure D
    else if ιC.isConstOf ``Unit then pure (mkConst ``Unit.unit)
    else throwError "{declName}: the child {child}'s family"
  let srcC := if isLoop then cargs[12]! else if isCausal then cargs[11]! else if isExt then cargs[10]!
    else cargs[9]!
  -- one theorem per child: every field of every call of it reuses it
  let causalName := child ++ `machine_src_causal
  unless (← getEnv).contains causalName do
    let causalHead ← if isLoop then
        pure (mkAppN (mkConst ``Tools.ShippingMachineCausal.src_causal_of_loop) cargs)
      else if isCausal then do
        unless (← getEnv).contains (child ++ `machine_ext_causal) do
          throwError "{declName}: the child {child} has no machine_ext_causal"
        pure (mkAppN (mkConst ``Tools.ShippingMachineCausal.src_causal_of_data_causal)
          (cargs.push (mkConst (child ++ `machine_ext_causal))))
      else if isExt then do
        let pre := mkAppN (mkConst ``Tools.ShippingMachineCausal.src_causal_of_data_ext) cargs
        pure (mkApp pre (← extPointwiseProof declName cargs[9]!))
      else pure (mkAppN (mkConst ``Tools.ShippingMachineCausal.src_causal_of_data) cargs)
    let ty ← inferType causalHead
    addDecl (.thmDecl { name := causalName, levelParams := [], type := ty, value := causalHead })
  let causalHead := mkConst causalName
  let srcF ← withLocalDeclD `B boolsT fun B => withLocalDeclD `V bitsT fun V =>
    mkLambdaFVars #[B, V] (mkAppN srcC #[iC, B, V])
  let hsrc ← withLocalDeclD `B boolsT fun B => withLocalDeclD `B' boolsT fun B' =>
    withLocalDeclD `V bitsT fun V => withLocalDeclD `V' bitsT fun V' =>
    withLocalDeclD `t nat fun t => do
      let pf := mkAppN causalHead #[iC, B, B', V, V', t]
      let hbT := (← inferType pf).bindingDomain!
      withLocalDeclD `hb hbT fun hb => do
        let pf := mkApp pf hb
        let hvT := (← inferType pf).bindingDomain!
        withLocalDeclD `hv hvT fun hv => mkLambdaFVars #[B, B', V, V', t, hb, hv] (mkApp pf hv)
  -- the argument families over a context, and their causality
  let some kinds := telescopeKinds (← getConstInfo child).type
    | throwError "{declName}: the child {child}'s binders"
  let args := cl.getAppArgs
  let argFacts ← ((kinds.zip args.toList).zipIdx).filterMapM fun ((kd, ar), p) => do
    match kd with
    | .domain => pure none
    | .bool => pure (some (p, kd, ← causalOf ar (mkConst ``Bool)))
    | .bits w => pure (some (p, kd, ← causalOf ar (bvT w)))
  let base0B ← withLocalDeclD `p nat fun pv => mkLambdaFVars #[pv]
    (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.pure [.zero]) D (mkConst ``Bool) (mkConst ``Bool.false))
  let base0V ← withLocalDeclD `p nat fun pv => withLocalDeclD `n nat fun n => mkLambdaFVars #[pv, n]
    (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.pure [.zero]) D (mkApp (mkConst ``BitVec) n)
      (mkApp2 (mkConst ``BitVec.ofNat) n (mkNatLit 0)))
  let famsOf (x : Lean.Expr) : Lean.Expr × Lean.Expr := Id.run do
    let mut fb := base0B
    let mut fv := base0V
    for (p, kd, (g, _)) in argFacts do
      match kd with
      | .bool => fb := mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBools) #[D, fb, mkNatLit p, g.beta #[x]]
      | .bits w => fv := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits) #[D, fv, mkNatLit p, mkNatLit w, g.beta #[x]]
      | .domain => pure ()
    return (fb, fv)
  let famB ← withLocalDeclD `x ctxT fun x => mkLambdaFVars #[x] (famsOf x).1
  let famV ← withLocalDeclD `x ctxT fun x => mkLambdaFVars #[x] (famsOf x).2
  -- `∀ x x' t, agree → ∀ p (n) c, c ≤ t → fam x at c = fam x' at c`
  let famCausal (isB : Bool) : MetaM Lean.Expr :=
    withLocalDeclD `x ctxT fun x => withLocalDeclD `x' ctxT fun x' => withLocalDeclD `t nat fun t => do
    withLocalDeclD `h (agreeT x x' t) fun h => withLocalDeclD `c nat fun c => do
    withLocalDeclD `hc (← mkAppM ``LE.le #[c, t]) fun hc => do
      let hcP := mkAppN (mkConst ``Tools.ShippingMachineCausal.CtxAgree.mono)
        #[D, hlistT, x, x', t, c, h, hc]
      let mut cur ← if isB then
          withLocalDeclD `j nat fun j => do
            mkLambdaFVars #[j] (← mkEqRefl (valE (mkConst ``Bool) (mkApp base0B j) c))
        else withLocalDeclD `j nat fun j => withLocalDeclD `n nat fun n => do
            mkLambdaFVars #[j, n] (← mkEqRefl (valE (mkApp (mkConst ``BitVec) n) (mkApp2 base0V j n) c))
      let mut fS := if isB then base0B else base0V
      let mut fS' := if isB then base0B else base0V
      for (p, kd, (g, gc)) in argFacts do
        let hsig := mkAppN gc #[x, x', c, hcP]
        match kd, isB with
        | .bool, true =>
          cur := mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBools_val)
            #[D, fS, fS', mkNatLit p, g.beta #[x], g.beta #[x'], c, cur, hsig]
          fS := mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBools) #[D, fS, mkNatLit p, g.beta #[x]]
          fS' := mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBools) #[D, fS', mkNatLit p, g.beta #[x']]
        | .bits w, false =>
          cur := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits_val)
            #[D, fS, fS', mkNatLit p, mkNatLit w, g.beta #[x], g.beta #[x'], c, cur, hsig]
          fS := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits) #[D, fS, mkNatLit p, mkNatLit w, g.beta #[x]]
          fS' := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits) #[D, fS', mkNatLit p, mkNatLit w, g.beta #[x']]
        | _, _ => pure ()
      if isB then
        withLocalDeclD `p nat fun pv => mkLambdaFVars #[x, x', t, h, pv, c, hc] (mkApp cur pv)
      else
        withLocalDeclD `p nat fun pv => withLocalDeclD `n nat fun n =>
          mkLambdaFVars #[x, x', t, h, pv, n, c, hc] (mkApp2 cur pv n)
  -- the call's causality, once per call (its fields share the families)
  unless (← getEnv).contains callName do
    let hfB ← famCausal true
    let hfV ← famCausal false
    let hcall ← withLocalDeclD `x ctxT fun x => withLocalDeclD `x' ctxT fun x' =>
      withLocalDeclD `t nat fun t => do
      withLocalDeclD `h (agreeT x x' t) fun h => do
        mkLambdaFVars #[i, x, x', t, h] (mkAppN hsrc
          #[famB.beta #[x], famB.beta #[x'], famV.beta #[x], famV.beta #[x'], t,
            mkAppN hfB #[x, x', t, h], mkAppN hfV #[x, x', t, h]])
    let ty ← inferType hcall
    progress s!"{callName}: checking"
    addDecl (.thmDecl { name := callName, levelParams := [], type := ty, value := hcall })
  let hcall := mkApp (mkConst callName) i
  -- the observation the entry is
  progress s!"{declName}: entry observation"
  let (g, _) ← causalOf term α
  progress s!"{declName}: entry observation read"
  let hobsStmt ← withLocalDeclD `x ctxT fun x => do
    let obs ← withLocalDeclD `t nat fun t => do
      let v := valE α (g.beta #[x]) t
      mkLambdaFVars #[t] (match kind with
        | .bits w => mkApp2 (mkConst ``BitVec.toNat) (mkNatLit w) v
        | _ => mkApp (mkConst ``Tools.ShippingMuxLoweringSoundness.encodeBool) v)
    let lhs ← mkAppM ``GetElem?.getElem? #[mkAppN srcF #[famB.beta #[x], famV.beta #[x]], mkNatLit cidx]
    mkForallFVars #[x] (← mkEq lhs (← mkAppM ``Option.some #[obs]))
  progress s!"{declName}: hobs statement"
  let hobs ← reflProof hobsStmt true
  progress s!"{declName}: hobs"
  let pf := match kind with
    | .bits w => mkAppN (mkConst ``Tools.ShippingMachineCausal.field_causal_ctx)
        #[D, hlistT, srcF, famB, famV, hcall, mkNatLit cidx, mkNatLit w, g, hobs]
    | _ => mkAppN (mkConst ``Tools.ShippingMachineCausal.field_causalB_ctx)
        #[D, hlistT, srcF, famB, famV, hcall, mkNatLit cidx, g, hobs]
  mkLambdaFVars #[i] (← transport term α g pf)

/-- The endpoint of a declaration that is one `circuit do`, through
`machine_trace_of_data`. Returns the partial application, the name of the
source observations and the checks (name suffix, side of the `rfl`). -/
def singleProof (declName : Name) (r : Read) (data ι i D bools bits src inst : Lean.Expr) :
    MetaM (Lean.Expr × Name × List (Name × Bool) × Option Lean.Expr) := do
  let nat := mkConst ``Nat
  let some run := inst.find? fun t => t.isAppOfArity ``Sparkle.Core.runCircuitH 8
    | throwError "{declName}: no runCircuitH in the unfolded value"
  let a := run.getAppArgs
  let (rho, inhab, inits, body) := (a[2]!, a[5]!, a[6]!, a[7]!)
  if inits.hasFVar || inhab.hasFVar then
    throwError "{declName}: the reset values depend on a binder"
  -- the `@[hardware_module]` calls of the body, their extension of the inputs
  -- and its pointwiseness
  let hasInsts := !r.shape.insts.isEmpty
  let αs := a[1]!
  let hlistT := mkApp (mkConst ``HList) αs
  let (extE, hextE) ← if !hasInsts then pure (mkConst ``Unit.unit, mkConst ``Unit.unit) else
    withLocalDeclD `regs body.bindingDomain! fun regsF => do
    let env ← getEnv
    let senv := structEnv env
    let calls ← collectInsts senv (body.bindingBody!.instantiate1 regsF)
    withLocalDeclD `S (mkApp2 (mkConst ``Sparkle.Core.Signal.Signal [.zero]) D hlistT) fun S =>
    withLocalDeclD `t nat fun t => do
      let regsS := mkApp3 (mkConst ``Tools.ShippingMachineFuse.regsOf) D αs S
      let constS := mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.mk [.zero]) D hlistT
        (.lam `u nat (mkApp (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.val [.zero]) D hlistT S) t)
          .default)
      let regsC := mkApp3 (mkConst ``Tools.ShippingMachineFuse.regsOf) D αs constS
      for c in calls do
        if c.hasAnyFVar (fun id => id != regsF.fvarId! && id != i.fvarId! &&
            id != bools.fvarId! && id != bits.fvarId!) then
          throwError "{declName}: a hardware-module call reads a variable the endpoint does not cover"
      let (extS, hext) ← instExtension declName r D #[i, bools, bits, S] t bits calls
        (fun _ c => c.replaceFVar regsF regsS) (fun _ c => c.replaceFVar regsF regsC)
      pure (← mkLambdaFVars #[i, bools, bits, S] extS, ← mkLambdaFVars #[i, bools, bits, S, t] hext)
  -- the generic theorem, applied step by step; the binder types name the facts
  let mut p := mkAppN (mkConst (if hasInsts then ``machine_trace_of_data_ext else ``machine_trace_of_data))
    #[toExpr declName, data, ι, ← mkLambdaFVars #[i] D, inhab, ← mkLambdaFVars #[i] rho]
  let initsName := declName ++ `machineInits
  addDef initsName (← inferType p).bindingDomain! inits
  p := mkApp p (mkConst initsName)
  let bodyName := declName ++ `machineBody
  addDef bodyName (← inferType p).bindingDomain! (← mkLambdaFVars #[i, bools, bits] body)
  p := mkApp p (mkConst bodyName)
  -- the source observations, one per output port
  let scalar := r.ctor?.isNone
  let obs ← (r.outNames.zip (r.shape.layout.outs.map outKind)).mapM fun (nm, k) => do
    let field ← if scalar then pure src else mkProjection src (outFieldName r nm)
    withLocalDeclD `t nat fun t => do
      let v (α : Lean.Expr) :=
        mkApp (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.val [.zero]) D α field) t
      let e ← match k with
        | .bool => pure (mkApp (mkConst ``Tools.ShippingMuxLoweringSoundness.encodeBool)
            (v (mkConst ``Bool)))
        | .bits w =>
          let wE := mkNatLit w
          pure (mkApp2 (mkConst ``BitVec.toNat) wE (v (mkApp (mkConst ``BitVec) wE)))
        | .domain => throwError "{declName}: an output is a domain"
      mkLambdaFVars #[t] e
  -- the observations of a result, by field
  let env ← getEnv
  let rhoHead := rho.getAppFn.constName?.getD .anonymous
  let fieldNames : List (Option Name) ←
    if rhoHead == ``Sparkle.Core.Signal.Signal then pure [none]
    else if r.ctor?.isSome then pure (r.outNames.map fun nm => some (outFieldName r nm))
    else match r.sel? with
      | some (_, _, idx) =>
        match (getStructureFields env rhoHead)[idx]? with
        | some f => pure [some f]
        | none => throwError "{declName}: the selected field of {rhoHead}"
      | none => throwError "{declName}: the result type {rhoHead}"
  let resName := declName ++ `machineResult
  let resV ← withLocalDeclD `r rho fun res => do
    let fs ← (fieldNames.zip (r.shape.layout.outs.map outKind)).mapM fun (fn, k) => do
      let field ← match fn with
        | none => pure res
        | some f => mkProjection res f
      withLocalDeclD `t nat fun t => do
        let v (α : Lean.Expr) :=
          mkApp (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.val [.zero]) D α field) t
        let e ← match k with
          | .bool => pure (mkApp (mkConst ``Tools.ShippingMuxLoweringSoundness.encodeBool)
              (v (mkConst ``Bool)))
          | .bits w =>
            let wE := mkNatLit w
            pure (mkApp2 (mkConst ``BitVec.toNat) wE (v (mkApp (mkConst ``BitVec) wE)))
          | .domain => throwError "{declName}: an output is a domain"
        mkLambdaFVars #[t] e
    mkLambdaFVars #[i, res] (listE (← mkArrow nat nat) fs)
  addDef resName (← inferType p).bindingDomain! resV
  p := mkApp p (mkConst resName)
  if hasInsts then
    let extName := declName ++ `machineExt
    addDef extName (← inferType p).bindingDomain! extE
    p := mkApp p (mkConst extName)
  let srcName := declName ++ `machineSource
  addDef srcName (← inferType p).bindingDomain!
    (← mkLambdaFVars #[i, bools, bits] (listE (← mkArrow nat nat) obs))
  p := mkApp p (mkConst srcName)
  return (p, srcName, [(`machine_ok, false), (`machine_body, true), (`machine_inits, false),
    (`machine_writes, true), (`machine_result, true), (`machine_source, true)],
    if hasInsts then some hextE else none)

def causalProof (declName : Name) (r : Read) (data ι i D bools bits src inst : Lean.Expr) :
    MetaM (Lean.Expr × Name × List (Name × Bool) × Option Lean.Expr) := do
  let nat := mkConst ``Nat
  let some run := inst.find? fun t => t.isAppOfArity ``Sparkle.Core.runCircuitH 8
    | throwError "{declName}: no runCircuitH in the unfolded value"
  let a := run.getAppArgs
  let (rho, inhab, inits, body) := (a[2]!, a[5]!, a[6]!, a[7]!)
  if inits.hasFVar || inhab.hasFVar then
    throwError "{declName}: the reset values depend on a binder"
  -- the calls of the body, one entry per output read (a structure call one
  -- per field), their extension of both input families, and its causality
  let αs := a[1]!
  let hlistT := mkApp (mkConst ``HList) αs
  let sigS := mkApp2 (mkConst ``Sparkle.Core.Signal.Signal [.zero]) D hlistT
  let kindOf (k : Nat) : MixedGateBinder := match r.shape.insts[k]? with
    | some (_, _, kd) => kd
    | none => .domain
  let (extE, extBE, hcE) ← withLocalDeclD `regs body.bindingDomain! fun regsF => do
    let env ← getEnv
    let senv := structEnv env
    let entries ← callEntriesG senv (body.bindingBody!.instantiate1 regsF)
    unless entries.size == r.shape.insts.length do
      throwError "{declName}: {entries.size} call outputs found, the compiler read {r.shape.insts.length}"
    for (cl, _, _) in entries do
      if cl.hasAnyFVar (fun id => id != regsF.fvarId! && id != i.fvarId! &&
          id != bools.fvarId! && id != bits.fvarId!) then
        throwError "{declName}: a hardware-module call reads a variable the endpoint does not cover"
    -- an entry over a state signal
    let over (e S : Lean.Expr) : Lean.Expr :=
      e.replaceFVar regsF (mkApp3 (mkConst ``Tools.ShippingMachineFuse.regsOf) D αs S)
    -- the extension over a state signal
    let extOf (S : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
      let mut eV := bits
      let mut eB := bools
      for k in [0:entries.size] do
        let (_, term, _) := entries[k]!
        let pos := mkNatLit (r.nDecl + k)
        match kindOf k with
        | .bits w =>
          eV := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits) #[D, eV, pos, mkNatLit w, over term S]
        | .bool =>
          eB := mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBools) #[D, eB, pos, over term S]
        | .domain => throwError "{declName}: a call output is a domain"
      pure (eV, eB)
    -- the causality of every entry, a theorem each
    let mut facts : Array Lean.Expr := #[]
    let mut combCache : Std.HashMap Name Bool := {}
    for k in [0:entries.size] do
      let (cl, term, cidx) := entries[k]!
      -- the entries before this call's first field: its arguments cannot read
      -- its own fields, so the call's families are the same for every field
      let k0 := ((List.range k).find? fun j => entries[j]!.1 == cl).getD k
      let earlier := ((List.range k0).map fun j =>
        (entries[j]!.2.1, r.nDecl + j, kindOf j)).toArray
      -- whether the child is combinational (read once per child)
      let child := cl.getAppFn.constName!
      let comb ← match combCache.get? child with
        | some b => pure b
        | none => do
          -- a child that is not a machine is compiled by a certified gate:
          -- combinational
          try
            let rc ← readMachine child
            pure (rc.shape.layout.slots.isEmpty && rc.shape.insts.isEmpty)
          catch _ => pure true
      combCache := combCache.insert child comb
      let pf ← causalFactE declName D αs i bools bits regsF cl term cidx (kindOf k) earlier
        (facts.extract 0 k0) (declName ++ Name.mkSimple s!"machine_call_{k0}") comb
      progress s!"{declName}: fact {k} built"
      let name := declName ++ Name.mkSimple s!"machine_causal_{k}"
      if (← IO.getEnv "SPARKLE_MACHINE_METACHECK").isSome then
        withOptions (fun o => o.set `pp.rawOnError true) do Meta.check pf
      let ty ← inferType pf
      progress s!"{name}: checking ({cl.getAppFn.constName!} field {cidx}, {earlier.size} earlier, hits {earlier.filter (fun (t, _, _) => (cl.find? (· == t)).isSome || (term.find? (· == t)).isSome) |>.size}, size {term.approxDepth})"
      addDecl (.thmDecl { name, levelParams := [], type := ty, value := pf })
      progress s!"{name}: checked"
      facts := facts.push (mkConst name)
    -- the joint causality of the extension, in the inputs and the state
    let ctxT := mkApp2 (mkConst ``Tools.ShippingMachineCausal.Ctx) D hlistT
    let xB (x : Lean.Expr) := mkApp3 (mkConst ``Tools.ShippingMachineCausal.Ctx.B) D hlistT x
    let xV (x : Lean.Expr) := mkApp3 (mkConst ``Tools.ShippingMachineCausal.Ctx.V) D hlistT x
    let xS (x : Lean.Expr) := mkApp3 (mkConst ``Tools.ShippingMachineCausal.Ctx.S) D hlistT x
    let overX (e x : Lean.Expr) : Lean.Expr :=
      e.replaceFVars #[regsF, bools, bits]
        #[mkApp3 (mkConst ``Tools.ShippingMachineFuse.regsOf) D αs (xS x), xB x, xV x]
    let joint ← withLocalDeclD `x ctxT fun x => withLocalDeclD `x' ctxT fun x' =>
      withLocalDeclD `t (mkConst ``Nat) fun t => do
      withLocalDeclD `h (mkAppN (mkConst ``Tools.ShippingMachineCausal.CtxAgree) #[D, hlistT, x, x', t])
        fun h => do
      let mut hV := mkAppN (mkConst ``Tools.ShippingMachineCausal.CtxAgree.v) #[D, hlistT, x, x', t, h]
      let mut hB := mkAppN (mkConst ``Tools.ShippingMachineCausal.CtxAgree.b) #[D, hlistT, x, x', t, h]
      let mut curV := xV x
      let mut curV' := xV x'
      let mut curB := xB x
      let mut curB' := xB x'
      for k in [0:entries.size] do
        let (_, term, _) := entries[k]!
        let pos := mkNatLit (r.nDecl + k)
        let fact := mkAppN facts[k]! #[i, x, x', t, h]
        match kindOf k with
        | .bits w =>
          hV := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits_val)
            #[D, curV, curV', pos, mkNatLit w, overX term x, overX term x', t, hV, fact]
          curV := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits) #[D, curV, pos, mkNatLit w, overX term x]
          curV' := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits) #[D, curV', pos, mkNatLit w, overX term x']
        | .bool =>
          hB := mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBools_val)
            #[D, curB, curB', pos, overX term x, overX term x', t, hB, fact]
          curB := mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBools) #[D, curB, pos, overX term x]
          curB' := mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBools) #[D, curB', pos, overX term x']
        | .domain => pure ()
      mkLambdaFVars #[i, x, x', t, h] (← mkAppM ``And.intro #[hV, hB])
    pure (← withLocalDeclD `S sigS fun S0 => do
            let (v, _) ← extOf S0
            mkLambdaFVars #[i, bools, bits, S0] v,
          ← withLocalDeclD `S sigS fun S0 => do
            let (_, b) ← extOf S0
            mkLambdaFVars #[i, bools, bits, S0] b,
          joint)
  -- the generic theorem, applied step by step; the binder types name the facts
  let mut p := mkAppN (mkConst ``Tools.ShippingMachineCausal.machine_trace_of_data_causal)
    #[toExpr declName, data, ι, ← mkLambdaFVars #[i] D, inhab, ← mkLambdaFVars #[i] rho]
  let initsName := declName ++ `machineInits
  addDef initsName (← inferType p).bindingDomain! inits
  p := mkApp p (mkConst initsName)
  let bodyName := declName ++ `machineBody
  addDef bodyName (← inferType p).bindingDomain! (← mkLambdaFVars #[i, bools, bits] body)
  p := mkApp p (mkConst bodyName)
  -- the source observations, one per output port
  let scalar := r.ctor?.isNone
  let obs ← (r.outNames.zip (r.shape.layout.outs.map outKind)).mapM fun (nm, k) => do
    let field ← if scalar then pure src else mkProjection src (outFieldName r nm)
    withLocalDeclD `t nat fun t => do
      let v (α : Lean.Expr) :=
        mkApp (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.val [.zero]) D α field) t
      let e ← match k with
        | .bool => pure (mkApp (mkConst ``Tools.ShippingMuxLoweringSoundness.encodeBool)
            (v (mkConst ``Bool)))
        | .bits w =>
          let wE := mkNatLit w
          pure (mkApp2 (mkConst ``BitVec.toNat) wE (v (mkApp (mkConst ``BitVec) wE)))
        | .domain => throwError "{declName}: an output is a domain"
      mkLambdaFVars #[t] e
  -- the observations of a result, by field
  let env ← getEnv
  let rhoHead := rho.getAppFn.constName?.getD .anonymous
  let fieldNames : List (Option Name) ←
    if rhoHead == ``Sparkle.Core.Signal.Signal then pure [none]
    else if r.ctor?.isSome then pure (r.outNames.map fun nm => some (outFieldName r nm))
    else match r.sel? with
      | some (_, _, idx) =>
        match (getStructureFields env rhoHead)[idx]? with
        | some f => pure [some f]
        | none => throwError "{declName}: the selected field of {rhoHead}"
      | none => throwError "{declName}: the result type {rhoHead}"
  let resName := declName ++ `machineResult
  let resV ← withLocalDeclD `r rho fun res => do
    let fs ← (fieldNames.zip (r.shape.layout.outs.map outKind)).mapM fun (fn, k) => do
      let field ← match fn with
        | none => pure res
        | some f => mkProjection res f
      withLocalDeclD `t nat fun t => do
        let v (α : Lean.Expr) :=
          mkApp (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.val [.zero]) D α field) t
        let e ← match k with
          | .bool => pure (mkApp (mkConst ``Tools.ShippingMuxLoweringSoundness.encodeBool)
              (v (mkConst ``Bool)))
          | .bits w =>
            let wE := mkNatLit w
            pure (mkApp2 (mkConst ``BitVec.toNat) wE (v (mkApp (mkConst ``BitVec) wE)))
          | .domain => throwError "{declName}: an output is a domain"
        mkLambdaFVars #[t] e
    mkLambdaFVars #[i, res] (listE (← mkArrow nat nat) fs)
  addDef resName (← inferType p).bindingDomain! resV
  p := mkApp p (mkConst resName)
  let extName := declName ++ `machineExt
  addDef extName (← inferType p).bindingDomain! extE
  p := mkApp p (mkConst extName)
  let extBName := declName ++ `machineExtB
  addDef extBName (← inferType p).bindingDomain! extBE
  p := mkApp p (mkConst extBName)
  -- the joint causality, stated over the extension's definitions; the
  -- calls' causality in the state (`hcausal`) is its case of fixed inputs
  let ctxT := mkApp2 (mkConst ``Tools.ShippingMachineCausal.Ctx) D hlistT
  let jointName := declName ++ `machine_ext_causal
  let jointT ← withLocalDeclD `x ctxT fun x => withLocalDeclD `x' ctxT fun x' =>
    withLocalDeclD `t nat fun t => do
    let agree := mkAppN (mkConst ``Tools.ShippingMachineCausal.CtxAgree) #[D, hlistT, x, x', t]
    let args (x : Lean.Expr) := #[i,
      mkApp3 (mkConst ``Tools.ShippingMachineCausal.Ctx.B) D hlistT x,
      mkApp3 (mkConst ``Tools.ShippingMachineCausal.Ctx.V) D hlistT x,
      mkApp3 (mkConst ``Tools.ShippingMachineCausal.Ctx.S) D hlistT x]
    let valE (α s : Lean.Expr) := mkApp (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.val [.zero]) D α s) t
    let cV ← withLocalDeclD `p nat fun pv => withLocalDeclD `w nat fun w => do
      let bv := mkApp (mkConst ``BitVec) w
      mkForallFVars #[pv, w] (← mkEq (valE bv (mkAppN (mkConst extName) (args x ++ #[pv, w])))
        (valE bv (mkAppN (mkConst extName) (args x' ++ #[pv, w]))))
    let cB ← withLocalDeclD `p nat fun pv => do
      mkForallFVars #[pv] (← mkEq (valE (mkConst ``Bool) (mkAppN (mkConst extBName) (args x ++ #[pv])))
        (valE (mkConst ``Bool) (mkAppN (mkConst extBName) (args x' ++ #[pv]))))
    mkForallFVars #[i, x, x', t] (← mkArrow agree (mkAnd cV cB))
  progress s!"{jointName}: checking"
  addDecl (.thmDecl { name := jointName, levelParams := [], type := jointT, value := hcE })
  let sigS := mkApp2 (mkConst ``Sparkle.Core.Signal.Signal [.zero]) D hlistT
  let hcE ← withLocalDeclD `S sigS fun S => withLocalDeclD `S' sigS fun S' =>
    withLocalDeclD `t nat fun t => do
    let agreeT ← withLocalDeclD `c nat fun c => do
      mkForallFVars #[c] (← mkArrow (← mkAppM ``LE.le #[c, t])
        (← mkEq (mkApp (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.val [.zero]) D hlistT S) c)
          (mkApp (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.val [.zero]) D hlistT S') c)))
    withLocalDeclD `h agreeT fun h => do
      let mk (S : Lean.Expr) := mkApp5 (mkConst ``Tools.ShippingMachineCausal.Ctx.mk) D hlistT bools bits S
      mkLambdaFVars #[i, bools, bits, S, S', t, h] (mkAppN (mkConst jointName)
        #[i, mk S, mk S', t, mkAppN (mkConst ``Tools.ShippingMachineCausal.CtxAgree.of_state)
          #[D, hlistT, bools, bits, S, S', t, h]])
  let srcName := declName ++ `machineSource
  addDef srcName (← inferType p).bindingDomain!
    (← mkLambdaFVars #[i, bools, bits] (listE (← mkArrow nat nat) obs))
  p := mkApp p (mkConst srcName)
  return (p, srcName, [(`machine_ok, false), (`machine_body, true), (`machine_inits, false),
    (`machine_writes, true), (`machine_result, true), (`machine_source, true)],
    some hcE)


/-! ### A hand-written `Signal.loop`

`let s := Signal.loop f; result s` (after the root `let`s before it): the
endpoint goes through `machine_trace_of_loop` with `res := fun L => result L`,
`σ` the reading of the state tuple as the machine's typed tuple, and the
reset tuple from the registers' initial values. -/

/-- The packed bits of a tuple value `x` whose components have kinds `ks`
(first component high, a Bool as one bit): the observation of a tuple
result, the legacy lowering's single `out` port. -/
partial def packTuple (x : Lean.Expr) : List MixedGateBinder → MetaM Lean.Expr
  | [] => throwError "packTuple: no component"
  | [k] => comp x k
  | k :: ks => do
    let a ← comp (← mkAppM ``Prod.fst #[x]) k
    let b ← packTuple (← mkAppM ``Prod.snd #[x]) ks
    mkAppM ``HAppend.hAppend #[a, b]
where
  comp (c : Lean.Expr) : MixedGateBinder → MetaM Lean.Expr
    | .bool => pure (mkApp (mkConst ``Tools.ShippingMachineLoop.boolBits) c)
    | _ => pure c

/-- The observations of a value `v` of the declaration's result type. -/
def resultObsOf (declName : Name) (r : Read) (D v rho : Lean.Expr) : MetaM (List Lean.Expr) := do
  match r.tuple with
  | some ks =>
    let nat := mkConst ``Nat
    let o ← withLocalDeclD `t nat fun t => do
      let x ← mkAppM ``Sparkle.Core.Signal.Signal.val #[v, t]
      mkLambdaFVars #[t] (← mkAppM ``BitVec.toNat #[← packTuple x ks])
    pure [o]
  | none =>
    observations declName D v (← resultFields declName r rho) (r.shape.layout.outs.map outKind)

/-- The endpoint of a machine without slots (a combinational body with
`let`s), through `machine_trace_of_comb`. -/
def combProof (declName : Name) (r : Read) (data ι i D bools bits src inst : Lean.Expr) :
    MetaM (Lean.Expr × Name × List (Name × Bool) × Option Lean.Expr) := do
  let nat := mkConst ``Nat
  let rho ← inferType inst
  let mut p := mkAppN (mkConst ``Tools.ShippingMachineLoop.machine_trace_of_comb)
    #[toExpr declName, data, ι, ← mkLambdaFVars #[i] D]
  let initsName := declName ++ `machineInits
  addDef initsName (← inferType p).bindingDomain! (mkConst ``Unit.unit)
  p := mkApp p (mkConst initsName)
  let srcName := declName ++ `machineSource
  addDef srcName (← inferType p).bindingDomain!
    (← mkLambdaFVars #[i, bools, bits] (listE (← mkArrow nat nat) (← resultObsOf declName r D src rho)))
  p := mkApp p (mkConst srcName)
  return (p, srcName, [(`machine_ok, false), (`machine_body, true), (`machine_inits, false),
    (`machine_next, true), (`machine_result, true)], none)

/-- The endpoint of a machine without slots whose calls go through the
structure path (sequential or Bool-result children), through
`machine_trace_of_comb_calls`: the calls' values are the input families at
their positions (`machineExt`, `machineExtB`). -/
def combCallsProof (declName : Name) (r : Read) (data ι i D bools bits src inst : Lean.Expr) :
    MetaM (Lean.Expr × Name × List (Name × Bool) × Option Lean.Expr) := do
  let nat := mkConst ``Nat
  let rho ← inferType inst
  let kindOf (k : Nat) : MixedGateBinder := match r.shape.insts[k]? with
    | some (_, _, kd) => kd
    | none => .domain
  let senv := structEnv (← getEnv)
  let entries ← callEntriesG senv inst
  unless entries.size == r.shape.insts.length do
    throwError "{declName}: {entries.size} call outputs found, the compiler read {r.shape.insts.length}"
  for (cl, _, _) in entries do
    if cl.hasAnyFVar (fun id => id != i.fvarId! && id != bools.fvarId! && id != bits.fvarId!) then
      throwError "{declName}: a hardware-module call reads a variable the endpoint does not cover"
  let mut eV := bits
  let mut eB := bools
  for k in [0:entries.size] do
    let (_, term, _) := entries[k]!
    let pos := mkNatLit (r.nDecl + k)
    match kindOf k with
    | .bits w => eV := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits) #[D, eV, pos, mkNatLit w, term]
    | .bool => eB := mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBools) #[D, eB, pos, term]
    | .domain => throwError "{declName}: a call output is a domain"
  let mut p := mkAppN (mkConst ``Tools.ShippingMachineCausal.machine_trace_of_comb_calls)
    #[toExpr declName, data, ι, ← mkLambdaFVars #[i] D]
  let initsName := declName ++ `machineInits
  addDef initsName (← inferType p).bindingDomain! (mkConst ``Unit.unit)
  p := mkApp p (mkConst initsName)
  let extName := declName ++ `machineExt
  addDef extName (← inferType p).bindingDomain! (← mkLambdaFVars #[i, bools, bits] eV)
  p := mkApp p (mkConst extName)
  let extBName := declName ++ `machineExtB
  addDef extBName (← inferType p).bindingDomain! (← mkLambdaFVars #[i, bools, bits] eB)
  p := mkApp p (mkConst extBName)
  let srcName := declName ++ `machineSource
  addDef srcName (← inferType p).bindingDomain!
    (← mkLambdaFVars #[i, bools, bits] (listE (← mkArrow nat nat) (← resultObsOf declName r D src rho)))
  p := mkApp p (mkConst srcName)
  return (p, srcName, [(`machine_ok, false), (`machine_body, true), (`machine_inits, false),
    (`machine_next, true), (`machine_result, true)], none)

def loopProof (declName : Name) (r : Read) (data ι i D bools bits src inst : Lean.Expr) :
    MetaM (Lean.Expr × Name × List (Name × Bool) × Option Lean.Expr) := do
  let nat := mkConst ``Nat
  -- the root `let`s before the loop substituted; the loop and the rest
  let mut cur := inst
  let mut found : Option (Lean.Expr × Lean.Expr) := none
  for _ in [0:100000] do
    match cur with
    | .letE _ _ v b _ =>
      if v.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then
        found := some (v, b)
        break
      else cur := b.instantiate1 v
    | _ => break
  -- the loop as the whole value: `let s := loop; s`
  if found.isNone && cur.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then
    found := some (cur, .bvar 0)
  let some (loopApp, rest) := found | throwError "{declName}: no root Signal.loop"
  let la := loopApp.getAppArgs
  let (α, inh, f) := (la[1]!, la[2]!, la[3]!)
  let .lam _ _ fBody _ := f | throwError "{declName}: the loop body is not a function"
  -- the registers read off the body with its `let`s substituted (a reset
  -- value may read a `let` of the body: `0#W`, `W := w + f`)
  let fBodyZ ← withLocalDeclD `state (← inferType f).bindingDomain! fun st => do
    let b ← zetaReduce (fBody.instantiate1 st)
    pure (b.abstract #[st])
  let some regs := machLoopRegs (machLetTail fBodyZ) | throwError "{declName}: the loop's registers"
  if regs.any (fun (_, init, _) => init.hasLooseBVars) then
    throwError "{declName}: a reset value reads the loop state"
  let n := regs.length
  unless n == r.shape.layout.slots.length do throwError "{declName}: slot count"
  if inh.hasFVar then throwError "{declName}: the state's Inhabited instance depends on a binder"
  -- the result over a state signal
  let sigα := mkApp2 (mkConst ``Sparkle.Core.Signal.Signal [.zero]) D α
  let rho ← inferType (rest.instantiate1 loopApp)
  let resV ← withLocalDeclD `L sigα fun L => mkLambdaFVars #[i, bools, bits, L] (rest.instantiate1 L)
  -- the generic theorem, applied step by step; the binder types name the facts
  let mut p := mkAppN (mkConst ``Tools.ShippingMachineLoop.machine_trace_of_loop)
    #[toExpr declName, data, ι, ← mkLambdaFVars #[i] D, ← mkLambdaFVars #[i] α,
      ← mkLambdaFVars #[i] inh, ← mkLambdaFVars #[i] rho]
  let sigmaName := declName ++ `machineSigma
  let sigmaV ← withLocalDeclD `x α fun x => do mkLambdaFVars #[i, x] (← loopSigma x n)
  addDef sigmaName (← inferType p).bindingDomain! sigmaV
  p := mkApp p (mkConst sigmaName)
  let initsName := declName ++ `machineInits
  let initsV ← loopSigmaInits regs
  addDef initsName (← inferType p).bindingDomain! initsV
  p := mkApp p (mkConst initsName)
  let bodyName := declName ++ `machineBody
  addDef bodyName (← inferType p).bindingDomain! (← mkLambdaFVars #[i, bools, bits] f)
  p := mkApp p (mkConst bodyName)
  let resName := declName ++ `machineRes
  addDef resName (← inferType p).bindingDomain! resV
  p := mkApp p (mkConst resName)
  let obsName := declName ++ `machineResult
  let obsV ← withLocalDeclD `r rho fun res => do
    mkLambdaFVars #[i, res] (listE (← mkArrow nat nat) (← resultObsOf declName r D res rho))
  addDef obsName (← inferType p).bindingDomain! obsV
  p := mkApp p (mkConst obsName)
  let srcName := declName ++ `machineSource
  addDef srcName (← inferType p).bindingDomain!
    (← mkLambdaFVars #[i, bools, bits] (listE (← mkArrow nat nat) (← resultObsOf declName r D src rho)))
  p := mkApp p (mkConst srcName)
  return (p, srcName, [(`machine_ok, false), (`machine_body, true), (`machine_inits, false),
    (`machine_reset, true), (`machine_writes, true), (`machine_result, true),
    (`machine_source, true)], none)
where
  /-- The reset tuple, from the registers' initial values. -/
  loopSigmaInits (regs : List (Lean.Expr × Lean.Expr × Lean.Expr)) : MetaM Lean.Expr := do
    let mut hl := mkConst ``Unit.unit
    for (_, init, _) in regs.reverse do
      hl ← mkAppM ``Prod.mk #[init, hl]
    return hl

/-! ### Sign extension and arithmetic right shift

The reader takes `signExtend` / `sshiftRight` / `Signal.ashr` in their
derived form (`Sparkle.Compiler.MachSignOps`), which is equal to the
operator by a theorem, not by evaluation. The generator rewrites the
declaration's value with the Signal-level equations
(`Tools.ShippingSignOps`), proves the endpoint for the rewritten value, and
transports it back to the declaration along the equation. -/

def hasSignOp (v : Lean.Expr) : Bool :=
  (v.find? fun e => e.isConstOf ``BitVec.signExtend || e.isConstOf ``BitVec.sshiftRight ||
    e.isConstOf ``Sparkle.Core.Signal.Signal.ashr).isSome

/-- The `(width, target)` pairs of the `signExtend`s of `e`, at literal widths. -/
partial def sextPairs (e : Lean.Expr) (acc : Array (Nat × Nat)) : Array (Nat × Nat) :=
  match e with
  | .app f a =>
    let acc := match e with
      | .app (.app (.app (.const ``BitVec.signExtend _) wE) vE) _ =>
        match canonicalNatLitValue? wE, canonicalNatLitValue? vE with
        | some w, some V => acc.push (w, V)
        | _, _ => acc
      | _ => acc
    sextPairs a (sextPairs f acc)
  | .lam _ t b _ | .forallE _ t b _ => sextPairs b (sextPairs t acc)
  | .letE _ t v b _ => sextPairs b (sextPairs v (sextPairs t acc))
  | .mdata _ b | .proj _ _ b => sextPairs b acc
  | _ => acc

/-- `h : f = g` applied to arguments: `f a₁ … aₙ = g a₁ … aₙ`. -/
def mkCongrFun' (h : Lean.Expr) (args : Array Lean.Expr) : MetaM Lean.Expr :=
  args.foldlM (fun h a => mkCongrFun h a) h

/-- `funext` over three variables. -/
def mkFunExt3 (x y z h : Lean.Expr) : MetaM Lean.Expr := do
  let h ← mkAppM ``funext #[← mkLambdaFVars #[z] h]
  let h ← mkAppM ``funext #[← mkLambdaFVars #[y] h]
  mkAppM ``funext #[← mkLambdaFVars #[x] h]

/-- `Signal.map (fun u => signExtend V u) x = sextS (V - w) x` for Signals of
`BitVec w`, every domain (`map_signExtend` at `k := V - w`; `(V - w) + w` is
`V` by evaluation). -/
def sextThm (w V : Nat) : MetaM Lean.Expr := do
  let k := V - w
  withLocalDeclD `dom (mkConst ``Sparkle.Core.Domain.DomainConfig) fun dom => do
  let bv (n : Nat) := mkApp (mkConst ``BitVec) (mkNatLit n)
  withLocalDeclD `x (mkApp2 (mkConst ``Sparkle.Core.Signal.Signal [.zero]) dom (bv w)) fun x => do
    let hw ← mkDecideProof (← mkLt (mkNatLit 0) (mkNatLit w))
    let pf := mkAppN (mkConst ``Tools.ShippingSignOps.map_signExtend) #[dom, mkNatLit k, mkNatLit w, hw, x]
    let lhs := mkAppN (mkConst ``Sparkle.Core.Signal.Signal.map [.zero]) #[dom, bv w, bv V,
      .lam `u (bv w) (mkApp3 (mkConst ``BitVec.signExtend) (mkNatLit w) (mkNatLit V) (.bvar 0)) .default, x]
    let rhs := mkAppN (mkConst ``Tools.ShippingSignOps.sextS) #[dom, mkNatLit k, mkNatLit w, x]
    let ty := mkApp3 (mkConst ``Eq [.one]) (mkApp2 (mkConst ``Sparkle.Core.Signal.Signal [.zero]) dom (bv V))
      lhs rhs
    mkLambdaFVars #[dom, x] (← mkExpectedTypeHint pf ty)

/-- The value with every sign operation rewritten to its derived form, and
the equation (`none` when there is none to rewrite). -/
def signNormalize (declName : Name) (v : Lean.Expr) : MetaM (Lean.Expr × Option Lean.Expr) := do
  if !hasSignOp v then return (v, none)
  let mut thms : SimpTheorems := {}
  for n in [``Tools.ShippingSignOps.ashr_eq, ``Tools.ShippingSignOps.map_sshiftRight,
      ``Tools.ShippingSignOps.lift_sshiftRight, ``Tools.ShippingSignOps.ap_sshiftRight] do
    thms ← thms.addConst n
  -- sign extension: one theorem per (width, target) pair met
  for (w, V) in (sextPairs v #[]).toList.eraseDups do
    if V ≤ w || w == 0 then continue
    thms ← thms.add (.other (Name.mkSimple s!"sext_{w}_{V}")) #[] (← sextThm w V)
  let cfg : Simp.Config := {}
  let cfg := { cfg with zeta := false }
  let cfg := { cfg with decide := true }
  let ctx ← Simp.mkContext (config := cfg)
    (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simp v ctx
  if hasSignOp r.expr then
    throwError "{declName}: a sign operation is left after the rewriting to the derived forms"
  return (r.expr, some (← match r.proof? with
    | some p => pure p
    | none => mkEqRefl v))

/-- The machine endpoint of `declName`: the definitions, the six kernel
checks, the theorem (whose name is returned). `checkCloses` also runs the
machine synthesis and checks that it ties the `let`s (the `MachineCloses`
boundary, in this environment). -/
partial def generateCore (declName : Name) (checkCloses : Bool) : MetaM Name := do
  progress s!"{declName}: reading"
  let r ← readMachine declName
  -- the children's own endpoints first (a sequential child's facts are used)
  -- (only a parent with state reads them; a child the certified gate
  -- compiles is combinational and has none)
  if !r.shape.instFields.isEmpty && !r.shape.layout.slots.isEmpty then
    for c in (r.shape.insts.map (·.1)).eraseDups do
      unless (← getEnv).contains (c ++ `machine_sound) do
        if (← try discard (readMachine c); pure true catch _ => pure false) then
          discard <| generateCore c checkCloses
  let dataName := declName ++ `machineData
  progress s!"{declName}: data"
  addDef dataName (mkConst ``MachineData) (← dataE r)
  progress s!"{declName}: data added"
  let data := mkConst dataName
  if checkCloses then
    let translate : TranslateFn := fun e h t n => translateExprToWire e h t n
    unless (← synthesizeMachineCertified translate (fun _ => pure ()) declName r.shape).isSome do
      throwError "{declName}: the machine synthesis does not tie the lets"
  let some entryV := r.entry.value? | throwError "{declName}: no value"
  let bsIn := r.shape.binders.take r.nDecl
  -- the family of domains: every domain for a domain binder, one otherwise
  let poly := bsIn.any fun b => b.2 == .domain
  let domT := mkConst ``Sparkle.Core.Domain.DomainConfig
  let ι := if poly then domT else mkConst ``Unit
  withLocalDeclD `i ι fun i => do
    let D := if poly then i else r.srcDom
    let nat := mkConst ``Nat
    let sig (α : Lean.Expr) := mkApp2 (mkConst ``Sparkle.Core.Signal.Signal [.zero]) D α
    let boolsT ← mkArrow nat (sig (mkConst ``Bool))
    let bitsT := Lean.Expr.forallE `j nat
      (.forallE `n nat (sig (mkApp (mkConst ``BitVec) (.bvar 0))) .default) .default
    withLocalDeclD `bools boolsT fun bools => withLocalDeclD `bits bitsT fun bits => do
    -- a tuple-typed input is its packed port, unpacked (`MachTupleIn`)
    let rec binderTys : Lean.Expr → List Lean.Expr
      | .forallE _ t b _ => t :: binderTys b
      | _ => []
    let tys := binderTys r.entry.type
    let args := ((List.range bsIn.length).zip bsIn).map fun (p, b) =>
      match b.2 with
      | .domain => D
      | .bool => mkApp bools (mkNatLit p)
      | .bits w =>
        match (tys[p]?).bind Sparkle.Compiler.MachTupleIn.tupleInput? with
        | some (_, ws) => Sparkle.Compiler.MachTupleIn.unpackE D ws (mkApp2 bits (mkNatLit p) (mkNatLit w))
        | none => mkApp2 bits (mkNatLit p) (mkNatLit w)
    let src := mkAppN (mkConst declName) args.toArray
    -- sign operations: the endpoint is proved for the rewritten value
    let (entryN, normPf?) ← signNormalize declName entryV
    let srcN := if normPf?.isSome then entryN.beta args.toArray else src
    let inst := Sparkle.Compiler.MachRawSurface.rootFloat (entryN.beta args.toArray)
    let (p, srcName, checks, extra) ←
      if r.shape.layout.slots.isEmpty && !r.shape.instFields.isEmpty then
        combCallsProof declName r data ι i D bools bits srcN inst
      else if r.shape.layout.slots.isEmpty then combProof declName r data ι i D bools bits srcN inst
      else if !r.shape.loops.isEmpty && r.shape.runs.isEmpty then
        loopProof declName r data ι i D bools bits srcN inst
      else if r.nested || !r.shape.loops.isEmpty then nestedProof declName r data ι i D bools bits srcN inst
      else if !r.shape.instFields.isEmpty then causalProof declName r data ι i D bools bits srcN inst
      else singleProof declName r data ι i D bools bits srcN inst
    let mut p := p
    for (suffix, left) in checks do
      let stmt := (← inferType p).bindingDomain!
      let name := declName ++ suffix
      let proof ← reflProof stmt left
      let t0 ← IO.monoMsNow
      progress s!"{name}: checking"
      try
        addDecl (.thmDecl { name, levelParams := [], type := stmt, value := proof })
      catch ex =>
        throwError "{declName}: {suffix} is not checked by the kernel: {ex.toMessageData}"
      trace[Sparkle.machine] "{name}: {(← IO.monoMsNow) - t0} ms"
      p := mkApp p (mkConst name)
    -- the pointwiseness of the hardware-module calls' extension
    if let some hext := extra then
      p := mkApp p hext
    -- a telescope's loops start at their reset values (`Tele.InitOk`)
    if let .forallE _ dT _ _ := (← whnfR (← inferType p)) then
      if (dT.find? (·.isConstOf ``Tools.ShippingMachineTele.Tele.InitOk)).isSome then
        p := mkApp p (← initOkProof dT)
    progress s!"{declName}: theorem"
    -- back to the declaration: its observations are the rewritten value's
    let mut srcName := srcName
    if let some pf := normPf? then
      let obsN := (← getConstInfo srcName).value!.beta #[i, bools, bits]
      let motObs ← kabstract obsN srcN
      unless motObs.hasLooseBVars do throwError "{declName}: the observations do not read the source"
      let obsD := motObs.instantiate1 src
      let srcDecl := declName ++ `machineSourceDecl
      addDef srcDecl (← inferType (mkConst srcName)) (← mkLambdaFVars #[i, bools, bits] obsD)
      -- `src = srcN`: the declaration applied is its (inlined) value applied
      let hArgs ← mkCongrFun' pf args.toArray
      let hObs ← mkCongrArg (.lam `s (← inferType src) motObs .default) hArgs
      let hFun ← mkFunExt3 i bools bits hObs
      let heq ← mkExpectedTypeHint hFun (← mkEq (mkConst srcDecl) (mkConst srcName))
      let T ← inferType p
      let motT ← kabstract T (mkConst srcName)
      let hT ← mkCongrArg (.lam `s (← inferType (mkConst srcName)) motT .default) heq
      p ← mkEqMPR hT p
      srcName := srcDecl
    let soundName := declName ++ `machine_sound
    addDecl (.thmDecl
      { name := soundName, levelParams := [], type := ← inferType p, value := p })
    let mut names := [soundName]
    -- to the emitted Verilog, at the full entry (gates as premises); not for
    -- a module with instances (the gates are for assign + register modules)
    if r.shape.insts.isEmpty then
      let shipsName := declName ++ `machine_ships
      let ships := mkAppN (mkConst ``Tools.ShippingMachineShipping.machine_ships_checked)
        #[toExpr declName, data, ι, ← mkLambdaFVars #[i] D, mkConst srcName, mkConst soundName]
      addDecl (.thmDecl
        { name := shipsName, levelParams := [], type := ← inferType ships, value := ships })
      names := names ++ [shipsName]
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "{name} uses a non-standard axiom: {ax}"
    progress s!"{declName}: done"
    return soundName

/-- Generate the machine endpoint of `declName`; on failure nothing is
added. Every declaration is checked by the kernel before the next one is
built (no asynchronous checking), so a failed check is an exception here. -/
def generate (declName : Name) (checkCloses : Bool := true) : MetaM Name := do
  let saved ← getEnv
  try
    withOptions (fun o => Lean.Elab.async.set o false) (generateCore declName checkCloses)
  catch ex =>
    setEnv saved
    throw ex

open Lean.Elab Lean.Elab.Command in
/-- `#machine_endpoint f` adds the machine data of `f` and the theorem
`f.machine_sound`. -/
elab "#machine_endpoint " d:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← liftTermElabM (generate declName)
  logInfo m!"{name}: source circuit do → real entry → registers → trace, checked by the kernel"

end Tools.ShippingMachineCommand
