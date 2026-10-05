import Tools.ShippingMachineAuto
import Tools.ShippingMachineNest
import Tools.ShippingMachineTeleNest
import Tools.ShippingMachineLoop
import Tools.ShippingMachineShipping
import Tools.ShippingSignOps

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
  let shape := mkApp6 (mkConst ``MachineShape.mk) (listE binderT (r.shape.binders.map binderE))
    body layout runs insts loops
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

/-- Walk an expression in the compiler's reading order (a `let`'s value
before its body, a function before its argument), with the local context
extended at every binder, applying `onRun` to every `runCircuitH`
application (which is not entered). -/
partial def walkRuns (onRun : Lean.Expr → MetaM Lean.Expr) : Lean.Expr → MetaM Lean.Expr
  | e@(.app ..) => do
    if e.isAppOfArity ``Sparkle.Core.runCircuitH 8 then onRun e else
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
    if e.isAppOfArity ``Sparkle.Core.runCircuitH 8 then onRun e else
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
  let some kinds := machSlotKinds αs | throwError "{declName}: a sub-machine's slot types"
  let ss ← kinds.mapM fun k => match sortOf k with
    | some s => pure s
    | none => throwError "{declName}: a sub-machine's slot kind"
  return (ss, listE stypeT (ss.map stypeE))

/-- Component `j` of a right-nested tuple. -/
def tupleProj (rs : Lean.Expr) (j : Nat) : Lean.Expr :=
  .proj ``Prod 0 ((List.range j).foldl (fun acc _ => .proj ``Prod 1 acc) rs)

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
      let a := runZ.getAppArgs
      let (_, ssE) := (← slotSortsE declName a[1]!)
      if a[6]!.hasFVar || a[5]!.hasFVar then
        throwError "{declName}: a sub-machine's reset values depend on a binder"
      let ρE ← mkLambdaFVars #[i] a[2]!
      let bodyE ← mkLambdaFVars #[i, bools, bits, regsF] a[7]!
      let inner := mkAppN (mkConst ``InnerT.mk) #[ι, domF, ss₂E, ssE, ρE, a[5]!, a[6]!, bodyE]
      occRef.modify (·.push known.size)
      runsRef.modify (·.push (runZ, inner))
    pure run) e0
  let inners := (← runsRef.get).map (·.2)
  let occ ← occRef.get
  let innerT := mkApp3 (mkConst ``InnerT) ι domF ss₂E
  let lE := listE innerT inners.toList .one
  unless inners.size == r.shape.runs.length - (if run?.isSome then 1 else 0) do
    throwError "{declName}: {inners.size} sub-machines found, the compiler read {r.shape.runs.length - (if run?.isSome then 1 else 0)}"
  -- a CHAIN: a sub-machine reading an earlier one's result (its body holds
  -- the earlier `runCircuitH`): the sub-machines are a telescope (`TeleT`),
  -- each body over the earlier results (`prev`, latest first)
  let runsZ0 := (← runsRef.get).map (·.1)
  let chain := (List.range runsZ0.size).any fun j =>
    (List.range j).any fun k => runsZ0[k]!.occurs runsZ0[j]!
  let typeT := mkSort (.succ .zero)
  let preList (j : Nat) : Lean.Expr :=
    listE typeT ((List.range j).reverse.map fun k => runsZ0[k]!.getAppArgs[2]!) .one
  let preE (j : Nat) : MetaM Lean.Expr := mkLambdaFVars #[i] (preList j)
  -- each body with the earlier sub-machines replaced by `prev`'s components
  let bodiesC ← (List.range runsZ0.size).mapM fun j =>
    withLocalDeclD `prev (hlistE (preList j)) fun pv => do
      let b := runsZ0[j]!.getAppArgs[7]!
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
def generateCore (declName : Name) (checkCloses : Bool) : MetaM Name := do
  progress s!"{declName}: reading"
  let r ← readMachine declName
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
      if r.shape.layout.slots.isEmpty then combProof declName r data ι i D bools bits srcN inst
      else if !r.shape.loops.isEmpty then loopProof declName r data ι i D bools bits srcN inst
      else if r.nested then nestedProof declName r data ι i D bools bits srcN inst
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
