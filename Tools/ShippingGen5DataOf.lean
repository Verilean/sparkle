import Tools.ShippingGen5DataOfPure
import Tools.ShippingGen5DataOfPure2
import Tools.ShippingReaderApp
import Tools.ShippingMachineCommand
set_option autoImplicit false
-- BUILT: clean issue-linked build do4v-8b57cc6e exit 0 (762 jobs, Tests.Gen5.DataOfCheck3 + DataOfCheck2 targets together); conditional results only, reviewer changes_requested on the Check closure audit addressed in Tests/Gen5/DataOfCheck.lean (not yet clean-built) (DG-DATAOF `dataOfFrom` / `dataOfAt` and their CONDITIONAL soundness;
-- scripts/gen5/DG_DATAOF_FREEZE.md rev2 §2.4a Q5). No sorry / axiom / native_decide.

/-! # DG-DATAOF: `dataOfFrom`, `dataOfAt`

`dataOfFrom` is the pure part of `readMachine` (`Tools/ShippingMachineCommand.lean:440-541`) with the results of the two
`partial` helpers (`packTupleInputs entryV`, `rootFloat`) given as ARGUMENTS; `dataOfAt` supplies them.

What is proved: `dataOfFrom_sound` / `dataOfAt_sound` are CONDITIONAL on `dataOfFrom ... = some d` and hold for every
`tin`, `fl`, `lvl`. Soundness comes from the structural checks of the function itself (`readN`'s soundness, the structural
comparison `bitsBeq`, and the guard `d.ok`), NOT from the re-pack: the declared width of a `.bits n` binder comes from the
`ok` rows (`Tools.ShippingGen5DataOfPure2.ok_K_nexts / ok_letsTyped / ok_outsFit`), the re-pack does not supply it.

What is NOT here: that `dataOfAt` is `some` on any run (coverage, DG-COVER), the connection of `tin`/`fl` to the values
the compiler's shape layer used (S-COV-FLOAT), the connection to `readMachine`'s output or to the compiler's actual reader,
the existence of a quotation for a successful run (C-CMP / C-QWIT), termination of the `partial` helpers (T-X).
`dataOf` (at DG-READKINDS's `exprSize`) is not defined: that module is not in this tree. -/
namespace Tools.ShippingGen5DataOf
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineCommand
open Tools.ShippingMachineEntry Tools.ShippingReaderInputs Tools.ShippingReaderApp
open Tools.ShippingReaderTerm Tools.ShippingGen5DataOfPure Tools.ShippingGen5DataOfPure2
open Tools.ShippingMixedSourceBridge (inputExpr)
open Sparkle.Core Sparkle.IR.Machine Sparkle.Compiler.Elab

/-! ## The domain of the data (readMachine :476-509), total -/

/-- `readMachine` :479-483, the `loopLet` search. -/
def loopLet (k : Nat) : Lean.Expr → Option (Lean.Expr × Nat)
  | .letE _ _ v b _ =>
    if v.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then some (v.getAppArgs[0]!, k)
    else loopLet (k + 1) b
  | _ => none

/-- `readMachine` :487-495, the `resDom` search. -/
def resDom (senv : StructEnv) : Lean.Expr → Nat → Option (Lean.Expr × Nat)
  | .forallE _ _ b _, k => resDom senv b (k + 1)
  | e, _ =>
    match e.getAppFn, e.getAppArgs.toList with
    | .const ``Sparkle.Core.Signal.Signal _, [d, _] => some (d, 0)
    | .const s _, [d] => if (senv.fields s).isSome then some (d, 0) else none
    | _, _ => none

/-- `readMachine` :476-501: the source domain and the number of root `let`s enclosing it. -/
def srcDomOf (senv : StructEnv) (ty : Lean.Expr) (entryBody : Lean.Expr) : Option (Lean.Expr × Nat) :=
  let r := machRoot senv.proj entryBody []
  match r.2.2.1 with
  | some run => some (run.getAppArgs[0]!, r.1.length)
  | none =>
    match entryBody.find? fun t => t.isAppOfArity ``Sparkle.Core.runCircuitH 8 with
    | some run => some (run.getAppArgs[0]!, r.1.length)
    | none =>
      match loopLet 0 entryBody with
      | some x => some x
      | none => resDom senv ty 0

/-- `readMachine` :502-509: the placeholder form of the domain. -/
def srcDom'Of (srcDom : Lean.Expr) (depth : Nat) : Option Lean.Expr :=
  match srcDom with
  | .bvar j => if j < depth then none else some (machIn (j - depth))
  | e => some e

/-- The front part of `readMachine` (`:466-514`): from the two helper RESULTS to `(nIn, dom)`.
`tin = packTupleInputs entryV`, `fl = rootFloat` are ordinary arguments here. -/
def dataOfFront (E : Lean.ConstantInfo) (senv : StructEnv) (shape : MachineShape)
    (tin : Lean.Expr) (fl : Lean.Expr → Lean.Expr) : Option (Nat × Lean.Expr) :=
  (mixedGatePeel tin).bind fun p =>
    let entryBody := fl p.2
    let nIn := p.1.length + shape.insts.length
    let nSlots := shape.layout.slots.length
    let nLets := shape.layout.lets
    if shape.binders.length == nIn + nSlots + nLets then
      (srcDomOf senv E.type entryBody).bind fun sd =>
      (srcDom'Of sd.1 sd.2).bind fun sd' =>
      (machDom? (shape.insts.length + nSlots + nLets) sd').bind fun dr =>
      ((match machTupleKinds? E.type with
        | some _ => some ()
        | none => (machOuts? senv E.type).map fun _ => ())).bind fun _ =>
      some (nIn, dr.1)
    else none

/-! ## The core (readMachine :515-537), with the reader `readN` in place of `unq` -/

/-- `readMachine`'s `typed`. -/
def typedFields (ks : List MixedGateBinder) (fs : List (Σ w : Nat, Term (.bits w))) :
    Option (List (Σ s : SType, Term s)) :=
  (ks.zip fs).mapM fun p => unField p.1 p.2

/-- The record `readMachine` returns (`:535-537`), restricted to `MachineData`'s fields. -/
def mkData (shape : MachineShape) (nIn : Nat) (dom : Lean.Expr)
    (ls outs nl : List (Σ s : SType, Term s)) : MachineData :=
  { shape := shape, nIn := nIn, dom := dom
    bposL := ((List.range (shape.binders.map (·.2)).length).zip (shape.binders.map (·.2))).filterMap
      fun (pk : Nat × MixedGateBinder) => if pk.2 == .bool then some pk.1 else none
    vposL := ((List.range (shape.binders.map (·.2)).length).zip (shape.binders.map (·.2))).filterMap
      fun (pk : Nat × MixedGateBinder) => match pk.2 with | .bits _ => some pk.1 | _ => none
    vwL := ((List.range (shape.binders.map (·.2)).length).zip (shape.binders.map (·.2))).filterMap
      fun (pk : Nat × MixedGateBinder) => match pk.2 with | .bits w => some w | _ => none
    ss := nl.map (·.1), ls := ls, outs := outs, nexts := termsOfAny nl }

/-- The two final guards: the structural re-pack comparison (width AND term, no `Expr.equal`) and `d.ok`. -/
def checked (W : Nat) (whole : Term (.bits W)) (d : MachineData) : Option MachineData :=
  if bitsBeq ⟨W, whole⟩ ⟨_, d.packed⟩ && d.ok then some d else none

/-- After the body is read as `⟨.bits W, whole⟩`. -/
def dataOfTail (shape : MachineShape) (nIn : Nat) (dom : Lean.Expr) (W : Nat) (whole : Term (.bits W)) :
    Option MachineData :=
  let kinds := shape.binders.map (·.2)
  let nSlots := shape.layout.slots.length
  let nOuts := shape.layout.outs.length
  (splitLets shape.layout.lets ⟨W, whole⟩).bind fun lc =>
  (splitFields (nOuts + nSlots) lc.2).bind fun fs =>
  (typedFields (kinds.drop (nIn + nSlots)) lc.1).bind fun ls =>
  (typedFields (shape.layout.outs.map outKind) (fs.take nOuts)).bind fun outs =>
  (typedFields ((kinds.drop nIn).take nSlots) (fs.drop nOuts)).bind fun nl =>
  checked W whole (mkData shape nIn dom ls outs nl)

def dataOfCore (lvl : Lean.Expr → Nat) (shape : MachineShape) (nIn : Nat) (dom : Lean.Expr) :
    Option MachineData :=
  match readN (kindsCfg dom (isExpr dom) (shape.binders.map (·.2))) (lvl shape.body) shape.body with
  | some ⟨.bits W, whole⟩ => dataOfTail shape nIn dom W whole
  | _ => none

/-- `dataOfAt` with the results of the two `partial` helpers given as ARGUMENTS. -/
def dataOfFrom (lvl : Lean.Expr → Nat) (E : Lean.ConstantInfo) (senv : StructEnv) (shape : MachineShape)
    (tin : Lean.Expr) (fl : Lean.Expr → Lean.Expr) : Option MachineData :=
  (dataOfFront E senv shape tin fl).bind fun p => dataOfCore lvl shape p.1 p.2

/-- The only place the `partial` helpers occur. -/
def dataOfAt (lvl : Lean.Expr → Nat) (E : Lean.ConstantInfo) (senv : StructEnv) (shape : MachineShape) :
    Option MachineData :=
  match E.value? with
  | none => none
  | some entryV =>
    dataOfFrom lvl E senv shape (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV)
      Sparkle.Compiler.MachRawSurface.rootFloat

/-! ## Conditional soundness -/

theorem checked_sound {W : Nat} {whole : Term (.bits W)} {d d' : MachineData}
    (h : checked W whole d = some d') :
    d' = d ∧ d.ok = true ∧ (⟨W, whole⟩ : Σ w : Nat, Term (.bits w)) = ⟨_, d.packed⟩ := by
  unfold checked at h
  by_cases hc : (bitsBeq ⟨W, whole⟩ ⟨_, d.packed⟩ && d.ok) = true
  · rw [if_pos hc] at h
    have hd : d = d' := Option.some.inj h
    simp only [Bool.and_eq_true] at hc
    exact ⟨hd.symm, hc.2, bitsBeq_eq hc.1⟩
  · rw [if_neg hc] at h
    cases h

theorem dataOfTail_sound {shape : MachineShape} {nIn : Nat} {dom : Lean.Expr} {W : Nat} {whole : Term (.bits W)}
    {d : MachineData} (h : dataOfTail shape nIn dom W whole = some d) :
    d.shape = shape ∧ d.dom = dom ∧ d.ok = true ∧
      (⟨W, whole⟩ : Σ w : Nat, Term (.bits w)) = ⟨_, d.packed⟩ ∧
      d.bposL = posB 0 (shape.binders.map (·.2)) ∧ d.vposL = posV 0 (shape.binders.map (·.2)) := by
  unfold dataOfTail at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨_, _, hc⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨rfl, hok, hbeq⟩ := checked_sound hc
  exact ⟨rfl, rfl, hok, hbeq, bposL_eq _, vposL_eq _⟩

theorem dataOfCore_sound (lvl : Lean.Expr → Nat) {shape : MachineShape} {nIn : Nat} {dom : Lean.Expr}
    {d : MachineData} (h : dataOfCore lvl shape nIn dom = some d) :
    d.shape = shape ∧ d.ok = true ∧
    d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed := by
  unfold dataOfCore at h
  split at h
  · rename_i W whole hr
    obtain ⟨hs, hd, hok, hbeq, hb, hv⟩ := dataOfTail_sound h
    refine ⟨hs, hok, ?_⟩
    obtain ⟨hw, hr'⟩ := Sigma.mk.inj hbeq
    subst hw
    have hwh := eq_of_heq hr'
    subst hwh
    have hq := (readN_expr_sound dom (shape.binders.map (·.2)) _ shape.body _ hr).1
    have hbp : ∀ j, d.bpos j = (posB 0 (shape.binders.map (·.2))).getD j 0 := fun j => by
      unfold MachineData.bpos; rw [hb]
    have hvp : ∀ j, d.vpos j = (posV 0 (shape.binders.map (·.2))).getD j 0 := fun j => by
      unfold MachineData.vpos; rw [hv]
    have hl : d.shape.binders.length = (shape.binders.map (·.2)).length := by
      rw [hs, List.length_map]
    simp only [hbp, hvp, hl, hd]
    rw [hs]
    exact hq.symm
  · cases h

theorem dataOfFrom_sound (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData}
    (h : dataOfFrom lvl E senv s tin fl = some d) :
    d.shape = s ∧ d.ok = true ∧
    d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.initOk (initsOf d) = true := by
  unfold dataOfFrom at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨p, _, hc⟩ := h
  obtain ⟨h1, h2, h3⟩ := dataOfCore_sound lvl hc
  exact ⟨h1, h2, h3, initOk_of_ok d h2⟩

theorem dataOfAt_sound (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {d : MachineData} (h : dataOfAt lvl E senv s = some d) :
    d.shape = s ∧ d.ok = true ∧
    d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.initOk (initsOf d) = true := by
  unfold dataOfAt at h
  split at h
  · cases h
  · exact dataOfFrom_sound lvl h

end Tools.ShippingGen5DataOf
