import Tools.ShippingGateKidFactsT
import Tools.ShippingKidsTyped
import Tools.ShippingWireNamesRun
import Tools.ShippingCallWidths
import Tools.ShippingPortsMatchRaw
import Tools.ShippingSVBridge
import Tools.ShippingGatePorts
-- Round par/cert. BUILT: ce1 (Tools.ShippingGateCert, …CertCommand, exit 0 for both; the test failed on missing `open`s), ce2 (the test, exit 0, 662 jobs; integrator fix: the opens repeated in the second namespace block).

/-! # The data certificate of a gate-collision parent (round par/cert)

Each gate-collision parent `p` (`collMixSame`, `collMixDiff`, `collMixArgs`, `collWidth`) had
five hand-written run lemmas `<p>_runFacts`, `<p>_outsG0`, `<p>_designP0`, `<p>_typedRun`,
`<p>_names` (`Tests/Compiler/MemNameCollisionGate{Closed,Typed,TypedAll,Bound}Test.lean`).
Each is ONE general lemma (`kidsC_runFactsT`, `kidsC_outsCheckT`, `kidsC_designCheckT`,
`core_typedRunMT`, `wireNames_runMT`) applied to the parent's reader data plus data conditions
decided one by one (`decide`), plus the per-entry kid facts and the closing.

Here:

* `gateParentCertOk d nDecl kidOuts kidIns : Bool` — the COMMON data conditions in one Bool
  (one `decide` per parent): `callsOk`, slot count, no late domain binder, `insts ≠ []`,
  `slots ≠ []`, `instFields ≠ []`, output types, `callWidthsOk`, `callArgsOk`, output-name
  characters, scalar output types;
* `gateParentFacts_of_ok` — its soundness (the eleven Props the general lemmas ask);
* `gateParent_runFacts`, `gateParent_outsG0`, `gateParent_designP0`, `gateParent_typedRun`,
  `gateParent_names` — the five run lemmas from the certificate, the parent's `machine_ok` /
  `machine_body`, the per-entry kid facts (`hkid`, and `hkidF` for the typed bound) and the
  closing. Their conclusions are exactly those of the hand-written lemmas (the shapes the head
  `Tools.ShippingNoPortsTyped.machine_design_noPortsTB` asks in `hFacts`, `hOuts`, `hTyped`,
  `hDesign`, `hNames`); the per-parent `hR0` is not an argument here (it only enters through
  the kid facts and the closing).
  Argument order (for `mkAppM` in `Tools.ShippingGateCertCommand.generateCert`):
  `d ok hbody hcert hkid [hkidF] closes hcore hpost entry [hg] hB`.
* `memGate_kids`, `memGate_kidTyped` — the per-entry kid facts of a parent whose every entry is
  ONE memory origin `.mem cb aw dw` or the `.ord` call of ONE gate child `c`, generically (the
  per-parent `<p>_kids` / `<p>_kidTyped` were each this proof at concrete data). What stays per
  parent: the entry table (`hentry`, decided), the gate child's reflection `hR0` and its gate
  facts (`old`, `peel`, `wf`, binder positions, result width ≠ 1).

NOT covered: the reflection boundary (`EntryDefines` / `MachineDefines` stay premises), the
closing `MachineClosesAt` (an argument; per parent `<p>_closesR`), runtime / extern, output-string
semantics. No new fact about the compiler; nothing added to `RefLaws` or a trusted list. -/

namespace Tools.ShippingGateCert
open Lean
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Sparkle.IR.Machine (OutField)
open Tools.ShippingMachineAuto (MachineData)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-! ## The certificate -/

/-- **The common data conditions of a gate-collision parent**, as one Bool (decided once per
parent). Each conjunct is one data premise of the general run lemmas. -/
def gateParentCertOk (d : MachineData) (nDecl : Nat) (kidOuts : Nat → List OutField)
    (kidIns : Nat → List Nat) : Bool :=
  d.callsOk nDecl &&
  decide (d.ss.length = d.shape.layout.slots.length) &&
  decide (∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain) &&
  decide (d.shape.insts.length ≠ 0) &&
  decide (d.shape.layout.slots.length ≠ 0) &&
  decide (d.shape.instFields.length ≠ 0) &&
  decide (∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width) &&
  Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts &&
  Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns &&
  decide (∀ o ∈ d.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true) &&
  decide (∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)

/-- The data premises of the general run lemmas (what `gateParentCertOk` certifies). -/
structure GateParentFacts (d : MachineData) (nDecl : Nat) (kidOuts : Nat → List OutField)
    (kidIns : Nat → List Nat) : Prop where
  hC : d.callsOk nDecl = true
  hslots : d.ss.length = d.shape.layout.slots.length
  hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain
  hins : d.shape.insts ≠ []
  hsl : d.shape.layout.slots ≠ []
  hfne : d.shape.instFields ≠ []
  outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width
  hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true
  hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true
  hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name
  hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true

/-- `a && b` is `true` only if both are. -/
theorem and_split {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

/-- **Soundness of the certificate.** -/
theorem gateParentFacts_of_ok {d : MachineData} {nDecl : Nat} {kidOuts : Nat → List OutField}
    {kidIns : Nat → List Nat} (h : gateParentCertOk d nDecl kidOuts kidIns = true) :
    GateParentFacts d nDecl kidOuts kidIns := by
  unfold gateParentCertOk at h
  obtain ⟨h, hoty⟩ := and_split h
  obtain ⟨h, hchars⟩ := and_split h
  obtain ⟨h, hargs⟩ := and_split h
  obtain ⟨h, hcw⟩ := and_split h
  obtain ⟨h, houtTy⟩ := and_split h
  obtain ⟨h, hfne⟩ := and_split h
  obtain ⟨h, hsl⟩ := and_split h
  obtain ⟨h, hins⟩ := and_split h
  obtain ⟨h, hdomB⟩ := and_split h
  obtain ⟨hC, hslots⟩ := and_split h
  -- (writing-time guess, accepted by build ce1/ce2: `of_decide_eq_true` picks up the same `Decidable` instances the
  -- definition elaborated, since both are synthesized at a generic `d`)
  exact
    { hC := hC
      hslots := of_decide_eq_true hslots
      hdomB := of_decide_eq_true hdomB
      hins := fun h0 => absurd (congrArg List.length h0) (of_decide_eq_true hins)
      hsl := fun h0 => absurd (congrArg List.length h0) (of_decide_eq_true hsl)
      hfne := fun h0 => absurd (congrArg List.length h0) (of_decide_eq_true hfne)
      outTy := of_decide_eq_true houtTy
      hcw := hcw
      hargs := hargs
      hon := fun o ho =>
        Tools.ShippingSVBridge.sanitizeName_of_clean (of_decide_eq_true hchars o ho)
      hoty := of_decide_eq_true hoty }

/-! ## The five run lemmas from the certificate -/

/-- **The run's facts of the full entry's module** (`kidsC_runFactsT` at the certificate). -/
theorem gateParent_runFacts {c : Name} {nDecl : Nat} {kidOuts : Nat → List OutField}
    {kidIns : Nat → List Nat} {n : Nat} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.vpos j))
      d.packed)
    (hcert : gateParentCertOk d nDecl kidOuts kidIns = true)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      Tools.ShippingMemKid.KidFactsTC mref cref (Tools.ShippingInstTagged.originAt d.shape k)
        (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref c d.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore c [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref c d.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  have F := gateParentFacts_of_ok hcert
  Tools.ShippingMemKid.kidsC_runFactsT d ok hbody F.hC F.hslots F.hdomB F.hins F.hsl F.hfne
    F.outTy kidOuts kidIns n hkid F.hcw hB hcore hpost entry closes

/-- **The output check at depth `n` under the statement-kind gate** (`kidsC_outsCheckT`). -/
theorem gateParent_outsG0 {c : Name} {nDecl : Nat} {kidOuts : Nat → List OutField}
    {kidIns : Nat → List Nat} {n : Nat} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.vpos j))
      d.packed)
    (hcert : gateParentCertOk d nDecl kidOuts kidIns = true)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      Tools.ShippingMemKid.KidFactsTC mref cref (Tools.ShippingInstTagged.originAt d.shape k)
        (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref c d.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore c [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref c d.shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) n
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  have F := gateParentFacts_of_ok hcert
  Tools.ShippingMemKid.kidsC_outsCheckT d ok hbody F.hC F.hslots F.hdomB F.hins F.hfne F.outTy
    kidOuts kidIns n hkid hB hcore hpost entry closes hg

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth `n` of the shipped module, with no check premise**
(`kidsC_designCheckT`). -/
theorem gateParent_designP0 {c : Name} {nDecl : Nat} {kidOuts : Nat → List OutField}
    {kidIns : Nat → List Nat} {n : Nat} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.vpos j))
      d.packed)
    (hcert : gateParentCertOk d nDecl kidOuts kidIns = true)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      Tools.ShippingMemKid.KidFactsTC mref cref (Tools.ShippingInstTagged.originAt d.shape k)
        (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref c d.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore c [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref c d.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) n
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  have F := gateParentFacts_of_ok hcert
  Tools.ShippingMemKid.kidsC_designCheckT d ok hbody F.hC F.hslots F.hdomB F.hins F.hsl F.hfne
    F.outTy kidOuts kidIns n hkid F.hcw F.hargs hB hcore hpost entry closes F.hon F.hoty

set_option maxHeartbeats 4000000 in
/-- **The typed children bound of the full entry's module** (`core_typedRunMT`). -/
theorem gateParent_typedRun {c : Name} {nDecl : Nat} {kidOuts : Nat → List OutField}
    {kidIns : Nat → List Nat} {n : Nat} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.vpos j))
      d.packed)
    (hcert : gateParentCertOk d nDecl kidOuts kidIns = true)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      Tools.ShippingMemKid.KidFactsTC mref cref (Tools.ShippingInstTagged.originAt d.shape k)
        (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hkidF : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingInstTagged.KidT mref cref (Tools.ShippingInstTagged.originAt d.shape k)
        (d.shape.insts[k]).1 y →
      Tools.ShippingMemKid.FlatOk y.1 ∨ Tools.ShippingKidsTyped.KidTyped y.1)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref c d.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore c [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref c d.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingKidsTyped.TypedRun (Tools.ShippingMachineLinked.childMap D.modules) b
      Tools.ShippingMachineShipsHier.mixInv :=
  have F := gateParentFacts_of_ok hcert
  Tools.ShippingKidsTyped.core_typedRunMT d ok hbody F.hC F.hslots F.hdomB F.hins F.hfne F.outTy
    kidOuts kidIns n hkid F.hargs hkidF hB hcore hpost entry closes F.hon F.hoty

set_option maxHeartbeats 4000000 in
/-- **The name facts of the full entry's module, from the core run** (`wireNames_runMT`).
`kidOuts` / `kidIns` enter only through the certificate (its `callWidthsOk` / `callArgsOk`
conjuncts are not used here). -/
theorem gateParent_names {c : Name} {nDecl : Nat} {kidOuts : Nat → List OutField}
    {kidIns : Nat → List Nat} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.vpos j))
      d.packed)
    (hcert : gateParentCertOk d nDecl kidOuts kidIns = true)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref c d.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore c [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref c d.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    (b.wires.map (·.name)).Nodup ∧
      ∀ p ∈ b.wires ++ b.inputs ++ b.outputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name :=
  have F := gateParentFacts_of_ok hcert
  Tools.ShippingWireNamesRun.wireNames_runMT d ok hbody F.hC F.hslots F.hdomB F.hins F.outTy
    F.hfne hB hcore hpost entry closes F.hon F.hoty

/-! ## Generic kid facts: one memory origin and one gate child -/

open Sparkle.Compiler.Elab (MixedGateBinder certifiedShape? mixedGatePeel) in
open Tools.ShippingUnifiedSource (SType Term quote) in
/-- **`KidFactsTC` of every entry** of a parent whose entries are the memory origin
`.mem cb aw dw` or the `.ord` call of the gate child `c` (`hentry`, decided per parent), at
depth 0, for any `outsF` / `insF` that read `memOuts` / `memIns` at the memory origin and
`gateOuts` / `gateIns` at `.ord` (`rfl` for the tests' `outsG` / `insG` / `outsFN` / `insFN`).
The proof is the per-parent `<p>_kids`' at generic data. -/
theorem memGate_kids {cb : Bool} {aw dw : Nat} {c : Name}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (d : MachineData) (outsF : InstOrigin → List OutField) (insF : InstOrigin → List Nat)
    (hmo : outsF (.mem cb aw dw) = Tools.ShippingMemKid.memOuts dw)
    (hmi : insF (.mem cb aw dw) = Tools.ShippingMemKid.memIns aw dw)
    (hgo : outsF .ord = Tools.ShippingMemKid.gateOuts srt.width)
    (hgi : insF .ord = Tools.ShippingMemKid.gateIns bs)
    (hentry : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      Tools.ShippingInstTagged.originAt d.shape k = .mem cb aw dw ∨
        (Tools.ShippingInstTagged.originAt d.shape k = .ord ∧ (d.shape.insts[k]).1 = c))
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref c value)
    (old : ∀ dv : DefinitionVal, dv.value = value → certifiedShape? false [] (.defnInfo dv) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (bpos j))
        (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (hw1 : srt.width ≠ 1) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length),
      Tools.ShippingMemKid.KidFactsTC mref cref (Tools.ShippingInstTagged.originAt d.shape k)
        (d.shape.insts[k]).1 (outsF (Tools.ShippingInstTagged.originAt d.shape k))
        (insF (Tools.ShippingInstTagged.originAt d.shape k)) 0 := by
  intro k hk
  rcases hentry k hk with ho | ⟨ho, hn⟩
  · rw [ho, hmo, hmi]
    exact (Tools.ShippingMemKid.memKidT_facts (Tools.ShippingInstTagged.child?_mem cb aw dw)).toC
  · rw [ho, hn, hgo, hgi]
    exact Tools.ShippingMemKid.gateKidT_factsC (o := InstOrigin.ord) (c := c) (bs := bs) rfl hR0
      old peel he hb hv hw1 0

open Sparkle.Compiler.Elab (MixedGateBinder certifiedShape? mixedGatePeel) in
open Tools.ShippingUnifiedSource (SType Term quote) in
/-- **Per kid, by origin: the memory entry `FlatOk`, the gate entry `KidTyped`** (the
per-parent `<p>_kidTyped`' proof at generic data). -/
theorem memGate_kidTyped {cb : Bool} {aw dw : Nat} {c : Name}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (d : MachineData)
    (hentry : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      Tools.ShippingInstTagged.originAt d.shape k = .mem cb aw dw ∨
        (Tools.ShippingInstTagged.originAt d.shape k = .ord ∧ (d.shape.insts[k]).1 = c))
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref c value)
    (old : ∀ dv : DefinitionVal, dv.value = value → certifiedShape? false [] (.defnInfo dv) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (bpos j))
        (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingInstTagged.KidT mref cref (Tools.ShippingInstTagged.originAt d.shape k)
        (d.shape.insts[k]).1 y →
      Tools.ShippingMemKid.FlatOk y.1 ∨ Tools.ShippingKidsTyped.KidTyped y.1 := by
  intro k hk y hy
  rcases hentry k hk with ho | ⟨ho, hn⟩
  · rw [ho] at hy
    exact Or.inl ((Tools.ShippingMemKid.memKidT_facts
      (Tools.ShippingInstTagged.child?_mem cb aw dw)).flat y hy)
  · rw [ho, hn] at hy
    exact Or.inr (Tools.ShippingKidsTyped.kidTyped_of_gate
      (Tools.ShippingGatePorts.gate_real_ports (bs := bs) hR0 old peel he hb hv
        (Tools.ShippingInstTagged.KidT.real hy rfl)))

end Tools.ShippingGateCert
