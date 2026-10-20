import Tools.ShippingGateCert
import Tools.ShippingGateChild
-- BUILT as written: cf1 (exit 0, 665 jobs; round par/cert2).

/-! # The kid side of a gate-collision parent as ONE decided Bool (round par/cert2)

`Tools.ShippingGateCert.memGate_kids` / `memGate_kidTyped` still ask, per parent, the entry
table `hentry` (the hand-written `<p>_entry`, one `decide`), the binder positions of the gate
child (`bool_positions (by decide)`, `bits_positions (by decide)`) and its result width ≠ 1
(`fakeSrc_width` / `fakeN_width`). Here:

* `memGateEntryOk d cb aw dw c : Bool` — the ORIGIN TABLE: every entry is the memory origin
  `.mem cb aw dw` or the `.ord` call of `c` (`memGateEntry_of_ok` its soundness);
* `memGateOk d cb aw dw c bs bposL vposL vwL w : Bool` — the origin table, the gate child's
  binder positions (`boolPositionsOk`, `bitsPositionsOk`) and `w ≠ 1`, in one Bool;
* `memGate_kidsS`, `memGate_kidTypedS` — `memGate_kids` / `memGate_kidTyped` from that one
  Bool and the gate facts in the form `#gate_child` / `gateDefs` write them (`peel` at
  `bposL.getD j 0` / `vposL.getD j 0`, `wf` at `bposL.length vposL.length (vwL.getD · 0)`).

Explicit argument order (for `mkAppM` in `Tools.ShippingGateCert2Command.generateCert2`):
`memGate_kidsS d cb aw dw c outsF insF hok hmo hmi hgo hgi hR0 old peel he`,
`memGate_kidTypedS d cb aw dw c hok hR0 old peel he`.

No new fact about the compiler; nothing added to `RefLaws` or a trusted list. The reflection
`hR0` stays a premise. -/

namespace Tools.ShippingGateCert2
open Lean
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Sparkle.IR.Machine (OutField)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingGateCert (and_split)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **The origin table**: every entry is the memory origin `.mem cb aw dw` or the `.ord` call of
`c`. -/
def memGateEntryOk (d : MachineData) (cb : Bool) (aw dw : Nat) (c : Name) : Bool :=
  decide (∀ (k : Nat) (hk : k < d.shape.insts.length),
    Tools.ShippingInstTagged.originAt d.shape k = .mem cb aw dw ∨
      (Tools.ShippingInstTagged.originAt d.shape k = .ord ∧ (d.shape.insts[k]).1 = c))

theorem memGateEntry_of_ok {d : MachineData} {cb : Bool} {aw dw : Nat} {c : Name}
    (h : memGateEntryOk d cb aw dw c = true) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length),
      Tools.ShippingInstTagged.originAt d.shape k = .mem cb aw dw ∨
        (Tools.ShippingInstTagged.originAt d.shape k = .ord ∧ (d.shape.insts[k]).1 = c) :=
  -- (writing-time guess, accepted by build cf1: the `Decidable` instance `of_decide_eq_true` synthesizes is the one
  -- `memGateEntryOk` elaborated, as in `gateParentFacts_of_ok`, built ce1)
  of_decide_eq_true h

/-- **The kid side of a memory + one-gate-child parent, as one Bool**: the origin table, the
gate child's Bool / BitVec binder positions, its result width ≠ 1. -/
def memGateOk (d : MachineData) (cb : Bool) (aw dw : Nat) (c : Name)
    (bs : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)) (bposL vposL vwL : List Nat)
    (w : Nat) : Bool :=
  memGateEntryOk d cb aw dw c &&
  Tools.ShippingGateChild.boolPositionsOk bs bposL &&
  Tools.ShippingGateChild.bitsPositionsOk bs vposL vwL &&
  decide (w ≠ 1)

open Sparkle.Compiler.Elab (MixedGateBinder certifiedShape? mixedGatePeel) in
open Tools.ShippingUnifiedSource (SType Term quote) in
/-- **`KidFactsTC` of every entry from ONE Bool** (`memGate_kids` with the entry table, the
binder positions and the width read off `memGateOk`). -/
theorem memGate_kidsS {value dom : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {bposL vposL vwL : List Nat} {srt : SType}
    {e : Term srt}
    (d : MachineData) (cb : Bool) (aw dw : Nat) (c : Name)
    (outsF : InstOrigin → List OutField) (insF : InstOrigin → List Nat)
    (hok : memGateOk d cb aw dw c bs bposL vposL vwL srt.width = true)
    (hmo : outsF (.mem cb aw dw) = Tools.ShippingMemKid.memOuts dw)
    (hmi : insF (.mem cb aw dw) = Tools.ShippingMemKid.memIns aw dw)
    (hgo : outsF .ord = Tools.ShippingMemKid.gateOuts srt.width)
    (hgi : insF .ord = Tools.ShippingMemKid.gateIns bs)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref c value)
    (old : ∀ dv : DefinitionVal, dv.value = value → certifiedShape? false [] (.defnInfo dv) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (bposL.getD j 0))
        (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (vposL.getD j 0)) e))
    (he : e.WF bposL.length vposL.length (fun j => vwL.getD j 0)) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length),
      Tools.ShippingMemKid.KidFactsTC mref cref (Tools.ShippingInstTagged.originAt d.shape k)
        (d.shape.insts[k]).1 (outsF (Tools.ShippingInstTagged.originAt d.shape k))
        (insF (Tools.ShippingInstTagged.originAt d.shape k)) 0 := by
  obtain ⟨h, hw⟩ := and_split hok
  obtain ⟨h, hv⟩ := and_split h
  obtain ⟨hE, hb⟩ := and_split h
  exact Tools.ShippingGateCert.memGate_kids (cb := cb) (aw := aw) (dw := dw) (c := c)
    (bs := bs) (srt := srt) (e := e) (kb := bposL.length) (kv := vposL.length)
    (vw := fun j => vwL.getD j 0) (bpos := fun j => bposL.getD j 0)
    (vpos := fun j => vposL.getD j 0)
    d outsF insF hmo hmi hgo hgi (memGateEntry_of_ok hE) hR0 old peel he
    (Tools.ShippingGateChild.bool_positions hb) (Tools.ShippingGateChild.bits_positions hv)
    (of_decide_eq_true hw)

open Sparkle.Compiler.Elab (MixedGateBinder certifiedShape? mixedGatePeel) in
open Tools.ShippingUnifiedSource (SType Term quote) in
/-- **Per kid, the memory entry `FlatOk`, the gate entry `KidTyped`, from ONE Bool**
(`memGate_kidTyped`). -/
theorem memGate_kidTypedS {value dom : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {bposL vposL vwL : List Nat} {srt : SType}
    {e : Term srt}
    (d : MachineData) (cb : Bool) (aw dw : Nat) (c : Name)
    (hok : memGateOk d cb aw dw c bs bposL vposL vwL srt.width = true)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref c value)
    (old : ∀ dv : DefinitionVal, dv.value = value → certifiedShape? false [] (.defnInfo dv) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (bposL.getD j 0))
        (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (vposL.getD j 0)) e))
    (he : e.WF bposL.length vposL.length (fun j => vwL.getD j 0)) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingInstTagged.KidT mref cref (Tools.ShippingInstTagged.originAt d.shape k)
        (d.shape.insts[k]).1 y →
      Tools.ShippingMemKid.FlatOk y.1 ∨ Tools.ShippingKidsTyped.KidTyped y.1 := by
  obtain ⟨h, _⟩ := and_split hok
  obtain ⟨h, hv⟩ := and_split h
  obtain ⟨hE, hb⟩ := and_split h
  exact Tools.ShippingGateCert.memGate_kidTyped (cb := cb) (aw := aw) (dw := dw) (c := c)
    (bs := bs) (srt := srt) (e := e) (kb := bposL.length) (kv := vposL.length)
    (vw := fun j => vwL.getD j 0) (bpos := fun j => bposL.getD j 0)
    (vpos := fun j => vposL.getD j 0)
    d (memGateEntry_of_ok hE) hR0 old peel he
    (Tools.ShippingGateChild.bool_positions hb) (Tools.ShippingGateChild.bits_positions hv)

end Tools.ShippingGateCert2
