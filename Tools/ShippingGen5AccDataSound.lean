import Tools.ShippingGen5AccCloses
set_option autoImplicit false
-- Pod build (g5ac-r16) at 317fb29f: `kjob lake build Tools.ShippingGen5AccDataSound` (723 jobs) and `kjob lake build Tests.Gen5.AccDataSoundCheck` (726 jobs, committed tree), each exit 0; clean issue-linked build is the coder's. No sorry / axiom / native_decide.

/-! # DG-ACC unit A8: `DataOfShape` and `ClosesData` from one `DataSound` premise (scripts/gen5/DG_ACC_FREEZE_REV8.md §1)

PROVED here (conditionally): `DataOfShape K` follows from `DataSound K`; `ClosesData K Reach` follows from `DataSound K` and `letsAliasOk` for the
reader data of each reached name.

LIMITS: `DataSound K` for a real kit (dg-dataof integration obligation; `K.dataOf` is not tied to `dataOfAt` here), `letsAliasOk` (L),
`ClosesCalls`, `ReachCover`, `ReadsSupplyAt`, `GenSFacts`, off-route, any real run are NOT supplied. Not DG-ACC / M5 / FG completion. -/

namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineClosesData
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingUnifiedSource (quote)

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}

/-- Conjuncts 1-3 of `dataOfAt_sound` / `dataOfFrom_sound`, for the kit's `dataOf`. -/
def DataSound (K : AssignKit ι dom env₀) : Prop :=
  ∀ (E : ConstantInfo) (se : StructEnv) (s : MachineShape) (d : MachineData),
    K.dataOf E se s = some d →
    d.shape = s ∧ d.ok = true ∧
    d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed

theorem dataOfShape_of_sound (K : AssignKit ι dom env₀) (h : DataSound K) : DataOfShape K :=
  fun E se s d hd => (h E se s d hd).1

theorem closesData_of_sound (K : AssignKit ι dom env₀) (Reach : Name → Prop) (h : DataSound K)
    (hL : ∀ c d, Reach c → dataOf₀ K c = some d → d.letsAliasOk = true) : ClosesData K Reach := by
  intro c d hc hd
  have hd' := hd
  unfold dataOf₀ at hd'
  obtain ⟨E, _, hE⟩ := Option.bind_eq_some_iff.mp hd'
  obtain ⟨s, _, hs⟩ := Option.bind_eq_some_iff.mp hE
  obtain ⟨_, hok, hbody⟩ := h E (structEnv env₀) s d hs
  exact ⟨hok, hbody, hL c d hc hd⟩

end Tools.ShippingGen5Acc

#print axioms Tools.ShippingGen5Acc.dataOfShape_of_sound
#print axioms Tools.ShippingGen5Acc.closesData_of_sound
