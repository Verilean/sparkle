import Tools.ShippingGen5AccDataSound
set_option autoImplicit false
-- NOT BUILT yet at this commit (g5ac-r18, freeze rev9 153a31a2). Build/Check SHA is recorded here by a comment-only commit after a successful Pod build. No sorry / axiom / native_decide.

/-! # DG-ACC unit A9: `DataSound` from kit agreement with a specified function (scripts/gen5/DG_ACC_FREEZE_REV9.md §1)

PROVED here (conditionally): `DataSound K` follows from `DataSoundAt f` (the spec of a plain function `f`) and `KitAgrees K f` (the kit's `dataOf` is `f`).
This only splits the single dg-dataof integration obligation `DataSound K` into two statements with different owners.

LIMITS: `DataSoundAt` for any named function (e.g. `dataOfAt lvl`, via `dataOfAt_sound` conjuncts 1-3 on `kjob/g5do-r6`), `KitAgrees` for any real kit,
`K.dataOf = dataOfAt`, `letsAliasOk` (L), `ClosesCalls` (C'), `ReachCover`, `ReadsSupplyAt`, `GenSFacts`, off-route, any real run are NOT supplied.
INTEGRATION OBLIGATION (kept open): close `hf` and `hK` from the real definitions at the integration SHA. Not DG-ACC / M5 / FG completion. -/

namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingUnifiedSource (quote)

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}

/-- Conjuncts 1-3 of `dataOfAt_sound lvl`, for an arbitrary function `f`. -/
def DataSoundAt (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) : Prop :=
  ∀ (E : ConstantInfo) (se : StructEnv) (s : MachineShape) (d : MachineData),
    f E se s = some d →
    d.shape = s ∧ d.ok = true ∧
    d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed

/-- The kit's `dataOf` is `f` (pointwise). -/
def KitAgrees (K : AssignKit ι dom env₀)
    (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) : Prop :=
  ∀ (E : ConstantInfo) (se : StructEnv) (s : MachineShape), K.dataOf E se s = f E se s

theorem dataSound_of_agree (K : AssignKit ι dom env₀)
    (f : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (hf : DataSoundAt f) (hK : KitAgrees K f) : DataSound K :=
  fun E se s d hd => hf E se s d (by rw [← hK E se s]; exact hd)

end Tools.ShippingGen5Acc

#print axioms Tools.ShippingGen5Acc.dataSound_of_agree
