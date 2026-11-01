import Tools.ShippingGen5AccOrdCallees
set_option autoImplicit false
-- Pod incremental build OK (Tools 728 jobs, Check 731 jobs, exit 0). Clean issue-linked build: pending (coder). Lean source for DG-ACC unit A13 (freeze scripts/gen5/DG_ACC_FREEZE_REV13.md, design approved at cff12a48). No sorry / axiom / native_decide.

/-! # DG-ACC unit A13: `GDf`, `genDataF`, f-derived evidence and success (scripts/gen5/DG_ACC_FREEZE_REV13.md §1)

PROVED here: `GDf f env₀ E` is the subtype of (shape, data) pairs with `machineShape? = some shape`, `f .. = some data`, `data.shape = shape`;
`genDataF` picks such a pair by classical choice (`Classical.choice` only); `genDataF_evidence` is `GDEvidence f (GDf f env₀) dOfF env₀`;
`genDataF_isSome_iff` characterizes success; `genDataF_isSome_of_sound` derives success from `hf`, a shape witness and `f` success.

LIMITS: `GDf` is NOT DG-SEM's `GenData` (a different type); no `genSem`, `GenWF`, `hloc/hdecl/hd`, no kit, no real run. No real `GenData` / `genSem`,
and no success of a real run is supplied.
Premises RESOLVED by this unit: `hev` for the f-derived GD (`genDataF_evidence`, unconditional); the success characterization of `genData₀` for the
f-derived GD (`genDataF_isSome_iff`).
Premises INTRODUCED / still open: for `genDataF_isSome_of_sound`: `hf : DataSoundAt f`, a shape witness `hs : machineShape? .. = some s`, and
`hd : f .. s = some d` (success of `f`). Still open elsewhere: `hf` for `dataOfAt lvl`, real `GenData` (`hshape/hdata`), `genSem`, laws, coverage,
L, C', `ReachCover`, real run, M5, FG. Not DG-ACC / M5 / FG completion. -/

namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)

def GDf (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Environment)
    (E : ConstantInfo) : Type :=
  { p : MachineShape × MachineData //
      machineShape? false [] E (structEnv env₀) = some p.1 ∧ f E (structEnv env₀) p.1 = some p.2 ∧ p.2.shape = p.1 }

def dOfF (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Environment)
    {E : ConstantInfo} (g : GDf f env₀ E) : MachineData := g.val.2

open Classical in
noncomputable def genDataF (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Environment)
    (E : ConstantInfo) : Option (GDf f env₀ E) :=
  if h : ∃ p : MachineShape × MachineData,
      machineShape? false [] E (structEnv env₀) = some p.1 ∧ f E (structEnv env₀) p.1 = some p.2 ∧ p.2.shape = p.1
  then some ⟨h.choose, h.choose_spec⟩ else none

theorem genDataF_evidence (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Environment) :
    GDEvidence f (GDf f env₀) (fun {E} g => dOfF f env₀ g) env₀ := by
  intro E g
  obtain ⟨h1, h2, h3⟩ := g.property
  have h4 : (dOfF f env₀ g).shape = g.val.1 := h3
  refine ⟨?_, ?_⟩
  · rw [h4]; exact h1
  · rw [h4]; exact h2

theorem genDataF_isSome_iff (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Environment)
    (E : ConstantInfo) :
    (genDataF f env₀ E).isSome = true ↔
      ∃ (s : MachineShape) (d : MachineData),
        machineShape? false [] E (structEnv env₀) = some s ∧ f E (structEnv env₀) s = some d ∧ d.shape = s := by
  unfold genDataF
  by_cases h : ∃ p : MachineShape × MachineData,
      machineShape? false [] E (structEnv env₀) = some p.1 ∧ f E (structEnv env₀) p.1 = some p.2 ∧ p.2.shape = p.1
  · rw [dif_pos h]
    simp only [Option.isSome_some, true_iff]
    obtain ⟨p, hp⟩ := h
    exact ⟨p.1, p.2, hp⟩
  · rw [dif_neg h]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨s, d, hs⟩
    exact h ⟨(s, d), hs⟩

theorem genDataF_isSome_of_sound (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Environment)
    (hf : DataSoundAt f) (E : ConstantInfo) (s : MachineShape) (d : MachineData)
    (hs : machineShape? false [] E (structEnv env₀) = some s) (hd : f E (structEnv env₀) s = some d) :
    (genDataF f env₀ E).isSome = true :=
  (genDataF_isSome_iff f env₀ E).2 ⟨s, d, hs, hd, (hf E (structEnv env₀) s d hd).1⟩

end Tools.ShippingGen5Acc

#print axioms Tools.ShippingGen5Acc.GDf
#print axioms Tools.ShippingGen5Acc.dOfF
#print axioms Tools.ShippingGen5Acc.genDataF
#print axioms Tools.ShippingGen5Acc.genDataF_evidence
#print axioms Tools.ShippingGen5Acc.genDataF_isSome_iff
#print axioms Tools.ShippingGen5Acc.genDataF_isSome_of_sound
