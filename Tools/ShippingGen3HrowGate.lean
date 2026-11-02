import Tools.ShippingShapeDecomp
import Tools.ShippingGen2DataBridge
set_option autoImplicit false

/-! # G-HROW-GATE, L2: a shape `machineShape?` returns satisfies `noMemRowS` (scripts/gen3/HROW_GATE_DECISION.md, user decision G)

Built: cached target build at 76c9d2ae (kjob lake build in the rt77 Pod; NOT a clean build, the coder runs it), exit 0, standard axioms.

`Sparkle/Compiler/Elab.lean` `machineShape?` ends with a final gate (before `unifiedGateRoot`):

    if !(st.instOrigins.all (·.child?.isNone) || (st.instStruct && !st.instFields.isEmpty)) then none else

`machineShape?_noMemRow` unfolds `machineShape?` ONCE (the walk of `ShapeDecomp.machineShape?_decomp`, with the
`ite_none_inv'` that keeps the negated condition), takes that gate's hypothesis and concludes
`noMemRowS sp = true` (`Tools.ShippingGen2DataBridge.noMemRowS`) for every returned shape. No fact about the
`partial` readers is used: the gate is a test on the reader state, and its result is read off.

This is a PER-SHAPE statement (any `sym params ci senv allow`). It is not a statement about all `DataOk`
packages; the consumer theorems (`Tools/ShippingGen3HrowGateServed.lean`) apply it to the shape of ONE run.
No sorry / axiom / native_decide. -/
namespace Tools.ShippingGen3HrowGate
open Lean
open Sparkle.Compiler.Elab
open Sparkle.Compiler.MachInstOrigin
open Tools.ShippingMachineShapeUnfold
open Tools.ShippingGen2DataBridge

/-- `ite_none_inv`, keeping the negated condition. -/
theorem ite_none_inv' {α : Type} {c : Prop} [Decidable c] {x : Option α} {b : α}
    (h : (if c then none else x) = some b) : ¬ c ∧ x = some b := by
  by_cases hc : c
  · rw [if_pos hc] at h; cases h
  · rw [if_neg hc] at h; exact ⟨hc, h⟩

/-- Every origin ordinary: every `getD` is ordinary (the default `.ord` is too). -/
theorem child_none_getD (l : List InstOrigin) (hall : ∀ o ∈ l, o.child? = none) (k : Nat) :
    (l.getD k InstOrigin.ord).child? = none := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[k]? with
  | none => rfl
  | some o => exact hall o (List.mem_of_getElem? h)

/-- The gate's condition gives the row. `A`, `b`, `F` are the reader state's origins, `instStruct` and fields. -/
theorem noMemRowS_of_gate {sp : MachineShape} {A : Array InstOrigin} {b : Bool} {F : Array String}
    (hA : sp.instOrigins = A.toList) (hF : sp.instFields = if b = true then F.toList else [])
    (hg : ¬ ((!(A.all (fun o => o.child?.isNone) || (b && !F.isEmpty))) = true)) :
    noMemRowS sp = true := by
  have hg' : (A.all (fun o => o.child?.isNone) || (b && !F.isEmpty)) = true := by
    revert hg
    generalize (A.all (fun o => o.child?.isNone) || (b && !F.isEmpty)) = x
    cases x <;> simp
  rcases Bool.or_eq_true_iff.mp hg' with hall | hst
  · have hall' : ∀ o ∈ sp.instOrigins, o.child? = none := by
      rw [hA]
      intro o ho
      have := (Array.all_eq_true_iff_forall_mem.mp hall) o (Array.mem_toList_iff.mp ho)
      simpa using this
    unfold noMemRowS
    rw [Bool.or_eq_true_iff]
    right
    rw [List.all_eq_true]
    intro x hx
    unfold MachineShape.instTagged at hx
    obtain ⟨⟨i, k⟩, -, rfl⟩ := List.mem_map.mp hx
    simp only
    rw [child_none_getD _ hall' k]
    rfl
  · have hb : b = true := by simpa using (Bool.and_eq_true_iff.mp hst).1
    have hF2 : F.isEmpty = false := by simpa using (Bool.and_eq_true_iff.mp hst).2
    unfold noMemRowS
    rw [Bool.or_eq_true_iff]
    left
    rw [hF, if_pos hb]
    have : F.toList.isEmpty = false := by
      first
        | (rw [Array.isEmpty_toList]; exact hF2)
        | (cases F with | mk l => simpa [Array.isEmpty] using hF2)
    simp [this]

/-- **L2 (declaration case)**: the one-unfolding walk of `machineShape?_decomp`, keeping the final gate. -/
theorem machineShape?_noMemRow_defn {sym : Bool} {params : List (String × Nat)} {d : DefinitionVal}
    {senv : StructEnv} {allow : Bool} {sp : MachineShape}
    (h : machineShape? sym params (.defnInfo d) senv allow = some sp) : noMemRowS sp = true := by
  unfold machineShape? at h
  dsimp only at h
  replace h := ite_none_inv h
  obtain ⟨x, hx, h⟩ := bind_inv h
  generalize hk : machTupleKinds? d.type = tup at h
  cases tup <;> dsimp only at h
  all_goals obtain ⟨o, ho, h⟩ := bind_inv h
  all_goals replace h := ite_none_inv h
  all_goals generalize hrun : Option.bind _ machRunApp? = run at h
  all_goals rcases run with _ | ⟨dom, αs, initsE, body⟩
  all_goals try dsimp only at h
  all_goals
    repeat first
      | (replace h := ite_none_inv' h; obtain ⟨_, h⟩ := h)
      | (replace h := bind_inv h; obtain ⟨_, _, h⟩ := h)
      | (replace h := Option.bind_eq_some_iff.mp h; obtain ⟨_, _, h⟩ := h)
  all_goals replace h := ite_else_none_inv h
  all_goals have hsp := Option.some.inj h
  all_goals subst hsp
  all_goals
    refine noMemRowS_of_gate rfl rfl ?_
    assumption

/-- **L2**: every shape `machineShape?` returns has `noMemRowS = true` (i.e. `OneOutNoMemRow` of a package whose
shape it is, by `OneOutNoMemRow_eq`). -/
theorem machineShape?_noMemRow {sym : Bool} {params : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {allow : Bool} {sp : MachineShape}
    (h : machineShape? sym params ci senv allow = some sp) : noMemRowS sp = true := by
  cases ci <;> first
    | exact machineShape?_noMemRow_defn h
    | (unfold machineShape? at h; cases h)

end Tools.ShippingGen3HrowGate
