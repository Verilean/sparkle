import Tools.ShippingRankRun
import Tools.ShippingKidsComb
import Tools.ShippingDesignWith

/-! # The parent side of the one-output closing: shapes and names

What `instStmt_some` and `closeChecks_of` need of the PARENT: the let-closed
transition as `closeLets` returns it, the wires / inputs / outputs / name of
the register-closed module, an `Option` `mapM` that succeeds, and that an
instance name `inst{k}_{…}` is none of the names the harness or
`closeMachine` produce (allocated names start with `_`; `clk`, `rst`, the
next-value names do not start with `inst`). An OUTPUT port may be named like
an instance (a result field `inst0_f` of a declaration calling `f`): that is
a real collision, `closeInsts` returns nothing there; it stays a premise
(`hfreshOuts` of the assembly), decided per declaration. -/
namespace Tools.ShippingCallsParent
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Sparkle.IR.NameHints (Allocated)
open Tools.ShippingCloseLetsSplit (closedBody)
open Tools.ShippingMachineClose (nextName_not_allocated)

/-- **What `closeLets` returns**, with `let`s. -/
theorem closeLets_eq {K : Nat} {t t' : Module} (hK : K ≠ 0) (h : closeLets K t = some t') :
    ∃ w al core, packedWire? t.body = some w ∧
      letOperands t.body (t.inputs.drop (t.inputs.length - K)) w = some (al, core) ∧
      t' = { t with inputs := t.inputs.take (t.inputs.length - K), body := closedBody t al core } ∧
      Sparkle.IR.OptCheck.assignmentOrderCheck (closedBody t al core) = true := by
  unfold closeLets at h
  simp only [hK, if_false] at h
  split at h
  · cases h
  · rename_i w hpw
    split at h
    · cases h
    · rename_i al core hops
      split at h
      · rename_i hchk
        cases h
        simp only [Bool.and_eq_true] at hchk
        exact ⟨w, al, core, hpw, hops, rfl, hchk.2⟩
      · cases h

/-- The register-closed module's wires, inputs, outputs and name. -/
theorem closeMachine_parts {lay : Layout} {t : Module} {B : List Stmt} {w : String}
    (hbody : t.body = B ++ [.assign "out" (.ref w)]) :
    (closeMachine lay t).name = t.name ∧
    (∀ p ∈ t.wires, p ∈ (closeMachine lay t).wires) ∧
    (∀ p ∈ (closeMachine lay t).wires, p ∈ t.wires ∨ ∃ x, p.name = nextName x) ∧
    (∀ p ∈ (closeMachine lay t).inputs, p ∈ t.inputs ∨ p.name = "clk" ∨ p.name = "rst") ∧
    (closeMachine lay t).outputs = lay.outs.map fun o => { name := o.name, ty := o.ty } := by
  have hpw : packedWire? t.body = some w := by simp [packedWire?, hbody]
  unfold closeMachine
  simp only [hpw]
  refine ⟨trivial, fun p hp => List.mem_append_left _ hp, fun p hp => ?_, fun p hp => ?_, trivial⟩
  · rcases List.mem_append.mp hp with h | h
    · exact Or.inl h
    · obtain ⟨q, _, rfl⟩ := List.mem_map.mp h
      exact Or.inr ⟨q.name, rfl⟩
  · rcases List.mem_append.mp hp with h | h
    · exact Or.inl (List.mem_of_mem_take h)
    · split at h
      · cases h
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
        rcases h with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)

/-- An `Option` `mapM` that succeeds at every element. -/
theorem mapM_some_of {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ (l : List α), (∀ a ∈ l, f a = some (g a)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.mapM_cons, h a (List.mem_cons_self ..),
      mapM_some_of f g l (fun x hx => h x (List.mem_cons_of_mem _ hx)), bind, Option.bind]
    rfl

/-! ## The instance name -/

theorem instName_head (k : Nat) (nm : String) :
    (s!"inst{k}_{nm}").toList.head? = some 'i' := by
  simp [String.toList_append]
  exact Or.inl rfl

theorem instName_not_allocated (k : Nat) (nm : String) : ¬ Allocated s!"inst{k}_{nm}" := by
  intro h
  have := h.2
  rw [instName_head] at this
  cases this

theorem instName_ne_clk (k : Nat) (nm : String) : s!"inst{k}_{nm}" ≠ "clk" := by
  intro h
  have := instName_head k nm
  rw [h] at this
  revert this
  decide

theorem instName_ne_rst (k : Nat) (nm : String) : s!"inst{k}_{nm}" ≠ "rst" := by
  intro h
  have := instName_head k nm
  rw [h] at this
  revert this
  decide

theorem instName_ne_next (k : Nat) (nm x : String) : s!"inst{k}_{nm}" ≠ nextName x := by
  intro h
  have h1 := instName_head k nm
  have h2 : (nextName x).toList.head? = some 'n' := by
    simp [nextName, String.toList_append]
  rw [h, h2] at h1
  cases h1

theorem clk_not_allocated : ¬ Allocated "clk" := by
  intro h
  have := h.2
  revert this
  decide

end Tools.ShippingCallsParent
