import Tools.VedU2HierProj

/-!
# H2 unit 3: the acceptance shape/order check `OrderOkHS` (design docs/VED-HIER-H2-DESIGN.md §4)

`HierShapeS` is NOT a soundness check (it does not exclude duplicate register outputs, a register
against an assign / instance-output clash, a write to a top input, an undriven register input, a
combinational cycle through an instance).  `OrderOkHS` is the netlist check of ONE arrangement `b`
of the top body, the hierarchical analogue of `OrderOk` (Tools/VedU1Contract.lean), and it
excludes exactly those:

* `b` is a permutation of the body, hierarchically well-ordered (`WOH`: no read of a later or own
  write, every write once, across assignments AND instances; an instance reads ALL its input
  connections and writes ALL its output connections, so every child output is taken to depend on
  all of its inputs — conservative: a legal sequential circuit may be refused, never the reverse);
* only assignments, registers and instances;
* every read (register input expressions INCLUDED, `allReadsHS`) is an input, a register output or
  a write; every output is driven;
* no write to an input; no name is both written and a register output (assign / instance output
  against register); no register output is an input; no register output twice.

From it `hwr` (the parent writes no input) is DERIVED (`orderOkHS_hwr`), never assumed.
-/

namespace Tools.VedU2Hier

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier

/-- Names a statement reads, a register's input expression included. -/
def allReadsHS (d : Design) : Stmt → List String
  | .register _ _ _ e _ => refsOf e
  | s => rdH d s

/-- The netlist check of one arrangement `b` of the top body. -/
def OrderOkHS (d : Design) (m : Module) (b : List Stmt) : Bool :=
  isPermOf b m.body && decide (WOH d b) && b.all isAsgInstReg &&
  decide (regOuts b).Nodup &&
  b.all (fun s => (allReadsHS d s).all (fun n =>
    (inNames m).contains n || (regOuts b).contains n || (wrsH d b).contains n)) &&
  m.outputs.all (fun p => (regOuts b).contains p.name || (wrsH d b).contains p.name) &&
  (wrsH d b).all (fun n => !(inNames m).contains n && !(regOuts b).contains n) &&
  (regOuts b).all (fun n => !(inNames m).contains n)

def OrderHS (d : Design) (m : Module) : Prop := ∃ b, OrderOkHS d m b = true

theorem orderOkHS_sound {d : Design} {m : Module} {b : List Stmt} (h : OrderOkHS d m b = true) :
    b.Perm m.body ∧ WOH d b ∧ (∀ s ∈ b, isAsgInstReg s = true) ∧ (regOuts b).Nodup ∧
    (∀ n ∈ wrsH d b, n ∉ inNames m) ∧ (∀ n ∈ regOuts b, n ∉ inNames m) ∧
    (∀ n ∈ wrsH d b, n ∉ regOuts b) := by
  simp only [OrderOkHS, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hp, hw⟩, hai⟩, hnd⟩, _⟩, _⟩, hwr⟩, hro⟩ := h
  refine ⟨isPermOf_sound hp, hw, by simpa using hai, hnd, ?_, ?_, ?_⟩
  · intro n hn hin
    have := List.all_eq_true.mp hwr n hn
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    have h2 : (inNames m).contains n = true := List.contains_iff_mem.mpr hin
    rw [h2] at this
    exact absurd this.1 (by simp)
  · intro n hn hin
    have := List.all_eq_true.mp hro n hn
    have h2 : (inNames m).contains n = true := List.contains_iff_mem.mpr hin
    simp [h2] at this
  · intro n hn hr
    have := List.all_eq_true.mp hwr n hn
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    have h2 : (regOuts b).contains n = true := List.contains_iff_mem.mpr hr
    rw [h2] at this
    exact absurd this.2 (by simp)

/-- `hwr` for ANY arrangement of the body, derived from the check of one. -/
theorem orderOkHS_hwr {d : Design} {m : Module} {b0 : List Stmt} (h : OrderOkHS d m b0 = true)
    {arr : Module → List Stmt} (hp : (arr m).Perm m.body) :
    ∀ n ∈ wrsH d (arr m), n ∉ inNames m := by
  obtain ⟨hp0, _, _, _, hwr, _⟩ := orderOkHS_sound h
  intro n hn
  have : n ∈ wrsH d b0 := (wrsH_perm_mem d (hp.trans hp0.symm) n).mp hn
  exact hwr n this

end Tools.VedU2Hier
