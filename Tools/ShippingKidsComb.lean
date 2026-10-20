import Tools.ShippingInstStmt
import Tools.ShippingGateChildComb

/-! # `kidsCombB` from the children's facts (all five conditions)

`kidsCombB ms body`: every instance of `body` names a module of `ms` that is
assignment-only, closed over its inputs, drives its outputs, has no output
that is an input, and has every input connected by a wire. From: each
instance resolves (in `ms`) to a module with the child-side facts
(`ChildComb`, derived for a gate child's full-entry module) and its
connections are a call's (`callConns` over the child's inputs). Pure. -/
namespace Tools.ShippingKidsComb
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Sparkle.IR.NameHints (Allocated)
open Tools.ShippingGateChildComb Tools.ShippingInstStmt

theorem out_not_allocated : ¬ Allocated "out" := by
  intro h
  have := h.2
  revert this
  decide

/-- **`kidsCombB`, all five conditions.** -/
theorem kidsCombB_of {ms : List Module} {body : List Stmt}
    (h : ∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
      ∃ c, moduleByName ms mn = some c ∧ ChildComb c ∧
        ∃ argWs outP outW, c.inputs.length = argWs.length ∧
          conns = callConns c.inputs argWs outP outW) :
    kidsCombB ms body = true := by
  unfold kidsCombB
  rw [List.all_eq_true]
  intro st hs
  cases st with
  | inst mn iname conns =>
    obtain ⟨c, hc, hcomb, argWs, outP, outW, hlen, rfl⟩ := h mn iname conns hs
    obtain ⟨ty, hout⟩ := hcomb.output
    simp only [hc, Bool.and_eq_true]
    refine ⟨⟨⟨⟨hcomb.assigns, hcomb.closed⟩, ?_⟩, ?_⟩, conns_inputs hlen⟩
    · rw [hout]
      simpa using hcomb.outDriven
    · rw [hout]
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_eq_true',
        List.contains_eq_mem, decide_eq_false_iff_not, List.mem_map, not_exists, not_and]
      intro p hp he
      exact out_not_allocated (he ▸ hcomb.inputAlloc p hp)
  | _ => rfl

end Tools.ShippingKidsComb
