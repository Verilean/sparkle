import Tools.ShippingChecksDerived2
import Tools.ShippingGateChildComb

/-! # The output facts of a GATE child (G1)

`Tools.ShippingChecksCore.core_outsCheck_all` asks two facts of each real
child (`hkidA`, `hkidR`); `leaf_real_kidA` / `leaf_real_kidR` give them for
a machine child without calls, `kids_real_kid` for a machine child with
calls from the same facts of ITS children. A child of that child may be a
GATE (a combinational declaration: `midH` calls `rcH`). This file gives the
two facts for a gate child, from `ChildFull` — what
`Tools.ShippingCallsGate.childFull_of_real` derives from the child's
`RealChild` witness and its reflection:

* `gate_kidA`: its module assigns its output, and its design has no module;
* `gate_kidR`: its module has no instance statement.

What is NOT done: the GENERATION of the `kids_real_kid` call for a child
with calls (it also asks that child's `KidNames`, its `MachineClosesAt` in
every context and `hself`); `#machine_no_outs` still refuses `grandH`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingChecksGate
open Sparkle.IR.AST
open Tools.ShippingGateChildComb (ChildComb ChildFull)
open Tools.ShippingChecksDerived (ff_absurd)

/-- In an assignments-only body, a written name is assigned. -/
theorem assign_of_writes {body : List Stmt} {n : String}
    (ha : body.all Sparkle.IR.RegDedup.isAssign = true)
    (h : n ∈ Sparkle.IR.Reorder.writesOf body) : ∃ r, Stmt.assign n r ∈ body := by
  unfold Sparkle.IR.Reorder.writesOf at h
  obtain ⟨st, hst, hn⟩ := List.mem_flatMap.mp h
  have hs := List.all_eq_true.mp ha st hst
  cases st with
  | assign l r =>
    have hn' : n ∈ [l] := hn
    have e : n = l := List.mem_singleton.mp hn'
    exact ⟨r, by rw [e]; exact hst⟩
  | _ => exact ff_absurd hs

/-- **`hkidA` for a gate child.** -/
theorem gate_kidA {c : Lean.Name} {bs : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {b : Sparkle.IR.AST.Module} {design : Design} (h : ChildFull c bs b design) :
    Tools.ShippingDesignSVBack.outsAssigned b = true ∧
      ∀ g ∈ design.modules, Tools.ShippingDesignSVBack.outsAssigned g = true := by
  refine ⟨Tools.ShippingChecksDerived2.outsAssigned_of_assigned fun p hp => ?_, ?_⟩
  · obtain ⟨ty, hout⟩ := h.comb.output
    rw [hout] at hp
    have e : p = { name := "out", ty := ty } := List.mem_singleton.mp hp
    rw [e]
    exact assign_of_writes h.comb.assigns h.comb.outDriven
  · intro g hg
    rw [h.design] at hg
    cases hg

/-- **`hkidR` for a gate child**: no instance statement. -/
theorem gate_kidR {c : Lean.Name} {bs : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {b : Sparkle.IR.AST.Module} {design : Design} (h : ChildFull c bs b design) :
    ∀ g ∈ b :: design.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
      ∃ g2 ∈ design.modules, g2.name = mn := by
  intro g hg mn i conns hm
  rw [h.design] at hg
  have hgb : g = b := List.mem_singleton.mp hg
  rw [hgb] at hm
  exact ff_absurd (List.all_eq_true.mp h.comb.assigns _ hm)

end Tools.ShippingChecksGate
