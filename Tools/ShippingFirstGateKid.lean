import Tools.ShippingFirstGateChild
import Tools.ShippingGateConeW
import Tools.ShippingReflectCtx

/-! # The cone's child facts for a FIRST-gate child, against the run's OWN child

WRITTEN, NOT BUILT. Worker N, round 5.

The world-level cone (`Tools.ShippingGateConeW`) reads an instance leaf's
callee off the final child cache `mF` and asks of its entry `y` the
`KidFacts children C mn n v y` (port shape, `children y.1.name = some (y.1, cwe)`,
the child's evaluation). Round 4 left two antecedents about `y`: (b)
`y.1 = childModule` (text equality with a hand-written module — not
derivable, a `RunsTo` is not kernel-computable) and (c) `y.2.modules = []`.

Here (b) is REPLACED: the linked context is the run's own child,
`ownChild y` (`y.1` at its own declared widths), and `KidFacts (ownChild y) …`
is PROVED from `RealChild c y` (every `mF` entry is one: `CacheInv`) and
`EntryDefines c (quoteDecl dn names n fe)` (ALLOWED), for ANY first-gate
child `c`; (c) is proved on the way (`ChildFull.design`).

The child semantics `C` is the consumer's: `hC` says what `C` answers on `c`
(the argument count, in-range values, and the result as `evalFE` of the
fragment). It is a property of `C` alone, discharged per declaration by
evaluation (`Tests/Compiler/GateConeKidTest.lean`: `addSem_spec`). -/
namespace Tools.ShippingFirstGateKid
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingFirstGateChild
open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingMachineChild (InRange)
open Tools.ShippingGateChildComb (ChildComb ChildFull)
open Tools.ShippingUnifiedMeaning (Value ChildSem)
open Tools.ShippingEntrySoundness (RunsTo FExpr evalFE quoteDecl)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingChildInv (Res RealChild)
open Tools.ShippingGateParentRun (KidFacts)

set_option linter.unusedSectionVars false

/-- The linked context of ONE child: the run's own module `y.1`, at its own
declared widths. -/
def ownChild (y : Res) : String → Option (Sparkle.IR.AST.Module × WEnv) :=
  fun s => if s = y.1.name then some (y.1, Sparkle.IR.RegDedup.declWidth y.1) else none

theorem ownChild_self (y : Res) :
    ownChild y y.1.name = some (y.1, Sparkle.IR.RegDedup.declWidth y.1) := by
  unfold ownChild
  rw [if_pos rfl]

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 1000000 in
/-- **The cone's child facts of a first-gate child, from its `RealChild`
witness and `EntryDefines`** — in the linked context of the run's own child
(no pinned module text: (b) replaced), with an empty design ((c) proved).
`hC`: what the consumer's child semantics answers on `c`. -/
theorem kidFacts_of_first {c : Name} {b : Sparkle.IR.AST.Module} {design : Design}
    {dn : Name} {names : List Name} {n : Nat} {fe : FExpr}
    (entry : EntryDefines mctx mref cctx cref c (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    (h : RealChild mref cref c (b, design)) (C : ChildSem) (v : Value) (hv : v.kind.width = n)
    (hC : ∀ (vs : List Value) (u : Value), @ChildSem.childSem C c vs = some u →
      vs.length = names.length ∧ (∀ x ∈ vs, x.toNat < 2 ^ n) ∧
      u.toNat = (evalFE n (fun j => BitVec.ofNat n ((vs.map Value.toNat).getD j 0)) fe).toNat) :
    KidFacts (ownChild (b, design)) C c names.length v (b, design) := by
  -- the child's OWN run, in its own contexts; the reflection moved there
  obtain ⟨mctx', cctx', w, w', -, hr⟩ := h.inv
  have entry' : EntryDefines mctx' mref cctx' cref c (quoteDecl dn names n fe) :=
    Tools.ShippingReflectCtx.EntryDefines.ctx entry
  have full := first_child_fullFacts hr entry' hwf hn
  have fn := first_child_fnR hr entry' hwf hn
  have houts := first_full_outputs hr entry' hwf hn
  have alloc := full.comb.inputAlloc
  have hinLen : b.inputs.length = names.length := by
    have hl := congrArg List.length full.tys
    simp only [List.length_map, firstBs_filter] at hl
    exact hl
  have hargs : argPorts b = b.inputs := by
    unfold argPorts
    apply List.filter_eq_self.mpr
    intro p hp
    have hc : p.name ≠ "clk" := fun e => nAlloc_clk (by rw [← e]; exact alloc p hp)
    have hr' : p.name ≠ "rst" := fun e => nAlloc_rst (by rw [← e]; exact alloc p hp)
    simp [hc, hr']
  refine ⟨Sparkle.IR.RegDedup.declWidth b, "out", n, full.design, ?_, full.comb.inputNames,
    houts, ?_, hinLen, hv, ownChild_self (b, design), ?_⟩
  · intro p hp
    exact ⟨beq_false_of_ne (fun e => nAlloc_clk (by rw [← e]; exact alloc p hp)),
      beq_false_of_ne (fun e => nAlloc_rst (by rw [← e]; exact alloc p hp))⟩
  · intro p hp
    exact beq_false_of_ne (fun e => nAlloc_out (by rw [e]; exact alloc p hp))
  · intro mems envIn vs u hsem hports
    obtain ⟨hlen, hbnd, hu⟩ := hC vs u hsem
    obtain ⟨outP, houtP, hf⟩ := fn
    have hP : outP = { name := "out", ty := .bitVector n } := by
      rw [houts] at houtP
      exact (List.cons.inj houtP).1.symm
    subst hP
    have hvals : (argPorts b).map (fun p => envIn p.name) = vs.map Value.toNat := by
      rw [hargs]
      apply List.ext_getElem
      · rw [List.length_map, List.length_map, hinLen, hlen]
      · intro k h1 h2
        rw [List.getElem_map, List.getElem_map]
        exact hports k (by rw [List.length_map] at h1; exact h1)
          (by rw [List.length_map] at h2; exact h2)
    have hrange : InRange ((argPorts b).map fun p => envIn p.name)
        ((firstBs dn names n).filter fun x => x.2 != .domain) := by
      rw [hvals, firstBs_filter]
      exact inRange_bits _ _ (by rw [List.length_map]; exact hlen)
        (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          exact hbnd y hy)
    obtain ⟨cres, hev, hcres⟩ := hf mems envIn hrange
    refine ⟨cres, hev, ?_⟩
    have hfe := firstFn_eval dn (fe := fe) (vs.map Value.toNat) hwf
    rw [hvals] at hcres
    rw [hu, ← hfe]
    exact hcres

/-- The same over a cache entry `y` (a pair). -/
theorem kidFacts_of_first' {c : Name} {y : Res}
    {dn : Name} {names : List Name} {n : Nat} {fe : FExpr}
    (entry : EntryDefines mctx mref cctx cref c (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    (h : RealChild mref cref c y) (C : ChildSem) (v : Value) (hv : v.kind.width = n)
    (hC : ∀ (vs : List Value) (u : Value), @ChildSem.childSem C c vs = some u →
      vs.length = names.length ∧ (∀ x ∈ vs, x.toNat < 2 ^ n) ∧
      u.toNat = (evalFE n (fun j => BitVec.ofNat n ((vs.map Value.toNat).getD j 0)) fe).toNat) :
    KidFacts (ownChild y) C c names.length v y := by
  obtain ⟨b, design⟩ := y
  exact kidFacts_of_first entry hwf hn h C v hv hC

end Tools.ShippingFirstGateKid
