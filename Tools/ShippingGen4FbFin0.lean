import Tools.ShippingGen4FbFin
set_option autoImplicit false
-- BUILT (unit FB-11): kjob lake build Tools.ShippingGen4FbFin0 exit 0 (Pod build); clean issue-linked build fb11v-438d2448 exit 0, 812 jobs, scoped approved at 438d2448. Written against scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §19.5 (rev11, scoped approved at 23682b7b).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. Two theorems only.

/-! # FB-11: T-FIN at depth 0 on the `R4RunInvT` side

`tFin0_of_r4RunInvT`: at `D = 0` the `coreFinally` of an `R4RunInvT` run is only the depth decrement, so the cache
value of the end world is that of `w₅`, and `InvAt 0 w'` is the given `JQC L.O 0 w'` plus `CacheShips (cv w₅)`.
`a4_inv_tail_fin0`: the K-RUNT extraction with it. Preservation only (P); the `A4MachineSideA` side carries no
`InvAt` conclusion and is not covered. -/

namespace Tools.ShippingGen4FbFin0
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildVCA
open Tools.ShippingChildCacheA Tools.ShippingChildBndCore
open Tools.ShippingMachineOutcomeA Tools.ShippingMachineOutcomeA3 Tools.ShippingMachineOutcomeA4
open Tools.ShippingGen2 Tools.ShippingGen4FbR4 Tools.ShippingGen4FbInv Tools.ShippingGen4FbTailInv

theorem tFin0_of_r4RunInvT {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : R4RunInvT L P Reach mctx cctx 0 declName shape m d w w') :
    InvAt L P Reach 0 w' := by
  obtain ⟨tenv, pb, ci, envR', w₁, w₂, w₃, w₄, w₅, w₆, h4, h6, h5, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10,
    htail, g11⟩ := h
  obtain ⟨sf, sw, sl, sp, sc, ss, sg, _, hfr, _, _⟩ := g9
  obtain ⟨y0, hmod, h0, -⟩ := hfr
  have hw' : w' = y0 := h0 rfl
  obtain ⟨hcv, -, -⟩ := L.O.depthModify' hA (· - 1) h5.1.1.1 hmod
  exact ⟨g10, by rw [hw', hcv]; exact h5.2⟩

theorem a4_inv_tail_fin0 {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach 0 w) (hC : ChildKeepsInv L P Reach 1)
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape) :
    A4MachineSideA L.O mctx cctx 0 declName shape m d w w' ∨
      (R4RunInvT L P Reach mctx cctx 0 declName shape m d w w' ∧ InvAt L P Reach 0 w') := by
  rcases a4_inv_tail_machine_or_R4RunInvT L P Reach hA hI hC hr entry with hside | hT
  · exact Or.inl hside
  · exact Or.inr ⟨hT, tFin0_of_r4RunInvT L P Reach hA hT⟩

end Tools.ShippingGen4FbFin0
