import Tools.ShippingGen4FbTailInv
set_option autoImplicit false
-- BUILT (unit FB-9) at 777f89cc (header-sync commit follows, comments only): kjob lake build Tools.ShippingGen4FbSplit (709 jobs) exit 0 (Pod build, NOT a clean issue-linked build; that is the coder's). Text = scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §17.3 (rev10, scoped approved at 22147275).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. Two theorems only.

/-! # FB-9: K-TSPLIT — the first action of `legacyTail` (false mode) is the memo read

`legacyTail_hit_or_miss`: a returning `legacyTail … false` run starts with a cache read at its start world; either the
returned pair is the cached entry or the read missed. `r4RunInvT_tail_hit_or_miss`: the same at the `w₆` of `R4RunInvT`.
Structural control-flow facts only; they say nothing about the meaning of `(m, d)`. -/

namespace Tools.ShippingGen4FbSplit
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildVCA
open Tools.ShippingChildCacheA Tools.ShippingChildBndCore
open Tools.ShippingMachineOutcomeA
open Tools.ShippingGen2 Tools.ShippingGen4FbR4 Tools.ShippingGen4FbInv Tools.ShippingGen4FbTailInv

theorem legacyTail_hit_or_miss
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {translate : TranslateFn} {logProf : String → IO Unit} {declName : Name} {ci : ConstantInfo}
    {w w₅ : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : RunsTo (legacyTail translate logProf declName [] false ci) mctx mref cctx cref w (m, d) w₅) :
    ∃ (memo : Std.HashMap Name (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) (w₁ : Void IO.RealWorld),
      RunsTo (sparkleSubModuleCache.get : MetaM _) mctx mref cctx cref w memo w₁ ∧
      (memo.get? declName = some (m, d) ∨ memo.get? declName = none) := by
  unfold legacyTail at h
  rw [if_pos (by decide : (!false) = true)] at h
  have h' := h
  obtain ⟨memo, w₁, hget, hrest⟩ := RunsTo.bind h'
  refine ⟨memo, w₁, hget, ?_⟩
  split at hrest
  · rename_i cached hc
    obtain ⟨_, w₂, _, hret⟩ := RunsTo.bind hrest
    have hp := RunsTo.pure_world hret
    left
    rw [hc, hp.1]
  · rename_i hc
    right
    cases hq : memo.get? declName with
    | none => rfl
    | some c => exact absurd hq (hc c)

theorem r4RunInvT_tail_hit_or_miss
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {mctx : Meta.Context} {cctx : Core.Context} {D : Nat} {declName : Name} {shape : MachineShape}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (h : R4RunInvT L P Reach mctx cctx D declName shape m d w w') :
    ∃ (tenv : Lean.Environment) (pb : Bool) (ci : ConstantInfo) (w₅ w₆ : Void IO.RealWorld)
      (memo : Std.HashMap Name (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) (w₁ : Void IO.RealWorld),
      InvAt L P Reach (D + 1) w₆ ∧ InvAt L P Reach (D + 1) w₅ ∧
      RunsTo (legacyTail (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
        declName [] false
        (entryConst true false [] ci (instancePredicate tenv) (userInliner tenv) (structEnv tenv)))
        mctx mref cctx cref w₆ (m, d) w₅ ∧
      RunsTo (sparkleSubModuleCache.get : MetaM _) mctx mref cctx cref w₆ memo w₁ ∧
      (memo.get? declName = some (m, d) ∨ memo.get? declName = none) := by
  obtain ⟨tenv, pb, ci, envR', w₁, w₂, w₃, w₄, w₅, w₆, h4, h6, h5, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10,
    htail, g11⟩ := h
  obtain ⟨memo, w₇, hget, hmem⟩ := legacyTail_hit_or_miss htail
  exact ⟨tenv, pb, ci, w₅, w₆, memo, w₇, h6, h5, htail, hget, hmem⟩

end Tools.ShippingGen4FbSplit
