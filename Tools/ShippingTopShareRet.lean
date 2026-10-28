import Tools.ShippingSharedLeafNL
import Tools.ShippingMemClosesKidsT
import Tools.ShippingMachineClosesData
import Tools.ShippingTopShareRun
-- BUILT (unit SR10): r1 exit 0 (dev run); see REPORT-SR10.md for the final-SHA rebuild.
-- No `sorry`, no `axiom`, no `native_decide`, no new RefLawsAOps/RefLawsATele field, no existing statement changed.
-- `topshare_entry_run4_ret`: `topshare_entry_run4'` with the outer run's RETURNED value linked (L8ap); NOT a semantic endpoint.

namespace Tools.ShippingTopShareRet
open Tools.ShippingTopShareRun
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildInvA
open Tools.ShippingChildVCA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildPinC
open Tools.ShippingChildDepthC Tools.ShippingChildRunA
open Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingSharedLeafHit
open Tools.ShippingSharedLeafExt Tools.ShippingLeafKeepCache Tools.ShippingLeafBodyCi Tools.ShippingLeafTermKeeps
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineCloses Tools.ShippingSeqChildIface Tools.ShippingSeqChildIfaceA
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMixedEntrySoundness
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingChildRunAKids Tools.ShippingMachineOutcomeA3 Tools.ShippingChildCoreC Tools.ShippingChildVertA
open Tools.ShippingClosedKinds Tools.ShippingSharedLeafNL
open Tools.ShippingMemCloses Tools.ShippingMachineClosesData
open Tools.ShippingInstTagged (originAt)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`topshare_entry_run4'` KEEPING the outer run's returned value (unit SR10, L8ap).** The conclusion additionally contains
(a) the CORE run `synthesizeCombinationalCore c [] false` from the SAME start world `w`, returning exactly the `(M, Dg)` built by
the closing (`some (M, Dg) = closeInstsG …`), ending in a world `wc` with the cache of the machine synthesis's end (`cv wc = cv w10`),
and (b) the post-processing relation to the OUTER run's returned `y`: `y.1`/`y.2` are the clean-up (`dropZeroWidthModule`, then
possibly `mergeChecked`, only on the module named like `M`) of `M` / `Dg`, at the same worlds `w`, `w'` as the run premise.
WORDING: this relates `y` to `M`/`Dg`; it does NOT state that `M`/`Dg` compute the source (no semantic endpoint). -/
theorem topshare_entry_run4_ret (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {c c₁ c₂ : Name} (hc12 : c₁ ≠ c₂) {o₁ o₁' o₂ o₂' : InstOrigin}
    (ho₁ : o₁.child? = none) (ho₁' : o₁'.child? = none) (ho₂ : o₂.child? = none) (ho₂' : o₂'.child? = none)
    (dp : MachineData) (okp : dp.ok = true)
    (hbodyp : dp.shape.body = quote dp.dom
      (fun j => inputExpr dp.shape.binders.length (dp.bpos j))
      (fun j => inputExpr dp.shape.binders.length (dp.vpos j)) dp.packed)
    (hinsp : dp.shape.insts ≠ []) (hfnep : dp.shape.instFields ≠ [])
    (hP : dp.shape.instTagged = [(c₁, o₁), (c₁, o₁'), (c₂, o₂), (c₂, o₂')])
    (entryP : MachineDefines mctx mref cctx cref c dp.shape)
    (closes0 : MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx c dp.shape)
    (d₁ d₂ : MachineData) (K₁ : CalleeOK O mctx cctx c₁ d₁) (K₂ : CalleeOK O mctx cctx c₂ d₂)
    (hc2not : ∀ k (hk : k < d₁.shape.insts.length), (d₁.shape.insts[k]).1 ≠ c₂)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : RunsTo (synthesizeCombinational c) mctx mref cctx cref w y w') :
    ∃ (y₁ y₂ : Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      closeLets dp.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn dp.shape) dp.shape.insts.length
        dp.shape.layout.slots.length (t.inputs.map (·.name)) (dp.shape.insts.map (·.2.1))
        dp.shape.instFields [y₁, y₁, y₂, y₂] (closeMachine dp.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (cv w10).get? c₁ = some y₁ ∧ (cv w10).get? c₂ = some y₂ ∧
      (∀ a ∈ ModsOf y₁, ∀ b ∈ ModsOf y₂, a.name = b.name → a = b) ∧
      (∀ k₁ (hk₁ : k₁ < d₁.shape.insts.length) k₂ (hk₂ : k₂ < d₂.shape.insts.length),
        (d₁.shape.insts[k₁]).1 = (d₂.shape.insts[k₂]).1 →
        ∃ e, (cv w10).get? (d₁.shape.insts[k₁]).1 = some e ∧ e.1 ∈ y₁.2.modules ∧ e.1 ∈ y₂.2.modules) ∧
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) := by
  obtain ⟨M, Dg, wc, hcore, htail, hpost⟩ := full_run_tracked O hA (D := 0) h
  obtain ⟨tenv, b, w9, w10, hmach, hw9, hc9, htl⟩ := core_run_tracked0' O hA entryP closes0 hw hcore
  obtain ⟨t, t', d₀, w1, -, hlets, hj1, hcv1, hclose⟩ :=
    machineSynth_closing_split O hA (D' := 1) dp okp hbodyp hinsp hfnep hw9 hmach
  have hcvw1 : cv w1 = {} := hcv1.trans hc9
  obtain ⟨y₁, y₂, hrr, hj, hc, hk, hcoh, hg1, hg2, hcross, hshared⟩ :=
    topshare_closing4 O hA (D := 1) Nat.one_ne_zero hc12 ho₁ ho₁' ho₂ ho₂' hP d₁ d₂ K₁ K₂ hc2not hj1
      (by rw [hcvw1]; exact cacheClosed_empty) (by rw [hcvw1]; exact keyTop_empty)
      (by rw [hcvw1]; simp) (by rw [hcvw1]; simp) hclose
  obtain ⟨hjc, hcvc⟩ := htl hj
  obtain ⟨hj2, hcv2⟩ := htail hjc
  exact ⟨y₁, y₂, t, t', d₀, M, Dg, w10, wc, hlets, hrr, hj2, hcv2.trans hcvc, hc, hk, hcoh, hg1, hg2,
    hcross, hshared, hcore, hcvc, hpost⟩

end Tools.ShippingTopShareRet

#print axioms Tools.ShippingTopShareRet.topshare_entry_run4_ret
