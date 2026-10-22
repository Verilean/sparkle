import Tests.Compiler.SeqDeepGenDiffTest
import Tools.ShippingTopShareRun
import Tools.ShippingTopShareRet
import Tests.Compiler.TopShareInstTest
-- BUILT (unit SR10): r2/r3 exit 0 (dev runs); see REPORT-SR10.md for the final-SHA rebuild.
-- SCOPE: the outer run's RETURNED value y is linked to the closing's (M, Dg); NOT a semantic endpoint (module = source is not stated).
namespace Tests.Compiler.TopShareRetInstTest
open Tests.Compiler.TopShareInstTest
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA
open Tools.ShippingMachineEntry
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMemCloses (ChildIfaceP)
open Tools.ShippingChildRunAKids Tools.ShippingChildInv
open Tests.Compiler.SeqDeepGenDiffTest
open Tools.ShippingTopShareRun Tools.ShippingSharedLeafNL
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildPinC Tools.ShippingChildDepthC
open Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingSharedLeafHit


theorem topshare_entry_run_inst_ret {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryT : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare
      topshare.machineData.shape)
    (entryW : MachineDefines mctx mref cctx cref wrapN Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (entryW3 : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinational ``Tests.Compiler.SeqDeepGenDiffTest.topshare)
      mctx mref cctx cref w y w') :
    ∃ (y₁ y₂ : Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Sparkle.IR.Machine.closeLets topshare.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshare.machineData.shape)
        topshare.machineData.shape.insts.length topshare.machineData.shape.layout.slots.length
        (t.inputs.map (·.name)) (topshare.machineData.shape.insts.map (·.2.1))
        topshare.machineData.shape.instFields [y₁, y₁, y₂, y₂]
        (Sparkle.IR.Machine.closeMachine topshare.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (cv w10).get? wrapN = some y₁ ∧ (cv w10).get? ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 = some y₂ ∧
      (∀ a ∈ ModsOf y₁, ∀ b ∈ ModsOf y₂, a.name = b.name → a = b) ∧
      (∀ k₁ (hk₁ : k₁ < Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts.length)
        k₂ (hk₂ : k₂ < wrap3.machineData.shape.insts.length),
        (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k₁]).1 =
          (wrap3.machineData.shape.insts[k₂]).1 →
        ∃ e, (cv w10).get? (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k₁]).1 = some e ∧
          e.1 ∈ y₁.2.modules ∧ e.1 ∈ y₂.2.modules) ∧
      Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.topshare [] false)
        mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) := by
  obtain ⟨o₁, o₁', o₂, o₂', h1, h1', h2, h2', hP⟩ := topshare_instTagged_shape
  have closes0 : MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx
      ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData.shape := by
    intro tenv b w9 r w10 hj hcv hr
    exact machineSynth_ne_none4 O hA (by decide) h1 h1' h2 h2' topshare.machineData topshare.machine_ok
      topshare.machine_body topshare_halias topshare_hC topshare_hslots topshare_hdomB
      (by first | decide | decide +kernel) (by first | decide | decide +kernel) hP topshare_hlen4 topshare_hmk
      _ _ (wrap_calleeOK O T hA entryW hR0) (wrap3_calleeOK O T hA entryW3 hR0) topshare_calleeOKs_ne
      nameK nkK outsK namesK
      (fun y hy k hk => by
        have := topdiff2.epD2M0_C_ifaceP O T entryW hR0 hy
        simpa [nameK, nkK, outsK, namesK, if_pos hk] using this)
      (fun y hy k hk2 hk4 => by
        have := wrap3_ifaceP O T hA entryW3 hR0 hy
        simpa [nameK, nkK, outsK, namesK, if_neg (Nat.not_lt.mpr hk2)] using this)
      topshare_hargsN topshare_hfieldOut topshare_hfieldsNd topshare_hsep topshare_hparent topshare_hfresh
      topshare_hparentD hj hcv hr
  exact Tools.ShippingTopShareRet.topshare_entry_run4_ret O hA (by decide) h1 h1' h2 h2' topshare.machineData topshare.machine_ok
    topshare.machine_body (by first | decide | decide +kernel) (by first | decide | decide +kernel) hP
    entryT closes0 _ _ (wrap_calleeOK O T hA entryW hR0) (wrap3_calleeOK O T hA entryW3 hR0)
    topshare_calleeOKs_ne hw h

/-! ## Expected WHOLE statement incl. y; mutations that break the y-link are REJECTED -/

/-- v=0 expected; 1…10 as in `TopShareFull`; 11 `Dg` replaced by `y₁.2` (design of another call); 12 by `y₂.2`; 13 module `t'` instead of `M`;
14 `y.2 = Dg` without the clean-up map; 15 `y.1 = M` without clean-up; 16 only the first disjunct; 17 core run starts at `w'`; 18 `cv wc` is the START cache; 19 core returns `(M, d₀)`. -/
def TopShareRetFull (v : Nat) : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryT : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare
      topshare.machineData.shape)
    (entryW : MachineDefines mctx mref cctx cref wrapN Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (entryW3 : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O (if v = 7 then 1 else 0) w)
    (h : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinational ``Tests.Compiler.SeqDeepGenDiffTest.topshare)
      mctx mref cctx cref w y w'),
    ∃ (y₁ y₂ : Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      (if v = 10 then True else Sparkle.IR.Machine.closeLets topshare.machineData.shape.layout.lets t = some t') ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshare.machineData.shape)
        topshare.machineData.shape.insts.length topshare.machineData.shape.layout.slots.length
        (t.inputs.map (·.name)) (topshare.machineData.shape.insts.map (·.2.1))
        topshare.machineData.shape.instFields
        (if v = 1 then [y₁, y₂, y₁, y₂] else if v = 5 then [y₁, y₂] else [y₁, y₁, y₂, y₂])
        (Sparkle.IR.Machine.closeMachine topshare.machineData.shape.layout t', d₀) ∧
      JQC O (if v = 4 then 1 else 0) w' ∧ cv w' = cv (if v = 8 then w else w10) ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (cv w10).get? wrapN = some (if v = 2 then y₂ else y₁) ∧
      (cv w10).get? ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 = some (if v = 2 then y₁ else y₂) ∧
      (∀ a ∈ ModsOf y₁, ∀ b ∈ ModsOf (if v = 6 then y₁ else y₂), a.name = b.name → a = b) ∧
      (∀ k₁ (hk₁ : k₁ < Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts.length)
        k₂ (hk₂ : k₂ < wrap3.machineData.shape.insts.length),
        (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k₁]).1 =
          (wrap3.machineData.shape.insts[k₂]).1 →
        ∃ e, (cv w10).get? (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k₁]).1 = some e ∧
          e.1 ∈ y₁.2.modules ∧ e.1 ∈ (if v = 3 then y₁ else y₂).2.modules) ∧
      Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.topshare [] false)
        mctx mref cctx cref (if v = 17 then w' else w) (if v = 19 then (M, d₀) else (M, Dg)) wc ∧
      cv wc = cv (if v = 18 then w else w10) ∧
      (let postM : Sparkle.IR.AST.Module := if v = 13 then t' else M
       let postD : Sparkle.IR.AST.Design := if v = 11 then y₁.2 else if v = 12 then y₂.2 else Dg
       let A := (y.1 = (if v = 15 then postM else Sparkle.IR.ZeroWidth.dropZeroWidthModule postM) ∧
          y.2 = (if v = 14 then postD else
            Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule postD))
       let B := (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule postM) ∧
          y.2 = Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule postD))
       if v = 16 then A else (A ∨ B))

open Lean Meta Elab Command in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let thm := ``Tests.Compiler.TopShareRetInstTest.topshare_entry_run_inst_ret
  let ty := (← getConstInfo thm).type
  forallTelescope ty fun xs _ => do
    let names ← xs.toList.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes.toString
    unless names == ["mctx", "mref", "cctx", "cref", "O", "T", "hA", "entryT", "entryW", "entryW3", "hR0", "w", "w'", "y", "hw", "h"] do
      throwError "SR10 AUDIT FAILED: premises of {thm} are {names}"
  if ty.hasMVar then throwError "SR10 AUDIT FAILED: metavariables in the statement"
  Meta.check ty
  let full (v : Nat) : Lean.Expr := mkApp (mkConst ``Tests.Compiler.TopShareRetInstTest.TopShareRetFull) (mkNatLit v)
  let mut rejected : List Nat := []
  unless ← isDefEq ty (full 0) do throwError "SR10 AUDIT FAILED: the statement of {thm} differs from the hand-written expected statement"
  for v in [1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] do
    if ← isDefEq ty (full v) then throwError "SR10 AUDIT FAILED: the mutation {v} of the expected statement was ACCEPTED"
    rejected := v :: rejected
  -- the statement MENTIONS the outer run's returned value `y` in its conclusion (not only in the premise `h`)
  let concl ← forallTelescope ty fun xs b => do
    let y := xs[13]!
    return (b.containsFVar y.fvarId!)
  unless concl do throwError "SR10 AUDIT FAILED: the conclusion does not mention y"
  logInfo m!"SR10 STATEMENT AUDIT: {thm} equals the hand-written TopShareRetFull 0 (isDefEq, no mvars, Meta.check); the conclusion mentions y; mutations rejected: {rejected.reverse}"

end Tests.Compiler.TopShareRetInstTest

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for n in [``Tests.Compiler.TopShareRetInstTest.topshare_entry_run_inst_ret, ``Tools.ShippingTopShareRet.topshare_entry_run4_ret] do
    Tests.Compiler.ChildVertAuditTest.stdAxioms n
    let s ← Tests.Compiler.ChildVertAuditTest.depClosure n
    let hs := Tests.Compiler.ChildVertAuditTest.hits s
    unless hs.isEmpty do throwError "SR10 AUDIT FAILED: {n} depends on the old boundary: {hs}"
    logInfo m!"SR10 AUDIT: {n}: closure {s.size} constants, standard axioms only, no RefLaws / RefLawsCore / toAOps / toA"

#print axioms Tests.Compiler.TopShareRetInstTest.topshare_entry_run_inst_ret
