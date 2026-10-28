import Tests.Compiler.ParentEndpointFactsATest
import Tests.Compiler.PortsMatchRawParentTest
import Tests.Compiler.ClosedTypedTest
import Tests.Compiler.KidsPassLeafTest
import Tools.ShippingParentDesignFA
-- BUILT (unit SR3f, par/u-sr3f): fa5 exit 0 (fa3/fa4 exit 1: arg order, audit predicate). In-test audit THROWS on failure.
-- SCOPE (binding): the `designCheck` success condition of `parent_noShips_noBdA_free` is PROVED for `parent` from the core run
-- and `BndA` (portsMatchB through `core_portsMatch_raw_ranA`, kidsPass through `core_kidsPass_anyA`, RunFacts/TypedIn as before).
-- soundL / composed / houtTy / run / entry / closes and `BndA` (an existential, not a proof that it holds) stay (named).
-- NOT unconditional semantic equivalence; not runtime fit.

/-! # Unit SR3f: `designCheck` of `parent`'s shipped module on the new boundary

`designCheck C n o = textCheckI C o && kidsPass C (designCheck C (n-1)) o.body`.  `parent_designCheckFA`: from the core run, the
post-processing disjunction, `entry : MachineDefines parent` and `BndA` (so `O`, `T`, `AdmCtx`, `MachineDefines cnt`, a start
world in `JQ`), `designCheck (childMap D.modules) n (checkedOptimize b) = true` at EVERY depth `n`, by
`Tools.ShippingParentDesignFA.core_designCheck_ranFA`: the run facts (SR3e), `TypedIn` (PH), `portsMatchB` (raw module by
`core_portsMatch_raw_ranA`, `core_clk_ranA`, then through the optimizer by `portsMatchB_shipped`), `kidsPass` (`core_kidsPass_anyA`).
The per-child facts of `cnt` (a leaf register machine) come from `RealChildA` (a HISTORY of past synthesis results, not semantic
correctness in the current environment).  `parent_noShips_noBdA_dc` is `parent_noShips_noBdA_free` without its `designCheck`
antecedent. -/

namespace Tests.Compiler.ParentDesignCheckFATest
open Tests.Compiler.ParentEndpointFactsATest Tests.Compiler.ParentEndpointMaskedATest
open Tests.Compiler.ParentEndpointMaskedATest Tests.Compiler.KidsMaskedParentATest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Tools.ShippingShipsFree
open Tools.ShippingShipsDesignSV Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingHierOptRun
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal



open Tools.ShippingParentRunFactsA in
set_option maxHeartbeats 4000000 in
/-- **`designCheck` of `parent`'s shipped module, at every depth, on the new boundary** (no check premise). -/
theorem parent_designCheckFA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design} (n : Nat)
    (hcore : RunsTo (synthesizeCombinationalCore ``parent [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``parent parent.machineData.shape)
    (hBnd : BndA mctx mref cctx cref w raw D) :
    designCheck (childMap D.modules) n (checkedOptimize b) = true := by
  obtain ⟨O, T, hA, hR0, D₀, hw, hc⟩ := hBnd
  have ran := Tools.ShippingParentRanA.machineRanA_main O hA T hcore entry (parent_closesA O T hA hR0) hw hc
  have hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context),
      Tools.ShippingMachineEntry.MachineCloses mc mref cc cref ``cnt cnt.machineData.shape :=
    fun mc cc => cnt.machine_closes mc _ cc _
  have hon : ∀ o ∈ cnt.machineData.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name :=
    fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (Tests.Compiler.KidsPassLeafTest.cnt_outs_clean o ho)
  have hdw : Tools.ShippingPortWidthsPure.declWidths cnt.machineData = [1] := by first | decide | decide +kernel
  have hkidP : ∀ (k : Nat) (hk : k < parent.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      RealChildA O (parent.machineData.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ Tools.ShippingInstStmtG.inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧ p.name ≠ "rst" := by
    intro k hk y hy
    rw [parent_insts_cnt k hk] at hy
    exact (Tools.ShippingSeqChildIfaceA.seqChild_of_realA O cnt.machineData cnt.machine_ok cnt.machine_body
      (by decide) (by decide) hR0 (fun mc cc => cnt.machine_closes mc _ cc _) hy).outsIn
  have hkidT : ∀ (k : Nat) (hk : k < parent.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      RealChildA O (parent.machineData.shape.insts[k]).1 y →
      Tools.ShippingChildIfaceTy.ChildOutTys cnt.machineData.shape.layout.outs y.1 := by
    intro k hk y hy
    rw [parent_insts_cnt k hk] at hy
    exact Tools.ShippingCallWidthsChildRealA.leaf_real_outTysA (O := O) cnt.machineData cnt.machine_ok cnt.machine_body
      (by decide) (by decide) (by decide) (by decide) hR0
      (fun mctx' cctx' {tenv} b _ w r w' _ _ hr => cnt.machine_closes mctx' _ cctx' _ (Tools.ShippingChildInv.profLogIO b) w r w' hr) hy
  exact Tools.ShippingParentDesignFA.core_designCheck_ranFA (nDecl := 1) O parent.machineData parent.machine_ok
    parent.machine_body (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) hkidP
    (Tools.ShippingParentRunFactsA.hkidW_of_dataA O
      (kidOuts := fun _ => cnt.machineData.shape.layout.outs)
      (by first | decide | decide +kernel) hkidT)
    (fun k hk y hy => by
      rw [parent_insts_cnt k hk] at hy
      exact Tools.ShippingParentDesignFA.leaf_real_portsInA O cnt.machineData cnt.machine_ok cnt.machine_body
        (nDecl := cnt.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hon (by decide) hy)
    (kidIns := fun _ => [1]) Tests.Compiler.PortsMatchRawParentTest.parent_callArgs
    (fun k hk y hy j q hq => by
      rw [parent_insts_cnt k hk] at hy
      obtain ⟨wd, h1, h2⟩ := Tools.ShippingParentDesignFA.leaf_real_inWidthsA O cnt.machineData cnt.machine_ok
        cnt.machine_body (nDecl := cnt.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hy j q hq
      rw [hdw] at h1
      exact ⟨wd, h1, h2⟩)
    (fun k hk y hy => by
      rw [parent_insts_cnt k hk] at hy
      exact Tools.ShippingParentDesignFA.leaf_real_clkA O cnt.machineData cnt.machine_ok cnt.machine_body
        (nDecl := cnt.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hy)
    (fun k hk y hy => by
      rw [parent_insts_cnt k hk] at hy
      exact Tools.ShippingParentDesignFA.leaf_real_kidK_regA O cnt.machineData cnt.machine_ok cnt.machine_body
        (nDecl := cnt.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) (by decide) hR0 hcl hon (by decide) hy)
    hpost ran
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
      (Tests.Compiler.ClosedTypedTest.parent_outs_clean o ho))
    (by decide) n

set_option maxHeartbeats 4000000 in
set_option maxHeartbeats 4000000 in
/-- **`parent`'s depth endpoint with the `designCheck` success condition DISCHARGED** (unit SR3f): the conclusion of
`parent_noShips_noBdA_free` without its `designCheck … = true →` antecedent, which `parent_designCheckFA` proves from the core run and `BndA`. -/
theorem parent_noShips_noBdA_dc (n : Nat)
    (C : Meta.Context → ST.Ref IO.RealWorld Meta.State → Core.Context →
      ST.Ref IO.RealWorld Core.State → Prop)
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {lsrc srcL : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {extL : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extBL : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    -- the wired endpoint, for the cleanup facts only (its source may be the
    -- fused / sign-normalised one a transported endpoint rewrites)
    (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore ``parent [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref ``parent parent.machineData.shape →
      C mctx mref cctx cref →
      BndA mctx mref cctx cref w m design →
      MachineTraceLB ``parent parent.machineData m design dom srcL extL extBL lsrc)
    (composed : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore ``parent [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref ``parent parent.machineData.shape →
      C mctx mref cctx cref →
      BndA mctx mref cctx cref w m design → Tools.ConeFold.memFree m.body →
      ComposedG (fun D => KSn (childMap D.modules) n) (ResetNk n) ``parent parent.machineData kD m design dom src ext extB)
    (houtTy : ∀ o ∈ parent.machineData.shape.layout.outs, o.ty.bitWidth = o.width)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    (hr : RunsTo (synthesizeCombinational ``parent) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref ``parent parent.machineData.shape)
    (closes : C mctx mref cctx cref) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (-- NO checker premise: `designCheck` is proved (`parent_designCheckFA`)
        BndA mctx mref cctx cref w raw D →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = parent.machineData.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = parent.machineData.ss.length ∧
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → KT n),
            (∀ t st, t < T → SourceInputs ``parent (parent.machineData.bsIn.take kD) ids cache
              (fun j => (extB i bools bits j).val (T - 1 - t))
              (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              parent.machineData.shape.layout.slots[k]? = some f → st0 r = f.init) →
            ResetNk n raw D kids →
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
              st0 x < 2 ^ declWidth b x) →
            (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
            -- the emitted widths' use conditions: inputs, start registers, instance states
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS (checkedOptimize b) x) →
            Bounded (weS (checkedOptimize b)) st0 →
            (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
              childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) n gc (kids iname)) →
            -- a closed run of the emitted texts showing the source exists ...
            (∃ envsO,
              DesignSV (childMap D.modules) n (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                parent.machineData.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j)
            -- ... and EVERY closed run from the same seeding and states shows it
            ∧ ∀ envs', DesignSV (childMap D.modules) n (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
                envs'.length = T ∧
                ∀ j (hj : j < envs'.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                  parent.machineData.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                  (envs'[j]'hj) o.name = f j) := by
  obtain ⟨raw, D, w1, hcore, hpost⟩ := synthesizeCombinational_checked hr
  refine ⟨raw, D, hpost, ?_⟩
  intro hBnd
  have hBdRun : kidsMaskedN D.modules b.body = true := by
    obtain ⟨O, T, hA, hR0, D₀, hw, hc⟩ := hBnd
    exact KidsMaskedParentATest.parent_kidsMaskedN_topA O T hA hcore entry hR0 hw hc hpost
  have hF := parent_runFactsA hcore hpost entry hBnd
  exact design_at_free n (ResetNk n) (BndA mctx mref cctx cref w) (fun b D => kidsMaskedN D.modules b.body = true)
    (machine_ships_hierC_at_free (fun D => KSn (childMap D.modules) n)
      (fun D => KSn_local (childMap D.modules) n) (ResetNk n) BndA C
      (fun b D => kidsMaskedN D.modules b.body = true) (fun _ _ => True)
      (fun b D h => KSn_boundedIn D.modules b.body h n) (true_inv (ResetNk n)) parent.machineData soundL composed
      houtTy hcore hpost entry closes (fun hBnd => parent_runFactsA hcore hpost entry hBnd))
    (fun hBnd => parent_outsCheckA n hcore hpost entry (parent_runFactsA hcore hpost entry hBnd).gate hBnd)
    (parent_designCheckFA n hcore hpost entry hBnd) hBnd hBdRun

open Lean Elab Command Meta Term in
/-- Split `∃ raw D, hp ∧ (B → rest)` (no `designCheck` antecedent) into `(hp, B, rest)` over shared `raw D`. -/
def splitConcl2 (e : Lean.Expr) (raw D : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Lean.Expr) := do
  let e ← whnfR e
  unless e.getAppFn.isConstOf ``Exists do throwError "not ∃: {e}"
  let e1 := (e.appArg!.bindingBody!).instantiate1 raw
  unless e1.getAppFn.isConstOf ``Exists do throwError "not ∃ (2): {e1}"
  let e2 := (e1.appArg!.bindingBody!).instantiate1 D
  let hp := e2.appFn!.appArg!
  let imp := e2.appArg!
  let .forallE _ B rest _ := imp | throwError "no B: {imp}"
  return (hp, B, rest)

open Lean Elab Command Meta Term in
open Tests.Compiler.ChildVertAuditTest in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let new := ``parent_noShips_noBdA_dc
  let old := ``parent_noShips_noBdA_free
  stdAxioms new
  stdAxioms ``parent_designCheckFA
  let ty := (← getConstInfo new).type
  let premises ← forallTelescope ty fun xs _ => do
    let mut ps : Array String := #[]
    for x in xs do
      let t ← inferType x
      let nm := (← x.fvarId!.getUserName).toString
      if (← isProp t) then ps := ps.push s!"{nm} : {t.getAppFn.constName?.getD Name.anonymous}"
    return ps
  let expected := ["soundL : [anonymous]", "composed : [anonymous]", "houtTy : [anonymous]",
    "hr : Tools.ShippingEntrySoundness.RunsTo", "entry : Tools.ShippingMachineEntry.MachineDefines",
    "closes : [anonymous]"]
  unless premises.toList == expected do
    throwError "SR3f AUDIT FAILED: outer Prop premises are {premises}, expected {expected}"
  let cl ← depClosure new
  let bad := hits cl ++ cl.toList.filter fun c =>
    [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV].any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "{new}: old boundary in closure: {bad}"
  for must in [``Tools.ShippingParentDesignFA.core_designCheck_ranFA, ``Tools.ShippingParentDesignFA.core_portsMatch_raw_ranA,
      ``Tools.ShippingParentDesignFA.core_clk_ranA, ``Tools.ShippingParentDesignFA.core_callConns_ranA,
      ``Tools.ShippingParentDesignFA.leaf_real_portsA, ``Tools.ShippingParentDesignFA.leaf_real_kidK_regA,
      ``Tools.ShippingParentDesignFA.leaf_real_portsInA, ``Tools.ShippingParentDesignA.core_kidsPass_anyA,
      ``Tools.ShippingPortsMatchShipped.portsMatchB_shipped, ``Tools.ShippingParentRunFactsA.core_runFacts_ranA,
      ``Tools.ShippingParentPortsA.core_outsCheck_all_gate_ranA, ``Tools.ShippingParentRanA.machineRanA_main] do
    unless cl.contains must do throwError "SR3f AUDIT FAILED: {must} not in the closure"
  -- the rest of the conclusion is DEFEQ to `parent_noShips_noBdA_free`'s, all shared binders being FVARS; only the
  -- `designCheck … = true →` antecedent is gone
  forallTelescope (← getConstInfo old).type fun oldXs co => do
    alignInst oldXs [] ty (fun cn al fr _ => do
      unless fr.isEmpty do throwError "SR3f AUDIT FAILED: binders of {new} not in {old}: {fr}"
      let oldNames ← oldXs.mapM fun x => do return (← x.fvarId!.getUserName).toString
      unless al.toList == oldNames.toList do throwError "SR3f AUDIT FAILED: aligned {al} vs old binders {oldNames}"
      withLocalDeclD `raw (mkConst ``Sparkle.IR.AST.Module) fun raw => withLocalDeclD `D (mkConst ``Sparkle.IR.AST.Design) fun D => do
        let (hpO, dcO, BO, restO) ← splitConcl co raw D
        let (hpN, BN, restN) ← splitConcl2 cn raw D
        unless (dcO.find? (·.isConstOf ``Tools.ShippingDesignSV.designCheck)).isSome do
          throwError "SR3f AUDIT FAILED: old antecedent is not designCheck: {dcO}"
        let ok1 ← isDefEq hpN hpO
        let ok2 ← isDefEq BN BO
        let ok3 ← isDefEq restN restO
        unless ok1 && ok2 && ok3 do
          throwError "SR3f AUDIT FAILED: conclusion parts differ (post {ok1}, BndA {ok2}, rest {ok3})"
        logInfo m!"SR3f CONCLUSION: {new} = {old} minus the antecedent `{← ppExpr dcO}` (post, BndA and rest isDefEq, shared binders as fvars)"
        -- the new conclusion no longer mentions designCheck at all outside `rest`'s own run-level hypotheses
        unless !(BN.find? (·.isConstOf ``Tools.ShippingDesignSV.designCheck)).isSome do
          throwError "SR3f AUDIT FAILED: designCheck still in the BndA part")
  logInfo m!"SR3f AUDIT OK: {new}: standard axioms; closure {cl.size} constants, none of RefLaws/RefLawsCore/toAOps/toA/ChildBnd/StartV; outer Prop premises ASSERTED: {premises}. `BndA` (existential) stays in the conclusion; `designCheck` is proved, not assumed."

#print axioms parent_designCheckFA
#print axioms parent_noShips_noBdA_dc

end Tests.Compiler.ParentDesignCheckFATest
