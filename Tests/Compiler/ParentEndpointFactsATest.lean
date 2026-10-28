import Tests.Compiler.ParentEndpointMaskedATest
import Tools.ShippingParentRunFactsA
-- BUILT (unit SR3e, par/u-sr3e): sr3e7 exit 0 (before the in-test audit): see REPORT-SR3e.md for the build log. In-test audit THROWS on failure.
-- SCOPE (binding): `hFacts` (`RunFacts`) and `hOuts` (gated `outsCheck`) of `parent_noShips_noBdA` are SUPPLIED for `parent`
-- from the new boundary (`MachineRanA`, from the core run + `BndA`); soundL / composed / houtTy / run / entry / closes, the
-- `designCheck` success condition and `BndA` stay (named). NOT unconditional semantic equivalence; not runtime fit.

/-! # Unit SR3e: `parent`'s depth endpoint without `hFacts` / `hOuts`

`parent_runFactsA` / `parent_outsCheckA`: the run facts and the gated output check of `parent`'s shipped module, from the core
run, the post-processing disjunction, `entry : MachineDefines parent` and the boundary `BndA` (so `O`, `T`, `AdmCtx`,
`MachineDefines cnt`, a start world in `JQ`).  `MachineRanA` comes from `machineRanA_main` with the closing `parent_closesA`;
the children's facts (`hkidP`, `hkidW`, `hkidA`, `hkidR`) from `cnt`'s `RealChildA` (a HISTORY of past synthesis results, not
semantic correctness in the current environment). -/

namespace Tests.Compiler.ParentEndpointFactsATest
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
/-- Data of `parent` and `cnt` used by both theorems below (all by `decide`, as in the generated `parent.machine_*`). -/
theorem parent_insts_cnt : ∀ (k : Nat) (hk : k < parent.machineData.shape.insts.length),
    (parent.machineData.shape.insts[k]).1 = ``cnt := by first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
/-- **`RunFacts` of `parent`'s shipped module** on the new boundary (the head's `hFacts`). -/
theorem parent_runFactsA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``parent [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``parent parent.machineData.shape)
    (hBnd : BndA mctx mref cctx cref w raw D) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b := by
  obtain ⟨O, T, hA, hR0, D₀, hw, hc⟩ := hBnd
  have ran := Tools.ShippingParentRanA.machineRanA_main O hA T hcore entry (parent_closesA O T hA hR0) hw hc
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
  exact Tools.ShippingParentRunFactsA.core_runFacts_ranA (nDecl := 1) O parent.machineData parent.machine_ok parent.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) hkidP
    (Tools.ShippingParentRunFactsA.hkidW_of_dataA O
      (kidOuts := fun _ => cnt.machineData.shape.layout.outs)
      (by first | decide | decide +kernel) hkidT)
    hpost ran

set_option maxHeartbeats 4000000 in
/-- **The gated `outsCheck` of `parent`'s shipped module** on the new boundary (the head's `hOuts`). -/
theorem parent_outsCheckA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design} (n : Nat)
    (hcore : RunsTo (synthesizeCombinationalCore ``parent [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``parent parent.machineData.shape)
    (hg : hierGate b = true) (hBnd : BndA mctx mref cctx cref w raw D) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true := by
  obtain ⟨O, T, hA, hR0, D₀, hw, hc⟩ := hBnd
  have ran := Tools.ShippingParentRanA.machineRanA_main O hA T hcore entry (parent_closesA O T hA hR0) hw hc
  have hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context),
      Tools.ShippingMachineEntry.MachineCloses mc mref cc cref ``cnt cnt.machineData.shape :=
    fun mc cc => cnt.machine_closes mc _ cc _
  exact Tools.ShippingParentPortsA.core_outsCheck_all_gate_ranA (nDecl := 1) O parent.machineData parent.machine_ok
    parent.machine_body (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun k hk y hy => by
      rw [parent_insts_cnt k hk] at hy
      exact Tools.ShippingParentRunFactsA.leaf_real_kidAA O cnt.machineData cnt.machine_ok cnt.machine_body
        (by decide) (by decide) (by decide) (by decide) hR0 hcl hy)
    (fun k hk y hy => by
      rw [parent_insts_cnt k hk] at hy
      exact Tools.ShippingParentRunFactsA.leaf_real_kidRA O cnt.machineData cnt.machine_ok cnt.machine_body
        (by decide) (by decide) hR0 hcl hy)
    hpost ran hg n

set_option maxHeartbeats 4000000 in
/-- **`parent`'s depth endpoint, `kidsMaskedN` discharged on the new boundary.** -/
theorem parent_noShips_noBdA_free (n : Nat)
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
      (-- checker premises: only `designCheck` (the success condition of this implication)
        -- the shipped design's emitted-text checks
        designCheck (childMap D.modules) n (checkedOptimize b) = true →
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
  refine parent_noShips_noBdA n C (soundL := soundL) (composed := composed) (houtTy := houtTy) (hr := hr)
    (entry := entry) (closes := closes) ?_ ?_
  · intro raw D w1 hcore hpost hBnd
    exact parent_runFactsA hcore hpost entry hBnd
  · intro raw D w1 hcore hpost hg hBnd
    exact parent_outsCheckA n hcore hpost entry hg hBnd

open Lean Elab Command Meta Term in
open Tests.Compiler.ChildVertAuditTest in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let new := ``parent_noShips_noBdA_free
  let old := ``parent_noShips_noBdA
  stdAxioms new
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
    throwError "SR3e AUDIT FAILED: outer Prop premises are {premises}, expected {expected} (hFacts / hOuts must be GONE)"
  let cl ← depClosure new
  let bad := hits cl ++ cl.toList.filter fun c =>
    [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV].any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "{new}: old boundary in closure: {bad}"
  for must in [``Tools.ShippingParentRunFactsA.core_runFacts_ranA, ``Tools.ShippingParentPortsA.core_outsCheck_all_gate_ranA,
      ``Tools.ShippingParentRunFactsA.core_instOutWidthsOk_ranA, ``Tools.ShippingParentRunFactsA.core_outsExtracted_ranA,
      ``Tools.ShippingParentRunFactsA.core_raw_facts_ranA, ``Tools.ShippingParentRanA.machineRanA_main,
      ``Tests.Compiler.KidsMaskedParentATest.parent_kidsMaskedN_topA] do
    unless cl.contains must do throwError "SR3e AUDIT FAILED: {must} not in the closure"
  -- the conclusion is DEFEQ to `parent_noShips_noBdA`'s, all shared binders being FVARS (no metavariable)
  forallTelescope (← getConstInfo old).type fun oldXs co => do
    alignInst oldXs [] ty (fun cn al fr _ => do
      unless fr.isEmpty do throwError "SR3e AUDIT FAILED: binders of {new} not in {old}: {fr}"
      unless ← isDefEq cn co do throwError "SR3e AUDIT FAILED: conclusion of {new} differs from {old}"
      let oldNames ← oldXs.mapM fun x => do return (← x.fvarId!.getUserName).toString
      let gone := oldNames.toList.filter (!al.contains ·)
      unless gone == ["hFacts", "hOuts"] do throwError "SR3e AUDIT FAILED: binders removed: {gone}"
      logInfo m!"SR3e CONCLUSION IDENTICAL (isDefEq with all shared binders as fvars); removed binders exactly {gone}")
  logInfo m!"SR3e AUDIT OK: {new}: standard axioms; closure {cl.size} constants, none of RefLaws/RefLawsCore/toAOps/toA/ChildBnd/StartV; remaining outer Prop premises ASSERTED: {premises}. The conclusion keeps the `designCheck` success condition and `BndA` (existential)."

#print axioms parent_noShips_noBdA_free

end Tests.Compiler.ParentEndpointFactsATest
