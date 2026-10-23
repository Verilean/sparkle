import Tests.Compiler.Srm19EndToEndTest
import Tests.Compiler.Srm9ComposedTest
set_option autoImplicit false
-- BUILT (unit SRM20): dev runs b1 (exit 1), b2 (exit 0); the final-SHA rebuild in REPORT-SRM20.md is the only final evidence.
-- SCOPE: a typed bridge from the ComposedG statement of `topshare{M,Q}` (SRM9 `topshare*_composed_binder`: ComposedG at KS = KSn (childMap D.modules) 2, Reset = ResetNk 2, consumed by `machine_ships_hierC_at_free`)
-- to the SRM19 `topshare{M,Q}_svBoundsH_endToEnd`.  The ComposedG run is the run of the CORE module `raw` (weOf raw, arbitrary seed); the optimizer transport to `checkedOptimize b` with `seedIn b ins` is the one of
-- `machine_ships_hierC_at_free` (SRM9 `topshare*_hierC_at_free`).  Its `∃ envsO` run is the `hrun` of SRM19: same width function, childMap, body, seed, T, start state; `envsO` is the same list in `SVBoundsH`.
-- `Reset` (`hRK : ResetNk 2 raw D kids`) is the hypothesis INSIDE the ComposedG statement for the state `kids` it quantifies over: it is a hypothesis of the quantified bridge, NOT supplied by ComposedG.
-- topshareM (depth 2 on both sides): the bridge CLOSES, residuals explicit.  topshareQ: ComposedG is at KSn 2/KT 2/ResetNk 2, SRM19 at KSn 1/KT 1/ResetNk 1: the bridge is PROVED UNDER the Prop `QDepthLift`
-- (a premise, defined here; OPEN: no proof of it for the concrete D).
-- Residuals (PREMISE): hBnd (TmBnd/TqBnd bundle incl. TmH1/TmH2/TmGrp | TqHcallsP/TqFQ/TqGrp), hBd (kidsMaskedN), the ComposedG antecedents (source inputs, regs pass, rst, clk, init), hRK, hinsFit/hstX/hstR (declWidth b form),
-- hin/hst₁/hst₂/hst₃ (weS (checkedOptimize b) form), hfit.  No `sorry`, no `axiom`, no `native_decide`.
namespace Tests.Compiler.SharedLeafMemKidIfaceTest
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingSrm4Kid Tools.ShippingSrm4Core6 Tools.ShippingSrm4Parent
open Sparkle.Compiler.MachMemory (memModule)
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingMachineLinked (childMap)
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidEntryTest
open Tools.ShippingSrm5Height Tools.ShippingSrm6Sem Tools.ShippingSrm11Bounds
open Tools.ShippingHierStateG (KT KSn KState runModuleTG)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingSrm13Supply Tools.ShippingSrm7Rank Tests.Compiler.Srm7RankTest
open Tools.ShippingSeqOptSoundness (seedIn)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.Semantics (MEnv Env)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingMachineShipsDepth Sparkle.IR.HierCheck Sparkle.IR.OptCheck
open Tests.Compiler.Srm9ComposedTest (TmBnd TqBnd tmExt tmExtB tqExt tqExtB)

theorem topshareM_svBoundsH_underComposedG
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    (hBnd : TmBnd mctx mref cctx cref w raw D)
    (hBd : kidsMaskedN D.modules b.body = true) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = topshareM.machineData.shape.binders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
      regs.Nodup ∧ regs.length = topshareM.machineData.ss.length ∧
      ∀ (i : Unit) (bools : Nat → Signal defaultDomain Bool)
        (bits : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n))
        (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv) (kids : String → KT 2),
        (∀ t st, t < T → Tools.ShippingMixedSourceBridge.SourceInputs ``topshareM (topshareM.machineData.bsIn.take 4) ids cache
          (fun j => (tmExtB i bools bits j).val (T - 1 - t)) (fun j n => (tmExt i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
        (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
        (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r → topshareM.machineData.shape.layout.slots[k]? = some f → st0 r = f.init) →
        ResetNk 2 raw D kids →
        (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
        (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body → st0 x < 2 ^ declWidth b x) →
        (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
        (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x) →
        RegsAtInit (checkedOptimize b) st0 → RegsFit (checkedOptimize b) → NonRegBounded (checkedOptimize b) st0 →
        (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
          childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 2 gc (kids iname)) →
        ∃ envs, runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b)) (childMap D.modules)
            (checkedOptimize b).body (seedIn b ins) T (⟨st0, mems, kids⟩ : KState (KT 2)) = some envs ∧
          envs.length = T ∧
          (∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            topshareM.machineData.shape.layout.outs[k]? = some o → (topshareM.machineSource i bools bits)[k]? = some f → (envs[j]'hj) o.name = f j) ∧
          SVBoundsH (childMap D.modules) (rkOf gM 4) 2 (checkedOptimize b) (seedIn b ins) T (⟨st0, mems, kids⟩ : KState (KT 2)) envs := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ :=
    Tests.Compiler.Srm9ComposedTest.topshareM_hierC_at_free hcore hpost entry trivial hBnd hBd
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hrst hclk hinit hRK hinsFit hstX hstR hin hst₁ hst₂ hst₃ hfit
  obtain ⟨envs, hrun, hlen, hobs⟩ := H i bools bits T ins st0 mems kids hsrc hpass hrst hclk hinit hRK hinsFit hstX hstR
  obtain ⟨O, T0, hA, entryL, entry₁, entry₂, -, -, -, hw⟩ := hBnd
  exact ⟨envs, hrun, hlen, hobs,
    topshareM_svBoundsH_endToEnd O T0 hA entryL entry₁ entry₂ entry hcore hpost hw ins T st0 mems kids envs hrun hin hst₁ hst₂ hst₃ hRK hfit⟩

/-- **PREMISE (OPEN; not proved for the concrete `D`).**  The depth-2 start state and run of the ComposedG statement of `topshareQ` (`KSn 2`, `ResetNk 2`) agree with the depth-1 start state and run of SRM19
(`KSn 1`, `ResetNk 1`): every depth-1 Reset state `kids1` has a depth-2 Reset state `kids2` whose depth-2 run on the shipped module is also its depth-1 run from `kids1`. -/
def QDepthLift (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (b : Sparkle.IR.AST.Module) : Prop :=
  ∀ kids1 : String → KT 1, ResetNk 1 raw D kids1 →
    ∃ kids2 : String → KT 2, ResetNk 2 raw D kids2 ∧
      ∀ (seed : Nat → (String → Nat) → Env) (T : Nat) (st0 : String → Nat) (mems : MEnv) (envs : List Env),
        runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b)) (childMap D.modules) (checkedOptimize b).body seed T
          (⟨st0, mems, kids2⟩ : KState (KT 2)) = some envs →
        runModuleTG (KSn (childMap D.modules) 1) (declWidth (checkedOptimize b)) (childMap D.modules) (checkedOptimize b).body seed T
          (⟨st0, mems, kids1⟩ : KState (KT 1)) = some envs

theorem topshareQ_svBoundsH_underComposedG
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    (hBnd : TqBnd mctx mref cctx cref w raw D)
    (hBd : kidsMaskedN D.modules b.body = true)
    (hlift : QDepthLift raw D b) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = topshareQ.machineData.shape.binders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
      regs.Nodup ∧ regs.length = topshareQ.machineData.ss.length ∧
      ∀ (i : Unit) (bools : Nat → Signal defaultDomain Bool)
        (bits : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n))
        (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv) (kids : String → KT 1),
        (∀ t st, t < T → Tools.ShippingMixedSourceBridge.SourceInputs ``topshareQ (topshareQ.machineData.bsIn.take 4) ids cache
          (fun j => (tqExtB i bools bits j).val (T - 1 - t)) (fun j n => (tqExt i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
        (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
        (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r → topshareQ.machineData.shape.layout.slots[k]? = some f → st0 r = f.init) →
        ResetNk 1 raw D kids →
        (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
        (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body → st0 x < 2 ^ declWidth b x) →
        (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
        (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x) →
        RegsAtInit (checkedOptimize b) st0 → RegsFit (checkedOptimize b) → NonRegBounded (checkedOptimize b) st0 →
        (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
          childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 1 gc (kids iname)) →
        ∃ envs, runModuleTG (KSn (childMap D.modules) 1) (declWidth (checkedOptimize b)) (childMap D.modules)
            (checkedOptimize b).body (seedIn b ins) T (⟨st0, mems, kids⟩ : KState (KT 1)) = some envs ∧
          envs.length = T ∧
          (∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            topshareQ.machineData.shape.layout.outs[k]? = some o → (topshareQ.machineSource i bools bits)[k]? = some f → (envs[j]'hj) o.name = f j) ∧
          SVBoundsH (childMap D.modules) (rkOf gQ 3) 1 (checkedOptimize b) (seedIn b ins) T (⟨st0, mems, kids⟩ : KState (KT 1)) envs := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ :=
    Tests.Compiler.Srm9ComposedTest.topshareQ_hierC_at_free hcore hpost entry trivial hBnd hBd
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hrst hclk hinit hRK hinsFit hstX hstR hin hst₁ hst₂ hst₃ hfit
  obtain ⟨kids2, hR2, hagree⟩ := hlift kids hRK
  obtain ⟨envs, hrun2, hlen, hobs⟩ := H i bools bits T ins st0 mems kids2 hsrc hpass hrst hclk hinit hR2 hinsFit hstX hstR
  have hrun := hagree _ _ _ _ _ hrun2
  obtain ⟨O, T0, hA, hR0, hcl, entry₁, entry₂, -, -, -, hw⟩ := hBnd
  exact ⟨envs, hrun, hlen, hobs,
    topshareQ_svBoundsH_endToEnd O T0 hA hR0 hcl entry₁ entry₂ entry hcore hpost hw ins T st0 mems kids envs hrun hin hst₁ hst₂ hst₃ hRK hfit⟩

end Tests.Compiler.SharedLeafMemKidIfaceTest

#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_svBoundsH_underComposedG
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_svBoundsH_underComposedG
