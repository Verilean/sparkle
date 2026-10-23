import Tests.Compiler.Srm21LiftTest
import Tests.Compiler.Srm16ParentTest
import Tools.ShippingSrm22Width
import Tools.ShippingNamesClk
set_option autoImplicit false
-- BUILT (unit SRM22): dev runs see STATUS/REPORT; the final-SHA rebuild in REPORT-SRM22.md is the only final evidence.
-- SCOPE: (1) two COUNTEREXAMPLES (Prop-level, over ARBITRARY modules `raw`/`b` related by `hpost`; they say nothing about the concrete topshare modules):
--   `hin_not_hinsFit` (SRM19 `hin` does not give ComposedG `hinsFit` without an input-is-wire fact), `hstX_hstR_not_hst3` (ComposedG `hstX`+`hstR` do not give SRM19 `hst₃`).
-- (2) corollaries: SRM20 `topshareM_svBoundsH_underComposedG` / SRM21 `topshareQ_svBoundsH_underComposedG'` CALLED UNCHANGED, with the `hin` binder REPLACED (not discharged) by three explicit structural PREMISES
--   `hnd` (wire names distinct), `hsI` (input names sanitize-stable), `hIW` (an input's declared width is at most its port type's width); `hin` is obtained from `hinsFit` by `Tools.ShippingSrm22Width.hin_of_hinsFit`,
--   with `hierGate b` (core_hierGate_anyAM) and the wire / output sanitize-stability and `hoi` (TypedIn.wn / ostable / oi of core_closed_typedIn_ranAM) DERIVED from `hBnd`.
-- Every other residual (hRK, hfit, hst₁₋₃, hinsFit, hstX, hstR, hBnd, hBd, hsrc/hpass/hrst/hclk/hinit) is exactly that of SRM20/SRM21.  hst₁₋₃ and hstX/hstR are NOT supplied: see scripts/srm22/PAIR_TABLE.txt.
namespace Tests.Compiler.Srm22PairsTest
open Lean Meta
open Lean Meta
open Tools.ShippingSrm7Rank Tools.ShippingSrm12Corr Sparkle.Compiler.MachInstOrigin
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.Srm7RankTest Tests.Compiler.Srm12CorrTest
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingMemCloses Tools.ShippingMachineAuto
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tests.Compiler.SharedLeafMemKidIfaceTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidEntryTest
open Tools.ShippingSrm21Lift
open Tools.ShippingMachineLinked (childMap)
open Sparkle.IR.ModuleName (ofDecl)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierStateG (KT KSn KState runModuleTG instFree)
open Tools.ShippingMachineShipsDepth (ResetNk kidsMaskedN)
open Tools.ShippingSrm5Height Tools.ShippingSrm6Sem Tools.ShippingSrm11Bounds
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingMachineShipsDepth Sparkle.IR.HierCheck Sparkle.IR.OptCheck
open Tools.ShippingSeqOptSoundness (seedIn)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.Semantics (MEnv Env)
open Tools.ShippingSrm13Supply Tools.ShippingSrm4Core6 Tools.ShippingSrm4Parent
open Tests.Compiler.Srm9ComposedTest (TmBnd TqBnd tmExt tmExtB tqExt tqExtB)
open Tools.ShippingSrm22Width Sparkle.IR.HierCheck Sparkle.IR.OptCheck
open Tests.Compiler.SharedLeafMemKidIfaceTest

/-! ## counterexamples -/

def eIn : Sparkle.IR.AST.Module := { name := "a", inputs := [⟨"clk", .bitVector 8⟩], outputs := [], wires := [], body := [] }
def eEmpty : Sparkle.IR.AST.Module := { name := "e", inputs := [], outputs := [], wires := [], body := [] }

theorem eIn_dz : eIn = Sparkle.IR.ZeroWidth.dropZeroWidthModule eIn := by decide +kernel
theorem eEmpty_dz : eEmpty = Sparkle.IR.ZeroWidth.dropZeroWidthModule eEmpty := by decide +kernel
theorem eEmpty_opt : checkedOptimize eEmpty = eEmpty := by decide +kernel
theorem eIn_weS : Tools.ShippingDesignSV.weS (checkedOptimize eIn) "clk" = 8 := by
  obtain ⟨hi, ho⟩ := Tools.ShippingOptimizePorts.checkedOptimize_ports eIn
  have hw : (checkedOptimize eIn).wires = [] :=
    List.eq_nil_iff_forall_not_mem.mpr (fun p hp => by simpa [eIn] using Tools.ShippingOptSoundness.checkedOptimize_wires_subset eIn p hp)
  simp only [Tools.ShippingDesignSV.weS, Tools.ShippingDesignSV.wofOf, Tools.SVParser.EmitSem.weOf,
    Tools.SVParser.RoundtripProof.moduleWof]
  rw [hw, hi, ho]
  simp [eIn, Tools.ShippingNamesClk.sanitizeName_clk]
theorem eEmpty_weS : Tools.ShippingDesignSV.weS eEmpty "z" = 0 := by decide +kernel
theorem eIn_declWidth : declWidth eIn "clk" = 0 := by decide +kernel

/-- **COUNTEREXAMPLE [pair A, SRM19 ⇒ ComposedG]**: without an input-is-wire fact (`InputsAreWires`), `hin` does not give `hinsFit`: an input that is not a wire has `declWidth` 0 but `weS` its port width. -/
theorem hin_not_hinsFit : ∃ (raw b : Sparkle.IR.AST.Module) (ins : Nat → String → Nat),
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
    (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x) ∧
    ¬ (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) := by
  refine ⟨eIn, eIn, fun _ _ => 5, Or.inl eIn_dz, ?_, ?_⟩
  · intro t x hx
    have hx' : x = "clk" := by simpa [eIn] using hx
    subst hx'
    rw [eIn_weS]
    show (5 : Nat) < 2 ^ 8
    decide
  · intro h
    have := h 0 "clk" (by simp [eIn])
    rw [eIn_declWidth] at this
    exact absurd this (by decide)

/-- **COUNTEREXAMPLE [pair B, ComposedG ⇒ SRM19]**: `hstX` and `hstR` do not give `hst₃`, which speaks about EVERY non-register name (`weS` is 0 off the declared names). -/
theorem hstX_hstR_not_hst3 : ∃ (raw b : Sparkle.IR.AST.Module) (st0 : String → Nat),
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
    (∀ x ∈ (openIns b).map (·.name), x ∉ Tools.ShippingHierOpen.bodyInstOuts (fun _ => none) b.body → st0 x < 2 ^ declWidth b x) ∧
    (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) ∧
    ¬ Tools.ShippingSrm13Supply.NonRegBounded (checkedOptimize b) st0 := by
  refine ⟨eEmpty, eEmpty, fun _ => 1, Or.inl eEmpty_dz, ?_, ?_, ?_⟩
  · intro x hx
    simp [openIns, eEmpty] at hx
  · intro r hr
    simp [seqRegs, openFlat, openBody, eEmpty] at hr
  · intro h
    have := h "z" (by rw [eEmpty_opt]; simp [eEmpty])
    rw [eEmpty_opt, eEmpty_weS] at this
    exact absurd this (by decide)

/-! ## corollaries: `hin` REPLACED by `hnd hsI hIW` -/

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

theorem topshareM_svBoundsH_underComposedG_noHin
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    (hBnd : TmBnd mctx mref cctx cref w raw D)
    (hBd : kidsMaskedN D.modules b.body = true)
    (hnd : (b.wires.map (·.name)).Nodup)
    (hsI : ∀ p ∈ b.inputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (hIW : ∀ p ∈ b.inputs, declWidth b p.name ≤ Tools.ShippingLeafInputWidths.tyW p.ty) :
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
        RegsAtInit (checkedOptimize b) st0 → RegsFit (checkedOptimize b) → NonRegBounded (checkedOptimize b) st0 →
        (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
          childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 2 gc (kids iname)) →
        ∃ envs, runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b)) (childMap D.modules)
            (checkedOptimize b).body (seedIn b ins) T (⟨st0, mems, kids⟩ : KState (KT 2)) = some envs ∧
          envs.length = T ∧
          (∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            topshareM.machineData.shape.layout.outs[k]? = some o → (topshareM.machineSource i bools bits)[k]? = some f → (envs[j]'hj) o.name = f j) ∧
          SVBoundsH (childMap D.modules) (rkOf gM 4) 2 (checkedOptimize b) (seedIn b ins) T (⟨st0, mems, kids⟩ : KState (KT 2)) envs
 := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ :=
    Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_svBoundsH_underComposedG hcore hpost entry hBnd hBd
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hrst hclk hinit hRK hinsFit hstX hstR hst₁ hst₂ hst₃ hfit
  have hB := hBnd
  obtain ⟨O, T0, hA, entryL, entry₁, entry₂, -, -, -, hw⟩ := hB
  have ran := topshareM_ranA O T0 hA entryL entry₁ entry₂ entry hcore hw
  have hgate : Sparkle.IR.RefineCheck.hierGate b = true :=
    Tools.ShippingSrm4Core2.core_hierGate_anyAM O topshareM.machineData topshareM_parentData.ok topshareM_parentData.body
      (nDecl := 4) topshareM_parentData.callsOk topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne topshareM_fne
      topshareM_outTy hpost ran
  have hT := Tools.ShippingSrm4Core1.core_closed_typedIn_ranAM O topshareM.machineData topshareM_parentData.ok topshareM_parentData.body
    (nDecl := 4) topshareM_parentData.callsOk topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne topshareM_fne
    topshareM_outTy hpost ran (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (topshareM_outsClean o ho)) topshareM_scalar
  have hs : ∀ p ∈ b.wires ++ b.inputs ++ b.outputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · exact hT.wn p hp
      · exact hsI p hp
    · exact hT.ostable p hp
  exact H i bools bits T ins st0 mems kids hsrc hpass hrst hclk hinit hRK hinsFit hstX hstR
    (hin_of_hinsFit hgate hnd hs hT.oi hIW ins hinsFit) hst₁ hst₂ hst₃ hfit

theorem topshareQ_svBoundsH_underComposedG'_noHin
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    (hBnd : TqBnd mctx mref cctx cref w raw D)
    (hBd : kidsMaskedN D.modules b.body = true)
    (hnd : (b.wires.map (·.name)).Nodup)
    (hsI : ∀ p ∈ b.inputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (hIW : ∀ p ∈ b.inputs, declWidth b p.name ≤ Tools.ShippingLeafInputWidths.tyW p.ty) :
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
        RegsAtInit (checkedOptimize b) st0 → RegsFit (checkedOptimize b) → NonRegBounded (checkedOptimize b) st0 →
        (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
          childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 1 gc (kids iname)) →
        ∃ envs, runModuleTG (KSn (childMap D.modules) 1) (declWidth (checkedOptimize b)) (childMap D.modules)
            (checkedOptimize b).body (seedIn b ins) T (⟨st0, mems, kids⟩ : KState (KT 1)) = some envs ∧
          envs.length = T ∧
          (∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            topshareQ.machineData.shape.layout.outs[k]? = some o → (topshareQ.machineSource i bools bits)[k]? = some f → (envs[j]'hj) o.name = f j) ∧
          SVBoundsH (childMap D.modules) (rkOf gQ 3) 1 (checkedOptimize b) (seedIn b ins) T (⟨st0, mems, kids⟩ : KState (KT 1)) envs
 := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ :=
    Tests.Compiler.Srm21LiftTest.topshareQ_svBoundsH_underComposedG' hcore hpost entry hBnd hBd
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hrst hclk hinit hRK hinsFit hstX hstR hst₁ hst₂ hst₃ hfit
  have hB := hBnd
  obtain ⟨O, T0, hA, hR0, hcl, entry₁, entry₂, -, -, -, hw⟩ := hB
  have ran := topshareQ_ranA O T0 hA hR0 hcl entry₁ entry₂ entry hcore hw
  have hgate : Sparkle.IR.RefineCheck.hierGate b = true :=
    Tools.ShippingSrm4Core2.core_hierGate_anyAM O topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body
      (nDecl := 4) topshareQ_parentData.callsOk topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne topshareQ_fne
      topshareQ_outTy hpost ran
  have hT := Tools.ShippingSrm4Core1.core_closed_typedIn_ranAM O topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body
    (nDecl := 4) topshareQ_parentData.callsOk topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne topshareQ_fne
    topshareQ_outTy hpost ran (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (topshareQ_outsClean o ho)) topshareQ_scalar
  have hs : ∀ p ∈ b.wires ++ b.inputs ++ b.outputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · exact hT.wn p hp
      · exact hsI p hp
    · exact hT.ostable p hp
  exact H i bools bits T ins st0 mems kids hsrc hpass hrst hclk hinit hRK hinsFit hstX hstR
    (hin_of_hinsFit hgate hnd hs hT.oi hIW ins hinsFit) hst₁ hst₂ hst₃ hfit

end Tests.Compiler.Srm22PairsTest

#print axioms Tests.Compiler.Srm22PairsTest.hin_not_hinsFit
#print axioms Tests.Compiler.Srm22PairsTest.hstX_hstR_not_hst3
#print axioms Tests.Compiler.Srm22PairsTest.topshareM_svBoundsH_underComposedG_noHin
#print axioms Tests.Compiler.Srm22PairsTest.topshareQ_svBoundsH_underComposedG'_noHin
