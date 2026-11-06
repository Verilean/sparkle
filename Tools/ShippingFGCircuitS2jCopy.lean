import Tools.ShippingFGCircuitS2gGates
import Tools.ShippingGen2OneOutTopO
set_option autoImplicit false
-- FG circuit pilot S2j, unit 1: the one-output parent's top-ships proof (`oneOut_topShipsO`) restated for the PROFILE-FREE core run `synthesizeCombinationalCoreOff` with the run-local entry `MachineDefinesLinkedOff`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. docs/FG-CIRCUIT-PILOT.md §36.

/-! # S2j copies

`machine_ships_hierC_run` (Tools/ShippingGen2FitChain.lean:1073) and `oneOut_topShipsO` (Tools/ShippingGen2OneOutTopO.lean:336) with exactly three kinds of edits (all in binder TYPES; the proof bodies are verbatim):
`RunsTo (synthesizeCombinationalCore X [] false) … → RunsTo (synthesizeCombinationalCoreOff X) …`; `MachineDefines … → MachineDefinesLinkedOff … w raw D w1` (the run-local entry); the name. Both runs are only passed to the `soundL`/`composed` binders and
ignored by their supplied lambdas, so the proofs are unchanged. -/
namespace Tools.ShippingFGCircuitS2jCopy
open Tools.ShippingFGCircuitS1qLinked (MachineDefinesLinkedOff)
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
open Tools.ShippingSrm25Init (SourceRegsAreSlots)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

open Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Tools.ShippingSrm25Init (SourceRegsAreSlots)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- (S2j copy, profile-free core run) `machine_ships_hierC_noHstR` (Srm33Core:24-189, f51e68a4) with the run-local fit: no `Bd`/`Inv`/`hBd`/`hRI`, no
`Bd b D` antecedent; `composed` is `ComposedNWRegsF`, whose run tail carries `KSBoundedRun` on the same `envs`; the
extracted-input fit comes from `fitX_of_runR` (freeze §3.8 line table; every other line verbatim). -/
theorem machine_ships_hierC_runOff {n : Nat} (hloc : ∀ D : Design, KSLocal (KSn (childMap D.modules) n))
    (Bnd : CtxBnd)
    (C : Meta.Context → ST.Ref IO.RealWorld Meta.State → Core.Context →
      ST.Ref IO.RealWorld Core.State → Prop)
    {declName : Name} (d : MachineData) {kD : Nat}
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
      RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w
        (m, design) w' →
      MachineDefinesLinkedOff mctx mref cctx cref declName d.shape w m design w' →
      C mctx mref cctx cref →
      Bnd mctx mref cctx cref w m design →
      MachineTraceLB declName d m design dom srcL extL extBL lsrc)
    (composed : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design} {b : Sparkle.IR.AST.Module},
      RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w
        (m, design) w' →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule m ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule m)) →
      MachineDefinesLinkedOff mctx mref cctx cref declName d.shape w m design w' →
      C mctx mref cctx cref →
      Bnd mctx mref cctx cref w m design → Tools.ConeFold.memFree m.body →
      Tools.ShippingGen2Fit.ComposedNWRegsF n declName d kD m design dom src ext extB
        (fun regs => ∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
          d.shape.layout.slots[k]? = some f → f.width ≤ declWidth b r))
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hinitW : ∀ f ∈ d.shape.layout.slots, f.init < 2 ^ f.width)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w
      (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefinesLinkedOff mctx mref cctx cref declName d.shape w raw D w1)
    (closes : C mctx mref cctx cref)
    -- what the core run provides of the full entry's module, at this run
    (facts : Bnd mctx mref cctx cref w raw D →
      Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b) :
        -- NO checker premise: the run's facts are derived (`facts`)
        -- the run boundary of the children (in the run's contexts)
        Bnd mctx mref cctx cref w raw D →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = d.ss.length ∧
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → KT n),
            (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
              (fun j => (extB i bools bits j).val (T - 1 - t))
              (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              d.shape.layout.slots[k]? = some f → st0 r = f.init) →
            ResetNk n raw D kids →
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
              st0 x < 2 ^ declWidth b x) →
            ∃ envsO, runModuleTG (KSn (childMap D.modules) n) (declWidth (checkedOptimize b))
                (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T
                ⟨st0, mems, kids⟩ = some envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j := by
  intro hBnd
  have hL := soundL hcore entry closes hBnd
  obtain ⟨_, _, _, _, _, _, _, _, _, wired, _⟩ := id hL
  obtain ⟨_, _, _, _, _, _, hlink, houts, _, _, _, _, _, _, _, hclean, _⟩ := wired
  obtain ⟨hb, hw, hi, ho⟩ := hclean houtTy
  obtain ⟨hgate, hwfB, hndB, hself, hOut, hrstIn, hIW⟩ := facts hBnd
  have hOutM := Tools.ShippingHierPremisesBase.outsExtracted_sound hOut
  have hI : Tools.ShippingMachineShipsHier.hasInst b :=
    Tools.ShippingGuardsSound.hasInst_of_hierGate hgate
  have hbr : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw := by
    rcases hpost with h | h
    · exact h
    · exact mergeChecked_inst h hI
  have hbB : b.body = raw.body := by rw [hbr]; exact hb
  have hbW : declWidth b = Tools.ShippingEntrySoundness.weOf raw := by rw [hbr]; exact hw
  have hbI : b.inputs = raw.inputs := by rw [hbr]; exact hi
  have hbO : b.outputs = raw.outputs := by rw [hbr]; exact ho
  have hmf : Tools.ConeFold.memFree raw.body := by
    rw [← hbB]; exact memFree_of_linkedWF _ hwfB
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, hPw, lets, llen, wired, H⟩ :=
    composed hcore hpost entry closes hBnd hmf
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hrstZ hclk hinit hreset hinsFit hstX
  have hstR : ∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1 :=
    Tools.ShippingSrm31.hstR_of_wired_slots hbB (Tools.ShippingSrm28.sourceRegsAreSlots_of_wired_all wired) hinit hinitW hPw
  have hrst : ∀ t st, seedIn b ins t st "rst" = 0 := by
    intro t st
    simp only [seedIn, List.contains_eq_mem, decide_eq_true hrstIn, if_true]
    exact hrstZ t
  obtain ⟨envs, hrun, hlen, hobs, hfitI⟩ := H i bools bits T (seedIn b ins) st0 mems kids hsrc hpass hrst
    hclk hinit hreset
  have hrunB : runModuleTG (KSn (childMap D.modules) n) (declWidth b) (childMap D.modules) b.body
      (seedIn b ins) T ⟨st0, mems, kids⟩ = some envs := by
    rw [hbW, hbB]; exact hrun
  have hfitB : Tools.ShippingGen2Fit.KSBoundedRun (childMap D.modules) b.body envs := by
    rw [hbB]; exact hfitI
  have houtSrc : ∀ (k : Nat) (o : OutField), d.shape.layout.outs[k]? = some o →
      o.name ∈ b.outputs.map (·.name) := by
    intro k o hk
    rw [hbO, houts]
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨o, List.mem_of_getElem? hk, rfl⟩, rfl⟩
  by_cases hbind : hierBinds b = true
  · -- the optimizer: checked on the extracted interface, or not applied
    have hopt : checkedOptimize b = (if hierRefineCheck b (deinline b (Sparkle.IR.Optimize.optimizeModule b))
        then deinline b (Sparkle.IR.Optimize.optimizeModule b) else b) := by
      unfold checkedOptimize
      simp only [simpleBody_inst hI, not_all_seqOk hI, hbind, Bool.false_eq_true, if_false, if_true]
    by_cases hacc : hierRefineCheck b (deinline b (Sparkle.IR.Optimize.optimizeModule b)) = true
    · -- accepted: the guards give conjuncts 2 and 4, the instance statements 5
      obtain ⟨hwfO, hndO⟩ := Tools.ShippingGuardsSound.deinline_guards
        (o := Sparkle.IR.Optimize.optimizeModule b) hacc hwfB hndB hOut
      have hselfO : Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules)
          (deinline b (Sparkle.IR.Optimize.optimizeModule b)).body = true :=
        Tools.ShippingChecksDerived2.all_inst_transfer _
          (fun mn iname conns =>
            (Tools.ShippingChecksDerived2.hierRefineCheck_inst_iff hacc mn iname conns).mp)
          (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) hself
      have hnofb := Tools.ShippingHierPremisesBase.noSelfRead_sound hselfO
      rw [hopt, if_pos hacc]
      obtain ⟨-, -, envsO, hrunO, hlenO, hcorr⟩ := hierRefineCheck_linked
        (KSn (childMap D.modules) n) (hloc D) (childMap D.modules) hacc
        hwfB hwfO hndB hndO hnofb hOutM ins hinsFit hrstIn hrstZ hrunB
        (Tools.ShippingGen2Fit.fitX_of_runR _ (childMap D.modules) b ins hwfB hIW T _ envs hrunB hfitB hstX) hstR
      refine ⟨envsO, hrunO, by omega, ?_⟩
      intro j hj k o f hk hf
      obtain ⟨p, hp, hpn⟩ := List.mem_map.mp (houtSrc k o hk)
      rw [← hpn, hcorr p hp j hj (by omega), hpn]
      exact hobs j (by omega) k o f hk hf
    · rw [hopt, if_neg hacc]
      exact ⟨envs, hrunB, hlen, hobs⟩
  · -- the check does not bind: the module is shipped as it is
    have hb0 : hierBinds b = false := by simpa using hbind
    rw [Tools.ShippingGuardsSound.checkedOptimize_not_binding hgate hb0]
    exact ⟨envs, hrunB, hlen, hobs⟩

end Tools.ShippingFGCircuitS2jCopy

namespace Tools.ShippingGen2
open Lean hiding Module Expr
open Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingQuadComposed (GenFacts)
open Tools.ShippingMachineShipsDepth (ResetNk)
open Tools.ShippingMachineCallsLinkedT (valsOf MemFacts)
open Tools.ShippingMachineChild (InRange boolsOf bitsOf)
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildCacheA (RealChildA JQC)
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain
open Tools.ShippingChildBndCore (cv dv)
open Tools.ShippingFGCircuitS1qLinked (MachineDefinesLinkedOff)

variable {ι : Type} {dom : ι → DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- (S2j copy, profile-free core run) Copy of `Tools.ShippingGen2.oneOut_topShips` (P-MEM-4; scripts/gen2/S4_PMEM4_FREEZE.md §2): `hnomem` replaced at the
same position by `hord`, passed only to `oneOutWidthAtO`; the run facts from the `O` copies. -/
theorem oneOut_topShipsOff (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hord : ∀ (k : Nat) (hk : k < p.d.shape.insts.length),
      (p.d.shape.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl : p.d.shape.layout.slots ≠ [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hcore : RunsTo (synthesizeCombinationalCoreOff p.decl) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefinesLinkedOff mctx mref cctx cref p.decl p.d.shape w raw D w1)
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hW : ∀ k, OneOutWidth P p k)
    (n : Nat) :
    TopShips p (n + 1) p.decl b raw D := by
  cases Classical.em (Nonempty ι) with
  | inr hne =>
    -- `ι` empty: `h`'s existing witness; `∀ i` is vacuous (freeze §3; `machine_ships_hierC_run` not called)
    obtain ⟨ids, nd, len, cache, regs, rnd, rlen, _⟩ := h
    unfold TopShips
    exact ⟨ids, nd, len, cache, regs, rnd, rlen, fun i => (hne ⟨i⟩).elim⟩
  | inl hne =>
  obtain ⟨i0⟩ := hne
  obtain ⟨hok, hco, hslots, houtTy, hdomB⟩ := hdata.rows
  have hkD := data_hkD p.d p.kD hok hco
  have hI := data_hI hdata
  have hIlen := data_hIlen p.d p.kD hok hco
  have hSL := data_hSL p.d hok
  have hSlen := data_hSlen p.d hok hslots
  have hLlen := data_hLlen p.d hok
  have hNIn := data_hNIn p.d p.kD hok hco hslots
  have ranA := Tools.ShippingRanABridge.machineRanA_of_runJQC L.O hA L.T ran
  -- `kidsCombB` of the run, checked by its one-output closing (as `oneOut_composedNW`)
  obtain ⟨_, _, _, _, _, _, _, _, hcl, _⟩ :=
    Tools.ShippingParentDesignA.core_closeInstsA L.O p.d hins hsimple ranA
  have hkc : kidsCombB D.modules raw.body = true := Tools.ShippingChildServe.closeInsts_kidsComb hcl
  -- the trace's witness: `ids`, `cache` and the served evidence (the SAME `h`)
  obtain ⟨ids, _, len, cache, _, _, _, _, _, _, hx, _⟩ := id h
  -- `RunFacts` (freeze §4 "Use"): `wid` from the local width fact at `i0`
  have factsB : ∀ {b' : Sparkle.IR.AST.Module}, (b' = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b' = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b' := fun hpb =>
    { gate := (Tools.ShippingParentDesignO.core_runFactsHO L.O p.d hok (Pkg.body_eq p) hco hslots hdomB hins hsimple
        houtTy hpb ranA hsl).gate
      wfB := Tools.ShippingParentTailsO.core_linkedWF_ranO L.O p.d hok (Pkg.body_eq p) hco hslots hdomB hins houtTy
        hpb ranA
      ndB := (Tools.ShippingParentDesignO.core_runFactsHO L.O p.d hok (Pkg.body_eq p) hco hslots hdomB hins hsimple
        houtTy hpb ranA hsl).ndB
      self := (Tools.ShippingParentDesignO.core_runFactsHO L.O p.d hok (Pkg.body_eq p) hco hslots hdomB hins hsimple
        houtTy hpb ranA hsl).self
      outs := (Tools.ShippingParentDesignO.core_runFactsHO L.O p.d hok (Pkg.body_eq p) hco hslots hdomB hins hsimple
        houtTy hpb ranA hsl).outs
      rst := (Tools.ShippingParentDesignO.core_runFactsHO L.O p.d hok (Pkg.body_eq p) hco hslots hdomB hins hsimple
        houtTy hpb ranA hsl).rst
      wid := core_instOutWidthsOk_oneO L.O p.d hok (Pkg.body_eq p) (nDecl := p.kD) hco hslots hdomB hins hsimple
        houtTy hpb ranA len cache
        (fun _ hk _ _ _ hargs hst hcs hmod =>
          oneOutWidthAtO L P p hx.2 hsimple hord hW i0 hk hargs hst hcs hmod) }
  -- the run-local fit chain (FitChain): `ComposedHBF` → `ComposedNWF` at height `n + 1`
  have hNWF := Tools.ShippingGen2Fit.composedNWn_of_HBF (n + 1) (R := fun _ _ => True)
    (machine_linked_callsServed1F L P p h hsimple hkD hI hIlen hSL hSlen hLlen hNIn hkc hdec hW)
    (by unfold Tools.ShippingMachineDepthH.BoundH; intros; trivial)
    (Tools.ShippingMachineDepthHR.kidsComb_of_B hkc)
  let Bnd : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx' mref' cctx' cref' w' m' D' =>
    mctx' = mctx ∧ mref' = mref ∧ cctx' = cctx ∧ cref' = cref ∧ w' = w ∧ m' = raw ∧ D' = D
  have key := Tools.ShippingFGCircuitS2jCopy.machine_ships_hierC_runOff (n := n + 1)
    (fun D' => Tools.ShippingHierStateG.KSn_local _ _) Bnd (fun _ _ _ _ => True)
    p.d (kD := p.kD) (src := p.src) (ext := p.extS) (extB := p.extBS)
    (lsrc := p.lsrc) (srcL := p.src) (extL := p.extS) (extBL := p.extBS)
    (fun {mctx'} {mref'} {cctx'} {cref'} {w'} {w''} {m'} {design'} _ _ _ hB => by
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hB
      exact (Pkg.trace L.O L.T hA p ran).toLB)
    (fun {mctx'} {mref'} {cctx'} {cref'} {w'} {w''} {m'} {design'} {b'} _ hpb _ _ hB _ => by
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hB
      refine Tools.ShippingGen2Fit.composedNWRegsF_of_composedNWF _ hNWF ?_
      intro _ _ _ _ _ _ hWr
      exact Tools.ShippingSrm32.hWd_of_wired hpb (factsB hpb).gate houtTy hWr)
    houtTy (Tools.ShippingC4InitW.hinitW_of_ok p.d hok) hcore hpost entry trivial (fun _ => factsB hpost)
  -- R-G: `key` has the consumer-1 (old) premises; L2 with both memberships from the run (U-TOP-CLKIN)
  obtain ⟨_, _, _, _, _, _, _, _, _, wired, _, _⟩ := id h
  exact topShips_ofOld_wired p (n + 1) wired hsl hpost (key ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)


end Tools.ShippingGen2

#print axioms Tools.ShippingFGCircuitS2jCopy.machine_ships_hierC_runOff
#print axioms Tools.ShippingGen2.oneOut_topShipsOff
