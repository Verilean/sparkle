import Tools.ShippingSeqParentLemmas
import Tools.ShippingMachineDepthRunR
import Tools.ShippingSharedLeafNL
-- BUILT (unit SR11): b2 exit 0 (qbuild build Tools.ShippingSeqParentAt); see REPORT-SR11.md for the final-SHA rebuild.
-- SCOPE (binding): `machine_design_noShips_noBd_dc_at` is `Tools.ShippingSeqParentLemmas.machine_design_noShips_noBd_dc` with the core run
-- (`hcore`, producing the RAW module `raw` and design `D`) and the clean-up relation (`hpost`: `b` is the clean-up of `raw`) GIVEN as
-- arguments instead of being obtained from `synthesizeCombinational_checked` of an outer run, and without the existential `∃ raw D`.
-- The proof body is the original one with that `obtain` removed; nothing else differs.  Purpose (REVIEW-SR11): the endpoint can then be
-- applied to the SAME `raw`/`D` that another theorem (`topshare_entry_run4_ret`) obtained from the same start world.
-- Also: `DesignSemConcl` (the semantic conclusion of the endpoint for the post-processed `b` with the children of the raw design `D`, stated as a
-- definition so a caller can put it in a conclusion) and `moduleByName_post_other` (the returned design `y.2 = topMap …` looks up every module not
-- named like the entry's as the core run's design does).
-- WORDING (SR12, reviewer): the exact object of the semantic conclusion is `checkedOptimize` of `y.1` judged with the children of the RAW design `Dg`
-- (inputs / reset / bounds etc. remain inside `DesignSemConcl`); it is NOT `y.1` itself in its own design and NOT `DesignSV` of the returned design `y.2`.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field, no existing statement changed.
namespace Tools.ShippingSeqParentAt
open Tools.ShippingSeqParentLemmas
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
open Tools.ShippingMachineCallsLinkedT Tools.ShippingMachineCallsLinkedTNR
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineSource Tools.ShippingMachineDenote

/-- The semantic statement of the endpoint for the post-processed module `b` (the clean-up of the raw `raw`) with the children of the raw
design `D`: the emitted `checkedOptimize b` runs (`DesignSV`) and its outputs are the source's outputs (existence and for every run). -/
def DesignSemConcl (n : Nat) (declName : Name) (d : MachineData) (kD : Nat) {ι : Type} (dom : ι → DomainConfig)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool)
    (b raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
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
          (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
          (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS (checkedOptimize b) x) →
          Bounded (weS (checkedOptimize b)) st0 →
          (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
            childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) n gc (kids iname)) →
          (∃ envsO,
            DesignSV (childMap D.modules) n (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
              d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
              (envsO[j]'hj) o.name = f j)
          ∧ ∀ envs', DesignSV (childMap D.modules) n (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
              envs'.length = T ∧
              ∀ j (hj : j < envs'.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envs'[j]'hj) o.name = f j

theorem machine_design_noShips_noBd_dc_at (n : Nat) (Bnd : CtxBnd)
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
    (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      C mctx mref cctx cref →
      Bnd mctx mref cctx cref w m design →
      MachineTraceLB declName d m design dom srcL extL extBL lsrc)
    (composed : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      C mctx mref cctx cref →
      Bnd mctx mref cctx cref w m design → Tools.ConeFold.memFree m.body →
      ComposedG (fun D => KSn (childMap D.modules) n) (ResetNk n) declName d kD m design dom src ext extB)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hFacts : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
      {raw b : Sparkle.IR.AST.Module} {D : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      MachineDefines mctx mref cctx cref declName d.shape →
      Bnd mctx mref cctx cref w raw D →
      Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b)
    (hOuts : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
      {raw b : Sparkle.IR.AST.Module} {D : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      MachineDefines mctx mref cctx cref declName d.shape →
      hierGate b = true → Bnd mctx mref cctx cref w raw D →
      Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true)
    (hBdRun : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
      {raw b : Sparkle.IR.AST.Module} {D : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      MachineDefines mctx mref cctx cref declName d.shape →
      Bnd mctx mref cctx cref w raw D →
      kidsMaskedN D.modules b.body = true)
    (hdc : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
      {raw b : Sparkle.IR.AST.Module} {D : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      MachineDefines mctx mref cctx cref declName d.shape →
      Bnd mctx mref cctx cref w raw D →
      designCheck (childMap D.modules) n (checkedOptimize b) = true)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld}
    (hcore : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : C mctx mref cctx cref) :
    Bnd mctx mref cctx cref w raw D →
      DesignSemConcl n declName d kD dom src ext extB b raw D := by
  intro hBnd
  unfold DesignSemConcl
  exact design_at_free n (ResetNk n) (Bnd mctx mref cctx cref w) (fun b D => kidsMaskedN D.modules b.body = true)
    (machine_ships_hierC_at_free (fun D => KSn (childMap D.modules) n)
      (fun D => KSn_local (childMap D.modules) n) (ResetNk n) Bnd C
      (fun b D => kidsMaskedN D.modules b.body = true) (fun _ _ => True)
      (fun b D h => KSn_boundedIn D.modules b.body h n) (true_inv (ResetNk n)) d soundL composed
      houtTy hcore hpost entry closes (fun hBnd => hFacts hcore hpost entry hBnd))
    (fun hBnd => hOuts hcore hpost entry (hFacts hcore hpost entry hBnd).gate hBnd)
    (hdc hcore hpost entry hBnd) hBnd (hBdRun hcore hpost entry hBnd)

/-- **The returned design `y.2` looks up every module NOT named like the entry's exactly as the core run's design `Dg` does.**
From the clean-up relation of `topshare_entry_run4_ret` (`y.2 = topMap M.name f Dg`, one or two clean-up stages): the stages are
name-preserving (`dropZW_name`, `mergeChecked_name`), so `moduleByName_map_other` applies.  This is the side condition that lets the
CHILD lookups of the semantic statement (`childMap D.modules`, `D := Dg`) be read in the returned design for every callee name
different from the entry's name.  It does NOT by itself transport `DesignSV` from `Dg` to `y.2` (OPEN in this change). -/
theorem moduleByName_post_other (M : Sparkle.IR.AST.Module) (Dg y2 : Design)
    (h : y2 = Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg ∨
      y2 = Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.RefineCheck.mergeChecked
        (Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg)) :
    ∀ mn : String, mn ≠ M.name → moduleByName y2.modules mn = moduleByName Dg.modules mn := by
  intro mn hmn
  have hd := Tools.ShippingMachineDepthRun.moduleByName_map_other M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule
    Tools.ShippingMachineDepthRun.dropZW_name
  have hm := Tools.ShippingMachineDepthRun.moduleByName_map_other M.name Sparkle.IR.RefineCheck.mergeChecked
    Tools.ShippingMachineDepthRun.mergeChecked_name
  rcases h with rfl | rfl
  · exact hd Dg.modules mn hmn
  · show moduleByName ((Dg.modules.map _).map _) mn = _
    rw [hm _ mn hmn, hd _ mn hmn]

#print axioms machine_design_noShips_noBd_dc_at
#print axioms moduleByName_post_other
end Tools.ShippingSeqParentAt
