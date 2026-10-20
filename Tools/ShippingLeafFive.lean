import Tools.ShippingLeafSatDesign
import Tools.ShippingGuardsLeaf
-- BUILT by the integrator: lv1 exit 0 (559 jobs, first try; integrator-written, round par/leaf5).

/-! # `leaf_sat_design` with four of its five inner antecedents discharged from the run

`leaf_sat_design` (Tools/ShippingLeafSatDesign.lean) concludes the closed-design run of the optimized leaf
module at the emitter's own width map `wofOf (checkedOptimize b)` under five inner antecedents. Here
(1) `(checkedOptimize b).body.all seqStmtOk` (`leaf_entry_shipped_seq_closed`), (2) `simpleBody b = false`,
(3) `seqCheck` at `wofOf`, (4) the `seqNames` width agreement (`leaf_entry_textChecks_closed`) are derived
from the same run, given the data/reflection bundle `LeafKid` (produced per declaration by
`#machine_leaf_entry`) and `ChildBnd`. The fifth inner antecedent (every input of `dropZeroWidth raw` has `declWidth ≤ weS (checkedOptimize b)`)
is left here and discharged in `Tools/ShippingLeafInputWidths.lean` (`leaf_input_widths`,
`leaf_sat_design_closed5`: no inner antecedent left; built iw2). Premises added w.r.t. `leaf_sat_design`: `K`, `hbnd`. -/
namespace Tools.ShippingLeafFive
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingSeqOptSoundness Tools.ShippingSeqSVSoundness
open Tools.ShippingSatAssemblyS (slotInit)
open Tools.ShippingLeafSat
open Sparkle.IR.RegDedup (declWidth)

theorem leaf_sat_design_closed {declName : Name} (d : MachineData)
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      MachineTraceL declName d m design dom src (fun _ _ bits => bits) lsrc)
    (hnoI : d.shape.insts = []) (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hlen : d.nIn + d.shape.layout.slots.length + d.shape.layout.lets = d.shape.binders.length)
    (hinitW : ∀ f ∈ d.shape.layout.slots, f.init < 2 ^ f.width)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape)
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref declName d)
    (hbnd : Tools.ShippingChildInv.ChildBnd mref cref w) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (regs : List String),
        (∃ lets : List String, MachineWired declName d.shape ids cache raw D regs lets) ∧
        (
          (∀ x ∈ (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).inputs.map (·.name),
            declWidth (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) x ≤
              Tools.ShippingDesignSV.weS (checkedOptimize b) x) →
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (T : Nat) (mems : MEnv),
            (∀ t st, t < T → SourceInputs declName d.bsIn ids cache
              (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
              (seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)
                (leafIns declName d.bsIn ids cache bools bits T) t st)) ∧
            ∃ envsO,
              runModule (declWidth (checkedOptimize b)) (checkedOptimize b).body
                (seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)
                  (leafIns declName d.bsIn ids cache bools bits T)) T
                (tgtSt2 (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b (checkedOptimize b)
                  (slotInit regs d.shape.layout.slots)) mems = some envsO ∧
              (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
                  (kids : String → Tools.ShippingHierStateG.KT 0),
                Tools.ShippingDesignSV.DesignSV C 0 (checkedOptimize b)
                  (seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)
                    (leafIns declName d.bsIn ids cache bools bits T)) T
                  ⟨tgtSt2 (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b (checkedOptimize b)
                    (slotInit regs d.shape.layout.slots), mems, kids⟩ envsO) ∧
              envsO.length = T ∧
              (∀ j (hj : j < envsO.length) (k : Nat) (q : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) q.name = f j) ∧
              ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
                (kids : String → Tools.ShippingHierStateG.KT 0)
                (envs' : List Sparkle.IR.Semantics.Env),
                Tools.ShippingDesignSV.DesignSV C 0 (checkedOptimize b)
                  (seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)
                    (leafIns declName d.bsIn ids cache bools bits T)) T
                  ⟨tgtSt2 (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b (checkedOptimize b)
                    (slotInit regs d.shape.layout.slots), mems, kids⟩ envs' →
                envs' = envsO) := by
  obtain ⟨raw, D, hpost, ids, cache, regs, hW, H⟩ :=
    Tools.ShippingLeafSatDesign.leaf_sat_design d @soundL hnoI hsl hSS houtTy hlen hinitW hr entry closes
  have h1 := Tools.ShippingGuardsLeaf.leaf_entry_shipped_seq_closed K hbnd hr
  obtain ⟨h2, h3, h4⟩ := Tools.ShippingGuardsLeaf.leaf_entry_textChecks_closed K hbnd hr
  exact ⟨raw, D, hpost, ids, cache, regs, hW, H h1 h2 h3 h4⟩

end Tools.ShippingLeafFive
