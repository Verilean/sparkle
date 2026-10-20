import Tools.ShippingLeafSat
import Tools.ShippingLeafDesign

/-! # The leaf route at the design level, two start states, run hypotheses discharged

BUILT by the integrator: ls1 exit 0 (574 jobs, first try; axioms standard, asserted by LeafDeadInitSatTest) (round par/leafnz-sat, base 9df7578c).

The design-level leaf heads of Tools/ShippingLeafDesign.lean (`leaf_design_of_ships`,
:240ff) take `MachineShips` (one start state) and ask `Bounded (weS (checkedOptimize b)) st0`
over every name — vacuous when the optimizer removes a nonzero-init register
(docs/parallel/leaf-nonzero-init.md §2). `leaf_sat_design` is the design-level form of
`Tools.ShippingLeafSat.leaf_sat` at the emitter's own width map `wofOf (checkedOptimize b)`:
the shipped module's IR run from the target state `tgtSt2 … (slotInit regs slots)` is, over
EVERY child map and children's state, a closed run at depth 0 (`DesignSV C 0`), showing the
source, and the ONLY one from that seeding and those states (`designSV0_of_leaf`,
`designSV0_leaf_unique`, as `leaf_design_of_ships` uses them). No run hypothesis on the
stream or the start state remains; the antecedents are the emitted-text checks and the
statement kinds of the shipped module (`hs`, as in `leaf_design_of_ships`).

Writing-time guesses: (d1) the `weS` abbrev unfolding to `EmitSem.weOf (wofOf _)` when
`leaf_sat`'s conclusion is instantiated at `wofOf (checkedOptimize b)`; (d2) `hsvR` accepted
as `TextRun` by type ascription (definitional unfolding).
-/
namespace Tools.ShippingLeafSatDesign
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingSeqOptSoundness Tools.ShippingSeqSVSoundness
open Tools.ShippingSatAssemblyS (slotInit)
open Tools.ShippingLeafSat
open Sparkle.IR.RegDedup (declWidth)

set_option maxHeartbeats 2000000 in
/-- **A leaf state machine at the full entry, at the design level, from the target start
state, with every run hypothesis discharged.** -/
theorem leaf_sat_design {declName : Name} (d : MachineData)
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
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (regs : List String),
        (∃ lets : List String, MachineWired declName d.shape ids cache raw D regs lets) ∧
        ((checkedOptimize b).body.all seqStmtOk = true →
          simpleBody b = false →
          Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf (checkedOptimize b))
            (Tools.ShippingDesignSV.weS (checkedOptimize b)) (checkedOptimize b).body = true →
          ((seqNames (checkedOptimize b).body).all fun n =>
            declWidth (checkedOptimize b) n == Tools.ShippingDesignSV.weS (checkedOptimize b) n)
            = true →
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
  obtain ⟨raw, D, hpost, ids, cache, regs, hwired, H⟩ :=
    leaf_sat d soundL hnoI hsl hSS houtTy hlen hinitW hr entry closes
  refine ⟨raw, D, hpost, ids, cache, regs, hwired, ?_⟩
  intro hs hsB hsv hwag hwofIn i bools bits T mems
  obtain ⟨hsrc, envsO, hrun, hsvR, hlenO, hobs⟩ :=
    H (Tools.ShippingDesignSV.wofOf (checkedOptimize b)) hsB hsv hwag hwofIn i bools bits T mems
  have htext : Tools.ShippingDesignSV.TextRun (checkedOptimize b)
      (seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)
        (leafIns declName d.bsIn ids cache bools bits T)) T
      (tgtSt2 (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b (checkedOptimize b)
        (slotInit regs d.shape.layout.slots)) mems envsO := hsvR
  refine ⟨hsrc, envsO, hrun, ?_, hlenO, hobs, ?_⟩
  · intro C kids
    exact Tools.ShippingLeafEntry.designSV0_of_leaf C hs (s := ⟨_, mems, kids⟩) htext
  · intro C kids envs' hD
    exact Tools.ShippingLeafDesign.designSV0_leaf_unique C hs htext hD

end Tools.ShippingLeafSatDesign
