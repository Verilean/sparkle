import Tools.ShippingShipsFreeMasked
import Tools.ShippingMachineDepthRunRA
-- UNBUILT (unit SR3i). Built by: see header of Tests/Compiler/SeqParentGenTest.lean for run names / exits.
-- SCOPE (binding): general (declaration-independent) statements used by the generator `#machine_seq_parent_endpoint`
-- (Tools/ShippingSeqParentGen.lean):
--   * `HCausalOf`, `HCallsOf`: the STATED TYPES of the two pieces of the OLD generated `f.machine_composedNR1` that the new-boundary
--     composed proof reuses (the causality fact `hcausal` of the trace head and the per-call facts `hcalls`). Both are boundary-free
--     (no `O`, no `RefLaws`, no `ChildBnd`): they are statements about `f.machineData`, the streams and the module `m`/design.
--   * `machine_design_noShips_noBd_dc`: `Tools.ShippingShipsFreeMasked.machine_design_noShips_noBd` with `Reset := ResetNk n`,
--     `Bd := kidsMaskedN`, `Inv := True`, and the three hypotheses `hFacts`/`hOuts`/`hBdRun` AND the `designCheck` success condition
--     `hdc` as closed hypotheses (each takes `entry : MachineDefines` as an argument); the conclusion has NO `designCheck` antecedent.
--     It is the declaration-independent form of the hand-wired chain `parent_noShips_noBdA` / `_free` / `_dc` of units SR3d-SR3f.
-- Nothing here is an axiom, a law or a refusal guard.  NOT a semantic-equivalence theorem by itself.
namespace Tools.ShippingSeqParentLemmas
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

/-- **Stated type of the causality fact** of a sequential-call machine (the `hcausal` argument of
`Tools.ShippingMachineCausal.machine_traceL_of_data_causal*`): the external-input families of the machine are causal in the state
stream.  A statement about `ext`/`extB`; boundary-free. -/
def HCausalOf (d : MachineData) {ι : Type} (dom : ι → DomainConfig)
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → Nat → Signal (dom i) Bool) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S S' : Signal (dom i) (HList (tys d.ss))) (t : Nat),
    (∀ c, c ≤ t → S.val c = S'.val c) →
    (∀ p w, (ext i bools bits S p w).val t = (ext i bools bits S' p w).val t) ∧
    (∀ p, (extB i bools bits S p).val t = (extB i bools bits S' p).val t)

/-- **Stated type of the per-call facts** `hcalls` of `Tools.ShippingMachineDepthRunRA.machine_linkedT_callsRNA` (and of the old
`machine_linkedT_callsRN`): every call entry `k` of callee `c` is either a memory read or satisfies `SeqFactsRN` with the
child tables `bsC outsC S PC`.  Boundary-free (mentions neither `O` nor the child-run boundary); `PC` is what a run of the callee's
entry must establish. -/
def HCallsOf (n : Nat) (d : MachineData) (dsn : Design) (m : Sparkle.IR.AST.Module) {ι : Type} {dom : ι → DomainConfig}
    (lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool)
    (kD : Nat) (bsC : Name → List (Name × MixedGateBinder)) (outsC : Name → List OutField)
    (S : ι → Name → (Nat → List Nat) → List (Nat → Nat)) (PC : Name → Sparkle.IR.AST.Module → Prop) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) k c,
    (d.shape.insts.map (·.1))[k]? = some c →
    MemFacts d.shape (lsrc i bools bits) d.ls.length (d.bsIn.drop kD) kD (ext i bools bits) k c ∨
    SeqFactsRN (childMap dsn.modules) n d.shape dsn m.body (lsrc i bools bits) d.ls.length
      (d.bsIn.drop kD) kD (extB i bools bits) (ext i bools bits) bsC outsC (S i) PC k c

/-- **The depth endpoint with the check premises discharged by closed hypotheses.**  `machine_design_noShips_noBd` at
`Reset := ResetNk n`, `Bd := fun b D => kidsMaskedN D.modules b.body = true`, `Inv := True`, with
* `hFacts` (run facts), `hOuts` (gated `outsCheck`), `hBdRun` (`kidsMaskedN`) and `hdc` (`designCheck … = true`) given as CLOSED
  hypotheses over every context (each takes the `entry` as an argument), so that the partial application leaves exactly
  `hr`, `entry`, `closes` as premises;
* the `designCheck … = true →` antecedent of the conclusion removed (supplied by `hdc`).
The boundary `Bnd` stays in the conclusion. -/
theorem machine_design_noShips_noBd_dc (n : Nat) (Bnd : CtxBnd)
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
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : C mctx mref cctx cref) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (Bnd mctx mref cctx cref w raw D →
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
                  (envs'[j]'hj) o.name = f j) := by
  obtain ⟨raw, D, w1, hcore, hpost⟩ := synthesizeCombinational_checked hr
  refine ⟨raw, D, hpost, ?_⟩
  intro hBnd
  exact design_at_free n (ResetNk n) (Bnd mctx mref cctx cref w) (fun b D => kidsMaskedN D.modules b.body = true)
    (machine_ships_hierC_at_free (fun D => KSn (childMap D.modules) n)
      (fun D => KSn_local (childMap D.modules) n) (ResetNk n) Bnd C
      (fun b D => kidsMaskedN D.modules b.body = true) (fun _ _ => True)
      (fun b D h => KSn_boundedIn D.modules b.body h n) (true_inv (ResetNk n)) d soundL composed
      houtTy hcore hpost entry closes (fun hBnd => hFacts hcore hpost entry hBnd))
    (fun hBnd => hOuts hcore hpost entry (hFacts hcore hpost entry hBnd).gate hBnd)
    (hdc hcore hpost entry hBnd) hBnd (hBdRun hcore hpost entry hBnd)

#print axioms machine_design_noShips_noBd_dc
end Tools.ShippingSeqParentLemmas
