import Tools.ShippingCallsGateA
-- BUILT (unit SR2f): r2 exit 0; with at_reads: a4 exit 0.
open Lean in
/-! # Unit SR2f: run-local entry-constant boundary (`EntryDefinesRun`)

`EntryDefines c v` quantifies over ALL worlds `w1 … w6` of a `getConstInfo` / `getEnv` pair.  Every consumer on the
gate path (`gate_core_facts`, `gate_child_comb`, `gate_child_fullFacts`) applies it only at the reads of ONE
successful core run (`synthesizeCombinationalCore_reads`).  `EntryDefinesRun` asks the entry constant to be a
definition of value `v` only for tuples whose `synthesizeFromConst` sub-run returns the module of a successful core
run.  `EntryDefines → EntryDefinesRun` (`EntryDefinesRun.of_entry`).  Local ≠ discharged. -/
namespace Tools.ShippingEntryDefinesRun
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineCompose
open Tools.ShippingMachineChild
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingEntrySoundness (RunsTo EnvDefines entry_kept synthesizeCombinationalCore_reads MReturns)
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedExecutionSoundness
open Tools.ShippingUnifiedMeaning (pack)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingTransitionClosed Tools.ShippingMergeClosed
open Tools.ShippingSettledSoundness (Acyclic)
open Sparkle.IR.NameHints (Allocated)
open Sparkle.IR.Reorder
open Tools.ShippingGateChild Tools.ShippingGateChildComb

variable {tenv : Lean.Environment}

def EntryDefinesRun (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name) (v : Lean.Expr) : Prop :=
  ∀ (w : Void IO.RealWorld) (M : Sparkle.IR.AST.Module) (D : Design) (w' : Void IO.RealWorld),
    RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w' →
    ∀ (logProf : String → IO Unit) (envR : Environment) (ci : ConstantInfo)
      (w1 w2 w3 w4 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n) logProf
        declName [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref w3 (M, D) w4 →
      ∃ d : DefinitionVal,
        entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) = .defnInfo d ∧
          d.value = v

theorem EntryDefinesRun.of_entry {mctx mref cctx cref declName v}
    (h : EntryDefines mctx mref cctx cref declName v) : EntryDefinesRun mctx mref cctx cref declName v :=
  fun _ _ _ _ _ _ envR ci w1 w2 _ _ w5 w6 get henv _ => h w1 ci w2 w5 envR w6 get henv

/-- The parent-level form: every successful core run of `c` in the refs, in ANY contexts. -/
def EntryDefinesRuns (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)
    (declName : Name) (v : Lean.Expr) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), EntryDefinesRun mctx mref cctx cref declName v

theorem EntryDefinesRuns.of_entry {mctx mref cctx cref declName v}
    (h : EntryDefines mctx mref cctx cref declName v) : EntryDefinesRuns mref cref declName v :=
  fun _ _ => EntryDefinesRun.of_entry (Tools.ShippingReflectCtx.EntryDefines.ctx h)

/-- The environment half: the constant a successful core run reads is a definition of value `v`
(a property of the run's own reads, not of arbitrary start worlds). -/
def EnvDefinesRun (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name) (v : Lean.Expr) : Prop :=
  ∀ (w : Void IO.RealWorld) (M : Sparkle.IR.AST.Module) (D : Design) (w' : Void IO.RealWorld),
    RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w' →
    ∀ (logProf : String → IO Unit) (envR : Environment) (ci : ConstantInfo)
      (w1 w2 w3 w4 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n) logProf
        declName [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref w3 (M, D) w4 →
      ∃ d : DefinitionVal, ci = .defnInfo d ∧ d.value = v

theorem EnvDefinesRun.of_env {mctx mref cctx cref declName v}
    (h : EnvDefines mctx mref cctx cref declName v) : EnvDefinesRun mctx mref cctx cref declName v :=
  fun _ _ _ _ _ _ envR ci w1 w2 _ _ w5 w6 get henv _ => h w1 ci w2 get

/-- The gate half as in `EntryDefines.of_env`, now at the run's reads. -/
theorem EntryDefinesRun.of_envRun {mctx mref cctx cref declName v}
    (env : EnvDefinesRun mctx mref cctx cref declName v)
    (gate : ∀ d : DefinitionVal, d.value = v → ∀ isInst,
      (mixedCertifiedShape? false [] (.defnInfo d) isInst).isSome = true) :
    EntryDefinesRun mctx mref cctx cref declName v := by
  intro w M D w' hr logProf envR ci w1 w2 w3 w4 w5 w6 get henv run
  obtain ⟨d, rfl, hv⟩ := env w M D w' hr logProf envR _ w1 w2 w3 w4 w5 w6 get henv run
  refine ⟨d, ?_, hv⟩
  have h := gate d hv (instancePredicate envR)
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h
  exact Tools.ShippingEntrySoundness.entryConst_mixed hr

theorem EntryDefinesRuns.of_envRuns {mref cref declName v}
    (env : ∀ mctx cctx, EnvDefinesRun mctx mref cctx cref declName v)
    (gate : ∀ d : DefinitionVal, d.value = v → ∀ isInst,
      (mixedCertifiedShape? false [] (.defnInfo d) isInst).isSome = true) :
    EntryDefinesRuns mref cref declName v :=
  fun mctx cctx => EntryDefinesRun.of_envRun (env mctx cctx) gate

/-- **Coverage.** For a successful core run, the reads the consumers extract (`synthesizeCombinationalCore_reads`)
form a tuple at which `EntryDefinesRun` applies: the premise is used at the run's own `getConstInfo` / `getEnv`
worlds, and yields the definition there. -/
theorem EntryDefinesRun.at_reads {mctx mref cctx cref declName v}
    (h : EntryDefinesRun mctx mref cctx cref declName v)
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w') :
    ∃ (envR : Environment) (ci : ConstantInfo) (w1 w2 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      ∃ d : DefinitionVal,
        entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) = .defnInfo d ∧
          d.value = v := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ := synthesizeCombinationalCore_reads hr
  exact ⟨envR, ci, w1, w2, w5, w6, get, henv, h w M D w' hr logProf envR ci w1 w2 w3 w4 w5 w6 get henv run⟩

section leaves
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The gate's core run, with its ports.** A run of the core entry on a
declaration the unified gate accepts (its value peels to the quote of a
well-formed term; `EntryDefines`: the constant the entry hands on, the
declaration as read or its unfolding) returns a module whose value on admissible inputs is the
term's (`RawValueAt`) and whose input ports are the binder walk's. -/
theorem gate_core_factsL {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, design) w')
    (entry : EntryDefinesRun mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)),
      ids.Nodup ∧ ids.length = bs.length ∧
      (∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n) (initial : Env)
          (mems : MEnv),
        SourceInputs declName bs ids cache bools bits initial →
        RawValueAt srt.width bs m initial mems
          (pack srt (eval (fun j => bools (bpos j)) (fun j w => bits (vpos j) w) e)).toNat) ∧
      (∀ bools bits, m.inputs = inputPorts bools bits (bs.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName))) ∧
      Tools.ShippingMixedEntrySoundness.PositiveBinders bs := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hr
  obtain ⟨d, hd, definition⟩ := entry w m design w' hr logProf envR ci w1 w2 w3 w4 w5 w6 get henv run
  rw [hd] at run
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have shape := term_gate (d := d) (by rw [definition]; exact peel) he hb hv
  have core := synthesizeFromConst_mixed_run oldGate (shape _) run.mreturns
  obtain ⟨ids, cache, returned, st, nd, len, hrun, hm, _, nameLegal⟩ :=
    synthesizeMixedCertified_returns core
  obtain ⟨vals, _, ins⟩ := transition_facts nd len hrun hm nameLegal he hb hv rfl
  exact ⟨ids, cache, nd, len, vals, ins,
    Tools.ShippingMixedPrintSoundness.mixedShape_positive (shape (fun _ => false))⟩

/-- **A gate child at the full entry.** A run of the full entry on a
declaration the unified gate accepts returns a module that computes `F` on
its argument ports, `F` being the term's value on them decoded (`ChildFn`, as
`machine_linked` uses it): the gate analogue of `child_full`, and without its
cleanup premise — the gate's module is typed, so the zero-width cleanup
changes nothing it computes. -/
theorem gate_child_fullL {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefinesRun mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    {F : List Nat → Nat}
    (hF : ∀ vs, InRange vs (bs.filter fun b => b.2 != .domain) →
      F vs = (pack srt (eval (fun j => decB bs vs (bpos j)) (fun j w => decV bs vs (vpos j) w) e)).toNat) :
    ChildFn b (fun vs => InRange vs (bs.filter fun b => b.2 != .domain)) F := by
  obtain ⟨M, D, w1, hcore, hpost⟩ := Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  obtain ⟨ids, cache, nd, len, vals, ins, positive⟩ := gate_core_factsL hcore entry old peel he hb hv
  obtain ⟨hfn, hall, htp⟩ := gate_childFn nd len vals ins positive hF
  exact childFn_post hfn htp hall hpost

set_option maxHeartbeats 1000000 in
/-- **A gate child's full-entry module is combinational, closed and
one-output** — from a run of the full entry and the reflection of the
declaration. -/
theorem gate_child_combL {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefinesRun mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ChildComb b := by
  obtain ⟨M, D, w1, hcore, hpost⟩ := Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  obtain ⟨logProf, envR, ci, w1', w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hcore
  obtain ⟨d, hd, definition⟩ := entry w M D w1 hcore logProf envR ci w1' w2 w3 w4 w5 w6 get henv run
  rw [hd] at run
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have shape := term_gate (d := d) (by rw [definition]; exact peel) he hb hv
  have core := Tools.ShippingGateChild.synthesizeFromConst_mixed_run oldGate (shape _) run.mreturns
  obtain ⟨ids, cache, returned, st, nd, len, hrun, hm, _, nameLegal⟩ :=
    synthesizeMixedCertified_returns core
  have positive := Tools.ShippingMixedPrintSoundness.mixedShape_positive (shape (fun _ => false))
  obtain ⟨hclosed, hassign, ⟨ow, pb⟩, ready, -, -⟩ :=
    transition_closed nd len hrun hm nameLegal positive e he hb hv rfl
  obtain ⟨_, ⟨B, wOut, hB⟩, _⟩ := transition_facts nd len hrun hm nameLegal he hb hv rfl
  -- the core module
  have hM : ChildComb M :=
    { assigns := acyclic_isAssign pb.order
      closed := hclosed
      output := pb.output
      outDriven := by
        rw [hB]
        exact List.mem_flatMap.mpr ⟨_, List.mem_append_right _ (List.mem_singleton.mpr rfl),
          by simp [stmtWrites]⟩
      inputNames := pb.inputNames
      inputAlloc := fun p hp => pb.wireNames p (pb.inputWires p hp) }
  -- the zero-width cleanup changes nothing of a typed module
  obtain ⟨dzb, _, dzi, dzo, _⟩ := Tools.ShippingTypedPostSoundness.dropZeroWidth_typed ready
  have hZ : ChildComb (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) :=
    { assigns := by rw [dzb]; exact hM.assigns
      closed := by rw [dzb, dzi]; exact hM.closed
      output := by rw [dzo]; exact hM.output
      outDriven := by rw [dzb]; exact hM.outDriven
      inputNames := by rw [dzi]; exact hM.inputNames
      inputAlloc := by rw [dzi]; exact hM.inputAlloc }
  rcases hpost with rfl | rfl
  · exact hZ
  · -- the checked merge of an assignment-only body
    obtain ⟨mi, mo, _⟩ := Sparkle.IR.RefineCheck.mergeChecked_ports
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)
    obtain ⟨mc, mw⟩ := mergeChecked_closed (S := (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).inputs.map (·.name))
      hZ.assigns hZ.closed
    have hmd : Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) =
        Sparkle.IR.RegDedup.mergeDuplicates (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) := by
      unfold Sparkle.IR.RefineCheck.mergeChecked
      simp only [hZ.assigns, if_true]
    exact
      { assigns := by
          rw [hmd]
          exact acyclic_isAssign (Tools.ShippingPostSoundness.mergeDuplicates_order
            (by rw [dzb]; exact pb.order))
        closed := by rw [mi]; exact mc
        output := by rw [mo]; exact hZ.output
        outDriven := by rw [mw]; exact hZ.outDriven
        inputNames := by rw [mi]; exact hZ.inputNames
        inputAlloc := by rw [mi]; exact hZ.inputAlloc }


set_option maxHeartbeats 1000000 in
/-- **A gate child's full-entry result, from one run and the declaration's
reflection.** -/
theorem gate_child_fullFactsL {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefinesRun mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ChildFull declName bs b design := by
  have hcomb := gate_child_combL hr entry old peel he hb hv
  obtain ⟨M, D, w1, hcore, hpost, hdes⟩ := synthesizeCombinational_parts hr
  obtain ⟨logProf, envR, ci, w1', w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hcore
  obtain ⟨d, hd, definition⟩ := entry w M D w1 hcore logProf envR ci w1' w2 w3 w4 w5 w6 get henv run
  rw [hd] at run
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have shape := term_gate (d := d) (by rw [definition]; exact peel) he hb hv
  have core := Tools.ShippingGateChild.synthesizeFromConst_mixed_run oldGate (shape _) run.mreturns
  obtain ⟨ids, cache, returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    synthesizeMixedCertified_returns core
  have positive := Tools.ShippingMixedPrintSoundness.mixedShape_positive (shape (fun _ => false))
  obtain ⟨-, -, -, ready, hdesign, hname⟩ :=
    transition_closed nd len hrun hm nameLegal positive e he hb hv rfl
  obtain ⟨_, _, hin⟩ := transition_facts nd len hrun hm nameLegal he hb hv rfl
  have hMtys : M.inputs.map (·.ty) = (bs.filter fun x => x.2 != .domain).map fun x => kindTy x.2 := by
    rw [hin (fun _ => false) (fun _ n => 0#n)]
    exact Tools.ShippingTransitionFields.inputPorts_tys bs ids _ len
  have hDm : D.modules = [] := by
    rw [hD, hdesign]
    rfl
  obtain ⟨_, _, dzi, _, _⟩ := Tools.ShippingTypedPostSoundness.dropZeroWidth_typed ready
  refine ⟨hcomb, ?_, ?_, hdes hDm⟩
  · rcases hpost with rfl | rfl
    · rw [dzi]; exact hMtys
    · rw [(Sparkle.IR.RefineCheck.mergeChecked_ports _).1, dzi]; exact hMtys
  · rcases hpost with rfl | rfl
    · rw [dropZeroWidth_name]; exact hname
    · rw [Tools.ShippingMachineDepthRun.mergeChecked_name, dropZeroWidth_name]; exact hname


variable (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)

/-- `childFull_of_realA` with the run-local boundary. -/
theorem childFull_of_realAL {c : Name} {y : Tools.ShippingChildInv.Res}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (entry : EntryDefinesRuns mref cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (h : Tools.ShippingChildCacheA.RealChildA O c y) : ChildFull c bs y.1 y.2 := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    exact gate_child_fullFactsL hr (entry mctx' cctx') old peel he hb hv

/-- **The boundary for a gate child, run-local.** -/
def GateRunL (c : Name) (v : Lean.Expr) (mc : Sparkle.IR.AST.Module) : Prop :=
  ∃ (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld) (design : Design),
    RunsTo (synthesizeCombinational c) mctx mref cctx cref w (mc, design) w' ∧
    EntryDefinesRun mctx mref cctx cref c v

theorem childFn_of_gateRunL {c : Name} {v : Lean.Expr} {mc : Sparkle.IR.AST.Module}
    {P : List Nat → Prop} {F : List Nat → Nat}
    (hc : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
      {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w' →
      EntryDefinesRun mctx mref cctx cref c v → ChildFn b P F)
    (h : GateRunL c v mc) : ChildFn mc P F := by
  obtain ⟨_, _, _, _, _, _, _, hr, entry⟩ := h
  exact hc hr entry

end leaves
end Tools.ShippingEntryDefinesRun
