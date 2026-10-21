import Tools.ShippingEntryDefinesRun
import Tools.ShippingMachineOutcomeA3
-- BUILT (unit SR2g): g4 exit 0.
open Lean in
/-! # Unit SR2g: the reads of the entry as ONE linked run (start world, consecutive reads, body, finally, end world)

SR2f's `EntryDefinesRun` quantified over `getConstInfo` (w1→w2), `getEnv` (w5→w6) and the body (w3→w4) at
UNCONNECTED worlds, keyed on the output `(M, D)`.  Here:

* `coreHead declName` / `coreRest declName s` split `synthesizeCombinationalCore declName [] false` into the prefix
  (profile read, depth check, saved maps, cache clears, `depth+1`) and `try doSynth finally …`;
  `core_eq` is the equation, `core_split`/`core_chain` the CONSEQUENCE for a run `hr : w → w'` (law-free):
  `w —head→ w1 —getConstInfo→ w2 —getEnv→ w3 —body→ w4 —finally→ w'`, every world the output of the previous step.
* `EntryDefinesRunG` asks the entry constant to be a definition of value `v` only for such a CHAIN (the run is a
  function of its start world, so the chain is determined by `w`; another run with the same `(M, D)` is not covered).
  `EntryDefinesRun.toG`: the SR2f premise implies it.
* ENVIRONMENT SNAPSHOT: `getEnv_value`, `getConstInfo_value` (law-free): both reads return the environment field of the
  Core state AT THEIR START WORLD (`envAt cref`).  `ST.Ref.get` is an opaque primitive, so nothing in the model says
  the worlds `w1`, `w2`, `w3`, `w4` carry the same `envAt`: that is `EnvSnapshot`, a NAMED HYPOTHESIS (OPEN).
  `ci_in_envR` shows what it would give.  Writes that could break it: any `Core.State.env` write between `w1` and
  `w4` — none occurs in `Sparkle/` source (no `addDecl`/`setEnv`/`modifyEnv`/`withEnv` outside Verification), but the
  body calls Lean's `whnf`/`inferType`/`mkAppM`/`unfoldDefinition?`/instance synthesis, whose env-preservation is
  not modelled by any law (`RefLawsAOps` says nothing about `Core.State`).
No `sorry`, no axiom, no new law. -/
namespace Tools.ShippingEntryReadsLinked
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
open Tools.ShippingChildInv (profLogIO readOf)
open Tools.ShippingMachineOutcomeA3 (coreFinally RunsTo.try_finally')
open Tools.ShippingEntryDefinesRun (EntryDefinesRun)

/-- What the entry's prefix saves for its `finally` (and the profile flag for `logProf`). -/
structure CoreSaved where
  profile : Bool
  depth : Nat
  sf : Std.HashMap Name Lean.Expr
  sw : Std.HashMap String Nat
  sl : Std.HashMap String String
  sp : Std.HashMap String String
  sc : Std.HashMap String String
  ss : Std.HashMap (UInt64 × String) String
  sg : Std.HashMap String String

/-- The prefix of `synthesizeCombinationalCoreWith … declName [] false`, up to and including `depth + 1`
(copied from the source with `parameters := []`, `symbolicMode := false`). -/
def coreHead (declName : Name) : MetaM CoreSaved := do
  let profile := (← IO.getEnv "SPARKLE_PROFILE").isSome
  let logProf (msg : String) : IO Unit := do
    if profile then
      IO.eprintln msg
      Sparkle.Compiler.flushStderr
      let h ← IO.FS.Handle.mk "/tmp/sparkle-profile.log" .append
      h.putStrLn msg
      h.flush
  logProf s!"[profile] synthesizeCombinational {declName} entering"
  let depth ← sparkleSynthDepth.get
  if depth ≥ sparkleSynthDepthLimit then
    throwError "hardware modules nested deeper than the synthesis depth limit"
  let savedFvarMap ← if depth == 0 then pure ({} : Std.HashMap Lean.Name Lean.Expr)
                     else sparkleFvarValueMap.get
  let savedWireWidthCache ←
    if depth == 0 then pure ({} : Std.HashMap String Nat)
    else sparkleWireWidthCache.get
  let savedLetWireCache ←
    if depth == 0 then pure ({} : Std.HashMap String String)
    else sparkleLetWireCache.get
  let savedLoopWireCache ←
    if depth == 0 then pure ({} : Std.HashMap String String)
    else sparkleLoopWireCache.get
  let savedWireCanon ←
    if depth == 0 then pure ({} : Std.HashMap String String)
    else sparkleWireCanon.get
  let savedSubInstanceOutputs ←
    if depth == 0 then pure ({} : Std.HashMap (UInt64 × String) String)
    else sparkleSubInstanceOutputs.get
  let savedSingleOutInstanceCache ←
    if depth == 0 then pure ({} : Std.HashMap String String)
    else sparkleSingleOutInstanceCache.get
  if depth == 0 then
    sparkleTypeCache.set {}
    sparkleTypeCacheHits.set 0
    sparkleTypeCacheMiss.set 0
    sparkleSubModuleCache.set {}
    sparkleChildCache.set {}
    sparkleSubInstanceOutputs.set {}
    sparkleSingleOutInstanceCache.set {}
    sparkleFvarValueMap.set {}
    sparkleWireWidthCache.set {}
    sparkleLetWireCache.set {}
    sparkleLoopWireCache.set {}
    sparkleWireCanon.set {}
  else
    sparkleFvarValueMap.set {}
    sparkleWireWidthCache.set {}
    sparkleLetWireCache.set {}
    sparkleLoopWireCache.set {}
    sparkleWireCanon.set {}
    sparkleSubInstanceOutputs.set {}
    sparkleSingleOutInstanceCache.set {}
  sparkleSynthDepth.set (depth + 1)
  pure ⟨profile, depth, savedFvarMap, savedWireWidthCache, savedLetWireCache, savedLoopWireCache,
    savedWireCanon, savedSubInstanceOutputs, savedSingleOutInstanceCache⟩

/-- `try doSynth finally …`, `doSynth` = `getConstInfo`, `getEnv`, `synthesizeFromConst` on the entry constant. -/
def coreRest (declName : Name) (s : CoreSaved) : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
  let doSynth : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
    let constInfo ← getConstInfo declName
    let env ← getEnv
    synthesizeFromConst (fun e h t n => translateExprToWire env e h t n) (profLogIO s.profile) declName [] false true
      (entryConst true false [] constInfo
        (instancePredicate env) (userInliner env) (structEnv env))
      (instancePredicate env)
  tryFinally doSynth (coreFinally s.depth s.sf s.sw s.sl s.sp s.sc s.ss s.sg)

/-- bind associativity, by cases on the first run. -/
theorem bind_assoc_fn {α β γ : Type} (x : MetaM α) (f : α → MetaM β) (k : β → MetaM γ) :
    ((x >>= f) >>= k) = (x >>= fun a => f a >>= k) := by
  funext a b c d w
  change EST.bind (EST.bind (x a b c d) (fun v => f v a b c d)) (fun v => k v a b c d) w =
    EST.bind (x a b c d) (fun v => EST.bind (f v a b c d) (fun u => k u a b c d)) w
  unfold EST.bind
  cases x a b c d w <;> rfl

theorem ite_bind_fn {α β : Type} {c : Prop} [Decidable c] (a b : MetaM α) (k : α → MetaM β) :
    ((if c then a else b) >>= k) = if c then a >>= k else b >>= k := by
  split <;> rfl

theorem core_eq (declName : Name) :
    synthesizeCombinationalCore declName [] false = (coreHead declName >>= fun s => coreRest declName s) := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith coreHead coreRest
  simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc_fn, ite_bind_fn]
  rfl

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The run of the core entry is a run of the prefix `w → w1` and a run of the rest `w1 → w'`. -/
theorem core_split {declName : Name} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w') :
    ∃ (s : CoreSaved) (w1 : Void IO.RealWorld),
      RunsTo (coreHead declName) mctx mref cctx cref w s w1 ∧
      RunsTo (coreRest declName s) mctx mref cctx cref w1 (M, D) w' := by
  rw [core_eq] at hr
  obtain ⟨s, w1, hh, hk⟩ := RunsTo.bind hr
  exact ⟨s, w1, hh, hk⟩

/-- **The chain.**  `w —head→ w1 —getConstInfo→ w2 —getEnv→ w3 —body→ w4 —finally→ w'`, every step starting where the
previous one ended, the whole being the run `hr`.  Law-free. -/
theorem core_chain {declName : Name} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w') :
    ∃ (s : CoreSaved) (w1 : Void IO.RealWorld) (envR : Environment) (ci : ConstantInfo)
      (w2 w3 w4 : Void IO.RealWorld),
      RunsTo (coreHead declName) mctx mref cctx cref w s w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n) (profLogIO s.profile)
        declName [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref w3 (M, D) w4 ∧
      RunsTo (coreFinally s.depth s.sf s.sw s.sl s.sp s.sc s.ss s.sg) mctx mref cctx cref w4 () w' := by
  obtain ⟨s, w1, hh, hk⟩ := core_split hr
  unfold coreRest at hk
  obtain ⟨w4, u, hx, hfin⟩ := RunsTo.try_finally' hk
  cases u
  obtain ⟨ci, w2, hget, hx⟩ := RunsTo.bind hx
  obtain ⟨envR, w3, henv, hx⟩ := RunsTo.bind hx
  exact ⟨s, w1, envR, ci, w2, w3, w4, hh, hget, henv, hx, hfin⟩

/-! ## The boundary, restated against the linked chain -/

def EntryDefinesRunG (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name) (v : Lean.Expr) : Prop :=
  ∀ (w : Void IO.RealWorld) (s : CoreSaved) (w1 : Void IO.RealWorld) (envR : Environment) (ci : ConstantInfo)
    (w2 w3 w4 w' : Void IO.RealWorld) (M : Sparkle.IR.AST.Module) (D : Design),
    RunsTo (coreHead declName) mctx mref cctx cref w s w1 →
    RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
    RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n) (profLogIO s.profile)
      declName [] false true
      (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
        (userInliner envR) (structEnv envR))
      (Sparkle.Compiler.Elab.instancePredicate envR))
      mctx mref cctx cref w3 (M, D) w4 →
    RunsTo (coreFinally s.depth s.sf s.sw s.sl s.sp s.sc s.ss s.sg) mctx mref cctx cref w4 () w' →
    ∃ d : DefinitionVal,
      entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) = .defnInfo d ∧
        d.value = v

/-- In any contexts (the parent-level form, as `EntryDefinesRuns`). -/
def EntryDefinesRunsG (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)
    (declName : Name) (v : Lean.Expr) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), EntryDefinesRunG mctx mref cctx cref declName v

/-- The all-world `EntryDefines` implies the linked premise (the chain's reads are among its tuples, `w5 := w2`).
(SR2f's `EntryDefinesRun` also implies it, by composing the chain back into a run `hr`; not done here.) -/
theorem EntryDefinesRunG.of_entry {mctx mref cctx cref declName v}
    (h : EntryDefines mctx mref cctx cref declName v) : EntryDefinesRunG mctx mref cctx cref declName v :=
  fun _ _ _ envR ci w2 w3 _ _ _ _ _ hget henv _ _ => h _ ci w2 w2 envR w3 hget henv

theorem EntryDefinesRunsG.of_entry {mctx mref cctx cref declName v}
    (h : EntryDefines mctx mref cctx cref declName v) : EntryDefinesRunsG mref cref declName v :=
  fun _ _ => EntryDefinesRunG.of_entry (Tools.ShippingReflectCtx.EntryDefines.ctx h)

/-- **Coverage, at THIS run.**  For a successful core run `hr : w → w'` the boundary applies at its OWN chain, and
gives (besides the definition) the reads in the shape the consumers use (`synthesizeCombinationalCore_reads`, with
`w5 := w2`, `w6 := w3`). -/
theorem EntryDefinesRunG.at_core {mctx mref cctx cref declName v}
    (h : EntryDefinesRunG mctx mref cctx cref declName v)
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w') :
    ∃ (logProf : String → IO Unit) (envR : Environment) (ci : ConstantInfo)
      (w1 w2 w3 w4 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n) logProf
        declName [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref w3 (M, D) w4 ∧
      ∃ d : DefinitionVal,
        entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) = .defnInfo d ∧
          d.value = v := by
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hget, henv, hbody, hfin⟩ := core_chain hr
  exact ⟨profLogIO s.profile, envR, ci, w1, w2, w3, w4, w2, w3, hget, henv, hbody,
    h w s w1 envR ci w2 w3 w4 w' M D hh hget henv hbody hfin⟩

/-! ## The environment snapshot -/

/-- The environment held by the Core state at world `w`. -/
def envAt (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) : Environment := (readOf cref w).env

/-- `getEnv` returns the environment of the Core state at its start world. -/
theorem getEnv_value {w w' : Void IO.RealWorld} {e : Environment}
    (h : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w e w') : e = envAt cref w := by
  unfold RunsTo at h
  unfold envAt readOf
  have key : (Lean.getEnv : MetaM Environment) mctx mref cctx cref w =
      (match (ST.Ref.get cref : ST IO.RealWorld Core.State) w with
        | .mk v w2 => EST.Out.ok v.env w2) := rfl
  rw [key] at h
  revert h
  cases (ST.Ref.get cref : ST IO.RealWorld Core.State) w
  intro h
  cases h
  rfl

/-- `getConstInfo` returns a constant of the environment at its start world. -/
theorem getConstInfo_value {n : Name} {w w' : Void IO.RealWorld} {ci : ConstantInfo}
    (h : RunsTo (Lean.getConstInfo n : MetaM ConstantInfo) mctx mref cctx cref w ci w') :
    (envAt cref w).find? n = some ci := by
  unfold Lean.getConstInfo at h
  obtain ⟨env, w1, he, hm⟩ := RunsTo.bind h
  rw [← getEnv_value he]
  cases hf : env.find? n with
  | none => rw [hf] at hm; exact (Tools.ShippingReflectCtx.throwUnknownConstant_not_runs n hm).elim
  | some i =>
    rw [hf] at hm
    obtain ⟨hi, -⟩ := Tools.ShippingChildInv.RunsTo.pure_world hm
    rw [hi]

/-- **The snapshot hypothesis (OPEN, a named statement, NOT proved or assumed anywhere).**  The Core state carries
the same environment at the start of the `getConstInfo` read and of the `getEnv` read. -/
def EnvSnapshot (cref : ST.Ref IO.RealWorld Core.State) (w1 w2 : Void IO.RealWorld) : Prop :=
  envAt cref w2 = envAt cref w1

/-- What the snapshot would give: the constant `getConstInfo` read is a constant of the environment `getEnv`
returned, i.e. both reads see ONE environment value. -/
theorem ci_in_envR {n : Name} {w1 w2 w3 : Void IO.RealWorld} {ci : ConstantInfo} {envR : Environment}
    (hget : RunsTo (Lean.getConstInfo n : MetaM ConstantInfo) mctx mref cctx cref w1 ci w2)
    (henv : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3)
    (snap : EnvSnapshot cref w1 w2) : envR.find? n = some ci := by
  rw [getEnv_value henv, snap]
  exact getConstInfo_value hget

section leaves
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The gate's core run, with its ports.** A run of the core entry on a
declaration the unified gate accepts (its value peels to the quote of a
well-formed term; `EntryDefines`: the constant the entry hands on, the
declaration as read or its unfolding) returns a module whose value on admissible inputs is the
term's (`RawValueAt`) and whose input ports are the binder walk's. -/
theorem gate_core_factsG {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, design) w')
    (entry : EntryDefinesRunG mctx mref cctx cref declName value)
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
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run, d, hd, definition⟩ :=
    entry.at_core hr
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
theorem gate_child_fullG {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefinesRunG mctx mref cctx cref declName value)
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
  obtain ⟨ids, cache, nd, len, vals, ins, positive⟩ := gate_core_factsG hcore entry old peel he hb hv
  obtain ⟨hfn, hall, htp⟩ := gate_childFn nd len vals ins positive hF
  exact childFn_post hfn htp hall hpost

set_option maxHeartbeats 1000000 in
/-- **A gate child's full-entry module is combinational, closed and
one-output** — from a run of the full entry and the reflection of the
declaration. -/
theorem gate_child_combG {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefinesRunG mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ChildComb b := by
  obtain ⟨M, D, w1, hcore, hpost⟩ := Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  obtain ⟨logProf, envR, ci, w1', w2, w3, w4, w5, w6, get, henv, run, d, hd, definition⟩ :=
    entry.at_core hcore
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
theorem gate_child_fullFactsG {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefinesRunG mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ChildFull declName bs b design := by
  have hcomb := gate_child_combG hr entry old peel he hb hv
  obtain ⟨M, D, w1, hcore, hpost, hdes⟩ := synthesizeCombinational_parts hr
  obtain ⟨logProf, envR, ci, w1', w2, w3, w4, w5, w6, get, henv, run, d, hd, definition⟩ :=
    entry.at_core hcore
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
theorem childFull_of_realAG {c : Name} {y : Tools.ShippingChildInv.Res}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (entry : EntryDefinesRunsG mref cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (h : Tools.ShippingChildCacheA.RealChildA O c y) : ChildFull c bs y.1 y.2 := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    exact gate_child_fullFactsG hr (entry mctx' cctx') old peel he hb hv

/-- **The boundary for a gate child, run-local.** -/
def GateRunG (c : Name) (v : Lean.Expr) (mc : Sparkle.IR.AST.Module) : Prop :=
  ∃ (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld) (design : Design),
    RunsTo (synthesizeCombinational c) mctx mref cctx cref w (mc, design) w' ∧
    EntryDefinesRunG mctx mref cctx cref c v

theorem childFn_of_gateRunG {c : Name} {v : Lean.Expr} {mc : Sparkle.IR.AST.Module}
    {P : List Nat → Prop} {F : List Nat → Nat}
    (hc : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
      {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w' →
      EntryDefinesRunG mctx mref cctx cref c v → ChildFn b P F)
    (h : GateRunG c v mc) : ChildFn mc P F := by
  obtain ⟨_, _, _, _, _, _, _, hr, entry⟩ := h
  exact hc hr entry

end leaves


end Tools.ShippingEntryReadsLinked
