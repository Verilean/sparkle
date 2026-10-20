import Tools.ShippingGateDesign

/-! # The SOURCE side of a gate-route entry: the Signal-level form (round par/b-36)

WRITTEN, NOT BUILT.

`f.gate_design0` (`Tools/ShippingGateDesign.lean`, BUILT at 0a0a4f71) states
the source PER CYCLE ON VALUES: the output is `childValue f.machineSource
f.gateBinders i0` of the cycle's argument values, under `InRange`. The
machine-route leaves (`f.machine_design_comb0`) state it on SIGNALS: under
`SourceInputs … (fun j => (bools j).val (T-1-t)) … (seedR b ins t st)`, the
output at list index `j` is `f j` for the observation `f` of `src i bools
bits`.

This file gives the gate entry the Signal-level form. It does NOT go through
`childValue`: the gate's harness theorem
(`Tools.ShippingGateChild.gate_core_facts`) is already stated under
`SourceInputs` with arbitrary Bool / BitVec values — one evaluation of the
core module on an environment admissible for `bools`, `bits` gives the
term's value `pack srt (eval (fun j => bools (bpos j)) (fun j w => bits
(vpos j) w) e)`. Instantiated at the values of the input Signals at one time
this is the Signal-level statement about the TERM. What connects the term
to the source function is one equation per declaration,

    hsrc : ∀ i bools bits t,
      (src i bools bits).map (fun g => g t) =
        [(pack srt (eval (fun j => (bools (bpos j)).val t)
                         (fun j w => (bits (vpos j) w).val t) e)).toNat]

"the source's observation at time `t` is the term's value on the inputs'
values at time `t`" — the pointwise-ness of a combinational declaration,
in the form the machine route's own `f.machine_result` has (`hres` of
`Tools.ShippingMachineLoop.machine_trace_of_comb`: a kernel `rfl` against
the declaration). It is a HYPOTHESIS of the general theorem here and a
generated, kernel-checked theorem `f.gate_pointwise` per declaration
(`Tools/ShippingGateSourceCommand.lean`). It is a statement about the
source function and the reflected term only — nothing about a module or a
run, no check.

* `singleton_get` (pure).
* `post_eval` (pure): the full entry's post-processing keeps every
  evaluation of a typed assignment-only module, and its ports.
* `text_run_of_steps` (pure): `gate_design_of_childFn`'s proof with the
  per-cycle evaluation as a hypothesis (any named output, any per-time
  value `G`), instead of `ChildFn`.
* `gate_entry_design0S` (from the run): the endpoint form
  `#gate_design0S` instantiates.

## The statement against `f.machine_design_comb0`

Same shape: `∃ raw, (b = dz raw ∨ b = mergeChecked (dz raw)) ∧ … ∃ ids,
ids.Nodup ∧ ids.length = … ∧ ∃ cache, ∀ i bools bits T ins st0 mems kids,
(SourceInputs at every cycle) → (two width bounds) → Bounded … → (∃ envsO,
DesignSV (childMap design.modules) 0 (checkedOptimize b) (seedR b ins) T
⟨st0, mems, kids⟩ envsO ∧ envsO.length = T ∧ source) ∧ ∀ envs', DesignSV …
envs' → …`, the source clause on `(src i bools bits)[k]? = some f`.

What still differs:
1. the reflection binder is `EntryDefines` (the gate's);
2. no `ChildBnd` antecedent (not needed);
3. the binders are the gate's (`bs`, generated: `f.gateBinders`) where the
   machine form has `d.shape.binders` / `d.bsIn` (`f.gate_binders` says
   `f.machineData.bsIn = f.gateBinders`);
4. the output port is the literal `"out"` (derived: `RawValueAt` evaluates
   `out`, and it is an output port of the returned module — used inside the
   proof), where the machine form reads `q.name` off
   `d.shape.layout.outs[k]?`. The clause is `∀ k f, (src i bools bits)[k]? =
   some f → envs[j] "out" = f j`; by `hsrc` the source list has exactly one
   observation, so only `k = 0` is inhabited.
-/
namespace Tools.ShippingGateSource
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineCompose
open Tools.ShippingMachineChild
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedExecutionSoundness
open Tools.ShippingUnifiedMeaning (pack)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingMachineShipsComb (seedR)
open Tools.ShippingGateDesign (runModule_assigns_total)

/-! ## Pure -/

/-- An index into a one-element list reads that element. -/
theorem singleton_get {α : Type} {x y : α} : ∀ {k : Nat}, [x][k]? = some y → x = y
  | 0, h => by simpa using h
  | k + 1, h => by simp at h

/-- **The full entry's post-processing keeps every evaluation of a typed
assignment-only module**, and its ports: the zero-width cleanup changes
nothing of a typed module, the checked merge of an assignment-only body is
`mergeDuplicates` (the same environment). -/
theorem post_eval {M b : Sparkle.IR.AST.Module}
    (tpr : Tools.ShippingTypedPostSoundness.TypedPostReady M)
    (hall : M.body.all Sparkle.IR.RegDedup.isAssign = true)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) :
    b.inputs = M.inputs ∧ b.outputs = M.outputs ∧
      ∀ (mems : MEnv) (init e : Env),
        evalAssigns (Tools.ShippingEntrySoundness.weOf M) mems M.body init = some e →
        evalAssigns (Tools.ShippingEntrySoundness.weOf b) mems b.body init = some e := by
  obtain ⟨hb, hw, hi, ho, _⟩ := Tools.ShippingTypedPostSoundness.dropZeroWidth_typed tpr
  have hall0 : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body.all
      Sparkle.IR.RegDedup.isAssign = true := by
    rw [hb]
    exact hall
  have h0 : ∀ (mems : MEnv) (init e : Env),
      evalAssigns (Tools.ShippingEntrySoundness.weOf M) mems M.body init = some e →
      evalAssigns (Tools.ShippingEntrySoundness.weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
        mems (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body init = some e := by
    intro mems init e h
    rw [hw, hb]
    exact h
  rcases hpost with h | h
  · rw [h]
    exact ⟨hi, ho, h0⟩
  · rw [h, Tools.ShippingCombKidText.mergeChecked_assign hall0]
    obtain ⟨hpi, hpo, _⟩ := Sparkle.IR.RegDedup.mergeDuplicates_ports
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)
    exact ⟨hpi.trans hi, hpo.trans ho, fun mems init e h1 =>
      (Tools.ShippingPostSoundness.mergeDuplicates_sound
        (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) mems init e hall0 (h0 mems init e h1)).1⟩

/-- **A simple assignment module whose every seeded evaluation shows `G` on
one output, as the run of its shipped text.** `hstep`: at seeding index `k`
(signal time `s`, `s + k + 1 = T`) the evaluation of `b` succeeds and shows
`G s` on `outName`. Then the emitted text of `checkedOptimize b` runs from
`seedR b ins` and its element at list index `j` shows `G j`. The proof is
`Tools.ShippingGateDesign.gate_design_of_childFn`'s, with the evaluations
given instead of read off `ChildFn`. -/
theorem text_run_of_steps {b : Sparkle.IR.AST.Module} {outName : String}
    (hout : outName ∈ b.outputs.map (·.name))
    (hfc : Tools.ShippingSVBridge.forwardCheck (Sparkle.IR.OptCheck.checkedOptimize b) = true)
    (hs : Tools.ShippingPostSoundness.SimpleStmts b.body)
    {T : Nat} {ins : Nat → String → Nat} {G : Nat → Nat}
    (hstep : ∀ (k : Nat) (st : String → Nat) (mems' : MEnv), k < T →
      ∃ e, evalAssigns (Sparkle.IR.RegDedup.declWidth b) mems' b.body (seedR b ins k st) =
          some e ∧
        ∀ s, s + k + 1 = T → e outName = G s)
    (st0 : String → Nat) (mems : MEnv)
    (hinsB : ∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Sparkle.IR.RegDedup.declWidth b x)
    (hinsW : ∀ t x, x ∈ b.inputs.map (·.name) →
      ins t x < 2 ^ Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b) x)
    (hst : Bounded (Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b)) st0) :
    ∃ envsO,
      Tools.ShippingDesignSV.TextRun (Sparkle.IR.OptCheck.checkedOptimize b) (seedR b ins) T
        st0 mems envsO ∧
      envsO.length = T ∧
      ∀ (j : Nat) (hj : j < envsO.length), (envsO[j]'hj) outName = G j := by
  have hsB : Sparkle.IR.OptCheck.simpleBody b = true :=
    Tools.ShippingPostSoundness.simpleBody_of b hs
  have hallB : b.body.all Sparkle.IR.RegDedup.isAssign = true :=
    Tools.ShippingMachineShipsComb.simpleBody_assigns hsB
  have hallO : (Sparkle.IR.OptCheck.checkedOptimize b).body.all Sparkle.IR.RegDedup.isAssign =
      true := Tools.ShippingMachineShipsComb.checkedOptimize_assigns hsB
  obtain ⟨_, c2, c3⟩ := Tools.ShippingCombKidText.forwardCheck_text hfc
  obtain ⟨envsB, hrunB, hlB, hRB⟩ := runModule_assigns_total hallB (seed := seedR b ins)
    (R := fun k e => ∀ s, s + k + 1 = T → e outName = G s)
    hstep T st0 mems (Nat.le_refl T)
  -- the optimizer: the same outputs
  have hQ : ∀ k st, ∀ x ∈ b.inputs.map (·.name),
      seedR b ins k st x < 2 ^ Sparkle.IR.RegDedup.declWidth b x := by
    intro k st x hx
    simp only [seedR]
    split
    · exact Nat.two_pow_pos _
    · split
      · exact hinsB k x hx
      · rename_i _ hc
        exact absurd (by simpa [List.contains_eq_mem] using hx) hc
  obtain ⟨envsO, hrunO, hlO, hcO⟩ := Tools.ShippingMachineShipsComb.runModule_assigns
    (we₁ := Sparkle.IR.RegDedup.declWidth b)
    (we₂ := Sparkle.IR.RegDedup.declWidth (Sparkle.IR.OptCheck.checkedOptimize b)) hallB hallO
    (P := fun x => x ∈ b.outputs.map (·.name))
    (fun init => ∀ x ∈ b.inputs.map (·.name), init x < 2 ^ Sparkle.IR.RegDedup.declWidth b x) hQ
    (fun mems init e hq h => by
      obtain ⟨envO, hevO, heq, _, _⟩ := Tools.ShippingOptSoundness.checkedOptimize_sound hsB hq h
      refine ⟨envO, hevO, fun x hx => ?_⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact heq p hp) T st0 mems envsB hrunB
  -- the emitted text
  have hwag' : ∀ n ∈ Tools.ShippingSeqSVSoundness.seqNames
        (Sparkle.IR.OptCheck.checkedOptimize b).body,
      Sparkle.IR.RegDedup.declWidth (Sparkle.IR.OptCheck.checkedOptimize b) n =
        Tools.SVParser.EmitSem.weOf
          (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b)) n := by
    intro n hn
    have := List.all_eq_true.mp c3 n hn
    simpa using this
  have c2' : Tools.SVParser.EmitSem.seqCheck
      (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b))
      (Tools.SVParser.EmitSem.weOf
        (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b)))
      (Sparkle.IR.OptCheck.checkedOptimize b).body = true := c2
  have hSV := Tools.ShippingSeqSVSoundness.seq_run_to_sv
    (wof := Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b))
    (Tools.ShippingMachineShipsComb.assigns_seqOk hallO) c2' hwag' (seedR b ins)
    (Tools.ShippingMachineShipsComb.seedR_bounded hinsW) hst hrunO
  have htext : Tools.ShippingDesignSV.TextRun (Sparkle.IR.OptCheck.checkedOptimize b)
      (seedR b ins) T st0 mems envsO := hSV
  refine ⟨envsO, htext, by omega, ?_⟩
  intro j hj
  have hjB : j < envsB.length := by omega
  have h2 : ∀ s, s + (T - 1 - j) + 1 = T → (envsB[j]'hjB) outName = G s :=
    hRB j hjB (T - 1 - j) (by omega)
  rw [hcO j hj hjB outName hout]
  exact h2 j (by omega)

/-! ## From the run of the full entry -/

/-- **A gate-route declaration as an entry at the design level, depth 0,
with the source on Signals.** Binders: the run of the full entry, the
reflection (`EntryDefines`), the gate's reading of the value (as
`gate_child_full`), and `hsrc`: the source's one observation at time `t` is
the term's value on the inputs' values at time `t` (per declaration a
kernel `rfl`, `f.gate_pointwise`). Conclusion: the form of
`machine_design_comb0` — for input Signals whose values the seeding shows at
every cycle (`SourceInputs`), a closed run `DesignSV (childMap
design.modules) 0 (checkedOptimize b)` from `seedR b ins` exists and shows
every observation of `src i bools bits` on the port `out`, and EVERY such
closed run shows it. No `ChildBnd`, no check constant. -/
theorem gate_entry_design0S {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    {ι : Type} {sdom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (sdom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (sdom i) (BitVec n)) → List (Nat → Nat)}
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (sdom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (sdom i) (BitVec n)) (t : Nat),
      (src i bools bits).map (fun g => g t) =
        [(pack srt (eval (fun j => (bools (bpos j)).val t)
          (fun j w => (bits (vpos j) w).val t) e)).toNat]) :
    ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
      ∃ cache : IO.Ref (ExprStructMap String),
        ∀ (i : ι) (bools : Nat → Signal (sdom i) Bool)
          (bits : (j : Nat) → (n : Nat) → Signal (sdom i) (BitVec n))
          (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
          (kids : String → Tools.ShippingHierStateG.KT 0),
          -- the source's inputs are the seeding's (`rst` low)
          (∀ t st, t < T → SourceInputs declName bs ids cache
            (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
            (seedR b ins t st)) →
          -- the inputs within the declared and the emitted widths; the state within the emitted
          (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Sparkle.IR.RegDedup.declWidth b x) →
          (∀ t x, x ∈ b.inputs.map (·.name) →
            ins t x < 2 ^ Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b) x) →
          Bounded (Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b)) st0 →
          -- a closed run of the emitted text showing the source exists ...
          (∃ envsO,
            Tools.ShippingDesignSV.DesignSV (Tools.ShippingMachineLinked.childMap design.modules)
              0 (Sparkle.IR.OptCheck.checkedOptimize b) (seedR b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length) (k : Nat) (f : Nat → Nat),
              (src i bools bits)[k]? = some f → (envsO[j]'hj) "out" = f j)
          -- ... and EVERY closed run from the same seeding and states shows it
          ∧ ∀ envs', Tools.ShippingDesignSV.DesignSV
                (Tools.ShippingMachineLinked.childMap design.modules)
                0 (Sparkle.IR.OptCheck.checkedOptimize b) (seedR b ins) T ⟨st0, mems, kids⟩ envs' →
              envs'.length = T ∧
              ∀ (j : Nat) (hj : j < envs'.length) (k : Nat) (f : Nat → Nat),
                (src i bools bits)[k]? = some f → (envs'[j]'hj) "out" = f j := by
  obtain ⟨M, D, w1, hcore, hpost⟩ := Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  obtain ⟨ids, cache, nd, len, vals, insP, positive⟩ :=
    Tools.ShippingGateChild.gate_core_facts hcore entry old peel he hb hv
  obtain ⟨hfc, hs⟩ := Tools.ShippingGateDesign.gate_entry_text hr entry old peel he hb hv
  -- the facts that do not depend on the inputs, at the all-zero environment
  obtain ⟨_, _, _, tpr, simple, _, hout0, _, _⟩ := vals (fun _ => false) (fun _ n => 0#n)
    (fun _ => 0) (fun _ _ => 0) (Tools.ShippingGateChild.admissible_zero _ _)
  have hall : M.body.all Sparkle.IR.RegDedup.isAssign = true := by
    rw [List.all_eq_true]
    intro st hst
    obtain ⟨l, r, rfl, _⟩ := simple st hst
    rfl
  obtain ⟨_, hbo, hev⟩ := post_eval tpr hall hpost
  have hout : "out" ∈ b.outputs.map (·.name) := by
    rw [hbo]
    exact hout0
  have hdw : Sparkle.IR.RegDedup.declWidth b = Tools.ShippingEntrySoundness.weOf b := rfl
  have hsq : (Sparkle.IR.OptCheck.checkedOptimize b).body.all Sparkle.IR.OptCheck.seqStmtOk =
      true :=
    Tools.ShippingMachineShipsComb.assigns_seqOk
      (Tools.ShippingMachineShipsComb.checkedOptimize_assigns
        (Tools.ShippingPostSoundness.simpleBody_of b hs))
  refine ⟨M, hpost, ids, nd, len, cache, ?_⟩
  intro i bools bits T ins st0 mems kids hsi hinsB hinsW hst
  -- every cycle's evaluation of `b`: the harness's theorem at the Signals'
  -- values of that cycle, through the post-processing
  have hstep : ∀ (k : Nat) (st : String → Nat) (mems' : MEnv), k < T →
      ∃ e', evalAssigns (Sparkle.IR.RegDedup.declWidth b) mems' b.body (seedR b ins k st) =
          some e' ∧
        ∀ s, s + k + 1 = T → e' "out" =
          (pack srt (eval (fun q => (bools (bpos q)).val s)
            (fun q w => (bits (vpos q) w).val s) e)).toNat := by
    intro k st mems' hk
    obtain ⟨result, hevM, hres, _, _, hwe, _, _, _⟩ :=
      vals _ _ (seedR b ins k st) mems' (hsi k st hk)
    rw [← hwe] at hevM
    refine ⟨result, ?_, ?_⟩
    · rw [hdw]
      exact hev mems' _ result hevM
    · intro s hs'
      have e1 : T - 1 - k = s := by omega
      subst e1
      exact hres
  obtain ⟨envsO, htext, hlen, hobs⟩ := text_run_of_steps hout hfc hs
    (G := fun s => (pack srt (eval (fun q => (bools (bpos q)).val s)
      (fun q w => (bits (vpos q) w).val s) e)).toNat)
    hstep st0 mems hinsB hinsW hst
  -- the term's value at time `j` is the source's observation at `j`
  have hobs' : ∀ (j : Nat) (hj : j < envsO.length) (k : Nat) (f : Nat → Nat),
      (src i bools bits)[k]? = some f → (envsO[j]'hj) "out" = f j := by
    intro j hj k f hf
    have h1 : ((src i bools bits).map (fun g => g j))[k]? = some (f j) := by
      first
        | (rw [List.getElem?_map, hf]; rfl)
        | rw [List.getElem?_map, hf]
        | simp [hf]
    rw [hsrc i bools bits j] at h1
    exact (hobs j hj).trans (singleton_get h1)
  refine ⟨⟨envsO, Tools.ShippingLeafEntry.designSV0_of_leaf
    (Tools.ShippingMachineLinked.childMap design.modules) hsq (s := ⟨st0, mems, kids⟩) htext,
    hlen, hobs'⟩, ?_⟩
  intro envs' hD'
  have e2 := Tools.ShippingLeafDesign.designSV0_leaf_unique
    (Tools.ShippingMachineLinked.childMap design.modules) hsq htext hD'
  subst e2
  exact ⟨hlen, hobs'⟩

end Tools.ShippingGateSource
