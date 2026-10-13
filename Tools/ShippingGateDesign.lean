import Tools.ShippingGateChild
import Tools.ShippingCombKidText
import Tools.ShippingMixedForwardSoundness
import Tools.ShippingMachineShipsComb
import Tools.ShippingCombLeafShape

/-! # A GATE-route declaration as an ENTRY at the design level, depth 0 (round par/b-35)

WRITTEN, NOT BUILT.

A declaration the certified unified gate compiles (`rcH`, `pick`, `pickD` in
the tests) was so far used only as a CHILD: `c.gate_child` gives `ChildFn b P
F` for the module `b` of a run of the full entry — ONE evaluation of the
body, on any environment with reset low and in-range argument values — and
`Tools.ShippingCombKidText.gate_child_forwardCheck` gives `forwardCheck b`
(the module's own text). Neither is a statement about a RUN of the shipped
module `checkedOptimize b` nor about `DesignSV`.

This file is the bridge to the depth-0 design-level conclusion:

* `runModule_assigns_total` (pure): an assignment-only body whose every
  seeded evaluation succeeds HAS a run, cycle by cycle (the existing
  `runModule_assigns` transfers a run that is given; here none is given).
* `seedR_arg`, `seedR_rst` (pure): what `seedR` shows on argument ports and
  on `rst`.
* `gate_entry_text` (from the run): `forwardCheck (checkedOptimize b)` and
  `SimpleStmts b.body`, over every run of the full entry on a gate
  declaration. It is `gate_child_forwardCheck`'s proof with
  `Tools.ShippingMixedForwardSoundness.checked_forwardCheck` (the SHIPPED
  module) in place of `post_forwardCheck`.
* `gate_design_of_childFn` (pure): from `ChildFn b P F`, the shipped
  module's forward check and the simple shape — the emitted text of
  `checkedOptimize b` runs from `seedR b ins` for `T` cycles and its one
  output shows `F` of that cycle's argument values.
* `gate_entry_design0` (from the run): the endpoint form
  `#gate_design0` instantiates.

## The statement, and how it differs from `f.machine_design_comb0`

Same: binders the run of `synthesizeCombinational f` and the reflection;
`∃ raw, (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule
raw)) ∧ …`; `DesignSV (childMap design.modules) 0 (checkedOptimize b) (seedR
b ins) T ⟨st0, mems, kids⟩ envs`; "a closed run showing the source exists AND
every closed run shows it"; the two input-width antecedents and the state
bound; no check constant.

Different (stated, not hidden):

1. The reflection is `EntryDefines f f.gateValue` (the gate's), not
   `MachineDefines f f.machineData.shape`.
2. NO `ChildBnd` antecedent. The gate's text facts
   (`checked_forwardCheck`) come from `PrintBaseAt` / `TypedPostReady` of
   the harness's module and need no bound on the name counter. The
   endpoint is therefore STRONGER than the form asked for; a consumer that
   wants the uniform form adds an unused antecedent.
3. The source is stated PER CYCLE on values, not on Signals: the one output
   at list index `j` (cycle `T - 1 - j`: `runModule` lists the latest cycle
   first) is `F` of the argument ports' values of that cycle, where the
   generated `F` is `childValue f.machineSource f.gateBinders i0` — the
   source function at constant inputs, exactly the `F` of `f.gate_child`.
   The antecedent on the inputs is `InRange` of each cycle's argument
   values (the gate's own input condition), in the place of
   `SourceInputs`. NO theorem here says that `f.machineSource` on arbitrary
   input Signals, sampled at cycle `t`, is `childValue` at the values of
   cycle `t` (true for a combinational body; not proved, not used).
4. The output port is `∃ outP, b.outputs = [outP]` (what `ChildFn` gives);
   its name is not stated to be `out`.

SCOPE: ONE declaration as an entry, depth 0, no call, no register, one
output; `DesignSV` of the module list over the returned design's child map —
not the SV string, not `#sim`; seeding `seedR` (`rst` low). -/
namespace Tools.ShippingGateDesign
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

/-! ## Pure: runs of an assignment-only body -/

/-- **An assignment-only body whose seeded evaluations succeed has a run.**
If, for every cycle index `k < N` and every state, the evaluation of `body`
on `seed k st` succeeds with an environment satisfying `R k`, then for every
`T ≤ N` the run of `T` cycles exists, has length `T`, and its element at
list index `j` (cycle `t`, `t + j + 1 = T`: the latest cycle first)
satisfies `R t`. -/
theorem runModule_assigns_total {we : WEnv} {body : List Stmt}
    (hall : body.all Sparkle.IR.RegDedup.isAssign = true)
    {seed : Nat → (String → Nat) → Env} {R : Nat → Env → Prop} {N : Nat}
    (hstep : ∀ (k : Nat) (st : String → Nat) (mems : MEnv), k < N →
      ∃ e, evalAssigns we mems body (seed k st) = some e ∧ R k e) :
    ∀ (T : Nat) (st : String → Nat) (mems : MEnv), T ≤ N →
      ∃ envs, runModule we body seed T st mems = some envs ∧ envs.length = T ∧
        ∀ (j : Nat) (hj : j < envs.length) (t : Nat), t + j + 1 = T → R t (envs[j]'hj) := by
  intro T
  induction T with
  | zero =>
    intro st mems _
    exact ⟨[], by simp [runModule], rfl, fun j hj => absurd hj (by simp)⟩
  | succ k ih =>
    intro st mems hT
    obtain ⟨e, he, hR⟩ := hstep k st mems (by omega)
    obtain ⟨rest, hr, hl, hc⟩ := ih st mems (by omega)
    refine ⟨e :: rest, ?_, by simp [hl], ?_⟩
    · simp only [runModule, stepModule]
      simp only [he, Tools.ShippingMachineShipsComb.regNexts_assigns hall,
        Tools.ShippingMachineShipsComb.memNexts_assigns hall, Option.bind_eq_bind,
        Option.bind_some, Tools.ShippingMachineShipsComb.applyNexts_nil]
      simp [hr]
    · intro j hj t ht
      cases j with
      | zero =>
        have e1 : t = k := by omega
        subst e1
        exact hR
      | succ j => exact hc j (by simpa using hj) t (by omega)

/-- `seedR` shows the input stream on an argument port. -/
theorem seedR_arg {b : Sparkle.IR.AST.Module} {ins : Nat → String → Nat} {k : Nat}
    {st : String → Nat} {p : Port} (hp : p ∈ argPorts b) :
    seedR b ins k st p.name = ins k p.name := by
  unfold argPorts at hp
  obtain ⟨hin, hne⟩ := List.mem_filter.mp hp
  have hr : ¬ p.name = "rst" := by
    intro h
    simp [h] at hne
  have hmem : p.name ∈ b.inputs.map (·.name) := List.mem_map.mpr ⟨p, hin, rfl⟩
  have hc : (b.inputs.map (·.name)).contains p.name = true := by
    first
      | exact List.contains_iff_mem.mpr hmem
      | simpa [List.contains_eq_mem] using hmem
      | simpa using hmem
  show (if p.name = "rst" then 0
    else if (b.inputs.map (·.name)).contains p.name then ins k p.name else st p.name) =
      ins k p.name
  rw [if_neg hr, if_pos hc]

/-- `seedR` holds the reset low. -/
theorem seedR_rst (b : Sparkle.IR.AST.Module) (ins : Nat → String → Nat) (k : Nat)
    (st : String → Nat) : seedR b ins k st "rst" = 0 := by
  show (if "rst" = "rst" then 0
    else if (b.inputs.map (·.name)).contains "rst" then ins k "rst" else st "rst") = 0
  rw [if_pos rfl]

/-- The argument values `seedR` shows at cycle `k` are the input stream's. -/
theorem seedR_args (b : Sparkle.IR.AST.Module) (ins : Nat → String → Nat) (k : Nat)
    (st : String → Nat) :
    (argPorts b).map (fun p => seedR b ins k st p.name) =
      (argPorts b).map (fun p => ins k p.name) := by
  apply List.map_congr_left
  intro p hp
  exact seedR_arg hp

/-! ## Pure: from one evaluation to the emitted text's run -/

/-- **A one-output assignment module that computes `F` at every evaluation,
as the run of its shipped text.** From `ChildFn b P F` (one evaluation, reset
low, argument values in `P`), the forward check of the SHIPPED module
`checkedOptimize b` and the simple shape of `b`: for every input stream
whose argument values are in `P` at each of `T` cycles (and fit the declared
and the emitted widths), the emitted text of `checkedOptimize b` runs from
`seedR b ins`, and the one output shows `F` of each cycle's argument
values. -/
theorem gate_design_of_childFn {b : Sparkle.IR.AST.Module} {P : List Nat → Prop}
    {F : List Nat → Nat}
    (hfn : ChildFn b P F)
    (hfc : Tools.ShippingSVBridge.forwardCheck (Sparkle.IR.OptCheck.checkedOptimize b) = true)
    (hs : Tools.ShippingPostSoundness.SimpleStmts b.body) :
    ∃ outP : Port, b.outputs = [outP] ∧
      ∀ (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv),
        (∀ t, t < T → P ((argPorts b).map fun p => ins t p.name)) →
        (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Sparkle.IR.RegDedup.declWidth b x) →
        (∀ t x, x ∈ b.inputs.map (·.name) →
          ins t x < 2 ^ Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b) x) →
        Bounded (Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b)) st0 →
        ∃ envsO,
          Tools.ShippingDesignSV.TextRun (Sparkle.IR.OptCheck.checkedOptimize b) (seedR b ins) T
            st0 mems envsO ∧
          envsO.length = T ∧
          ∀ (j : Nat) (hj : j < envsO.length),
            (envsO[j]'hj) outP.name = F ((argPorts b).map fun p => ins (T - 1 - j) p.name) := by
  obtain ⟨outP, houts, hf⟩ := hfn
  refine ⟨outP, houts, ?_⟩
  intro T ins st0 mems hP hinsB hinsW hst
  have hsB : Sparkle.IR.OptCheck.simpleBody b = true :=
    Tools.ShippingPostSoundness.simpleBody_of b hs
  have hallB : b.body.all Sparkle.IR.RegDedup.isAssign = true :=
    Tools.ShippingMachineShipsComb.simpleBody_assigns hsB
  have hallO : (Sparkle.IR.OptCheck.checkedOptimize b).body.all Sparkle.IR.RegDedup.isAssign =
      true := Tools.ShippingMachineShipsComb.checkedOptimize_assigns hsB
  obtain ⟨_, c2, c3⟩ := Tools.ShippingCombKidText.forwardCheck_text hfc
  -- every cycle's evaluation of `b`: `ChildFn` on the seeded environment
  have hstep : ∀ (k : Nat) (st : String → Nat) (mems' : MEnv), k < T →
      ∃ e, evalAssigns (Sparkle.IR.RegDedup.declWidth b) mems' b.body (seedR b ins k st) =
          some e ∧
        e outP.name = F ((argPorts b).map fun p => ins k p.name) := by
    intro k st mems' hk
    have hargs := seedR_args b ins k st
    obtain ⟨cres, hev, hc⟩ := hf mems' (seedR b ins k st) (seedR_rst b ins k st)
      (Eq.mpr (congrArg P hargs) (hP k hk))
    exact ⟨cres, hev, hc.trans (congrArg F hargs)⟩
  obtain ⟨envsB, hrunB, hlB, hRB⟩ := runModule_assigns_total hallB (seed := seedR b ins)
    (R := fun k e => e outP.name = F ((argPorts b).map fun p => ins k p.name))
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
  have hon : outP.name ∈ b.outputs.map (·.name) := by
    rw [houts]
    simp
  rw [hcO j hj (by omega) outP.name hon]
  exact hRB j (by omega) (T - 1 - j) (by omega)

/-! ## From the run of the full entry -/

/-- **The shipped module of a gate declaration passes the forward check, and
the entry's module is of the simple shape** — over every run of the full
entry, from the declaration's reflection. The proof of
`Tools.ShippingCombKidText.gate_child_forwardCheck` with the theorem about
the SHIPPED module (`checked_forwardCheck`: the optimizer's output is kept
only behind its own guard). No check constant is a premise. -/
theorem gate_entry_text {declName : Name} {mctx : Meta.Context}
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
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    Tools.ShippingSVBridge.forwardCheck (Sparkle.IR.OptCheck.checkedOptimize b) = true ∧
      Tools.ShippingPostSoundness.SimpleStmts b.body := by
  obtain ⟨M, D, w1, hcore, hpost⟩ := Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  obtain ⟨ids, cache, nd, len, vals, ins, positive⟩ :=
    Tools.ShippingGateChild.gate_core_facts hcore entry old peel he hb hv
  -- the facts that do not depend on the inputs, at the all-zero environment
  obtain ⟨_, _, _, tpr, simple, _, _, _, pb⟩ := vals (fun _ => false) (fun _ n => 0#n)
    (fun _ => 0) (fun _ _ => 0) (Tools.ShippingGateChild.admissible_zero _ _)
  have pb := pb positive
  have hall : M.body.all Sparkle.IR.RegDedup.isAssign = true := by
    rw [List.all_eq_true]
    intro st hs
    obtain ⟨l, r, rfl, _⟩ := simple st hs
    rfl
  obtain ⟨dzb, _, _, _, _⟩ := Tools.ShippingTypedPostSoundness.dropZeroWidth_typed tpr
  have hZa : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body.all
      Sparkle.IR.RegDedup.isAssign = true := by
    rw [dzb]
    exact hall
  have post' : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = Sparkle.IR.RegDedup.mergeDuplicates (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) := by
    rcases hpost with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans (Tools.ShippingCombKidText.mergeChecked_assign hZa))
  refine ⟨Tools.ShippingMixedForwardSoundness.checked_forwardCheck pb tpr simple post', ?_⟩
  have hd : Tools.ShippingPostSoundness.SimpleStmts
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body := by
    rw [dzb]
    exact simple
  rcases post' with h | h
  · rw [h]
    exact hd
  · rw [h]
    exact Tools.ShippingPostSoundness.mergeDuplicates_simple _ hd

/-- **A gate-route declaration as an entry at the design level, depth 0.**
Binders: the run of the full entry and the reflection (`EntryDefines`); the
gate's reading of the value (`old`, `peel`, `he`, `hb`, `hv`, `hF` — what
`#gate_child` generates per declaration: kernel `rfl` / `decide` on the
reflected value, conditions and not reductions of the module). Conclusion:
the returned module is the cleaned core module or its checked merge; it has
ONE output port; and for every input stream whose argument values are in
range at each of `T` cycles, a closed run `DesignSV (childMap design.modules)
0 (checkedOptimize b)` from `seedR b ins` exists and shows `F` of each
cycle's argument values on that port, and EVERY such closed run shows it.
No `ChildBnd`, no check constant. This is the term `#gate_design0`
instantiates (file header for the differences from `machine_design_comb0`). -/
theorem gate_entry_design0 {declName : Name} {mctx : Meta.Context}
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
    {F : List Nat → Nat}
    (hF : ∀ vs, InRange vs (bs.filter fun b => b.2 != .domain) →
      F vs = (pack srt (eval (fun j => decB bs vs (bpos j)) (fun j w => decV bs vs (vpos j) w) e)).toNat) :
    ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∃ outP : Port, b.outputs = [outP] ∧
        ∀ (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
          (kids : String → Tools.ShippingHierStateG.KT 0),
          -- each cycle's argument values are in range of the binders' types
          (∀ t, t < T → InRange ((argPorts b).map fun p => ins t p.name)
            (bs.filter fun b => b.2 != .domain)) →
          -- the inputs within the declared and the emitted widths; the state within the emitted
          (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Sparkle.IR.RegDedup.declWidth b x) →
          (∀ t x, x ∈ b.inputs.map (·.name) →
            ins t x < 2 ^ Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b) x) →
          Bounded (Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b)) st0 →
          -- a closed run of the emitted text showing the source function exists ...
          (∃ envsO,
            Tools.ShippingDesignSV.DesignSV (Tools.ShippingMachineLinked.childMap design.modules)
              0 (Sparkle.IR.OptCheck.checkedOptimize b) (seedR b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) outP.name = F ((argPorts b).map fun p => ins (T - 1 - j) p.name))
          -- ... and EVERY closed run from the same seeding and states shows it
          ∧ ∀ envs', Tools.ShippingDesignSV.DesignSV
                (Tools.ShippingMachineLinked.childMap design.modules)
                0 (Sparkle.IR.OptCheck.checkedOptimize b) (seedR b ins) T ⟨st0, mems, kids⟩ envs' →
              envs'.length = T ∧
              ∀ (j : Nat) (hj : j < envs'.length),
                (envs'[j]'hj) outP.name =
                  F ((argPorts b).map fun p => ins (T - 1 - j) p.name) := by
  obtain ⟨M, D, w1, hcore, hpost⟩ := Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  have hfn := Tools.ShippingGateChild.gate_child_full hr entry old peel he hb hv hF
  obtain ⟨hfc, hs⟩ := gate_entry_text hr entry old peel he hb hv
  obtain ⟨outP, houts, G⟩ := gate_design_of_childFn hfn hfc hs
  refine ⟨M, hpost, outP, houts, ?_⟩
  intro T ins st0 mems kids hP hinsB hinsW hst
  obtain ⟨envsO, htext, hlen, hobs⟩ := G T ins st0 mems hP hinsB hinsW hst
  have hsq : (Sparkle.IR.OptCheck.checkedOptimize b).body.all Sparkle.IR.OptCheck.seqStmtOk =
      true :=
    Tools.ShippingMachineShipsComb.assigns_seqOk
      (Tools.ShippingMachineShipsComb.checkedOptimize_assigns
        (Tools.ShippingPostSoundness.simpleBody_of b hs))
  refine ⟨⟨envsO, Tools.ShippingLeafEntry.designSV0_of_leaf
    (Tools.ShippingMachineLinked.childMap design.modules) hsq (s := ⟨st0, mems, kids⟩) htext,
    hlen, hobs⟩, ?_⟩
  intro envs' hD'
  have e1 := Tools.ShippingLeafDesign.designSV0_leaf_unique
    (Tools.ShippingMachineLinked.childMap design.modules) hsq htext hD'
  subst e1
  exact ⟨hlen, hobs⟩

end Tools.ShippingGateDesign
