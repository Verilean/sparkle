import Tools.ShippingGateChildComb
import Tools.ShippingPostSoundness

variable {tenv : Lean.Environment}

/-! # A FIRST-gate child at the full entry (worker N, round 5)

WRITTEN, NOT BUILT.

A declaration the FIRST gate accepts (`certifiedShape?`: a uniform-width
fragment declaration `quoteDecl dn names n fe`) goes through
`synthesizeCertified`, not `synthesizeMixedCertified`. The built child facts
(`gate_child_fullFacts`, `gate_core_facts`, `gate_childFn`) are for the mixed
gate (`old : certifiedShape? … = none` is one of their premises). This file
gives the same facts for a first-gate child, with NO compiler change:

* **The bridge** (`bindCertified_mixed`): `bindCertifiedInputs k (bs.zip ids)`
  IS `bindMixedCertifiedInputs k ((bs.map mixB).zip ids)` (`mixB` sends
  `.signal n` to `.bits n`), and `synthesizeCertified` is otherwise the
  mixed harness verbatim (same fresh ids, cache, `emitLeaves`, translator,
  `finishSynth`). So a first-gate core run IS a run of the mixed harness on
  the binders `firstBs dn names n` and the body `quoteBody names.length n fe`
  — which is `quote` of the unified term `ofF n fe` (`first_body`).
  Every built harness theorem (`transition_closed`, `transition_facts`)
  applies to it.
* `fragmentDecl_of_entry` / `synthesizeCombinational_fragment_entry`:
  `fragmentDecl_of_env` / `synthesizeCombinational_fragment` with
  `EnvDefines` replaced by `EntryDefines` (ALLOWED).
* `first_core_postReady`, `first_full_outputs`: `PostReady M n`, and the full
  entry's `outputs = [out : bitVector n]`.
* **(c), the design frame** (`first_core_design`, `ChildFull.design`): the
  first-gate translation of a fragment body leaves `st.design` the initial
  one (the harness spine's `Ext` via `transition_closed`), so the core's
  design and the full entry's design have no module.
* `first_child_fullFacts`: `ChildFull` (combinational, closed, one output
  `out`, distinct allocated input names — so none is `clk`/`rst`/`out` —
  port types, name, empty design) from ONE run + `EntryDefines`.
* `ChildFnR` / `first_child_fnR`: what the full-entry module computes on its
  argument ports, for EVERY environment (no `rst` premise: `ChildFn` without
  its unused `env "rst" = 0`; the proofs are the built ones' with that binder
  dropped), with the function `firstFn` = `evalFE` of the decoded ports
  (`firstFn_eval`). -/
namespace Tools.ShippingFirstGateChild
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.Builder
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineCompose
open Tools.ShippingMachineChild
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingEntrySoundness (RunsTo EnvDefines synthesizeCombinationalCore_reads MReturns
  FExpr evalFE quoteF quoteBody quoteDecl quoteBinders PostReady denoteFE denoteFE_val
  outcome_quote synthesizeFromConst_sound certifiedShape_quote quoteF_congr finishSynth_returns
  CertifiedOutcome)
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedExecutionSoundness
open Tools.ShippingUnifiedMeaning (pack)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingTransitionClosed Tools.ShippingMergeClosed
open Tools.ShippingGateChildComb
open Tools.ShippingSettledSoundness (Acyclic)
open Sparkle.IR.NameHints (Allocated)
open Sparkle.IR.Reorder

set_option linter.unusedSectionVars false

/-! ## 1. The bridge: the first gate's binder walk is the mixed one -/

/-- A first-gate binder as a mixed-gate binder. -/
def mixB : Name × GateBinder → Name × MixedGateBinder
  | (nm, .domain) => (nm, .domain)
  | (nm, .signal n) => (nm, .bits n)

/-- **The first gate's binder walk IS the mixed gate's** on the translated
binders (both bind a `.signal n` / `.bits n` binder with `bindInputPort … (.bitVector n)`,
both skip the domain). -/
theorem bindCertified_mixed {α : Type} (k : CompilerM α) :
    ∀ (bs : List (Name × GateBinder)) (ids : List FVarId),
      bindCertifiedInputs k (bs.zip ids) = bindMixedCertifiedInputs k ((bs.map mixB).zip ids)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | (_, .domain) :: bs, _ :: ids => by
    simp only [List.zip_cons_cons, List.map_cons, mixB, bindCertifiedInputs,
      bindMixedCertifiedInputs]
    exact bindCertified_mixed k bs ids
  | (_, .signal _) :: bs, _ :: ids => by
    simp only [List.zip_cons_cons, List.map_cons, mixB, bindCertifiedInputs,
      bindMixedCertifiedInputs]
    rw [bindCertified_mixed k bs ids]

/-- The first gate's entry: a run of `synthesizeFromConst` on a constant the
first gate accepts is a run of `synthesizeCertified`. -/
theorem synthesizeFromConst_first_run {logProf declName ci bs body m d}
    {isInst : Lean.Expr → Bool}
    (shape : certifiedShape? false [] ci = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName [] false true
        ci isInst) (m, d)) :
    MReturns (synthesizeCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName bs body)
      (m, d) := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact run

/-- **`synthesizeCertified` returns a run of the MIXED harness** on the
translated binders (`synthesizeMixedCertified_returns`' conclusion, verbatim,
at `bs.map mixB`). -/
theorem synthesizeCertified_returnsM {logProf declName bs body m d}
    (hr : MReturns (synthesizeCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName bs body)
      (m, d)) :
    ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (returned : String)
      (st : CircuitState), ids.Nodup ∧ ids.length = (bs.map mixB).length ∧
      Tools.ShippingTranslateSoundness.Returns (bindMixedCertifiedInputs
        (emitLeaves (fun e hint top named => translateExprToWire tenv e hint top named) cache logProf
          [("out", instFVars (ids.map Lean.Expr.fvar).toArray 0 body)] none 0) ((bs.map mixB).zip ids))
        (entryCompilerState false cache) (CircuitM.init (Sparkle.IR.ModuleName.ofDecl declName))
        returned st ∧
      m = (addClockResetIfSequential st.module).finalize ∧ d = st.design ∧
      Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName m.name) = true := by
  unfold synthesizeCertified at hr
  obtain ⟨ids, _, hr⟩ := MReturns.bind hr
  split at hr
  rotate_left
  · exact (MReturns.throw hr).elim
  rename_i hids
  dsimp only at hr
  obtain ⟨cache, _, hr⟩ := MReturns.bind hr
  obtain ⟨⟨returned, st⟩, run, finish⟩ := MReturns.bind hr
  obtain ⟨hm, hd, name⟩ := finishSynth_returns finish
  have run' := MReturns.run run
  rw [bindCertified_mixed] at run'
  exact ⟨ids, cache, returned, st, hids.1, by rw [List.length_map]; exact hids.2, run', hm, hd, name⟩

/-! ## 2. The first gate's binders and body, as the mixed harness reads them -/

/-- The mixed-gate binders of `quoteDecl dn names n fe`. -/
def firstBs (dn : Name) (names : List Name) (n : Nat) : List (Name × MixedGateBinder) :=
  (quoteBinders dn names n).map mixB

theorem firstBs_eq (dn : Name) (names : List Name) (n : Nat) :
    firstBs dn names n = (dn, .domain) :: names.map (fun nm => (nm, MixedGateBinder.bits n)) := by
  unfold firstBs quoteBinders
  rw [List.map_cons, List.map_map]
  all_goals rfl

theorem firstBs_length (dn : Name) (names : List Name) (n : Nat) :
    (firstBs dn names n).length = names.length + 1 := by
  rw [firstBs_eq, List.length_cons, List.length_map]

theorem firstBs_bits {dn : Name} {names : List Name} {n j : Nat} (hj : j < names.length) :
    (firstBs dn names n)[j + 1]? = some (names[j], .bits n) := by
  rw [firstBs_eq, List.getElem?_cons_succ, List.getElem?_map, List.getElem?_eq_getElem hj]
  all_goals rfl

theorem firstBs_positive {dn : Name} {names : List Name} {n : Nat} (hn : 0 < n) :
    PositiveBinders (firstBs dn names n) := by
  intro name m hm
  rw [firstBs_eq] at hm
  rcases List.mem_cons.mp hm with h | h
  · cases h
  · obtain ⟨nm, -, h⟩ := List.mem_map.mp h
    cases h
    exact hn

/-- The non-domain binders: every name at width `n`. -/
theorem firstBs_filter (dn : Name) (names : List Name) (n : Nat) :
    (firstBs dn names n).filter (fun x => x.2 != MixedGateBinder.domain) =
      names.map (fun nm => (nm, MixedGateBinder.bits n)) := by
  rw [firstBs_eq]
  have htail : List.filter (fun x : Name × MixedGateBinder => x.2 != MixedGateBinder.domain)
      (names.map (fun nm => (nm, MixedGateBinder.bits n))) =
      names.map (fun nm => (nm, MixedGateBinder.bits n)) :=
    List.filter_eq_self.mpr (fun x hx => by
      obtain ⟨nm, -, rfl⟩ := List.mem_map.mp hx
      first | rfl | simp)
  -- the head binder is the domain: `filter` drops it (by computation)
  first
    | exact htail
    | (simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
       exact htail)

/-- **The first gate's body is the quote of the unified term `ofF n fe`** at
the mixed harness' input positions (the domain at position 0, input `j` at
position `j + 1`). -/
theorem first_body {dn : Name} {names : List Name} {n : Nat} {fe : FExpr}
    (hwf : fe.WF names.length n) :
    quoteBody names.length n fe =
      quote (.bvar names.length) (fun _ => inputExpr (firstBs dn names n).length 0)
        (fun j => inputExpr (firstBs dn names n).length (j + 1)) (ofF n fe) := by
  rw [quote_ofF, firstBs_length]
  unfold quoteBody
  exact quoteF_congr (fun j _ => by
    show Lean.Expr.bvar (names.length - 1 - j) =
      Lean.Expr.bvar (names.length + 1 - 1 - (j + 1))
    congr 1
    omega) fe hwf

/-- A port of the first gate's walk: position `j + 1` is the `j`-th
non-domain binder. -/
theorem portIdx_first {dn : Name} {names : List Name} {n j : Nat} (hj : j < names.length) :
    portIdx (firstBs dn names n) (j + 1) = j := by
  unfold portIdx
  rw [firstBs_eq, List.take_succ_cons]
  have hall : ((names.map fun nm => (nm, MixedGateBinder.bits n)).take j).filter
      (fun b => b.2 != MixedGateBinder.domain) =
      (names.map fun nm => (nm, MixedGateBinder.bits n)).take j :=
    List.filter_eq_self.mpr (fun x hx => by
      obtain ⟨nm, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hx)
      first | rfl | simp)
  have key : (List.filter (fun b : Name × MixedGateBinder => b.2 != MixedGateBinder.domain)
      ((names.map fun nm => (nm, MixedGateBinder.bits n)).take j)).length = j := by
    rw [hall, List.length_take, List.length_map]
    omega
  first
    | exact key
    | (simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
       exact key)

theorem evalFE_congr {n k : Nat} {f g : Nat → BitVec n} (h : ∀ j, j < k → f j = g j) :
    ∀ (fe : FExpr), fe.WF k n → evalFE n f fe = evalFE n g fe
  | .inp j, hj => h j hj
  | .lit _, _ => rfl
  | .bin op a b, ⟨ha, hb⟩ => by
    show op.apply (evalFE n f a) (evalFE n f b) = op.apply (evalFE n g a) (evalFE n g b)
    rw [evalFE_congr h a ha, evalFE_congr h b hb]

/-- What the first-gate child computes on its argument-port values `vs`: the
harness' function (`gate_childFn`'s `F`) at the first gate's positions. -/
def firstFn (dn : Name) (names : List Name) (n : Nat) (fe : FExpr) (vs : List Nat) : Nat :=
  (pack (.bits n) (eval (fun _ => decB (firstBs dn names n) vs 0)
    (fun j w => decV (firstBs dn names n) vs (j + 1) w) (ofF n fe))).toNat

/-- … which is `evalFE` of the port values, in order. -/
theorem firstFn_eval (dn : Name) {names : List Name} {n : Nat} {fe : FExpr} (vals : List Nat)
    (hwf : fe.WF names.length n) :
    firstFn dn names n fe vals = (evalFE n (fun j => BitVec.ofNat n (vals.getD j 0)) fe).toNat := by
  have hc : ∀ j, j < names.length →
      decV (firstBs dn names n) vals (j + 1) n = BitVec.ofNat n (vals.getD j 0) := by
    intro j hj
    unfold decV
    rw [portIdx_first hj]
  unfold firstFn
  rw [eval_ofF]
  show (evalFE n (fun j => decV (firstBs dn names n) vals (j + 1) n) fe).toNat = _
  rw [evalFE_congr hc fe hwf]

/-- In-range port values of the first gate's non-domain binders. -/
theorem inRange_bits {n : Nat} : ∀ (vals : List Nat) (names : List Name),
    vals.length = names.length → (∀ v ∈ vals, v < 2 ^ n) →
    InRange vals (names.map fun nm => (nm, MixedGateBinder.bits n))
  | [], [], _, _ => Zip₂.nil
  | [], _ :: _, hl, _ => by simp only [List.length_nil, List.length_cons] at hl <;> omega
  | _ :: _, [], hl, _ => by simp only [List.length_nil, List.length_cons] at hl <;> omega
  | v :: vals, _ :: names, hl, hb =>
    Zip₂.cons (show v < 2 ^ n from hb v (List.mem_cons_self ..))
      (inRange_bits vals names (by simp only [List.length_cons] at hl; omega)
        (fun x hx => hb x (List.mem_cons_of_mem _ hx)))

/-! ## 3. The core run: a mixed-harness run, and the fragment outcome -/

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 1000000 in
/-- **A core run of a first-gate declaration is a run of the mixed harness**
on `firstBs` and the declaration's body, with the translator at the run's
environment. From the run and `EntryDefines` (ALLOWED). -/
theorem first_core_run {declName : Name} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) :
    ∃ (envR : Environment) (logProf : String → IO Unit) (ids : List FVarId)
      (cache : IO.Ref (ExprStructMap String)) (returned : String) (st : CircuitState),
      ids.Nodup ∧ ids.length = (firstBs dn names n).length ∧
      Tools.ShippingTranslateSoundness.Returns (bindMixedCertifiedInputs
        (emitLeaves (fun e hint top named => translateExprToWire envR e hint top named) cache logProf
          [("out", instFVars (ids.map Lean.Expr.fvar).toArray 0 (quoteBody names.length n fe))]
          none 0) ((firstBs dn names n).zip ids))
        (entryCompilerState false cache) (CircuitM.init (Sparkle.IR.ModuleName.ofDecl declName))
        returned st ∧
      M = (addClockResetIfSequential st.module).finalize ∧ D = st.design ∧
      Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName M.name) = true := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hr
  obtain ⟨d, hd, definition⟩ := entry w1 ci w2 w5 envR w6 get henv
  rw [hd] at run
  have shape := certifiedShape_quote definition hwf
  have core := synthesizeFromConst_first_run shape run.mreturns
  obtain ⟨ids, cache, returned, st, nd, len, hrun, hm, hD, legal⟩ :=
    synthesizeCertified_returnsM core
  exact ⟨envR, logProf, ids, cache, returned, st, nd, len, hrun, hm, hD, legal⟩

/-- The fragment outcome of the core module, at the constant THIS run handed
on (`EntryDefines`). -/
theorem first_core_outcome {declName : Name} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) :
      ∃ port : Nat → Option String,
        (∀ j j' w, port j = some w → port j' = some w → j = j') ∧
        (∀ j, j < names.length → ∃ w, port j = some w) ∧
        ∀ (vals : Nat → BitVec n) (mems : MEnv) (initial : Env),
          (∀ j w, j < names.length → port j = some w → initial w = (vals j).toNat) →
          ∃ env, evalAssigns (Tools.ShippingEntrySoundness.weOf M) mems M.body initial = some env ∧
            env "out" = (evalFE n vals fe).toNat ∧ "out" ∈ M.outputs.map (·.name) ∧
            (∀ j w, j < names.length → port j = some w →
              ({ name := w, ty := .bitVector n } : Port) ∈ M.inputs) ∧
            PostReady M n ∧
            (∀ p ∈ M.inputs, ∃ j, j < names.length ∧ port j = some p.name ∧
              p.ty = .bitVector n ∧ ({ name := p.name, ty := .bitVector n } : Port) ∈ M.wires) := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads h
  obtain ⟨d, hd, definition⟩ := entry w1 ci w2 w5 envR w6 get henv
  rw [hd] at run
  exact outcome_quote (synthesizeFromConst_sound run.mreturns) definition hwf

/-- **`fragmentDecl_of_env` with `EnvDefines` replaced by `EntryDefines`**
(ALLOWED): the core module computes the Lean meaning at every cycle, on
distinct input ports. -/
theorem fragmentDecl_of_entry {declName : Name} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) :
    ∃ port : Nat → Option String,
      (∀ j j' w, port j = some w → port j' = some w → j = j') ∧
      (∀ j, j < names.length → ∃ w, port j = some w) ∧
      ∀ {dom : Sparkle.Core.Domain.DomainConfig}
        (sigs : Nat → Sparkle.Core.Signal.Signal dom (BitVec n)) (t : Nat) (mems : MEnv)
        (initial : Env),
        (∀ j w, j < names.length → port j = some w → initial w = ((sigs j).val t).toNat) →
        ∃ env, evalAssigns (Tools.ShippingEntrySoundness.weOf M) mems M.body initial = some env ∧
          env "out" = ((denoteFE n sigs fe).val t).toNat ∧ PostReady M n ∧
          (∀ p ∈ M.inputs, ∃ j, j < names.length ∧ port j = some p.name ∧
            p.ty = .bitVector n ∧ ({ name := p.name, ty := .bitVector n } : Port) ∈ M.wires) ∧
          "out" ∈ M.outputs.map (·.name) ∧
          (∀ j w, j < names.length → port j = some w →
            ({ name := w, ty := .bitVector n } : Port) ∈ M.inputs) := by
  obtain ⟨port, hdist, hex, hsem⟩ := first_core_outcome h entry hwf
  refine ⟨port, hdist, hex, fun sigs t mems initial hinit => ?_⟩
  obtain ⟨env, hev, hout, hmo, hin, hpr, hins⟩ := hsem (fun j => (sigs j).val t) mems initial hinit
  exact ⟨env, hev, by rw [hout, denoteFE_val], hpr, hins, hmo, hin⟩

/-- The core module is `PostReady` at the fragment's width. -/
theorem first_core_postReady {declName : Name} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) : PostReady M n := by
  obtain ⟨port, -, -, hsem⟩ := first_core_outcome h entry hwf
  obtain ⟨_, _, _, _, _, hpr, _⟩ := hsem (fun _ => 0) (fun _ _ => 0)
    (fun _ => (0 : BitVec n).toNat) (fun _ _ _ _ => rfl)
  exact hpr

/-- **The full entry (`#synthesizeVerilog`'s IR) for a first-gate fragment,
under `EntryDefines`**: `synthesizeCombinational_fragment` with
`EnvDefines` replaced. Evaluation for EVERY initial environment whose ports
carry the input signals. -/
theorem synthesizeCombinational_fragment_entry {declName : Name} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) :
    ∃ port : Nat → Option String,
      (∀ j j' w, port j = some w → port j' = some w → j = j') ∧
      (∀ j, j < names.length → ∃ w, port j = some w) ∧
      ∀ {dom : Sparkle.Core.Domain.DomainConfig}
        (sigs : Nat → Sparkle.Core.Signal.Signal dom (BitVec n)) (t : Nat) (mems : MEnv)
        (initial : Env),
        (∀ j w, j < names.length → port j = some w → initial w = ((sigs j).val t).toNat) →
        ∃ env, evalAssigns (Tools.ShippingEntrySoundness.weOf M') mems M'.body initial = some env ∧
          env "out" = ((denoteFE n sigs fe).val t).toNat := by
  obtain ⟨M, D, w1, hcore, hM'⟩ := Tools.ShippingPostSoundness.synthesizeCombinational_reads h
  obtain ⟨port, hdist, hex, hsem⟩ := fragmentDecl_of_entry hcore entry hwf
  refine ⟨port, hdist, hex, fun sigs t mems initial hinit => ?_⟩
  obtain ⟨env, hev, hout, hpr, -, -, -⟩ := hsem sigs t mems initial hinit
  obtain ⟨hev', -, -⟩ := Tools.ShippingPostSoundness.postprocess_sound hn hpr hM' hev
  exact ⟨env, hev', hout⟩

/-- **The full entry's one output is `out : bitVector n`.** -/
theorem first_full_outputs {declName : Name} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) :
    b.outputs = [{ name := "out", ty := .bitVector n }] := by
  obtain ⟨M, D, w1, hcore, hpost, -⟩ := synthesizeCombinational_parts hr
  have hpr := first_core_postReady hcore entry hwf
  obtain ⟨-, -, -, hdo, -⟩ := Tools.ShippingPostSoundness.dropZeroWidth_entry M n hn hpr
  have hMo : M.outputs = [{ name := "out", ty := .bitVector n }] := hpr.2.2.2.1 hn
  rcases hpost with rfl | rfl
  · rw [hdo, hMo]
  · rw [(Sparkle.IR.RefineCheck.mergeChecked_ports _).2.1, hdo, hMo]

/-! ## 4. (c) The design frame, and the child-side facts -/

set_option maxHeartbeats 1000000 in
/-- **(c) The first-gate translation of a fragment body adds no module**: the
core run's design has no module. (The harness run of the bridge keeps the
initial design: `transition_closed`, from the spine's `Ext`.) -/
theorem first_core_design {declName : Name} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (hcore : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) : D.modules = [] := by
  obtain ⟨envR, logProf, ids, cache, returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    first_core_run hcore entry hwf
  have he := wf_ofF 0 names.length n hn fe hwf
  obtain ⟨-, -, -, -, hdesign, -⟩ :=
    transition_closed (dom := .bvar names.length) (bpos := fun _ => 0) (vpos := fun j => j + 1)
      nd len hrun hm nameLegal (firstBs_positive hn) (ofF n fe) he
      (fun j hj => absurd hj (Nat.not_lt_zero j)) (fun j hj => ⟨names[j], firstBs_bits hj⟩)
      (first_body (dn := dn) hwf)
  rw [hD, hdesign]
  rfl

set_option maxHeartbeats 1000000 in
/-- **A first-gate child's full-entry result, from one run and
`EntryDefines`**: `gate_child_fullFacts` for the first gate (its proof, the
core run replaced by the bridge). In particular the design has no module
(c), and the input ports are distinct allocated names (`inputAlloc`: none is
`clk`, `rst` or `out`). -/
theorem first_child_fullFacts {declName : Name} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) :
    ChildFull declName (firstBs dn names n) b design := by
  obtain ⟨M, D, w1, hcore, hpost, hdes⟩ := synthesizeCombinational_parts hr
  obtain ⟨envR, logProf, ids, cache, returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    first_core_run hcore entry hwf
  have he := wf_ofF 0 names.length n hn fe hwf
  obtain ⟨hclosed, -, ⟨ow, pb⟩, ready, hdesign, hname⟩ :=
    transition_closed (dom := .bvar names.length) (bpos := fun _ => 0) (vpos := fun j => j + 1)
      nd len hrun hm nameLegal (firstBs_positive hn) (ofF n fe) he
      (fun j hj => absurd hj (Nat.not_lt_zero j)) (fun j hj => ⟨names[j], firstBs_bits hj⟩)
      (first_body (dn := dn) hwf)
  obtain ⟨-, ⟨B, wOut, hB⟩, hin⟩ :=
    transition_facts (dom := .bvar names.length) (bpos := fun _ => 0) (vpos := fun j => j + 1)
      nd len hrun hm nameLegal he
      (fun j hj => absurd hj (Nat.not_lt_zero j)) (fun j hj => ⟨names[j], firstBs_bits hj⟩)
      (first_body (dn := dn) hwf)
  -- the core module (the text of `gate_child_comb`)
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
  obtain ⟨dzb, _, dzi, dzo, _⟩ := Tools.ShippingTypedPostSoundness.dropZeroWidth_typed ready
  have hZ : ChildComb (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) :=
    { assigns := by rw [dzb]; exact hM.assigns
      closed := by rw [dzb, dzi]; exact hM.closed
      output := by rw [dzo]; exact hM.output
      outDriven := by rw [dzb]; exact hM.outDriven
      inputNames := by rw [dzi]; exact hM.inputNames
      inputAlloc := by rw [dzi]; exact hM.inputAlloc }
  have hcomb : ChildComb b := by
    rcases hpost with rfl | rfl
    · exact hZ
    · obtain ⟨mi, mo, _⟩ := Sparkle.IR.RefineCheck.mergeChecked_ports
        (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)
      obtain ⟨mc, mw⟩ := mergeChecked_closed
        (S := (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).inputs.map (·.name))
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
  -- ports, name, design (the text of `gate_child_fullFacts`)
  have hMtys : M.inputs.map (·.ty) =
      ((firstBs dn names n).filter fun x => x.2 != .domain).map fun x => kindTy x.2 := by
    rw [hin (fun _ => false) (fun _ k => 0#k)]
    exact Tools.ShippingTransitionFields.inputPorts_tys (firstBs dn names n) ids _ len
  have hDm : D.modules = [] := by
    rw [hD, hdesign]
    rfl
  refine ⟨hcomb, ?_, ?_, hdes hDm⟩
  · rcases hpost with rfl | rfl
    · rw [dzi]; exact hMtys
    · rw [(Sparkle.IR.RefineCheck.mergeChecked_ports _).1, dzi]; exact hMtys
  · rcases hpost with rfl | rfl
    · rw [dropZeroWidth_name]; exact hname
    · rw [Tools.ShippingMachineDepthRun.mergeChecked_name, dropZeroWidth_name]; exact hname

theorem nAlloc_clk : ¬ Allocated "clk" := by
  intro h
  have := h.2
  revert this
  decide

theorem nAlloc_rst : ¬ Allocated "rst" := by
  intro h
  have := h.2
  revert this
  decide

theorem nAlloc_out : ¬ Allocated "out" := by
  intro h
  have := h.2
  revert this
  decide

/-- **The allocation fact**: the full entry's input ports (`bindCertifiedInputs`'
names, through the bridge) are distinct, allocated, and none is `clk`, `rst` or
`out`. -/
theorem first_full_inputs {declName : Name} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) :
    (b.inputs.map (·.name)).Nodup ∧ b.inputs.length = names.length ∧
      ∀ p ∈ b.inputs, Allocated p.name ∧ p.name ≠ "clk" ∧ p.name ≠ "rst" ∧ p.name ≠ "out" := by
  have full := first_child_fullFacts hr entry hwf hn
  have hlen := congrArg List.length full.tys
  simp only [List.length_map, firstBs_filter] at hlen
  refine ⟨full.comb.inputNames, hlen, fun p hp => ?_⟩
  have alloc := full.comb.inputAlloc p hp
  refine ⟨alloc, fun e => nAlloc_clk ?_, fun e => nAlloc_rst ?_, fun e => nAlloc_out ?_⟩
  · rw [← e]; exact alloc
  · rw [← e]; exact alloc
  · rw [← e]; exact alloc

/-! ## 5. What the full-entry module computes, for every environment -/

section fn
open Tools.ShippingGateChild

/-- `ChildFn` without the reset premise: on EVERY environment whose argument
values satisfy `P`, the single output carries `f` of them. -/
def ChildFnR (mc : Sparkle.IR.AST.Module) (P : List Nat → Prop) (f : List Nat → Nat) : Prop :=
  ∃ outP, mc.outputs = [outP] ∧ ∀ (mems : MEnv) (env : Env),
    P ((argPorts mc).map fun p => env p.name) →
    ∃ cres, evalAssigns (Sparkle.IR.RegDedup.declWidth mc) mems mc.body env = some cres ∧
      cres outP.name = f ((argPorts mc).map fun p => env p.name)

/-- `gate_childFn` without its (unused) reset premise: its proof, the binder
dropped. -/
theorem gate_childFnR {declName : Name} {m : Sparkle.IR.AST.Module}
    {bs : List (Name × MixedGateBinder)} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {srt : SType} {e : Term srt} {bpos vpos : Nat → Nat}
    (nd : ids.Nodup) (len : ids.length = bs.length)
    (vals : ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n) (initial : Env)
        (mems : MEnv),
      SourceInputs declName bs ids cache bools bits initial →
      RawValueAt srt.width bs m initial mems
        (pack srt (eval (fun j => bools (bpos j)) (fun j w => bits (vpos j) w) e)).toNat)
    (ins : ∀ bools bits, m.inputs = inputPorts bools bits (bs.zip ids)
      (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName)))
    (positive : Tools.ShippingMixedEntrySoundness.PositiveBinders bs)
    {F : List Nat → Nat}
    (hF : ∀ vs, InRange vs (bs.filter fun b => b.2 != .domain) →
      F vs = (pack srt (eval (fun j => decB bs vs (bpos j)) (fun j w => decV bs vs (vpos j) w) e)).toNat) :
    ChildFnR m (fun vs => InRange vs (bs.filter fun b => b.2 != .domain)) F ∧
      m.body.all Sparkle.IR.RegDedup.isAssign = true ∧
      Tools.ShippingTypedPostSoundness.TypedPostReady m := by
  -- the facts that do not depend on the inputs, at the all-zero environment
  obtain ⟨_, _, _, tpr, simple, _, _, _, pb⟩ := vals (fun _ => false) (fun _ n => 0#n) (fun _ => 0)
    (fun _ _ => 0) (Tools.ShippingGateChild.admissible_zero _ _)
  have pb := pb positive
  have hall : m.body.all Sparkle.IR.RegDedup.isAssign = true := by
    rw [List.all_eq_true]
    intro st hs
    obtain ⟨l, r, rfl, _⟩ := simple st hs
    rfl
  refine ⟨?_, hall, tpr⟩
  obtain ⟨ty, hout⟩ := pb.output
  refine ⟨{ name := "out", ty := ty }, hout, ?_⟩
  intro mems env hP
  -- the argument ports are the binder walk's
  have hargs : argPorts m = machPorts declName ids cache bs := by
    unfold argPorts machPorts
    rw [ins (fun _ => false) (fun _ n => 0#n)]
    apply List.filter_eq_self.mpr
    intro p hp
    have hpi : p ∈ m.inputs := by rw [ins (fun _ => false) (fun _ n => 0#n)]; exact hp
    have alloc : Sparkle.IR.NameHints.Allocated p.name := pb.wireNames p (pb.inputWires p hpi)
    have hc : p.name ≠ "clk" := fun h => by
      have := (h ▸ alloc : Sparkle.IR.NameHints.Allocated "clk").2
      revert this; decide
    have hr : p.name ≠ "rst" := fun h =>
      Tools.ShippingRegisterSoundness.not_allocated_rst (h ▸ alloc)
    simp [hc, hr]
  let vs := (argPorts m).map fun p => env p.name
  let bools : Nat → Bool := fun p => decB bs vs p
  let bits : (j : Nat) → (n : Nat) → BitVec n := fun p n => decV bs vs p n
  have hlenIn : bs.length ≤ ids.length := by omega
  have hsi : SourceInputs declName bs ids cache bools bits env := by
    unfold SourceInputs
    apply admissible_of_portsD
    rw [show inputPorts (boolValues ids bools) (bitValues ids bits) (bs.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName)) =
        machPorts declName ids cache bs from inputPorts_congr _ _ _ rfl, ← hargs]
    have hlenP : (argPorts m).length =
        ((bs.zip ids).filter fun b => b.1.2 != .domain).length := by
      rw [hargs, machPorts_length _ hlenIn, ← zip_filter_fst _ _ hlenIn, List.length_map]
    apply Zip₂.of_get hlenP
    intro q p b hp hb
    obtain ⟨pos, hpos, hcnt⟩ := filter_getElem_pos _ _ q b hb
    obtain ⟨⟨nm, kind⟩, id⟩ := b
    obtain ⟨hb1, hb2⟩ := List.getElem?_zip_eq_some.mp hpos
    have hidx : ids.idxOf id = pos := by
      have hlt : pos < ids.length := (List.getElem?_eq_some_iff.mp hb2).1
      have hg : ids[pos]! = id := by simp [List.getElem!_eq_getElem?_getD, hb2]
      rw [← hg]; exact index_fresh ids nd pos hlt
    have hport : portIdx bs pos = q := by
      unfold portIdx
      have hpl : pos < bs.length := (List.getElem?_eq_some_iff.mp hb1).1
      rw [← hcnt, show (bs.zip ids).take pos = (bs.take pos).zip (ids.take pos) from
        List.take_zipWith, ← zip_filter_fst (bs.take pos) (ids.take pos)
        (by simp only [List.length_take]; omega), List.length_map]
    have hval : vs.getD q 0 = env p.name := by
      simp [vs, List.getD_eq_getElem?_getD, hp]
    have hfq : (bs.filter fun b => b.2 != .domain)[q]? = some (nm, kind) := by
      rw [← zip_filter_fst _ _ hlenIn, List.getElem?_map, hb]; rfl
    have hr := inRange_get hP q (nm, kind) hfq
    rw [hval] at hr
    simp only [binderEnc]
    cases kind with
    | domain =>
      have := (List.mem_filter.mp (List.mem_of_getElem? hb)).2
      simp at this
    | bool =>
      simp only [boolValues, hidx, bools, decB, hport, hval]
      simp only [Tools.ShippingMuxLoweringSoundness.encodeBool]
      simp only at hr
      split <;> simp_all <;> omega
    | bits n =>
      simp only [bitValues, hidx, bits, decV, hport, hval]
      simp only at hr
      simp [Nat.mod_eq_of_lt hr]
  obtain ⟨result, hev, hres, _, _, hwe, _, _, _⟩ := vals bools bits env mems hsi
  refine ⟨result, ?_, ?_⟩
  · have : Sparkle.IR.RegDedup.declWidth m = moduleWidths m := by
      rw [← hwe]; rfl
    rw [this]; exact hev
  · rw [hres, hF vs hP]

/-- `childFn_dropZW` without the reset premise. -/
theorem childFnR_dropZW {M : Sparkle.IR.AST.Module} {P : List Nat → Prop} {F : List Nat → Nat}
    (h : ChildFnR M P F) (htp : Tools.ShippingTypedPostSoundness.TypedPostReady M) :
    ChildFnR (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) P F := by
  obtain ⟨hb, hw, hi, ho, _⟩ := Tools.ShippingTypedPostSoundness.dropZeroWidth_typed htp
  obtain ⟨outP, houts, hf⟩ := h
  refine ⟨outP, by rw [ho]; exact houts, ?_⟩
  intro mems env hP
  have hargs : argPorts (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) = argPorts M := by
    unfold argPorts; rw [hi]
  rw [hargs] at hP ⊢
  obtain ⟨cres, hev, hcres⟩ := hf mems env hP
  have hdw : Sparkle.IR.RegDedup.declWidth (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) =
      Sparkle.IR.RegDedup.declWidth M := by
    change Tools.ShippingEntrySoundness.weOf _ = Tools.ShippingEntrySoundness.weOf _
    exact hw
  exact ⟨cres, by rw [hdw, hb]; exact hev, hcres⟩

/-- `childFn_merge` without the reset premise. -/
theorem childFnR_merge {raw : Sparkle.IR.AST.Module} {P : List Nat → Prop} {F : List Nat → Nat}
    (h : ChildFnR raw P F) (hall : raw.body.all Sparkle.IR.RegDedup.isAssign = true) :
    ChildFnR (Sparkle.IR.RegDedup.mergeDuplicates raw) P F := by
  obtain ⟨outP, houts, hf⟩ := h
  refine ⟨outP, ?_, ?_⟩
  · unfold Sparkle.IR.RegDedup.mergeDuplicates
    simp only [hall, if_true]
    split <;> exact houts
  · intro mems env hP
    have hin : (Sparkle.IR.RegDedup.mergeDuplicates raw).inputs = raw.inputs := by
      unfold Sparkle.IR.RegDedup.mergeDuplicates
      simp only [hall, if_true]
      split <;> rfl
    have hargs : argPorts (Sparkle.IR.RegDedup.mergeDuplicates raw) = argPorts raw := by
      unfold argPorts; rw [hin]
    rw [hargs] at hP ⊢
    obtain ⟨cres, hev, hcres⟩ := hf mems env hP
    obtain ⟨hev', _⟩ := Tools.ShippingPostSoundness.mergeDuplicates_sound raw mems env cres
      hall hev
    exact ⟨cres, hev', hcres⟩

/-- `childFn_post` without the reset premise. -/
theorem childFnR_post {M b : Sparkle.IR.AST.Module} {P : List Nat → Prop} {F : List Nat → Nat}
    (h : ChildFnR M P F) (htp : Tools.ShippingTypedPostSoundness.TypedPostReady M)
    (hall : M.body.all Sparkle.IR.RegDedup.isAssign = true)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) :
    ChildFnR b P F := by
  have hdz := childFnR_dropZW h htp
  have hall' : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body.all
      Sparkle.IR.RegDedup.isAssign = true := by
    rw [(Tools.ShippingTypedPostSoundness.dropZeroWidth_typed htp).1]; exact hall
  rcases hpost with rfl | rfl
  · exact hdz
  · rcases Sparkle.IR.RefineCheck.mergeChecked_cases (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)
      with he | he <;> rw [he]
    · exact childFnR_merge hdz hall'
    · exact hdz

end fn

set_option maxHeartbeats 1000000 in
/-- **What a first-gate child's full-entry module computes**, on every
environment whose argument ports hold in-range values: `firstFn` of them
(`evalFE` of the fragment, `firstFn_eval`). From one run + `EntryDefines`. -/
theorem first_child_fnR {declName : Name} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) :
    ChildFnR b (fun vs => InRange vs ((firstBs dn names n).filter fun x => x.2 != .domain))
      (firstFn dn names n fe) := by
  obtain ⟨M, D, w1, hcore, hpost, -⟩ := synthesizeCombinational_parts hr
  obtain ⟨envR, logProf, ids, cache, returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    first_core_run hcore entry hwf
  have he := wf_ofF 0 names.length n hn fe hwf
  obtain ⟨vals, -, ins⟩ :=
    transition_facts (dom := .bvar names.length) (bpos := fun _ => 0) (vpos := fun j => j + 1)
      nd len hrun hm nameLegal he
      (fun j hj => absurd hj (Nat.not_lt_zero j)) (fun j hj => ⟨names[j], firstBs_bits hj⟩)
      (first_body (dn := dn) hwf)
  obtain ⟨hfn, hall, htp⟩ := gate_childFnR nd len vals ins (firstBs_positive hn)
    (F := firstFn dn names n fe) (fun _ _ => rfl)
  exact childFnR_post hfn htp hall hpost

end Tools.ShippingFirstGateChild
