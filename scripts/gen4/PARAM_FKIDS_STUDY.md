# PARAM_FKIDS_STUDY: does F-kids hold in a successful parametric run?

Status: study only. No Lean source edited, nothing committed except this document. Base 99d5d5d1 (par/param-fkids).
Ledger: FG 92 / T1 57 (this unit: FG -0 +0 / T1 -0 +0). Accepted counts unchanged.

F-kids (PARAM_LEGAL_STUDY §4 item 3), for a returning run `Run declName θ (M', D')` of
`synthesizeCombinationalWithParameters`:

    ∀ x ∈ D'.modules, x.name ≠ M'.name → x.parameters = []

## Result in one paragraph

**By code reading and by a scratch probe, F-kids held in every case tried, and this study found no path by which a
module with a non-empty `parameters` list gets into `design.modules`.** The reading gives a reason (one write site for
`parameters`, reached only from the top call's `θ`). It is not a Lean theorem. The probe is a set of observations of
seven declarations, not a proof; the missing piece is an invariant over the recursive translator, which has not been
stated or proved here. "Not found" is not "cannot happen".

## 1. Every path by which a module enters `design.modules` (Sparkle/Compiler/Elab.lean, line numbers at base)

`design.modules` is written only through `CompilerM.addModuleToDesign` (Elab.lean:294) → `CircuitM.addModuleToDesign`
(IR/Builder.lean:81, `design.addModule m`). The call sites:

| # | site | what it adds | where the added module comes from |
|---|---|---|---|
| 1 | Elab.lean:6622-6628 (legacy instance arm, `translateInstance…`) | `subDesign.modules` (not already present), then `subModule` | `synthesizeCombinational name` (6586, 6598) |
| 2 | `instAddModules` Elab.lean:8517-8520, `instRegisterChild` 8558-8562 | same two things, certified/machine instance lowering (`translateInstanceUncachedWith`, 8590-8605; record-field arm 8660-8690) | the `(subModule, subDesign)` handed to the lowering, which the callers get from `synthesizeCombinational`/`synthesizeChild` |
| 3 | `finishSynth` (2218-2236) returns `finalCircuitState.design` unchanged | — | the design accumulated by 1 and 2 |
| 4 | `synthesizeCombinationalWithParameters` (8940-8954): `top f d` maps `f` over modules named `m.name` only | no new module | — |
| 5 | `synthesizeHierarchicalWithParameters` (9125-9128): `design.addModule module` when no module has the top's name | the top `M'` itself | the `D.addModule b` shape of PARAM_LEGAL_STUDY §2; the top is the one module allowed `parameters ≠ []` |

`synthesizeCombinational` (6332) is `childSynthEntry`/`synthesizeChild` (8929-8934), i.e. `synthesizeCombinationalWith`
(5594) = `synthesizeCombinationalCoreWith translate declName [] false`: **`parameters = []`, `symbolicMode = false`**.
No other caller of `synthesizeCombinationalCoreWith`/`synthesizeFromConst` passes a non-empty list or `true`
(grep: 5594 and 8943 only; 8943 is the parametric entry).

## 2. Where `parameters` of a module is written

* `grep` over Sparkle/ finds one site that adds a parameter: `bindInputsLegacy` (Elab.lean:2123-2128) calls
  `CompilerM.addParameter` (300) only for a binder whose user name is a key of the `parameters` argument it was given
  (`parameters.find? …`). Every other `parameters := …` in Sparkle/ is the empty list (AST.lean:342, 353), a reverse
  of the same list in `finalize` (AST.lean:405), the post-specialization `[]` (Specialize.lean:124), or a copy
  `parameters := m.parameters` (Backend/Partition.lean:128, 137, after synthesis).
* The certified front ends (`certifiedShape?` 2316, `mixedCertifiedShape?` 2874) both return `none` when
  `symbolicMode || !parameters.isEmpty`, so they are not used with `θ`; their binder walks (`bindCertifiedInputs`,
  `bindMixedCertifiedInputs`) do not call `addParameter`; the machine route needs `!symbolicMode && parameters.isEmpty`
  (5314-5316).
* So `parameters ≠ []` on a module requires `bindInputsLegacy` to have run with a non-empty `parameters`, which only
  the top call of the parametric entry supplies. A child is synthesized by a fresh `CircuitM.init` state with
  `parameters = []` (5379-5383), hence has `parameters = []` and so does every module of its `subDesign`
  (by the same argument for its own children; this is the induction the Lean proof would need, see §4).
* Post-processing keeps the field (by reading): `dropZeroWidthModule` and `mergeChecked` update `body`/`wires` or
  return `m`/a merge of `m` (PARAM_LEGAL_STUDY §3, F-post). Not stated in Lean, and `mergeDuplicates` was not read to
  the end by that study. For F-kids it matters only for the child's own `[]`; an empty list stays empty if the field
  is untouched.
* Caches that could hand back a module: `sparkleSubModuleCache` / `sparkleChildCache` are reset at depth 0
  (Elab.lean:5538-5541). The symbolic top run stores its own (parameterised) result in `sparkleSubModuleCache` only
  on the certified branches (5297, 5304, 5323), which are not reached with `symbolicMode = true`, and on 5388 only
  `if !symbolicMode`. A nested child call runs with depth ≥ 1, so it reads only entries made earlier in the same run
  by children (parameters `[]`). A run that throws leaves the depth balanced (`try … finally`), and the next depth-0
  entry resets. By reading.
* A child that has the top's name: `finishSynth`'s `ModuleNameCheck.check (module :: finalCircuitState.design.modules)`
  throws when names collide, so a returning run has no `x ∈ D.modules` with `x.name = M.name`. That makes the guard
  `x.name ≠ M'.name` in F-kids vacuous for the core's own output (post-processing keeps names by reading), so the
  `D'.modules = D.modules` branch of the I4-struct lemma applies. (By reading; the name check's Lean statement was
  not used here.)

## 3. Probe (scratch, not committed): observations of the seven declarations

Scratch file Tests/Gen4/ParamFkidsProbe.lean (untracked, added to lakefile.lean locally, both removed before this
commit; built once with `kjob lake build Tests.Gen4.ParamFkidsProbe`, exit 0, 51 s, 226 jobs; the second edit failed to
elaborate one declaration, see below). It calls the unchanged `synthesizeCombinationalWithParameters` and prints
`d.modules` with each module's `parameters`. Declarations (all `Signal defaultDomain (BitVec 8)`), θ as shown:

| declaration | what it does | θ | observation |
|---|---|---|---|
| `topPlain (W) x := x` | no child | [W=8] | OK, `modules=[]`, top.params=[W], F-kids true |
| `topI (W) x := kidInl W x` | child is NOT `@[hardware_module]`, takes a Nat binder; inlined | [W=8] | OK, `modules=[]`, F-kids true |
| `topW (W) x := kidW W x` | `@[hardware_module]` child with a Nat binder named `W` | [W=8] | SYNTH FAILED: "Native symbolic-width synthesis currently supports combinational modules only" |
| `topP (W) x := kidPlain x` | `@[hardware_module]` child without Nat binder | [W=8] | same failure |
| `topKids (W)(K) x := kidW K x` | child Nat binder `K`, also in θ | [W=8,K=4] and [K=4] | same failure (both) |
| `topDead (W) x := let _u := kidPlain x; x` | child called, result unused | [W=8] | same failure (the `.inst` is still emitted) |
| `topKidW0 (W) x := let _u := kidW 3 x; x` | child with a Nat literal argument, unused | [W=8] | same failure |
| `topW` with θ containing a name that is not a Nat binder | — | [W=8,K=4] | SYNTH FAILED: "… 'K' is not a top-level Nat binder of topW" (the F-θ check) |

Reading of the table: a child that is a module instance makes the run throw (the `.inst` in the top body, `finishSynth`
2221-2227); a child that is inlined contributes no module. In no returning run was `d.modules` non-empty. One further
fixture (`topMulZero`, a child result `&&&` a literal) did not elaborate (typeclass stuck on the literal's domain),
so it gave no observation; it is not counted. These are observations of the listed declarations at the listed θ; they
do not say anything about other declarations, and a single `OK` is not a statement for other bindings.

Not tried: parametric tops that reach a module-instance child through paths that still return, if there are any
(none found by reading: any `.inst` in the final top body is refused, and `addModuleToDesign` at the sites of §1 is
followed in the same arm by the `emitInstance`, 6640ff, 8575ff, 8686-8690). If an instance were emitted and the arm then
threw and was caught (`try … catch` around inline attempts, 6586-6600), `CompilerM` is `StateT` over `MetaM`, so by
reading the state at the `try` is restored; not tested.

## 4. If it holds: the statement and a route (not frozen; for a later freeze)

Complete type (over the existing run relation; new file, no production edit), with the same binders as
`synthesizeCombinationalWithParameters_designTop` (Tools/ShippingGen4ParamIface.lean:27):

    theorem synthesizeCombinationalWithParameters_kids {declName : Name} {parameters : List (String × Nat)}
        {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
        {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
        {M' : Module} {D' : Design}
        (h : RunsTo (synthesizeCombinationalWithParameters declName parameters)
              mctx mref cctx cref w (M', D') w') :
        ∀ x ∈ D'.modules, x.name ≠ M'.name → x.parameters = []

Route, and its size (an estimate from reading, not measured):

1. `…_designTop` (exists) turns `h` into a run of `synthesizeCombinationalCoreWith Tsyn declName parameters true true`
   with `D'.modules = D.modules` under `∀ x ∈ D.modules, x.name ≠ M.name` and `M' = post M`. The hypothesis of that
   implication is the name-collision refusal of §2 (needs a statement about `ModuleNameCheck.check`; new), or F-kids
   is stated for `D.modules` directly and `D'.modules = (D.modules).map (top f)` with `f` parameter-preserving (F-post).
2. Core invariant: a returning run of `synthesizeCombinationalCoreWith Tsyn n [] false true` returns `(M,D)` with
   `M.parameters = []` and `∀ x ∈ D.modules, x.parameters = []`. This is an induction over the recursive translator
   through child synthesis (depth-bounded by `sparkleSynthDepthLimit`); it needs a preserved invariant "every module of
   `cs.design.modules` has `parameters = []`" over every `CompilerM` step of the translator, because `design` is
   changed only at `addModuleToDesign` (the sites of §1), and `addParameter` writes `cs.module`, not `cs.design`.
   This is the large part: the translator is a big recursive function, and no existing lemma states a design-wide
   invariant of this kind. The tree has per-shape results in the same spirit (Tools/ShippingKidsChildIface.lean,
   `synthesizeCombinational_designL`, and the Kids* family) that are stated for fixed declaration shapes, not for
   the full legacy translator.
3. Top call: `synthesizeFromConst` with `symbolicMode = true` reaches only the legacy branch (certified gates refuse
   it, §2); `finishSynth` returns `finalCircuitState.design`, which by step 2's invariant (the top's `CircuitState`
   starts from `Design.empty`, the top's `addParameter` writes `module`) has only parameterless modules.

I3b (`core_symbolic_reads`) already gives the peel down to `synthesizeFromConst`; the legacy branch past it
(`lambdaTelescope`, `emitLeaves`, `bindInputsLegacy`, `finishSynth`) has no lemma (PARAM_LEGAL_STUDY §4 item 1). The
size is that of I3b/I3c-class work (I3c's record: "no `Start`→`Out0` lemma found"); not measured.

## 5. If a counterexample is found later: options (not decided here)

No counterexample was found, so this is conditional. If F-kids were false for a reachable run (a child module with a
non-empty `parameters`), the choices would be:

| option | effect on the ledger | effect on scope | note |
|---|---|---|---|
| (a) add a guard hypothesis to the declaration (`∀ x ∈ D'.modules, x.name ≠ M'.name → x.parameters = []`) as a premise | +1 (replaces B.P-8 / B.P-1 by one premise: net -1 instead of -2) | none | a new ledger premise; needs its own reviewer-approved freeze |
| (b) restrict the covered declarations to those with no module children (`D.modules = []` of the run) | +1 or the same, as a premise on the declaration | **reduces the claimed scope**: user decision | not decided here |
| (c) strengthen the entry to refuse such runs | −2 as a theorem | production edit | not allowed for this unit; user approval |

## 6. Ledger prospect (row units; a bundled row's partial supply counts 0)

Nothing is accepted by this study: no Lean theorem exists. Conditional on all of F-θ, F-top, F-kids, F-post, the design
shape and the assembly (PARAM_LEGAL_STUDY §4 items 1-6) being proved with no new assumption: B.P-8 `LegalBinding D θ`
−1, B.P-1 `AllPos θ` −1 (via `legalBinding_allPos`, approved), coverage row −0 (row ID not confirmed, PARAM_LEGAL_STUDY
§5), additions +0. F-kids alone supplies 0: the rows disappear only when `LegalBinding` is assembled. B.P-5
(`SpecSuccess`-side) is unaffected (D3, user decision pending).

`条件付き台帳: 見込み B.P-8 -1 / B.P-1 -1、追加 0（F-θ/F-top/F-post/形/組立 の証明が全部入った場合のみ。F-kids 単独は 0）`.
Accepted line: `台帳: FG 92 / T1 57（今回 FG -0 +0 / T1 -0 +0）`.

## 7. Limits

* The probe covers the seven declarations of §3 (one fixture did not elaborate). Observations only.
* §1/§2 are code reading at base 99d5d5d1; nothing there is a Lean fact. The claim "only one site writes
  `parameters`" is a grep over Sparkle/, not over the whole repository (Tools/ copies of the compiler were not searched).
* F-θ, F-top, F-post, the design shape and the assembly are untouched by this study; their status is as in
  PARAM_LEGAL_STUDY.
* Not a statement that F-kids is true for all declarations; it is "not falsified by the paths read and the cases run".
