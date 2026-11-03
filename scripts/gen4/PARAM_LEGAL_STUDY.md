# PARAM_LEGAL_STUDY: can `LegalBinding` (B.P-8) be taken from a successful parametric run?

Status: study only (document, no Lean edited, no scratch committed). Base 50d22e3b (par/g4par-r23, F3 approved).
Plan: par/ledger-replan scripts/gen2/LEDGER_SHORTEN_PLAN2.md §4 recommendation 1 (rev3.1 3e90ef74).
Ledger: FG 93 / T1 55 (this unit: FG -0 +0 / T1 -0 +0). The accepted counts are not changed.

## Result in one paragraph

**This study did not find a supply path, and no Lean lemma in the tree connects a returning run of
`synthesizeCombinationalWithParameters` to `LegalBinding`.** Nothing was elaborated, because there is nothing to
elaborate that is not new proof work. The study found the reason the path is not a one-line combination of
`specializeDesign_ok_legal` and the I4-struct lemma, and it lists, as Lean types, the facts that are missing.
Several of those facts look available by reading the entry code; they have not been stated or proved in Lean.
This is "not found by this study", not a claim that the path is impossible or not derivable.

## 1. The types (read from the tree)

* `LegalBinding D θ := specValidateBindings D.modules θ = .ok ()`  (Tools/ShippingGen4ParamIface.lean:91), where
  `validateBindings` (Sparkle/IR/Specialize.lean:33) checks: (a) `validateParameterDeclarations`: no module declares a
  duplicate parameter name; (b) θ has no duplicate names; (c) every θ name is a declared parameter name of some
  module of D; (d) every θ value is nonzero; (e) every declared parameter name of every module of D has a θ binding.
* F3 (Tools/ShippingGen4ParamBridgeLegal.lean, approved): `legalBinding_allPos : LegalBinding D θ → AllPos θ`,
  `legalBinding_covers`, `legal_facts` (necessary conditions only).
* `specializeDesign_ok_legal : specializeDesign design θ = .ok D' → LegalBinding design θ`.
* Users: B.P-1 `AllPos θ`; B.P-8 itself; the "declared parameter coverage" row (read as part of B.P-2, see §5);
  `ParamTopShips b D src` and `SpecSuccessAllPositive b D` quantify `∀ θ, LegalBinding (D.addModule b) θ → …`
  (they take legality as a hypothesis and do not need it supplied).

## 2. Which design: `D` or `D.addModule b`

Both appear in the tree; they are not interchangeable.
* `ParamTopShips` and `SpecSuccessAllPositive` are stated on `D.addModule b`.
* `specializeDesign_ok_legal` is for whatever design `specializeDesign` is applied to.
* The real caller of the parametric entry (Sparkle/Compiler/Elab.lean:9126-9130 `synthesizeHierarchicalWithParameters`)
  forms `design' := if design.modules.any (·.name == module.name) then design else design.addModule module`, then
  `#writeParameterizedCppSimDesign` / `#writeParameterizedCudaDesign` (Elab.lean:9198-9200, 9250-9252) pass `design'`
  (after `validateDesignNames`) to `specializeDesign`. So the object that is actually specialized is `design'`, which
  is `D.addModule b`-shaped only when the entry's design does not already contain a module named like the top.
  The entry's `CircuitState` starts from `Design.empty topName` with `topName = ModuleName.ofDecl declName`
  (Builder.lean:59-62), so `topModule` is the top name in both cases; no lemma states this.
* Consequence: the answer to "`D` or `D.addModule b`" depends on the `any`-branch, which the I4-struct lemma
  (`synthesizeCombinationalWithParameters_designTop`) does not decide: it gives `D'.modules = D.modules` only under
  `∀ x ∈ D.modules, x.name ≠ M.name`.

## 3. Where the run is and is not connected to `specializeDesign`

`synthesizeCombinationalWithParameters` (Elab.lean:8940) does NOT call `specializeDesign` or `validateBindings`.
It runs `synthesizeCombinationalCoreWith … symbolicMode := true`, then `dropZeroWidthModule` and (unless
`SPARKLE_NO_REGDEDUP`) `mergeChecked`. `specializeDesign` is called by the command elaborators after the run. So a
returning run does not by itself contain a `validateBindings` success; `specializeDesign_ok_legal` has no premise
that a run can provide. The only way to `LegalBinding` is to derive each of (a)-(e) from checks the entry does perform.
Checks the entry does perform on θ (symbolic mode), by code reading:

| validateBindings clause | entry check found by reading | where |
|---|---|---|
| (b) θ names unique | `hasDuplicate` → `throwError` | Elab.lean:5427-5430 |
| (d) θ values nonzero | `defaultValue == 0` → `throwError` | Elab.lean:5431-5434 |
| (c) θ names declared | each θ name must be in `module.parameters` of the top module | `finishSynth`, Elab.lean:2228-2231; also top-level Nat binder check, Elab.lean:5361-5371 |
| (a) no duplicate declaration (top module) | `CompilerM.addParameter` rejects duplicates | Elab.lean:300-305 |
| (e) every declared name bound (top module) | top-module parameters are added only for binders whose name is a θ name | `bindInputsLegacy`, Elab.lean:2123-2128 |

Not covered by anything found:
* (a), (c), (e) for the modules of the entry design OTHER than the top module (children in `finalCircuitState.design`).
  In symbolic mode `finishSynth` rejects a top body containing `.inst`, but this study did not show that
  `design.modules` is empty of parameterised modules; this is the first open fact.
* Whether `dropZeroWidthModule` / `mergeChecked` preserve `parameters`. By reading, `dropZeroWidthModule` and
  `RegDedup`/`mergeChecked` update only `body`/`wires` (ZeroWidth.lean:113-118) or return `m`/a merge of `m`
  (RefineCheck.lean:260, mergeChecked_cases); `mergeDuplicates` was not read to the end. Not stated in Lean.
* Name normalisation: the entry checks `parameter.name == parameterName` on strings it created itself; `validateBindings`
  uses the same `String`s, so no mismatch is expected, but this is by reading.

## 4. What is missing, as Lean types (stopped here)

Let `Run declName θ (M', D') := RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w'`.
None of the following exists in the tree. Each is a new statement about the existing entry (no production edit).

1. Entry facts on θ (F-θ): `Run … (M', D') → θ.Nodup-by-fst ∧ (∀ p ∈ θ, p.2 ≠ 0) ∧ (∀ p ∈ θ, p.1 ∈ M'.parameters.map (·.name))`.
   Needs: peel `synthesizeCombinationalCoreWith` (guard loop at Elab.lean:5427-5434) and `finishSynth`'s loop. The guard
   loops are `for`-in-`MetaM`; `forIn_yield_each` in ParamBridgeLegal.lean is the style used for the same shape.
   The peel to `synthesizeFromConst` is I3b (`core_symbolic_reads`, already approved); the part after it
   (lambdaTelescope, `emitLeaves`, `bindInputsLegacy`, `finishSynth`) has no lemma.
2. Top declaration facts (F-top): `(M'.parameters.map (·.name))` is duplicate-free and ⊆ `θ.map (·.1)` (clauses (a), (e) for the top).
3. Child facts (F-kids): `∀ x ∈ D'.modules, x.name ≠ M'.name → x.parameters = []`, or the weaker
   `x.parameters.map (·.name) ⊆ θ.map (·.1)` with no duplicates, for the other modules of the design.
4. Parameters survive post-processing (F-post): `(dropZeroWidthModule m).parameters = m.parameters`,
   `(mergeChecked m).parameters = m.parameters`; both are plausibly `rfl`/short, not yet written.
5. The design shape: the `design'` formula of §2 (`if … then design else design.addModule module`) and that
   `topModule` is the top name. This is a statement about `synthesizeHierarchicalWithParameters`, which is outside the
   entry that I4-struct covers (it is a separate `MetaM` function, Elab.lean:9126). It also only matters for
   `ParamTopShips`/`SpecSuccessAllPositive` if those are stated on `D.addModule b`.
6. Assembly: from F-θ, F-top, F-kids, F-post, show `specValidateBindings D'.modules θ = .ok ()`, i.e. unfold the private
   `validateBindings` (mangled-constant style of `specValidateBindings`) and discharge clauses (a)-(e). F3 already
   proves the (b)/(d)-direction consequences in the reverse direction only; the constructive direction is new.

The hard item is F-kids (3) and its link to (a)/(e) for non-top modules: for the declaration shapes where
`finishSynth` forbids instances, this study did not find where `design.modules` could get a parameterised module, but
did not prove there is none either. If F-kids is false for some reachable run, `LegalBinding θ` would not follow from
the run alone; that was not tested (no probe was run in this study; Tests/Gen4/ParamReachProbe.lean runs the entry on
declarations and is the place such a check could be made).

## 5. Ledger effect (per row ID)

If items 1-6 were supplied as Lean theorems with no new assumption (not done in this study):

| Row | Now | If supplied | Note |
|---|---|---|---|
| B.P-8 `LegalBinding D θ` | UN-C, input kept | disappears (-1) | becomes a theorem of the run; `D` vs `D.addModule b` fixed by item 5 |
| B.P-1 `AllPos θ` | UN-C | disappears (-1) | `legalBinding_allPos` already approved; only the run-to-`LegalBinding` link is new |
| declared-parameter coverage row | not 1:1 identified | -0 or -1 | plan reads it as B.P-2 `Bound θ d`; "declared parameter in θ" is a different statement from `Bound θ d` (a bound on dimension expressions). Not confirmed; counted as 0 until the row ID is fixed |
| new rows | | +0 expected | items 1-6 are theorems about the existing entry. They would add Lean work (F-kids may fail), not ledger premises, unless F-kids turns out false and needs a guard on the declaration |

Conditional ledger (expected, not accepted): `条件付き台帳: 見込み B.P-8 -1 / B.P-1 -1 / coverage -0〜1、追加 0。
供給の Lean が未作成のため受入数は変えない`. The accepted line stays `台帳: FG 93 / T1 55（今回 FG -0 +0 / T1 -0 +0）`.
The expected net is -2 (up to -3), conditional on F-kids being provable; if F-kids is not provable the net is 0 and
B.P-8 stays an input condition.

## 6. Recommendation and what the user would decide

No user decision is required by this study: it does not propose a new law, shared-definition change, or scope
reduction. A possible next unit (not started; needs its own freeze with a ledger delta, reviewer's turn because it
touches ledger premises): "entry facts F-θ/F-top/F-post/F-kids as theorems over `RunsTo`" in new files only. Cost: the
peel past `synthesizeFromConst` (lambdaTelescope / `emitLeaves` / `bindInputsLegacy` / `finishSynth`) is the same kind
of work as I3b/I3c, which I3c's record shows was not completed ("no `Start`→`Out0` lemma found"); the estimate is not
measured. If that unit is not run, B.P-8 and B.P-1 stay as they are, and nothing else is affected.

## 7. Not done / limits

* No scratch elaboration and no `#print axioms`: no candidate statement was proved. Reading only (Elab.lean, Specialize.lean,
  Tools/ShippingGen4ParamIface.lean, ShippingGen4ParamBridgeLegal.lean, PARAMETRIC_SPECSUCCESS_DECISION.md).
* All "by reading" entries in §3 are not Lean facts.
* The `pDivOut` W=1 probe in PARAMETRIC_SPECSUCCESS_DECISION.md is about success of `specializeDesign` (T), not legality; it shows
  legality does not imply success, so supplying `LegalBinding` would not supply B.P-5.
