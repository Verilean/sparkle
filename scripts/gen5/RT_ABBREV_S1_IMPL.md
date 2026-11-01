# RT abbrev S1 implementation record (freeze rev2: `scripts/gen5/RT_ABBREV_S1_FREEZE.md`)

Issue `sparkle-rt-abbrev-s1`. User decision: option A (`scripts/gen5/RT_ABBREV_S1_DECISION.md`, 2026-11-02).
**台帳: FG 100 / T1 55（今回 FG -0 +0 / T1 -0 +0。受理・登録時 T1 56: `ReplaceAgrees` +1、`ZeroLitAgrees0`(T1L-54) −1 降格、`HeadBetaAgrees0` +1）。** 件数はこの文書では計数していない値を推測していない。

## Files (all new; shared definitions, compiler and `N3Extern.lean` untouched; lakefile.lean: 3 `lean_lib` entries added)

| file | content |
|---|---|
| `Tools/Assume/AbbrevExtern.lean` | statements only: `ReplaceAgrees`, `HeadBetaAgrees0`, and the models they mention (`instSpec`, `betaGo`, `betaRevSpec`, `headBetaSpec`). No axiom, no theorem. Docstrings give the C++ / core basis and the limits |
| `Tools/ShippingGen5ReaderTraceAbbrevS1.lean` | `zeroLitAgrees0_of_replace`, `instSpec_noPh`, `instSpec_bvarLt`, `betaGo_good`, `headBetaSpec_good`, `headBeta_good`, `rnc_ph`, `abbrevFn_ph`, `inlAbbrevs_ph` (+ helpers). `DeclValuePh` stays a theorem hypothesis |
| `Tests/Gen5/ReaderTraceAbbrevS1Check.lean` | TYPE / MUTANT / AXIOMS / DEPENDENCY / CLOSURE / RUNTIME |

* `ZeroLitAgrees0` in `Tools/Assume/N3Extern.lean` is NOT removed; its users are unchanged. The re-attachment in the ledger rests on `zeroLitAgrees0_of_replace : ReplaceAgrees → ZeroLitAgrees0`.
* The types are those of freeze §4. In the Check, 3 comparisons are accepted by `isDefEq` (not syntactic) because the freeze's helper `Good a` is spelled out in the independent `Exp…` statements.
* Private core helpers (`getAppRevArgsAux`, `mkAppRevRangeAux`) are reached by the file-local meta helpers `priv%` / `unfold_priv`. Their names carry a numeric component.
* No addendum to the freeze was needed: every type closed as frozen.

## Check output (build of the commit recorded in the file header; Pod `kjob lake build Tests.Gen5.ReaderTraceAbbrevS1Check`, exit 0)

* TYPE 11 declarations compared (9 theorems + 2 assumption Props). MUTANT 8 rejected (signature / defeq rejection, NOT semantic counterexamples). AXIOMS 9 (standard only; `zeroLitAgrees0_of_replace` uses `propext` only). CLOSURE OK: 5708 constants from 9 roots, no `sorryAx` / `ofReduceBool` / `trustCompiler`, controls OK. POSITIVE 6 (2 decide + 4 `#guard`).
* DEPENDENCY (which theorem takes the assumption in its type): `ReplaceAgrees` ← `zeroLitAgrees0_of_replace`, `inlAbbrevs_ph`; `HeadBetaAgrees0` ← `headBeta_good`, `inlAbbrevs_ph`; `DeclValuePh` ← `abbrevFn_ph`, `inlAbbrevs_ph`. The other 5 theorems take no assumption.

## rev2 runtime comparison (re-run; a finite comparison, NOT a proof)

Inside the Check (`run_cmd`), compiled `Expr.replace` / `Expr.headBeta` against `replaceNoCache` / `headBetaSpec` with `Expr.equal`:

* `headBeta` vs `headBetaSpec`: 14 hand-written terms (partial / exact / over application, `mdata` between lambdas, `letE` / `mdata` heads, nested redexes, `proj`, `forallE` bodies), 0 mismatch. Corpus = 6000 constants of the imported `Sparkle.*` / `Tools.*` modules (12000 types and values, first 6000 by name): 35 redex subterms inside the domain `NoPh ∧ BvarLt 0` (all 35 actually reduce), 0 mismatch; 3871 redex subterms with loose bvars (outside the assumed domain, informational), 0 mismatch. In total 49 in-domain comparisons.
* `replace` vs `replaceNoCache`: 5 functions (`abbrevFn env` of the production `inlAbbrevs`, `zeroLitF`, three generic ones) × 12014 terms = 60070 comparisons, 18097 of them changed by the replacement, 0 mismatch. With the environment of the Check `abbrevFn env` changed 93 terms; `zeroLitF` changed 0 (no `BitVec.zero` literal in this corpus).
* No mismatch was found on these inputs. This does not show that the assumptions hold. The corpus contains few user `abbrev`s and few beta redexes in the assumed domain; the sample is small for `headBeta`.

## Not claimed

* `ReplaceAgrees` / `HeadBetaAgrees0` hold: C++ / core reading and the finite comparison above only (limits in the docstrings and freeze §1.3 / §2.4).
* `DeclValuePh` holds for accepted sources; `rounds` / `MachRecUnfold.pass` (S2) are not covered; the composition of `userInliner` is out of scope.
* The Lean commit is not clean-built by the coder yet; ledger update (T1 56) is after acceptance.
