# Decision material: "specialization succeeds for every positive binding" — issue `sparkle-gen4-parametric-supply`

- **Status:** for the user (coder collects it; the Issue is NOT in `decision`, independent work continues). Revision 2: rewritten after the reviewer's remarks on rev4 (the target and the extra goal are now separate; the classification of declarations is no longer asserted; the earlier code-reading examples are labelled as such).
- **Base:** 3682b80b (branch `kjob/g4par-r6`). Companion: `scripts/gen4/PARAMETRIC_FREEZE.md` §11.1, §13. Wording: "this survey did not find X" = the cited sources were read and X was not there; it never says X is impossible. A code-reading example is not a Lean-checked fact.

## 1. Background (no prior knowledge assumed)
A "parametric" compile (`synthesizeCombinationalWithParameters`, Sparkle/Compiler/Elab.lean:8940) keeps chosen `Nat` arguments of a Lean hardware declaration as module parameters, so a port can have a width like `n + 1`. To use such a design with a fixed-width consumer, `Sparkle.IR.Specialize.specializeDesign` (Specialize.lean:145) substitutes concrete numbers (a "binding" θ) and returns `.error` when some width becomes invalid (underflow, division by zero, zero width, inverted slice). The guarantee has two different parts:

- **(a) behaviour when specialization succeeds** (`ParamTopShips`): if `specializeDesign` returns `.ok` at θ, the specialized module runs as the declaration instantiated at θ. Success is a HYPOTHESIS there. Nothing in this document changes (a).
- **(b) success itself** (`SpecSuccessAllPositive`): "for every legal binding with all values ≥ 1 (and a present top module), `specializeDesign` returns `.ok`".

## 2. Two items that must not be mixed
| | item | where it comes from | status |
|---|---|---|---|
| **T** (FG body, KEPT, not narrowed) | `SpecSuccessAllPositive`: all-positive legal θ ⇒ specialization succeeds | the target recorded since freeze rev2 (R2) as the part of the parametric guarantee beyond (a) | unproved; nothing here narrows it |
| **G+** (additional goal, optional) | a conditional form that uses a premise on the declaration or on θ: `Region`: `∀ θ legal, R θ → success` | proposed in rev4 as a possible weaker companion | not chosen; adds to T, does not replace it |

Reading of FG: the text of FG (GENERAL_SPEC.md:88-100) states the shipped behaviour of a run that succeeded; §M4 (:478-483) says "the parametric quantification" is fixed in M4. This document does not decide whether T is part of what the user approved; it keeps T as a target and records what is and is not supplied.

## 3. What the investigation found (and what it did not)
1. **Code reading, not a run:** the translator can put a user-written `-`, `/`, `%` of a retained parameter into a width (Elab:658, 660-661, 675, 678-679), and `specializeDesign` has error branches for underflow, division/modulo by zero, a zero `.bitVectorDim` and an inverted `.sliceDim` (Type.lean:68-93, Specialize.lean:49-62, 87-88). A width such as `n - 1` at `n ↦ 1` evaluates to 0 by that reading and `specializeType` would throw. This is an example read off the code; it is not kernel evidence and not a claim about every declaration that contains `-`, `/` or `%` (some of those succeed for all positive θ, e.g. when a larger term dominates). No classification of whole declarations is asserted.
2. **New in rev5 — the production functions are `partial`:** `DimExpr.evaluate` (Type.lean:68), `specializeType` (Specialize.lean:56) and `specializeExpr` (:75) are `partial def`s; the Check log lists `specializeExpr` and `specializeType` as opaque constants (body not visible). Consequence: **in Lean, neither success nor failure of the production `specializeDesign` on a concrete width can be proved or refuted today, for any declaration**, including the "good" class. So T is not provable for any class without first supplying a bridge ("Layer B" in the freeze §13.2) between the production functions and a total model of them. This survey did not find a supply path for that bridge.
3. A pure structural induction over a total model (Layer A) is writable, but it proves statements about the model, not about `specializeDesign`.

## 4. Decisions that are the user's (only these)
**D1. Is a bridge for the three `partial` functions acceptable, and in which form?**
| option | what it gives | effect | cost | risk / reversibility |
|---|---|---|---|---|
| 1. None now (default) | (a) as built/planned; Layer A on a model only; T stays an unproved target | no change to any shipped behaviour or file | none | reversible: nothing is committed to; every report must say T is not supplied |
| 2. Production edit: make `DimExpr.evaluate`, `specializeType`, `specializeExpr` total (structural recursion) with the same behaviour | the bridge becomes an equation lemma; T becomes provable for classes such as `PosPlus` (and G+ for others) | users see no change if the edit is behaviour-preserving; it touches `Sparkle/IR/Type.lean` / `Specialize.lean` (production, currently forbidden for this work) | moderate (nested `List`/`mapM` recursion over `Expr` needs care); needs a CSim/backends regression run | needs the user's approval of a production edit; reversible by git revert; data loss: none |
| 3. New trusted equation law (the model equals the production function) | same as 2 without editing production | adds a TRUSTED boundary to the guarantee: the guarantee then rests on the law | small | not approved today; weakens the meaning of the proof; reversible but every downstream statement would cite it |
| 4. Narrow T to a class (user wording change) | T becomes "for the `PosPlus` class" | the guarantee is smaller than the current target | none | NOT proposed by this work; only the user can narrow FG; reversible by restoring the wording |

Recommendation: **1 now**, and **2 if the user wants T proved** (it is the only option that keeps T unnarrowed without a new TRUSTED boundary). Not recommended: 3; 4 is not proposed.

**D2. Add G+ (conditional form) next to T?** Recommendation: **defer until D1 is decided**: any production-level statement of G+ needs the same bridge as T. If D1 = 1, G+ can only be stated about the model. Reversible; adding G+ never removes T.

## 5. If no decision is made
Independent work does not stop: the interface definitions, I3c (outermost symbolic keeps/worlds/balance), I4-struct and the Check are done (freeze §13.1); remaining writable pieces are Layer A (model) and the definitions. Every report must say: (a) is "correct behaviour when specialization succeeds"; T (all-positive success) is NOT supplied; no completeness of the parametric route is claimed.

## 6. Evidence
`scripts/gen4/PARAMETRIC_FREEZE.md` §11.1 (P4 survey, code reading), §13.2-13.4; Sparkle/IR/Type.lean:68-93; Sparkle/IR/Specialize.lean:49-62, 75-92, 145-150; Sparkle/Compiler/Elab.lean:632-687, 856-859; `Tests/Gen4/ParamIfaceCheck.lean` (the opaque-constant log lines at 3682b80b).
