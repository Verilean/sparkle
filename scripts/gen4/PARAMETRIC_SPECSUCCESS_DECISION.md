# Decision material: "specialization succeeds for every positive binding" (I5b) — issue `sparkle-gen4-parametric-supply`

- **Status:** for the user. Written with PARAMETRIC_FREEZE.md rev4 §11.1. Nothing here is implemented; the freeze does not choose.
- **Base:** 8acc71dd (branch `kjob/g4par-r5`). Wording: "found" means read in the cited sources; a code-reading example is not a run.

## 1. Background (no prior knowledge assumed)
A "parametric" compile (`synthesizeCombinationalWithParameters`, Elab.lean:8940) keeps chosen `Nat` arguments of a Lean hardware declaration as module parameters, so a port may have a width like `n - 1`. To use such a design with a fixed-width consumer, `Sparkle.IR.Specialize.specializeDesign` (Specialize.lean:145) substitutes concrete numbers (a "binding" θ) and returns an error if some width becomes invalid. The proof plan has two parts: (a) IF specialization succeeds at θ, the specialized module runs as the declaration instantiated at θ (`ParamTopShips`, freeze §3.2/§11.5); (b) a separate claim that specialization DOES succeed for every positive θ (`SpecSuccessAllPositive`). Part (b) is a candidate target recorded since freeze rev2 (R2); the reviewer asked not to mistake it for a guarantee FG already demands.

## 2. Finding (rev4 P4, by code reading)
The translator can put `Nat.sub`, `/`, `%` of retained parameters into a width (Elab:658,660-661,675,678-679), and the specializer rejects underflow, division/modulo by zero and zero widths (Type.lean:68-93, Specialize.lean:49-51, :87-88). Example: a wire of type `BitVec (n - 1)` becomes `.sub (.parameter "n") (.literal 1)`; `n ↦ 1` is a legal binding (positive, name matches) but evaluates to width 0 and `specializeDesign` returns `.error`. Hence "success for every positive θ" is FALSE for such declarations as an unconditional statement, and TRUE (provable by induction, not yet proved) for declarations whose widths use only parameters, positive literals, `+ * ^ min max` (class `Pos⁺`, freeze §11.1).

## 3. Why a decision is needed
Part (b) cannot be proved for the whole of FG's parametric domain; to keep part (b) it must be stated with a condition on the declaration (or a region of θ), i.e. be CONDITIONAL. Whether that counts as shrinking the guarantee depends on whether the user reads FG as promising success for all positive bindings; FG's text (GENERAL_SPEC.md:88-100) states only the shipped behavior when a run succeeds, and §M4 (:478-483) says "the parametric quantification" is fixed in M4.

## 4. Options
| option | what is proved | user-visible effect | cost | risk |
|---|---|---|---|---|
| A. Keep only (a) plus the `Pos⁺` class of (b) (recommended) | `ParamTopShips` for every successful specialization; `PosPlus → SpecSuccessAllPositive`; for other declarations success is not claimed | for `Pos⁺` declarations: specialization success AND correct behavior proved; for others: correct behavior WHEN specialization succeeds (the specializer already fails closed, no wrong design) | smallest; induction over `DimExpr` is pure | the statement "every positive θ succeeds" is not given for declarations with `-`, `/`, `%` in widths |
| B. Conditional (b): per declaration a region `R` with `∀ θ legal, R θ → ok` | A plus a proved region (e.g. `n ≥ 2` for `n - 1`) | explicit, checkable preconditions per declaration | needs a region language or a per-declaration premise; larger | a premise per declaration is a guarantee of the same kind as G3 and must be reported as conditional every time |
| C. Change the compiler/specializer so that every positive θ succeeds (e.g. reject `-`,`/`,`%` in widths at translation) | unconditional (b) | some declarations that compile today would be rejected | touches production code, which this work may not do | would need user approval of a compiler behavior change |
| D. Do not decide | A is what gets built; B/C stay open | none now | none | I5b-cond and any FG claim of "all positive θ" stay unproved and are reported as such |

## 5. Recommendation and reversibility
Recommend A now (it is a subset of B and C, loses nothing, and can be extended); B later if the user wants explicit regions. A is reversible: the definitions `SpecSuccessAllPositive`, `PosPlus`, `Region` all stay in the statement list, so B or C can be added without redoing A.

## 6. If no decision is made
Work on A proceeds (it is already part of the rev4 request). I5b-cond and the FG wording for non-`Pos⁺` declarations stay open; every report must say the parametric guarantee is "correct behavior when specialization succeeds" for those declarations. No claim of completeness for the parametric route is made.

## 7. Evidence
scripts/gen4/PARAMETRIC_FREEZE.md §11.1; Sparkle/IR/Type.lean:68-93; Sparkle/IR/Specialize.lean:49-62, 84-91, 145-150; Sparkle/Compiler/Elab.lean:632-687, :858.
