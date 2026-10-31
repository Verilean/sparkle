# M4 parametric: bridge unit 3 (`ParamBridgeWidth`) — freeze, complete types, supplier table

Issue `sparkle-gen4-parametric-supply`, branch `kjob/g4par-r15`, base dc5bf090 (= D1 approved 40bc5ec0 + comment/doc-only BUILT header sync to par14v-40bc5ec0, exit 0, 229 jobs). Docs only; Lean waits for approval of this freeze.
Words: "this survey did not find a route/supplier for X" = the cited sources were read and X was not found; it never says X is impossible or underivable. A "mutant" in a Check is a rejection by signature/defeq, not a semantic counterexample. Nothing here supplies a production I5b fact, discharges T, changes FG, adds a law/TRUSTED boundary, or edits production/shared files. Options of `PARAMETRIC_SPECSUCCESS_DECISION.md` are NOT adopted.

## 1. Row selection among B1-B4 (re-surveyed at dc5bf090)
Sources re-read: Sparkle/IR/Type.lean:34-93 (`mkAdd/mkSub/mkMul`, `partial def evaluate`, `hwTypeFromWidth/hwTypeFromDim`), Sparkle/IR/Specialize.lean:18-93 (`requirePositive` private; `partial def specializeType`, `partial def specializeExpr`), PARAMETRIC_BRIDGE_FREEZE.md §1 (opaque probe), Layer A / C1-C3 / D1 theorem lists.

| row | what a proof needs | supplier now | status |
|---|---|---|---|
| B1 `DimExpr.evaluate θ e = evalM θ e` | unfolding/equation lemma of `partial def evaluate` | none (opaque; probe: no `rfl`/`unfold`/`eq_1`) | **未供給 / この調査で経路未発見** |
| B2 `specializeType` arm `.bitVectorDim` (production side) | B1 + unfolding of `partial def specializeType` | none | **未供給 / この調査で経路未発見** (after B1 a separate unfolding obligation remains) |
| B3 `specializeExpr` arm `.sliceDim` (production side) | B1 + unfolding of `partial def specializeExpr` | none | **未供給 / この調査で経路未発見** (after B1 a separate unfolding obligation remains) |
| B4 private `requirePositive` / `validateBindings` | visibility change = shared-file edit | none | **未供給 / この調査で経路未発見**; not edited |
| B3' (model half of B3) | C1, `sliceOK_order`, Layer A | D1 `startLength_node_ordered` | closed (approved 40bc5ec0) |
| **B2' (model half of B2)**: for a width `d` with `PosDim d` that is bound under an all-positive θ, the `HWType` that `hwTypeFromDim d` produces is the literal-width type or `.bitVectorDim d`, and in the `.bitVectorDim d` case the value the model evaluates `d` to is a positive width (what `requirePositive` in B2's arm would test) | `hwTypeFromDim_literal`, `hwTypeFromDim_nonliteral` (C2), `evalM_pos` (Layer A) | all exist and are approved | **closed by E1 below** (model-level; says nothing about `specializeType` itself) |

Remaining after E1 (unchanged): B1 -> B2/B3 production sides need `specializeType` / `specializeExpr` unfolding -> T. E1 does not shorten B1-B4. Rows that need a production edit (making `evaluate`/`specializeType`/`specializeExpr` total, or exposing the private helpers) or a new law/TRUSTED boundary are not taken; no guarantee/compiler change is needed by E1, so none is proposed and nothing is stopped for a decision in this unit.

First unit to implement: E1 only. Why: it is the only remaining row that closes from approved parts with no decision and no production edit; it mirrors D1 for the type side (B2'), so after B1 both production arms (B2, B3) have their model side already fixed. It adds no information about the production functions and is not counted as progress on B1-B4.

## 2. Unit E1: complete types
New file `Tools/ShippingGen4ParamBridgeWidth.lean` (imports `Tools.ShippingGen4ParamBridgeShape`; no new imports), check `Tests/Gen4/ParamBridgeWidthCheck.lean`; `lean_lib` entries only in lakefile. Namespace `Tools.ShippingGen4ParamBridgeWidth`, `open Sparkle.IR.Type Tools.ShippingGen4ParamLayerA Tools.ShippingGen4ParamBridgeShape`.
```lean
-- E1 (B2')
theorem hwTypeFromDim_width_ok {θ : Binding} {d : DimExpr}
    (hp : PosDim d) (hb : Bound θ d) (ha : AllPos θ) :
    (∃ v, d = DimExpr.literal v ∧ 0 < v ∧ evalM θ d = .ok v ∧
        hwTypeFromDim d = hwTypeFromWidth v) ∨
    ((∀ v, d ≠ DimExpr.literal v) ∧ hwTypeFromDim d = HWType.bitVectorDim d ∧
        ∃ w, evalM θ d = .ok w ∧ 0 < w)
```
Reading: each disjunct is a conjunction of node/type shape and model positivity; dropping either part weakens it. Model-level: `evalM`, not `DimExpr.evaluate`; positivity of `w` is the model analogue of the `requirePositive` test, not a statement about `specializeType`. Proof plan (not asserted yet): case on `d`; literal: `hp : 0 < v`, `rfl`, `hwTypeFromDim_literal`; otherwise `hwTypeFromDim_nonliteral` (constructor discrimination) and `evalM_pos hp hb ha`. No helper lemma planned.

## 3. Check (`Tests/Gen4/ParamBridgeWidthCheck.lean`), written from this text
TYPE: `isDefEq` (one `withReducible` comparator) to an independent copy of the statement. MUTANT (well-typed single change, signature/defeq rejection only): drop the type-shape conjunct of disjunct 1 (`hwTypeFromDim d = hwTypeFromWidth v`); drop the positivity conjunct `0 < w` of disjunct 2; `0 < w` -> `w = 0`; drop `evalM θ d = .ok v` of disjunct 1; replace `.bitVectorDim d` by `.bitVectorDim (.literal 0)`; drop `hp`; drop `ha`; drop disjunct 2 (leaving the literal case only). AXIOMS: propext/Classical.choice/Quot.sound only. CLOSURE: reuse the detector of `ParamBridgeComposeCheck` (unknown names fail; root judged itself; negatives for unknown root / helper value / helper type + clean control, bad fixtures under `withoutModifyingEnv`); limitation unchanged: opaque bodies (`evaluate`, `specializeType`, `specializeExpr`) are not followed by the `getUsedConstants`-based closure. No `sorry`/`native_decide`. Counts reported as real numbers with category and counting rule (top-level `#...` directive lines per kind); the Check build is run on the exact tree that is committed before committing.

## 4. Open and unchanged
B1-B4, T, Layer B, F1-F6, FG connection: unsupplied. No guarantee change, compiler change, shared-definition edit, law or TRUSTED boundary is needed by E1 or proposed. Issue not complete.
