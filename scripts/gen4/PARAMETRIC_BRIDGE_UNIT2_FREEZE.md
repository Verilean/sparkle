# M4 parametric: bridge unit 2 (`ParamBridgeCompose`) — freeze, complete types, supplier table

Issue `sparkle-gen4-parametric-supply`, branch `kjob/g4par-r13`, base 4a13204e (= C1-C3 approved 2f421f4f + comment-only BUILT header sync to par12v-2f421f4f, exit 0, 228 jobs). Docs only; Lean waits for approval of this freeze.
Words: "this survey did not find a route/supplier for X" = the cited sources were read and X was not found; it never says X is impossible or underivable. A "mutant" in a Check is a rejection by signature/defeq, not a semantic counterexample. Nothing here supplies a production I5b fact, discharges T, changes FG, adds a law/TRUSTED boundary, or edits production/shared files. Options of `PARAMETRIC_SPECSUCCESS_DECISION.md` are NOT adopted.

## 1. Row selection among B1-B4 (what existing parts + C1-C3 close)
| row | what it needs | supplier now | status |
|---|---|---|---|
| B1 `DimExpr.evaluate θ e = evalM θ e` | unfolding of opaque `partial def evaluate` | none (probe in PARAMETRIC_BRIDGE_FREEZE §1) | **未供給 / この調査で経路未発見** |
| B2 `specializeType` arm `.bitVectorDim` | B1 + unfolding of opaque `specializeType` | none | **未供給 / この調査で経路未発見** (after B1, a separate unfolding obligation remains) |
| B3 `specializeExpr` arm `.sliceDim` | B1 + unfolding of opaque `specializeExpr` | none | **未供給 / この調査で経路未発見** (after B1, a separate unfolding obligation remains) |
| B4 private `requirePositive`/`validateBindings` | visibility change (shared-file edit) | none | **未供給 / この調査で経路未発見**; not edited |
| B3' *model-side half of B3*: for the node the translator actually emits for a start/length slice, the bounds that B3's arm would evaluate are well-ordered, and in the all-literal case (`.slice`, which `specializeExpr` passes through unchecked) the literal bounds are ordered | `makeSliceFromStartLength_eq` (C1 file), `makeSliceExpr_sliceOK` (C1), `sliceOK_order`, `evalM_mkAdd`, `evalM_mkSub_of_le`, `evalM_pos`, `evalM_nonneg` (Layer A) | all exist and are approved | **closed by D1 below** (model-level; says nothing about `specializeExpr` itself) |

Remaining after D1, stated as rows: B1 (evaluate = evalM) -> B3 needs `specializeExpr` unfolding on `.sliceDim` -> T. D1 does not shorten B1/B2/B3/B4; it only fixes the model-side shape that B3 will later be applied to. First unit: D1 only (D1 is the only row that closes from existing approved parts without a decision or production edit).

## 2. Unit D1: complete types
New file `Tools/ShippingGen4ParamBridgeCompose.lean` (imports `Tools.ShippingGen4ParamBridgeShape`; no new imports), check `Tests/Gen4/ParamBridgeComposeCheck.lean`; `lean_lib` entries only in lakefile. Namespace `Tools.ShippingGen4ParamBridgeCompose`, `open Sparkle.IR.Type Sparkle.IR.AST Tools.ShippingGen4ParamLayerA Tools.ShippingGen4ParamBridgeShape`.
```lean
-- helper lemmas (outside the statement list; forward direction of the existing Bound_mkAdd/Bound_mkSub)
theorem Bound_of_mkAdd {θ : Binding} {a b : DimExpr} (ha : Bound θ a) (hb : Bound θ b) : Bound θ (DimExpr.mkAdd a b)
theorem Bound_of_mkSub {θ : Binding} {a b : DimExpr} (ha : Bound θ a) (hb : Bound θ b) : Bound θ (DimExpr.mkSub a b)

-- D1 (B3')
theorem startLength_node_ordered {θ : Binding} {src : Expr} {s l : DimExpr}
    (hs : NonNegDim s) (hl : PosDim l) (hb : Bound θ s ∧ Bound θ l) (ha : AllPos θ) :
    (Sparkle.Compiler.Elab.makeSliceFromStartLength src s l =
        Expr.sliceDim src (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) s ∧
      ∃ h' l', evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = .ok h' ∧
        evalM θ s = .ok l' ∧ l' ≤ h') ∨
    (∃ a b, Sparkle.Compiler.Elab.makeSliceFromStartLength src s l = Expr.slice src a b ∧
        evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = .ok a ∧
        evalM θ s = .ok b ∧ b ≤ a)
```
Reading: the conjunction in each disjunct is the content (node shape AND ordering in the model); dropping either conjunct weakens it. This is model-level: `evalM`, not `DimExpr.evaluate`; the `.slice` disjunct says the literal bounds the translator froze are ordered in the model, not that `specializeExpr` checks anything. Proof plan (not asserted yet): `makeSliceFromStartLength_eq`, `makeSliceExpr_sliceOK` applied with `SliceOK` witnessed by `⟨s, l, rfl, rfl, hs, hl⟩`, `sliceOK_order` with `Bound` from the helpers; the literal disjunct transports `evalM θ (.literal a) = .ok a` by `rfl`/simp.

## 3. Check (`Tests/Gen4/ParamBridgeComposeCheck.lean`), written from this text
TYPE: `isDefEq` (one `withReducible` comparator) to an independent copy of the three statements above (helpers included as type checks). MUTANT (well-typed single change, signature/defeq rejection only): D1: drop first conjunct of disjunct 1 (node shape); drop the ordering conjunct `l' ≤ h'`; change `l' ≤ h'` to `h' ≤ l'`; swap `sliceDim` for `slice` with matching argument types; drop `hl`; drop `hs`; drop `ha`; helpers: `mkAdd`->`mkSub` in the conclusion, drop `hb`. AXIOMS: propext/Classical.choice/Quot.sound only. CLOSURE: reuse the detector of `ParamBridgeShapeCheck` (unknown names fail; root judged itself; negatives for unknown root / helper value / helper type + clean control, bad fixtures under `withoutModifyingEnv`); limitation unchanged: opaque bodies (`evaluate`, `specializeType`, `specializeExpr`) are not followed by the `getUsedConstants`-based closure. No `sorry`/`native_decide`. Counts reported as real numbers with category and counting rule (top-level `#...` directive lines per kind); the Check build is run on the exact tree that is committed before committing.

## 4. Open and unchanged
B1-B4, T, Layer B, F1-F6, FG connection: unsupplied. No guarantee change, compiler change, shared-definition edit, law or TRUSTED boundary is needed by D1 or proposed. Issue not complete.

## 5. Wording sync at implementation (g4par-r14; no re-freeze)
- `Bound_of_mkAdd` / `Bound_of_mkSub` are the forward direction (components bound => combination bound), the reverse of Layer A's `Bound_mkAdd` / `Bound_mkSub`.
- The `sliceDim` -> `slice` mutant is counted only as the well-typed statement with literal bounds `0 0`; ill-typed variants are not counted. Mutants are signature/defeq rejections, not semantic counterexamples.
- Implemented unchanged from §2: `Tools/ShippingGen4ParamBridgeCompose.lean`, `Tests/Gen4/ParamBridgeComposeCheck.lean` (no extra lemma, no extra hypothesis). Pod build of Tools + Check (exit 0, 229 jobs) is not a clean issue-linked build.
