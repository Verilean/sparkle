# M4 parametric: production bridge survey (Layer A model <-> production `DimExpr` evaluation) — freeze, complete types

Issue `sparkle-gen4-parametric-supply`, branch `kjob/g4par-r11`, base a7851a62 (= Layer A approved 0d932e22 + comment-only header sync). Docs only. No Lean of this unit exists yet; Lean waits for approval of this freeze.
Words: "this survey did not find a route/supplier for X" = the cited sources were read and the probe below was run and X was not there; it never says X is impossible or underivable. A "mutant" in any later Check is a rejection by signature/defeq, not a semantic counterexample. Nothing here is a production I5b supply, discharges T, changes FG, adds a law or a TRUSTED boundary, or edits production. The options of `PARAMETRIC_SPECSUCCESS_DECISION.md` (D1 1-4, D2, D3) are NOT adopted by this document.

## 1. Probe (executed observation, scratch file outside the tree, `kjob lake env lean`, Lean 4.32.1)
Imported `Sparkle.IR.Specialize` and ran: `#print Sparkle.IR.Type.DimExpr.evaluate` -> `opaque Sparkle.IR.Type.DimExpr.evaluate : List (String × Nat) → DimExpr → Except String Nat`; `#print Sparkle.IR.Specialize.specializeType` -> `opaque ... : Bindings → String → HWType → Except String HWType`. On `evaluate [] (.literal 3) = .ok 3`: `rfl` fails (not defeq), `decide` fails (no `Decidable` instance), `simp [DimExpr.evaluate]` makes no progress, `unfold DimExpr.evaluate` fails, `DimExpr.evaluate.eq_1` is an unknown constant; the same `rfl`/`unfold` failures for `specializeType b "c" .bit = .ok .bit`. `#print axioms DimExpr.evaluate` shows none. Observed for one term each; it shows that on this build no unfolding or equation lemma for these constants is available to a proof, not that no other route exists. (`specializeExpr` is `partial` too, Specialize.lean:75; not separately probed.)

## 2. Table: model (Layer A, `Tools.ShippingGen4ParamLayerA`) vs production
Names are real; `Bindings = List (String × Nat)` (Specialize.lean:18) and `Binding` (Layer A) are both that type. "closed" = provable from public total definitions without a production edit.

| # | model object | production object (full type) | relation a proof would need | status |
|---|---|---|---|---|
| B1 | `evalM (θ : Binding) : DimExpr → Except String Nat` | `Sparkle.IR.Type.DimExpr.evaluate (bindings : List (String × Nat)) : DimExpr → Except String Nat` (`partial`, opaque) | `∀ θ e, DimExpr.evaluate θ e = evalM θ e` | **未供給 / この調査で経路未発見** (§3) |
| B2 | `evalM`, `Bound`, `PosDim` on a width | `Sparkle.IR.Specialize.specializeType (bindings : Bindings) (context : String) : HWType → Except String HWType` (`partial`, opaque), arm `.bitVectorDim d` = `hwTypeFromWidth <$> (evaluate d >>= requirePositive ctx)` | needs B1 and an unfolding of `specializeType` | **未供給 / この調査で経路未発見** (opaque; depends on B1) |
| B3 | `SliceOK`, `evalM` ordering (`sliceOK_order`) | `Sparkle.IR.Specialize.specializeExpr (bindings : Bindings) : Expr → Except String Expr` (`partial`, opaque), arm `.sliceDim e hi lo` (invalid if `evaluate hi < evaluate lo`) | needs B1 and an unfolding of `specializeExpr` | **未供給 / この調査で経路未発見** |
| B4 | private `requirePositive`, `validateBindings` (`Specialize.lean:36,49`) | same, `private`, total | statement needs visibility change or an unlinked local copy | **未供給 / この調査で経路未発見** (visibility edit is a shared-file change, not made; see freeze §9 U1) |
| B5 | `SliceOK hi lo` (smart `mkSub (mkAdd s l) 1`, `lo = s`) | `Sparkle.Compiler.Elab.makeSliceFromStartLength (source : Sparkle.IR.AST.Expr) (start length : DimExpr) : Sparkle.IR.AST.Expr` and `makeSliceExpr (source) (hi lo : DimExpr) : Sparkle.IR.AST.Expr` (Elab.lean:850-858, total, public) | which `Expr` node the emitter builds for a `SliceOK` pair (so that B3's arm is the one reached) | **closed** (C1 below) |
| B6 | the width positions covered by `PosDim`/`Bound` | `Sparkle.IR.Type.hwTypeFromDim (width : DimExpr) : HWType` and `hwTypeFromWidth (w : Nat) : HWType` (Type.lean:196-203, total, public) | which `HWType` a non-literal width becomes (so that B2's arm is the one reached) | **closed** (C2) |
| B7 | `evalM_mkAdd`, `evalM_mkSub_of_le` (Layer A) | `DimExpr.mkAdd`, `DimExpr.mkSub` (Type.lean:43-52, total) | preservation | **closed** (already proved in Layer A, approved 0d932e22) |
| B8 | (none in Layer A) | `DimExpr.mkMul : DimExpr → DimExpr → DimExpr` (Type.lean:55-61, total): `mkMul (.literal 0) b = .literal 0` drops `b` | `evalM θ (mkMul a b) = evalM θ (.mul a b)` only under `evalM θ a = .ok x ∧ evalM θ b = .ok y` (without it the two can differ: `b` may fail) | **closed** (C3), conditional as stated |
| B9 | I5a (`ParamIface`) | `specializeDesign`/`specializeStmt`/`specializeModuleUnchecked` structure (total) | structure facts not looking at a result of a partial call | already supplied in `Tools/ShippingGen4ParamIface.lean` (not repeated) |
| B10 | `evalM` error strings (`sub`, missing parameter, div/mod by zero, `clog2 0`) | `evaluate` error strings (Type.lean:68-93) | string equality is part of B1 | covered by B1; strings were synchronised in 0d932e22 |

## 3. B1 and what depends on it (the row that does not close; STOP here)
Exact Prop that would be needed (type only, not asserted true or false; no theorem is proposed to be stated with it as hypothesis):
```lean
Sparkle.IR.Type.DimExpr.evaluate θ e = Tools.ShippingGen4ParamLayerA.evalM θ e      -- ∀ θ : List (String × Nat), ∀ e : DimExpr
```
- Impact: until B1 holds (or an equivalent link for `specializeType`/`specializeExpr`), every Layer A statement is about the model only; no statement about `specializeDesign` success (T) follows. B2, B3 depend on it. Stopped rows: none of the closed rows C1-C3 depends on B1.
- This survey did not find a supply route for B1 inside the approved scope (sources: Type.lean:68-93, Specialize.lean:56-130, the probe of §1, `PARAMETRIC_FREEZE.md` §13.2, the existing tests that run `evaluate` only by `#eval`/runtime: Tests/TestCppSim.lean:109,316-324). Routes that would need a decision, listed for the record and NOT chosen: (i) a production edit making the three functions total (decision material D1 option 2); (ii) a new equation law / TRUSTED boundary (D1 option 3). A guarantee change or compiler change is required by B1-B3 only if one of those is taken; nothing is taken here.
- If no decision is made: B1-B3 stay unsupplied; closed rows still make the rest of the bridge precise.

## 4. First unit to implement (after approval of this freeze), and why
Unit `ParamBridgeShape`: rows B5, B6, B8 (C1-C3), the three that close with public total definitions. Why first: they need no decision, they connect the approved model to the nodes the translator actually emits (so the eventual B1 link has exactly one remaining gap), and B8 is the only smart constructor not yet covered by Layer A's preservation lemmas. Cost: the file imports `Sparkle.Compiler.Elab` (already in the closure of `Tools.ShippingGen4ParamEntry`); no edit to it.

New file `Tools/ShippingGen4ParamBridgeShape.lean` (imports `Tools.ShippingGen4ParamLayerA`, `Sparkle.Compiler.Elab`), check `Tests/Gen4/ParamBridgeShapeCheck.lean`; `lean_lib` entries only in lakefile. Namespace `Tools.ShippingGen4ParamBridgeShape`, `open Sparkle.IR.Type Sparkle.IR.AST Tools.ShippingGen4ParamLayerA`:
```lean
-- C1 (B5)
theorem makeSliceExpr_sliceOK {src : Expr} {hi lo : DimExpr} (h : SliceOK hi lo) :
    Sparkle.Compiler.Elab.makeSliceExpr src hi lo = Expr.sliceDim src hi lo ∨
    ∃ a b, hi = DimExpr.literal a ∧ lo = DimExpr.literal b ∧
      Sparkle.Compiler.Elab.makeSliceExpr src hi lo = Expr.slice src a b
theorem makeSliceFromStartLength_eq (src : Expr) (s l : DimExpr) :
    Sparkle.Compiler.Elab.makeSliceFromStartLength src s l =
      Sparkle.Compiler.Elab.makeSliceExpr src (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) s
-- C2 (B6)
theorem hwTypeFromDim_literal (v : Nat) : hwTypeFromDim (DimExpr.literal v) = hwTypeFromWidth v
theorem hwTypeFromDim_nonliteral {d : DimExpr} (h : ∀ v, d ≠ DimExpr.literal v) : hwTypeFromDim d = HWType.bitVectorDim d
-- C3 (B8)
theorem evalM_mkMul {θ : Binding} {a b : DimExpr} {x y : Nat}
    (ha : evalM θ a = .ok x) (hb : evalM θ b = .ok y) : evalM θ (DimExpr.mkMul a b) = .ok (x * y)
```
(`makeSliceExpr` takes `toNat?` of both bounds; `.sliceDim` is built unless both are literals. `Expr.slice`/`Expr.sliceDim` constructor names and argument order are as in Specialize.lean:78-89; the implementation re-checks them against `Sparkle/IR/AST.lean` before writing.) Design note: `evalM_mkMul` is stated with the conclusion `.ok (x*y)` rather than equality with `evalM (.mul a b)`; both are derivable from the other under the hypotheses.

## 5. Check (`Tests/Gen4/ParamBridgeShapeCheck.lean`), written from this text
TYPE: `isDefEq` to an independent copy of each of the five statements above. MUTANT (well-typed single change, same reducible comparator, rejection by signature/defeq only): C1 drop the second disjunct; swap `sliceDim` for `slice`; C2 `.bitVectorDim d` -> `.bitVectorDim (.literal 0)`; drop the `h` hypothesis of `_nonliteral`; C3 `x * y` -> `x + y`; drop `hb`; and, for the conjunct-bearing statement `makeSliceExpr_sliceOK`, a mutant dropping its first disjunct. AXIOMS: propext / Classical.choice / Quot.sound only. CLOSURE: reuse the detector of `ParamLayerACheck` (unknown names fail; root judged itself; negatives for an unknown root / helper value / helper type, clean control, bad fixtures under `withoutModifyingEnv`). No `sorry`, no `native_decide`. Counts will be reported as real numbers with category and counting rule (directive lines per kind).

## 6. Open and unchanged
B1-B4 unsupplied; T, Layer B, F1-F6, source/clock/PostTransfer/FG connection: OPEN. Issue not complete. No guarantee change, compiler change, law, or TRUSTED boundary is proposed here.

## 7. Wording added at approval (no re-freeze; text clarifications only)
- C1 (`makeSliceExpr_sliceOK`) is a structural fact about `makeSliceExpr` (a case split on `toNat?` of both bounds). It does not use the meaning of `SliceOK`; the hypothesis is carried only because the frozen type has it. It is not a semantic check of `SliceOK`.
- Even after B1 (`evaluate = evalM`) is supplied, the link to `specializeType` / `specializeExpr` unfolding (B2, B3) remains a separate obligation each; §4's "exactly one remaining gap" is limited to that sense.
- The `slice` mutants in the Check are well-typed (argument types matched), rejected by signature/defeq only, not semantic counterexamples.
