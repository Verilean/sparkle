# M4 parametric: bridge unit 4 (`ParamBridgeSpecType`) — freeze, complete types, supplier table

Issue `sparkle-gen4-parametric-supply`, branch `kjob/g4par-r17`, base 6b2bcfa9 (= E1 approved d7892ef6, build parv-d7892ef6, + comment/doc-only BUILT header sync). Docs only; Lean waits for approval of this freeze.
Words: "this survey did not find a route/supplier for X" = the cited sources were read and X was not found; it never says X is impossible or underivable. A "mutant" in a Check is a rejection by signature/defeq, not a semantic counterexample. Nothing here supplies a production I5b fact, discharges T, changes FG, adds a law/TRUSTED boundary, or edits production/shared files. Options of `PARAMETRIC_SPECSUCCESS_DECISION.md` (D1-D3) are NOT adopted. M4 / FG are not complete.

## 1. State of B1-B4 / T / FG (re-checked at 6b2bcfa9; sources: Sparkle/IR/Type.lean:34-93,126-131,190-203; Sparkle/IR/Specialize.lean:18-93; PARAMETRIC_BRIDGE_FREEZE.md §1 probe; UNIT2/UNIT3 freezes; theorem lists of LayerA/BridgeShape/BridgeCompose/BridgeWidth/Iface)
| row | what a proof needs | supplier now | status |
|---|---|---|---|
| B1 `DimExpr.evaluate θ e = evalM θ e` | unfolding/equation lemma of `partial def evaluate` (opaque) | none | **未供給 / この調査で経路未発見** |
| B2 production arm `specializeType` `.bitVectorDim` | B1 + unfolding of `partial def specializeType` | none | **未供給 / この調査で経路未発見** |
| B3 production arm `specializeExpr` `.sliceDim` | B1 + unfolding of `partial def specializeExpr` | none | **未供給 / この調査で経路未発見** |
| B4 private `requirePositive` / `validateBindings` | visibility change (shared-file edit) | none | **未供給 / この調査で経路未発見**; not edited |
| B2' / B3' (model halves) | — | E1 (approved d7892ef6) / D1 (approved 40bc5ec0) | 承認済み（モデル側のみ） |
| T `SpecSuccessAllPositive` | B1-B3 production links + per-declaration success condition | none | **未供給 / この調査で経路未発見**; whether T is part of FG is the user's (decision material exists, not decided) |
| FG connection | T and/or Layer B | none | 未供給 |

Result of this re-survey: no B1-B4 / T row closes from existing lemmas (each needs unfolding of a `partial` opaque function or a visibility change, or a decision D1 option 2/3). The survey did not find a route inside the approved scope; it does not say none exists. No new law / TRUSTED / shared-definition / compiler change is proposed in this unit, so nothing is stopped for a decision here. The pending D1/D3 decision material stays as is.

## 2. Row selected for the next unit: F1 = model-level lift of B2' from one width to a whole `HWType` (not a B1-B4 row)
Why this one: it is the only remaining writable piece that closes from approved lemmas only (`evalM_pos`, E1 `hwTypeFromDim_width_ok`, C2 `hwTypeFromDim_literal`) with no decision and no production edit. It models the clauses of `specializeType` that the width lemma E1 feeds (the `.array` recursion and the `requirePositive` test), so that a later B2 link (if a bridge to `specializeType` is ever supplied) has its model side stated for whole types, not only for a leaf width. **It gives no information about the production `specializeType` and is not counted as progress on B1-B4, T or FG.** Cost: one new file + Check, no new imports beyond `Tools.ShippingGen4ParamBridgeWidth`.

New file `Tools/ShippingGen4ParamBridgeSpecType.lean` (imports `Tools.ShippingGen4ParamBridgeWidth`), check `Tests/Gen4/ParamBridgeSpecTypeCheck.lean`; `lean_lib` entries only in lakefile. Namespace `Tools.ShippingGen4ParamBridgeSpecType`, `open Sparkle.IR.Type Tools.ShippingGen4ParamLayerA Tools.ShippingGen4ParamBridgeShape Tools.ShippingGen4ParamBridgeWidth`.
```lean
-- Total model of `specializeType` (Specialize.lean:56-65), clause by clause; `requirePositive` (:42-44) copied as requirePositiveM. Structural on HWType.
def requirePositiveM (context : String) (value : Nat) : Except String Nat :=
  if value == 0 then .error s!"{context} specializes to zero width" else .ok value

def specTypeM (θ : Binding) (context : String) : HWType → Except String HWType
  | .bit => .ok .bit
  | .bitVector width => .ok (.bitVector width)
  | .bitVectorDim dimension =>
      (evalM θ dimension).bind fun width =>
        (requirePositiveM context width).bind fun w => .ok (hwTypeFromWidth w)
  | .array size elementType =>
      (specTypeM θ s!"{context} element" elementType).bind fun e => .ok (.array size e)

-- every symbolic width inside the type is a PosDim / is Bound
def TyPos : HWType → Prop
  | .bit => True | .bitVector _ => True | .bitVectorDim d => PosDim d | .array _ e => TyPos e
def TyBound (θ : Binding) : HWType → Prop
  | .bit => True | .bitVector _ => True | .bitVectorDim d => Bound θ d | .array _ e => TyBound θ e

-- F1a: model success for whole types
theorem specTypeM_ok {θ : Binding} {t : HWType} (context : String)
    (hp : TyPos t) (hb : TyBound θ t) (ha : AllPos θ) :
    ∃ t', specTypeM θ context t = .ok t'

-- F1b: composition with E1 / C2 on the type the translator builds for a width
theorem specTypeM_hwTypeFromDim {θ : Binding} {d : DimExpr} (context : String)
    (hp : PosDim d) (hb : Bound θ d) (ha : AllPos θ) :
    ∃ w, evalM θ d = .ok w ∧ 0 < w ∧ specTypeM θ context (hwTypeFromDim d) = .ok (hwTypeFromWidth w)
```
Notes: `specTypeM` is a model copied from the text of `specializeType` (do-notation expanded to explicit `bind`, `requirePositive`'s `do/throw/return` to `if`); same error string; it is not claimed equal to `specializeType` (that is B2, unsupplied). Proof plan: F1a by induction on `t` (bitVectorDim: `evalM_pos` then `requirePositiveM` on `0 < w`; array: IH); F1b by `hwTypeFromDim_width_ok` (literal case: `specTypeM` of `hwTypeFromWidth v` is `.ok (hwTypeFromWidth v)` by cases on `v == 1`, `.bit`/`.bitVector`; nonliteral case: the `.bitVectorDim d` clause with `evalM_pos`, then `requirePositiveM` and `hwTypeFromWidth w`). Literal case note: for `.literal v`, `v` may equal 0 only if `¬PosDim`, excluded by `hp`.

## 3. Check (`Tests/Gen4/ParamBridgeSpecTypeCheck.lean`), written from this text
Same requirements as E1's Check. TYPE: `isDefEq` to an independent copy of each statement (2 theorems) and of the two `def` bodies is NOT asserted (defs are checked by the theorem statements only). MUTANT (well-typed single change, same reducible comparator, rejection by signature/defeq only): F1a drop `hp`; `TyBound` -> `TyPos` in the hypothesis; `∃ t'` -> `∃ t', t' = t`; F1b `0 < w` -> `0 ≤ w`; `hwTypeFromWidth w` -> `.bitVectorDim d`; drop `hb`; drop `ha`; swap `evalM θ d` for `evalM [] d`. AXIOMS: propext / Classical.choice / Quot.sound only (both theorems, via `collectAxioms`). CLOSURE: reuse the detector of `ParamBridgeWidthCheck` (explicit `thmInfo/defnInfo` value traversal; unknown names fail; root judged itself; positive and negative controls, including an unknown root, an unknown helper value and an unknown helper type; clean control; fixtures under `withoutModifyingEnv`); opaque constant bodies are not tracked (logged). No `sorry`, no `native_decide`. Real directive counts by kind will be reported with the counting rule (top-level `#...` directive lines per kind). The Check must not import more than the Tool plus `Lean`.

## 4. Open and unchanged
B1-B4, T, Layer B, F1-F6 of the older freeze, source/clock/PostTransfer/FG connection: OPEN. Issue not complete. No guarantee change, compiler change, shared-definition edit, law, or TRUSTED boundary is proposed here. If the reviewer judges F1 not worth doing, the honest alternative is that the supply work waits for the user's D1 decision (`PARAMETRIC_SPECSUCCESS_DECISION.md`); that is not taken unilaterally.
