# M4 parametric: bridge unit 5 (`ParamBridgeSpecExpr`) — freeze, complete types, supplier table

Issue `sparkle-gen4-parametric-supply`, branch `kjob/g4par-r20`, base 9a6fbde1 (= F1 approved 10e7df1e, build parv19-10e7df1e, + comment/doc-only BUILT sync). Docs only; Lean waits for approval of this freeze.
**Status (synced after F2 implementation):** F2 (6 mutual defs + `specExprM_ok` / `specExprM_noDim` / `specExprM_startLength`) implemented at 0ebbddc0 and approved; clean build `par21w-0ebbddc0` (Tests.Gen4.ParamBridgeSpecExprCheck) exit 0, 230 jobs. Rows B1-B4 / T / FG are unchanged: 未供給 / この調査で経路未発見. Model-side conditional result only; M4 / FG are not complete.

Words: "this survey did not find a route/supplier for X" = the cited sources were read and X was not found; it never says X is impossible or underivable. A "mutant" in a Check is a rejection by signature/defeq/elaboration, not a semantic counterexample. Nothing here supplies a production I5b fact, discharges T, changes FG, adds a law/TRUSTED boundary, or edits production/shared files. D1-D3 of `PARAMETRIC_SPECSUCCESS_DECISION.md` are NOT adopted. M4 / FG are not complete.

## 1. Supplier table (re-checked at 9a6fbde1; sources: Sparkle/IR/Specialize.lean:18-175, Sparkle/IR/Type.lean:34-93,126-131,190-203, UNIT4 freeze §1, Tools/ShippingGen4Param{LayerA,BridgeShape,BridgeCompose,BridgeWidth,BridgeSpecType,Iface}.lean)
| row | needs | existing lemma that could supply it (real name) | status |
|---|---|---|---|
| B1 `DimExpr.evaluate θ e = evalM θ e` | equation/unfolding of `partial def DimExpr.evaluate` (opaque to the kernel) | none | **未供給 / この調査で経路未発見** |
| B2 `specializeType` arm `.bitVectorDim` | B1 + unfolding of `partial def specializeType` | none (model side: `specTypeM_ok`, `specTypeM_hwTypeFromDim`) | **未供給 / この調査で経路未発見** |
| B3 `specializeExpr` arm `.sliceDim` | B1 + unfolding of `partial def specializeExpr` | none (model side: `startLength_node_ordered`, `sliceOK_order`) | **未供給 / この調査で経路未発見** |
| B4 private `requirePositive` / private `validateBindings` | `requirePositive` is `private def`, not nameable from a new file; `validateBindings` is reachable only through the `specValidateBindings` elab (Iface) | `specializeDesign_ok_legal` (success => `LegalBinding`) is the only direction supplied; the converse and `specializeModuleUnchecked` (private) are not nameable | **未供給 / この調査で経路未発見**; no visibility edit made |
| T `SpecSuccessAllPositive` | B1-B3 production links + per-declaration success | none | **未供給 / この調査で経路未発見**; membership of T in FG is the user's (not decided) |
| FG connection | T and/or Layer B | none | 未供給 |

Result: no B1-B4 / T row closes from existing lemmas; every one needs an unfolding of a `partial` (opaque) function or a visibility change of a shared file, or a D1 option. The survey did not find a route inside the approved scope; it does not say none exists. No new law / TRUSTED / shared-definition / compiler change is proposed here, so nothing is stopped for a decision.

## 2. Unit selected: F2 = model-level lift of D1 (B3') from one slice node to a whole `Expr` (not a B1-B4 row)
Why this one (first of the writable units): it closes from approved lemmas only (`sliceOK_order` D1/LayerA, `startLength_node_ordered` D1, `evalM`/`Bound`/`PosDim`/`SliceOK`/`NonNegDim`) with no decision and no production edit, and it is the exact expression-side counterpart of the approved F1 (type side): F1 modelled `specializeType`, F2 models `specializeExpr` (Specialize.lean:71-93), which is the other half of what a later B2/B3 link would need on the model side. Port lift (`specializePort`) is a 1-line `specTypeM` wrapper and is left for a later unit. **It gives no information about the production `specializeExpr` and is not counted as progress on B1-B4, T or FG.**

New file `Tools/ShippingGen4ParamBridgeSpecExpr.lean` (imports `Tools.ShippingGen4ParamBridgeCompose`), check `Tests/Gen4/ParamBridgeSpecExprCheck.lean`; `lean_lib` entries only in lakefile. Namespace `Tools.ShippingGen4ParamBridgeSpecExpr`, `open Sparkle.IR.Type Sparkle.IR.AST Tools.ShippingGen4ParamLayerA Tools.ShippingGen4ParamBridgeShape Tools.ShippingGen4ParamBridgeCompose`. Complete text:
```lean
-- Total model of `specializeExpr` (Specialize.lean:71-93), clause by clause. The production `arguments.mapM (specializeExpr bindings)`
-- is modelled by the mutual list function (same left-to-right order, first error wins). `evalM` replaces `DimExpr.evaluate` (B1 NOT claimed).
mutual
def specExprM (θ : Binding) : Expr → Except String Expr
  | .const value width => .ok (.const value width)
  | .ref name => .ok (.ref name)
  | .op operator arguments => (specExprsM θ arguments).bind fun a => .ok (.op operator a)
  | .concat arguments => (specExprsM θ arguments).bind fun a => .ok (.concat a)
  | .slice expression hi lo => (specExprM θ expression).bind fun e => .ok (.slice e hi lo)
  | .sliceDim expression hi lo =>
      (evalM θ hi).bind fun concreteHi =>
        (evalM θ lo).bind fun concreteLo =>
          if concreteHi < concreteLo then
            .error s!"invalid specialized slice [{concreteHi}:{concreteLo}]: high bound is below low bound"
          else (specExprM θ expression).bind fun e => .ok (.slice e concreteHi concreteLo)
  | .index array index =>
      (specExprM θ array).bind fun a => (specExprM θ index).bind fun i => .ok (.index a i)
def specExprsM (θ : Binding) : List Expr → Except String (List Expr)
  | [] => .ok []
  | e :: es => (specExprM θ e).bind fun e' => (specExprsM θ es).bind fun es' => .ok (e' :: es')
end

-- every sliceDim in the expression has SliceOK bounds that are Bound under θ (mutual, same shape as specExprM)
mutual
def ExprOK (θ : Binding) : Expr → Prop
  | .const _ _ => True
  | .ref _ => True
  | .op _ arguments => ExprsOK θ arguments
  | .concat arguments => ExprsOK θ arguments
  | .slice expression _ _ => ExprOK θ expression
  | .sliceDim expression hi lo => SliceOK hi lo ∧ Bound θ hi ∧ Bound θ lo ∧ ExprOK θ expression
  | .index array index => ExprOK θ array ∧ ExprOK θ index
def ExprsOK (θ : Binding) : List Expr → Prop
  | [] => True
  | e :: es => ExprOK θ e ∧ ExprsOK θ es
end

-- the output mentions no symbolic slice
mutual
def NoDim : Expr → Prop
  | .const _ _ => True
  | .ref _ => True
  | .op _ arguments => NoDims arguments
  | .concat arguments => NoDims arguments
  | .slice expression _ _ => NoDim expression
  | .sliceDim .. => False
  | .index array index => NoDim array ∧ NoDim index
def NoDims : List Expr → Prop
  | [] => True
  | e :: es => NoDim e ∧ NoDims es
end

-- F2a: model success for whole expressions
theorem specExprM_ok {θ : Binding} {e : Expr} (hok : ExprOK θ e) (ha : AllPos θ) :
    ∃ e', specExprM θ e = .ok e'

-- F2b: every successful model output has no symbolic slice left (no hypothesis on the input)
theorem specExprM_noDim {θ : Binding} {e e' : Expr} (h : specExprM θ e = .ok e') : NoDim e'

-- F2c: composition with D1 on the node the translator builds (`makeSliceFromStartLength`, Compiler/Elab)
theorem specExprM_startLength {θ : Binding} {src : Expr} {s l : DimExpr}
    (hs : NonNegDim s) (hl : PosDim l) (hb : Bound θ s ∧ Bound θ l) (ha : AllPos θ) (hsrc : ExprOK θ src) :
    ∃ e', specExprM θ (Sparkle.Compiler.Elab.makeSliceFromStartLength src s l) = .ok e'
```
(`ExprsOK`/`NoDims`/`specExprsM` are the list companions of the mutual definitions; the auxiliary list-lemmas used inside the proofs, e.g. `specExprsM_ok`, are helpers outside this theorem list. If structural mutual recursion over the nested `List Expr` is rejected by the elaborator, the fallback is `termination_by`/`decreasing_by` with the same statements; the freeze types do not change.)

Proof plan: F2a/F2c by mutual induction on `e` (nested `List` through the list companion); `.sliceDim` clause uses `sliceOK_order` (gives `evalM θ hi = .ok h'`, `evalM θ lo = .ok l'`, `l' ≤ h'`), so the `if` takes the else branch; F2c is `startLength_node_ordered` (both disjuncts) plus `hsrc`. F2b by the same induction on `e` (the only constructor that can leave `.sliceDim` is absent from every output clause).

## 3. Check (`Tests/Gen4/ParamBridgeSpecExprCheck.lean`), same requirements as F1, written from this text
- **Independent Expected**: `ExpSpec`, `ExpSpecs`, `ExpOK`, `ExpOKs`, `ExpNoDim`, `ExpNoDims` are written in the Check from §2 (not by `open`ing the Tool bodies) and compared with the Tool defs by full-argument agreement theorems `∀ θ e, specExprM θ e = ExpSpec θ e`, `∀ θ es, specExprsM θ es = ExpSpecs θ es`, `∀ θ e, ExprOK θ e ↔ ExpOK θ e`, `∀ e, NoDim e ↔ ExpNoDim e` (and the list versions), plus a per-clause equation-statement comparison (specExprM 7 clauses, specExprsM 2, ExprOK 7, NoDim 7) with the same reducible comparator (`withReducible isDefEq` on `inferType`) as the theorem types.
- **Def mutants (well-typed single changes, signature/defeq/elaboration rejections, not semantic counterexamples)** planned 12: `.sliceDim` `concreteHi < concreteLo` -> `concreteHi ≤ concreteLo`; `<` -> `>`; skip the order test; `.slice e concreteHi concreteLo` -> `.slice e concreteLo concreteHi`; `.sliceDim` clause returns `.sliceDim e hi lo` (keeps symbolic); drop the recursive call on `expression` in `.sliceDim`; `.op` clause drops the list recursion; `.concat` clause builds its result with the specialized arguments reversed; `.index` clause drops the `index` recursion; `ExprOK` `.sliceDim` drops `SliceOK`; `ExprOK` `.sliceDim` drops `Bound θ lo`; `NoDim` `.sliceDim .. => False` -> `True`. Counts are plans; the Check reports measured counts by the rule "top-level `#...` directive lines per kind".
- **Theorem types**: `isDefEq` of F2a/F2b/F2c to independent copies; **theorem mutants** planned 8 (drop `ha`; drop `hok`; `ExprOK` -> `NoDim` hypothesis; F2b `.ok e'` -> `.error _`; F2b `NoDim e'` -> `NoDim e`; F2c drop `hsrc`; F2c drop `hl`; F2c `makeSliceFromStartLength` -> `makeSliceExpr`).
- **AXIOMS**: `propext` / `Classical.choice` / `Quot.sound` only, for F2a-c and every agreement theorem (`collectAxioms`). **CLOSURE**: reuse the `ParamBridgeWidthCheck` detector: explicit `thmInfo/defnInfo` value traversal; unknown names fail; root judged itself; positive and negative controls including an unknown root, an unknown helper value and an unknown helper type; clean control; fixtures under `withoutModifyingEnv`; opaque constant bodies are not tracked (logged). No `sorry`, no `native_decide`. The Check imports only the Tool plus `Lean`. The Check is built on the exact tree to be committed. Planned numbers are not results.

## 4. Open and unchanged
B1-B4, T, Layer B, F3 (port/module/design lift), source/clock/PostTransfer/FG connection: OPEN. Issue not complete. No guarantee change, compiler change, shared-definition edit, law, or TRUSTED boundary is proposed. If the reviewer judges F2 not worth doing, the honest alternative is to wait for the user's D1 decision (`PARAMETRIC_SPECSUCCESS_DECISION.md`); that is not taken unilaterally.
