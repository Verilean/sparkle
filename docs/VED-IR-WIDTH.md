# VED IR width: where widths come from, what W costs, and (1)/(2)/(3)

Issue `sparkle-ved-ir-width`, base 4f9b6494. Investigation only; no IR/compiler/printer/statement file is touched.

REVIEW CORRECTION (reviewer, changes_requested on c4c37a5a): the recommendation below is a PROVISIONAL shortest option for the current small examples, to be re-evaluated on a real IP row. The adjustment in §5 is NOT proved; for now a failing `WOKb` means REFUSAL. Work units are unverified estimates; grep file counts are not counts of required changes.

## 1. Where widths come from (file:line)

| constructor | width | where |
|---|---|---|
| `const v w` | `w` (stored) | Sparkle/IR/AST.lean:95, Semantics.lean:56 |
| `ref n` | `we n` (the WEnv; in the statements `declWidth m n`, the WIRE declaration, 0 for ports/undeclared) | Semantics.lean:57, Tools/VedU1Contract.lean:92 |
| `op mux [_,t,_]` | width of `t` | Semantics.lean:58 |
| `op eq/lt*/le*/gt*/ge*` | 1 | Semantics.lean:62 |
| `op not [a]`, `op shr [a,_]` | width of `a` | Semantics.lean:64, :73 |
| other `op` (and/or/xor/add/sub/mul/shl/asr/neg) | max of the operand widths (1 operand: its width) | Semantics.lean:78 |
| `concat as` | sum | Semantics.lean:82 |
| `slice _ hi lo` | `hi-lo+1` (stored in the node) | Semantics.lean:83 |
| `sliceDim`/`index` | 0, evaluator returns `none` | Semantics.lean:84 |

`widthOf` is a pure function of the SYNTAX plus the `ref` leaf widths. Other twins: `inferExprWidth` (Sparkle/Backend/CSim.lean:180, also Verilog, Smt, Optimize, ZeroWidth, CostCmd), `widthOfPartT` (Tools/ConeFold.lean:765), `widthOfPartG` (ConeFoldRT.lean:881), `widthOf` (SVParser/VerifyEmit.lean:74).

Semantics (Semantics.lean:92-160): values are `Nat`, masked to the *context width* `w = widthOf (op ..)`; `not`, `asr`, signed compares and `concat` use the operand's own `widthOf`. `evalAssigns` (Semantics.lean:210) stores the right-hand side value UNMASKED to `we l`: a wire's declared width is used by READERS (`ref`), never to truncate/extend the assigned value. So `assign x(8) = add(a(4),b(4))` stores `(a+b)%16` and every reader sees width 8.
Register next-values are masked to `we out` (regNexts).

## 2. Obstruction (kernel-checked: Tests/Ved/IrWidthProbe.lean, lean_lib `Tests.Ved.IrWidthProbe`)

wire `x : 8 := add(a:4, b:4)`, reader `not x`. The assignment holds (`x = 14` at a=9,b=5), yet
`evalExpr we E (.op .not [.ref "x"]) = some 241` while after inlining `evalExpr we E (.op .not [add a b]) = some 1`
(`widthOf (ref x) = 8`, `widthOf (add a b) = 4`). Theorem `naive_unsound`:

```
def NaiveInlSound : Prop :=
  ∀ (we : WEnv) (E : Env) (A : String → Option Expr),
    (∀ l r, A l = some r → evalExpr we E r = some (E l)) →
    ∀ e, evalExpr we E (not [inline e]) = evalExpr we E (not [e])      -- ¬ NaiveInlSound
```
i.e. `inl_sound` needs `widthOf we r = we l` per inlined assignment (VedComposeResearchCut.lean:124-126). The same effect hits concat shifts, slices of a narrower inlined expression, signed compares, `asr`. An existing control with `concat` is `ctl_width_semantics` (VedComposeResearchCut.lean:692).
Truncation direction (`y:2 := add(a:4,b:4)`): `evalAssigns` stores 14 in a 2-bit wire (`trunc_unmasked`); this is not a Verilog-faithful value, so inlining there is not even the right thing to state: well-formedness (`widthOf r ≤ we l`, stored values masked) is a standing hypothesis of the semantics.

## 3. What W costs today

* Tools/VedComposeConnect.lean (595 lines): W = lines 36-243 (~205 lines, 12 theorems: renE/renL, six `*_map2` lemmas with two width environments, `ren_eval`/`ren_evalL`, `tabW`, `tabW_sound`, `cone_deep_eval`). R is 12 lines (244-255), F 125 lines (446-570); the `flat` machinery (256-445) is width-independent of this issue except `bn` taking `we`.
* ResearchCut: the width-map lemmas `width_op_map/width_concat_map/evalOp_map/evalList_map/foldl_zip_map/go_map` (50-123) and the width conjunct of `inl_sound` (~45 lines) + `WOKb` (456-472, 17 lines, closed Bool).
* Per object cost at use: ONE closed check `WOKb (declWidth m) m b0` per module, ONE `tabW` per cone — no per-leaf proof obligation, `decide`/closed evaluation. (Their cost growth on real modules is not measured; no linear-cost claim is made.)
* Observed (ResearchCut doc comment, scratch runs 54/55): on the returned module of the 9 registered toy modules the only width-inconsistent assignment is the output port `out` (excluded from `Atab`). This is a result on those 9 toys only; it does NOT show that real IP output is width-consistent, and it is not evidence that a specification change is never needed.

So the W cost is already written (~270 lines, kernel-checked in connect1) and the per-instance cost is a closed Bool check. If a real IP produces a wire declared wider/narrower than its RHS, `WOKb` is false and the connection REFUSES (sound failure, not unsoundness); that refusal is the current behaviour.

## 4. Comparison

| | (1) IR unchanged + width-consistency check / explicit adjustment | (2) width-annotated proof-side representation + sound map | (3) IR carries result widths / explicit ext/trunc |
|---|---|---|---|
| change | keep `WOKb`+`tabW` (exists); an inconsistent wire is refused. A later CANDIDATE (unproved): adjust on the proof-side inlining table with `concat [const 0 k, e]` (zero-extend; only the one closed example `ext_ok` is checked) or `slice e (w-1) 0` (truncate; `slc_sound`, VedComposeConnect.lean:279, is slice COMPOSITION, not a proof that truncation preserves the stored value) | new `WExpr` (every node carries width), `toIR`, `widthOf (toIR e) = w` lemma; connection proved on `WExpr` | new Expr constructors/fields, or `resize` node; every consumer changes |
| files/defs touched | 0 existing (new lemma/def in the connect file only) | 0 existing, +1 type, +~6 functions/lemmas, +1 map theorem per `Expr` constructor (7) | `Expr` is matched in ~63 files (`.concat/.slice/...`), `widthOf` in 37 files/1014 lines, `evalExpr` 51 files/957, `evalOp` 29, `declWidth` 46, backends (Verilog, CSim, Smt, Optimize, ZeroWidth), parser/lowering, 6 `deep_fidelity` files, 33 VED files that unfold the IR |
| golden SV/C++ | none | none | at risk: printers and the optimizer (inferExprWidth twins) may change; affected golden outputs/co-sim must be re-verified (extent not measured) |
| guarantee | none (U2HRStmt untouched, `WOKb` is a check not an assumption) | none if the map is proved faithful; adds a trusted-nothing but extra layer between returned IR and statement | must re-prove deep fidelity / U1/U2 for all existing IPs; weakens nothing only after a large migration |
| work (unverified estimates) | ~0 for refusal; the adjustment needs range / positive-width / value-equality lemmas first (estimate not verified) | est. 1.5-2 units (type + map theorem + re-do `ren_eval`/`inl_sound` on it) and it still needs the same check at the IR boundary (the IR-to-`WExpr` map needs `declWidth` anyway) | est. >= 10 units (grep counts above are upper bounds of files mentioning the names, not required changes) |
| removes from connection | nothing, but nothing must be added | W's width side condition moves into the type, but the IR→WExpr translation re-creates it | may remove the W side condition and `WOKb` for explicitly-sized nodes; not shown that all checks disappear |

## 5. Provisional recommendation: (1) (current small examples; re-evaluate on a real IP row)

Reasons: (a) the IR does carry widths where they matter (`declWidth` of the wire declaration, slice and const widths); the issue is that `evalAssigns` does not enforce `widthOf rhs = declWidth lhs` — and that is DECIDABLE and checked by the closed `WOKb`; (b) W is already written; the per-use cost is a closed check; (c) (2) re-implements `WOKb` at the translation boundary and (3) is a large change (extent estimated by grep, not counted) while the final guarantee gains nothing.

Current behaviour: a failing `WOKb` is a REFUSAL. The following is a CANDIDATE only, to be considered after the needed lemmas exist; it is NOT proved: `Atab' x := (asgOf b x).map (adj (declWidth m x))` where `adj w r = if widthOf we r = w then r else if widthOf we r < w then .concat [.const 0 (w - widthOf we r), r] else .slice r (w-1) 0`, with `inl_sound` using `evalExpr (adj w r) = E x`. Missing before it can be used: (i) a RANGE fact for the adjusted wire's value: `needed_range` (R) supplies ranges only for the needed LEAVES (inputs, registers, child outputs), not for arbitrary intermediate wires; `concat` masks each operand to that operand's width, so for a general unmasked `ref`/`mux` the extension case needs `E x < 2 ^ widthOf r`; (ii) the truncation case needs `E x < 2 ^ w` (stored values are unmasked, `trunc_unmasked`) and a value-preservation lemma for `slice`, which does not exist (`slc_sound` is composition only); (iii) width 0 (ports/undeclared names, `declWidth = 0`) needs separate handling. The probe checks the extension case on ONE closed example only (`ext_w`, `ext_ok`), not in general. Note the extension changes the cone shape: the generated `renE τ c = L` equation then has to be stated on the adjusted cone, which is a generator change (VedComposeConnectGen), not a lemma change.

Not doing (3) now; if it is wanted later for other reasons (e.g. making `evalAssigns` mask to `declWidth`), do it as a separate, whole-IR migration issue, not as a compose-connect dependency.

## 6. Files
* Tests/Ved/IrWidthProbe.lean (+ lakefile stanza `Tests.Ved.IrWidthProbe`), kernel-checked, no sorry/axiom/native_decide.
