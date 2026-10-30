# DG-COVER rev3 — implementation record: rev2 preservation lemmas proved, let/instance range suppliers (Issue sparkle-gen5-dg-cover)

Docs only. Base `93a7c331` (rev2, scoped approved), branch `kjob/g5cv-r4`. No type of rev2 is changed: `ArgsExist`, `CallOrderInv`, `PushInstPreserves`, `PushLetPreserves`, `PhInRange`
are the rev2 / `Tests/Gen5/CoverNegCheck.lean` texts, re-stated in `Tools/ShippingGen5Cover2.lean` (the test file is not importable from `Tools`). No guarantee, law, TRUSTED boundary, FG
scope or shared definition changes. **The clean build is the coder's**; the Pod builds below are not the clean-build record. Nothing here completes the Issue, M5 or FG.

## 1. What is proved (`Tools/ShippingGen5Cover2.lean`, Pod `kjob lake build Tools.ShippingGen5Cover2` and `Tests.Gen5.Cover2Check` exit 0)

| name | statement |
|---|---|
| `callOrderInv_of_empty` | `st.lets = #[] → st.insts = #[] → CallOrderInv st` |
| `pushInst_preserves : PushInstPreserves` | rev2 statement, proved |
| `pushLet_preserves : PushLetPreserves` | rev2 statement, proved. Uses `ArgsExist` to keep the pushed index out of every argument, `LetValuesEarlier` to keep `LetReach` inside the old lets (`letReach_push`) |
| `letReach_push`, `letReach_lt` | reachability in `lets.push x` from an old index stays in `lets`; reachability stays below `lets.size` (given `LetValuesEarlier`) |
| `letPh_lt_of_inv`, `instPh_lt_of_inv` | let / instance clauses of `PhInRange` for the value of let `j`: `j ≤ k`, `insts.size ≤ kI` |
| `phInRange_of_inv` | `PhInRange nDecl kI n k v` for let `j`'s value, **with the input and slot clauses as hypotheses** |
| `phInRange_mono` | `PhInRange` is monotone in the four bounds |
| `PushStep`, `PushReach`, `callOrderInv_of_steps` | an invariant-state followed by any sequence of pushes of the premise shape stays in `CallOrderInv` |

`Tests/Gen5/Cover2Check.lean`: 10 theorems against independently spelled `Exp…` statements (only the scanners `MentionsPh` / `LetReach` are shared; the Prop definitions `pushInst_preserves` /
`pushLet_preserves` are compared after unfolding their type); 5 mutants (invariant without `ArgsExist`; `a ≤ lets.size` premise; reversed `j ≤ k`; reversed `kI` bound; reversed `k` in monotonicity)
rejected by signature / defeq comparison — **not semantic counterexamples**; axioms standard only; closure walk (1727 constants, no forbidden constant) with 3 negative and 2 clean controls
(the controls print three "declaration uses `sorry`" warnings from in-memory declarations; the source has no `sorry`).

## 2. Still unsupplied (distinction from rev2 §2.2 kept)

- That the reader's actual steps are `PushStep`s (fuel-twin induction): not proved; this survey found no existing lemma for it. `callOrderInv_of_steps` is only the closure of the invariant under the stated steps.
- `ReadsOfQuoteStmt` (needs the quote-side occurrence lemma and the quotation witness Q-wit): not proved.
- `PhInRange` clauses for `_machIn` (`< nDecl`) and `_machSlot` (`< n`): hypotheses of `phInRange_of_inv`, no supplier. Write / result expressions' ranges: no supplier.
- Q-cmp, Q-snd, Q-wit; reader/write/result/slot/input ranges; dataOf success; `GenWF` rows on real data; fuel twin; production connection. Unchanged from rev2 §4.

## 3. Expr syntax the scan predicates do not cover (R: no claim of exhaustiveness)

`MentionsPh` (and `LooseOcc`, `MentionPos`, `PhInRange`) look at exactly the constructors `machClose` rewrites: placeholder `fvar ⟨.num (.str .anonymous tag) i⟩`, `app`, `lam` (type and body),
`forallE` (type and body). All other constructors are treated as containing nothing: `letE`, `mdata`, `proj`, `mvar`, `bvar` (for `MentionsPh`), `sort`, `const`, `lit`, and `fvar` of any other form.
`machClose` likewise returns those unchanged, so a placeholder nested under `letE` / `mdata` / `proj` is neither seen by the predicates nor closed by `machClose`. Consequently the lemmas here say nothing
about such a placeholder, and **no claim is made that the reader never produces one**; that is part of the unproved reader-side step in §2. A quote bridge proof must either show the reader's output
avoids these constructors or extend the predicates (a new freeze).
