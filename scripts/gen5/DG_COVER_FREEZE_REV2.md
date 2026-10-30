# DG-COVER freeze rev2 — R1 existing-argument invariant, R2 placeholder range and supplier (Issue sparkle-gen5-dg-cover)

**FOR REVIEW — docs only.** Answers the `changes_requested` on rev1 (`ea1b738a`, `DG_COVER_FREEZE_REV1.md`): R1 `PushLetPreserves`, R2 `ReadsOfQuoteStmt`. Base `ea1b738a`, branch `kjob/g5cv-r3`.
Everything in rev1 not mentioned here is unchanged (§0 scope, §1 (A) U-C1..U-C5 as implemented and scoped-approved at `a54446a1`, §3 rows, §4 roadmap, §5 R3 split). Nothing here
completes the Issue, M5 or FG; no guarantee, law, TRUSTED boundary, FG scope or shared definition is changed or proposed. Both new definitions below are `Prop` statements, not theorems.

Wording rule: "not found" = *this survey found no supplier or route*, never "impossible". A "mutant"/rejection by signature or defeq is not a semantic counterexample.
The two counterexamples below were first derived by the reviewer by reading definitions; **they are now checked in the kernel** (`Tests/Gen5/CoverNegCheck.lean`, §3). They are
counterexamples to the *rev1 statements as written* (abstract premise gaps); they say nothing about any state a successful source produces.

## 1. R1 — `PushLetPreserves` (rev1 §2.4) was false

### 1.1 Example (kernel-checked)
`r1Pre = { lets := #[], insts := #[(`c, [0], .bool)] }` (one instance entry whose argument is let 0; no let exists), push `v = machInstOut 0` (value of the new let).
- rev1 `CallOrderInv r1Pre` holds: `LetValuesEarlier`/`LetsInstRange` vacuous (no lets); `ArgsInstBounded` vacuous because `lets[0]? = none` (`r1_pre_rev1_inv`).
- rev1 push premises hold: `v` mentions no let; it mentions instance 0 < `insts.size = 1` (`r1_val_prem_let`, `r1_val_prem_inst`).
- After the push the new let 0 is the argument of entry 0 and mentions instance 0, so `ArgsInstBounded` would need `0 < 0` (`r1_post_not_args_bounded`).
- Hence rev1's `PushLetPreserves` is false (`r1_rev1_push_false : ¬ PushLetPreservesRev1`). Cause: an entry's argument may name a let that is pushed *later*; the later push then
  makes that let an argument of an entry with a smaller index.

### 1.2 Corrected invariant (replaces rev1 `CallOrderInv`; the other rev1 definitions `MentionsPh/MentionsLet/MentionsInst/LetEdge/LetReach/LetValuesEarlier/LetsInstRange/ArgsInstBounded` are unchanged)
```lean
/-- every argument of every pushed instance entry names an existing let. -/
def ArgsExist (st : MachRead) : Prop :=
  ∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder), st.insts[k]? = some (c, js, r) → ∀ a ∈ js, a < st.lets.size

def CallOrderInv (st : MachRead) : Prop :=
  LetValuesEarlier st ∧ LetsInstRange st ∧ ArgsExist st ∧ ArgsInstBounded st
```
`PushInstPreserves` and `PushLetPreserves` keep the rev1 text and are now stated with this `CallOrderInv` (full text: `Tests/Gen5/CoverNegCheck.lean`, the single copy; they are
`Prop` definitions only). The example pre-state is **not** in the new invariant (`r1_pre_not_rev2_inv`), so it is not a counterexample to the rev2 statement. That is all the kernel
check says about rev2: **no proof of `PushLetPreserves`/`PushInstPreserves` exists in this revision, and no other counterexample has been searched for beyond the reviewer's.**

Supplier of `ArgsExist` in the reader: the reader converts an instance's arguments to lets before pushing the entry (Elab.lean 3743, 4062-4068, 4096-4112 as rev1 §2.2). That the
actual steps are instances of `PushInstPreserves`/`PushLetPreserves` is the fuel-twin induction (rev0 W-C), **not proved; this survey found no existing lemma for it**.

## 2. R2 — `ReadsOfQuoteStmt` (rev1 §2.3) was false

### 2.1 Example (kernel-checked)
`nDecl = kI = n = 0`, `k = 1`, `bpos = vpos = fun _ => 0`, `t = boolInput 0`, `v = machLet 1`, `okP = fun _ => false`, `dom = const D []`.
- Range premises `bpos j < 1`, `vpos j < 1` hold (`decide`). `v` has no loose bvar.
- `quote … (boolInput 0) = inputExpr 1 0 = bvar 0` and `machClose 0 0 1 0 (machLet 1) = bvar (1 - 1 - 1 + 0) = bvar 0` (Nat subtraction saturates): the quotation equation holds by `rfl` (`r2_quote_eq`).
- `MentionPos 0 0 0 1 (machLet 1) p` is false for all `p`, since the let placeholder 1 is not `< k = 1` (`r2_mentionPos_empty`), so the `okP` premise is vacuous.
- `reads (fun _ => false) (fun _ => false) (boolInput 0) = false`. So rev1's statement is false (`r2_rev1_false : ¬ ReadsOfQuoteStmtRev1`).
The failure class is exactly: a placeholder *outside* the telescope `machClose` closes against is closed by saturating subtraction to a bvar that can coincide with an input bvar.
For `_machInst j` (`j ≥ kI`), `_machSlot i` (`i ≥ n`), `_machLet j` (`j ≥ k`) the closed index can land inside the range; for `_machIn i` (`i ≥ nDecl`) it lands at `≥ kI+n+k+nDecl`, outside the `bpos/vpos` range.

### 2.2 Placeholder scope (added premise) and fixed supplier
```lean
/-- every placeholder `v` mentions lies inside the telescope `machClose nDecl kI n k` closes against. -/
def PhInRange (nDecl kI n k : Nat) (v : Lean.Expr) : Prop :=
  (∀ i, MentionsPh "_machIn" i v → i < nDecl) ∧ (∀ j, MentionsPh "_machInst" j v → j < kI) ∧
  (∀ i, MentionsPh "_machSlot" i v → i < n) ∧ (∀ j, MentionsPh "_machLet" j v → j < k)
```
`ReadsOfQuoteStmt` (rev2) = rev1's statement with the extra premise `PhInRange nDecl kI n k v →` as first hypothesis after the binders (full text: `Tests/Gen5/CoverNegCheck.lean`).
The example fails this premise (`r2_example_not_in_range`), so it does not refute rev2. Again: **rev2 is a statement; it is not proved, and no further counterexample search was done.**

Suppliers of the four range clauses, fixed (the mapping to the reader state; each is a *obligation*, not a proved fact):
| clause | n/kI/k/nDecl instantiated as | supplier (this survey) |
|---|---|---|
| lets `< k` | `k` = number of lets closed against (`st.lets.size` at that point) | `LetValuesEarlier` (§1.2) for a let value; for a write/result expression, "mentions only pushed lets" — no existing lemma found |
| instances `< kI` | `kI = st.insts.size` | `LetsInstRange` (§1.2) for a let value; same note for write/result |
| slots `< n` | `n` = number of slots of the machine (`st.kinds.size`) | reader: slot placeholders are made by `machSlot i` for `i < kinds.size` — no lemma found |
| inputs `< nDecl` | `nDecl` = declaration binder count | `machIn i` made from binder index `i`; no lemma found |
The premise `hb`/`hv` (`bpos/vpos < nDecl+kI+n+k`) and the quote-side occurrence lemma and quotation witness are unchanged from rev1 §2.3 / R3 (**unsupplied**).

## 3. Kernel check
`Tests/Gen5/CoverNegCheck.lean` (library `Tests.Gen5.CoverNegCheck` in `lakefile.lean`): 10 closed theorems: `r1_pre_rev1_inv r1_val_prem_let r1_val_prem_inst r1_post_not_args_bounded
r1_rev1_push_false r1_pre_not_rev2_inv r2_rev1_false r2_quote_eq r2_mentionPos_empty r2_example_not_in_range`. Pod `kjob lake build Tests.Gen5.CoverNegCheck` exit 0 at `b7ba89f8`
(header commit follows, comment-only); `#print axioms` for each lists only `propext`/`Classical.choice`/`Quot.sound` subsets; no `sorry`, no new axiom, no `native_decide`.
Both rev1 statements were refuted in the kernel, i.e. **both reviewer examples were confirmed**. **The clean build is the coder's**; the Pod build is not the clean-build record.

## 4. Not claimed
- Nothing about any successful run, `dataOf`, `GenWF` on real data, M5, FG. rev1 §6 still applies.
- rev2 `CallOrderInv`/`PushLetPreserves`/`PushInstPreserves`/`ReadsOfQuoteStmt` are unproved statements; "no counterexample found" would only mean this check did not try (only the two reviewer examples were checked).
- R3 rows Q-cmp/Q-snd/Q-wit remain unsupplied (rev1 §5); no decision is requested.
