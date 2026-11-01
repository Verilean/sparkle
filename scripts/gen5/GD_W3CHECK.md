# GD-W3CHECK — roadmap §4 W3 check (LetQuoteEq, Bool let, machCanonAp idempotence)

Issue `sparkle-gd-w3check`. Base: par/gd-int f18eb040. Documentation only; no Lean file edited, no ledger change
(ledger FG 102 / T1 54, delta 0/0; C.CV-1 stays "conditional, not counted"). Roadmap: `git show 7c223331:scripts/gen5/GENDATA_ROADMAP.md` §4 W3, §9 D4.

## Result in one paragraph
Of the three points, (iii) is a match by construction, (ii) the `.bool` case adds no problem of its own, but (i) is **false as stated**, and
`LetQuoteEq` needs exactly (i) for every let. So `letQuoteEq_witness` cannot be proved from `dataOfAt_sound` + `shapePost_pack` alone: it needs an
extra fact about the reader's let table ("every stored let value is `machCanonAp`-fixed after `machClose`"). This investigation did **not** find a
reachable reader state that violates it (no semantic counterexample); it also did **not** find a source of that fact. D4 is therefore a *candidate*,
not a confirmed case. Stopped at review as the brief asks for a false/unprovable (ii)-side outcome.

## What was read
* `LetQuoteEq d st` (Cover3.lean:693): `st.lets[j]? = some (nm,kd,v) → quote d.dom bools bits (d.ls[j]).2 = machClose |insts| |kinds| |lets| 0 v` (propositional `=` on `Expr`, so binder names count).
* Producer (Elab.lean:5162-5181): `letFields := st.lets.mapM (machField dom' kind (machClose kI n k 0 value))`, `body := machCanonAp (machPack dom' (letFields ++ outFields ++ slotFields))`.
* `machField dom .bool e = some (1, machBoolBits dom e)`, `machBoolBits dom b = Signal.mux dom (BitVec 1) b 1#1 0#1` (Elab.lean:4293-4299). `unField .bool ⟨_, .mux c _ _⟩ = ⟨.bool, c⟩`, `unField (.bits _)` keeps the term (ShippingMachineCommand.lean:265).
* `machCanonAp` (Elab.lean:5013) recurses through `.app` only and rewrites each node `Signal.ap (Signal.map f a) b` with `inlCanonPi`/`inlCanonLam` (binder names `a`, `x1`, `x2`, …). Commit 27623e79 says why it exists: hand-written `Signal.ap (Signal.map f a) b` (the tests of `circuit do`'s `match`) carry hygienic names and "the body was the quotation of no term".
* `typed_letsAlias` (Tools/Prototype/ReaderFixpointTyped.lean:204) / `peel` / `shapePost_pack` already give, per let `i`: `machCanonAp lfs[i].2 = quote … (d.letFields[i]).2` (field level).

## (i) `machCanonAp (machClose … v) = machClose … v` — false as a general lemma
`machCanonAp` is not the identity on an `Expr` containing `Signal.ap (Signal.map (lam y …) a) b` whose binder names are not the canonical ones.
Scratch computation (outside the source tree, `kjob lake env lean`, `import Sparkle.Compiler.Elab`, an `Expr` built by hand, comparison with `Expr.equal`
because `==` ignores binder names): `machCanonAp (machClose 0 0 0 0 v) ≠ machClose 0 0 0 0 v` for `v` = `Signal.ap D A B (Signal.map D A (∀ y:A, B) (fun y:A => #0) in0) in1`
with `y` non-canonical; the same for the Bool field `machField dom .bool (…)`; and `machCanonAp (machCanonAp v) = machCanonAp v` holds for that `v` (idempotence of the *function* is a different, true-looking statement, not what is needed).
This is a **signature/defeq-level refutation of the lemma on a hand-built Expr, not a semantic counterexample**: it does not show that the reader ever stores such a `v` in `st.lets`.
What is true and probably provable: `machCanonAp (machCanonAp e) = machCanonAp e` (not yet proved in Lean), and `machCanonAp e = e` when `e` is "ap-canonical".

## (ii) Bool let
For `kd = .bool`: field `= mux dom (BitVec 1) (machClose v) 1#1 0#1`; `machCanonAp` of it keeps the `mux` head and canonicalises the arguments, so `unField` returns `c = machCanonAp (machClose v)` (modulo `readN` being the inverse of `quote` on this field, which `dataOfAt_sound` supplies at body level). Hence `quote … (d.ls[j]).2 = machCanonAp (machClose v)` for Bool and for bits alike.
The `machBoolBits` wrapper is **not** the obstruction (the earlier suspicion in the roadmap): it is stripped by `unField`. The obstruction is the same canonical-form gap as (i), for every let kind.
`rowC_of_reader` (Cover3:814) does not treat Bool lets specially: `hq l hldl nm kd v hv_l` is fed to `readsOfQuoteStmt` for every let `l` regardless of `kd`; `cleanLets` is a plain fold over `d.ls`. So the Bool case needs nothing extra there, and `hq` is needed with `=` for each let.

## (iii) binder / domain of C.CV-1 vs `rowC_of_reader`'s `hq`
The Lean side matches by construction: `hq : LetQuoteEq d st` with the `∀ j hj nm kd v` of Cover3:693 (`d`, `st` are the lemma's own variables, `j < d.ls.length` bound by `hj`).
The ledger row text (UN-C, "`LetQuoteEq d st`; reader state `st` is run-local") was **not found** in par/gd-int or par/gen2-spec by `git grep` for "CV-1" in this investigation, so the row-vs-Lean binder comparison is not done. (This investigation did not find where the ledger file lives; that is not a statement that it does not exist.)

## Consequence for W3
`letQuoteEq_witness` as stated in the roadmap has no proof route in what is currently proved. Needed in addition, one of:
* (A) a predicate `LetsCanon st := ∀ j nm kd v, st.lets[j]? = some (nm,kd,v) → machCanonAp (machClose |insts| |kinds| |lets| 0 v) = machClose … v`, proved from the reader trace (R-trace / `FullInv` family, readertrace's domain) — would need a source for it; this investigation found none;
* (B) weaken `LetQuoteEq` to `… = machCanonAp (machClose … v)` and re-prove `readsOfQuoteStmt`'s use (it only needs `reads` of the quote, i.e. position data, which canonical renaming does not change — **not checked**); this changes the FG/ledger row C.CV-1's statement;
* (C) show no reader state stores a non-canonical `v` (reachability), by case analysis over the 4 `lets.push` sites (Elab.lean:3627, 3647, 3671, 3750) — not attempted.

## D4 decision material (candidate; for reviewer)
* **What it is, no background needed.** The generator checks that a let's stored value, after renaming placeholders to de Bruijn indices (`machClose`), equals the let's value re-printed from the typed term (`quote`). The re-printing goes through `machCanonAp`, which renames lambda/pi binder names inside `Signal.ap (Signal.map …) …`. If the stored value kept the user's (macro-hygienic) names, the two differ only in binder names, and `=` on `Expr` sees that.
* **Impact.** W3 (C.CV-1) cannot be turned into a `letQuoteEq_witness` theorem; C.CV-1 stays; W6 (genWF_of_prod) needs `hq`, so it stays conditional on it. Nothing already accepted is affected.
* **Options.** (A) add `LetsCanon` as a new reader-state invariant, proved in readertrace (cost: new invariant in an approved freeze; reviewer approval; no ledger change if it replaces CV-1's content 1:1, +1 if additional). (B) weaken the statement of C.CV-1 (changes an FG row's statement: user decision). (C) a reachability proof (cost: unknown, depends on the 4 push sites + `machNorm`/`inlCanon*`; might fail if a hygienic `ap/map` really is stored).
* **Recommendation.** Do (C) first as a read-only check (small, reversible); if a reachable counterexample exists, choose between (A)/(B), else (A) with its proof from (C). No Lean has been committed for this.
* **Reversible.** Yes for all (new definitions only), except (B) which changes a ledger row.
* **If not decided.** W3/C.CV-1 remains as is (a premise); W1, G0–G2 proceed.

## Not done / not verified
No Lean edited or elaborated except the scratch file above; no clean build; `machCanonAp` idempotence not proved; reachability of non-canonical let values not examined; ledger row text not found.
