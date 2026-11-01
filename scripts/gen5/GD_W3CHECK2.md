# GD-W3CHECK2 — reachability of non-canonical let values (follow-up to GD_W3CHECK.md)

Issue `sparkle-gd-w3check`, agent gdw3b. Base `kjob/gdw3` 2e17b3a1. Documentation only; no Lean file in the repo edited, no ledger change
(ledger FG 102 / T1 54, delta 0/0; C.CV-1 stays "conditional, not counted"). Scratch Lean files were elaborated outside the source tree.

## Conclusion: (B) — a reader-reachable counterexample exists; D4 is confirmed as a decision item
`LetQuoteEq` needs, for every stored let `v`, `machCanonAp (machClose … v) = machClose … v` (see GD_W3CHECK.md (i)). The reader does store non-canonical `v` for an
ordinary `circuit do` source (below). So the extra fact "every stored let is `machCanonAp`-fixed" is **false on reachable states**, not merely unproved.
Caveat on strength: this is shown on the production reader's output (stored `v`, packed body bytes). I did not elaborate `dataOfAt` to build `d` and evaluate `LetQuoteEq d st`
itself; the step "quote of the let field = the body's (canonical) subterm" is `shapePost_pack`/`dataOfAt_sound` (GD_W3CHECK.md) and is taken from there.

## 1. The four `lets.push` paths (Elab.lean; the fuel reader Tools/ShippingReaderFuelDefs.lean calls the same helpers)
Every pushed value is an output of `machConv` (the reader's converter), taken BEFORE `machClose` and BEFORE `machCanonAp` (`machCanonAp` is applied once, to the whole packed body, Elab.lean:5180).
`machConv` rebuilds `.app` nodes and keeps `.lam` binder names (Elab.lean ~3973), so user/macro binder names survive into `v`.

| # | helper (line) | pushed `v` | callers: production (fuel) | reached? |
|---|---|---|---|---|
| 1 | `machBindLet` (3627) | `v'` = `machConv` of the `let` value (not a bare var, not already stored) | 4009, 4174, 4187/5130 (fuel 378, 527, 542-544) | **yes**: scratch `w1`, `w3` |
| 2 | `machBindLetNamed` (3647) | `v'` with `machIsSlot v'`, i.e. an `fvar _machSlot i`; or (from path 3's fallback) an `fvar _machLet` | 4187, 5130 (fuel 542) | reached only for hand-written `Signal.loop` bodies (not exercised); value is a bare `fvar`, so `machCanonAp` fixes it trivially |
| 3 | `machBindLetAlias` (3671) | `val` = the stored definition of an earlier let (resolved through `_machLet` chain) — i.e. a value already pushed by path 1/4 | 4188 (fuel 543) | reached only in `Signal.loop` bodies (not exercised); its range is a subset of path 1/4 values, so it is non-canonical iff those are |
| 4 | `machLetIndex` (3750) | `v'` = `machConv` of an instance argument (`@[hardware_module]` call, struct call, memory call) | 4070, 4110 (fuel 422, 453) | **yes**: scratch `inst1`, `inst2` |

## 2. Reachable counterexample (read by the real `machineShape?`; scratch copy `machineShapeDbg` is byte-identical code, and its `body` equals the real one: `real==dbg body true`)
```lean
def w3 (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let t := Signal.ap (Signal.map (fun a b => a == b) x) y
    r <~ Signal.mux t x y
    return r
```
Reader result: `lets = 1`, stored `v = (Signal.map (fun a b => a == b) _machIn.1).ap _machIn.0` — `Expr.equal (machCanonAp v) v = false` (binders `a b` vs canonical `x1 x2`).
The shape body (after `machCanonAp`) has `fun x1 x2 => x1 == x2` in the let field; the pre-canon packed value has `fun a b => …`. Same for `w1` (`(· == ·)` with hygienic names)
and for a call argument (path 4): `inst1`/`inst2` = `toggle (Signal.ap (Signal.map (fun a b => a == b) x) y)` → stored `inst0_arg0` non-canonical.
Controls (canonical, `machCanonAp v = v`): `x === y`; `(· == ·) <$> x <*> y` (the `<$>`/`<*>` normaliser already canonicalises); scalar lifts such as `Signal.ap (Signal.map (fun p q => (p+q)*3#8) x) y`
(`machNormAp`/`machLiftScalarN` turn them into gates, no `ap` left). A lambda the normaliser cannot lift (`if p < q then p else q`, `decide (p < q)`) gives "no machine shape" (not read, so not a counterexample).
Bool let is not special: `w3` is a Bool let (its field is `mux t 1 0`).

Corpus scan (scratch, the imported modules only: every `defnInfo` with prefix `Sparkle` — 428 machine-shaped declarations, 155 with lets, incl. Tests and Display — and `Tests`: 38): **0** declarations store a non-canonical let.
(`IP.*` imported demos matched 0 declarations under that prefix scan, so they were not covered.) So no current corpus declaration is a counterexample; the issue is for user sources like `w3`, which the reader accepts.
This is a statement about the scanned set only, not about all sources.

## 3. `machCanonAp` idempotence
`machCanonApNode` only renames `lam` binders by depth (`inlCanonLam`) and `forallE` binders to `a` (`inlCanonPi`); applying it twice gives the same node. So `machCanonAp (machCanonAp e) = machCanonAp e` should hold by structural induction
(the recursion enters `.app` only). **Not proved in Lean in this investigation** (no Lean committed). It is not what `LetQuoteEq` needs (see GD_W3CHECK.md (i)).

## 4. C.CV-1 ledger text vs `LetQuoteEq` vs `rowC_of_reader`'s `hq` — same
Ledger (`kjob/fgnext2` 500c0370, scripts/gen2/premise_ledger/C_M5dg.md §8 CV-1): `LetQuoteEq (d : MachineData) (st : MachRead) : Prop := ∀ (j : Nat) (hj : j < d.ls.length) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → quote d.dom (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.bpos i)) (fun i => inputExpr (… ) (d.vpos i)) (d.ls[j]'hj).2 = machClose st.insts.size st.kinds.size st.lets.size 0 v`.
`Tools/ShippingGen5Cover3.lean:693` has the same binders (`j hj nm kd v`), the same domain (`j < d.ls.length`, `st.lets[j]?`), and the same equation. `rowC_of_reader` (Cover3:815) takes `hq : LetQuoteEq d st` and applies `hq l hldl nm kd v hv_l` (Cover3:844): same.
So the ledger row states exactly the statement shown false-on-reachable-states above.

## D4 decision material
* **What it is, no background needed.** The generator reads a `circuit do` program, stores each `let` value the reader meets, and later checks that the stored value (placeholders renamed to de Bruijn indices) equals the same value re-printed from the typed term.
  The re-printing goes through a step (`machCanonAp`) that renames the lambda/pi binder names inside `Signal.ap (Signal.map f a) b` to fixed names. A program that writes such a `Signal.ap (Signal.map (fun a b => …) x) y` itself in a `let` or an instance argument keeps `a b` in the stored value but gets `x1 x2` in the re-print, and `=` on `Expr` compares binder names. So the stated check is false for such programs, which the reader accepts.
* **Impact.** C.CV-1 as written is false for reachable reader states; W3 `letQuoteEq_witness` and hence `rowC_of_reader`'s `hq` for W6 (`genWF_of_prod`) cannot be proved from the current statement. Nothing already accepted is affected (the premise is an assumption; no accepted theorem derives from a false instance unless it is applied to such a run).
* **Options (all need user approval; none changes ledger counts by itself).**
  1. Weaken C.CV-1's right-hand side to `machCanonAp (machClose … v)`. Changes one FG row's statement (user decision). Cost: re-check `rowC_of_reader`'s use of `hq` (it feeds `readsOfQuoteStmt`, which needs positions, which renaming does not change — **not checked**); then the witness needs `shapePost_pack`-style field lemma + canon of `machField`. Counts: 0 net (statement replaced 1:1).
  2. Make the reader canonicalise on push (`lets.push (…, machCanonAp v')`). Edits the production reader (compiler/shared definition: prohibited without approval) and the fuel reader; then `LetsCanon` still needs idempotence + `machCanonAp`/`machClose` commuting. Counts: possibly +1 (new invariant) −0.
  3. Restrict the covered programs (exclude non-canonical lets). Shrinks FG: not allowed without approval; no reason to prefer it.
* **Recommendation.** Option 1 (smallest, local to the statement; the quote side is already canonical).
* **Reversible?** Option 1 and 3: yes (statement change in a doc/def, git-revertible). Option 2: yes in git, but touches the compiler.
* **If not decided.** C.CV-1 stays an unsupplied premise that is false on some reachable states; W6 stays conditional on it; W1, G0–G2 proceed.

## Not done / not verified
`dataOfAt` was not elaborated on `w3` (so `LetQuoteEq d st` itself was not evaluated); path 2 and 3 not exercised with a hand-written `Signal.loop`; `machCanonAp` idempotence not proved; the option-1 side condition (`readsOfQuoteStmt` insensitive to canonical renaming) not checked; no clean build (no repo Lean changed).
Mutants/counterexamples here are real reader runs on `circuit do` sources, but the final step to `LetQuoteEq d st` is by `shapePost_pack`, not recomputed.
