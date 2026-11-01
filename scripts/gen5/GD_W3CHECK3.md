# GD-W3CHECK3 — `dataOfAt` evaluated on `w3`: `LetQuoteEq d st` is false on a real run (follow-up to GD_W3CHECK2.md)

Issue `sparkle-gd-w3check`, agent gdw3c. Base `kjob/gdw3b` a9be259a. Documentation only; no repo Lean file edited, no ledger change
(ledger FG 102 / T1 54, delta 0/0; C.CV-1 stays "conditional, not counted" until the user decides D4). Scratch Lean was elaborated outside the source tree.

## Conclusion: (A) — a counterexample in the real quantification domain (`dataOfAt = some d`, same run's `st`)
Reviewer's open point in GD_W3CHECK2: "`dataOfAt` was not evaluated on `w3`". It is now. For `w3` (source below) and for a path-4 variant, `dataOfAt` returns `some d`,
and for that `d` and the reader state `st` of the same run, the instance `j = 0` of `LetQuoteEq d st` fails: the two `Expr`s differ in lambda binder names.

## 1. Setup (what was run)
* `st`: a scratch copy `machineShapeDbg` of `Sparkle/Compiler/Elab.lean` `machineShape?` (lines 5072–5200, copied by `sed`; only change: it returns `(shape, st)`).
  Check printed `realBodyEq = some true`: the copy's `shape.body` equals the production `machineShape?` body, for both examples. `st` is the final `MachRead` of that run,
  the same one whose `lets` G1's `stateSide_of_production` / `machineShapeF` witness talks about.
* `d`: `dataOfAt (fun _ => 1000000) entry senv sp` (`Tools/ShippingGen5DataOf.lean:134`), with `entry := entryConst true false [] ci (instancePredicate env) (userInliner env) senv`
  and `senv := structEnv env` as in `readMachine` (`Tools/ShippingMachineCommand.lean:440+`), `sp` = the copy's shape. `lvl` is the fuel for `readN`; a large constant was used
  (`dataOfAt_sound` holds for every `lvl`; with this `lvl` the result is `some`; which `lvl` the final pipeline supplies was not checked here).
* The comparison is exactly the `LetQuoteEq` body (`Tools/ShippingGen5Cover3.lean:693`) at `j`, with
  `K := kDOf d + st.insts.size + st.kinds.size + st.lets.size`:
  `quote d.dom (fun i => inputExpr K (d.bpos i)) (fun i => inputExpr K (d.vpos i)) (d.ls[j]).2` versus `machClose st.insts.size st.kinds.size st.lets.size 0 v`, where `st.lets[j]? = some (nm, kd, v)`.

## 2. Results
Source (the GD_W3CHECK2 `w3`):
```lean
def w3 (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let t := Signal.ap (Signal.map (fun a b => a == b) x) y
    r <~ Signal.mux t x y
    return r
```
| run | `dataOfAt` | `d.ls.length` / `st.lets.size` | `j=0` quote side | `j=0` `machClose … v` | `Expr.equal` | lam binder names (quote / stored) |
|---|---|---|---|---|---|---|
| `w3` (path 1) | `some d` | 1 / 1 | `(Signal.map (fun x1 x2 => x1 == x2) #3).ap #2` | `(Signal.map (fun a b => a == b) #3).ap #2` | **false** | `[x1,x2]` / `[a,b]` |
| `inst1` (path 4) | `some d` | 1 / 1 (`st.insts.size = 1`, `nm = inst0_arg0`) | `(Signal.map (fun x1 x2 => x1 == x2) #4).ap #3` | `(Signal.map (fun a b => a == b) #4).ap #3` | **false** | `[x1,x2]` / `[a,b]` |
| control `w3c` (`let t := x === y`) | `some d` | 1 / 1 | `#3 === #2` | `#3 === #2` | true | — |

`inst1` is `w3` with the `let` value passed to a `@[hardware_module] def tog (e : Signal defaultDomain Bool)` (`circuit do let r ← Signal.reg false; r <~ Signal.mux e (Signal.map (fun b => !b) r) r; return r`) and `let c := tog (Signal.ap (Signal.map (fun a b => a == b) x) y); r <~ Signal.mux c x y`.
Only the binder names differ (`Expr.equal` is strict about them; Lean's `==` on `Expr`, `Expr.eqv`, ignores them and printed `true`, which is why the printed terms look equal up to the `fun` names).
Since the binder name is a field of the `Expr.lam` node, the two terms are different as Lean values (names `x1`, `x2` vs `a`, `b`), so `quote … = machClose … v` is false at `j = 0`.
Also printed: `machCanonAp (machClose … v)` equals the quote side (`Expr.equal = true`) in both rows, i.e. the weakened right-hand side of D4 option 1 holds on these two instances.

Why this is the cause: `shape.body = machCanonAp packed` (`Elab.lean:5180`), and `dataOfAt` reads `d.ls` from `shape.body`, so the quote side is canonical; the stored `v` was pushed by the reader BEFORE `machCanonAp` (GD_W3CHECK2 §1).

## 3. Status of the earlier statements
* GD_W3CHECK2 §2 (stored `v` non-canonical on reader runs) is now backed through `dataOfAt` for paths 1 and 4: in the quantification domain of C.CV-1 (`dataOfAt = some d`, `st` of that run) the equation is false.
* Not shown: paths 2/3 (`Signal.loop` bodies), anything about programs other than these two. The corpus scan of GD_W3CHECK2 (0 non-canonical lets among 466 scanned declarations) still says no existing corpus declaration is affected.
* The evaluation is a computation on real reader/`dataOfAt` code (the copy of `machineShape?` is verified body-equal only); it is not a Lean proof of `¬ LetQuoteEq d st` (no theorem was written).
* `st` comes from the copy, not from the production function (which does not return it). `lvl` is a constant as stated above.

## D4 decision material (replaces GD_W3CHECK2's, same content, now with the `dataOfAt` evidence)
* **What it is, no background needed.** The generator reads a `circuit do` program, stores each `let` value it meets, and a later statement (C.CV-1 / `LetQuoteEq`) says that value, re-printed from the typed term that `dataOfAt` reads off the machine body, equals the stored value.
  The body is passed through `machCanonAp`, which renames lambda binder names inside `Signal.ap (Signal.map (fun a b => …) x) y` to `x1 x2`; the stored value is taken before that and keeps `a b`. `=` on `Expr` compares binder names, so for such programs the statement is false although the two terms mean the same.
* **Impact.** C.CV-1 as written is false on reachable runs. The W3 witness `letQuoteEq_witness` and `rowC_of_reader`'s `hq` (Cover3:815/844) for W6 cannot be proved from it. Nothing already accepted is affected (the premise is an assumption; an accepted theorem is wrong only if applied to such a run).
* **Options (each needs user approval; counts net 0 unless noted).**
  1. Weaken the right-hand side to `machCanonAp (machClose … v)`. One FG row's statement changes. Holds on both counterexamples above (printed). Whether `machCanonAp` idempotence is needed: for the equation itself, the quote side is read from the already canonical body, so the witness proof needs the "canon of a field of `packed` is the field of the canon" step (`machCanonAp` commutes with `machClose`/`machField` extraction), not idempotence as such;
     idempotence would enter only if a proof applies `machCanonAp` to the quote side. Not proved either way; side condition that `rowC_of_reader` (via `readsOfQuoteStmt`) is insensitive to the canonical renaming is not checked.
  2. Canonicalise in the reader (`lets.push (…, machCanonAp v')`). Edits production/shared reader definitions (prohibited without approval) and the fuel reader; may add an invariant (+1).
  3. Restrict covered programs (exclude non-canonical lets). Shrinks FG; not recommended.
* **Recommendation.** Option 1. **Reversible.** Option 1/3 yes (statement change, git-revertible); option 2 yes in git but touches the compiler.
* **If not decided.** C.CV-1 remains an unsupplied premise false on some reachable states; W6 stays conditional on it; other work (W1, G0–G2) proceeds.

## Not done
Lean proof of `¬ LetQuoteEq`; paths 2/3; idempotence of `machCanonAp`; the option-1 side condition; production-function `st` (copy only); no clean build (no repo Lean changed).
