# `projChain`: the minimal switch-over (reader generalisation, unit 1 taken into the compiler)

Branch `fix/projchain-total` (base poc `80745d94`).
**WRITTEN, NOT BUILT.** Nothing here was compiled or run. "READ" = read in
this tree or in the toolchain's sources. "PREDICTED" = from reading. "BUILT"
/ "MEASURED" appear only for what the integrator's records in
`docs/parallel/F-reader-unit.md` and `docs/parallel/H-reader-units.md` state.

Ruling implemented (reviewer, 2026-10-14, second message, item 6): do the
minimal switch-over of `projChain` now; no reverse dependency (the compiler
does not import `Tools/`), the pure total definitions under `Sparkle/`; the
real function's equation and call-site success provable in the kernel;
record the distinction "agreement with the old `partial` = measured +
correspondence with the source equation"; no fixed fuel, no new refusal;
after the switch the suite, the existing shadow, a reflection-premise audit;
the result is which general lemmas now apply to the real reader. No other
reader function is touched.

## 0. Commits and files

| commit | content | valid on poc too |
|---|---|---|
| `ba0d75f3` | shadow keeps the OLD function: `Tools/ShippingReaderProjChainShadow.lean`, `Tests/Compiler/ReaderProjChainShadowTest.lean` | yes |
| `74ebde60` | `Tests/Compiler/ReaderDigestTest.lean` (new, target-only) | yes |
| `e5f0e0d5` | THE SWITCH-OVER: `Sparkle/Compiler/MachProjChain.lean` (new), `Sparkle/Compiler/MachRawSurface.lean`, `Tools/ShippingReaderProjChain.lean`, `Tools/ShippingReaderProjChainFold.lean` | — |
| `fea65d37` | `Tools/ShippingReaderProjChainReal.lean`, `…Result.lean`, `…Arm.lean` (new) | no (they need the switch) |
| (this doc) | `docs/parallel/L-projchain-switch.md` | — |

The two test commits come FIRST on purpose: the tree at `74ebde60` is poc
plus two measurement files, so the "before" side of both audits can be run
there (or the two files copied onto poc).

Not edited: `lakefile.lean`, `Tests/AllTests.lean` (§7 says what to add),
`docs/parallel/F-reader-unit.md`, `H-reader-units.md` (the integrator's
records; row 3 of H's table is superseded by §3 here).

## 1. The diff under `Sparkle/`

New `Sparkle/Compiler/MachProjChain.lean` (imports `Lean` only; 3
definitions, no proof):

```lean
namespace Sparkle.Compiler.MachProjChain
def prodE (a b : Expr) : Expr := mkApp2 (.const ``Prod [.zero, .zero]) a b
def tailTy : List Expr → Option Expr
  | [] => none
  | a :: rest =>
    match rest with
    | [] => some a
    | _ :: _ => (tailTy rest).map (prodE a)
def tailAt (tys : List Expr) (i : Nat) : Option Expr := tailTy (tys.drop (i + 1))
```

(The texts BUILT in `Tools/ShippingReaderProjChain.lean`, moved.)

`Sparkle/Compiler/MachRawSurface.lean`:

```diff
 import Sparkle.Core.CircuitMonad
+import Sparkle.Compiler.MachProjChain
…
-partial def projChain (regs : Lean.Expr) (tys : List Lean.Expr) (j : Nat) (last : Bool) :
+def projChain (regs : Lean.Expr) (tys : List Lean.Expr) (j : Nat) (last : Bool) :
     Option Lean.Expr := do
-  -- the pair type at level i: Prod tys[i] (tail i)
-  let rec tail : Nat → Option Lean.Expr
-    | i => if i + 1 == tys.length - 1 then tys[tys.length - 1]?
-      else do
-        let a ← tys[i + 1]?
-        let b ← tail (i + 1)
-        some (mkApp2 (.const ``Prod [.zero, .zero]) a b)
   let mut cur := regs
   for i in [0:j] do
     let a ← tys[i]?
-    let b ← tail i
+    let b ← Sparkle.Compiler.MachProjChain.tailAt tys i
     cur := mkApp3 (.const ``Prod.snd [.zero, .zero]) a b cur
   if last then return cur
   let a ← tys[j]?
-  let b ← tail j
+  let b ← Sparkle.Compiler.MachProjChain.tailAt tys j
   return mkApp3 (.const ``Prod.fst [.zero, .zero]) a b cur
```

(plus two lines of doc comment). `rawNode`, the only caller, is untouched.
Nothing under `Sparkle/` imports `Tools/`.

## 2. The choice, and why

Two candidates: **(A)** keep `projChain`'s `do` text and replace only its
six-line local `tail` by `tailAt tys` (= what `projChainW` was); **(B)**
make `projChain` the structural `projChainT` (`chainGo last regs tys j`).

**Taken: (A).**

| criterion | (A) | (B) |
|---|---|---|
| (i) same function as today | the text is today's text with ONE subterm replaced: `tail` ↦ `tailAt tys`. The argument uses `tailAt_eq` + `tail_unique` only | the same, PLUS `projChainW_eq_projChainT` (a kernel theorem, BUILT) to cross from the text to the structural form |
| (ii) non-partial, equation and call-site success about the REAL function | yes: a plain `def`; `projChain = projChainT` is `projChainW_eq_projChainT` read at the abbreviation (§3) | yes, and the equation would be `rfl` |
| (iii) smallest diff | −7 lines, 2 tokens replaced, 1 word deleted, 1 import | −16 lines of `do` text, +1; `chainGo` / `fstE` / `sndE` move under `Sparkle/` too |
| (iv) cost | below | below |

Why (A) although (B)'s equation is `rfl`: the ruling asks for the MINIMAL
switch and for the distinction between what is proved and what is measured
to stay sharp. With (A) the claim "the compiler runs the same function as
before" rests on exactly one non-kernel step (below) and on no theorem about
`forIn`; the reviewer can see it in the diff. With (B) the compiled code
changes shape (a loop becomes a recursion) and the same claim needs the fold
theorem in addition. (A) loses nothing: the structural form is one kernel
equation away (`projChain_eq_projChainT`), about the real constant.

### (i) "the same function", precisely

Let `tail₀ : Nat → Option Expr` be what the OLD compiled local `tail`
computed (for fixed `tys`), and `P tail regs tys j last` the compiler's `do`
text with `tail` a parameter (`projChainP`, BUILT). Old function = `P tail₀`;
new function = `P (tailAt tys)`.

| step | status |
|---|---|
| `TailEq tys` is the old `tail`'s source text (its `do` block is two binds of `Option`) | READ (the text is kept verbatim in the shadow file, `projChainOld`) |
| `tailAt_eq : TailEq tys (tailAt tys)` — the total function solves that equation | KERNEL THEOREM (BUILT, `[propext, Quot.sound]`) |
| `tail_unique : TailEq tys tail → ∀ i, tail i = tailAt tys i` — it is the ONLY solution | KERNEL THEOREM (BUILT, same axioms) |
| **`TailEq tys tail₀`: the old compiled `partial` `tail` satisfied its own source equation** | **NOT a kernel statement; unprovable; NOT assumed.** It is the meaning of `partial` (the constant is opaque, its code attached by `implemented_by`). This is the ONE step outside the kernel |
| hence `tail₀ = tailAt tys`, hence `P tail₀ = P (tailAt tys)` | follows from the three above (`projChainP_eq` packages it for any `tail` with `TailEq`) |
| `projChainW_eq_projChainT`: `P (tailAt tys) = projChainT` | KERNEL THEOREM (BUILT, `[propext, Classical.choice, Quot.sound]`) — NOT needed for (i) under choice (A); it is the equation of the real function (§3) |
| the old and the new compiled functions return `Expr.equal` results | MEASURED (§5) |

Nothing about the old compiled code is proved, before or after.

### (iv) cost

The old `tail` was memo-free: every call `tail i` recursed up to the last
component, and each of its steps evaluated `tys.length` and a LIST index
`tys[i + 1]?` (linear), so one call was O(n·(n − i)), and `projChain` made
`j` or `j + 1` of them. `tailAt tys i = tailTy (tys.drop (i + 1))` is also
memo-free and recomputed per call, at O(n) (one `drop`, one pass). So the
new function is not worse in order — one factor `n` better per call — and
`rawNode` calls it `k` times per pair-matcher node as before (`k` ≤ the
number of registers destructured; single digits in the corpus). Not
measured; no timing is claimed.

### Does the reader accept or refuse anything else?

No new refusal exists in the text: `tailAt` returns `none` exactly where the
unique solution of the old equation does (`tail_unique` is for ALL `i`, in
and out of range). `projChain_isSome_iff` (§3) pins the accepting set of the
new function to `Accepts`; the grid of the shadow measured the same set for
the old one (65 of 198).

## 3. The deliverable: which general lemmas now apply to the real reader

`Tools/ShippingReaderProjChain.lean` now defines NOTHING the compiler
defines: `prodE`, `tailTy`, `tailAt` are re-exported
(`export Sparkle.Compiler.MachProjChain (prodE tailTy tailAt)` — aliases, the
same constants; the precedent is `Tools/ShippingHierOptSoundness.lean` 19),
and `projChainW` is

```lean
abbrev projChainW (regs : Lean.Expr) (tys : List Lean.Expr) (j : Nat) (last : Bool) :
    Option Lean.Expr := Sparkle.Compiler.MachRawSurface.projChain regs tys j last
```

Kept there (the compiler does not use them): `sndE`, `fstE`, `TailEq`,
`chainGo`, `projChainT`, `Accepts`, `acceptsB`.

### 3a. Existing theorems: statement text, and what they are about

"copy" = a second definition in `Tools/` with the compiler's text; "real" =
`Sparkle.Compiler.MachRawSurface.projChain` or a constant it calls.

| theorem (old name kept) | statement text | about, BEFORE | about, NOW |
|---|---|---|---|
| `tailTy_nil`, `tailTy_one`, `tailTy_cons`, `tailTy_cons_some` | unchanged | a `Tools/` definition the compiler did not use | REAL: `MachProjChain.tailTy`, called by the compiler |
| `drop_cases` | unchanged | lists | lists |
| `tailAt_eq` | unchanged | `Tools/` `tailAt` vs the old source equation | REAL `tailAt` (the compiler's callee) solves the OLD function's source equation |
| `tail_unique` | unchanged | the same | the same: every solution is the REAL `tailAt` |
| `chainGo_zero_true`, `chainGo_zero_false_nil`, `chainGo_zero_false_cons`, `chainGo_succ_nil`, `chainGo_succ_cons`, `bind_some'`, `chainGo_step`, `chainGo_true_some`, `chainGo_false_some` | unchanged | structural form | structural form (not the compiler's) |
| `projChainT_some`, `projChainT_callSite` | unchanged | structural form | structural form; transferred to the real function in 3b |
| `projChainW_form` (Fold) | unchanged; proof: more alternatives | copy `projChainW` | REAL (abbreviation) |
| `forIn_range_list`, `forIn_list_foldO`, `loop_chain`, `finStep_chain`, the `pair2_*` / `bind_*` lemmas (Fold) | unchanged | generic | generic |
| `projChainW_eq_projChainT` (Fold) | unchanged | copy = structural | REAL = structural |
| `projChainP_tailAt` (Fold) | unchanged; proof: more alternatives | text-with-parameter at `tailAt` = copy | text-with-parameter at `tailAt` = REAL |
| `projChainP_eq`, `projChainP_callSite` (Fold) | unchanged | the text over any solution of `TailEq` | the same; at `tail := tailAt tys` it is the real function, at the old `tail₀` it is the old one (the boundary of §2) |

Definitions: `prodE`, `tailTy`, `tailAt` — moved (aliases keep the names
`Tools.ShippingReaderProjChain.prodE` …); `projChainW` — `def` → `abbrev` of
the real function; all others unchanged.

### 3b. New theorems, each with the real constant on its left-hand side

`Tools/ShippingReaderProjChainReal.lean` (`projChain` below is
`Sparkle.Compiler.MachRawSurface.projChain`):

```lean
theorem projChainW_is_projChain (regs tys j last) :
    projChainW regs tys j last = projChain regs tys j last                       -- rfl
theorem projChain_text (regs tys j last) :
    projChain regs tys j last = projChainP (tailAt tys) regs tys j last
theorem projChain_form (regs tys j last) :
    projChain regs tys j last =
      (forIn [0:j] regs (loopBody tys) : Option Expr).bind (finStep tys last j)
theorem projChain_eq_projChainT (regs tys j last) :
    projChain regs tys j last = projChainT regs tys j last                       -- THE EQUATION
theorem projChain_eq : projChain = projChainT
theorem projChain_zero_last (regs tys) : projChain regs tys 0 true = some regs
theorem projChain_zero_notLast_nil (regs) : projChain regs [] 0 false = none
theorem projChain_zero_notLast_cons (regs a rest) :
    projChain regs (a :: rest) 0 false = (tailTy rest).map fun b => fstE a b regs
theorem projChain_succ_nil (regs k last) : projChain regs [] (k + 1) last = none
theorem projChain_succ_cons (regs a rest k last) :
    projChain regs (a :: rest) (k + 1) last =
      (tailTy rest).bind fun b => projChain (sndE a b regs) rest k last
theorem projChain_some (regs tys j last) (h : Accepts last tys.length j) :
    ∃ r, projChain regs tys j last = some r
theorem projChain_callSite (regs tys j) (hj : j < tys.length) :
    ∃ r, projChain regs tys j (j + 1 == tys.length) = some r                     -- every call rawNode makes
theorem projChain_callSiteK (regs tys j k) (hk : tys.length = k) (hj : j < k) :
    ∃ r, projChain regs tys j (j + 1 == k) = some r
```

`Tools/ShippingReaderProjChainResult.lean` — the exact result:

```lean
def pairTy : Expr → List Expr → Expr           -- the pair type of a :: l, no Option
theorem tailTy_pairTy (a l) : tailTy (a :: l) = some (pairTy a l)
def sndsE : List Expr → Nat → Expr → Expr      -- cur under j snds
theorem projChain_last_eq (regs tys j) (h : j = 0 ∨ j + 1 ≤ tys.length) :
    projChain regs tys j true = some (sndsE tys j regs)
theorem projChain_notLast_eq (regs tys j a b l) (h : tys.drop j = a :: b :: l) :
    projChain regs tys j false = some (fstE a (pairTy b l) (sndsE tys j regs))
theorem projChain_none (regs tys j) :
    ∀ (last : Bool), ¬ Accepts last tys.length j → projChain regs tys j last = none
theorem projChain_isSome_iff (regs tys j last) :
    (projChain regs tys j last).isSome = true ↔ Accepts last tys.length j
```

(with `chainGo_true_eq`, `chainGo_false_eq`, `chainGo_true_none`,
`chainGo_false_none` about the structural form.)

### 3c. The table the ruling asks for

| lemma | about a copy / the structural form BEFORE | about the real function NOW |
|---|---|---|
| defining equation | none possible (`partial`: opaque) | `projChain_eq_projChainT`, `projChain_eq` |
| source text | `projChainW` was a copy of it | `projChain_text` (`= projChainP (tailAt tys)`), `projChain_form` |
| recursion equations | `chainGo_*` (structural form) | `projChain_zero_last`, `…_zero_notLast_nil`, `…_zero_notLast_cons`, `…_succ_nil`, `…_succ_cons` |
| success on `Accepts` | `projChainT_some` | `projChain_some` |
| success at every call of `rawNode` | `projChainT_callSite`, `projChainP_callSite` (under `TailEq`) | `projChain_callSite`, `projChain_callSiteK` — no premise about the source |
| exact result | — (measured: `Expr.equal` on the grid) | `projChain_last_eq`, `projChain_notLast_eq` |
| refusal outside `Accepts` | — (measured: `isSome == acceptsB` on the grid) | `projChain_none`, `projChain_isSome_iff` |
| existence / uniqueness for the `tail` equation | `tailAt_eq`, `tail_unique` about a `Tools/` definition | the same statements, about the compiler's callee |
| `tailTy` facts | `Tools/` definition | the compiler's callee |

### 3d. One step up: `rawNode`'s pair-matcher arm

`rawNode` is a plain `def` (it never was `partial`). After the switch NONE
of its callees is `partial`: `projChain` (now a `def`), `listElems`
(structural), `Lean.Expr` operations (`liftLooseBVars`, `lowerLooseBVars`,
`beta` — externs, used as values only in this arm), and `prodMatch`, a
PARAMETER.

`Tools/ShippingReaderProjChainArm.lean`:

PROVED (written) — the loop of the arm over the REAL `projChain`:

```lean
def buildC (regs : Expr) (tys : List Expr) (k : Nat) (body : Expr) :
    List (Nat × Name × Expr) → Option Expr       -- a COPY of rawNode's local `build`; the callee is the real projChain
theorem buildC_some (regs tys k body) (hk : tys.length = k) :
    ∀ (l : List (Nat × Name × Expr)), AllLt k l → ∃ r, buildC regs tys k body l = some r
theorem pairArmC_some (regs body k binders) (hlen : binders.length = k) :
    ∃ r, buildC regs (armTys binders) k body (armJobs k binders) = some r
```

i.e. once `k` binders are peeled, the arm returns a result — every
`projChain` call in it is inside `projChain_callSiteK`; the externs enter as
opaque values.

STATED, NOT PROVED — about `rawNode` itself (a `def … : Prop`, so that the
build checks the statement is well-formed; not a theorem, used by nothing):

```lean
def RawNodePairArmGoal : Prop :=
  ∀ (pm : Name → Option Nat) (e : Expr) (n : Name) (us : List Level) (m regs alt : Expr)
    (k : Nat) (binders : List (Name × Expr)) (body : Expr),
    e.getAppFn = Expr.const n us →
    e.getAppArgs = #[m, regs, alt] →
    pm n = some k →
    peelC k alt [] = some (binders, body) →
    rawNode pm e = buildC regs (armTys binders) k body (armJobs k binders)
```

What blocks it — neither a `partial` callee nor an extern any more:

1. `rawNode`'s local functions are the constants `rawNode.peel` /
   `rawNode.build`; the parameters Lean gives `rawNode.build` (which of
   `regs`, `tys`, `k`, `body`, in what order; whether the `let`-bound `tys`
   is abstracted or re-bound) cannot be determined by reading. The digest
   test logs both types (`READERDIGEST CONST …`). With them,
   `rawNode.build … = buildC …` and `rawNode.peel = peelC` are inductions.
2. The unfolding of `rawNode`'s six-arm `match` on `(e.getAppFn,
   e.getAppArgs)` at a constant head with three arguments (the five earlier
   arms need 5, 6, 4, 6, 5 arguments): a case analysis on the compiled
   matcher with name-literal and array-literal patterns — to be written
   against goals, not blind.
3. `peelC`'s count (`binders.length = k`), a small induction; not written
   (it only matters together with 1).

`e.getAppFn` / `e.getAppArgs` are PREMISES of the goal, so the private
auxiliary of `Expr.getAppArgs` (H's boundary 2 for `prodMatcherArity?`) is
not needed here.

One more step up nothing transfers: `rawNode`'s caller `machNorm` is
`partial`; `senv.prodMatch` is `prodMatcherArity?` (`partial`). NO endpoint
premise (`MachineDefines`) is removed by this unit.

## 4. Proved / measured / neither

| claim | status |
|---|---|
| the new `projChain` equals `projChainT`; succeeds at every call site; exact results; refuses exactly outside `Accepts` | PROVED in the kernel about the real constant (WRITTEN; rests on BUILT `projChainW_eq_projChainT` modulo the re-pointing) |
| the total `tail` satisfies the OLD source equation, and is its only solution | PROVED (BUILT; statements unchanged) — "correspondence with the source equation" |
| the old compiled function returned what the new one returns | MEASURED: first version on poc, old called directly — grid 198 calls / 65 returned / 0 disagreements; sweep 27964 definitions, 634 with a pair matcher, 1416 real sites, 3521 calls, 0 disagreements, 0 not compared (F's record). To be re-measured after the switch against `projChainOld` (§5) |
| the old compiled `partial` `tail` satisfied its own source equation | NEITHER proved nor assumed; not a kernel statement |
| anything else about the old compiled code | NOTHING is proved |
| `projChainOld` (the copy kept in the shadow) is the old function | same source text, recompiled in another module: READ; `old==compiler` on the pre-switch tree MEASURES it |
| `rawNode`'s arm returns a result | PROVED for the loop over the real `projChain` with the loop a copy; about `rawNode` itself STATED only |
| any endpoint statement / reflected data changed | PREDICTED no; audit (c) below measures; the suite re-generates and kernel-checks every endpoint |

## 5. The measurement stays meaningful

After the switch the compiler's `projChain` IS the total function; the old
comparison would compare it with itself. So
`Tools/ShippingReaderProjChainShadow.lean` now has

```lean
partial def projChainOld …   -- VERBATIM: MachRawSurface.lean 56–73 at 80745d94, local partial `tail` included
```

(not used by the compiler) and compares FOUR functions on every input, every
comparison against `old`: `old` = `projChainOld`; `compiler` = whatever
`MachRawSurface.projChain` is on the tree; `W` = `projChainW`; `T` =
`projChainT`. The first log line says which is which and reports
`compiler partial=T|F` from the environment (the constant `projChain.tail`
exists only for the old definition). The test file's header has the same
"which is which".

* pre-switch tree: `old==compiler` = the copy against its original;
* post-switch tree: `old==compiler` = the function the compiler runs now
  against the one it ran before, on the grid and at every real call site;
  and the `let` values of the REAL `rawNode` (now produced by the total
  function) against `T`, hence against `old`.

## 6. Audits (for the integrator) and PREDICTED results

(a) **The suite**: `Tests.AllTests` (and the usual executable). PREDICTED:
the counts of poc at `80745d94`, unchanged (the number itself is the
integrator's; not predicted here). Inside it, relevant to this change:
`Tests.Compiler.ShippingMachineRawTest` (`#machine_endpoint` of the five
raw `runCircuitH` declarations — the reader's output is kernel-checked
against the declaration again), `Tests.Compiler.LeafSweepRawTest`
(PREDICTED `GENERATED (7)` as before), `Tests.RunCircuitHTest`
(`#synthesizeVerilog` of the raw declarations), `DepthSwitchPinTest` (51
fingerprints, asserting).

(b) **The shadow**: `lake build Tests.Compiler.ReaderProjChainShadowTest`,
`grep -E '^PROJCHAIN (WHICH|GRID|SWEEP|:|DISAGREE|NOT COMPARED)'`.
PREDICTED:

```
pre-switch (74ebde60 or poc + the two files):
PROJCHAIN WHICH: … compiler partial=T …
PROJCHAIN GRID: calls=198 old returned=65 disagreements=0
PROJCHAIN SWEEP: definitions=<n> with a pair matcher=<m> sites=<s> calls=<c> old returned=<c> disagreements=0 not compared=0
PROJCHAIN: grid agree=T sweep agree=T real call sites compared=<s>

post-switch:
PROJCHAIN WHICH: … compiler partial=F …
(the same three lines; <n>, <m>, <s>, <c> not predicted — poc had 27964 / 634 / 1416 / 3521 and new files add definitions)
```

The other three shadows (`ReaderMatcherArityShadowTest`,
`ReaderInstTyShadowTest`, `ReaderBoolMapShadowTest`) import
`Tools.ShippingReaderSweepCommon`, which imports this shadow file and uses
its `roots` only: PREDICTED unchanged lines up to the definition counts.

(c) **Reflection-premise audit** — the switch must not change any
endpoint's statement. What exists, and what was missing:

* exists: `DepthSwitchPinTest` (in the suite; `Expr.hash` + binder count of
  51 depth statements, asserting), `RanSplitStatementsTest` (target-only;
  pinned statements by `example : <old> := @<name>`), `DesignCoverageTest` /
  `#design_coverage` (census totals and forms). PREDICTED unchanged. None of
  them covers the raw `runCircuitH` declarations' `machineData` or reruns
  the reader — by READING (`grep` for `machineData` fingerprints: only
  `ReaderCoverageTest`, which measures the strict reader's reach, not a
  digest).
* added: `Tests/Compiler/ReaderDigestTest.lean` (target-only, asserts
  nothing, never throws, elaborates on poc). For EVERY holder of
  `f.machineData` and every raw-surface definition under the roots it runs
  the reader again (`readMachine`) and logs a digest of the result
  (`READERDIGEST SHAPE`: `Expr.hash` of the transition body, binders,
  layout, runs, loops, instances, fields), the hashes of the type and value
  of `f.machineData` (`DATA`; read through `Meta`, never evaluated), one hash
  over the names and TYPES of all constants below `f` (`STATEMENTS`; listed
  one by one for `raw=T` holders), and the constants `projChain`,
  `projChain.tail`, `rawNode`, `rawNode.peel`, `rawNode.build` with their
  types (`CONST`).

```
lake build Tests.Compiler.ReaderDigestTest 2>&1 | grep '^READERDIGEST' | grep -v ' START ' | sort -u > digest.<tree>.txt
diff digest.poc.txt digest.candidate.txt
```

PREDICTED diff: exactly the lines
`READERDIGEST CONST Sparkle.Compiler.MachRawSurface.projChain: …` (`opaque`
→ `def`) and `…projChain.tail: …` (present → `absent`). Any other differing
line is a finding. Equal hashes are not a proof of equal terms; the kernel
evidence is (a): every endpoint is re-generated and checked on the candidate.

(d) Optional, as for any compiler edit: the corpus measurement
(`scripts/shipping-coverage`, `status.txt` diff) and `compare_outputs.py` on
the generated text. PREDICTED identical (the reader returns `Expr.equal`
terms). Simulation is not needed (no hierarchy / optimizer change).

(e) `#print axioms`: `projChain_eq_projChainT`, `projChain_callSite`,
`projChain_isSome_iff`, `pairArmC_some` — PREDICTED `[propext,
Classical.choice, Quot.sound]` (inherited from `projChainW_eq_projChainT`);
`tailAt_eq`, `tail_unique` — unchanged `[propext, Quot.sound]`.

## 7. Build order and `lakefile.lean` lines

To add (the existing three `Tools.ShippingReaderProjChain*` entries stay):

```
lean_lib «Tools.ShippingReaderProjChainReal» where
  roots := #[`Tools.ShippingReaderProjChainReal]

lean_lib «Tools.ShippingReaderProjChainResult» where
  roots := #[`Tools.ShippingReaderProjChainResult]

lean_lib «Tools.ShippingReaderProjChainArm» where
  roots := #[`Tools.ShippingReaderProjChainArm]
```

`Sparkle/Compiler/MachProjChain.lean` is in the `Sparkle` library through
the import (no line). `Tests/Compiler/ReaderDigestTest.lean` is in the
`Tests` library; TARGET-ONLY, NOT to be added to `Tests/AllTests.lean` (it
imports it). Nothing is to be added to `Tests/AllTests.lean`.

Order:

0. BEFORE the switch (poc, or the tree at `74ebde60`):
   `Tools.ShippingReaderProjChainShadow`,
   `Tests.Compiler.ReaderProjChainShadowTest` (keep the `PROJCHAIN` lines),
   `Tests.Compiler.ReaderDigestTest` (keep `digest.poc.txt`).
1. `Sparkle.Compiler.MachProjChain`, `Sparkle.Compiler.MachRawSurface`.
   NOTE: `MachRawSurface` is imported by `Elab.lean`, so everything
   downstream rebuilds (the whole compiler and every test), and the
   precompiled `Sparkle` shared library gets a new module (relink).
2. `Tools.ShippingReaderProjChain` (now imports `MachRawSurface`), then
   `Tools.ShippingReaderProjChainFold` — the two files whose proofs were
   BUILT and are now re-pointed; `#print axioms` as in (e).
3. `Tools.ShippingReaderProjChainReal`; then, independent of each other and
   leaves, `…Result` and `…Arm`.
4. The suite (a); the shadow (b); the digest and the diff (c).

## 8. Risks, in order

1. **`projChainW_form` (Fold) after the re-pointing.** Its proof is `first |
   rfl | unfold … | simp only … | …` and the record does not say which
   alternative closed it. If it was `rfl`: unaffected (one more δ-step
   through the abbreviation). If it was an alternative that unfolds
   `projChainW` by name, that now stops at the compiler's constant — the
   added alternatives unfold `Sparkle.Compiler.MachRawSurface.projChain` too.
   If all fail: `#print Sparkle.Compiler.MachRawSurface.projChain` against
   the old `#print projChainW`; the `do` text is the same, elaborated in
   another file (both `open Lean`, the `Option` monad). Everything in §3b
   hangs on this one lemma.
2. **`export … (prodE tailTy tailAt)`**: aliases instead of definitions.
   Every built proof term is the same up to the constants' names; the
   pattern is `Tools/ShippingHierOptSoundness.lean` 19. If an alias does not
   resolve somewhere (e.g. through `open Tools.ShippingReaderProjChain` in
   the shadow): replace the `export` line by three `abbrev`s — then `rfl`
   proofs see one more δ-step.
3. **Does making `projChain` non-partial change how `rawNode` compiles?**
   By READING: no semantic change. `rawNode` calls the constant `projChain`
   in both cases; before, its code was the `implemented_by` unsafe
   recursion with the auxiliary `projChain.tail` (closing over `tys`); now
   the definition's own code, calling `MachProjChain.tailAt`. Neither
   carries `@[inline]` / `@[specialize]`; `forIn` over the range is
   specialised by the code generator as before. `rawNode` itself is not
   edited. The `Inhabited` obligation of `partial` disappears.
4. **Import cycle**: none — `MachProjChain` imports `Lean` only;
   `MachRawSurface` imports it; `Tools/ShippingReaderProjChain.lean` now
   imports `Sparkle.Compiler.MachRawSurface` (was `Lean` only: its build
   gets the cost of `Sparkle.Core.CircuitMonad`'s closure).
5. **The definition is accepted without `partial`**: the same text was BUILT
   as `projChainW` (no recursion left; the `for` is `forIn`).
6. **Blind proofs in the new files.** `…Real`: term-mode transfers; the one
   tactic proof (`projChain_succ_cons`) has three alternatives. `…Result`:
   `chainGo_false_eq` (`subst` after reading `ts.drop 0 = …` as `ts = …`;
   `List.drop_nil`), the `rfl` equations of `sndsE` / `pairTy` (constructor
   forms only; `sndsE_zero` by `cases`), `tailTy_pairTy`. `…Arm`:
   `jobs_allLt` (the `show` through `List.zip` / `List.map` on constructor
   forms), `allLtN_of_mem` (`List.Mem.head` / `.tail`), `armTys_length`
   (`List.length_map`, `List.length_zipIdx` — names READ in the toolchain),
   `buildC_some` (`rw [buildC_cons, hv, hr]` with `hr` under a binder).
   `…Result` and `…Arm` are leaves: a failure there does not affect §3b's
   first block.
7. **The digest test**: API by reading (`MachineShape` fields, `Repr` of
   `Layout` / `MixedGateBinder`, `readMachine … (allowGate := true)`,
   `NameSet`, `ConstantInfo.value?`). Cost: it reruns the reader on every
   holder (not measured). Whether `Expr.hash` of generated statements is
   stable across two builds of the SAME tree is not known by reading
   (`DepthSwitchPinTest` relies on it for 51 statements); if the poc-vs-poc
   diff is not empty, the `STATEMENTS` lines are noise and only `SHAPE` /
   `DATA` count.
8. **`compilerPartial` in the shadow** is read off the existence of the
   constant `Sparkle.Compiler.MachRawSurface.projChain.tail` (PREDICTED name
   of the old `let rec`); if the old tree names it otherwise the line says
   `partial=F` on poc too — a wrong label, not a wrong comparison.

## 9. NOT determined by reading

* Whether any file elaborates; which alternative of `projChainW_form`
  closes it.
* The names and types of `rawNode.peel` / `rawNode.build` (the digest test
  logs them) — needed for `RawNodePairArmGoal`.
* The counts of the sweep and of the digest; whether the digest's
  `STATEMENTS` hashes are build-stable.
* Whether the code generator inlines or specialises anything differently
  around `projChain` (no effect on results is expected; not inspected).
* Timing before / after.

## Integrator's build record (2026-10-14) — MEASURED; INTEGRATED on poc

Verified on the poc tree as ONE STACK together with the threading split (docs/parallel/L-threading-split.md):
runs `l-before` (before-audits on poc 5face54e + the two measurement commits), `stack1`, `stack1b`,
`stack1c`; cgrun 3 GiB swap 0. Intermediate commits of the stack were not built one by one.
Worker's files unchanged; first attempt for this unit (`Sparkle`, the re-pointed
`ShippingReaderProjChain` / `…Fold`, the three new `…Real` / `…Result` / `…Arm` files).

* The compiler's `projChain` is now a plain `def` (`#print` shows the `forIn` text with
  `Sparkle.Compiler.MachProjChain.tailAt`); the constant `projChain.tail` is absent.
* About the REAL function, kernel-checked (`[propext, Classical.choice, Quot.sound]`):
  `projChain_eq_projChainT`, `projChain_callSite`, the recursion equations (`projChain_succ_cons` …),
  the exact result and refusal characterisation (`…Result`).
* Agreement with the OLD compiled `partial` function — MEASURED, not proved (`projChainOld` is a verbatim
  copy of the pre-switch source compiled in the shadow file):
  before the switch `GRID calls=198 old returned=65 disagreements=0`, `SWEEP sites=1417 calls=3523
  disagreements=0`, `compiler partial=T`; after the switch the same numbers with `compiler partial=F`.
  Correspondence with the old SOURCE equation: theorems `tailAt_eq`, `tail_unique`.
* Reader digest (re-running the reader on 135 declarations: shapes, data, statements hashes), poc vs
  after: ONE differing line — `CONST …projChain.tail: opaque …` → `absent`. (`projChain` itself was
  already listed as `def` before: predicted two lines, measured one.) Shapes / data / statements hashes
  identical.
* `Tests.AllTests` 1348 jobs green; census unchanged (134 / 133); pin tests green.
No endpoint lost a premise: `rawNode` is not yet connected (`RawNodePairArmGoal` is stated, not proved),
`machNorm` above it is still `partial`.
