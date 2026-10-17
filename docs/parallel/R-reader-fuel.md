# Worker A (reader, fuel), round 3 (`par/r-3`): a fuel-indexed TOTAL candidate of the machine reader

Base poc `c1c651a0`. **Status at 22908c5f:** `…FuelDefs` and `…FuelKleene` BUILT; `…FuelOldEq` / `…FuelLenOk` / `…FuelVerbatim` NOT built (see the Integration section at the end). `readF_agree` is conditional on `IsSol (step)`, not old agreement.
No file under `Sparkle/` changed; the real compiler path is untouched (the
eight `partial def`s are not edited, nothing that calls them is, nothing
imports the new files except the new files). No `sorry`, no new axiom, no
`native_decide`, no Mathlib tactic. ALLOWED unchanged.

## 0. What the fuel version PROVES, and what stays OPEN (first deliverable)

PROVED (when built), for ALL inputs `senv`, call `c` (any of the seven
functions, any arguments) and ALL fuels:

1. **Stability / monotonicity / fuel independence** (`fuel_stable`,
   `fuel_mono`, `fuel_det`; instances `readF_*`, `machConvF_stable`,
   `machChainF_stable`, `machLoopRootF_stable`, `machNormF_*`): a non-OUT
   answer at fuel `n` is the answer at every `m ≥ n`, and two non-OUT
   answers are equal. No hypothesis.
2. **Agreement with every solution of the old source equations**
   (`readF_agree_old`, `machConvF_agree_old`, `machChainF_agree_old`,
   `machLoopRootF_agree_old`, `machNormF_agree_old`; verbatim form
   `readF_agree_verbatim`, `machNormF_agree_verbatim`):
   `readF senv n c = some r → OldEq senv G → G.app c = r` for EVERY tuple
   `G` of seven functions satisfying the old equations; `r : Option _`, so this
   covers the old `some r` AND the old `none` (refusal). Hypothesis: only
   `OldEq` (a `Prop` over the tuple, never assumed of the real constants).
3. **R5 (`MachRead.LenOk`) for ALL fuels and ALL successful results**
   (`readF_good`, `machConvF_lenOk`, … seven, `readersKeepLenOkF` = the
   unprovable `ReadersKeepLenOk` of `Tools/ShippingReaderLenOk.lean`, now a
   theorem for the fuel functions; `machConvF_lenOk_init`): by induction on
   fuel, each arm closed from the BUILT `lenOk_*` update lemmas,
   `machReserve_lenOk`, `loopRoot_inits_length`. Only hypothesis: the input
   state is `LenOk` (`lenOk_init` gives it for `{}`).

OPEN — conditions for a production switch, none of them proved here:

* **O1 coverage**: an old success (or refusal) that NO fuel reaches. Not a
  kernel statement: a solution of the source equation need not be the least
  fixpoint (worker B's `fixpoint_not_complete`). "The compiled `partial`
  code computes the least fixpoint where it terminates" is operational;
  evidence only by shadows (old vs fuel on the corpus + sweep, minimal fuel
  recorded, `OUT` counted).
* **O2 the old implementation satisfies its own source equation**
  (`OldEq` / `OldEqV` / `OldEqN(V)` of the real `partial` constants): outside
  the kernel (`partial` = `opaque`). What IS now in the kernel: the fuel body
  agrees with the VERBATIM source text (`step_tot`, `oldEq_of_oldEqV`), so the
  transcription is no longer a trust step.
* **The wrapper**: no fuel `machineShape?` here (one fuel threaded through its
  six reader calls, OUT kept apart from its own `none`); R5 of the SHAPE
  (`ShapeDecomp.r5_of_lengths`) needs it.
* **The driver**: never a fixed FUEL with OUT → `none` → legacy (not
  acceptance-preserving). A partial doubling driver (OUT → retry with `2n`,
  never legacy) + the recorded `n` as certificate is the candidate (worker B,
  `R-reader-coverage.md` §4); not written.
* **Still-`partial` helpers called by the body** (`rootFloat`, `zetaAll` in
  `machReserve`, `rawNode`'s and `machNormNode`'s callees, `packTupleInputs`)
  and the `opaque` `Expr` primitives (`instantiate1`, `liftLooseBVars`, `==`):
  unchanged, outside the fuel.
* Compile-time cost and the GRID / SWEEP / CORPUS shadows (record
  `R-reader-outs-inv-2.md` §3.5) — not run.

## 1. Design (`Tools/ShippingReaderFuelDefs.lean`)

* `Call` (7 constructors = the 7 argument tuples, `senv` fixed), `Call.Res`.
  Each function is a NON-recursive body (`convStep`, `nestedStep`,
  `instStep`, `instSStep`, `chainStep`, `loopBodyStep`, `loopRootStep`); a
  recursive call is the effect `FM.call c`; `step senv` dispatches. No
  `mutual`, no termination argument.
* `FM κ R α` = a computation over a call table `h : (c : κ) → Option (R c)`
  TOGETHER with its monotonicity proof (`FM.mono`); `pure`/`bind`/`call` are
  monotone, so every body is (worker B's `Mono`, by construction).
* Three-valued answer `fuel Φ n c : Option (Option c.Res)`: `none` = OUT,
  `some none` = FAIL (old `none`), `some (some r)` = OK. OUT is the outer
  `Option`, propagated by `FM.bind` only; it is never read as FAIL.
* Sharing probes (`machNested` 4024–4030, `machLoopRoot` 4207–4211):
  `findSomeO` over `FM`; a probe's OUT makes the whole call OUT, a probe's
  FAIL is "not this one" (worker B's R2).
* Evaluation order mirrors the old text: `foldO` stops at the first FAIL,
  `findSomeO` at the first hit, guards before calls, and `machChain`'s `next`
  arm evaluates `machConv rhs` before inspecting `machHandleV h` (4133; R3/R4).
* Pure fragments shared verbatim with the old-equation side: `convBvar`
  (`let rec bundle` → `bundleSlots`), `instRes` (`let rec inst`),
  `instEntry`, `loopView?`, `loopRegBad/Kind/Init`; the two unsplittable
  matches as views `regView?`, `ashrView?`.
* `readF senv n : Hs`, `machConvF … machLoopRootF`, `machNormF n senv e :
  Option Lean.Expr` (`none` = OUT; `machNorm` never refuses).

### Coordinator note (worker B, `05bb23fa`) — what changed / how it is met

1. Three-valued result: met (`Option (Option _)`, OUT outer). Not B's `Fu`
   type; the correspondence is `none ↦ .out`, `some none ↦ .fail`,
   `some (some r) ↦ .ok r`.
2. OUT inside the sharing probes makes the whole call OUT: met by
   construction (`FM.bind` in `findSomeO`), and it is FORCED by the type
   (a body that read OUT as FAIL could not be written as an `FM`).
3. Evaluation order: met, including the eager `machConv rhs` (4133).
4. B's generic lemmas (`iter_mono`, `iter_det`, `agree_ok/fail`, `Fu.bind_le`)
   were NOT reused: with `FM` the body's `Mono` is free, and the Kleene part
   is 60 lines (`Tools/ShippingReaderFuelKleene.lean`: `fuel_mono` = `iter_mono`,
   `fuel_det` = `iter_det`, `fuel_agree` = `agree_ok` ∧ `agree_fail`, `IsSol` =
   `IsFix`). Not built against `Tools/ReaderFuelGeneric.lean` (not on this branch).

## 2. Files, build order, lean_lib lines

| file | content | risk |
|---|---|---|
| `Tools/ShippingReaderFuelDefs.lean` | definitions only (FM, Call, 7 bodies, `normStep`, `fuel`, `readF`, `machXF`) | low–medium (elaboration of long term-mode bodies) |
| `Tools/ShippingReaderFuelKleene.lean` | generic stability / monotonicity / agreement + instances | low |
| `Tools/ShippingReaderFuelOldEq.lean` | `OldFns`, the old texts (refactored as listed), `OldEq`, `OldEqN`, run lemmas, `tot_crunch`, `step_tot`, `normStep_tot`, `readF_agree_old`, `machNormF_agree_old` | HIGH (per-arm case analysis by a crunch tactic) |
| `Tools/ShippingReaderFuelLenOk.lean` | `GoodH`, `Sat`, `lenok_crunch`, per-arm `*_sat`, `readF_good`, `machXF_lenOk`, `readersKeepLenOkF` | HIGH (crunch + `solve_by_elim`) |
| `Tools/ShippingReaderFuelVerbatim.lean` | verbatim texts `oConvV …`, `regMatch_view`, `ashrMatch_view`, `oldEq_of_oldEqV`, `readF_agree_verbatim`, `machNormF_agree_verbatim` | HIGHEST (matcher-definition proofs) |

Build order (serial, each independent of the compiler build except importing it):
1. `lake build Tools.ShippingReaderFuelDefs`
2. `lake build Tools.ShippingReaderFuelKleene`
3. `lake build Tools.ShippingReaderFuelOldEq`
4. `lake build Tools.ShippingReaderFuelLenOk` (imports 3 and the BUILT `ShippingReaderLenOkReserve`)
5. `lake build Tools.ShippingReaderFuelVerbatim` (imports 3 and `ShippingSparseCasesTac`)

4 and 5 are independent of each other. If 3 fails only in its arm proofs, 4
can be unblocked by moving the `run_*` / `obind_*` lemmas (section `Run`) to
a separate file (they do not depend on the arms).

```
lean_lib «Tools.ShippingReaderFuelDefs» where
  roots := #[`Tools.ShippingReaderFuelDefs]

lean_lib «Tools.ShippingReaderFuelKleene» where
  roots := #[`Tools.ShippingReaderFuelKleene]

lean_lib «Tools.ShippingReaderFuelOldEq» where
  roots := #[`Tools.ShippingReaderFuelOldEq]

lean_lib «Tools.ShippingReaderFuelLenOk» where
  roots := #[`Tools.ShippingReaderFuelLenOk]

lean_lib «Tools.ShippingReaderFuelVerbatim» where
  roots := #[`Tools.ShippingReaderFuelVerbatim]
```

## 3. Main statements

```lean
theorem fuel_stable (Φ) (h : fuel Φ n c = some r) (hnm : n ≤ m) : fuel Φ m c = some r
theorem fuel_mono (Φ) (hnm : n ≤ m) : HLe (fuel Φ n) (fuel Φ m)
theorem fuel_det (Φ) (h : fuel Φ n c = some r) (h' : fuel Φ m c = some r') : r = r'
def IsSol (Φ) (g) : Prop := ∀ c, (Φ c).run (fun c => some (g c)) = some (g c)
theorem fuel_agree (Φ) (g) (hg : IsSol Φ g) (h : fuel Φ n c = some r) : g c = r

def OldEq (senv) (G : OldFns) : Prop      -- 7 source equations (refactored text)
def OldEqV (senv) (G : OldFns) : Prop     -- 7 source equations, verbatim text
theorem step_tot (senv G) : ∀ c, (step senv c).run (tot G) = some (oApp senv G c)
theorem isSol_of_oldEq (h : OldEq senv G) : IsSol (step senv) G.app
theorem readF_agree_old (h : OldEq senv G) (hr : readF senv n c = some r) : G.app c = r
theorem oldEq_of_oldEqV (h : OldEqV senv G) : OldEq senv G
theorem readF_agree_verbatim (h : OldEqV senv G) (hr : readF senv n c = some r) : G.app c = r
theorem machNormF_agree_verbatim (h : OldEqNV senv g) (hr : machNormF n senv e = some r) : g e = r

def GoodH (h : Hs) : Prop :=
  ∀ c, (Call.inSt c).LenOk → ∀ v, h c = some (some v) → (Call.outSt c v).LenOk
theorem readF_good (senv) : ∀ n, GoodH (readF senv n)
theorem machConvF_lenOk (h : machConvF n senv env d e st = some (some (r, st'))) (hst : st.LenOk) : st'.LenOk
theorem readersKeepLenOkF (senv n) : <ReadersKeepLenOk with machConvF/machLoopRootF/machChainF at fuel n>
```

## 4. Predicted axioms

* Kleene file, `fuel_*`, `readF_*` (stability/det): none or `[propext]`.
* `fuel_agree`, `readF_agree`: `[propext]` at most.
* `step_tot`, `readF_agree_old`, `normStep_tot`, `machNormF_agree_old`:
  `[propext, Classical.choice, Quot.sound]` (`simp`/`split`).
* `readF_good`, `machXF_lenOk`, `readersKeepLenOkF`: `[propext, Classical.choice, Quot.sound]`
  (via `machReserve_lenOk`, `simp`).
* `regMatch_view`, `ashrMatch_view`, `readF_agree_verbatim`: `[propext, Classical.choice, Quot.sound]`.

## 5. Risks (PREDICTED; nothing was elaborated)

1. **Defs**: long term-mode bodies with `match` alternatives whose right-hand
   side starts on the next line at the alternative's column (the source does
   the same); `let` blocks inside parentheses; dependent `Call.Res` in
   `step` (made `@[reducible]`). `FM.bind.mono` uses `Option.bind_eq_some_iff`.
2. **`tot_crunch` / `lenok_crunch`** (OldEq, LenOk): `repeat' (simp only … | split)`.
   Relies on (a) `split` generalising a non-variable discriminant in the
   WHOLE goal (both sides), (b) splitter generation for `chainStep`'s and
   `oChain`'s matchers (name-literal nested `Expr` patterns, no array
   literal), (c) the default arms' "not this pattern" hypotheses being closed
   by `simp_all` after the other side is split. If an arm fails, it is that
   arm's theorem (`conv_tot`, `chain_sat`, …) that fails; the others stand.
3. **`solve_by_elim (maxDepth := 24)`** in `lenok_crunch`: search depth/time;
   the `out_*` lemmas match any `LenOk` goal and backtrack on the call
   hypothesis. Record-update unification (`{ st with … }`) against the
   `lenOk_*` statements is syntactic after `simp only` (no projection
   reduction expected).
4. **Verbatim**: `regMatch_view` / `ashrMatch_view` are match15-style proofs
   over 5-component names (`rcases` one level deeper than `match15_three`);
   `oConvV_eq` uses `rw [regMatch_view]`, which needs the lemma's inline
   matcher and `oConvV`'s to be the SAME auxiliary (Lean's matcher cache within
   one module); the `rfl` equalities assume the lifted `let rec`s
   (`bundleSlots`, `instRes`) are definitionally the local ones.
5. `run_foldO_eq` / `run_findSomeO_eq`: `rw` steps after `simp only [foldO]`.

## Integration (integrator, 2026-10-15) — PARTIAL: definitions + fuel lemmas BUILT; agreement / R5 / verbatim NOT built
Applied on poc 0a53bd9e (lakefile conflict on appended lean_libs: resolved). Run `a1` (cgrun, 3 GiB, swap 0,
`-j 1`). Fixes: the seven `FM.call (.conv …)`-style uses in `ShippingReaderFuelDefs` qualified as `Call.conv`
etc. (dotted constructors had no expected type); `progress` (Mathlib-only) removed from the crunch macros
(`simp only` already fails without progress). Then:
* `Tools.ShippingReaderFuelDefs`, `Tools.ShippingReaderFuelKleene`: exit 0. Axioms: `fuel_mono`,
  `fuel_stable`, `fuel_det`, `fuel_agree`: none; `readF_stable`, `readF_det`, `readF_agree`,
  `machNormF_stable`, `machNormF_det`, `machNormF_agree`: [propext, Quot.sound].
* `Tools.ShippingReaderFuelOldEq` FAILS (hence `…LenOk`, `…Verbatim`, which import it, are not built): the
  `conv_tot` arm times out at `whnf` (200000 heartbeats) inside `tot_crunch2`; in `chain_tot` and
  `loopBody_tot` the crunch leaves leaves where the two sides disagree (`some none` vs `some (some …)`): the
  case split does not align the fuel body with the old text there. Full log kept at
  ~/sparkle-work/a1-fuel-oldeq-errors.log. These three files are NOT committed (kept for the next round).

WHAT IS PROVED NOW (built): for the isolated fuel-indexed reader (`readF`, `machNormF`; the real compiler
path unchanged): stability of a finished answer under more fuel, determinism (two finished answers are
equal), and agreement of every finished answer with ANY step-level solution `g` (`IsSol (step senv) g → readF
senv n c = some r → g c = r`). NOT YET PROVED: that a solution of the OLD source equations is such a step-level
solution (`OldEq → IsSol`, the failing file), R5 (`LenOk`) for the fuel functions, the verbatim-text link.
OPEN FOR ANY PRODUCTION SWITCH (unchanged): coverage (an old success no fuel reaches — not a kernel statement,
`fixpoint_not_complete`), the old partial constants satisfying their source equations (outside the kernel),
a fuel `machineShape?` and the doubling driver (not written), shadows (not run).

## R5 rebuilt on the fuel version alone (worker R5, `par/r-7`, 2026-10-15) — WRITTEN, NOT BUILT
Reviewer ruling (2026-10-15): R5 (`GoodH` → every step keeps `GoodH` → fuel induction) is a property of the
NEW fuel functions and does not depend on agreement with the old reader. It is therefore re-homed so that it
builds WITHOUT `ShippingReaderFuelOldEq` (which fails and is being repaired elsewhere). R5 is NOT connected to
the real old reader (`machConv`, …): that link is `OldEq → IsSol`, still open; `ReadersKeepLenOk` of the OLD
readers stays unproved.

Files (new; the previous draft `ShippingReaderFuelLenOk.pending.lean` is deleted, not committed):
* `Tools/ShippingReaderFuelRun.lean` — imports `Tools.ShippingReaderFuelKleene` only; the three `rfl` lemmas
  R5 uses, verbatim from the OldEq draft: `run_pure`, `run_bind`, `run_bindO`. NOTE: the OldEq draft declares
  the same three names in the same namespace; if it is rebuilt importing this file, drop its copies.
* `Tools/ShippingReaderFuelR5.lean` — imports `Tools.ShippingReaderFuelRun` and
  `Tools.ShippingReaderLenOkReserve` (hence `Tools.ShippingReaderLenOk`) only. Theorem names/statements of the
  draft kept: `GoodH`, `step_good`, `readF_good`, `machConvF_lenOk`, `machNestedF_lenOk`,
  `machInstanceF_lenOk`, `machInstanceSF_lenOk`, `machChainF_lenOk`, `machLoopBodyF_lenOk`,
  `machLoopRootF_lenOk`, `readersKeepLenOkF`, `machConvF_lenOk_init` (plus the draft's helpers `out_*`,
  `convBvar_ok`, `instEntry_ok`, `foldO_ok`, `findSomeO_ok`, `*_sat`, `*Fold_ok`, `nestedFind_ok`, `loopFind_ok`).

Build order: `Tools.ShippingReaderFuelDefs` → `Tools.ShippingReaderFuelKleene` (both built on poc) →
`Tools.ShippingReaderFuelRun` → (`Tools.ShippingReaderLenOk` → `Tools.ShippingReaderLenOkReserve`, built) →
`Tools.ShippingReaderFuelR5`. lean_lib lines appended at the END of lakefile.lean:
```
lean_lib «Tools.ShippingReaderFuelRun» where
  roots := #[`Tools.ShippingReaderFuelRun]

lean_lib «Tools.ShippingReaderFuelR5» where
  roots := #[`Tools.ShippingReaderFuelR5]
```

### Integrator's notes on the previous draft (recorded per ruling) and how this version meets them
1. The crunch macros used `progress` (Mathlib-only). Use `first | simp only [...] | split` style
   (`simp only` already fails without progress). — This version has NO crunch macro and no `progress`.
2. Dotted constructors of `Call` need qualification (`Call.conv`, not `.conv`) where no expected type is
   available. — Every `Call` constructor in the R5 file is written qualified (`Call.conv`, `Call.nested`, …),
   including the patterns of `Call.inSt` / `Call.outSt`.
3. A `repeat' split` over large bodies timed out (whnf, 200000 heartbeats) in the `conv` arm. Prefer
   per-constructor local lemmas and record expected time / max goal count. — This version proves each body
   with Hoare-style combinator lemmas (`sat_pure`, `sat_okO`, `sat_failO`, `sat_optK`, `sat_bindO`,
   `sat_bind`, `sat_ite`, `sat_domGuard`, `sat_pure_ite`, `sat_foldO`, `sat_findSomeO`) applied by `refine`
   in source order; each `match` is split ONCE on the goal when its arm is reached; `machConv` is split per
   constructor (`cases e`, 12 goals) with separate lemmas `conv_app_sat` / `conv_letE_sat`. `repeat' split`
   remains only on the hypothesis of the tiny pure parts of `instArg` / `instSArg` (≤ 3 rounds, 4 leaves).

Expected goal counts (open goals at any time ≤ 2 in every arm, except `cases e`):
| lemma | splits | leaves |
|---|---|---|
| `convBvar_ok` | `if` + 5-arm `match` (hyp) | 6 |
| `conv_app_sat` | 8 views, one at a time | 9 |
| `conv_letE_sat` | `if`, `rootFloat`, `if`, `machTailV`, `machHandleV` | 5 |
| `conv_sat` | `cases e` | 12 |
| `nested_sat` | `match shared` | 2 |
| `inst_sat` / `instS_sat` | `findIdx?` (+ `ctor?` cases) | 2 / 3 |
| `chain_sat` | 4-arm source `match` (once), inner 2-arm, letE as conv | 8 |
| `loopBody_sat` | `cases e` | 12 |
| `loopRoot_sat` | `loopView?`, `match shared` | 3 |
Expected time: every arm is linear in the body (no case product); no single tactic should approach the
heartbeat limit. The one heavy step is predicted to be `split` on `chainStep`'s 4-arm source match (deep
`Expr.app` patterns with `Name` literals; splitter generation) — see risks.

### Statements (main)
```lean
def GoodH (h : Hs) : Prop :=
  ∀ c, (Call.inSt c).LenOk → ∀ v, h c = some (some v) → (Call.outSt c v).LenOk
theorem step_good (senv : StructEnv) {h : Hs} (hG : GoodH h) : GoodH (fun c => (step senv c).run h)
theorem readF_good (senv : StructEnv) : ∀ n, GoodH (readF senv n)
theorem machConvF_lenOk {n senv env d e st r st'} :
    machConvF n senv env d e st = some (some (r, st')) → st.LenOk → st'.LenOk   -- (and six siblings)
theorem readersKeepLenOkF (senv : StructEnv) (n : Nat) : (conv) ∧ (loopRoot) ∧ (chain)   -- as the draft
theorem machConvF_lenOk_init : machConvF n senv env d e {} = some (some (r, st')) → st'.LenOk
```

### Predicted axioms
`run_*`, `sat_*` combinators, `out_*`, `sat_c*`, `step_good`, `readF_good`, `machXF_lenOk`,
`readersKeepLenOkF`: a subset of [propext, Quot.sound] (from `split`/`simp`/`by_cases` and from the
imported `machReserve_lenOk`, `loopRoot_inits_length`); `run_*`: none. No `sorryAx`, no `Classical.choice`
beyond what `by_cases` on a `Decidable` instance needs (none expected).

### Risks (PREDICTED; nothing was elaborated)
1. `split` on `chainStep`'s source match (after `revert hst; unfold chainStep`): splitter generation for the
   deep `Expr.app … (.const ``pure' _)` / `bind`/`next` patterns could be slow or refuse; fallback is to
   state the four arms as separate lemmas via `chainStep`'s equation lemmas.
2. `simp only [convStep]` on `convStep … (.app f a) st` (equation lemma for an overlapping-pattern def);
   fallback `unfold convStep; dsimp only` is in the proof.
3. `r5pair`: closing `match p with | (x, y) => k x y` by structure eta in `exact`; fallbacks split the pair.
4. `instS_sat`: `try dsimp only` must expose the `findIdx?` match (zeta of `let lvls`, iota of the pair
   match) before `split`.
5. Several `refine sat_X …` steps rely on `isDefEq` unfolding the step body (delta + matcher iota + zeta)
   to the expected combinator head; if one does not, insert `show`/`simp only [<body>]` there.
6. `convBvar_ok`'s `.state b n` leaf: three `Option.bind_eq_some_iff.mp` on the `do` block (after
   `Option.bind_eq_bind`).

## Integration of the re-homed R5 (integrator, 2026-10-15) — BUILT
Worker R5 (dd1f1c65, par/r-7) applied on poc 65eaccbb (lakefile conflict on appended lean_libs: kept both).
Run `r5` (cgrun, 3 GiB, swap 0, `-j 1`): `Tools.ShippingReaderFuelRun` built as written;
`Tools.ShippingReaderFuelR5` needed two fixes (no statement changed): the `r5pair` macro spliced `$t` where a
tactic sequence is expected (`$t:tactic`); the wildcard arms of `loopBody_sat` needed `unfold loopBodyStep`
before `refine sat_optK`. Then exit 0 (header updates rebuilt in run `r5b`). Imports: Defs / Kleene / Run and the
existing `ShippingReaderLenOk(Reserve)` — NOT `…FuelOldEq`.
Axioms: `step_good`, `readF_good`, `machConvF_lenOk`, `machNestedF_lenOk`, `machInstanceF_lenOk`,
`machInstanceSF_lenOk`, `machChainF_lenOk`, `machLoopBodyF_lenOk`, `machLoopRootF_lenOk`, `readersKeepLenOkF`,
`machConvF_lenOk_init` [propext, Quot.sound].
PROVED: R5 (`LenOk` preserved) for the FUEL functions, every fuel and every successful result
(`readersKeepLenOkF` = the old `ReadersKeepLenOk` statement for the fuel versions). NOT connected to the real
partial readers: the old `ReadersKeepLenOk` remains unproved; transferring R5 to the compiler's reader needs
the agreement chain (OldEq, A2 in progress) AND coverage of the real runs (O1).

## Round 2 (worker A, `par/r-6`, from poc 22908c5f) — OldEq repair: WRITTEN, NOT BUILT

Nothing was elaborated (workers never run `lean` / `lake`). Statements of every theorem and
definition unchanged (`OldFns`, `oConv` … `oLoopRoot`, `OldEq`, `step_tot`, `isSol_of_oldEq`,
`readF_agree_old`, … , `OldEqN`, `normStep_tot`); only proofs, file headers and imports changed.

**Diagnosis of the round-1 failures (log `a1-fuel-oldeq-errors.log`).** Line 675 is `chain_tot`,
line 685 is `loopRoot_tot` (not `loopBody_tot`: `loopBody_tot`, `nested_tot`, `inst_tot`,
`instS_tot`, the six probe/fold lemmas and `normStep_tot` raised no error). Every failing leaf
holds TWO equations on the same discriminant, one from each side, e.g.
`machHandleV env 0 h = some i¹` and `= some i`, `G.conv … = some (rhs'¹, st¹)` and `= some (rhs', st)`,
`¬ i¹ < st¹.kinds.size` and `i < st.kinds.size`; or `rootFloat v = .letE …` together with the
catch-all's `∀ …, rootFloat v = .letE … → False`; or `loopView? e = some (dom¹, body¹)` and
`= some (dom, body)`. `split` generalises a discriminant only inside the `match` it splits (the
other side is a different matcher constant), so the two sides were split independently; the
mixed leaves are contradictory, but `simp_all` did not close them (its normal forms: `¬ i < n`
becomes `n ≤ i`, `some a = some (mv, st)` is oriented `(mv, st) = a`, …). No leaf showed both
sides reduced to different values: **no difference between the fuel bodies and the old texts
was found**. `conv_tot` timed out because its `.app` arm has seven views in sequence: the
independent splits make a cross product (≈ 4^8 paths) inside one declaration.

**Repair.**
* `tot_align` (new macro): `repeat' (first | simp only [*, <run lemmas>, ite/Bool lemmas,
  ↓reduceIte] | split)`. After every `split`, its hypothesis (the discriminant equation of the
  branch) is used by `simp only [*]` on BOTH sides, so the old text's `match` / `if` on the same
  discriminant reduces in the same branch — one split per discriminant per path. Catch-all
  alternatives leave `∀ …, X = pat → False`; the old side's copy is split later and the
  contradictory branch is closed by `exfalso; solve_by_elim` (apply the negative hypothesis to
  the new equation); `contradiction`, `subst_vars; rfl`, `simp_all` remain as fallbacks. No
  closer proves a leaf whose two sides are reduced and different: such a leaf would fail the
  build (it would be a real transcription difference — none is expected, see above).
* `conv_tot` decomposed: per constructor of the input; `.app` per view with the view equations
  as explicit hypotheses (`conv_app_reg`, `_loopRead`, `_run`, `_inst`, `_instS`, `_mem`,
  `_readV`, `_default`, dispatcher `conv_app_tot` by `cases h : view`); `.letE` per constructor
  of `rootFloat v` (`conv_letE_tot`: `cases hR : rootFloat v`, so neither side keeps a catch-all
  `match`); `.lam` / `.forallE` one lemma each.
* `chain_tot`: per constructor; `.app` (`chain_app_tot`: `pure'`, `next`, catch-all; `next`'s
  pair match `machHandleV env 0 h, r` aligned by its split equations, its catch-all by
  `solve_by_elim`); `.letE` per constructor of `rootFloat v` (`chain_letE_tot`); others `rfl`.
* `loopRoot_tot`: `cases hv : loopView? e` → `loopRoot_none` / `loopRoot_some` (explicit `hv`).
* `nested_tot`, `inst_tot`, `instS_tot`, `loopBody_tot`, all `*_tot` probe / fold lemmas,
  `normStep_tot`: round-1 text, unchanged (they built).
* `run_pure` / `run_bind` / `run_bindO` deleted from OldEq; it imports
  `Tools/ShippingReaderFuelRun.lean` (worker R5, `par/r-7` dd1f1c65) — same names, statements.

**Per-lemma estimates (best guess, not measured; goals = leaves of the aligned analysis, worst
case; heartbeat option set locally where given, decomposition is the fix, not the budget):**

| lemma | goals (max) | expected time | maxHeartbeats |
|---|---|---|---|
| `conv_app_reg` | ≈ 12 (guard, `find?`, kind, init, conv dom, dom guard ×2, conv x) | 3–8 s | 400000 |
| `conv_app_loopRead`, `_readV` | ≤ 3 | < 2 s | default |
| `conv_app_run`, `_inst`, `_instS` | ≤ 3 | < 2 s | default |
| `conv_app_mem` | ≤ 4 | < 3 s | default |
| `conv_app_default` | ≤ 4 | < 3 s | default |
| `conv_app_tot` (dispatch) | 8 | < 1 s | default |
| `conv_lam_tot`, `conv_forallE_tot` | ≤ 4 | < 2 s | default |
| `conv_letE_tot` | 12 constructors × ≤ 10 | 10–30 s | 1600000 |
| `chain_app_tot` | ≈ 20 (outer 3 + `next` ≈ 6 + catch-all re-splits) | 5–15 s | 800000 |
| `chain_letE_tot` | 12 × ≤ 9 | 10–30 s | 1600000 |
| `loopRoot_none` | 1 | < 1 s | default |
| `loopRoot_some` | ≈ 16 (guards, mapM ×2, conv dom, dom guard, `findSome?`, `depth ≥ 1` ite, loopBody) | 5–15 s | 800000 |
| `conv_tot`, `chain_tot`, `loopRoot_tot` (dispatch) | 12 / 12 / 2 | < 2 s | default |

**Files / build order** (lean_lib lines appended at the END of `lakefile.lean`):
`Tools.ShippingReaderFuelRun` (par/r-7) → `Tools.ShippingReaderFuelOldEq` → `Tools.ShippingReaderFuelVerbatim`.
`Tools/ShippingReaderFuelLenOk.lean` is DROPPED from this branch (superseded by worker R5's
`Tools/ShippingReaderFuelR5.lean`, which proves the same `*_lenOk` / `readersKeepLenOkF` family
without importing OldEq). Verbatim: unchanged except its header (never built; risks as in §5:
`regMatch_view` / `ashrMatch_view` sparse-case proofs, `rw [regMatch_view]` relies on the inline
`match` sharing the matcher constant of `oConvV`'s, `oLoopRootV_eq` splits a name/list pattern).
Headers of Defs / Kleene updated to BUILT (doc-comment only).

**Risks (round 2).** (1) `simp only [*]` in `tot_align` rewrites with every hypothesis; a
hypothesis that rewrites a term into one containing itself would loop (none is produced by
these splits, but it is not checked). (2) `split` could pick a `match` of the old side first
where the fuel side has none left; alignment is symmetric, so this costs only order. (3) The
explicit view hypotheses must match the goal's terms syntactically (they are copied from the
text; if one does not, `tot_align` still splits that view and the mixed leaf is closed by
`simp_all` from the two equations — slower, not wrong). (4) `cases hR : rootFloat v` runs the
tail 11 times per `letE` lemma: the main time risk (heartbeats set to 1600000). (5)
`chain_app_tot` splits the outer `match` on the non-variable `.app g x` (generalised by `split`,
injection then substitutes `g`, `x`); round 1 split on the variable `e`. (6) `solve_by_elim` /
`exfalso` / `↓reduceIte` / `eq_self_iff_true` are core (v4.32.1 `Init`), not Mathlib.

STILL OPEN, unchanged: coverage, the compiled `partial` constants satisfying `OldEq` (outside the
kernel), a fuel `machineShape?` and the doubling driver, shadows. `readF_agree` stays conditional
on `IsSol (step senv)`; `readF_agree_old` / `_verbatim` are conditional on `OldEq` / `OldEqV`.

### Integration of round 2 (integrator, 2026-10-15) — OldEq BUILT; Verbatim NOT built
Only `…FuelOldEq.lean` and `…FuelVerbatim.lean` taken from 5e851930 (poc already had the Defs/Kleene header
updates and R5). Run `a2` (cgrun, 3 GiB, swap 0, `-j 1`, peak 1.16 GB): `Tools.ShippingReaderFuelOldEq` exit 0
AS WRITTEN — the per-view / per-constructor decomposition with `tot_align` closed every arm; no leaf with a
reduced fuel/old difference (a real difference could not have been closed). Axioms: `step_tot`,
`readF_agree_old`, `conv_tot`, `chain_tot`, `loopRoot_tot` [propext, Quot.sound]; `normStep_tot`,
`machNormF_agree_old` [propext, Classical.choice, Quot.sound].
PROVED: `readF_agree_old : OldEq senv G → readF senv n c = some r → G.app c = r` (and the same for machNorm via
`OldEqN`) — for every tuple of functions satisfying the old source equations (as transcribed in `OldEq`), a
finished fuel answer (success or refusal) is that tuple's answer. STILL CONDITIONAL / OPEN: `OldEq` is never
assumed about the real compiled constants (O2, outside the kernel); the link of `OldEq` to the VERBATIM source
text (`…FuelVerbatim`) FAILS to build (two `set_option … in` after docstrings, `rfl` / defeq failures at lines
~382–405, `simp` failures at ~56/81) and is not committed (kept for the next round); coverage of the real runs
(O1).

### Round 3 (worker A, efcd1b0a) — verbatim link BUILT as written
Run `a3` (cgrun, 3 GiB, swap 0, `-j 1`, peak 0.40 GB): `Tools.ShippingReaderFuelVerbatim` exit 0, no fix.
Axioms: `oldEq_of_oldEqV`, `readF_agree_verbatim`, `oConvV_eq`, `oInstSV_eq`, `oLoopRootV_eq`
[propext, Quot.sound]; `regMatch_view`, `ashrMatch_view`, `oInstV_eq` [propext];
`machNormF_agree_verbatim` [propext, Classical.choice, Quot.sound].
Causes found (no false equality; no transcription error in `OldEq`): array-literal cast on an abstract
argument list (view lemmas), lifted `let rec`s (`bundle`, `inst`) vs the shared helpers (proved equal by
recursion: `bundleV_eq`, `instV_eq`), a `do` join point vs a helper bind (`oInstV_eq` by cases), discriminant
alignment (`oLoopRootV_eq`).
PROVED NOW: `readF_agree_verbatim : OldEqV senv G → readF senv n c = some r → G.app c = r` — `OldEqV` is the
old source equations as written VERBATIM in Elab.lean (copied text), so: every tuple of functions satisfying
the compiler's own source equations agrees with every finished fuel answer (success or refusal); same for
`machNorm` (`machNormF_agree_verbatim`).
STILL OUTSIDE THE KERNEL / OPEN (unchanged): O2 — that the REAL compiled `partial` constants satisfy `OldEqV`;
O1 — that a run of the compiled code that returns gives a finite derivation (`Eval`), hence some fuel; the opaque
helpers; shadows beyond the 18-case grid. Production NOT switched.

## Worker G (`par/r-11`, from poc a3a1d2d4, 2026-10-16) — driver completion, headers, drift check — WRITTEN, NOT BUILT

### Driver eventual completion (`Tools/ShippingReaderFuelDriverComplete.lean`)
The bounded driver (`driveLoop` / `driveShape`, `…FuelDriver.lean`) stays a TEST tool: a final OUT means ONLY
"undecided within this trial budget". **A production switch must NEVER map a final OUT of a bounded driver to a
refusal or to the legacy route.** What is now stated (for a fuel-stable step, the SAME answer):
* generic: `StepStable step := ∀ {n m o}, step n = some o → n ≤ m → step m = some o`;
  `driveLoop_complete_le (hs) (hN : step N = some o) : ∀ r n k, N ≤ 2 ^ r * n → (driveLoop step r n k).1 = some o`;
  `driveLoop_complete : … → 0 < n → ∃ r, (driveLoop step r n k).1 = some o`;
  `driveLoop_complete_iff : 0 < n → ((∃ r, (driveLoop step r n k).1 = some o) ↔ ∃ N, step N = some o)`;
  `driveLoop_out_forever_iff : 0 < n → ((∀ r, (driveLoop step r n k).1 = none) ↔ ∀ N, step N = none)`;
* wrapper (`machineShapeF_stepStable` from `machineShapeF_stable`; no hypothesis on `start`, the driver starts at
  `max start 1 > 0`): `driveShape_complete_le (h : machineShapeF N … = some r) rounds start (N ≤ 2 ^ rounds)`,
  `driveShape_complete_ge (N ≤ rounds)`, `driveShape_complete : ∃ rounds, (driveShape rounds start …).res = some r`,
  `driveShape_complete_ok` (`r = some s`), `driveShape_complete_fail` (`r = none`, ordinary refusal),
  `driveShape_complete_iff`, `driveShape_out_forever_iff` (OUT for every round bound ⟺ OUT at every fuel);
* wrapper-level link with `…FuelEval` (finite executions): `WEval senv` (a `machNorm` call by `EvalN`, a block
  call by `Eval`), `ShapeRuns sm ps ci senv ai r` (the wrapper `shapeW` returns `r` against every table answering
  a finite list of calls, each with a finite derivation), `shapeRuns_fuel : ShapeRuns … r → ∃ N, machineShapeF N
  … = some r`, `shapeRuns_drive : ShapeRuns … r → ∃ rounds, (driveShape rounds start …).res = some r`,
  `shapeRuns_drive_le` (every `rounds ≥ N`). So: **a finite derivation of the wrapper ⟹ the driver eventually
  returns the same answer** (success or ordinary refusal).
NOT proved / missing: the converse `machineShapeF N … = some r → ShapeRuns … r` (needs `Compact (shapeW …)`,
the analogue of `compact_step` for the wrapper; not written — the fuel-level converse `driveShape_res` is
available); O1 (a returning run of the compiled `partial` `machineShape?` yields such a derivation) stays
outside the kernel, so nothing here says the driver answers whenever the OLD reader answers.

Build order: after `Tools.ShippingReaderFuelDriver` and `Tools.ShippingReaderFuelEval` (both BUILT),
`Tools.ShippingReaderFuelDriverComplete`. lean_lib (appended at the end of `lakefile.lean`):
`lean_lib «Tools.ShippingReaderFuelDriverComplete» where roots := #[`Tools.ShippingReaderFuelDriverComplete]`.
Predicted axioms: arithmetic `drv_*` none or [propext] (`omega` in `drv_le_two_pow_mul_pos`);
`driveLoop_complete*`, `driveLoop_out_forever_iff` ⊆ [propext]; `driveShape_complete*`,
`driveShape_out_forever_iff`, `machineShapeF_stepStable` [propext, Classical.choice, Quot.sound] (inherited from
`machineShapeF_stable` / `driveShape_res`); `wEval_fuel`, `wext_fuel_of`, `shapeRuns_*` [propext,
Classical.choice, Quot.sound] (from `eval_fuel` / `wtab_mono`).
Risks (PREDICTED; nothing elaborated): application of `hs : StepStable step` / `wtab_mono … : HLe …` (defs
unfolded at application — same pattern as the built files); defeq of `(driveShape …).res` with the `driveLoop`
projection (as in `driveShape_res`); `Nat.pow_succ` / `Nat.mul_two` / `Nat.two_mul` / `Nat.le_max_right` names
(`drv_max_pos` falls back to `omega`); the dependent `cases c` in `wEval_fuel`.

### Headers corrected (comment only)
`…FuelOldEq.lean` BUILT on poc fc697219 (run `a2`), `…FuelShape.lean` BUILT on poc 65eaccbb (run `f1`),
`…FuelEval.lean` BUILT on poc 36d6b5ef (run `e1`), `…FuelVerbatim.lean` BUILT on poc 8fac0511 (run `a3`).

### Source version of the copies + DRIFT CHECK
`OldEqV` / `OldEqNV` (`…FuelVerbatim.lean`), `OldEq` / `OldEqN`, the fuel bodies (`…FuelDefs.lean`) and the
wrapper fragments (`…FuelShape.lean`) copy source text of `Sparkle/Compiler/Elab.lean`. Source version (now in the
Verbatim header): Elab.lean last changed in commit 945a799ad77276a4285a7160097873fc7a7f13c7, blob
233f50e03a06eb796bed2644109ad3044213d203 (the same blob as at c1c651a0, where the line numbers were taken).

`scripts/shipping-coverage/oldeqv_drift.py` is a **comparison aid, NOT a correctness proof**: it extracts the
text of `machConv`, `machNested`, `machInstance`, `machInstanceS`, `machChain`, `machLoopBody`, `machLoopRoot`,
`machNorm` (the definitions OldEqV / OldEqNV copy; the copied helpers — `let rec bundle`, `let rec inst`, the
`foldlM` / `findSome?` functions, the inline `register` / `ashr` matches — are inside these texts) and
`machineShape?` (copied by `…FuelShape.lean`) from the current Elab.lean (header line to the next column-0
line) and compares it with `scripts/shipping-coverage/oldeqv_snapshot.txt` (generated from blob 233f50e0; each
entry `=== name sha256 lines` + text).
* `python3 scripts/shipping-coverage/oldeqv_drift.py` → exit 0 "no drift"; exit 1 "DRIFT in: <names>"; exit 2 a
  definition not found. `--diff` prints a unified diff per drifted definition; `--elab PATH` checks another file.
* Checked on the current tree: exit 0 (9 definitions). Self-test: a one-line edit inside `machChain` in a copy
  → exit 1, `DRIFT in: machChain`, with the diff.
* On drift: re-examine and re-prove the copies (`oldEq_of_oldEqV`, `step_tot`), THEN regenerate with `--update`.
  A clean result says only that the copied TEXT is unchanged; helpers referenced by name (not copied) and O2
  (the compiled code satisfies its equations) are not covered.

### Integration of worker G (76290ce3) — BUILT as written
Applied on poc 8d7648ea. `python3 scripts/shipping-coverage/oldeqv_drift.py`: "no drift (9 definitions match
the snapshot)", exit 0. Run `g1` (cgrun, 3 GiB, swap 0, `-j 1`): the four header-updated files (OldEq, Shape,
Eval, Verbatim) and `Tools.ShippingReaderFuelDriverComplete` exit 0. Axioms: `driveLoop_complete`,
`driveLoop_complete_iff`, `driveLoop_out_forever_iff` [propext, Quot.sound]; `driveShape_complete(_ok/_fail/_iff)`,
`driveShape_out_forever_iff`, `shapeRuns_fuel`, `shapeRuns_drive` [propext, Classical.choice, Quot.sound].
PROVED: driver eventual completion — `machineShapeF N … = some r → ∀ start, ∃ rounds, (driveShape rounds start …).res
= some r` (success and ordinary refusal); OUT forever ↔ every fuel OUT; a finite wrapper derivation (`ShapeRuns`)
→ the driver eventually returns the same answer. NOT written: the reverse at wrapper level (needs
`Compact (shapeW …)`). Unchanged: O1/O2 outside; production not switched; the bounded driver is a test tool.

## Wrapper compactness (worker J, `par/r-14`, from poc 20304f50, 2026-10-17) — WRITTEN, NOT BUILT

Reviewer 2026-10-17, item 1. New file `Tools/ShippingReaderFuelShapeEval.lean` (imports only the BUILT
`Tools.ShippingReaderFuelDriverComplete`); no existing statement changed; no compiler change.
Build order: `lake build Tools.ShippingReaderFuelShapeEval` (after `…FuelDriverComplete`, already built).
lean_lib (appended at the end of `lakefile.lean`):
`lean_lib «Tools.ShippingReaderFuelShapeEval» where roots := #[`Tools.ShippingReaderFuelShapeEval]`.

### What is proved (as written)
* `compact_shapeW : Compact (shapeW sm ps ci senv ai)` — the wrapper reads finitely many table answers (the wrapper
  counterpart of `compact_step` / `compact_normStep`): one table read each (`compact_wNorm`, `compact_wConv`,
  `compact_wChain`, `compact_wLoopRoot`), the reader fragments `compact_shapeStart`, `compact_shapeRootLet`,
  `compact_shapeBody` (crunch `wcompact_base`, as `compact_base`), composed along `shapeW` with `compact_optK` /
  `compact_bind` / `compact_bindO` / `compact_foldO` / `compact_pure`. Pure fragments (`shapePre`, `shapeMid`,
  `shapePost`, `machReserve`) are single discriminants / values, never inspected.
* `wEval_of_wtab` (a table answer at fuel `n` is a finite execution: `fuel_evalN` / `fuel_eval`).
* `fuel_shapeRuns : machineShapeF N … = some r → ShapeRuns … r` — the converse of `shapeRuns_fuel`.
* `shapeRuns_iff : ShapeRuns … r ↔ ∃ N, machineShapeF N … = some r`; `shapeRuns_ok_iff` (`r = some s`, success),
  `shapeRuns_fail_iff` (`r = none`, ordinary refusal); `shapeRuns_det`.
* `shapeRuns_drive_iff start r : ShapeRuns … r ↔ ∃ rounds, (driveShape rounds start …).res = some r` (+ `_ok` /
  `_fail`); `shapeRuns_none_iff` (no finite execution ⟺ OUT at every fuel), `shapeRuns_drive_none_iff` (⟺ the
  driver is OUT for every round bound).

### What stays outside
* **O1**: that a RETURNING run of the compiled `partial` `machineShape?` yields a finite derivation (runtime fact,
  not kernel). So "the old reader answers ⟹ the driver answers" is still NOT claimed.
* **Opaque helpers** (`rootFloat`, `zetaAll`, `rawNode`, `machNormNode`, `packTupleInputs`, `Expr` primitives) are
  parameters consumed as values; their termination / runtime agreement (O3/O4) not claimed. O2 unchanged.
* Production not switched; the bounded driver remains a test tool (OUT = undecided within budget).

Predicted axioms: `compact_*`, `wEval_of_wtab` — none or [propext]; `fuel_shapeRuns`, `shapeRuns_iff`,
`shapeRuns_drive_iff`, `shapeRuns_none_iff` — [propext, Classical.choice, Quot.sound] (inherited from
`shapeRuns_fuel` / `driveShape_*`).

Risks (PREDICTED; nothing elaborated): the `repeat' wcompact_base` crunch on `shapeRootLet` (an `if` on
`isAppOfArity`, a two-discriminant `match`, a `let (x, lets) := if …` destructuring) and `shapeBody` (`let v := match
m.wrap? …`) — same pattern as `compact_instArg` / `compact_loopNext`; the explicit `refine` chain in
`compact_shapeW` (zeta of `let m`, matcher reduction after `rcases`) has a crunch fallback inside `first`;
`unfold ShapeRuns` before the anonymous constructor; dependent `cases c` in `wEval_of_wtab` (as `wEval_fuel`).

### Integration of worker J (987b6612) — BUILT as written
Applied on poc 20304f50. Run `j1`: `scripts/shipping-coverage/cgrun.sh -n j1 -m 3G -t 7200 -j 1 -- lake build
Tools.ShippingReaderFuelShapeEval` → exit 0, no fix (header update rebuilt in run `j1b`, exit 0). Axioms:
`wEval_of_wtab` [propext, Quot.sound]; `compact_shapeW`, `fuel_shapeRuns`, `shapeRuns_iff`, `shapeRuns_ok_iff`,
`shapeRuns_fail_iff`, `shapeRuns_det`, `shapeRuns_drive_iff`, `shapeRuns_none_iff`, `shapeRuns_drive_none_iff`
[propext, Classical.choice, Quot.sound].
PROVED: wrapper compactness and the converse, hence `ShapeRuns … r ↔ ∃ N, machineShapeF N … = some r` and
`ShapeRuns … r ↔ ∃ rounds, (driveShape rounds start …).res = some r`, for success and ordinary refusal; no finite
execution ↔ every fuel OUT ↔ the bounded driver OUT for every round bound. OUTSIDE (unchanged): O1 (a returning
compiled partial run → `ShapeRuns`), O2, opaque helpers.
