# Worker A (reader, fuel), round 3 (`par/r-3`): a fuel-indexed TOTAL candidate of the machine reader

Base poc `c1c651a0`. **WRITTEN, NOT BUILT.** Nothing here was compiled or run.
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
