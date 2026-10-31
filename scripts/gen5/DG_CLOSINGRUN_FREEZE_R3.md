# DG-CLOSINGRUN next unit — freeze r3 (Issue sparkle-gen5-dg-closingrun)

**FOR REVIEW. Design only: every Lean block is UNELABORATED text; nothing here is built or proved.** No Lean file is edited by
this commit. Base: `kjob/g5cr-r2` `6f3c8ee5` (CR0-CR4 + conditional `closingRun_of_run`; clean issue-linked build crv-6f3c8ee5
exit 0, 755 jobs, scoped approved at 6f3c8ee5), plus the comment/docs sync `b872f5da`. Follows `DG_CLOSINGRUN_FREEZE.md` (rev0 + §8).

Wording: "not found" = this survey did not find a supplier / route; it is not a claim of impossibility. A mutant is a rejection by
signature / defeq of a changed statement, not a semantic counterexample. A new unsupplied premise is never counted as supply.
**No new TRUSTED boundary, no law, no change to FG / guarantees, no shared-definition change** (`Tools/ShippingGen2Defs.lean`,
`T1Hyp`, `T1HypND`, `Elab*.lean` untouched; `GenWF` not strengthened; no scope reduction such as `ReflectsAll = False`).
The final T1 / FG connection is NOT done by this unit.

## 0. Survey (what exists at the base; checked by grep in this worktree and with `git grep` on the other `kjob/*` branches)
| item | finding |
|---|---|
| `GeneratedAt`, `genP`, `genP_generated`, `GenData`, `genSem` | Not in the tree at the base. Text only: `par/gen5-t2:scripts/gen5/DGEN_FREEZE.md:221` (def), `kjob/g5cv-r5:scripts/gen5/DG_SEM_FREEZE_REV2.md` (P12, a roadmap row, "Nothing about P3 onward is elaborated"). `Tools/ShippingGen5SemPkg.lean` (kjob/g5sm-r3) has `SemPkg`, `Pkg.toSem`, `genPkg` only. This survey found no Lean definition of `GeneratedAt` on any branch. |
| `CacheAcc` | `Tools/ShippingGen5Acc.lean:181` on `kjob/g5ac-r2/r3` (not in the base); `acc_of_run` not found. |
| `entryConst`, `instancePredicate`, `userInliner`, `structEnv` | in the tree (`Sparkle/Compiler/Elab.lean:5272, :5397, :3387, :4394`). So the ARGUMENTS of `GeneratedAt` in DGEN §3 can be written now; `GeneratedAt` itself cannot. |
| `hrow` supplier | none found. `OneOutNoMemRow` is a decided Bool row (`DataBridge.lean:37`); DATA_SUPPLY_FREEZE rev0-rev3 list `OneOutNoMemRow` / R6 (`child? = none` coverage) as unsupplied (`kjob/g3ds-ds8:scripts/gen3/DATA_SUPPLY_FREEZE_REV3.md:127`). The consumer in `soundX_ships_at` uses `hord1` (semantic form), reached from `hrow` by `hord_of_row` (`DataBridge.lean:57`). |
| concrete `Laws mref cref` / `RefLawsAOps` instance | none found in `Tools/` or `Tests/` (grep for `Laws.mk` / `: Laws ` terms: only binders). A concrete world satisfying `InvAt`, `AdmCtx`, `T1HypND` is therefore not available. |
| depth 0: `Start` (`Defs:52`) | `AdmCtx ∧ JQC L.O 0 w`. It does NOT give `CacheShips (cv w)`, so `InvAt L P Reach 0 w` is not given. |

## 1. Unit U-A: depth-generic and depth-0 wrappers (provable now; new file, no existing name or type changed)
New file `Tools/ShippingGen5ClosingRun2.lean` (imports `Tools.ShippingGen5ClosingRun`), `namespace Tools.ShippingGen5ClosingRun2`,
`set_option autoImplicit false`; check file `Tests/Gen5/ClosingRun2Check.lean`. `ClosingRun`, `PortsServed`, CR0-CR4 and
`closingRun_of_run` of `Tools.ShippingGen5ClosingRun` are NOT edited; **`stop_of_run` keeps its name and type** (the fallback Issue
g4fb-fb6 may reuse it as a candidate supplier; its depth must be `dv w ≥ 1`, `hKI` at `dv w + 1`, and the integration is a separate check).

```lean
/-- The shared `∃` block of `ClosingRun`, as a stand-alone Prop (definitionally the type of `ClosingRun.shared`). -/
def ClosingShared (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld)
      (t t' : Sparkle.IR.AST.Module) (d₀ : Design) (children : List Res),
    <exactly the 7 conjuncts of ClosingRun.shared>

theorem ClosingRun.closingShared (h : ClosingRun L P Reach mctx cctx X p Gen w w' raw D) :
    ClosingShared L P Reach mctx cctx X p Gen w w' raw D := h.shared      -- by `rfl`-typed projection
```
(`mctx cctx` appear only through the premises of the statement; if `ClosingShared` would not mention them they are dropped from the
def and the comparison in the Check is by the Expected type. The implementer writes the def with exactly the binders the block uses.)

```lean
/-- (CR1') `InvAt (D+1)` at the reads chain's `w5` from `JQC D` and `D = 0 ∨ CacheShips` (the general form of
`invAt_w5_of_runReadsAt`, whose hypothesis `InvAt (dv w) w` is the case `D = dv w`). -/
theorem invAt_w5_of_runReadsAt_JQC (L) (P) (Reach) {mctx cctx} (hA : AdmCtx L.O.quiet mctx cctx)
    {X w w' raw D b ci envR envR' shape w5 w6}
    (hw : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hr : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6) :
    InvAt L P Reach (dv w + 1) w5
-- proof: the body of `invAt_w5_of_runReadsAt` with `coreHead_invAt0 … hw hc hh`.

/-- (SH) The shared block at any depth. The `hord` premise is the SEMANTIC form (below), weaker than `hrow`. -/
theorem closingShared_of_run (L) (P) (Reach) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] → ∀ k, k < q.d.shape.insts.length →
        (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk) {mctx cctx} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p) {w w' raw D}
    (hw : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen) (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR') :
    ClosingShared L P Reach mctx cctx X p Gen w w' raw D
```
Proof plan: the body of `closingRun_of_run` after `hdecl`, with `hst.1.1 := hw.1`, `hc' := hc.imp id (fun _ => hw.2)` for
`runReads_of_run`, `invAt_w5_of_runReadsAt_JQC`, and `hord1 := fun hf k hk => hord p hDp hf k hk`. Same `t t' d₀ children` as the trace (CR2 takes them
as arguments). No `T1Hyp.dec`; only `defines`, `closes`, `closed`, `pkg`. No `hrow`, no `hlim`.

**`hord` instead of `hrow`** is a supply-path change, not a supply: `hrow ⇒ hord` is `hord_of_row` (`DataBridge:57`, already
built), so `closingRun_of_run` (with `hrow`) is recovered as a corollary (its Check text is unchanged; a corollary
`closingRun_of_run'` is NOT added, the old theorem stays). It lets the data-supply units that prove R6 / U1 in the semantic form
(`postFacts_of_hord`, `PostFactsProof.lean:156-`) plug in without going through the Bool row. **`hord` is not supplied by this unit
(R6 and `OneOutNoMemRow` coverage: no run-derived supplier found).**

```lean
/-- (W0) The depth-0 start wrapper: `Start`'s own `JQC 0` and `dv w = 0` give `InvAt 1` at `w5` (the core head's depth-0 clear
establishes the cache invariant, as in `coreHead_invAt0`'s `D = 0` branch). `InvAt 0 w` is NOT claimed. -/
structure ClosingRun0 (L) (P) (Reach) (mctx cctx) (X) (p) (Gen) (w w' raw D) : Prop where
  run    : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  start0 : Start L mctx cctx w ∧ dv w = 0
  shared : ClosingShared L P Reach mctx cctx X p Gen w w' raw D
-- NO `stop` field: `stop` at depth 0 is not supplied (see §4).

theorem closingRun0_of_run … (hs : Start L mctx cctx w) (hd0 : dv w = 0) (… as closingShared_of_run, with hw := hs.2, hc := Or.inl hd0, hA := hs.1 …) :
    ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D
```
`hIH`, `hKI` at depth `1` stay premises (supplied inside the T1 induction by `ih_allPF`, not for the top-level call; that induction is another unit).
`ClosingRun0` is a NEW structure; it is not a drop-in replacement of `ClosingRun` (no `stop`, `start` is `JQC 0` not `InvAt 0`).

## 2. Unit U-B: `GeneratedAt` concretization as an instance, with the predicate abstract
`GeneratedAt` is not in the tree (§0), so it is not written here and no copy of it is made. The concrete SHAPE of `Gen` from DGEN §3 is
written with the predicate `GA` as a parameter standing for `GeneratedAt P X`:
```lean
theorem closingRun_of_run_ga (… the binders of `closingRun_of_run` up to `hrun`, with `hrow` kept …)
    (GA : ConstantInfo → StructEnv → Pkg ι dom → Prop)
    (hGA : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 →
      GA (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)) (structEnv envR') p) :
    ClosingRun L P Reach mctx cctx X p
      (fun ci envR envR' => GA (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR))
        (structEnv envR') p) w w' raw D :=
  closingRun_of_run … (Gen := fun ci envR envR' => GA …) hGA
```
It is an INSTANCE of `closingRun_of_run` (not the converse). When DG-SEM/DG-GENP land, `GA := GeneratedAt P X` and `hGA` is replaced by the
four premises of DGEN §3 / rev0 §3.3 (`genP_generated`, DG-COVER, DG-ENV `ReadsAt`, DG-ACC). `hGA` is NOT supply: it is exactly the
unsupplied `hGen` with `Gen` unfolded. Note `entryConst true false []` is written as in DGEN §3 (`certifiedFrontEnd = true`, `symbolicMode = false`, `parameters = []`);
the Check compares the unfolded `Gen` with an independent expected type and rejects `structEnv envR` (instead of `envR'`) at the second argument as a one-point mutant.
**Not done / not claimed:** `GeneratedAt`, `genP`, `genP_generated`, DG-COVER `cover_of_run`, DG-ENV C0 / `QuietStrength` / `AdmDown`, DG-ACC. Route not found by this survey for `hGA`; the
supply is the other Issues'.

## 3. Unit U-C: non-vacuity, conditional (no scope reduction)
A concrete `ClosingRun` needs a concrete `Laws`, `Pkg`, run, `T1HypND` and a `GeneratedAt` witness; this survey found none (§0). So the
unit proves only CONDITIONAL, named facts:
```lean
/-- The premises of `closingRun_of_run` as ONE named bundle (nothing new: the same hypotheses, in the same order). -/
structure ClosingPremises (L) (P) (Reach) (DataOk) (mctx cctx) (X) (p) (w w' raw D) (Gen) : Prop where
  hrow … hT … hA … hR … hP … hst … hIH … hKI … h1 … hrun … hGen   -- field types = the binder types of `closingRun_of_run`

theorem closingRun_nonempty_of_premises (h : ClosingPremises …) :
    Nonempty (ClosingRun L P Reach mctx cctx X p Gen w w' raw D)      -- = `⟨closingRun_of_run … ⟩`

/-- `Gen` is not decorative: `ClosingRun` yields the generation proposition at the run's own reads (a projection of `shared`). -/
theorem gen_of_closingRun (h : ClosingRun … Gen …) :
    ∃ b ci envR envR' w5 w6, RunReadsAt … p.d.shape w5 w6 ∧ Gen ci envR envR'
theorem not_closingRun_false (h : ClosingRun … (fun _ _ _ => False) …) : False
```
These show: the premises are the ONLY thing between the data and `Nonempty (ClosingRun …)` (the bundle is a restatement), and the
conclusion depends on `Gen` (so `Gen := True`-style weakenings are visible, not silent). **They are not a non-vacuity proof.** Non-vacuity
(some world / `Pkg` / run satisfying every premise) is NOT supplied; no route found (no concrete `Laws` in the tree). Not weakened by
`ReflectsAll = False`, `Gen := True` or any other scope reduction.

## 4. Supplier table for the remaining rows (status after this unit, if approved)
| row | after this unit |
|---|---|
| `hrow` / `hord` (R6) | **U**: no run-derived supplier found. `hord` form is the plug point (U-A). Not supplied. |
| `hGen` / `GeneratedAt` | **W/U**: instance shape `closingRun_of_run_ga` (U-B); `GeneratedAt`, `genP_generated`, COVER, ENV, ACC not in tree. Not supplied. |
| non-vacuity | **U** (conditional named facts only, U-C). |
| depth-0 `start` | wrapper `ClosingRun0` (U-A) gives `Start ∧ dv w = 0`, `InvAt 1` at `w5` and the shared block, **given** `hIH`, `hKI` at depth 1. |
| depth-0 `stop` | **U**: `core_tripleAInv` needs `1 ≤ D` (the depth-0 core run clears the cache); this survey found no `Triple` giving `InvAt 0` at the end world of a depth-0 core run. Not supplied; `ClosingRun0` has no `stop`. |
| final T1 / FG connection | **not done**: needs the T1 induction (`ih_allPF`) to supply `hIH`/`hKI`, `hord`, `hGen`, and a depth-0 `stop`-free consumer. Not claimed. |

## 5. Check plan (`Tests/Gen5/ClosingRun2Check.lean`)
- Independent Expected TYPES (fully bound `def … : Prop := ∀ …`, written without referring to the implementation): `ClosingShared` (against the
  telescope of `ClosingRun.shared`'s type: `isDefEq`), `invAt_w5_of_runReadsAt_JQC`, `closingShared_of_run`, `ClosingRun0` (structure comparison as in `ExpClosingRun`),
  `closingRun0_of_run`, `closingRun_of_run_ga`, `closingRun_nonempty_of_premises`, `gen_of_closingRun`, `not_closingRun_false`.
- One-point well-typed mutants (same comparator; rejection by signature / defeq, NOT semantic counterexample): `hord` with `k < length` dropped; `hord` with `instFields ≠ []`;
  `hc` dropped (`CacheShips` at depth ≥ 1 missing); `InvAt dv w` at `w5`; `ClosingRun0` with `stop`; `ClosingRun0.start0` with `dv w = 1`; `GA` at `structEnv envR` instead of `envR'`;
  `entryConst false …` (certifiedFrontEnd flipped); `Gen := True` in `closingRun_of_run_ga`; `T1Hyp` instead of `T1HypND`.
- **Reducible-comparator positive controls (audit improvement recommended by the reviewer at 6f3c8ee5):** the mutant comparator is run at REDUCIBLE
  transparency; for every mutant the SAME comparator is first shown to ACCEPT the independently written Expected TYPE of the real declaration (positive control,
  so a rejection is not an artifact of a too-weak `isDefEq`), and the existing `ClosingRun` / `ExpClosingRun`, `stop_of_run`, `closingRun_of_run` Expected types of
  `ClosingRunCheck` are re-accepted under the reducible comparator (positive control), without editing `ClosingRunCheck.lean`.
- Closure audit (full value + type closure, explicit): no `T1Hyp` field, no `core_reads_invAt0`, `BodyStepC`, `soundX_ships_ran`, `servedShips0_proved`, `TopShips`, `ofReduceBool`; negative controls
  (direct, other-namespace helper, raw `.proj`, recursor) detected and clean controls not flagged; no reach to `GeneratedAt` / `genP` (not in the tree). AXIOMS: standard.
- Build: coder runs the clean issue-linked build; the implementing agent commits with "clean build は coder が実行".

## 6. Questions for the reviewer (none touches a law / TRUSTED / FG)
1. U-A `hord` (semantic form) instead of `hrow` in the NEW theorems, `closingRun_of_run` unchanged: accepted?
2. U-B: `GA` as an abstract predicate parameter (no copy of `GeneratedAt`): accepted, or wait for DG-SEM?
3. U-C: is the named-bundle / projection form an acceptable "conditional witness", with the non-vacuity row recorded as unsupplied?
4. `ClosingRun0` without `stop` as the depth-0 wrapper (the alternative: no depth-0 wrapper until a depth-0 `InvAt 0` end-world supplier is found).

## 7. Not claimed
`hrow`/`hord`, `GeneratedAt`/DG-GENP/DG-COVER/DG-ENV/DG-ACC, concrete non-vacuity, depth-0 `stop`, T1 / G-SERVED / G-POST / M5 / FG completion, Issue completion. This document builds and proves nothing.
