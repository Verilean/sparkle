# Worker R round 2 (`par/r-2`): the memory-only generator on the reader's output facts, and the output-NAME invariant

Base poc `17560812`. **WRITTEN, NOT BUILT.** Nothing here was compiled or run.
READ = read in this tree; PREDICTED = worked out by reading.

## 0. Files, commits, build order

| commit | file | content |
|---|---|---|
| 1 | `Tools/ShippingReaderMemOnlyCloses.lean` (new) | `machineClosesAt_of_memOnlyDataR_names` |
| 1 | `Tools/ShippingNoPortsMemCommand.lean` | `#machine_no_ports_mem` switched to the reader; `Ctx.oldData`; `#machine_no_ports_mem_olddata[_try]` (the previous path) |
| 1 | `Tools/ShippingNoPortsMemKidCommand.lean` | a memory-machine callee may have `k.noPortsMem_dataR` instead of `k.noPortsMem_data` |
| 1 | `Tests/Compiler/NoPortsMemGenOldDataTest.lean` (new, TARGET-ONLY) | old vs new path on one tree, five declarations |
| 1 | `Tests/Compiler/NoPortsMemGenFamilyTest.lean` (target-only), `NoPortsMemGenOldNamesTest.lean` (target-only), `NoPortsMemGenCompareTest.lean` (in AllTests) | audits updated to the new names (see §1.4) |
| 1 | `lakefile.lean` | `Tools.ShippingReaderMemOnlyCloses` appended at the END |
| 2 | `Tools/ShippingReaderOutNames.lean` (new, leaf) | `outNames_of_reader`, `outNames_of_core`, `outsNodup_of_core`, `outsNe_of_core`, `outsOk_of_core` |
| 2 | `lakefile.lean` | `Tools.ShippingReaderOutNames` appended at the END |
| 2 | this file | the record |

No file under `Sparkle/` changed. No existing theorem statement changed. ALLOWED unchanged.

Build order (serial):

1. `lake build Tools.ShippingReaderMemOnlyCloses` (imports `ShippingReaderOutsMemOnly`, `ShippingMemOnlyNames`, both BUILT).
2. `lake build Tools.ShippingNoPortsMemCommand Tools.ShippingNoPortsMemKidCommand` (then everything importing them rebuilds: `ShippingNoPortsMemSeqCommand`, `ShippingDesignCoverage`, `ShippingNoPortsMemKidSweep`, …).
3. `lake build Tests.Compiler.NoPortsMemGenCompareTest` (AllTests), `Tests.Compiler.NoPortsMemKidTest` (AllTests; runs the switched command then the kid command), `Tests.Compiler.MemDepthProbeTest`, `Tests.Compiler.MemParentFreeTest`, `Tests.Compiler.MemParentClosesTest` (these use `memCounterH.noPortsMem_*`, see §1.4).
4. Target-only, ONE AT A TIME (they share `…_regen` names, never co-import): `Tests.Compiler.NoPortsMemGenFamilyTest`, then `Tests.Compiler.NoPortsMemGenOldDataTest`, then (separately) `Tests.Compiler.NoPortsMemGenOldNamesTest`.
5. `lake build Tools.ShippingReaderOutNames` (imports `ShippingReaderOutsInv`, BUILT). Independent of 1–4.

```
lean_lib «Tools.ShippingReaderMemOnlyCloses» where
  roots := #[`Tools.ShippingReaderMemOnlyCloses]

lean_lib «Tools.ShippingReaderOutNames» where
  roots := #[`Tools.ShippingReaderOutNames]
```

## 1. Piece 1: `#machine_no_ports_mem` takes `outTy` / `outScalar` from the reader

### 1.1 What the command generates now

| name | new path (default) | previous path (`…_olddata`, and `…_oldnames`) |
|---|---|---|
| `entry calls slots domB callWidths callArgs outChars` | decided | decided (same statements) |
| `outTy`, `outScalar` | **not generated** | decided |
| `data` | — | `MemOnlyData f.machineData nDecl aw dw` |
| `dataR` | `MemOnlyDataR f.machineData nDecl aw dw` (the 12 fields without `outTy`/`outScalar`) | — |
| `runFacts outsG0 kidsMemG designP0` | `memOnly_*_of_reader dataR hB hcore hpost entry closes [hg]` | `memOnly_* data …` — SAME statements |
| `alias argsN field argsNd outHead closeData` | decided / packed | same |
| `closes` | `machineClosesAt_of_memOnlyDataR_names dataR closeData` | `machineClosesAt_of_memOnlyData_names data closeData` (`…_oldnames`: with name lemmas) — SAME statement |
| `machine_design_noPortsR0[_closed]` | unchanged construction (uses the four run theorems and `closes` by name) | same |

The two output facts come from `outTy_of_core` / `outScalar_of_core`
(BUILT, every reader result) at the `hcore` / `entry` the four run theorems
already bind. The closing has no run, and does not need them: its proof
reads only `ok body calls slots domB fne mem` of the data
(`machineClosesAt_of_memOnlyData` 169–171, READ), all in `MemOnlyDataR`.

```lean
theorem Tools.ShippingReaderMemOnlyCloses.machineClosesAt_of_memOnlyDataR_names
    {declName : Name} {d : MachineData} {nDecl aw dw : Nat}
    (D : MemOnlyDataR d nDecl aw dw) (C : MemOnlyCloseData d) :
    MachineClosesAt mctx mref cctx cref declName d.shape
```

(by the BUILT `machineClosesAt_memOnly_names`).

`oldNames` implies `oldData` (`core`: `oldData := oldData || oldNames`): the
name path of par/b-30 was written over `MemOnlyData`.

### 1.2 The comparison (target-only, never a generator compared with itself)

`Tests/Compiler/NoPortsMemGenOldDataTest.lean` imports
`NoPortsMemGenFamilyTest` (which now runs the NEW path on the six memory-only
parents) and runs `#machine_no_ports_mem_olddata_try f "REBUILT"` on
`memCounter`, `syncNarrow`, `memWide`, `twoMems`, `mixedMems`. The previous
path finds every shared name and takes the compare path: it re-elaborates
under `…_regen` and throws unless the type is `isDefEq` the existing one.
The audit then asserts, per declaration, the 20 shared names
(`sharedNames`: 18 lemmas + 2 endpoints) with `n_regen` on standard axioms
and `isDefEq` types; the run theorems / closing apply the new constants
(new) and the old ones (`_regen`), not the other's; `dataR`, `data`,
`outTy`, `outScalar` exist. Acceptance: compared pairs `= 5 × 20 = 100`, non-zero.
Logged: `NOPORTS MEM OLDDATA COMPARE <f>: …` and a total line.

PREDICTED: class `REBUILT` for all five; 100 pairs `isDefEq`.

### 1.3 What is decided per declaration now (memory-only parents)

Before: 15 decides (`entry calls slots domB outTy callWidths callArgs outChars
outScalar alias argsN field argsNd outHead` + the `isMem` rfl's). Now: 13
(no `outTy`, `outScalar`). Still decided: `outChars` (every char `charOk`),
`outHead` (no output starts with `i`) — NOT implied by the reader (§2.3).

### 1.4 Dependents touched (READ which ones use the removed names)

* `ShippingNoPortsMemKidCommand`: required `k.noPortsMem_data` for a memory-machine callee; now accepts `noPortsMem_data` OR `noPortsMem_dataR`; `genKidM` reads the existing one. Its `outTy` / `outScalar` fields were already `first | exact ($md).outTy | decide`: with `dataR` the `exact` fails and `decide` runs (per-callee decide, as before for callees without data). Statement of `k.machine_genKidM0` unchanged.
* `NoPortsMemGenCompareTest` (AllTests): lemma list `data → dataR`; asserts `data`/`outTy`/`outScalar` NOT generated; the hand `memCounter_data` comparison is now `MemOnlyDataR` at the hand type's four arguments `isDefEq` `memCounter.noPortsMem_dataR`'s type.
* `NoPortsMemGenFamilyTest` (target-only): lemma list; `oldDataLemmas` must be absent; closing constant `machineClosesAt_of_memOnlyDataR_names`; the four run theorems apply `memOnly_*_of_reader`.
* `NoPortsMemGenOldNamesTest` (target-only): `genNew` is now `machineClosesAt_of_memOnlyDataR_names`; the old path there also GENERATES `outTy`/`outScalar`/`data`.
* `MemParentFreeTest` (hand): reads `memCounterH.noPortsMem_data.{calls,slots,domB,outTy,outNames,outScalar,cw,args}` each under `first | exact … | decide`. PREDICTED: the `exact`s fail (unknown constant) and `decide` runs — slower, same theorem. If the integrator prefers, `memCounterH.noPortsMem_dataR.<field>` works for all but `outTy`/`outScalar` (not edited here).
* NOT switched: `#machine_no_ports_mem_seq` (`ShippingNoPortsMemSeqCommand` 549/556 decide `outTy`/`outScalar` into its own `MemSeqData`); `#oneout_gen`, `#oneout_any_gen` (decide `outTy`). Same switch applies (they have `hcore`/`entry` in the run theorems); follow-up.

## 2. Piece 2: the output-NAME facts for every reader result

### 2.1 Statements (`Tools/ShippingReaderOutNames.lean`)

```lean
theorem ite_none_inv_not (h : (if c then none else x) = some b) : ¬ c
def outsTest (outs : List (String × MixedGateBinder)) : Bool :=
  outs.isEmpty || !outs.all (fun o => outNameOk o.1) || !decide (outs.map (·.1)).Nodup
theorem machineShape?_outsTest (h : machineShape? sym params (.defnInfo d) senv allow = some sp) :
    ∃ o, declOuts? senv d.type = some o ∧ outsTest o.2 = false
theorem outsTest_facts (h : outsTest outs = false) :
    outs ≠ [] ∧ (∀ p ∈ outs, outNameOk p.1 = true) ∧ (outs.map (·.1)).Nodup
theorem machOutFields_names / machOutFields_ne_nil / machOutFields_nameOk     -- pure
theorem outNames_of_reader (h : machineShape? sym params ci senv allow = some sp) :
    sp.layout.outs ≠ [] ∧ (∀ o ∈ sp.layout.outs, outNameOk o.name = true) ∧
      (sp.layout.outs.map (·.name)).Nodup
theorem outNames_of_core (hcore) (entry) : <same for MachineDefines' shape>
theorem outsNodup_of_core (hcore) (entry) : (shape.layout.outs.map (·.name)).Nodup
theorem outsNe_of_core   (hcore) (entry) : shape.layout.outs ≠ []
theorem outsOk_of_core   (hcore) (entry) (hpos : ∀ o ∈ shape.layout.outs, 0 < o.width) :
    ∀ o ∈ shape.layout.outs, 0 < o.width ∧ outNameOk o.name = true
```

The inversion step: `machineShape?_outsTest` is the walk of the BUILT
`machineShape?_prefix` (steps 1–3) plus step 4 with `ite_none_inv_not` in
place of `ite_none_inv`, so the condition is KEPT. It is joined with
`machineShape?_decomp` by `declOuts?` (same value, `Option.some.inj`), and
moved to the layout by `layoutOuts = machOutFields _ outs` (names copied).

### 2.2 Which per-declaration premise this discharges (READ: every `elab "#…"` under `Tools/`)

**None is decided separately today.** The three facts are exactly the
name half of conjunct 7 and conjunct 8 of `MachineData.ok`
(`Tools/ShippingMachineAuto.lean` 226–227):

    decide (∀ o ∈ d.shape.layout.outs, 0 < o.width ∧ outNameOk o.name = true) &&
    decide (d.shape.layout.outs.map (·.name)).Nodup && …

decided as ONE Bool by `f.machine_ok`; every consumer (`outsOk`, `outsNodup`
in `ShippingMachineEntry` 1048–1049, `ShippingMachineClose` 288–289,
`ShippingGenKidM` 148, `ShippingCallsPortsG` 170, …) reads them out of
`d.ok`. No generator decides `outNameOk`, the `Nodup`, or `outs ≠ []` alone.
So piece 2 removes no decide by itself: conjunct 8 and the name half of
conjunct 7 become redundant in `d.ok` (they hold for every reader result);
dropping them from `MachineData.ok` would change an existing definition
(not done). `outsNodup_of_core` / `outsOk_of_core` let a NEW lemma take the
run instead of `ok` for these two hypotheses; the width half (`0 < o.width`)
stays a premise — it is not derivable (`senv.fields` / a tuple of zero
widths can give width 0).

### 2.3 Output-name checks that ARE decided separately, and are NOT implied

| decided | where | why not from the wrapper |
|---|---|---|
| `noPortsMem_outChars`, `CombKid.outName` (`sanitizeName o.name = o.name` via every char `charOk`) | `#machine_no_ports_mem`, `…_seq`, `#machine_comb_design*`, kid commands | `outNameOk` does not constrain characters (`a'b` passes, `DesignTextTest` 102) |
| `noPortsMem_outHead`, `hfresh` (no output starts with `i`) | `#machine_no_ports_mem`, `ShippingCallsKidsSGen`, `ShippingChildIfaceGen`, `ShippingMachineClosesAtGen` | `outNameOk` only forbids a leading `_` |
| `CombKid.one` (names `= ["out"]`) | `#machine_comb_design*` | a property of the declaration's type |
| `machine_combPos` (`0 < o.width`) | `ShippingCombLeafClosedCommand` | NOT from the reader; but it IS conjunct 7 of `d.ok` (`f.machine_ok` is in scope there): a `d.ok` projection would replace that decide — noted, not done (outside this unit) |

## 3. Totalising `machNorm` and the 7-function mutual block (a COMPILER change: NOT done, awaiting a ruling)

### 3.1 What recursion there is (READ, `Sparkle/Compiler/Elab.lean` at this base)

* `machNorm` (4957–4986): recursive calls on `machNorm senv x/y` (`ashr` arm, args of `e`), on `rawNode`'s OUTPUT `e'` (`some e' => machNorm senv e'`), on `f`, `a`, `b`, `v` (structural), and on `b.instantiate1 v` (the `Nat` / closed-`BitVec` `let` arms). The `rawNode` arm and the `instantiate1` arms are not structural; `instantiate1` can duplicate `v`, so no size measure decreases. Its only caller is the wrapper (5077). It calls `machNormNode` → `machNormMap` → `machBoolMap` (row 8, `partial`), `machLiftScalarN` (row 7, `partial`); a `def machNorm` may keep calling those as opaque constants.
* The mutual block (3874–4233): `machConv`, `machNested`, `machInstance`, `machInstanceS`, `machChain`, `machLoopBody`, `machLoopRoot`. `machNested` re-reads `body` of a machine met before (`st.nested`, 4026–4029) and `machLoopRoot` re-reads a loop body (`st.loopWs`, 4207–4211): the argument comes from the STATE, not from a subterm. `machInstance*` read a callee's declaration. No structural measure; inner loops `foldlM` (4180), `findSome?` (4026, 4207), `mapM`.

### 3.2 The change (both pieces need fuel)

* `machNormF : Nat → StructEnv → Expr → Option Expr` (`none` at fuel 0), structural on the fuel; the wrapper does `let e ← machNormF FUEL senv e` (or keeps `Expr`, returning `e` unchanged at fuel 0 — weaker, NOT recommended: it would silently read a less-normalised body). `machNorm` kept as `partial` for the shadow only, or removed.
* The block: one extra `fuel : Nat` argument in all seven, every mutual call at `fuel - 1` / pattern `fuel+1`, `none` at 0; mutual structural recursion on `Nat` (supported in v4.32) or `termination_by fuel`. `machineShape?` passes one `FUEL`. At fuel exhaustion the reader returns `none` → the declaration falls back (legacy route), never a wrong shape.
* Unchanged: every other line of the text (the shadow requires it verbatim modulo fuel).

### 3.3 The equations that become available (generated by Lean, nothing hand-written)

`machNormF.eq_def` (+ `eq_1`, `eq_2` for fuel `0` / `n+1`); for each of the
seven, `eq_def` and the per-arm `eq_i` (machConv has ~20 arms: `.bvar`,
the `app` spines it recognises, `.letE`, `.mdata`, `.proj`, the default).
These are what `ShapeDecomp` lacks today: with them, the walk can go INTO
`machConv` / `machChain` / `machLoopRoot` instead of stopping at their
results (`names`, `kinds`, `inits` of the bundle).

### 3.4 The gate proofs (as for `projChain` / `prodMatcherArity?`)

1. **Source-equation agreement** (the analogue of `tail_unique` /
   `real_go_unique`): state `OldEqN g` (machNorm's source text as an
   equation on `g : Expr → Expr`) and `OldEqB g₁ … g₇` (the block's text as
   a system of 7 equations); prove `machNormF n e = some r → ∀ g, OldEqN g → g e = r`
   and the block analogue, by induction on `n`, plus monotonicity
   `F n x = some r → F (n+1) x = some r`. (Full uniqueness as for
   `prodMatcherArity?` is NOT available: on a diverging input the old
   equation has many solutions; agreement is on the inputs where the fuel
   suffices.) That the old compiled code satisfies its source equation stays
   the one step outside the kernel (not assumed).
2. **R5** (`MachRead.LenOk` of the returned state): mutual induction on fuel
   over the seven, each arm by `eq_i` and the 24 BUILT lemmas of
   `ShippingReaderLenOk` / `…Reserve`, plus three small loop lemmas
   (`foldlM` / `findSome?` / `mapM` preserve an invariant of the state they
   thread). Then `ShapeDecomp.r5_of_lengths`. NOTE (correction of round 1
   §2, which listed `machNorm` among R5's needs): R5 does NOT need
   `machNorm`'s equations — `machNorm` produces only the expression the
   block walks; LenOk preservation holds for every expression. `machNorm`
   equations are needed for facts about the BODY (what the reader read),
   not for R5.
3. The existing unfoldings of the wrapper (`machineShape?_decomp`,
   `_prefix`, `_outsTest`) must still build: with `machNormF` returning
   `Option`, the wrapper has one more bind before `machRoot`; `_prefix` and
   `_outsTest` stop before it (unaffected), `_decomp`'s step 6
   (`repeat … bind_inv …`) consumes it (PREDICTED unaffected; re-run).

### 3.5 The shadow tests (measurements, before and after the switch)

Pattern of `Tools/ShippingReaderMatcherArityOldShadow.lean`: keep the OLD
text VERBATIM as `…Old` (`partial`, `machNorm` + the 7 + nothing else
changed; helpers shared), detect the switch by an unchecked name, compare
on every input, THROW on a difference:

* **GRID**: every `machineShape?` call the test corpus makes (the 364
  machine-route corpus declarations + `Tests/Compiler` machine tests):
  `machineShape?Old` vs the compiler's — the whole `MachineShape`
  (binders, insts, instFields, layout, body) by `==`/repr, and
  `machNormOld e == machNormF FUEL e` on the wrapper's `e`.
* **SWEEP**: every `defnInfo` of the environment (~260k constants, as
  `PRODOLD SWEEP`): reader result old vs new, count `old returned`,
  `old!=new = 0`, and **`fuel exhausted = 0`** (any exhaustion is a
  behaviour change: old diverged or needed more fuel).
* **CORPUS**: `scripts/shipping-coverage` status diff (= 0) and the
  generated SV text against the PREVIOUS compiler (`compare_outputs.py`;
  shared arms change legacy output too), plus compile time
  (`Fp12MulHWTest` ≈ 23 s baseline).

## 4. Predicted axioms

* `machineClosesAt_of_memOnlyDataR_names`, `outNames_of_reader`, `outNames_of_core`, `outsNodup_of_core`, `outsNe_of_core`, `outsOk_of_core`, `machineShape?_outsTest`: `[propext, Classical.choice, Quot.sound]` (via `machineShape?_decomp`, `machineClosesAt_memOnly_names`).
* `ite_none_inv_not`, `bool_false_of_not_true`, `machOutFields_*`, `outsTest_facts`: none or `[propext]`.
* Generated `f.noPortsMem_*` (new path): standard; no `native_decide` anywhere.

## 5. Risks (PREDICTED)

1. `machineShape?_outsTest`, step 4: `ite_none_inv_not h` must unify with the same continuation `ite_none_inv h` does in the BUILT decomp (same walk). The condition's form is then whatever `whnf` gave (`o.2` or a projection); `bool_false_of_not_true hc` checks it against `outsTest o.2 = true` up to delta of `outsTest` — the wrapper text and `outsTest` are the same source text.
2. `outsTest_facts`: `rw [ha, hb, hc] at h` needs the three `cases` terms to match `h` syntactically after `unfold outsTest` (same text, same instances). If `rw` fails, `simp only [ha, hb, hc] at h` is the next thing to try.
3. `machOutFields_names` cons: three fallbacks (`congrArg` by defeq, `simp only`, `simp`).
4. The generator's `dataR` literal: `MemOnlyDataR.mk` positional order (ok body calls slots domB ins sl fne mem cw args outNames), READ from `ShippingReaderOutsMemOnly` 38–53.
5. `MemParentFreeTest` / `genKidM` fall back to `decide` for fields absent from `dataR` (slower, same statement); NoPortsMemKidTest depends on the kid command change.
6. `NoPortsMemGenCompareTest`: `memCounter_data`'s stated type must be literally `MemOnlyData … ` on 4 arguments (`isAppOfArity` after `instantiateMVars`); else the check throws with the type printed.

## Integration (integrator, 2026-10-15) — BUILT as written
Applied on poc ab3d3d5a (lakefile conflict on appended lean_libs: kept both; second commit as a diff).
Run `r2` (cgrun, 3 GiB, swap 0, `-j 1`): all twelve targets in the worker's order exit 0
(ReaderMemOnlyCloses, NoPortsMemCommand, NoPortsMemKidCommand, NoPortsMemGenCompareTest, NoPortsMemKidTest,
MemDepthProbeTest, MemParentFreeTest, MemParentClosesTest, NoPortsMemGenFamilyTest, NoPortsMemGenOldDataTest,
NoPortsMemGenOldNamesTest, ReaderOutNames); no `sorryAx`.
Old-vs-new generator comparison (MEASURED, kernel isDefEq of types on one tree):
`NOPORTS MEM OLDDATA COMPARE: 100 pairs over 5 declarations, all isDefEq; per declaration the new path decides
2 output facts fewer (outTy, outScalar).`
Suite run `r2-suite`: `Tests.AllTests` + `DesignCoverageTest` exit 0, census 134 declarations / 133 covered
(unchanged; suite population only), peak 0.74 GB.
Axioms: `machineClosesAt_of_memOnlyDataR_names`, `outNames_of_reader`, `outNames_of_core`
[propext, Classical.choice, Quot.sound].
