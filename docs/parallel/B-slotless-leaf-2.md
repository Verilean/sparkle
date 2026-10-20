# B — slotless leaves at the design level, closed: (S1) and (S2) as theorems about every run (round par/b-33)

Branch `par/b-33` from `poc/roundtrip-proof` 4103e86f. Worker B.

**NOTHING HERE IS BUILT OR RUN.** No `lean`, `lake` or simulator was started.
Every Lean file is WRITTEN, NOT BUILT; no endpoint exists until the
integrator builds it. No existing file was changed; no compiler file was
touched (no guard was added).

Marks: **[R]** read at 4103e86f; **[B]** built per the integration records;
**[M]** measured by the integrator's build of 4103e86f; **[P]** PREDICTED.

## 0. Files

| file | content |
|---|---|
| `Tools/ShippingCastMerge.lean` | `cast_rename`; `mergeDuplicates_hasCast` (a cast statement survives the validated merge) |
| `Tools/ShippingCombLeafShape.lean` | `transition_simple_of_run`, `closeLets_simple`, `closeMachine_slotless_shape`, `comb_entry_shape`, `comb_entry_design0_of_ships` |
| `Tools/ShippingCombLeafClosedCommand.lean` | `#machine_comb_design0 f`, `#comb_closed_sweep f`, `#comb_closed_sweep_summary` |
| `Tests/Compiler/CombClosedSweep{Raw,ApplicativeA,ApplicativeB,Comb,SignOps}Test.lean` | the 32, target-only |
| this file | |

## 1. Is the entry's module pinned to a concrete term? NO

The question of the round: under the run and `MachineDefines f`, is the
returned module `b` EQUAL to a term computed from `f.machineData`?

**[R] No.** `Tools/ShippingChildRun.lean` 528–540
(`synthesizeMachineCertified_runs`): for a machine without calls

    ∃ t t' d₀, MReturns (synthesizeMixedCertified … declName shape.binders shape.body) (t, d₀) ∧
      closeLets shape.layout.lets t = some t' ∧
      (shape.insts = [] ∧ m = closeMachine shape.layout t' ∧ d = d₀) ∨ …

`closeLets` and `closeMachine` are functions; `t`, the TRANSITION, is an
existential witness of a run of the mixed compiler. What the built theorems
say about `t` are properties, not an equation:

* `Tools/ShippingClosedTransitionTyped.lean` 73–84: `t'.body = B ++ [out := core]`
  for SOME `B`, `TypedStmts`, every target of `B` and every wire an
  `Allocated` name, distinct, the slot ports at the slots' widths;
* `Tools/ShippingMachineEntry.lean` 642–661 (`machPorts`, `MachineWired`):
  the port names are `machPorts declName ids cache binders` for an
  existential `ids : List FVarId` and `cache : IO.Ref (ExprStructMap String)`.

So `b` is known only up to (i) WHICH statements the mixed compiler emitted
(an existential list `B`) and (ii) the allocated wire names (they come from
the fresh-name state of the run). There is no closed term to evaluate:
(S1) / (S2) cannot be discharged by `decide` / `rfl` per declaration, and
nothing in this round does.

## 2. But (S1) and (S2) are invariant, and provable once

Among the properties of `t` there IS one about statement SHAPES, which the
exports dropped: **[R]** `Tools/ShippingMixedEntrySoundness.lean` 536–541,
`RawValueAt … m` = `∃ result, … ∧ TypedPostReady m ∧ SimpleStmts m.body ∧ …
∧ (PositiveBinders bs → PrintBaseAt outWidth m)`. **[R]**
`Tools/ShippingTransitionTyped.lean` 94–101 obtains that record for the
transition (`transition_facts … ; raw _ _ _ (fun _ _ => 0) zero`) and keeps
only its 4th and 9th components. The 5th is `SimpleStmts t.body`.

The chain, each step general (no declaration, no evaluation):

| step | fact | by |
|---|---|---|
| the transition `t` | `SimpleStmts t.body` | `transition_simple_of_run` — the built proof of `transition_typed_of_run`, lines 67–100, copied by script, reading the 5th component |
| `closeLets` | `SimpleStmts t'.body` | `closeLets_simple`: `closeLets_eq'` [B] gives `t'.body = frontAliases ++ insertAliases ++ [out := core]`; an alias is `p := a[w-1:0]` (`aliasStmt`, `Sparkle/IR/Machine.lean` 155), a part-select with `lo = 0`: `simpleRhs` is `decide (0 ≤ hi)`; `mem_frontAliases` / `mem_insertAliases` [B] |
| `closeMachine`, no slot | `SimpleStmts M.body ∧ HasCast M.body` | `closeMachine_slotless_shape`: `closeMachine_slotless_body` [B] gives `B ++ outAssigns w outs`; an output assignment is `o := w[lo+width-1:lo]` (`fieldRhs`, `Machine.lean` 71–76): simple iff `lo ≤ lo+width-1`, true when `0 < width`; and `isCastExpr (.slice …) = true` |
| zero-width cleanup | the body is kept | the wired facts (`hclean`), as `leaf_run_typedIn_bnd` reads them |
| checked merge | `SimpleStmts`, `HasCast` kept | an assignment-only body: `mergeChecked = mergeDuplicates` (`mergeChecked_assign` [B]); `mergeDuplicates_simple` [B]; `mergeDuplicates_hasCast` (NEW: the built proof of `mergeDuplicates_hasControl`, `Tools/ShippingControlOptSoundness.lean` 107–199, with `isCastExpr`, by script; `cast_rename` new) |
| the outputs | `b.outputs.map name = layout.outs.map name` | `closeMachine_outputs` [B], the cleanup and the merge keep the ports |

Result, `comb_entry_shape` — for EVERY run of the full entry from a world
with `ChildBnd`:

    SimpleStmts b.body ∧ HasCast b.body ∧ b.outputs.map (·.name) = d.shape.layout.outs.map (·.name)

Then **(S1)** `simpleBody b = true` is `simpleBody_of` [B], and **(S2)** is
its first disjunct: `checkedOptimize b = b` by
`Tools.ShippingControlOptSoundness.checkedOptimize_cast` [B] (a simple body
with a cast: `normBody` is `none`, so `optCheck` fails and the optimizer
keeps its input). No compiler guard, no `printOk` of an optimized module is
needed: the optimizer provably does nothing to these modules.

This agrees with **[M]**: on one run each, for all 32, `simpleBody b`,
`checkedOptimize b == b`, `printOk (checkedOptimize b)` were all `true`.

`comb_entry_shape`'s proof begins with the built proof of
`Tools.ShippingLeafEntryBnd.leaf_run_typedIn_bnd`, lines 89–146 (the run's
analysis down to the wired facts), copied by script unchanged, with two
statements inserted before `ok` is destructured.

## 3. The closed statement

```lean
theorem comb_entry_design0_of_ships
    (hships : ∃ raw, (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) ∧
      ∀ wof, simpleBody b = true → seqCheck wof (weOf wof) (checkedOptimize b).body = true →
        ((seqNames (checkedOptimize b).body).all fun n => declWidth (checkedOptimize b) n == weOf wof n) = true →
        MachineShipsComb declName d (dropZeroWidthModule raw) (checkedOptimize b) wof dom src)
    (K : CombKid c dk) (hpos : ∀ o ∈ dk.shape.layout.outs, 0 < o.width)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c dk.shape)
    (closes : MachineCloses mctx mref cctx cref c dk.shape) :
    ∃ raw, (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) ∧
      (ChildBnd mref cref w →
        ∃ ids, ids.Nodup ∧ ids.length = d.shape.binders.length ∧ ∃ cache,
          ∀ i bools bits T ins st0 mems (kids : String → KT 0),
            (SourceInputs … (seedR b ins t st)) →
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS (checkedOptimize b) x) →
            Bounded (weS (checkedOptimize b)) st0 →
            (∃ envsO, DesignSV (childMap design.modules) 0 (checkedOptimize b) (seedR b ins) T ⟨st0, mems, kids⟩ envsO ∧
               envsO.length = T ∧ (the source on the outputs))
            ∧ ∀ envs', DesignSV … envs' → envs'.length = T ∧ (the source on the outputs))
```

`hships` is `f.machine_ships_comb hr entry closes`. Its three check
antecedents are discharged inside: `simpleBody b` and `checkedOptimize b = b`
by `comb_entry_shape`; the text of `b` itself by `comb_entry_text_out` [B]
(one output `out`); the text of the shipped module by
`text_shipped_of_print` [B]; `DesignSV` and uniqueness by
`comb_design_of_ships` [B].

Premises of the generated `f.machine_design_comb0` **[P]**: binders the run
and `MachineDefines f`; under `∃ raw` ONE antecedent, `ChildBnd`. Nothing
else. Against the OPEN `f.machine_design_comb0_open` [B]: (S1) and (S2) gone.
Against `f.machine_ships_comb`: all three check antecedents gone, `ChildBnd`
added (allowed), conclusion `DesignSV` with "every closed run shows the
source". `_open` is kept as it is.

Data conditions per declaration (decided; conditions, not reductions): the
eleven fields of `f.machine_combKid` [B for 26] and the new
`f.machine_combPos : ∀ o ∈ outs, 0 < o.width`.

### What the kernel evaluates

NOT the module — it is not a term (§1). Per declaration only `decide`s on
`f.machineData`'s shape and layout (the same as for the open endpoint, plus
one comparison `0 < width` on the one output field). For the IP
declarations (`ipv4HeaderByte`, `ipv4HeaderChecksumSig`, `httpGetByte`,
`requantize`) that is what `f.machine_combKid` already did [M: GENERATED in
2–4 s per file for the first three]. No `native_decide`. The fallback asked
for ("a structural lemma for `simpleBody` over the statement list") is what
this round IS: `SimpleStmts` is carried structurally through the pipeline,
and nothing is decided on a statement list.

## 4. The six transported endpoints (`ShippingSignOpsTest`, `requantize`)

**[R]** `Tools/ShippingMachineCommand.lean` 2557–2589: when the declaration's
value was rewritten before the reader (sign normalisation here), the
endpoint is proved about the rewritten value's source `srcName` and then
transported: `p ← mkEqMPR hT p` with `hT = congrArg (fun s => T[s]) heq`,
`heq : f.machineSourceDecl = srcName`; `retarget` does the same to
`machine_ships_comb` (2582–2589, 2661). So `f.machine_ships_comb`'s VALUE is
`Eq.mpr …`, not an application of `machine_ships_comb` — which is what the
open generator's `endpointTerm` reads (it needs the wired trace `soundL`
from argument 7) and why it refused the six.

The closed generator does not open the value. Its bridge
(`comb_entry_design0_of_ships`) takes the ship-level endpoint's CONCLUSION as
a hypothesis — the route of the register leaves' generator
(`Tools.ShippingLeafDesignCommand.endpointTerm` [B], which GENERATED the
transported `outer` / `siblings` [M]) — and gets the output names from the
run's analysis instead of from `soundL`. So the six need no special case and
no new function was added to the open generator. **[P]** they are GENERATED
by the closed generator; their open endpoints stay refused (unchanged
behaviour for the 26 and for the 6).

Evidence that nothing else blocks the six **[M, by the order of
`combDesignCore`]**: the open generator's refusal for them came from
`endpointTerm`, which runs AFTER the scan (machine route, no call, no slot,
`machine_ships_comb` exists, output names `["out"]`), after `closesTheorem?`
and after `combKidTheorem` — so all of those succeeded for the six.

## 5. PREDICTED outcome per group

| group | declarations | `#comb_closed_sweep` class [P] |
|---|---|---|
| Raw (9) | `negSig` … `tupHwLet3` | GENERATED |
| ApplicativeA (7), ApplicativeB (6) | `reversed` … `permutedFour` | GENERATED |
| Comb (4) | `pickByte`, `ipv4HeaderByte`, `ipv4HeaderChecksumSig`, `httpGetByte` | GENERATED |
| SignOps (6) | `sext`, `ashrK`, `shiftSurface`, `ashrSig`, `scaleMul`, `requantize` | GENERATED (transported: §4) |

PREDICTED: 32 GENERATED, each with 3 premise lines (binder `hr`, binder
`entry`, antecedent `ChildBnd`), 0 NOT ALLOWED, gap hypotheses `[]`. The
premise count is asserted by the generator's own statement check (the
register leaves' `checkStatementWith`), not written in a sweep file. If the
general theorems do not build, ALL 32 fail the same way (FAILED lines) —
there is no per-declaration proof to fail separately except the two data
theorems.

## 6. For the integrator

`lakefile.lean` (not edited):

```lean
lean_lib «Tools.ShippingCastMerge» where
  roots := #[`Tools.ShippingCastMerge]

lean_lib «Tools.ShippingCombLeafShape» where
  roots := #[`Tools.ShippingCombLeafShape]

lean_lib «Tools.ShippingCombLeafClosedCommand» where
  roots := #[`Tools.ShippingCombLeafClosedCommand]
```

`Tests/AllTests.lean`: nothing in this round (the five files are
target-only). After a clean run they could be rewritten with asserted
classes, as the register sweeps were.

Build order:

1. `Tools.ShippingCastMerge` (imports the built
   `Tools.ShippingControlOptSoundness` only) — small, independent.
2. `Tools.ShippingCombLeafShape` — the unit's weight.
3. `Tools.ShippingCombLeafClosedCommand`.
4. `Tests.Compiler.CombClosedSweepRawTest` first, then `ApplicativeA`,
   `ApplicativeB`, `Comb`, and `SignOps` last (the transported ones).

Log:

    grep -E "COMBCLOSED (START|RESULT|ROW|SUMMARY)|COMBDESIGN0 (GENERATED|REBUILT|REFUSED|FAILED)"

* `COMBDESIGN0 PREMISE f.machine_design_comb0: ALLOWED …` — the premise
  listing (the classifier is `Tools.ShippingFinalGoalCommand.allowed`);
* `COMBCLOSED RESULT f: GENERATED; premise lines listed N, NOT ALLOWED 0;
  audit OK; gap hypotheses []; …; <ms> ms`;
* `COMBDESIGN0 FAILED f: …` with the first two errors of the generated proof
  — a finding;
* a `START` without a `RESULT`: that declaration hung or was killed.

What may be recorded after a green build, per declaration: "
`f.machine_design_comb0` exists: premises the run, `MachineDefines f`,
`ChildBnd`; 0 NOT ALLOWED; standard axioms" — and, against the open
endpoint, "(S1) and (S2) are no longer premises: they are theorems about
every run (`comb_entry_shape`)".

### The scope sentence each GENERATED line carries (binding)

"`f.machine_design_comb0` for ONE declaration `f` as an entry, depth 0, no
call, no register, one output `out`: data conditions decided for `f`
(conditions, not reductions); the run, the reflection `MachineDefines f` and
the runtime boundary `ChildBnd` stay premises; the conclusion is `DesignSV`
of the module list over the returned design's child map — not the SV string,
not `#sim`; seeded by `seedR` (`rst` low)." Not: several outputs, a slotless
leaf as a CHILD, any other declaration, all successful inputs.

## 7. Risks (unbuilt), in order

1. `comb_entry_shape` (`ShippingCombLeafShape.lean`): 58 copied lines of a
   built proof under that proof's `open`s, then my tail — `rw [hzb, hMeq]`
   (the orientation of the two equations as the built proof leaves them),
   `closeLets_simple hBt pbT.order hcl hsimpT`, the names the copied prefix
   binds (`t`, `t'`, `hcl`, `hbodyc`, `coreW`, `hzb`, `hzo`, `hMeq`, `hpost`,
   `M`). A hypothesis of mine was renamed (`houtsNe`) because the prefix
   binds `hne`; I looked for other clashes and found none.
2. `transition_simple_of_run`: the 34 copied lines end in `have zero …`; the
   anonymous pattern for `RawValueAt` has nine components (the built proof
   uses the same count).
3. `mergeDuplicates_hasCast`: a substitution of identifiers in 93 built
   lines; `cast_rename` (new) by cases on the argument list of an operator —
   `renameE` on `.op o [a]` must reduce to `.op o [renameE σ a]` by `rfl`
   (the built `control_rename` relies on the same for the head).
4. `closeLets_simple`: `intro st hst` on a goal `SimpleStmts …` (unfolding
   the definition); `have hst' : st ∈ frontAliases … ++ insertAliases … ++
   [..] := hst` (unfolding `closedBody` and a structure projection);
   left-associated `++`.
5. `outAssign_facts` / `aliasStmt_simple`: `simpleRhs (.slice (.ref _) hi lo)`
   reducing to `decide (lo ≤ hi)` for `exact decide_eq_true …` (a `simp`
   fallback is written).
6. `comb_entry_design0_of_ships`: `c2' := c2`, `c3' := c3` (as in the built
   open theorem); the first `rfl`-free use of `K.one` to get `outs ≠ []`.
7. the generator: `mkAppM` with the ship-level endpoint applied to its own
   binders as the first explicit argument — for a transported declaration
   its type is a β-redex at the head (the built leaf generator has the same
   situation with `machine_ships_wired`); `checkStatementWith` on the
   resulting type.
8. `f.machine_combPos` by `decide`.

## 8. What I could not determine by reading

* Whether the value of `f.machine_ships_comb` for the six really is
  `Eq.mpr …` (the open generator's message says "or another construction";
  §4 is the reading of the generator, and the closed generator does not
  depend on it).
* Whether the β-redex type of a transported `machine_ships_comb` unifies
  with the bridge's hypothesis as it does for `machine_ships_wired`
  (predicted yes, by the register leaves' measured results on `outer` /
  `siblings` — if those are transported, which I inferred from "fused" in
  the generator's comments, not from a log).
* Whether `intro` unfolds `SimpleStmts` (risk 4) and whether the copied
  prefixes elaborate under my file's `open`s exactly as in their files.
* Kernel time of `comb_entry_shape` (its model, `leaf_run_typedIn_bnd`,
  needs `maxHeartbeats 4000000`; I set the same).

## Integrator's build record (2026-10-13) — MEASURED

BUILT on tree `c85bd75ca83917af0a6445859009e7773295dc1a` (poc 3227149c + these files), cgrun 3 GiB swap 0, worker's files unchanged, FIRST
ATTEMPT. `b33`: `Tools.ShippingCastMerge`, `Tools.ShippingCombLeafShape`,
`Tools.ShippingCombLeafClosedCommand`, then the five `CombClosedSweep…` files one at a time (exit 0 each,
peak 0.81 GB; logs in `~/sparkle-work/comb-closed/`). `b33-all`: `Tests.AllTests` with the five sweep
files imported, 1318 jobs, exit 0, peak 0.44 GB; then, printed by the integrator independently of the
generator's audit: `#print axioms` of `sext`, `negSig`, `requantize` `.machine_design_comb0` —
`[propext, Classical.choice, Quot.sound]` — and the full statement of `negSig.machine_design_comb0`
(binders the run and `MachineDefines negSig`; `ChildBnd` under the existential; no other antecedent
before the trace hypotheses of the `DesignSV` conclusion).

Result over the 32 slotless leaves: GENERATED 32 (`f.machine_design_comb0`), REFUSED 0, FAILED 0 — the six
transported ones (sign operations, `requantize`) included. Each: 3 premise lines (`hr`, `entry`,
`ChildBnd`), 0 NOT ALLOWED, audit OK, gap hypotheses `[]`, 110–210 ms.

Endpoint — premise — state: for each of the 32, the antecedents (S1) `simpleBody b` and (S2)
`checkedOptimize b = b ∨ printOk …` of `f.machine_design_comb0_open` (and the three check antecedents of
`f.machine_ships_comb`) are ABSENT from `f.machine_design_comb0`; they are derived from the run by
`comb_entry_shape` (general, proved once), not decided per module.
SCOPE of each: one declaration as an entry, depth 0, no call, no register, one output `out`; data
conditions decided per declaration; the run, `MachineDefines f`, `ChildBnd` are premises; `DesignSV` of
the module list — not the SV string, not `#sim`; seeding `seedR` (`rst` low).

GENERATED (32):
```
Sparkle.IP.Net.HTTP.httpGetByte
Sparkle.IP.Net.IPv4.ipv4HeaderByte
Sparkle.IP.Net.IPv4.ipv4HeaderChecksumSig
Sparkle.IP.YOLOv8.Primitives.Requantize.requantize
Sparkle.Tests.Compiler.ApplicativeSemanticsTest.complement
Sparkle.Tests.Compiler.ApplicativeSemanticsTest.concatReverse
Sparkle.Tests.Compiler.ApplicativeSemanticsTest.constantLeft
Sparkle.Tests.Compiler.ApplicativeSemanticsTest.constantRight
Sparkle.Tests.Compiler.ApplicativeSemanticsTest.duplicate
Sparkle.Tests.Compiler.ApplicativeSemanticsTest.nested
Sparkle.Tests.Compiler.ApplicativeSemanticsTest.nestedSurface
Sparkle.Tests.Compiler.ApplicativeSemanticsTest.orderedLess
Sparkle.Tests.Compiler.ApplicativeSemanticsTest.permutedFour
Sparkle.Tests.Compiler.ApplicativeSemanticsTest.reversed
Sparkle.Tests.Compiler.ApplicativeSemanticsTest.reversedSurface
Sparkle.Tests.Compiler.ApplicativeSemanticsTest.rightAssociated
Sparkle.Tests.Compiler.ApplicativeSemanticsTest.withConstant
Sparkle.Tests.Compiler.ShippingMachineCombTest.pickByte
Sparkle.Tests.Compiler.ShippingMachineRawTest.addThree
Sparkle.Tests.Compiler.ShippingMachineRawTest.negLift
Sparkle.Tests.Compiler.ShippingMachineRawTest.negSig
Sparkle.Tests.Compiler.ShippingMachineRawTest.triBundle
Sparkle.Tests.Compiler.ShippingMachineRawTest.tupFst
Sparkle.Tests.Compiler.ShippingMachineRawTest.tupHwLet3
Sparkle.Tests.Compiler.ShippingMachineRawTest.tupMapFst
Sparkle.Tests.Compiler.ShippingMachineRawTest.tupSum
Sparkle.Tests.Compiler.ShippingMachineRawTest.useHalf
Sparkle.Tests.Compiler.ShippingSignOpsTest.ashrK
Sparkle.Tests.Compiler.ShippingSignOpsTest.ashrSig
Sparkle.Tests.Compiler.ShippingSignOpsTest.scaleMul
Sparkle.Tests.Compiler.ShippingSignOpsTest.sext
Sparkle.Tests.Compiler.ShippingSignOpsTest.shiftSurface
```
The five sweep files are in AllTests but assert consistency only, not yet the class per declaration.
