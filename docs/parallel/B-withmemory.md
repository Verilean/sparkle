# `withMemory`: the memory-only chain on a TRANSPORTED endpoint (round par/b-17)

Status of everything below: **WRITTEN, NOT BUILT**. Nothing was run (no `lean`, `lake`, probe). Every
statement about `withMemory`'s reader data is a PREDICTION by reading; the test's first command logs the
real data and throws where a prediction that a hypothesis depends on is wrong.

Files (new, branch `par/b-17` from d0de8898):

- `Tools/ShippingMemTransport.lean` — one lemma, `composedG_src`.
- `Tests/Compiler/NoPortsMemWithMemoryLib.lean` — `logData`, `generateT0`, `auditOpen`, `auditClosed`.
- `Tests/Compiler/NoPortsMemWithMemoryTest.lean` — the data theorems, the open and closed endpoints, gap, audits.

## 1. READ

| what | where |
|---|---|
| `withMemory`: a `Signal.loop` over `BitVec 4 × BitVec 8`, two `memoryComboRead` (one dead), `innerCnt` inlined (its own `Signal.loop`, no `@[hardware_module]`) | `Tests/Compiler/ShippingMachineFuseTest.lean` 17–20, 42–51 |
| its endpoint is made by `ShippingMachineCommand.generate … (checkCloses := false)` | same file 57–60 |
| fusion: `loops.length > 1 && runs.isEmpty` → `fuseInst`; `srcN := inst'`, `instEq? := base = inst'` | `Tools/ShippingMachineCommand.lean` 2501–2516 |
| the head after fusion: `loopProof`, `machine_trace_of_loop_causal` when there are calls | same file 2524–2525, 2149–2151 |
| the transport: `f.machineSourceDecl` (observations of the declaration applied), `heq : f.machineSourceDecl = f.machineSource` (`funext` of `congrArg` of the fusion equation), `p ← Eq.mpr (congrArg motive heq) p` | same file 2554–2576 |
| `machine_composedT` of a memory-only parent: `machine_linkedT_mem` on the wired twin applied to the UNTRANSPORTED arguments, 10 further arguments, then the same `Eq.mpr` | `Tools/ShippingMachineMemCommand.lean` 59–98 |
| `endpointParts`: strips the `Eq.mpr`, returns (wired head, untransported arguments, `some (heq, rewritten source)`) | `Tools/ShippingMachineSeqCommand.lean` 71–91 |
| `machine_ships_hier` for a transported parent: wired twin of the untransported head for the cleanup facts, the composed theorem already transported | `Tools/ShippingMachineShipsHierCommand.lean` 50–54, 68–75, 126–128 |
| both heads have SEPARATE sources: `src` (composed theorem, conclusion) and `srcL` (wired endpoint, cleanup only) | `Tools/ShippingMachineShipsHier.lean` 342–366; `Tools/ShippingNoPorts.lean` 52–76 |
| the refusal | `Tests/Compiler/NoPortsMemOnlyCounterTest.lean` 275–276 |
| what the at-form branch expects of `machine_composedT`: `lambdaTelescope ct.value` with 11 binders over `machine_linkedT_mem` on 21 arguments | same file 288–299 |
| `withMemory.machine_composedT` is made in two modules (same generator) | `ShippingMachineMemLinkedTest` 56, `ShippingMachineSeqLoopTest` 43 |
| `withMemory.machine_ships_hier` | `ShippingMachineSeqLoopTest` 44 |

## 2. What "transported" means

An equation between two SOURCE-OBSERVATION functions,

    heq : withMemory.machineSourceDecl = withMemory.machineSource

the left one the observations of `withMemory we wd` as declared, the right one of the fused single loop the
endpoint is proved for. It is not a renaming, not a `quantModule`, not another head: the head is the same
`machine_trace_of_loop_causal` as `memCounter`'s, and `machine_composedT` the same `machine_linkedT_mem`.
The source being rewritten occurs in exactly one place of the composed statement (the `src` argument of
`ComposedG`), and nowhere in the reader's data, the run, the reflection, the closing or the wired endpoint.

## 3. Shapes against `memCounter`

| | `memCounter` | `withMemory` |
|---|---|---|
| `machine_sound` value | `machine_trace_of_loop_causal …` | `Eq.mpr _ _ (congrArg _ heq) (machine_trace_of_loop_causal …)` |
| `machine_composedT` value | `fun [11] => machine_linkedT_mem [21 args]` | `Eq.mpr _ _ (congrArg _ heq) (fun [11] => machine_linkedT_mem [21 args])` — 0 leading binders |
| `machine_ships_hier` value | `machine_ships_hier` on 24 args, `src = srcL` | the same head and count, `src = machineSourceDecl`, `srcL = machineSource` |
| type binders of `machine_ships_hier` | 11 (8 contexts, run, `MachineDefines`, `MachineCloses`) | the same (INFERRED) |
| design-level base | `machine_design_sv0` | NONE |

Why `generateM0` refuses (275–276 is the explicit throw; without it the next failures would be): (a)
`lambdaTelescope ct.value` finds 0 binders, not 11 (291–292); (b) the composed theorem it would assemble
from the `RA` twin concludes about `machineSource`, while position 14 of `machine_ships_hier`'s arguments —
passed to the head as `src` by `finishM0` (166–170) — is `machineSourceDecl`: the head's application would
not type-check.

## 4. The memory-only chain on `withMemory`

Applies AS IS — no hypothesis of `MemOnlyData`, `memOnly_*`, `machineClosesAt_memOnly` mentions a source.
Per hypothesis: the table in `Tests/Compiler/NoPortsMemWithMemoryTest.lean` (header). Summary:

- BUILT constants: `ok` (`withMemory.machine_ok`), `body` (`withMemory.machine_body`), `mem_isMem` (4 / 8, combo).
- DECIDED in the test, predicted true, NOT MEASURED: `callsOk 2`, `slots`, `domB`, `outTy`, `outNames`,
  `outScalar`, `callWidthsOk`, `callArgsOk`, `ins / sl / fne ≠ []`, `letsAliasOk`, `hargsN`, `hfield`,
  `hargsNd`, `hout`, the name separation (`withMemory_notin`).
- By lemma: `hsep` (`sep_of_one`), `hparent` (`parent_of_one`).
- The one prediction with a real alternative: `hargsNd`. The two entries have one callee and one field;
  they differ only if the read addresses (`addr`, `0#4`) are two different `let`s. `twoMems` (MEASURED
  `[[1,2,3,0],[0,2,3,4]]`) has the same pattern for its second read, which is why it is predicted true.
  If false, the first command throws "hargsNd is FALSE: STOP" and the missing statement is the one
  recorded in `verification-a19.md` (one memory read twice on the same four lets).
- PREDICTED data: nDecl=2, slots=3, loops=2, entries 2 × `SparkleMem.combo.4.8`, instFields `[out, out]`,
  lets=4, binders=11. A parent with THREE slots and TWO loops has not gone through `kidsM_*` before (the
  five built parents have slots=2, loops=1); the theorems are general in both.

## 5. What the at-form needs for a transported endpoint

1. The wired endpoint: the `RA` twin on the untransported arguments, unchanged — it serves the head's
   `srcL`, which may be the rewritten source.
2. The composed theorem: read the 10 data arguments under the `Eq.mpr`; assemble
   `composedG_of_Tmem (machine_linkedT_mem (toLB (RA twin)) …) hm` (about `machineSource`); move it to
   `machineSourceDecl` with

       theorem Tools.ShippingMemTransport.composedG_src
           (H : ComposedG KS Reset declName d kD m dsn dom src ext extB) (heq : src' = src) :
           ComposedG KS Reset declName d kD m dsn dom src' ext extB

   at the endpoint's own `heq`. (The built generators do this step by `kabstract` on the whole statement;
   the lemma states it once and needs no abstraction.)

`generateT0` does this; with no transport it skips step 2's last part.

## 6. New statements

`withMemory.machine_design_noPortsR0` — binders: the contexts, `hr : RunsTo (synthesizeCombinational
``withMemory) … (b, design) w'`, `entry : MachineDefines … ``withMemory withMemory.machineData.shape`,
`closes : MachineClosesAt … ``withMemory withMemory.machineData.shape`; conclusion the head's
(`Tools/ShippingNoPorts.lean` 121–162) at `n = 0`, `Reset = ResetM`, `Bnd = ChildBnd mref cref w`,
`src = withMemory.machineSourceDecl`.

`withMemory.machine_design_noPortsR0_closed` — the same without `closes`
(`withMemory_closes`, no premise). `…_closed_gap` by `#machine_goal_gap_of`.

Relative to: `withMemory` has no design-level base. Against `withMemory.machine_ships_hier`:

| | `machine_ships_hier` | new (closed) |
|---|---|---|
| conclusion | `runModuleTG flatKS …` of the shipped IR module shows the source | `DesignSV … 0 (checkedOptimize b) …`: a closed run exists and every closed run shows the source; three more use conditions (emitted widths of inputs / start registers, instance invariants) |
| `shipsHierCheck (childMap D.modules) b` | antecedent | absent |
| `kidsMem (childMap D.modules) b.body` | antecedent | absent |
| boundary | `True` | `ChildBnd mref cref w` (ADDED) |
| closing | binder `MachineCloses withMemory` (all worlds; undischargeable) | none (open form: `MachineClosesAt withMemory`) |
| run, `MachineDefines withMemory` | binders | binders |
| source | `withMemory.machineSourceDecl` | the same |

## 7. For the integrator

- `lakefile.lean`: `lean_lib «Tools.ShippingMemTransport» where` / `  roots := #[`Tools.ShippingMemTransport]`.
- `Tests/AllTests.lean`: `import Tests.Compiler.NoPortsMemWithMemoryTest`.
- Build order: `Tools.ShippingMemTransport` → `Tests.Compiler.NoPortsMemWithMemoryLib` →
  `Tests.Compiler.NoPortsMemWithMemoryTest`.
- Name clashes: none found for `withMemory.machine_design_noPortsR0[_closed[_gap]]` (grep). The test
  imports `ShippingMachineSeqLoopTest` (for `withMemory.machine_ships_hier`) together with the
  `ShippingMachineMemLinkedTest` chain; both define the theorem `withMemory.machine_composedT` — the same
  pair of imports as the built `HierBindsCensusTest` 2–3.

## 8. Risks, most likely first

1. A reader-data prediction is wrong (`hargsNd`, `callArgsOk`, `letsAliasOk`, `callsOk 2`): a `decide`
   fails or the first command throws. The log line `WITHMEMORY DATA` says which.
2. `decide` on a 3-slot, 2-loop `machineData` exceeding the elaborator's limits (the five built parents
   are smaller); the pattern `first | decide | decide +kernel` is the built one.
3. `mkAppM composedG_src #[cg0, heq]`: `heq`'s type against the source type fixed by `cg0` (a
   definitional-equality check of two function types).
4. `auditOpen` assertions about `machine_ships_hier` (that it prints an antecedent `True`, that it does
   not mention `machineSource`): by reading only.
5. Syntax of the lib's `match` inside `do` (two places).

## 9. Not covered

Depth ≥ 1; a generator command; `#machine_design_sv0 withMemory` (never run; not needed here); other
transported parents (whether another memory parent with a transported endpoint exists was NOT searched);
transported parents on the sequential route (`generateCoreSR` already transports its composed theorem,
`ShippingMachineSeqCommandR` 299–304; the depth generators refuse, `ShippingMachineDepthCommand` 364, 397).

## Build record (integrator, 2026-10-13)

Built at the first attempt on poc d0de8898 + this round's files (worker files unchanged; test in AllTests).
`withMemory` (fused: an inlined loop counter and two combo memories, one dead; the "transport" is the
equation `machineSourceDecl = machineSource`): `withMemory.machine_design_noPortsR0` has no checker
constant and exactly one NOT-ALLOWED premise (`MachineClosesAt`), and
`withMemory.machine_design_noPortsR0_closed` has none — premises run, `MachineDefines withMemory`,
`ChildBnd`; goal-gap theorem with no gap hypothesis; standard axioms. A NEW statement (no design-level
base existed): against `withMemory.machine_ships_hier`, `shipsHierCheck` and `kidsMem` are absent, the
boundary `True` is `ChildBnd`, the all-worlds `MachineCloses` premise has nothing in its place, and the
conclusion is `DesignSV … 0` instead of the IR-level run.

```
20261013-075039-b17-tests: lake build Tools.ShippingMemTransport Tests.Compiler.NoPortsMemWithMemoryLib Tests.Compiler.NoPortsMemWithMemoryTest 
result=success
exit=0
memory_peak_file=770093056
Build completed successfully (591 jobs).
20261013-075129-b17-alltests: lake build Tests.AllTests 
result=success
exit=0
memory_peak_file=434692096
Build completed successfully (1244 jobs).
st.lean:115:0: WITHMEMORY DATA Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory: nDecl=2, binders=12, slots=3, loops=2, runs empty=true, call entries [SparkleMem.combo.4.8,
st.lean:360:0: WITHMEMORY ANTECEDENTS Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machine_ships_hier: 3 — [Tools.ShippingHierPremisesBase.shipsHierCheck (Tools.ShippingMachineLinked.childMap D.modules) b = true,
st.lean:360:0: WITHMEMORY ANTECEDENTS Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machine_design_noPortsR0: 1 — [Tools.ShippingChildInv.ChildBnd mref cref w]
st.lean:360:0: WITHMEMORY AUDIT Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory: Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machine_design_noPortsR0 on standard axioms, by the head machine_design_noPorts at depth 0, the memOnly_* theorems at Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory's data, composedG_src and the hand lemmas [Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_entry,
st.lean:374:0: WITHMEMORY CLOSED [Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machine_design_noPortsR0_closed]: Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machine_design_noPortsR0 with its binder MachineClosesAt Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory discharged by withMemory_closes (NO premise), by Tools.ShippingMemOnlyCloses.machineClosesAt_memOnly
st.lean:389:0: WITHMEMORY CLOSED ANTECEDENTS Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machine_design_noPortsR0_closed: 1 — [Tools.ShippingChildInv.ChildBnd mref cref w]
st.lean:389:0: WITHMEMORY CLOSED AUDIT Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory: Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machine_design_noPortsR0_closed and Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machine_design_noPortsR0_closed_gap on standard axioms, by Tools.ShippingMemOnlyCloses.machineClosesAt_memOnly and the hand lemmas [Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_entry,
```
