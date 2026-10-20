# A: cache coherence, step 9 — `EntryOk` swept over the built universe

Round par/a-42, base poc `2858bca5`. **WRITTEN, NOT BUILT**: nothing here was
compiled or run by its author. No file under `Sparkle/`, no built file, no
endpoint, no law is changed; options 1 and 3 for `mixDeep` are not touched.

## 1. Files

* `Tools/ShippingEntryOkWide.lean` — `#entry_ok_wide f`, `#entry_ok_all n`,
  `#entry_ok_all_summary`; the two refusals removed (below).
* `Tests/Compiler/EntryOkAllTest.lean` — target-only, imports
  `Tests.AllTests`; logs only.
* `docs/parallel/A-cache-coherence-summary.md` — the line a-33 … a-42 for a
  reviewer.

## 2. The two refusals removed

**(a) A machine leaf without `f.machine_closes`.** Read:
`seqChild_iface` / `seqChild_of_real` (`Tools/ShippingSeqChildIface.lean`
101, 236) ask `d.ok`, the body equation, `insts = []`, the output types, the
reflection and `MachineCloses` — NOTHING about slots. So the built leaf
generator applies to a slotless leaf as it is; what was missing is the
closing constant. It is produced by the built
`Tools.ShippingMachineClosesGen.closesTheorem?` (from the declaration's own
checks and `letsOk`, or from "no `let`, no call") — the function worker B's
leaf sweeps call. `comb_entry_shape` / `CombKid` are not needed: `EntryOk`
asks of a leaf only its module's name and an empty design, which
`ChildIfaceG` has. If the leaf fails afterwards the environment is put back.

**(b) A parent's closing under another name or form.** What the generators
leave (read: the name strings of `Tools/*.lean`):

| constant | generator | statement |
|---|---|---|
| `f.machine_closes` | `#machine_endpoint`, `closesTheorem?` | `∀ mctx mref cctx cref, MachineCloses …` |
| `f.machine_closes_at` | `ShippingMachineClosesAtGen` / `…GenG` (one-output and general closings over leaf callees) | reflections of the callees `→ MachineClosesAt …` |
| `f.closes_deep` (+ `shipping.deepSuffix`) | `ShippingChildIfaceGen` (`#machine_closes_deep`) | reflections of the descendants `→ MachineClosesAt …` |
| `f.noPortsMem_closes` | `ShippingNoPortsMemCommand` | `MachineClosesAt …` (memory-only parent) |
| `f.noPortsMemSeq_closes` | `ShippingNoPortsMemSeqCommand` | reflections of the leaf callees `→ MachineClosesAt …` |
| `f.closes_shared` | `ShippingCallsKidsSGen` | `MachineClosesAtS …` — the RELATIVE closing: not usable, not a candidate |

Instead of a list of names, `closingsOf f` takes every constant
`f.<…closes…>` whose statement CONCLUDES `MachineClosesAt` or
`MachineCloses`; a candidate is used when `apply` leaves only goals the
reflections at hand close. One with another premise is skipped.

A side effect: a parent with MEMORY call entries is now ATTEMPTED.
`entryOk_machine` allows it (`hinsG` asks `K` of non-memory callees only;
`hinsM` is vacuous when `instFields` is not empty), and the key set is the
non-memory descendants (`False` when there is none). Whether it goes through
is NOT known: `hout_of_data` asks `callsOk`. A failure is a row with the
reason `memory call entry`. Memory call entries stay listed as OPEN.

## 3. The sweep

Every declaration with `f.machineData` or `f.gateValue`, in the order
(height of the call tree, name); each row is the wide generator's outcome
with a reason; summary by kind (`gate leaf`, `machine leaf`, `parent`,
`memory parent`) and by reason (`memory call entry`,
`callee without entry_ok`, `missing data fact`, `no closing theorem`,
`no route`, `failed` + message). Capped and budgeted (25 min); leftovers
counted. Nothing is asserted.

### PREDICTED totals (129 declarations: 88 machine leaves, 38 with calls, 3 gate)

| kind | rows | made (predicted) | not made, by reason |
|---|---|---|---|
| gate leaf | 3 | 3 | — |
| machine leaf | 88 | 80 or more | `missing data fact` (no closing derivable), `failed` (a `decide` on a large term) |
| parent + memory parent | 38 | 10 to 25 | `no closing theorem` (`mixDeep`; closings generated only in target-only tests), `memory call entry`, `callee without entry_ok` (above one of those), `failed` |

These are ranges, not point predictions: which closings are in
`Tests.AllTests`' environment, and how many of the 38 are memory parents, I
did not establish.

## 4. Build queue (integrator)

`lakefile.lean` (not edited):

    lean_lib «Tools.ShippingEntryOkWide» where
      roots := #[`Tools.ShippingEntryOkWide]

`Tests/AllTests.lean`: nothing. Order: `Tools.ShippingEntryOkWide` (imports
`Tools.ShippingEntryOkCommand`, `Tools.ShippingMachineClosesGen`), then
`Tests.Compiler.EntryOkAllTest` alone (imports `Tests.AllTests`; minutes:
`mid2` alone took 3.7 s in par/a-41, and there are 38 parents).

## 5. UNVERIFIED, in risk order

1. `genParentW`: the memory branch (`absurd hEmpty (by decide)`, the
   conditional `entry_calleesW` with `memChild? x.1 = none` decided by the
   kernel), a memory parent as a callee (`EntryOk.mono … False.elim`).
2. `closingTacticW`: `refine machineClosesAt_of_closes ?_` then `apply`.
3. `entryOkWide`: the control flow (`return` in nested branches), the
   restore after a failed leaf.
4. `closesTheorem?` adding `f.machine_closes` inside this sweep (it is the
   built function; but it is called here from a command, through
   `liftTermElabM`).
5. Run time; the budget.

## 6. Open (unchanged by this round)

`MachineClosesAt mixDeep` at nested starts and `EntryOk mixDeep`; Finding I
(isolated fix verified, awaiting a ruling); memory call entries (attempted
here, not claimed); the legacy route; declarations without generated data.

## Integrator's build record (2026-10-13) — MEASURED

BUILT on poc 91f50d0b + these files, cgrun 3 GiB swap 0, run `a42` (exit 0, peak 0.87 GB), worker's files
unchanged, FIRST ATTEMPT: `Tools.ShippingEntryOkWide`; `Tests.Compiler.EntryOkAllTest` (target-only; the
sweep itself 156 s). Log: `~/sparkle-work/entryok-all.log`.

Sweep of the AllTests environment, 129 declarations with generated data: `f.entry_ok` made for 123
(GENERATED 123), REFUSED 6, FAILED 0. By kind: gate leaf 3 of 3; machine leaf 88 of 88; parent 28 of 29
(not made: `mixDeep`); memory parent 4 of 9. All six refusals have the reason "no closing theorem" in this
environment: `mixDeep` (only the relative `closes_shared`), and the memory parents `memWide`, `syncNarrow`,
`withMemory`, `mixedMems`, `twoMems` (their closings are generated in target-only tests AllTests does not
import). (Predicted: leaves ≥ 80 of 88, parents 10–25 of 38.)

A made row is `EntryOk` of ONE declaration (a returning run of its entry from an invariant world of
positive depth with a `Prov` cache and no entry for it keeps `Prov`, returns a fresh result and adds only
the listed keys), premises the reflections of the declaration and its non-memory descendants. It is not an
endpoint; no endpoint changed; `mixDeep` stays OPEN.
