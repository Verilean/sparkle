import Tests.AllTests
import Tools.ShippingEntryOkWide

/-! # `EntryOk` swept over the environment of `Tests.AllTests` (a measurement)

WRITTEN, NOT BUILT (par/a-42). TARGET-ONLY — never in `Tests/AllTests.lean`
(it imports it). Never an error except when nothing is swept; nothing is
expected or asserted. It ADDS constants to its own environment only
(`f.entry_ok`, `f.entry_wf`, `f.entry_callees` / `entry_calleesW`, and
`f.machine_closes` where a leaf had none): do not import this file anywhere.

`#entry_ok_all` runs the wide generator (`Tools/ShippingEntryOkWide.lean`)
on every declaration with generated data, leaves first, then parents by the
height of their call tree, so that a parent meets the `entry_ok` of its
callees when they succeeded:

    ENTRYOKW ROW <f>: GENERATED (<kind>); <n> premises, all reflections; … ms
    ENTRYOKW ROW <f>: <REFUSED|FAILED> (<kind>) — reason: <reason> — <note>
    ENTRYOKW SCAN: …
    ENTRYOKW KIND <kind>: <n> rows, made <a>, not made <b>
    ENTRYOKW REASON <reason>: <n> [declarations]
    ENTRYOKW FAILED <f> (<kind>): <message>
    ENTRYOKW SUMMARY of <n> rows: …

PREDICTED totals (by reading; the census of par/a-41 measured 129
declarations with a reflected term: 88 machines without a call, 38 with
calls, 3 gate children) — see `docs/parallel/A-cache-coherence-9.md`:

* gate leaves: 3 of 3 made;
* machine leaves: 80 or more of 88 made (the closing is there or derived
  for the 87 declarations worker B's leaf sweeps cover; the rest
  `missing data fact` or `failed`);
* parents (38, memory parents included): between 10 and 25 made. NOT made:
  `mixDeep` (`no closing theorem`: only the relative `closes_shared`), the
  memory parents (`memory call entry`: attempted, expected to fail at
  `hout_of_data`'s `callsOk` or at a `decide`), parents whose closing was
  generated only in a target-only test (`no closing theorem`), and every
  parent above one of those (`callee without entry_ok`).

A wall-clock budget (`Tools.ShippingEntryOkWide.budgetMs`) bounds the run;
what is left out is counted in the `SCAN` line. -/

#entry_ok_all 400

#entry_ok_all_summary
