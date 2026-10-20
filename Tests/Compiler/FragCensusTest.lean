import Tests.AllTests
import Tools.ShippingFragCensus

/-! # The walk's first fragment against the built universe (a measurement)

WRITTEN, NOT BUILT (par/a-41). TARGET-ONLY — never in `Tests/AllTests.lean`
(it imports it). Logs only: nothing is asserted, nothing is added.

`#frag_row` on the five declarations of the `mixDeep` family first, then
`#frag_census` over every declaration of `Tests.AllTests`' environment that
has a reflected term (`f.gateTerm`, else `f.machineData`), then the summary.
Each Boolean is a kernel `decide` tried in both polarities
(`Tools/ShippingFragCensus.lean`); reflected data is never evaluated by
compiled code.

    FRAGCENSUS ROW <f>: <machine|gate>; wfrag=<T/F/?>; wfragAll=T (every term); calls=<none|some|?|->
    FRAGCENSUS SCAN: …
    FRAGCENSUS SUMMARY of <n> rows: …

## What the numbers mean

`wfrag=T`: the declaration's term was already inside the walk of par/a-36.
`wfrag=F`: it uses one of the eleven constructors added in par/a-41
(`Tools/ShippingWalkStillMore.lean`) — reached by `walk_still_all` only.
`?`: the kernel did not decide within the default heartbeats (a large term);
not a verdict. Every row is inside `wfragAll` (the walk now has no term
condition).

## PREDICTED

* the five of the family: `wfrag=T` (MEASURED before: `cnt_frag`,
  `midH_frag`, `mid2_frag`, `mixDeep_frag`, `rcH_frag` are built theorems);
* the others: NO per-declaration prediction. By reading the sources of a few
  test files: declarations using slices, sign / zero extension, numeric
  literals (`Signal.pure 5`), `~~~` on a Bool, or applicative lifts
  (`(· && ·) <$> a <*> b`) are `wfrag=F`; plain register machines over
  `+`, `===`, `mux` are `T`. The count of `F` is the measurement.

Cost: up to four kernel decisions per declaration, about 130 declarations;
a wall-clock budget of `Tools.ShippingFragCensus.budgetMs` — what is left
out is counted in the `SCAN` line. -/

#frag_row Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
#frag_row Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
#frag_row Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
#frag_row Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
#frag_row Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep

#frag_census 200

#frag_census_summary
