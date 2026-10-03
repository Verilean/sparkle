/-
  F2: a cone equation discharged by the KERNEL, with no new trusted
  axiom — the obligation the shared route otherwise emits as
  `native_decide` (`hinl`).

  The chain is `inlineConeT_of_listS`: the structural walk `inlineConeS`
  (which the kernel CAN compute — it recurses on fuel, with `stepE`
  walking the expression structurally) agrees with the generic walk
  `inlineConeG`, which is the shipping `inlineConeT` at HashMap lookups,
  whose lookups are proven equal to the list ones
  (`buildDefMap_get?_eq`, `stopOfL_contains_elem`).  Every step is a
  proven rewrite, so `decide` discharges the shipping statement.

  The theorem must depend on the standard three axioms only; CI checks
  the `#print axioms` line.  Measured 2026-09-17: 145 ms for the kernel
  route, against 3 ms for `native_decide` on the same statement.

  (crc16's slot lives in ConeKernelSlotCrc16.lean — the two circuits'
  test modules cannot be imported into one file.)
-/
import Tests.Verification.ConeSharingGen
import Tools.ConeFoldRT
open Tools.ConeFold Sparkle.Tests.ConeSharingGen

set_option maxHeartbeats 1600000

/-- shareX4, wire slot 0. -/
theorem shareX4_slot_w0_kernel :
    inlineConeT (Sparkle.IR.Optimize.buildDefMap shareX4_sdeep_body)
      (stopOfL (shareX4_sdeep_stopL.erase "_tmp_op_a_9")) 10000 (.ref "_tmp_op_a_9")
      = .ok shareX4_sdeep_coneRaw_w0 :=
  inlineConeT_of_listS _ _ 10000 _ _ (by decide)

#print axioms shareX4_slot_w0_kernel
