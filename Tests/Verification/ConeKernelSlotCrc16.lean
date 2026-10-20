/-
  F2: the same kernel-discharged cone equation as
  ConeKernelSlotShareX.lean, on the real circuit.  See that file for
  the chain; CI checks that this depends on the standard three axioms
  only.  Measured 2026-09-17: 418 ms for the kernel route against 4 ms
  for `native_decide` on the same statement.
-/
import Tests.Verification.ConeSharingCrc16
import Tools.ConeFoldRT
open Tools.ConeFold Sparkle.IP.Bus.DroneCANHW

set_option maxHeartbeats 1600000

/-- crc16CcittHW, wire slot 9 (`_gen_shifted_4`). -/
theorem crc16_slot_w9_kernel :
    inlineConeT (Sparkle.IR.Optimize.buildDefMap crc16CcittHW_sdeep_body)
      (stopOfL (crc16CcittHW_sdeep_stopL.erase "_gen_shifted_4")) 10000 (.ref "_gen_shifted_4")
      = .ok crc16CcittHW_sdeep_coneRaw_w9 :=
  inlineConeT_of_listS _ _ 10000 _ _ (by decide)

#print axioms crc16_slot_w9_kernel
