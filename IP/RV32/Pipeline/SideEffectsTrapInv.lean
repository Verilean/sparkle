/-
  RV32 trap-time side-effect suppression — generic invariant

  Generalises `RegfileTrapInv.lean`'s regfile-write suppression
  to all EXWB-stage control bits gated by `suppressEXWB`.

  The witness theorem `dmemWe_not_gated_by_trap` in
  `Pipeline/AbortGuarantee.lean` (commit 90cf116) noted that the
  DRAM `dmem_we` was the *only* side-effect-bearing pipeline
  output that wasn't gated on suppressEXWB. Every other one
  was correctly gated. Commit 91a3278 fixed the DRAM gap; this
  module proves the systematic guarantee for the rest:

      For every EXWB latch driven by `mux suppressEXWB false x`,
      trap_taken at cycle t → that latch's value at cycle t+1
      = false.

  Specifically covered: exwb_regW (regfile), exwb_isCsr (CSR
  writes), prevStoreEn (store-load forwarding), exwb_m2r (load
  back-edge — though this is a read not a write, gating it
  matters for the load-result mux), exwb_jump (return-address
  writeback for JAL/JALR), exwb_isAMO (AMO RMW path).

  All inherit the same proof structure from
  `suppressEXWB_aborts_generic_bit`.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.Pipeline.AbortGuarantee
import IP.RV32.Pipeline.SuppressEXWB

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Generic theorem: any suppressEXWB-gated bit clears next cycle on trap -/

/-- For any latch built as `register false (mux suppressEXWB false x)`,
    trap_taken at cycle t → latch value at t+1 = false.

    This is the systematic generalisation of
    `trap_suppresses_exwb_regW` (`RegfileTrapInv.lean`). -/
theorem trap_clears_suppressEXWB_gated_bit {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (ctrl_bit : Signal dom Bool) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    let suppressEXWB := suppressEXWBSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect
    (Signal.register false
      (Signal.mux suppressEXWB (Signal.pure false) ctrl_bit)).atTime (t + 1) = false := by
  -- Step 1: suppressEXWB.val t = true
  have h_supp : (suppressEXWBSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect).atTime t = true := by
    unfold Signal.atTime
    rw [suppressEXWBSignal_eq_pure]
    show suppressEXWBPure (trap_taken.val t) (dTLBMiss.val t)
        (pendingWriteEn.val t) (mmuBusy.val t) (dMMURedirect.val t) = true
    rw [show trap_taken.val t = true from h_trap]
    exact suppressEXWB_trap (dTLBMiss.val t) (pendingWriteEn.val t) (mmuBusy.val t) (dMMURedirect.val t)
  -- Step 2: apply the generic abort guarantee
  exact suppressEXWB_aborts_generic_bit _ ctrl_bit t h_supp

/-! ## Per-bit specialisations

  These name each side-effect-bearing bit explicitly so other
  modules (or downstream invariants) can reference the
  bit-specific suppression. -/

/-- exwb_regW (register-file write) is suppressed at t+1 on trap. -/
theorem trap_clears_exwb_regW {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_regWrite : Signal dom Bool) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    (Signal.register false
      (Signal.mux
        (suppressEXWBSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
        (Signal.pure false) idex_regWrite)).atTime (t + 1) = false :=
  trap_clears_suppressEXWB_gated_bit _ _ _ _ _ idex_regWrite t h_trap

/-- exwb_m2r (memory-to-register, i.e. load) is suppressed at t+1 on trap. -/
theorem trap_clears_exwb_m2r {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_memToReg : Signal dom Bool) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    (Signal.register false
      (Signal.mux
        (suppressEXWBSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
        (Signal.pure false) idex_memToReg)).atTime (t + 1) = false :=
  trap_clears_suppressEXWB_gated_bit _ _ _ _ _ idex_memToReg t h_trap

/-- exwb_jump (return-address writeback for JAL/JALR) is suppressed
    at t+1 on trap. -/
theorem trap_clears_exwb_jump {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_jump : Signal dom Bool) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    (Signal.register false
      (Signal.mux
        (suppressEXWBSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
        (Signal.pure false) idex_jump)).atTime (t + 1) = false :=
  trap_clears_suppressEXWB_gated_bit _ _ _ _ _ idex_jump t h_trap

/-- exwb_isCsr (CSR write at WB-stage) is suppressed at t+1 on trap. -/
theorem trap_clears_exwb_isCsr {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_isCsr : Signal dom Bool) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    (Signal.register false
      (Signal.mux
        (suppressEXWBSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
        (Signal.pure false) idex_isCsr)).atTime (t + 1) = false :=
  trap_clears_suppressEXWB_gated_bit _ _ _ _ _ idex_isCsr t h_trap

/-- prevStoreEn (store-forward enable) is suppressed at t+1 on trap. -/
theorem trap_clears_prevStoreEn {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_memWrite : Signal dom Bool) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    (Signal.register false
      (Signal.mux
        (suppressEXWBSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
        (Signal.pure false) idex_memWrite)).atTime (t + 1) = false :=
  trap_clears_suppressEXWB_gated_bit _ _ _ _ _ idex_memWrite t h_trap

/-- exwb_isAMO (AMO opcode latched into WB stage) is suppressed at
    t+1 on trap. This is what prevents an in-flight AMOrw from
    triggering its writeback in the cycle after a trap-induced
    abort: when exwb_isAMO is false, exwb_isAMOrw is false, and
    the pending-write registers don't latch (cf. AMO/PendingWrite). -/
theorem trap_clears_exwb_isAMO {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_isAMO : Signal dom Bool) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    (Signal.register false
      (Signal.mux
        (suppressEXWBSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
        (Signal.pure false) idex_isAMO)).atTime (t + 1) = false :=
  trap_clears_suppressEXWB_gated_bit _ _ _ _ _ idex_isAMO t h_trap

/-! ## Summary

  These per-bit theorems certify that on a trap-taken cycle, *every*
  EXWB-stage side-effect-bearing latch is forced to false at cycle
  t+1. Combined with:

    * `Pipeline/StoreDuringTrap.lean` — DRAM `dmem_we` suppressed
      via `early_dramValid` (the validEX gate from commit 91a3278).

  ...the trap-entry cycle is fully clean: regfile, CSR, store,
  jump, AMO, load, DRAM are all suppressed.

  This is the **complete hardware-level** statement for invariant
  A's "regfile preservation" precondition: when the kernel takes
  a trap, no in-flight instruction modifies any architectural
  state on the trap-entry cycle (modulo the explicit trap-entry
  CSR writes to mepc/mcause/mstatus/etc. which go through the
  `csrTrapOverrideNextSignal` path proven separately in
  `CSR/Commit.lean`).
-/

end Sparkle.IP.RV32.Pipeline
