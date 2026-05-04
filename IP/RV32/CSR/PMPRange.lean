/-
  RV32 PMP CSR range check — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 946..952). The PMP
  (Physical Memory Protection) CSRs occupy addresses
  0x3A0..0x3EF in the CSR space:

    0x3A0..0x3AF   pmpcfg0..pmpcfg15   (configuration registers)
                                       (only 0x3A0-0x3A3 used in
                                        Sv32; 0x3A4-0x3AF would be
                                        Sv57+ extensions)
    0x3B0..0x3EF   pmpaddr0..pmpaddr63 (address registers)
                                       (only 0x3B0-0x3BF used)

  Sparkle does not implement PMP — these CSRs are recognized as a
  range but reads return 0 and writes are silently ignored. This
  satisfies the spec's "WPRI" (Writes Preserve Reserved-as-Zero)
  semantics for unimplemented CSRs.

  Spec:
    csrIsPmp  iff csrAddr[11:4] ∈ {0x3A, 0x3B, 0x3C, 0x3D, 0x3E}

  Equivalently: csrAddr ∈ [0x3A0, 0x3EF] (a 5-block range of 16
  addresses each, 80 total CSR slots).
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.CSR

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure PMP range check -/

/-- The CSR address's high 8 bits (bits [11:4]). -/
@[inline] def csrAddrHiPure (csrAddr : BitVec 12) : BitVec 8 :=
  csrAddr.extractLsb' 4 8

/-- True iff csrAddr[11:4] ∈ {0x3A..0x3E}. -/
@[inline] def csrIsPmpPure (csrAddr : BitVec 12) : Bool :=
  let hi := csrAddrHiPure csrAddr
  (hi == 0x3A#8) || (hi == 0x3B#8) || (hi == 0x3C#8) ||
  (hi == 0x3D#8) || (hi == 0x3E#8)

/-! ## Spec invariants — closed by `bv_decide` -/

/-- pmpcfg0 (0x3A0) is in range. -/
theorem pmpcfg0_in_range :
    csrIsPmpPure 0x3A0#12 = true := by
  unfold csrIsPmpPure csrAddrHiPure
  bv_decide

/-- pmpcfg15 (0x3AF) is in range. -/
theorem pmpcfg15_in_range :
    csrIsPmpPure 0x3AF#12 = true := by
  unfold csrIsPmpPure csrAddrHiPure
  bv_decide

/-- pmpaddr0 (0x3B0) is in range. -/
theorem pmpaddr0_in_range :
    csrIsPmpPure 0x3B0#12 = true := by
  unfold csrIsPmpPure csrAddrHiPure
  bv_decide

/-- pmpaddr63 (0x3EF) is in range — the highest PMP CSR. -/
theorem pmpaddr63_in_range :
    csrIsPmpPure 0x3EF#12 = true := by
  unfold csrIsPmpPure csrAddrHiPure
  bv_decide

/-- 0x39F (just below the range) is out. -/
theorem boundary_below_range :
    csrIsPmpPure 0x39F#12 = false := by
  unfold csrIsPmpPure csrAddrHiPure
  bv_decide

/-- 0x3F0 (just above the range) is out. -/
theorem boundary_above_range :
    csrIsPmpPure 0x3F0#12 = false := by
  unfold csrIsPmpPure csrAddrHiPure
  bv_decide

/-- mstatus (0x300) is NOT a PMP CSR. -/
theorem mstatus_not_pmp :
    csrIsPmpPure 0x300#12 = false := by
  unfold csrIsPmpPure csrAddrHiPure
  bv_decide

/-- satp (0x180) is NOT a PMP CSR. -/
theorem satp_not_pmp :
    csrIsPmpPure 0x180#12 = false := by
  unfold csrIsPmpPure csrAddrHiPure
  bv_decide

/-! ## Range characterization

  csrIsPmp fires iff csrAddr is in the closed interval [0x3A0, 0x3EF]. -/

theorem csrIsPmp_iff_in_range (csrAddr : BitVec 12) :
    csrIsPmpPure csrAddr = (csrAddr.extractLsb' 4 8 == 0x3A#8 ||
                             csrAddr.extractLsb' 4 8 == 0x3B#8 ||
                             csrAddr.extractLsb' 4 8 == 0x3C#8 ||
                             csrAddr.extractLsb' 4 8 == 0x3D#8 ||
                             csrAddr.extractLsb' 4 8 == 0x3E#8) := by
  rfl

/-! ## Signal-level wrapper -/

def csrAddrHiSignal {dom : DomainConfig}
    (csrAddr : Signal dom (BitVec 12)) : Signal dom (BitVec 8) :=
  csrAddr.map (BitVec.extractLsb' 4 8 ·)

def csrIsPmpSignal {dom : DomainConfig}
    (csrAddr : Signal dom (BitVec 12)) : Signal dom Bool :=
  let hi := csrAddrHiSignal csrAddr
  (hi === 0x3A#8) ||| (hi === 0x3B#8) ||| (hi === 0x3C#8) |||
  (hi === 0x3D#8) ||| (hi === 0x3E#8)

end Sparkle.IP.RV32.CSR
