/-
  RV32 satp register decode + bypassMMU — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 437..439). The `satp`
  CSR (Supervisor Address Translation and Protection) controls
  whether address translation is active.

  Per RISC-V priv §4.1.11 (satp):

    satp[31]    MODE   0 = bare (no translation), 1 = Sv32
    satp[30:22] ASID   address-space ID (not used in this SoC)
    satp[21:0]  PPN    root page table's physical page number

  Translation is **active** iff:
    1. `satp.MODE = 1` (Sv32 mode)
    2. AND current privilege ≤ S (i.e. !M-mode)

  When either condition fails, we "bypass" the MMU and the
  effective address equals the virtual address (= identity
  translation).

  This file proves:
    * satpMode and PPN extraction from the 32-bit satp value.
    * bypassMMU's truth table.
    * Mutual: bypassMMU = !(translation active).
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.MMU

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure satp decode -/

/-- satp.MODE bit (bit 31). Sv32 = 1, bare = 0. -/
@[inline] def satpModePure (satp : BitVec 32) : Bool :=
  satp.extractLsb' 31 1 == 1#1

/-- satp.PPN: low 22 bits — Sv32 root page table's PPN. -/
@[inline] def satpPPNPure (satp : BitVec 32) : BitVec 22 :=
  satp.extractLsb' 0 22

/-- isMmode: privilege == M (= 3). -/
@[inline] def isMmodePure (privMode : BitVec 2) : Bool :=
  privMode == 3#2

/-- bypassMMU: M-mode OR no-translation mode. -/
@[inline] def bypassMMUPure (privMode : BitVec 2) (satp : BitVec 32) : Bool :=
  isMmodePure privMode || !(satpModePure satp)

/-- translationActive: !bypassMMU = (priv ≤ S) ∧ (satp.MODE = Sv32). -/
@[inline] def translationActivePure (privMode : BitVec 2) (satp : BitVec 32) : Bool :=
  !bypassMMUPure privMode satp

/-! ## Spec invariants — closed by `bv_decide` / `decide` -/

/-- M-mode always bypasses. -/
@[simp] theorem bypassMMU_M (satp : BitVec 32) :
    bypassMMUPure 3#2 satp = true := by
  unfold bypassMMUPure isMmodePure
  rfl

/-- Bare-mode (satp.MODE=0) always bypasses, regardless of privilege. -/
theorem bypassMMU_bare (privMode : BitVec 2) :
    bypassMMUPure privMode 0#32 = true := by
  unfold bypassMMUPure satpModePure
  cases privMode == 3#2 <;> simp

/-- S-mode + Sv32 enabled → no bypass (translation active). -/
theorem bypassMMU_S_Sv32 (satp : BitVec 32)
    (h : satpModePure satp = true) :
    bypassMMUPure 1#2 satp = false := by
  unfold bypassMMUPure isMmodePure
  rw [show (1#2 == 3#2) = false from rfl, h]
  rfl

/-- U-mode + Sv32 enabled → no bypass. -/
theorem bypassMMU_U_Sv32 (satp : BitVec 32)
    (h : satpModePure satp = true) :
    bypassMMUPure 0#2 satp = false := by
  unfold bypassMMUPure isMmodePure
  rw [show (0#2 == 3#2) = false from rfl, h]
  rfl

/-- isMmode iff privMode = 3. -/
theorem isMmode_iff (privMode : BitVec 2) :
    isMmodePure privMode = true ↔ privMode = 3#2 := by
  unfold isMmodePure
  constructor
  · intro h; exact beq_iff_eq.mp h
  · intro h; rw [h]; rfl

/-- satp.MODE bit-extract: Sv32 (mode=1) sets bit 31. -/
theorem satpMode_bit31 (satp : BitVec 32) :
    satpModePure satp = (satp.extractLsb' 31 1 == 1#1) := by
  rfl

/-- satp.PPN bit-extract spec. -/
theorem satpPPN_bits (satp : BitVec 32) :
    satpPPNPure satp = satp.extractLsb' 0 22 := by
  rfl

/-! ## Mutual exclusion / decomposition -/

/-- translationActive ↔ !M-mode AND Sv32 mode. -/
theorem translationActive_iff (privMode : BitVec 2) (satp : BitVec 32) :
    translationActivePure privMode satp =
      (!isMmodePure privMode && satpModePure satp) := by
  unfold translationActivePure bypassMMUPure
  cases isMmodePure privMode <;> cases satpModePure satp <;> rfl

/-! ## Composite specs -/

theorem bypassMMUPure_spec :
    ∀ (privMode : BitVec 2) (satp : BitVec 32),
      bypassMMUPure privMode satp =
        (privMode == 3#2 || !(satp.extractLsb' 31 1 == 1#1)) := by
  intros; rfl

/-! ## Signal-level wrappers -/

def satpModeSignal {dom : DomainConfig}
    (satp : Signal dom (BitVec 32)) : Signal dom Bool :=
  (satp.map (BitVec.extractLsb' 31 1 ·)) === 1#1

def satpPPNSignal {dom : DomainConfig}
    (satp : Signal dom (BitVec 32)) : Signal dom (BitVec 22) :=
  satp.map (BitVec.extractLsb' 0 22 ·)

def isMmodeSignal {dom : DomainConfig}
    (privMode : Signal dom (BitVec 2)) : Signal dom Bool :=
  privMode === 3#2

def bypassMMUSignal {dom : DomainConfig}
    (privMode : Signal dom (BitVec 2))
    (satp : Signal dom (BitVec 32)) : Signal dom Bool :=
  isMmodeSignal privMode ||| (~~~(satpModeSignal satp))

end Sparkle.IP.RV32.MMU
