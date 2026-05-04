/-
  RV32 Sv32 physical-address formation — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (~lines 520..528). Reconstructs
  the 32-bit physical address from a TLB hit, given:

    * `tlbPPN` — 22-bit physical page number (a TLB-hit's payload)
    * `tlbMega` — flag: this is a megapage (4MB) vs regular page (4KB)
    * `va` — the virtual address (alu_result_approx in the SoC)

  Per RISC-V Sv32 spec (priv §4.3.1):

    Regular page (4KB):  PA = PPN[19:0]  ‖  va[11:0]
    Megapage (4MB):      PA = PPN[19:10] ‖  va[21:0]

  The megapage case keeps PPN's *upper* 10 bits as the high
  portion of PA and uses the *lower* 22 bits of VA as the page
  offset (4MB = 2^22 byte page). The regular case keeps all 20
  bits of PPN and uses the 12-bit page offset.

  Commit bf6d873 fixed a bug in this formation (mega-page case
  was previously using the wrong PPN slice). This file makes the
  spec machine-checkable so any future regression is caught.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.MMU

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure PA formation -/

/-- Megapage PA: PPN's high-10 ‖ VA's low-22.
    Sv32 PPN is 22 bits = PPN[1] (12 bits) ++ PPN[0] (10 bits), where
    PPN[1] is `tlbPPN[21:10]` here (we take the top 10 of those 12 to
    align with the 32-bit PA layout). -/
@[inline] def dPhysAddrMegaPure (tlbPPN : BitVec 22) (va : BitVec 32) : BitVec 32 :=
  let ppnHi10 : BitVec 10 := tlbPPN.extractLsb' 10 10
  let vaLow22 : BitVec 22 := va.extractLsb' 0 22
  ppnHi10 ++ vaLow22

/-- Regular-page PA: PPN's low-20 ‖ VA's low-12.
    The low 20 bits of PPN [22-bit] are taken; the upper 2 bits of PPN
    are unused for 4GB physical address space (Sv32 PA = 34 bits in
    full but we only model 32). -/
@[inline] def dPhysAddrRegPure (tlbPPN : BitVec 22) (va : BitVec 32) : BitVec 32 :=
  let ppnLo20 : BitVec 20 := tlbPPN.extractLsb' 0 20
  let pageOff : BitVec 12 := va.extractLsb' 0 12
  ppnLo20 ++ pageOff

/-- Selected PA: pick mega-page form when `tlbMega`, else regular. -/
@[inline] def dPhysAddrPure
    (tlbMega : Bool) (tlbPPN : BitVec 22) (va : BitVec 32) : BitVec 32 :=
  if tlbMega then dPhysAddrMegaPure tlbPPN va
  else dPhysAddrRegPure tlbPPN va

/-- Effective address: translated PA if MMU is active and TLB hit, else VA. -/
@[inline] def effectiveAddrPure
    (bypassMMU anyTLBHit : Bool) (dPhysAddr va : BitVec 32) : BitVec 32 :=
  let useTranslated := !bypassMMU && anyTLBHit
  if useTranslated then dPhysAddr else va

/-! ## Spec invariants — closed by `bv_decide` -/

/-- Megapage PA: high 10 bits are `tlbPPN[19:10]`. -/
theorem dPhysAddrMega_high10 (tlbPPN : BitVec 22) (va : BitVec 32) :
    (dPhysAddrMegaPure tlbPPN va).extractLsb' 22 10 = tlbPPN.extractLsb' 10 10 := by
  unfold dPhysAddrMegaPure
  bv_decide

/-- Megapage PA: low 22 bits are `va[21:0]`. -/
theorem dPhysAddrMega_low22 (tlbPPN : BitVec 22) (va : BitVec 32) :
    (dPhysAddrMegaPure tlbPPN va).extractLsb' 0 22 = va.extractLsb' 0 22 := by
  unfold dPhysAddrMegaPure
  bv_decide

/-- Regular PA: high 20 bits are `tlbPPN[19:0]`. -/
theorem dPhysAddrReg_high20 (tlbPPN : BitVec 22) (va : BitVec 32) :
    (dPhysAddrRegPure tlbPPN va).extractLsb' 12 20 = tlbPPN.extractLsb' 0 20 := by
  unfold dPhysAddrRegPure
  bv_decide

/-- Regular PA: low 12 bits are `va[11:0]` (the page offset). -/
theorem dPhysAddrReg_low12 (tlbPPN : BitVec 22) (va : BitVec 32) :
    (dPhysAddrRegPure tlbPPN va).extractLsb' 0 12 = va.extractLsb' 0 12 := by
  unfold dPhysAddrRegPure
  bv_decide

/-- Megapage PA preserves bits 11:0 of va exactly. -/
theorem dPhysAddrMega_preserves_offset (tlbPPN : BitVec 22) (va : BitVec 32) :
    (dPhysAddrMegaPure tlbPPN va).extractLsb' 0 12 = va.extractLsb' 0 12 := by
  unfold dPhysAddrMegaPure
  bv_decide

/-! ### Effective address spec -/

/-- M-mode (bypassMMU) → effective addr is just VA, no translation. -/
@[simp] theorem effectiveAddr_bypass (anyTLBHit : Bool) (dPhysAddr va : BitVec 32) :
    effectiveAddrPure true anyTLBHit dPhysAddr va = va := by
  unfold effectiveAddrPure
  rfl

/-- TLB miss → effective addr is VA (will trigger PTW). -/
@[simp] theorem effectiveAddr_no_tlb_hit (bypassMMU : Bool) (dPhysAddr va : BitVec 32) :
    effectiveAddrPure bypassMMU false dPhysAddr va = va := by
  unfold effectiveAddrPure
  cases bypassMMU <;> rfl

/-- TLB hit + non-bypass → use translated PA. -/
@[simp] theorem effectiveAddr_translated (dPhysAddr va : BitVec 32) :
    effectiveAddrPure false true dPhysAddr va = dPhysAddr := by
  unfold effectiveAddrPure
  rfl

/-! ## Composite spec -/

theorem dPhysAddrPure_spec :
    ∀ (tlbMega : Bool) (tlbPPN : BitVec 22) (va : BitVec 32),
      dPhysAddrPure tlbMega tlbPPN va =
        (if tlbMega then dPhysAddrMegaPure tlbPPN va
         else dPhysAddrRegPure tlbPPN va) := by
  intros; rfl

/-! ## Signal-level wrappers -/

def dPhysAddrSignal {dom : DomainConfig}
    (tlbMega : Signal dom Bool)
    (tlbPPN : Signal dom (BitVec 22))
    (va : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let ppnHi10 := tlbPPN.map (BitVec.extractLsb' 10 10 ·)
  let vaLow22 := va.map (BitVec.extractLsb' 0 22 ·)
  let ppnLo20 := tlbPPN.map (BitVec.extractLsb' 0 20 ·)
  let pageOff := va.map (BitVec.extractLsb' 0 12 ·)
  let mega : Signal dom (BitVec 32) := ppnHi10 ++ vaLow22
  let reg : Signal dom (BitVec 32) := ppnLo20 ++ pageOff
  Signal.mux tlbMega mega reg

def effectiveAddrSignal {dom : DomainConfig}
    (bypassMMU anyTLBHit : Signal dom Bool)
    (dPhysAddr va : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let useTranslated := (~~~bypassMMU) &&& anyTLBHit
  Signal.mux useTranslated dPhysAddr va

/-! ## useTranslatedAddr: shared predicate

  The "use the TLB-translated PA" predicate is `¬bypassMMU ∧
  anyTLBHit` — paging is on AND the TLB has a valid entry. It's
  used both inside `effectiveAddrPure` (above) and externally as
  a register-input predicate (e.g., `prevStoreAddr` in
  `Pipeline/StoreLoadFwd.lean` selects between PA and VA based
  on this flag).

  We expose it here so call sites that want the predicate alone
  (without applying it to addresses) can reuse the proven shape.
-/

@[inline] def useTranslatedAddrPure
    (bypassMMU anyTLBHit : Bool) : Bool :=
  !bypassMMU && anyTLBHit

@[simp] theorem useTranslatedAddr_bypass (anyTLBHit : Bool) :
    useTranslatedAddrPure true anyTLBHit = false := by
  unfold useTranslatedAddrPure; cases anyTLBHit <;> rfl

@[simp] theorem useTranslatedAddr_no_hit (bypassMMU : Bool) :
    useTranslatedAddrPure bypassMMU false = false := by
  unfold useTranslatedAddrPure; cases bypassMMU <;> rfl

@[simp] theorem useTranslatedAddr_active :
    useTranslatedAddrPure false true = true := rfl

theorem useTranslatedAddrPure_spec
    (bypassMMU anyTLBHit : Bool) :
    useTranslatedAddrPure bypassMMU anyTLBHit =
      (!bypassMMU && anyTLBHit) := rfl

def useTranslatedAddrSignal {dom : DomainConfig}
    (bypassMMU anyTLBHit : Signal dom Bool) : Signal dom Bool :=
  (~~~bypassMMU) &&& anyTLBHit

end Sparkle.IP.RV32.MMU
