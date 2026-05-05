/-
  RV32 Sv32 PTW memory-address generation — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 471..486). For Sv32, the
  PTW reads the page-table entries from physical memory at:

    L1 addr = {satpPPN[19:0], 12'd0} + {VPN1, 2'd0}
    L0 addr = {ptePPN[19:0], 12'd0} + {VPN0, 2'd0}

  Where:
    satpPPN[19:0] is the root page-table physical-page-number
    VPN1 = vaddr[31:22] (10 bits)
    VPN0 = vaddr[21:12] (10 bits)
    ptePPN[19:0] is the L1 PTE's PPN (when valid + non-leaf)

  The "+" operation is 32-bit add, but in practice the PPNs are
  4KB-aligned and VPN*4 is < 4KB, so there's no carry into the
  PPN bits. Each PTE is 4 bytes (hence the `*4` shift on VPN).

  Note: `0#20 ++ VPN*4` zero-extends the 12-bit VPN*4 to 32 bits
  before adding to the 32-bit PPN-shifted base.

  This file proves bit-level structure of the L1/L0 addresses:
  the 12-bit alignment, the VPN-byte-offset, etc.

  Reference: RISC-V priv §4.3.2 "Sv32 Address Translation Algorithm".
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.MMU

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure addr-generation -/

/-- Shift a 20-bit PPN to its 32-bit base address: PPN ++ 12'b0. -/
@[inline] def ppnShiftedPure (ppn20 : BitVec 20) : BitVec 32 :=
  ppn20 ++ (0#12 : BitVec 12)

/-- Shift VPN by 2 (each PTE is 4 bytes), zero-extend to 32 bits. -/
@[inline] def vpnExtPure (vpn10 : BitVec 10) : BitVec 32 :=
  let vpnx4 : BitVec 12 := vpn10 ++ (0#2 : BitVec 2)
  (0#20 : BitVec 20) ++ vpnx4

/-- L1 addr = satpPPNShifted + VPN1Ext. -/
@[inline] def l1AddrPure (satpPPN20 : BitVec 20) (vpn1 : BitVec 10) : BitVec 32 :=
  ppnShiftedPure satpPPN20 + vpnExtPure vpn1

/-- L0 addr = ptePPNShifted + VPN0Ext. -/
@[inline] def l0AddrPure (ptePPN20 : BitVec 20) (vpn0 : BitVec 10) : BitVec 32 :=
  ppnShiftedPure ptePPN20 + vpnExtPure vpn0

/-- ptwMemAddr: L1 if L1_REQ, else L0. -/
@[inline] def ptwMemAddrPure
    (ptwIsL1Req : Bool) (l1Addr l0Addr : BitVec 32) : BitVec 32 :=
  if ptwIsL1Req then l1Addr else l0Addr

/-- ptwMemActive: PTW has the bus iff L1_REQ ∨ L0_REQ. -/
@[inline] def ptwMemActivePure (ptwIsL1Req ptwIsL0Req : Bool) : Bool :=
  ptwIsL1Req || ptwIsL0Req

/-! ## Spec invariants — closed by `bv_decide` -/

/-- ppnShifted has bits [11:0] = 0 (4KB-aligned). -/
theorem ppnShifted_aligned_4k (ppn20 : BitVec 20) :
    (ppnShiftedPure ppn20).extractLsb' 0 12 = 0#12 := by
  unfold ppnShiftedPure
  bv_decide

/-- ppnShifted preserves the high 20 bits as the input PPN. -/
theorem ppnShifted_high_eq_ppn (ppn20 : BitVec 20) :
    (ppnShiftedPure ppn20).extractLsb' 12 20 = ppn20 := by
  unfold ppnShiftedPure
  bv_decide

/-- vpnExt has bits [31:12] = 0 (its only non-zero range is bits [11:2]). -/
theorem vpnExt_high_zero (vpn10 : BitVec 10) :
    (vpnExtPure vpn10).extractLsb' 12 20 = 0#20 := by
  unfold vpnExtPure
  bv_decide

/-- vpnExt has bits [1:0] = 0 (4-byte aligned). -/
theorem vpnExt_low_zero (vpn10 : BitVec 10) :
    (vpnExtPure vpn10).extractLsb' 0 2 = 0#2 := by
  unfold vpnExtPure
  bv_decide

/-- vpnExt's bits [11:2] equal the input VPN. -/
theorem vpnExt_mid_eq_vpn (vpn10 : BitVec 10) :
    (vpnExtPure vpn10).extractLsb' 2 10 = vpn10 := by
  unfold vpnExtPure
  bv_decide

/-- L1 addr is 4-byte aligned (PTE accesses are word-sized). -/
theorem l1Addr_word_aligned (satpPPN20 : BitVec 20) (vpn1 : BitVec 10) :
    (l1AddrPure satpPPN20 vpn1).extractLsb' 0 2 = 0#2 := by
  unfold l1AddrPure ppnShiftedPure vpnExtPure
  bv_decide

/-- L0 addr is 4-byte aligned. -/
theorem l0Addr_word_aligned (ptePPN20 : BitVec 20) (vpn0 : BitVec 10) :
    (l0AddrPure ptePPN20 vpn0).extractLsb' 0 2 = 0#2 := by
  unfold l0AddrPure ppnShiftedPure vpnExtPure
  bv_decide

/-! ### Mux spec -/

@[simp] theorem ptwMemAddr_l1 (l1Addr l0Addr : BitVec 32) :
    ptwMemAddrPure true l1Addr l0Addr = l1Addr := by rfl

@[simp] theorem ptwMemAddr_l0 (l1Addr l0Addr : BitVec 32) :
    ptwMemAddrPure false l1Addr l0Addr = l0Addr := by rfl

@[simp] theorem ptwMemActive_l1Req (ptwIsL0Req : Bool) :
    ptwMemActivePure true ptwIsL0Req = true := by
  unfold ptwMemActivePure; cases ptwIsL0Req <;> rfl

@[simp] theorem ptwMemActive_l0Req (ptwIsL1Req : Bool) :
    ptwMemActivePure ptwIsL1Req true = true := by
  unfold ptwMemActivePure; cases ptwIsL1Req <;> rfl

@[simp] theorem ptwMemActive_neither :
    ptwMemActivePure false false = false := by rfl

/-! ## Composite specs -/

theorem l1AddrPure_spec (satpPPN20 : BitVec 20) (vpn1 : BitVec 10) :
    l1AddrPure satpPPN20 vpn1 =
      (satpPPN20 ++ (0#12 : BitVec 12) +
        ((0#20 : BitVec 20) ++ (vpn1 ++ (0#2 : BitVec 2)))) := by rfl

theorem l0AddrPure_spec (ptePPN20 : BitVec 20) (vpn0 : BitVec 10) :
    l0AddrPure ptePPN20 vpn0 =
      (ptePPN20 ++ (0#12 : BitVec 12) +
        ((0#20 : BitVec 20) ++ (vpn0 ++ (0#2 : BitVec 2)))) := by rfl

/-! ## Signal-level wrappers -/

def ppnShiftedSignal {dom : DomainConfig}
    (ppn20 : Signal dom (BitVec 20)) : Signal dom (BitVec 32) :=
  let zero12 : Signal dom (BitVec 12) := Signal.pure 0#12
  ppn20 ++ zero12

def vpnExtSignal {dom : DomainConfig}
    (vpn10 : Signal dom (BitVec 10)) : Signal dom (BitVec 32) :=
  let zero2 : Signal dom (BitVec 2) := Signal.pure 0#2
  let vpnx4 : Signal dom (BitVec 12) := vpn10 ++ zero2
  let zero20 : Signal dom (BitVec 20) := Signal.pure 0#20
  zero20 ++ vpnx4

def l1AddrSignal {dom : DomainConfig}
    (satpPPN20 : Signal dom (BitVec 20)) (vpn1 : Signal dom (BitVec 10))
    : Signal dom (BitVec 32) :=
  ppnShiftedSignal satpPPN20 + vpnExtSignal vpn1

def l0AddrSignal {dom : DomainConfig}
    (ptePPN20 : Signal dom (BitVec 20)) (vpn0 : Signal dom (BitVec 10))
    : Signal dom (BitVec 32) :=
  ppnShiftedSignal ptePPN20 + vpnExtSignal vpn0

def ptwMemAddrSignal {dom : DomainConfig}
    (ptwIsL1Req : Signal dom Bool)
    (l1Addr l0Addr : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux ptwIsL1Req l1Addr l0Addr

def ptwMemActiveSignal {dom : DomainConfig}
    (ptwIsL1Req ptwIsL0Req : Signal dom Bool) : Signal dom Bool :=
  ptwIsL1Req ||| ptwIsL0Req

end Sparkle.IP.RV32.MMU
