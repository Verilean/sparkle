/-
  RV32 needTranslate predicates — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean`:
    * `needTranslateD` (line 524)
    * `needTranslateI` (line 1211)
    * `ifetchTranslated` (line 1212)
    * `ifetchTLBMiss` (line 1213)
    * `dTLBMiss` (line 525)

  Translation is needed iff the MMU is active (satp.MODE = Sv32 ∧
  current priv ≤ S = !bypassMMU) AND there's a memory access in
  flight at the relevant stage:

    D-side:
      needTranslateD = (memRead ∨ memWrite) ∧ !bypassMMU

    I-side (fetch):
      needTranslateI = !bypassMMU ∧ (fetchPC[31] = 1)
                     = (satp.MODE ∧ !M-mode) ∧ DRAM-region

  The I-side has an *extra* check: `fetchPC[31] = 1`. This
  restricts translation to the upper half (Linux's
  `0x80000000..0xFFFFFFFF` virtual range). The lower half is
  treated as identity-mapped (boot ROM / firmware before MMU is
  set up). This is a Sparkle-specific simplification, not a
  Sv32 spec requirement, but it lets the firmware load DTBs at
  low addresses without being subject to translation.

  TLB miss = need translation AND no TLB hit:
    dTLBMiss = needTranslateD ∧ !anyTLBHit ∧ MMU-idle ∧ PTW-idle
    ifetchTLBMiss = needTranslateI ∧ !anyITLBHit
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.MMU

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure needTranslate predicates -/

/-- D-side memory access? -/
@[inline] def dMemAccessPure (memRead memWrite : Bool) : Bool :=
  memRead || memWrite

/-- D-side translation needed? -/
@[inline] def needTranslateDPure
    (memRead memWrite bypassMMU : Bool) : Bool :=
  dMemAccessPure memRead memWrite && !bypassMMU

/-- D-side TLB miss: need translation, no TLB hit, MMU + PTW are idle. -/
@[inline] def dTLBMissPure
    (memRead memWrite bypassMMU anyTLBHit isMMUIdle ptwIsIdle : Bool) : Bool :=
  needTranslateDPure memRead memWrite bypassMMU
    && !anyTLBHit && isMMUIdle && ptwIsIdle

/-- fetchPC[31] = 1 (DRAM region in Sparkle's address map). -/
@[inline] def fetchPCInDRAMPure (fetchPC : BitVec 32) : Bool :=
  fetchPC.extractLsb' 31 1 == 1#1

/-- I-side translation needed? -/
@[inline] def needTranslateIPure
    (satpMode isMmode : Bool) (fetchPC : BitVec 32) : Bool :=
  satpMode && !isMmode && fetchPCInDRAMPure fetchPC

/-- I-side TLB hit produces translation. -/
@[inline] def ifetchTranslatedPure
    (needTranslateI anyITLBHit : Bool) : Bool :=
  needTranslateI && anyITLBHit

/-- I-side TLB miss. -/
@[inline] def ifetchTLBMissPure
    (needTranslateI anyITLBHit : Bool) : Bool :=
  needTranslateI && !anyITLBHit

/-! ## Spec invariants — closed by `decide` / `bv_decide` -/

/-- Bypass clears D-side translation (M-mode bypass). -/
@[simp] theorem needTranslateD_bypass_clears (memRead memWrite : Bool) :
    needTranslateDPure memRead memWrite true = false := by
  unfold needTranslateDPure
  cases memRead <;> cases memWrite <;> rfl

/-- No memory access → no D-side translation. -/
@[simp] theorem needTranslateD_no_access (bypassMMU : Bool) :
    needTranslateDPure false false bypassMMU = false := by
  unfold needTranslateDPure dMemAccessPure
  rfl

/-- Memory access + no bypass → translate. -/
theorem needTranslateD_active
    (memRead memWrite : Bool)
    (h : dMemAccessPure memRead memWrite = true) :
    needTranslateDPure memRead memWrite false = true := by
  unfold needTranslateDPure
  rw [h]
  rfl

/-- D-TLB miss requires (1) translate active, (2) no hit, (3) MMU/PTW idle. -/
theorem dTLBMiss_implies_translateD
    (memRead memWrite bypassMMU anyTLBHit isMMUIdle ptwIsIdle : Bool)
    (h : dTLBMissPure memRead memWrite bypassMMU
           anyTLBHit isMMUIdle ptwIsIdle = true) :
    needTranslateDPure memRead memWrite bypassMMU = true := by
  unfold dTLBMissPure at h
  rcases (Bool.and_eq_true _ _).mp h with ⟨h12, _⟩
  rcases (Bool.and_eq_true _ _).mp h12 with ⟨h_translate, _⟩
  rcases (Bool.and_eq_true _ _).mp h_translate with ⟨h_t, _⟩
  exact h_t

/-! ### I-side spec -/

/-- M-mode → no I-side translation. -/
@[simp] theorem needTranslateI_M_mode
    (satpMode : Bool) (fetchPC : BitVec 32) :
    needTranslateIPure satpMode true fetchPC = false := by
  unfold needTranslateIPure
  cases satpMode <;> rfl

/-- satp.MODE=0 (bare) → no I-side translation. -/
@[simp] theorem needTranslateI_bare
    (isMmode : Bool) (fetchPC : BitVec 32) :
    needTranslateIPure false isMmode fetchPC = false := by
  unfold needTranslateIPure
  rfl

/-- fetchPC in low half (bit 31 = 0) → no translation. -/
theorem needTranslateI_low_half_skipped
    (satpMode isMmode : Bool) (fetchPC : BitVec 32)
    (h : fetchPC.extractLsb' 31 1 = 0#1) :
    needTranslateIPure satpMode isMmode fetchPC = false := by
  unfold needTranslateIPure fetchPCInDRAMPure
  rw [h]
  cases satpMode <;> cases isMmode <;> rfl

/-- I-TLB hit excludes I-TLB miss (mutex). -/
theorem ifetchTranslated_TLBMiss_mutex (needTranslateI anyITLBHit : Bool) :
    !(ifetchTranslatedPure needTranslateI anyITLBHit
       && ifetchTLBMissPure needTranslateI anyITLBHit) = true := by
  unfold ifetchTranslatedPure ifetchTLBMissPure
  cases anyITLBHit <;> simp

/-! ## Composite specs -/

theorem needTranslateDPure_spec
    (memRead memWrite bypassMMU : Bool) :
    needTranslateDPure memRead memWrite bypassMMU =
      ((memRead || memWrite) && !bypassMMU) := by rfl

theorem needTranslateIPure_spec
    (satpMode isMmode : Bool) (fetchPC : BitVec 32) :
    needTranslateIPure satpMode isMmode fetchPC =
      (satpMode && !isMmode && (fetchPC.extractLsb' 31 1 == 1#1)) := by rfl

/-! ## Signal-level wrappers -/

def dMemAccessSignal {dom : DomainConfig}
    (memRead memWrite : Signal dom Bool) : Signal dom Bool :=
  memRead ||| memWrite

def needTranslateDSignal {dom : DomainConfig}
    (memRead memWrite bypassMMU : Signal dom Bool) : Signal dom Bool :=
  dMemAccessSignal memRead memWrite &&& (~~~bypassMMU)

def fetchPCInDRAMSignal {dom : DomainConfig}
    (fetchPC : Signal dom (BitVec 32)) : Signal dom Bool :=
  (fetchPC.map (BitVec.extractLsb' 31 1 ·)) === 1#1

def needTranslateISignal {dom : DomainConfig}
    (satpMode isMmode : Signal dom Bool)
    (fetchPC : Signal dom (BitVec 32)) : Signal dom Bool :=
  satpMode &&& ((~~~isMmode) &&& fetchPCInDRAMSignal fetchPC)

def ifetchTranslatedSignal {dom : DomainConfig}
    (needTranslateI anyITLBHit : Signal dom Bool) : Signal dom Bool :=
  needTranslateI &&& anyITLBHit

def ifetchTLBMissSignal {dom : DomainConfig}
    (needTranslateI anyITLBHit : Signal dom Bool) : Signal dom Bool :=
  needTranslateI &&& (~~~anyITLBHit)

def dTLBMissSignal {dom : DomainConfig}
    (needTranslateD anyTLBHit isMMUIdle ptwIsIdle : Signal dom Bool)
    : Signal dom Bool :=
  needTranslateD &&& ((~~~anyTLBHit) &&& (isMMUIdle &&& ptwIsIdle))

end Sparkle.IP.RV32.MMU
