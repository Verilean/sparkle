/-
  RV32 SC.W decode + dmem_we — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 551..554). The SC.W
  ("store-conditional") instruction needs special decoding at the
  EX stage to suppress the DRAM write when the reservation is
  invalid or the address doesn't match.

  Spec:

    idexIsSC_ex   = idex_isAMO ∧ (amoOp = 00011)
    scExAddrMatch = (effectiveAddr = reservationAddr)
    scExFails     = idexIsSC_ex ∧ ¬(reservationValid ∧ scExAddrMatch)
    dmem_we       = idex_memWrite ∧ isDMEM_ex
                  ∧ ¬dTLBMiss ∧ ¬scExFails

  Per RISC-V "A" extension §10.2 (SC behavior):
    SC fails (returns non-zero, doesn't write memory) if:
      - The reservation has been invalidated (any other write,
        trap, sret, mret, fence — see Reservation.lean).
      - OR the SC address doesn't match the prior LR address.
    SC succeeds (returns 0, writes memory) only when both
    conditions are met: reservation still valid AND addr match.

  Companion to:
    * `Reservation.lean` (commit 40f51e5) — reservation tracking
    * `Compute.lean` (commit 31d1f0b) — AMO compute semantics
    * `Decode.lean` (commit 07da706) — opcode decoder
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.AMO

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure decoders -/

/-- SC at EX-stage: idex_isAMO ∧ amoOp == 00011. -/
@[inline] def idexIsSCExPure (idex_isAMO : Bool) (amoOp : BitVec 5) : Bool :=
  idex_isAMO && (amoOp == 0b00011#5)

/-- SC address match: effectiveAddr == reservationAddr. -/
@[inline] def scExAddrMatchPure (effectiveAddr reservationAddr : BitVec 32) : Bool :=
  effectiveAddr == reservationAddr

/-- SC fail at EX: reservation invalid OR addr mismatch. -/
@[inline] def scExFailsPure
    (idexIsSC_ex reservationValid scExAddrMatch : Bool) : Bool :=
  idexIsSC_ex && !(reservationValid && scExAddrMatch)

/-- DRAM write enable at EX: memWrite + DMEM + no TLB miss + no SC fail. -/
@[inline] def dmemWePure
    (idex_memWrite isDMEM_ex dTLBMiss scExFails : Bool) : Bool :=
  idex_memWrite && isDMEM_ex && !dTLBMiss && !scExFails

/-! ## Spec invariants — closed by `decide` -/

/-- Non-AMO instruction → never an SC at EX. -/
@[simp] theorem idexIsSCEx_no_amo (amoOp : BitVec 5) :
    idexIsSCExPure false amoOp = false := by rfl

/-- AMO + amoOp=00011 → idexIsSCEx fires. -/
theorem idexIsSCEx_fires :
    idexIsSCExPure true 0b00011#5 = true := by rfl

/-- AMO + amoOp≠00011 → idexIsSCEx clear. -/
theorem idexIsSCEx_other_amoOp (amoOp : BitVec 5)
    (h : amoOp ≠ 0b00011#5) :
    idexIsSCExPure true amoOp = false := by
  unfold idexIsSCExPure
  have : (amoOp == 0b00011#5) = false := by
    cases h_eq : amoOp == 0b00011#5
    · rfl
    · exfalso; apply h
      -- Use BEq → eq for BitVec.
      have : amoOp = 0b00011#5 := by
        revert h_eq
        cases hb : amoOp
        bv_decide
      exact this
  simp [this]

/-! ### scExFails spec -/

/-- Non-SC instruction → never fails (vacuously). -/
@[simp] theorem scExFails_no_sc (reservationValid scExAddrMatch : Bool) :
    scExFailsPure false reservationValid scExAddrMatch = false := by rfl

/-- SC + reservation valid + addr match → succeed (no fail). -/
@[simp] theorem scExFails_succeed :
    scExFailsPure true true true = false := by rfl

/-- SC + reservation invalid → fail. -/
theorem scExFails_invalid_reservation (scExAddrMatch : Bool) :
    scExFailsPure true false scExAddrMatch = true := by
  unfold scExFailsPure
  cases scExAddrMatch <;> rfl

/-- SC + addr mismatch → fail. -/
theorem scExFails_addr_mismatch (reservationValid : Bool) :
    scExFailsPure true reservationValid false = true := by
  unfold scExFailsPure
  cases reservationValid <;> rfl

/-! ### dmem_we spec -/

/-- No memWrite → no DRAM write. -/
@[simp] theorem dmemWe_no_memWrite
    (isDMEM_ex dTLBMiss scExFails : Bool) :
    dmemWePure false isDMEM_ex dTLBMiss scExFails = false := by rfl

/-- Non-DMEM target → no DRAM write. -/
@[simp] theorem dmemWe_non_dmem
    (idex_memWrite dTLBMiss scExFails : Bool) :
    dmemWePure idex_memWrite false dTLBMiss scExFails = false := by
  unfold dmemWePure
  cases idex_memWrite <;> rfl

/-- TLB miss → suppress write. -/
@[simp] theorem dmemWe_tlb_miss
    (idex_memWrite isDMEM_ex scExFails : Bool) :
    dmemWePure idex_memWrite isDMEM_ex true scExFails = false := by
  unfold dmemWePure
  cases idex_memWrite <;> cases isDMEM_ex <;> rfl

/-- SC fail → suppress write. -/
@[simp] theorem dmemWe_sc_fail
    (idex_memWrite isDMEM_ex dTLBMiss : Bool) :
    dmemWePure idex_memWrite isDMEM_ex dTLBMiss true = false := by
  unfold dmemWePure
  cases idex_memWrite <;> cases isDMEM_ex <;> cases dTLBMiss <;> rfl

/-- All gates clear → write fires. -/
theorem dmemWe_fires :
    dmemWePure true true false false = true := by rfl

/-! ## Composite specs -/

theorem dmemWePure_spec
    (idex_memWrite isDMEM_ex dTLBMiss scExFails : Bool) :
    dmemWePure idex_memWrite isDMEM_ex dTLBMiss scExFails =
      (idex_memWrite && isDMEM_ex && !dTLBMiss && !scExFails) := by rfl

theorem scExFailsPure_spec
    (idexIsSC_ex reservationValid scExAddrMatch : Bool) :
    scExFailsPure idexIsSC_ex reservationValid scExAddrMatch =
      (idexIsSC_ex && !(reservationValid && scExAddrMatch)) := by rfl

/-! ## Signal-level wrappers -/

def idexIsSCExSignal {dom : DomainConfig}
    (idex_isAMO : Signal dom Bool) (amoOp : Signal dom (BitVec 5))
    : Signal dom Bool :=
  idex_isAMO &&& (amoOp === 0b00011#5)

def scExAddrMatchSignal {dom : DomainConfig}
    (effectiveAddr reservationAddr : Signal dom (BitVec 32)) : Signal dom Bool :=
  effectiveAddr === reservationAddr

def scExFailsSignal {dom : DomainConfig}
    (idexIsSC_ex reservationValid scExAddrMatch : Signal dom Bool) : Signal dom Bool :=
  idexIsSC_ex &&& (~~~(reservationValid &&& scExAddrMatch))

def dmemWeSignal {dom : DomainConfig}
    (idex_memWrite isDMEM_ex dTLBMiss scExFails : Signal dom Bool)
    : Signal dom Bool :=
  idex_memWrite &&& (isDMEM_ex &&& (~~~dTLBMiss)) &&& (~~~scExFails)

/-! ## WB-stage SC.W success check

  The WB stage re-evaluates SC success using the (possibly
  trap-cleared) reservation state, after the EX-stage check
  may have already gated the DRAM write. This drives the
  writeback-data path (wb_result = if isSC then (if scSucceeds
  then 0 else 1) else ...).

  Spec:
    scWBAddrMatch  = (exwb_physAddr = reservationAddr)
    scWBSucceeds   = reservationValid ∧ scWBAddrMatch

  Note: this is the "succeeds" form (negation of scExFails for
  the WB stage), reflecting that wb_result returns 0 (success)
  when both conditions hold.
-/

@[inline] def scWBAddrMatchPure (exwb_physAddr reservationAddr : BitVec 32) : Bool :=
  exwb_physAddr == reservationAddr

@[inline] def scWBSucceedsPure
    (reservationValid scWBAddrMatch : Bool) : Bool :=
  reservationValid && scWBAddrMatch

/-- Reservation invalid → SC fails (returns false). -/
@[simp] theorem scWBSucceeds_invalid (scWBAddrMatch : Bool) :
    scWBSucceedsPure false scWBAddrMatch = false := rfl

/-- Address mismatch → SC fails. -/
@[simp] theorem scWBSucceeds_no_match (reservationValid : Bool) :
    scWBSucceedsPure reservationValid false = false := by
  unfold scWBSucceedsPure; cases reservationValid <;> rfl

/-- Both true → SC succeeds. -/
@[simp] theorem scWBSucceeds_both : scWBSucceedsPure true true = true := rfl

theorem scWBSucceedsPure_spec
    (reservationValid scWBAddrMatch : Bool) :
    scWBSucceedsPure reservationValid scWBAddrMatch =
      (reservationValid && scWBAddrMatch) := rfl

/-- Bridge: scExFails ↔ ¬scWBSucceeds when same inputs.
    Exposes the dual relationship between the EX-stage gate
    (suppress write on fail) and the WB-stage result form
    (return 0 on succeed, 1 on fail). -/
theorem scWBSucceeds_dual
    (idexIsSC_ex reservationValid scAddrMatch : Bool) :
    scExFailsPure idexIsSC_ex reservationValid scAddrMatch =
      (idexIsSC_ex && !scWBSucceedsPure reservationValid scAddrMatch) := by
  unfold scExFailsPure scWBSucceedsPure; rfl

def scWBAddrMatchSignal {dom : DomainConfig}
    (exwb_physAddr reservationAddr : Signal dom (BitVec 32)) : Signal dom Bool :=
  exwb_physAddr === reservationAddr

def scWBSucceedsSignal {dom : DomainConfig}
    (reservationValid scWBAddrMatch : Signal dom Bool) : Signal dom Bool :=
  reservationValid &&& scWBAddrMatch

end Sparkle.IP.RV32.AMO
