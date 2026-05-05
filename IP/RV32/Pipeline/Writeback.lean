/-
  RV32 writeback data selector — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (~lines 389..390 and 843..849).
  Picks the value that goes into the regfile from the EX/WB stage.

  Two related selectors:

    1. **Forwarding-cycle approximate** (`wbResultNonMemPure`,
       used in EX-stage forwarding before the load-result is available):
         exwb_isCsr  → exwb_csrRdata
         exwb_jump   → exwb_pc4    (return-address for JAL/JALR)
         else        → exwb_alu

    2. **Final WB-stage value** (`wbResultPure`):
         exwb_isSC   → 0 if reservation hit (SC succeeded) else 1
         exwb_isCsr  → exwb_csrRdata
         exwb_jump   → exwb_pc4
         exwb_m2r    → busRdata    (load result)
         else        → exwb_alu

  The SC.W return convention (0=success, 1=fail) is per RISC-V "A"
  extension §10.2: SC writes 0 to rd on success, non-zero on
  failure (we use 1).

  The forwarding selector deliberately does NOT include the load
  case — load forwarding happens in a separate path (the
  `wb_data` rewriting in `SoC.lean`) because the load result
  isn't available in the EX cycle.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure selectors -/

/-- 3-way EX-stage forwarding selector (no load case). -/
@[inline] def wbResultNonMemPure
    (isCsr : Bool) (csrRdata : BitVec 32)
    (isJump : Bool) (pc4 : BitVec 32)
    (alu : BitVec 32) : BitVec 32 :=
  if isCsr then csrRdata
  else if isJump then pc4
  else alu

/-- 5-way WB-stage selector. SC takes top priority because the SC
    return value (0/1) is computed at WB regardless of the alu value. -/
@[inline] def wbResultPure
    (isSC : Bool) (scSucceeds : Bool)
    (isCsr : Bool) (csrRdata : BitVec 32)
    (isJump : Bool) (pc4 : BitVec 32)
    (isLoad : Bool) (busRdata : BitVec 32)
    (alu : BitVec 32) : BitVec 32 :=
  if isSC then (if scSucceeds then 0#32 else 1#32)
  else if isCsr then csrRdata
  else if isJump then pc4
  else if isLoad then busRdata
  else alu

/-! ## Spec invariants — closed by `decide` / `rfl` -/

/-- ALU result is the default writeback. -/
@[simp] theorem wbResult_default
    (csrRdata pc4 busRdata alu : BitVec 32) :
    wbResultPure false false false csrRdata false pc4 false busRdata alu = alu := by
  rfl

/-- SC takes priority over every other selector. -/
@[simp] theorem wbResult_SC_priority
    (scSucceeds : Bool) (isCsr : Bool) (csrRdata : BitVec 32)
    (isJump : Bool) (pc4 : BitVec 32)
    (isLoad : Bool) (busRdata alu : BitVec 32) :
    wbResultPure true scSucceeds isCsr csrRdata isJump pc4 isLoad busRdata alu =
      (if scSucceeds then 0#32 else 1#32) := by
  rfl

/-- SC success returns 0; SC failure returns 1. -/
theorem wbResult_SC_success
    (isCsr : Bool) (csrRdata : BitVec 32)
    (isJump : Bool) (pc4 : BitVec 32)
    (isLoad : Bool) (busRdata alu : BitVec 32) :
    wbResultPure true true isCsr csrRdata isJump pc4 isLoad busRdata alu = 0#32 := by
  rfl

theorem wbResult_SC_fail
    (isCsr : Bool) (csrRdata : BitVec 32)
    (isJump : Bool) (pc4 : BitVec 32)
    (isLoad : Bool) (busRdata alu : BitVec 32) :
    wbResultPure true false isCsr csrRdata isJump pc4 isLoad busRdata alu = 1#32 := by
  rfl

/-- CSR read takes priority over jump/load (CSR rdata is the result
    of csrr*, no SC). -/
@[simp] theorem wbResult_csr_priority
    (csrRdata : BitVec 32) (isJump : Bool) (pc4 : BitVec 32)
    (isLoad : Bool) (busRdata alu : BitVec 32) :
    wbResultPure false false true csrRdata isJump pc4 isLoad busRdata alu = csrRdata := by
  rfl

/-- JAL/JALR's return-address PC+4 takes priority over load/ALU. -/
@[simp] theorem wbResult_jump_priority
    (csrRdata pc4 : BitVec 32) (isLoad : Bool) (busRdata alu : BitVec 32) :
    wbResultPure false false false csrRdata true pc4 isLoad busRdata alu = pc4 := by
  rfl

/-- Load takes priority over ALU when neither SC, CSR, nor jump fires. -/
@[simp] theorem wbResult_load_priority
    (csrRdata pc4 busRdata alu : BitVec 32) :
    wbResultPure false false false csrRdata false pc4 true busRdata alu = busRdata := by
  rfl

/-! ### Forwarding selector spec -/

/-- ALU result is the default forwarded value. -/
@[simp] theorem wbResultNonMem_default
    (csrRdata pc4 alu : BitVec 32) :
    wbResultNonMemPure false csrRdata false pc4 alu = alu := by
  rfl

/-- CSR read takes priority over jump in forwarding. -/
@[simp] theorem wbResultNonMem_csr_priority
    (csrRdata : BitVec 32) (isJump : Bool) (pc4 alu : BitVec 32) :
    wbResultNonMemPure true csrRdata isJump pc4 alu = csrRdata := by
  rfl

/-- Jump (PC+4) takes priority over ALU in forwarding. -/
@[simp] theorem wbResultNonMem_jump_priority
    (csrRdata pc4 alu : BitVec 32) :
    wbResultNonMemPure false csrRdata true pc4 alu = pc4 := by
  rfl

/-! ## Connection between the two selectors

  When neither SC nor load fires, `wbResultPure` reduces to
  `wbResultNonMemPure` — i.e. the forwarding-time value matches
  the WB-time value for non-memory, non-AMO instructions. -/

theorem wbResult_eq_nonMem_when_not_SC_or_load
    (isCsr : Bool) (csrRdata : BitVec 32)
    (isJump : Bool) (pc4 : BitVec 32)
    (busRdata alu : BitVec 32) :
    wbResultPure false false isCsr csrRdata isJump pc4 false busRdata alu =
      wbResultNonMemPure isCsr csrRdata isJump pc4 alu := by
  unfold wbResultPure wbResultNonMemPure
  rfl

/-! ## Composite specs -/

theorem wbResultNonMemPure_spec :
    ∀ (isCsr : Bool) (csrRdata : BitVec 32)
      (isJump : Bool) (pc4 alu : BitVec 32),
      wbResultNonMemPure isCsr csrRdata isJump pc4 alu =
        (if isCsr then csrRdata
         else if isJump then pc4
         else alu) := by
  intros; rfl

theorem wbResultPure_spec :
    ∀ (isSC scSucceeds : Bool) (isCsr : Bool) (csrRdata : BitVec 32)
      (isJump : Bool) (pc4 : BitVec 32) (isLoad : Bool)
      (busRdata alu : BitVec 32),
      wbResultPure isSC scSucceeds isCsr csrRdata isJump pc4 isLoad busRdata alu =
        (if isSC then (if scSucceeds then 0#32 else 1#32)
         else if isCsr then csrRdata
         else if isJump then pc4
         else if isLoad then busRdata
         else alu) := by
  intros; rfl

/-! ## Signal-level wrappers -/

def wbResultNonMemSignal {dom : DomainConfig}
    (isCsr : Signal dom Bool) (csrRdata : Signal dom (BitVec 32))
    (isJump : Signal dom Bool) (pc4 alu : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  Signal.mux isCsr csrRdata
    (Signal.mux isJump pc4 alu)

def wbResultSignal {dom : DomainConfig}
    (isSC : Signal dom Bool) (scSucceeds : Signal dom Bool)
    (isCsr : Signal dom Bool) (csrRdata : Signal dom (BitVec 32))
    (isJump : Signal dom Bool) (pc4 : Signal dom (BitVec 32))
    (isLoad : Signal dom Bool) (busRdata alu : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  Signal.mux isSC
    (Signal.mux scSucceeds (Signal.pure 0#32) (Signal.pure 1#32))
    (Signal.mux isCsr csrRdata
    (Signal.mux isJump pc4
    (Signal.mux isLoad busRdata alu)))

end Sparkle.IP.RV32.Pipeline
