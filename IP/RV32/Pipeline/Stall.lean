/-
  RV32 stall-source composition — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean`:
    * `mmuStall`     (line 486)     — MMU active during translation
    * `ifetchStall`  (line 1223)    — I-side TLB miss (until PTW fills)
    * `stall`        (line 1225)    — top-level disjunction over 6 sources

  Spec (the "stall" signal that holds the pipeline):

      stall = hazard ∨ mmuStall ∨ isAMOrw ∨ pendingWriteEn
            ∨ divStall ∨ ifetchStall

  Each source corresponds to a distinct reason the IDEX register
  must hold its current value:

    hazard         — load-use data hazard (no forwarding policy)
    mmuStall       — MMU PTW is busy (translation in flight)
    isAMOrw        — AMO read-modify-write needs an extra cycle
    pendingWriteEn — AMO writeback in flight
    divStall       — multi-cycle DIV/REM running
    ifetchStall    — I-side TLB miss (waiting for PTW fill)

  Per-source firing lemmas certify that any single source
  setting `true` makes `stall = true` (no forgotten case).
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure stall sources -/

/-- mmuStall: MMU translation in flight (and not bypassed). -/
@[inline] def mmuStallPure (mmuBusy bypassMMU : Bool) : Bool :=
  mmuBusy && !bypassMMU

/-- ifetchStall: I-side TLB miss (until PTW fills, but not after fault). -/
@[inline] def ifetchStallPure
    (ifetchTLBMiss ifetchFaultPending : Bool) : Bool :=
  ifetchTLBMiss && !ifetchFaultPending

/-- 6-way stall disjunction. -/
@[inline] def stallPure
    (hazard mmuStall isAMOrw pendingWriteEn divStall ifetchStall : Bool) : Bool :=
  hazard || mmuStall || isAMOrw || pendingWriteEn || divStall || ifetchStall

/-! ## Spec invariants — closed by `decide` over Bool -/

/-- All-clear → no stall. -/
@[simp] theorem stall_all_clear :
    stallPure false false false false false false = false := by rfl

/-- Each source individually fires `stall`. -/
theorem stall_hazard
    (mmuStall isAMOrw pendingWriteEn divStall ifetchStall : Bool) :
    stallPure true mmuStall isAMOrw pendingWriteEn divStall ifetchStall = true := by
  unfold stallPure; revert mmuStall isAMOrw pendingWriteEn divStall ifetchStall; decide

theorem stall_mmuStall
    (hazard isAMOrw pendingWriteEn divStall ifetchStall : Bool) :
    stallPure hazard true isAMOrw pendingWriteEn divStall ifetchStall = true := by
  unfold stallPure; revert hazard isAMOrw pendingWriteEn divStall ifetchStall; decide

theorem stall_isAMOrw
    (hazard mmuStall pendingWriteEn divStall ifetchStall : Bool) :
    stallPure hazard mmuStall true pendingWriteEn divStall ifetchStall = true := by
  unfold stallPure; revert hazard mmuStall pendingWriteEn divStall ifetchStall; decide

theorem stall_pendingWriteEn
    (hazard mmuStall isAMOrw divStall ifetchStall : Bool) :
    stallPure hazard mmuStall isAMOrw true divStall ifetchStall = true := by
  unfold stallPure; revert hazard mmuStall isAMOrw divStall ifetchStall; decide

theorem stall_divStall
    (hazard mmuStall isAMOrw pendingWriteEn ifetchStall : Bool) :
    stallPure hazard mmuStall isAMOrw pendingWriteEn true ifetchStall = true := by
  unfold stallPure; revert hazard mmuStall isAMOrw pendingWriteEn ifetchStall; decide

theorem stall_ifetchStall
    (hazard mmuStall isAMOrw pendingWriteEn divStall : Bool) :
    stallPure hazard mmuStall isAMOrw pendingWriteEn divStall true = true := by
  unfold stallPure; revert hazard mmuStall isAMOrw pendingWriteEn divStall; decide

/-! ### mmuStall edge cases -/

@[simp] theorem mmuStall_bypass (mmuBusy : Bool) :
    mmuStallPure mmuBusy true = false := by
  unfold mmuStallPure; cases mmuBusy <;> rfl

@[simp] theorem mmuStall_idle (bypassMMU : Bool) :
    mmuStallPure false bypassMMU = false := by
  rfl

theorem mmuStall_active : mmuStallPure true false = true := by rfl

/-! ### ifetchStall edge cases -/

@[simp] theorem ifetchStall_no_miss (ifetchFaultPending : Bool) :
    ifetchStallPure false ifetchFaultPending = false := by
  rfl

@[simp] theorem ifetchStall_fault_pending (ifetchTLBMiss : Bool) :
    ifetchStallPure ifetchTLBMiss true = false := by
  unfold ifetchStallPure; cases ifetchTLBMiss <;> rfl

theorem ifetchStall_active : ifetchStallPure true false = true := by rfl

/-! ## Composite specs -/

theorem stallPure_spec :
    ∀ (h m a p d i : Bool),
      stallPure h m a p d i = (h || m || a || p || d || i) := by
  decide

theorem mmuStallPure_spec (mmuBusy bypassMMU : Bool) :
    mmuStallPure mmuBusy bypassMMU = (mmuBusy && !bypassMMU) := by rfl

theorem ifetchStallPure_spec (ifetchTLBMiss ifetchFaultPending : Bool) :
    ifetchStallPure ifetchTLBMiss ifetchFaultPending =
      (ifetchTLBMiss && !ifetchFaultPending) := by rfl

/-! ## Signal-level wrappers -/

def mmuStallSignal {dom : DomainConfig}
    (mmuBusy bypassMMU : Signal dom Bool) : Signal dom Bool :=
  mmuBusy &&& (~~~bypassMMU)

def ifetchStallSignal {dom : DomainConfig}
    (ifetchTLBMiss ifetchFaultPending : Signal dom Bool) : Signal dom Bool :=
  ifetchTLBMiss &&& (~~~ifetchFaultPending)

def stallSignal {dom : DomainConfig}
    (hazard mmuStall isAMOrw pendingWriteEn divStall ifetchStall
      : Signal dom Bool) : Signal dom Bool :=
  ((hazard ||| mmuStall) ||| ((isAMOrw ||| pendingWriteEn) ||| (divStall ||| ifetchStall)))

end Sparkle.IP.RV32.Pipeline
