/-
  RV32 mtime / mtimecmp arithmetic — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean`:
    * `mtimeLoInc`/`mtimeHiInc` (lines 1330..1333) — split-32 increment
      of the 64-bit mtime register with carry from low to high.
    * `timerIrq` (lines 892..895) — `mtime ≥ mtimecmp` as an unsigned
      64-bit comparison split into two 32-bit halves.

  Spec:

    Let mtime    = mtimeHi  ∶∶ mtimeLo  : BitVec 64
        mtimecmp = mtimecmpHi ∶∶ mtimecmpLo : BitVec 64

    mtimeIncHi, mtimeIncLo   = (mtime + 1).{hi,lo}
    timerIrq                 = (mtime ≥ mtimecmp)  unsigned

  We capture both as pure functions with `bv_decide`-closed
  correctness against the 64-bit interpretation, plus the per-half
  invariants used by SoC.lean's split arithmetic.

  These two pieces are the heart of the timer interrupt path —
  any drift between the split-32 implementation and the 64-bit
  spec would cause spurious or missed timer IRQs.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.CSR.Commit

namespace Sparkle.IP.RV32.CLINT

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure mtime increment -/

/-- Low half of mtime+1: unconditional 32-bit increment. -/
@[inline] def mtimeIncLoPure (mtimeLo : BitVec 32) : BitVec 32 :=
  mtimeLo + 1#32

/-- Carry from low to high: low half wraps to 0 iff its previous value
    was 0xFFFFFFFF (so the +1 becomes 0). The implementation tests the
    *result* against 0; this is correct because `0xFFFFFFFF + 1 = 0` in
    BitVec 32. -/
@[inline] def mtimeCarryPure (mtimeLo : BitVec 32) : Bool :=
  mtimeIncLoPure mtimeLo == 0#32

/-- High half of mtime+1: increment only if the low half wraps. -/
@[inline] def mtimeIncHiPure (mtimeLo mtimeHi : BitVec 32) : BitVec 32 :=
  if mtimeCarryPure mtimeLo then mtimeHi + 1#32 else mtimeHi

/-! ## Spec: split-32 increment matches 64-bit increment -/

/-- The combined 64-bit value matches `(mtimeHi || mtimeLo) + 1`. -/
theorem mtime_inc_eq_64bit (mtimeLo mtimeHi : BitVec 32) :
    (mtimeIncHiPure mtimeLo mtimeHi ++ mtimeIncLoPure mtimeLo)
      = (mtimeHi ++ mtimeLo) + 1#64 := by
  unfold mtimeIncHiPure mtimeIncLoPure mtimeCarryPure mtimeIncLoPure
  bv_decide

/-- Carry sanity check: low half wraps iff it was all-ones. -/
theorem mtimeCarry_iff_max (mtimeLo : BitVec 32) :
    mtimeCarryPure mtimeLo = (mtimeLo == 0xFFFFFFFF#32) := by
  unfold mtimeCarryPure mtimeIncLoPure
  bv_decide

/-! ## Pure timerIrq: mtime ≥ mtimecmp (unsigned, 64-bit) -/

/-- Split-32 ≥ comparison.

    `(mtimeHi ‖ mtimeLo) ≥ (mtimecmpHi ‖ mtimecmpLo)` decomposed:
      hiGt = mtimecmpHi <ᵤ mtimeHi
      hiEq = (mtimeHi = mtimecmpHi)
      loGe = ¬(mtimeLo <ᵤ mtimecmpLo)
      result = hiGt ∨ (hiEq ∧ loGe)
-/
@[inline] def timerIrqPure
    (mtimeLo mtimeHi mtimecmpLo mtimecmpHi : BitVec 32) : Bool :=
  let hiGt := mtimecmpHi.ult mtimeHi
  let hiEq := mtimeHi == mtimecmpHi
  let loGe := !(mtimeLo.ult mtimecmpLo)
  hiGt || (hiEq && loGe)

/-! ## Spec: split-32 ≥ matches 64-bit ≥ -/

/-- The split-32 form computes `mtime ≥ mtimecmp` on the combined 64-bit
    value, exactly. -/
theorem timerIrq_eq_64bit
    (mtimeLo mtimeHi mtimecmpLo mtimecmpHi : BitVec 32) :
    timerIrqPure mtimeLo mtimeHi mtimecmpLo mtimecmpHi =
      !((mtimeHi ++ mtimeLo).ult (mtimecmpHi ++ mtimecmpLo)) := by
  unfold timerIrqPure
  bv_decide

/-- When `mtime = mtimecmp`, `timerIrq` fires (greater-or-equal). -/
theorem timerIrq_eq_when_equal
    (mtimeLo mtimeHi : BitVec 32) :
    timerIrqPure mtimeLo mtimeHi mtimeLo mtimeHi = true := by
  unfold timerIrqPure
  bv_decide

/-- When `mtime` is strictly less than `mtimecmp`, `timerIrq` clears. -/
theorem timerIrq_clear_when_less
    (mtimeLo mtimeHi mtimecmpLo mtimecmpHi : BitVec 32)
    (h : (mtimeHi ++ mtimeLo).ult (mtimecmpHi ++ mtimecmpLo) = true) :
    timerIrqPure mtimeLo mtimeHi mtimecmpLo mtimecmpHi = false := by
  rw [timerIrq_eq_64bit, h]
  rfl

/-! ## Signal-level wrappers -/

def mtimeIncLoSignal {dom : DomainConfig}
    (mtimeLo : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let one : Signal dom (BitVec 32) := Signal.pure 1#32
  mtimeLo + one

def mtimeCarrySignal {dom : DomainConfig}
    (mtimeLo : Signal dom (BitVec 32)) : Signal dom Bool :=
  mtimeIncLoSignal mtimeLo === Signal.pure 0#32

def mtimeIncHiSignal {dom : DomainConfig}
    (mtimeLo mtimeHi : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let one : Signal dom (BitVec 32) := Signal.pure 1#32
  Signal.mux (mtimeCarrySignal mtimeLo) (mtimeHi + one) mtimeHi

def timerIrqSignal {dom : DomainConfig}
    (mtimeLo mtimeHi mtimecmpLo mtimecmpHi : Signal dom (BitVec 32))
    : Signal dom Bool :=
  let hiGt := Signal.ult mtimecmpHi mtimeHi
  let hiEq := mtimeHi === mtimecmpHi
  let loGe := ~~~(Signal.ult mtimeLo mtimecmpLo)
  hiGt ||| (hiEq &&& loGe)

/-! ## Sequential mtime ticking

  When no CSR write fires (trap, idle, normal cycle without
  mtimecmp update), the mtime register advances by 1 (mtimeLo)
  plus carry (mtimeHi). Built on top of `csrPlainReg_hold_when_we_false`
  but with the "old" arm being the incremented value
  `mtimeIncLo = mtimeLo + 1`. -/

/-- **No CSR write at t → mtimeLoReg at t+1 = mtimeLo.val t + 1.** -/
theorem mtimeLoReg_advances_when_no_we {dom : DomainConfig}
    (mtimeLoWE : Signal dom Bool)
    (newVal mtimeLo : Signal dom (BitVec 32)) (t : Nat)
    (h_no_we : mtimeLoWE.val t = false) :
    (Signal.register 0#32
      (Sparkle.IP.RV32.CSR.csrPlainNextSignal mtimeLoWE newVal
        (mtimeIncLoSignal mtimeLo))).val (t + 1) = mtimeLo.val t + 1#32 := by
  show (Signal.register 0#32 _).val (t + 1) = _
  show (Sparkle.IP.RV32.CSR.csrPlainNextSignal mtimeLoWE newVal
    (mtimeIncLoSignal mtimeLo)).val t = mtimeLo.val t + 1#32
  rw [Sparkle.IP.RV32.CSR.csrPlainNextSignal_eq_pure]
  rw [h_no_we]
  show (mtimeIncLoSignal mtimeLo).val t = mtimeLo.val t + 1#32
  unfold mtimeIncLoSignal
  rfl

/-- **No CSR write at t → mtimeHiReg at t+1 = mtimeHi.val t + carry.val t.**

    Where `carry = (mtimeLo + 1 == 0)` (i.e., the low half wraps
    around). Built on `mtimeIncHiPure` which already proves
    `mtimeIncHi = mtimeHi + carry`. -/
theorem mtimeHiReg_advances_when_no_we {dom : DomainConfig}
    (mtimeHiWE : Signal dom Bool)
    (newVal mtimeLo mtimeHi : Signal dom (BitVec 32)) (t : Nat)
    (h_no_we : mtimeHiWE.val t = false) :
    (Signal.register 0#32
      (Sparkle.IP.RV32.CSR.csrPlainNextSignal mtimeHiWE newVal
        (mtimeIncHiSignal mtimeLo mtimeHi))).val (t + 1) =
      (mtimeIncHiSignal mtimeLo mtimeHi).val t := by
  show (Signal.register 0#32 _).val (t + 1) = _
  show (Sparkle.IP.RV32.CSR.csrPlainNextSignal mtimeHiWE newVal
    (mtimeIncHiSignal mtimeLo mtimeHi)).val t = _
  rw [Sparkle.IP.RV32.CSR.csrPlainNextSignal_eq_pure]
  rw [h_no_we]
  rfl

/-! ## LTL forms -/

/-- **LTL form of `mtimeLoReg_advances_when_no_we`.** -/
theorem mtimeLoReg_advances_when_no_we_LTL {dom : DomainConfig}
    (mtimeLoWE : Signal dom Bool)
    (newVal mtimeLo : Signal dom (BitVec 32)) :
    ∀ t, mtimeLoWE.val t = false →
         (Signal.register 0#32
           (Sparkle.IP.RV32.CSR.csrPlainNextSignal mtimeLoWE newVal
             (mtimeIncLoSignal mtimeLo))).val (t + 1) = mtimeLo.val t + 1#32 :=
  fun t => mtimeLoReg_advances_when_no_we mtimeLoWE newVal mtimeLo t

/-- **LTL form of `mtimeHiReg_advances_when_no_we`.** -/
theorem mtimeHiReg_advances_when_no_we_LTL {dom : DomainConfig}
    (mtimeHiWE : Signal dom Bool)
    (newVal mtimeLo mtimeHi : Signal dom (BitVec 32)) :
    ∀ t, mtimeHiWE.val t = false →
         (Signal.register 0#32
           (Sparkle.IP.RV32.CSR.csrPlainNextSignal mtimeHiWE newVal
             (mtimeIncHiSignal mtimeLo mtimeHi))).val (t + 1) =
           (mtimeIncHiSignal mtimeLo mtimeHi).val t :=
  fun t => mtimeHiReg_advances_when_no_we mtimeHiWE newVal mtimeLo mtimeHi t

end Sparkle.IP.RV32.CLINT
