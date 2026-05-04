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

end Sparkle.IP.RV32.CLINT
