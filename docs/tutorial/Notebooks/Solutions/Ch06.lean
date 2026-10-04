import Sparkle

/-!
# Chapter 6 — reference solutions
-/

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Notebooks.Solutions.Ch06

/-- Solution to Ch06 §6.7 — 4-bit saturating counter. -/
def sat4Next (en : Bool) (curr : BitVec 4) : BitVec 4 :=
  if en then
    if curr == 0xF#4 then 0xF#4
    else curr + 1#4
  else
    curr

theorem sat4Next_bounded :
    ∀ (en : Bool) (curr : BitVec 4),
      sat4Next en curr ≤ 0xF#4 := by
  intro en curr
  unfold sat4Next
  cases en <;> bv_decide

theorem sat4Next_saturated :
    ∀ (en : Bool),
      sat4Next en 0xF#4 = 0xF#4 := by
  intro en
  cases en <;> rfl

/-- K-cycle stickiness for the 4-bit version. -/
theorem sat4Counter_stuck_at_F {dom : DomainConfig}
    (regSig : Signal dom (BitVec 4))
    (en : Signal dom Bool)
    (h_recurrence :
      ∀ s, regSig.val (s + 1) =
        sat4Next (en.val s) (regSig.val s)) :
    ∀ (t k : Nat),
      regSig.val t = 0xF#4 →
      regSig.val (t + k) = 0xF#4 := by
  intro t k h_init
  induction k with
  | zero => simpa using h_init
  | succ k ih =>
    have h_step : t + (k + 1) = (t + k) + 1 := by omega
    rw [h_step, h_recurrence (t + k), ih]
    exact sat4Next_saturated (en.val (t + k))

end Notebooks.Solutions.Ch06
