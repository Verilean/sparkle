/-
  Vertical stabilisation of an elongated tokamak plasma — plant model,
  controller, and the recoverable region.

  ## The physics, reduced

  An elongated plasma is vertically unstable: displaced by z, the shaping
  field pushes it further.  The passive structure slows the motion to a
  growth rate γ that a feedback system can follow; an active coil,
  driven by a power supply, pushes back.  The standard rigid-displacement
  model has three states:

      z   vertical position            ż = γ·z + g·I
      I   active-coil current          İ = (V − R·I)/L
      V   power-supply voltage         V̇ = (V_cmd − V)/τₛ       |V_cmd| ≤ V_max

  The supply saturates.  That is the whole difficulty: with a bounded
  actuator an unstable plant can only be recovered from a bounded set of
  states, and outside it the plasma is lost whatever the controller does
  (a vertical displacement event).

  ## The discrete model (what the circuit implements)

  Forward Euler at the control period dt, with the parameters chosen so
  that every coefficient is a shift (units: cm, kA, ms; dt = 1/16 ms):

      z' = z + z/64 + I/16          γ·dt = 1/64   (γ = 250 s⁻¹),  g·dt = 1/16
      I' = I − I/64 + V/16          dt·R/L = 1/64 (L/R = 4 ms),   dt/L = 1/16
      V' = V + 7·(V_cmd − V)/64     dt/τₛ = 7/64  (τₛ ≈ 0.57 ms)

  Q15.16 in `BitVec 32`; every division rounds down (an arithmetic shift).

  ## The unstable mode and the controller

  The matrix has one eigenvalue outside the unit circle, 65/64, with left
  eigenvector (1, 2, 1).  So the one quantity that matters is

      ξ = z + 2·I + V                ξ' = (65/64)·ξ + (7/64)·V_cmd

  (exactly, in real arithmetic; with the rounding above the error is
  between −5 and +2 units of 2⁻¹⁶ per step).  Two consequences:

    * |ξ| < 7·V_max is NECESSARY for recovery: beyond it ξ grows even at
      full opposing voltage;
    * the saturating law  V_cmd = clamp(−4·ξ, ±V_max)  recovers EVERY
      state inside it: it contracts ξ by 37/64 per step when unsaturated
      and still decreases |ξ| when saturated.

  With V_max = 2 the boundary is |ξ| = 14.

  ## What is proven, and about what

  The reference model below (`step`) is the discrete model with all its
  rounding, on mathematical integers (units of 2⁻¹⁶).  The theorems at the
  end are about it — not about the real-valued model:

    `recoverable_invariant`  the region |ξ| ≤ 14 − 2⁻⁷ (with |I|, |V|, |z|
                             in range) is never left;
    `recoverable_progress`   inside it, while |ξ| ≥ 16 units, |ξ| decreases
                             every step;
    `settled_invariant`      once below 16 units it stays below;
    `recovers`               so every state in the region reaches |ξ| < 16
                             units (2.4·10⁻⁴ cm) in finitely many steps;
    `beyond_is_lost`         for |ξ| ≥ 14 + 2⁻⁷ and ANY command within the
                             supply's range, |ξ| increases — no controller
                             recovers it.

  The proofs are `omega` (linear integer arithmetic with the floors), so
  they are checked by Lean's kernel with no solver trusted.  The gap
  between 14 − 2⁻⁷ and 14 + 2⁻⁷ is the rounding: the floors can move ξ by
  up to 5 units per step, always downwards, which costs the negative side
  of the region 320 units.

  Not proven: that the circuit `closedLoop` computes `step`.  It is
  compared with it cycle by cycle in simulation (`Tests/PlasmaTest.lean`);
  the two can only differ if a 32-bit value wraps, and inside the region
  everything stays below 2²² units.  The plant is a model: its parameters
  are round numbers of the right order of magnitude, not those of a
  particular machine.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Control.FixedPoint

namespace Sparkle.IP.Plasma.VerticalStab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Control.FixedPoint (clampSymC sext32to64)

/-! ### Reference model (integers, units of 2⁻¹⁶) -/

/-- Supply limit V_max = 2.0. -/
def vMax : Int := 131072

/-- Vessel half-height: 48.0 cm.  The position is clamped here — a plasma
    that reaches the wall is lost, and the model stops there. -/
def zWall : Int := 3145728

/-- Edge of the region the theorems cover: 14 − 2⁻⁷. -/
def xiSafe : Int := 916992

/-- Clamp to [−lim, lim]. -/
def clamp (lim x : Int) : Int := if lim < x then lim else if x < -lim then -lim else x

structure State where
  z : Int
  i : Int
  v : Int
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The unstable-mode coordinate ξ = z + 2·I + V. -/
def xi (s : State) : Int := s.z + 2 * s.i + s.v

/-- The control law: V_cmd = clamp(−4·ξ, ±V_max). -/
def control (s : State) : Int := clamp vMax (-(4 * xi s))

/-- One control period of the plant under command `vc`, with an external
    displacement `kick` added to the position.  `/` rounds down. -/
def plant (s : State) (vc kick : Int) : State :=
  { z := clamp zWall (s.z + s.z / 64 + s.i / 16 + kick)
    i := s.i - s.i / 64 + s.v / 16
    v := s.v + 7 * (vc - s.v) / 64 }

/-- One period of the closed loop (`enable = false`: the supply is commanded
    to zero — the open loop). -/
def step (enable : Bool) (s : State) (kick : Int) : State :=
  plant s (if enable then control s else 0) kick

/-- Outside the region the theorems cover?  (The alarm output.) -/
def alarm (s : State) : Bool := decide (xiSafe < xi s) || decide (xi s < -xiSafe)

/-- The closed loop left alone for `n` periods. -/
def settle (s : State) : Nat → State
  | 0 => s
  | n + 1 => settle (step true s 0) n

/-! ### The circuit -/

/-- The model's constants as the 32-bit words the circuit uses. -/
def vMaxW : BitVec 32 := 0x00020000#32
def zWallW : BitVec 32 := 0x00300000#32
def xiSafeW : BitVec 32 := 0x000DFE00#32

example : vMaxW.toInt = vMax ∧ zWallW.toInt = zWall ∧ xiSafeW.toInt = xiSafe := by decide

/-- `⌊x / 2ᵏ⌋` on a signal (arithmetic shift right), as sign-extend-and-slice
    — the form the synthesis elaborator lowers. -/
def asrS {dom : DomainConfig} (k : Nat) (x : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  (sext32to64 x).map (BitVec.extractLsb' k 32 ·)

/-- The controller alone — what goes on the board: three measurements in,
    the supply command out. -/
def controller {dom : DomainConfig} (z i v : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let x := z + (i + i) + v
  let x2 := x + x
  clampSymC vMaxW ((Signal.pure 0#32 : Signal dom (BitVec 32)) - (x2 + x2))

/-- Plant and controller in one loop, for simulation.
    Output: `alarm ++ V_cmd ++ z` (1 + 32 + 32 bits). -/
def closedLoop {dom : DomainConfig} (kick : Signal dom (BitVec 32)) (enable : Signal dom Bool) :
    Signal dom (BitVec 65) :=
  circuit do
    let zR ← Signal.reg 0#32
    let iR ← Signal.reg 0#32
    let vR ← Signal.reg 0#32
    let z := (zR : Signal dom (BitVec 32))
    let i := (iR : Signal dom (BitVec 32))
    let v := (vR : Signal dom (BitVec 32))
    let zero := (Signal.pure 0#32 : Signal dom (BitVec 32))
    let vc := Signal.mux enable (controller z i v) zero
    -- 7·(V_cmd − V) as 8·d − d
    let d := vc - v
    let d2 := d + d
    let d4 := d2 + d2
    zR <~ clampSymC zWallW (z + asrS 6 z + asrS 4 i + kick)
    iR <~ i - asrS 6 i + asrS 4 v
    vR <~ v + asrS 6 (d4 + d4 - d)
    let x := z + (i + i) + v
    let safe := (Signal.pure xiSafeW : Signal dom (BitVec 32))
    let out := Signal.mux (Signal.slt safe x) (Signal.pure 1#1)
      (Signal.mux (Signal.slt x (zero - safe)) (Signal.pure 1#1) (Signal.pure 0#1))
    return out ++ (vc ++ z)

/-! ### The recoverable region -/

/-- The region: |ξ| ≤ 14 − 2⁻⁷, and the other states in the ranges the
    dynamics keep them in (|I| ≤ 8 + 2⁻⁹, |V| ≤ V_max, |z| ≤ 40). -/
def recoverable (s : State) : Prop :=
  (-xiSafe ≤ xi s ∧ xi s ≤ xiSafe) ∧ (-524416 ≤ s.i ∧ s.i ≤ 524416) ∧
    (-vMax ≤ s.v ∧ s.v ≤ vMax) ∧ (-2621440 ≤ s.z ∧ s.z ≤ 2621440)

/-- What `clamp` does, as linear facts (so that the proofs below see no
    `if`). -/
theorem clamp_spec (lim x : Int) :
    (lim < x → clamp lim x = lim) ∧ (x < -lim → ¬ lim < x → clamp lim x = -lim) ∧
    (¬ lim < x → ¬ x < -lim → clamp lim x = x) := by
  unfold clamp
  exact ⟨fun h => by simp [h], fun h h' => by simp [h, h'], fun h h' => by simp [h, h']⟩

/-- The recoverable region is never left. -/
theorem recoverable_invariant (s : State) (h : recoverable s) :
    recoverable (step true s 0) := by
  obtain ⟨z, i, v⟩ := s
  have hc := clamp_spec vMax (-(4 * (z + 2 * i + v)))
  have hw := clamp_spec zWall (z + z / 64 + i / 16 + 0)
  simp only [recoverable, xi, step, plant, control, if_true] at h ⊢
  generalize clamp vMax (-(4 * (z + 2 * i + v))) = vc at hc ⊢
  generalize clamp zWall (z + z / 64 + i / 16 + 0) = z' at hw ⊢
  simp only [vMax, zWall, xiSafe] at h hc hw ⊢
  omega

/-- Inside it, while |ξ| ≥ 16 units, |ξ| decreases every step. -/
theorem recoverable_progress (s : State) (h : recoverable s)
    (hbig : 16 ≤ (xi s).natAbs) :
    (xi (step true s 0)).natAbs < (xi s).natAbs := by
  obtain ⟨z, i, v⟩ := s
  have hc := clamp_spec vMax (-(4 * (z + 2 * i + v)))
  have hw := clamp_spec zWall (z + z / 64 + i / 16 + 0)
  simp only [recoverable, xi, step, plant, control, if_true] at h hbig ⊢
  generalize clamp vMax (-(4 * (z + 2 * i + v))) = vc at hc ⊢
  generalize clamp zWall (z + z / 64 + i / 16 + 0) = z' at hw ⊢
  simp only [vMax, zWall, xiSafe] at h hc hw ⊢
  omega

/-- Once below 16 units, |ξ| stays below 16 units. -/
theorem settled_invariant (s : State) (h : recoverable s)
    (hsmall : (xi s).natAbs < 16) :
    (xi (step true s 0)).natAbs < 16 := by
  obtain ⟨z, i, v⟩ := s
  have hc := clamp_spec vMax (-(4 * (z + 2 * i + v)))
  have hw := clamp_spec zWall (z + z / 64 + i / 16 + 0)
  simp only [recoverable, xi, step, plant, control, if_true] at h hsmall ⊢
  generalize clamp vMax (-(4 * (z + 2 * i + v))) = vc at hc ⊢
  generalize clamp zWall (z + z / 64 + i / 16 + 0) = z' at hw ⊢
  simp only [vMax, zWall, xiSafe] at h hc hw ⊢
  omega

/-- Every state in the region is recovered: left alone, the closed loop
    brings |ξ| below 16 units (2.4·10⁻⁴ cm) in finitely many steps — at
    most |ξ| of them, since |ξ| is an integer that decreases. -/
theorem recovers (s : State) (h : recoverable s) :
    ∃ n, n ≤ (xi s).natAbs ∧ (xi (settle s n)).natAbs < 16 := by
  generalize hm : (xi s).natAbs = m
  induction m using Nat.strongRecOn generalizing s with
  | _ m ih =>
    by_cases hlt : (xi s).natAbs < 16
    · exact ⟨0, Nat.zero_le _, hlt⟩
    · have hbig : 16 ≤ (xi s).natAbs := Nat.le_of_not_lt hlt
      have hdec := recoverable_progress s h hbig
      obtain ⟨n, hn, hfin⟩ :=
        ih _ (by omega) (step true s 0) (recoverable_invariant s h) rfl
      exact ⟨n + 1, by omega, hfin⟩

/-- Beyond |ξ| = 14 + 2⁻⁷ no command within the supply's range helps: |ξ|
    increases under ANY `vc` with |vc| ≤ V_max.  (Other states in the ranges
    of `recoverable`, so the wall clamp is not what stops it.) -/
theorem beyond_is_lost (s : State) (vc : Int)
    (hvc : -vMax ≤ vc ∧ vc ≤ vMax)
    (hi : -524416 ≤ s.i ∧ s.i ≤ 524416) (hv : -vMax ≤ s.v ∧ s.v ≤ vMax)
    (hz : -2621440 ≤ s.z ∧ s.z ≤ 2621440)
    (hxi : 918016 ≤ (xi s).natAbs) :
    (xi s).natAbs < (xi (plant s vc 0)).natAbs := by
  obtain ⟨z, i, v⟩ := s
  have hw := clamp_spec zWall (z + z / 64 + i / 16 + 0)
  simp only [xi, plant] at hi hv hz hxi ⊢
  generalize clamp zWall (z + z / 64 + i / 16 + 0) = z' at hw ⊢
  simp only [vMax, zWall] at hvc hv hw ⊢
  omega

end Sparkle.IP.Plasma.VerticalStab
