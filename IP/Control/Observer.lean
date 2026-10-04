/-
  State estimators for the 2-state drone axis — steady-state Kalman, H∞, and a
  time-varying Kalman with the on-chip `DividerQ` gain computation.

  ## The plant

  One axis of a drone (angle + rate), sampled at `dt = 1/16`:

      x₁⁺ = x₁ + dt·x₂                 (angle)
      x₂⁺ = x₂ + dt·u + w              (rate; w = gust/process disturbance)
      y   = x₁ + v                     (angle measurement; v = sensor noise)

  ## One circuit, two filters

  `fixedGainObserver` is the predictor-form observer

      x̂₁⁺ = x̂₁ + dt·x̂₂        + k₁·(y − x̂₁)
      x̂₂⁺ = x̂₂ + dt·u         + k₂·(y − x̂₁)

  The **steady-state Kalman filter** and the **H∞ filter** are this same
  circuit with different `(k₁, k₂)` constants:

      Kalman (q = 0.5·dt, r = 0.01):   K = [0.4636, 1.3960]
      H∞     (γ = 1.964 = 1.5·γ_min):  K = [0.4974, 1.5472]

  Both gain pairs were computed offline (Riccati iteration for KF; the H∞
  filtering Riccati with the `P⁻¹ − γ⁻²I + HᵀR⁻¹H ≻ 0` existence check, γ_min
  found by bisection ≈ 1.309).  The RTL difference is *nothing but the two
  constants* — every meaningful difference between "optimal for Gaussian noise"
  and "bounded worst-case amplification" lives in the offline design and in the
  certificates proven in `proofs/SparkleProofs/Control/EstimatorDesign.lean`:

    * both:  the error dynamics `e⁺ = (A−KH)e` contract a quadratic `V`
    * H∞ only: the dissipation inequality
      `V(e⁺) − V(e) ≤ γ²(wᵀQ⁻¹w + vᵀR⁻¹v) − ‖e‖²`, i.e. a machine-checked
      bound on how much disturbance energy can reach the estimate.

  ## The time-varying Kalman (`tvKalman`)

  The full filter also propagates its covariance on-chip and *divides* to get
  the gain each sample — the part that needs `DividerQ`:

      s    = p₁₁ + r
      k₁   = (p₁₁ + dt·p₁₂) / s          ← dividerQ, 50 cycles
      k₂   = p₁₂ / s                     ← dividerQ, 50 cycles
      P⁺   = A P Aᵀ + Q − K·s·Kᵀ         (clamped)

  FSM: IDLE →(tick) DIV1 → DIV2 → UPDATE → IDLE, sharing ONE divider engine
  (the numerator is muxed).  A sample tick needs ≥ ~110 cycles of spacing at
  Q15.16 — at 27 MHz that allows sample rates up to ~240 kHz, far above any
  airframe's needs.  `y`/`u` are latched at the tick, so they may change freely
  between ticks.

  Structural safety, same policy as everything in `IP/Control/`:
    * `p₁₁`, `p₂₂` clamp to `[0, pLim]`, `p₁₂` to `[−pLim, pLim]`  ⇒ the
      denominator `s = p₁₁ + r ≥ r > 0`, so the divider never sees zero;
    * state and gain registers clamp symmetrically.

  The test suite checks that `(k₁, k₂)` converge to the steady-state constants
  above — the on-chip Riccati recursion reproducing the offline design is the
  cross-validation of both.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Control.FixedPointGen
import IP.Control.DividerQ

set_option maxRecDepth 100000

namespace Sparkle.IP.Control.Observer

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Control.FixedPointGen
open Sparkle.IP.Control.DividerQ

variable {dom : DomainConfig}

/-! ### Plant and design constants (Q-format-independent, quantized per format) -/

/-- `dt = 1/16`. -/
def dtQ (w f : Nat) : BitVec w := q w f 1 16

/-- Steady-state Kalman gain (offline Riccati, `q = 0.5·dt`, `r = 0.01`). -/
def kfK1 (w f : Nat) : BitVec w := q w f 4636 10000
def kfK2 (w f : Nat) : BitVec w := q w f 13960 10000

/-- H∞ gain (offline H∞ Riccati at `γ = 1.964`, i.e. 1.5 × γ_min). -/
def hinfK1 (w f : Nat) : BitVec w := q w f 4974 10000
def hinfK2 (w f : Nat) : BitVec w := q w f 15472 10000

/-- Measurement-noise variance `r = 0.01` (also the divider-denominator floor). -/
def rQ (w f : Nat) : BitVec w := q w f 1 100

/-- Process-noise variance per step `q = 0.5·dt = 1/32`. -/
def qwQ (w f : Nat) : BitVec w := q w f 1 32

/-- State/estimate clamp: ±64.0. -/
def xLim (w f : Nat) : BitVec w := q w f 64 1

/-- Covariance clamp: ±16.0 (P entries; diagonal additionally floored at 0). -/
def pLim (w f : Nat) : BitVec w := q w f 16 1

/-! ### Pure reference: fixed-gain observer -/

structure Est (w : Nat) where
  x1 : BitVec w
  x2 : BitVec w
  deriving Repr, DecidableEq

instance (w : Nat) : Inhabited (Est w) := ⟨⟨BitVec.zero w, BitVec.zero w⟩⟩

/-- One fixed-gain observer step (pure). -/
def obsStep (w f : Nat) (k1 k2 : BitVec w) (st : Est w) (y u : BitVec w) : Est w :=
  let lim := xLim w f
  let dt := dtQ w f
  let innov := satAdd w y (-st.x1)
  let x1' := clampSym w lim
    (satAdd w (satAdd w st.x1 (mulQ w f dt st.x2)) (mulQ w f k1 innov))
  let x2' := clampSym w lim
    (satAdd w (satAdd w st.x2 (mulQ w f dt u)) (mulQ w f k2 innov))
  ⟨x1', x2'⟩

/-- Run over a `(y, u)` trace. -/
def obsRun (w f : Nat) (k1 k2 : BitVec w)
    : Est w → List (BitVec w × BitVec w) → List (Est w)
  | _, [] => []
  | st, (y, u) :: rest =>
    let st' := obsStep w f k1 k2 st y u
    st' :: obsRun w f k1 k2 st' rest

/-! ### Pure reference: time-varying Kalman (one whole sample per step)

Uses `divQref` for the gain divisions, `mulQ` for products — exactly the
operations the FSM performs, so the circuit result must match this *bit for
bit* once its FSM completes a sample. -/

structure TVK (w : Nat) where
  x1 : BitVec w
  x2 : BitVec w
  p11 : BitVec w
  p12 : BitVec w
  p22 : BitVec w
  k1 : BitVec w
  k2 : BitVec w
  deriving Repr, DecidableEq

instance (w : Nat) : Inhabited (TVK w) :=
  ⟨⟨BitVec.zero w, BitVec.zero w, BitVec.zero w, BitVec.zero w, BitVec.zero w,
    BitVec.zero w, BitVec.zero w⟩⟩

/-- Clamp a covariance diagonal entry to `[0, pLim]`. -/
def clampDiag (w f : Nat) (x : BitVec w) : BitVec w :=
  let c := clampSym w (pLim w f) x
  if c.toInt < 0 then BitVec.zero w else c

/-- One complete time-varying Kalman sample (pure). -/
def tvkStep (w f : Nat) (st : TVK w) (y u : BitVec w) : TVK w :=
  let dt := dtQ w f
  let r := rQ w f
  let qw := qwQ w f
  let lim := xLim w f
  let plim := pLim w f
  -- gain: s = p11 + r;  k1 = (p11 + dt·p12)/s;  k2 = p12/s
  let s := satAdd w st.p11 r
  let num1 := satAdd w st.p11 (mulQ w f dt st.p12)
  let k1 := divQref w f num1 s
  let k2 := divQref w f st.p12 s
  -- estimate update
  let innov := satAdd w y (-st.x1)
  let x1' := clampSym w lim
    (satAdd w (satAdd w st.x1 (mulQ w f dt st.x2)) (mulQ w f k1 innov))
  let x2' := clampSym w lim
    (satAdd w (satAdd w st.x2 (mulQ w f dt u)) (mulQ w f k2 innov))
  -- covariance update: APAᵀ + Q − K s Kᵀ, clamped
  let dtp12 := mulQ w f dt st.p12
  let dtp22 := mulQ w f dt st.p22
  let apa11 := satAdd w (satAdd w st.p11 (satAdd w dtp12 dtp12)) (mulQ w f dt dtp22)
  let apa12 := satAdd w st.p12 dtp22
  let ks1 := mulQ w f k1 s
  let ks2 := mulQ w f k2 s
  let p11' := clampDiag w f (satAdd w apa11 (-(mulQ w f k1 ks1)))
  let p12' := clampSym w plim (satAdd w apa12 (-(mulQ w f k1 ks2)))
  let p22' := clampDiag w f (satAdd w (satAdd w st.p22 qw) (-(mulQ w f k2 ks2)))
  ⟨x1', x2', p11', p12', p22', k1, k2⟩

/-- Run the pure time-varying Kalman over a `(y, u)` trace. -/
def tvkRun (w f : Nat) : TVK w → List (BitVec w × BitVec w) → List (TVK w)
  | _, [] => []
  | st, (y, u) :: rest =>
    let st' := tvkStep w f st y u
    st' :: tvkRun w f st' rest

/-! ### Circuits -/

/-- Fixed-gain observer.  `k₁, k₂` are `Signal` inputs so the same module body
    serves both filters; the concrete tops below bake them to constants.
    Emits `x̂₁` (the angle estimate — the quantity a downstream controller
    consumes). -/
def fixedGainObserver (w f : Nat)
    (y u k1 k2 : Signal dom (BitVec w)) : Signal dom (BitVec w) :=
  circuit do
    let x1Reg ← Signal.reg (BitVec.zero w)
    let x2Reg ← Signal.reg (BitVec.zero w)

    let x1 := (x1Reg : Signal dom (BitVec w))
    let x2 := (x2Reg : Signal dom (BitVec w))

    let dt := (Signal.pure (dtQ w f) : Signal dom (BitVec w))
    let innov := y - x1
    let x1Next := clampSymC w (xLim w f) (x1 + mulQSig w f dt x2 + mulQSig w f k1 innov)
    let x2Next := clampSymC w (xLim w f) (x2 + mulQSig w f dt u + mulQSig w f k2 innov)

    x1Reg <~ x1Next
    x2Reg <~ x2Next

    return x1

/-- Steady-state Kalman filter at Q15.16 — `fixedGainObserver` with the offline
    Riccati gains. -/
def kalmanQ15_16 (y u : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  fixedGainObserver 32 16 y u
    (Signal.pure (kfK1 32 16)) (Signal.pure (kfK2 32 16))

/-- H∞ filter at Q15.16 — the same circuit, the worst-case gains. -/
def hinfQ15_16 (y u : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  fixedGainObserver 32 16 y u
    (Signal.pure (hinfK1 32 16)) (Signal.pure (hinfK2 32 16))

/-- Time-varying Kalman with the on-chip divider.

    `tick` pulses once per sample (spacing ≥ 2·(w+f)+10 cycles); `y`/`u` are
    latched on the tick.  Emits `x̂₁`.  One `dividerQ` engine is shared between
    the two gain divisions; the numerator is muxed by the FSM phase.

    FSM (3-bit phase):

        0 IDLE   —(tick: latch y,u; start div1 with num₁)→ 1
        1 WAIT1  —(done: latch k₁)→ 2
        2 START2 — one cycle; start div2 with num₂ → 3
        3 WAIT2  —(done: latch k₂)→ 4
        4 UPDATE — one cycle; estimate + covariance writeback → 0

    The dedicated START2 phase exists so the divider's `start` never has to
    reference the divider's own `done` in the same expression — the engine is
    guaranteed idle by the time phase 2 is reached, and the numerator mux is
    stable (`phase = 2`) on the start cycle.  Register file: phase(3) + x̂(2) +
    P(3) + K(2) + latched y,u = 11 registers plus the divider's 6. -/
def tvKalman (w f : Nat)
    (y u : Signal dom (BitVec w)) (tick : Signal dom Bool)
    : Signal dom (BitVec w) :=
  circuit do
    let phaseReg ← Signal.reg (0#3)
    let x1Reg ← Signal.reg (BitVec.zero w)
    let x2Reg ← Signal.reg (BitVec.zero w)
    let p11Reg ← Signal.reg (BitVec.zero w)
    let p12Reg ← Signal.reg (BitVec.zero w)
    let p22Reg ← Signal.reg (BitVec.zero w)
    let k1Reg ← Signal.reg (BitVec.zero w)
    let k2Reg ← Signal.reg (BitVec.zero w)
    let yReg ← Signal.reg (BitVec.zero w)
    let uReg ← Signal.reg (BitVec.zero w)

    let phase := (phaseReg : Signal dom (BitVec 3))
    let x1 := (x1Reg : Signal dom (BitVec w))
    let x2 := (x2Reg : Signal dom (BitVec w))
    let p11 := (p11Reg : Signal dom (BitVec w))
    let p12 := (p12Reg : Signal dom (BitVec w))
    let p22 := (p22Reg : Signal dom (BitVec w))
    let k1 := (k1Reg : Signal dom (BitVec w))
    let k2 := (k2Reg : Signal dom (BitVec w))
    let yL := (yReg : Signal dom (BitVec w))
    let uL := (uReg : Signal dom (BitVec w))

    let dt := (Signal.pure (dtQ w f) : Signal dom (BitVec w))
    let r := (Signal.pure (rQ w f) : Signal dom (BitVec w))
    let qw := (Signal.pure (qwQ w f) : Signal dom (BitVec w))

    let p0 := phase === (Signal.pure 0#3)
    let p1 := phase === (Signal.pure 1#3)
    let p2 := phase === (Signal.pure 2#3)
    let p3 := phase === (Signal.pure 3#3)
    let p4 := phase === (Signal.pure 4#3)

    -- Gain-division operands, combinational off the stable P registers.
    let s := p11 + r
    let num1 := p11 + mulQSig w f dt p12
    let divNum := Signal.mux p2 p12 num1

    -- Shared divider engine (inline, RV32-SoC style: instantiate, project).
    let startDiv := (tick &&& p0) ||| p2
    let engine := dividerQ w f divNum s startDiv
    let divRes := Signal.fst engine
    let divDone := Signal.snd engine

    -- Phase transitions.
    let phaseNext :=
      Signal.mux (tick &&& p0) (Signal.pure 1#3)
        (Signal.mux (divDone &&& p1) (Signal.pure 2#3)
          (Signal.mux p2 (Signal.pure 3#3)
            (Signal.mux (divDone &&& p3) (Signal.pure 4#3)
              (Signal.mux p4 (Signal.pure 0#3) phase))))

    -- Latches.
    let yNext := Signal.mux (tick &&& p0) y yL
    let uNext := Signal.mux (tick &&& p0) u uL
    let k1Next := Signal.mux (divDone &&& p1) divRes k1
    let k2Next := Signal.mux (divDone &&& p3) divRes k2

    -- UPDATE (p4, one cycle): estimate + covariance writeback.
    let innov := yL - x1
    let x1Upd := clampSymC w (xLim w f) (x1 + mulQSig w f dt x2 + mulQSig w f k1 innov)
    let x2Upd := clampSymC w (xLim w f) (x2 + mulQSig w f dt uL + mulQSig w f k2 innov)
    let dtp12 := mulQSig w f dt p12
    let dtp22 := mulQSig w f dt p22
    let apa11 := p11 + dtp12 + dtp12 + mulQSig w f dt dtp22
    let apa12 := p12 + dtp22
    let ks1 := mulQSig w f k1 s
    let ks2 := mulQSig w f k2 s
    let zeroS := (Signal.pure (BitVec.zero w) : Signal dom (BitVec w))
    -- diagonal entries: clampSym, then floor at zero via the sign bit
    let p11Raw := clampSymC w (pLim w f) (apa11 - mulQSig w f k1 ks1)
    let p11Neg := (p11Raw.map (BitVec.extractLsb' (w - 1) 1 ·)) === (Signal.pure 1#1)
    let p11Upd := Signal.mux p11Neg zeroS p11Raw
    let p12Upd := clampSymC w (pLim w f) (apa12 - mulQSig w f k1 ks2)
    let p22Raw := clampSymC w (pLim w f) (p22 + qw - mulQSig w f k2 ks2)
    let p22Neg := (p22Raw.map (BitVec.extractLsb' (w - 1) 1 ·)) === (Signal.pure 1#1)
    let p22Upd := Signal.mux p22Neg zeroS p22Raw

    let x1Next := Signal.mux p4 x1Upd x1
    let x2Next := Signal.mux p4 x2Upd x2
    let p11Next := Signal.mux p4 p11Upd p11
    let p12Next := Signal.mux p4 p12Upd p12
    let p22Next := Signal.mux p4 p22Upd p22

    phaseReg <~ phaseNext
    x1Reg <~ x1Next
    x2Reg <~ x2Next
    p11Reg <~ p11Next
    p12Reg <~ p12Next
    p22Reg <~ p22Next
    k1Reg <~ k1Next
    k2Reg <~ k2Next
    yReg <~ yNext
    uReg <~ uNext

    return x1

end Sparkle.IP.Control.Observer
