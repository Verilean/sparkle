/-
  Fixed-point arithmetic for control datapaths — Q(I.F) signed, `BitVec w`.

  This is the *implementation* side.  It is deliberately Mathlib-free: it is
  plain integer arithmetic on `BitVec`, exactly what the Verilog backend lowers,
  and it is what every theorem in `IP/Control/Proof/` talks about.

  ## Interpretation

  A `BitVec w` holding `x` denotes the rational `x.toInt / 2^F`.  The scale `F`
  is carried as an explicit `Nat` parameter on the operations rather than in the
  type — the house style elsewhere in the repo (`IP/BitNet/Types.lean`) keeps it
  in comments only, which has already produced two wrong theorem statements in
  `IP/BitNet/Spec/FixedPoint.lean`; naming it as an argument is the cheap fix.

  ## Why arithmetic-shift-right and not division

  `BitVec.sshiftRight k` and `Int./ 2^k` are **the same function** in Lean 4:
  both floor.  (Lean's `Int./` is `Int.div` = floor for the `Int` instance;
  the truncating one is `Int.tdiv`.  Checked: `(-7 : Int) / 2 = -4`,
  `((-7#8).sshiftRight 1).toInt = -4`.)  That coincidence is load-bearing —
  it means the rounding in the RTL is *exactly* the floor in the spec, so the
  quantization error of one scaling step is confined to `(-1, 0]` in units of
  `2^-F` and never depends on the sign of the operand.  A truncating shifter
  would make the error sign-dependent and the ultimate-bound argument messier.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.Control.FixedPoint

open Sparkle.Core.Domain
open Sparkle.Core.Signal

variable {dom : DomainConfig}

/-- Fractional bits used by every control datapath in this directory.
    Q15.16 in a `BitVec 32`: range ±32768, resolution 2^-16 ≈ 1.5e-5. -/
def fracBits : Nat := 16

/-- Total datapath width. -/
def totalBits : Nat := 32

/-- One in Q15.16. -/
def one : BitVec 32 := BitVec.ofNat 32 (2 ^ 16)

/-- Interpretation of a Q15.16 word as a numerator over `2^16`.
    Kept as `Int` (not `Rat`) so the whole implementation side stays decidable. -/
def toNum (x : BitVec 32) : Int := x.toInt

/-! ### Pure (`Int`/`BitVec`) reference semantics

These are the functions the proofs reason about.  Each has a `Signal`
counterpart below that lowers to Verilog; the `Proof/` directory ties the two
together via `Sparkle.Verification.LoopProps.loop_iterate`. -/

/-- Signed widening Q15.16 multiply: `(a * b) >> 16`, computed in 64 bits so the
    product cannot wrap, then narrowed.

    This is the *correct* version of the multiply that
    `IP/Drone/StateEstimator.lean : fixMul`,
    `IP/Humanoid/ZMPBalance.lean : fmul` and
    `IP/Humanoid/InverseKinematics.lean : fxMul` all get wrong: those write
    `a ++ 0#32` intending a zero-extension, but `++` puts `a` in the *high*
    half, so the product is `a*b*2^64 ≡ 0 (mod 2^64)` and the functions return
    `0` for every input. -/
def mulQ (a b : BitVec 32) : BitVec 32 :=
  BitVec.extractLsb' 16 32 ((a.signExtend 64) * (b.signExtend 64))

/-- Saturating signed add on `BitVec 32`, computed in 33 bits so the sum cannot
    wrap before it is clamped. -/
def satAdd (a b : BitVec 32) : BitVec 32 :=
  let s : BitVec 33 := (a.signExtend 33) + (b.signExtend 33)
  let hi : BitVec 33 := BitVec.ofInt 33 (2 ^ 31 - 1)
  let lo : BitVec 33 := BitVec.ofInt 33 (-(2 ^ 31))
  if BitVec.slt hi s then BitVec.ofInt 32 (2 ^ 31 - 1)
  else if BitVec.slt s lo then BitVec.ofInt 32 (-(2 ^ 31))
  else BitVec.extractLsb' 0 32 s

/-- Clamp to a symmetric range `[-lim, lim]`.  `lim` is expected non-negative;
    the definition is total regardless. -/
def clampSym (lim x : BitVec 32) : BitVec 32 :=
  let negLim := -lim
  if BitVec.slt lim x then lim
  else if BitVec.slt x negLim then negLim
  else x

/-! ### Signal (synthesizable) counterparts -/

/-- Sign-extend a 32-bit signal to 64 bits.

    Written as an explicit MSB test + `mux` of the high word rather than
    `Signal.map (·.signExtend 64)`, because the synthesis elaborator only lowers
    a `.map` lambda that is a single `extractLsb'` or a constant-prefix `append`
    — `signExtend` is neither.  Same shape as
    `IP/YOLOv8/Primitives/Requantize.lean : mulAccScale`, which is
    `#synthesizeVerilog`-verified. -/
def sext32to64 (a : Signal dom (BitVec 32)) : Signal dom (BitVec 64) :=
  let isNeg := a.map (BitVec.extractLsb' 31 1 ·) === (Signal.pure 1#1)
  let ones : Signal dom (BitVec 32) := Signal.pure (BitVec.ofNat 32 0xFFFFFFFF)
  let zeros : Signal dom (BitVec 32) := Signal.pure 0#32
  (Signal.mux isNeg ones zeros) ++ a

/-- Signal-level Q15.16 multiply.  Mirrors `mulQ`. -/
def mulQSig (a b : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  (sext32to64 a * sext32to64 b).map (BitVec.extractLsb' 16 32 ·)

/-- Signal-level symmetric clamp.  Mirrors `clampSym`. -/
def clampSymSig (lim x : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let negLim := (Signal.pure 0#32 : Signal dom (BitVec 32)) - lim
  let tooHigh := Signal.slt lim x
  let tooLow := Signal.slt x negLim
  Signal.mux tooHigh lim (Signal.mux tooLow negLim x)

/-- Clamp to a *constant* symmetric range.  Preferred inside `circuit do`: a
    constant bound keeps the emitted comparator a compare-against-literal and,
    more importantly, makes the ultimate-bound theorem a closed statement. -/
def clampSymC (lim : BitVec 32) (x : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let hi : Signal dom (BitVec 32) := Signal.pure lim
  let lo : Signal dom (BitVec 32) := Signal.pure (-lim)
  Signal.mux (Signal.slt hi x) hi (Signal.mux (Signal.slt x lo) lo x)

end Sparkle.IP.Control.FixedPoint
