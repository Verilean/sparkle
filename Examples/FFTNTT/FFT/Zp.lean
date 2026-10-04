/-
  FFT.Zp — the NTT coefficient ring: ℤ/pℤ realised as a `BitVec`.

  Default parameters: `p = 12289 = 3·2^12 + 1`, `w = 14`.  This is the
  NewHope / Kyber-family prime; `2^12 ∣ p−1`, so a primitive `n`-th
  root of unity exists for every power of two `n ≤ 4096`.

  ## Why this instance is the good first target

  Every operation is *exact*: there is no rounding, no overflow
  headroom to reason about, and no `Float` anywhere.  So the reference
  model and the circuit compute literally the same value, which makes
  the bit-exactness obligation `decide`-shaped rather than an error
  analysis.  The complex fixed-point instance in `FFT/Fixed.lean`
  reuses the *same* butterfly network but trades that exactness for a
  rounding model.

  ## Multiplication

  Schoolbook multiply followed by Barrett reduction:

      x  = a·b                       (< p² < 2^{2w})
      q  = (x · m) >> 2w             m = ⌊2^{2w}/p⌋
      r  = x − q·p                   (r < 3p)
      r := r − p  if r ≥ p           (×2, unrolled)

  Two constant-width multipliers and three conditional subtracts —
  all of it constant-folded logic when the multiplicand is a twiddle.
-/
import FFT.Algebra

namespace FFTNTT

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Modular exponentiation (elaboration-time only) -/

/-- Binary modular exponentiation with an explicit fuel bound.

    Only ever evaluated on literal arguments while building a twiddle
    constant, so the fuel (64 halvings, i.e. exponents below `2^64`)
    costs nothing at run time and keeps the definition structurally
    recursive. -/
def powModAux (m : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0,      _, _, acc => acc
  | _+1,    _, 0, acc => acc
  | fuel+1, b, e, acc =>
      powModAux m fuel (b * b % m) (e / 2) (if e % 2 == 1 then acc * b % m else acc)

/-- `powMod b e m = b^e mod m`. -/
def powMod (b e m : Nat) : Nat := powModAux m 64 (b % m) e (1 % m)

/-- `invMod a p = a^(p−2) mod p`, the inverse by Fermat's little
    theorem.  Valid because `p` is prime and `a ≢ 0`. -/
def invMod (a p : Nat) : Nat := powMod a (p - 2) p

/-! ## The ring -/

/-- Residues mod `p`, carried in a `w`-bit word.

    `p` and `w` are type parameters rather than fields so that
    `FFTAlg (Zp p w)` resolves by inference and the reduction
    constants are literals at every use site. -/
structure Zp (p : Nat) (w : Nat) where
  val : BitVec w
  deriving Repr, DecidableEq, Inhabited, BEq

namespace Zp

variable {p w : Nat}

@[inline] def ofNat (p w : Nat) (n : Nat) : Zp p w := ⟨BitVec.ofNat w (n % p)⟩

@[inline] def toNat (a : Zp p w) : Nat := a.val.toNat

/-- Conditional-subtract adder: `a + b` is below `2p`, so one
    comparison suffices.  Computed one bit wide to catch the carry. -/
@[inline] def add (a b : Zp p w) : Zp p w :=
  let pw : BitVec (w + 1) := BitVec.ofNat (w + 1) p
  let s  : BitVec (w + 1) := a.val.setWidth (w + 1) + b.val.setWidth (w + 1)
  ⟨(if BitVec.ule pw s then s - pw else s).setWidth w⟩

/-- Conditional-add subtractor: borrow out of the `w+1`-bit subtract
    marks the wrap, and adding `p` back fixes it. -/
@[inline] def sub (a b : Zp p w) : Zp p w :=
  let pw : BitVec (w + 1) := BitVec.ofNat (w + 1) p
  let d  : BitVec (w + 1) := a.val.setWidth (w + 1) + pw - b.val.setWidth (w + 1)
  ⟨(if BitVec.ule pw d then d - pw else d).setWidth w⟩

/-- Barrett-reduced modular multiply.  All intermediates live in
    `4w` bits: `x < 2^{2w}` and `x·m < 2^{2w}·2^{w+1}`, so `4w` is
    comfortable for any `w ≥ 2`. -/
@[inline] def mul (a b : Zp p w) : Zp p w :=
  let W := 4 * w
  let pv : BitVec W := BitVec.ofNat W p
  let mv : BitVec W := BitVec.ofNat W (2 ^ (2 * w) / p)
  let x  : BitVec W := a.val.setWidth W * b.val.setWidth W
  let q  : BitVec W := (x * mv) >>> (2 * w)
  let r0 : BitVec W := x - q * pv
  let r1 : BitVec W := if BitVec.ule pv r0 then r0 - pv else r0
  let r2 : BitVec W := if BitVec.ule pv r1 then r1 - pv else r1
  let r3 : BitVec W := if BitVec.ule pv r2 then r2 - pv else r2
  ⟨r3.setWidth w⟩

/-- The mathematical specification of `mul`, used as the reference in
    the bit-exactness tests. -/
@[inline] def mulSpec (a b : Zp p w) : Zp p w :=
  ⟨BitVec.ofNat w (a.val.toNat * b.val.toNat % p)⟩

end Zp

/-- Parameters that make `Zp p w` an NTT ring: a primitive root `g`
    of the multiplicative group, from which every `ω_n` is derived as
    `g^((p−1)/n)`.

    The consistency law `FFTRoot` asks for — `ω_{n·m}^m = ω_n` — holds
    by construction here: `(g^{(p−1)/(nm)})^m = g^{(p−1)/n}` whenever
    `nm ∣ p−1`.  That is exactly what makes the four-step
    decomposition valid over this ring. -/
class NTTParams (p : Nat) (w : Nat) where
  /-- A primitive root modulo `p`. -/
  gen : Nat

/-- `p = 12289`, `w = 14`, primitive root `11`.  Supports every
    power-of-two transform size up to 4096. -/
instance : NTTParams 12289 14 := ⟨11⟩

/-- The default NTT coefficient type used by the tests and the
    generated Verilog. -/
abbrev Z12289 : Type := Zp 12289 14

instance instFFTAlgZp (p w : Nat) : FFTAlg (Zp p w) where
  zero := Zp.ofNat p w 0
  one  := Zp.ofNat p w 1
  add  := Zp.add
  sub  := Zp.sub
  mul  := Zp.mul

instance instFFTRootZp (p w : Nat) [NTTParams p w] : FFTRoot (Zp p w) where
  twiddle n k :=
    Zp.ofNat p w (powMod (powMod (NTTParams.gen p w) ((p - 1) / n) p) k p)
  invTwiddle n k :=
    Zp.ofNat p w (powMod (invMod (powMod (NTTParams.gen p w) ((p - 1) / n) p) p) k p)
  scaleInv n a := Zp.mul ⟨BitVec.ofNat w (invMod (n % p) p)⟩ a

/-! ## Hardware wiring -/

instance (p w : Nat) : Sparkle.Core.Wireable (Zp p w) := ⟨w⟩

instance (p w : Nat) : Sparkle.Data.BitPack.BitPack (Zp p w) w where
  toBitVec a   := a.val
  fromBitVec b := ⟨b⟩

end FFTNTT
