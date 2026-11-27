/-
  FFT.RTL — the synthesisable carrier.

  ## Why a third carrier exists

  `instAlgOnSignal` lifts `Zp.add` / `Zp.mul` onto signals with
  `Signal.lift2` and `Signal.map`.  That simulates perfectly and is
  what the equivalence proofs are stated about, but Sparkle's Verilog
  elaborator only recognises a *fixed vocabulary* of lifted operators
  (`+`, `-`, `*`, `&&&`, `>>>`, `Signal.mux`, `Signal.ule`, concat,
  `Signal.map` of a bit-slice …).  A lift of an arbitrary Lean
  function — `Zp.add`, with its conditional subtract — is rejected
  with *"Complex lift … operator not found"*.

  So the modular arithmetic has to be re-expressed **in that
  vocabulary**: conditional subtract becomes an explicit
  `Signal.mux (Signal.ule p s) (s - p) s`, Barrett reduction becomes
  an explicit widen / multiply / shift / subtract chain.

  The point is that *only the carrier changes*.  `ctWith`,
  `fourStepWith`, `butterfly`, the index algebra — none of it is
  touched, because `AlgOn β α` never required `β` to be
  `Signal dom α`.  Here `β = Signal dom (BitVec 16)` while the
  coefficients stay `Zp p w`: the wires carry raw machine words, the
  twiddles are still residues.  That separation is the whole reason
  the class has two parameters instead of one.

  ## Widths

  * carrier `BitVec 16` — holds a residue `< p`, with one bit of
    headroom so `a + b < 2p` does not wrap;
  * `BitVec 48` inside `cmul` — the product is `< p² < 2^28`, and
    Barrett's `x·m` needs another `w+1` bits on top of that.

  Since `p` and the Barrett constant are compile-time literals, every
  multiplier here is constant-coefficient: synthesis folds them into
  shift-add trees rather than instantiating DSP blocks.
-/
import FFT.Algebra
import FFT.Zp
import FFT.CooleyTukey
import FFT.FourStep
import FFT.Unrolled

namespace FFTNTT

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Carrier width: one bit of headroom above `p` so an unreduced sum
    fits. -/
abbrev RtlW : Nat := 16

/-- Internal width for the Barrett chain. -/
abbrev RtlM : Nat := 48

namespace RTL

variable {dom : DomainConfig}

/-- `p` as a carrier-width constant. -/
def pC (p : Nat) : Signal dom (BitVec RtlW) :=
  Signal.pure (BitVec.ofNat RtlW p)

/-- `p` at Barrett width. -/
def pM (p : Nat) : Signal dom (BitVec RtlM) :=
  Signal.pure (BitVec.ofNat RtlM p)

/-- Barrett constant `⌊2^{2w}/p⌋`. -/
def mC (p w : Nat) : Signal dom (BitVec RtlM) :=
  Signal.pure (BitVec.ofNat RtlM (2 ^ (2 * w) / p))

/-- One conditional subtract of `p`, at Barrett width. -/
def condSubM (p : Nat) (x : Signal dom (BitVec RtlM)) :
    Signal dom (BitVec RtlM) :=
  let pv : Signal dom (BitVec RtlM) := pM p
  Signal.mux (Signal.ule pv x) (x - pv) x

/-- Modular add: `a + b` then one conditional subtract.  Correct
    because both operands are already reduced, so the sum is `< 2p`. -/
def addR (p : Nat) (a b : Signal dom (BitVec RtlW)) :
    Signal dom (BitVec RtlW) :=
  let pv : Signal dom (BitVec RtlW) := pC p
  let s := a + b
  Signal.mux (Signal.ule pv s) (s - pv) s

/-- Modular subtract: bias by `p` first so the intermediate never
    borrows, then one conditional subtract. -/
def subR (p : Nat) (a b : Signal dom (BitVec RtlW)) :
    Signal dom (BitVec RtlW) :=
  let pv : Signal dom (BitVec RtlW) := pC p
  let d := a + pv - b
  Signal.mux (Signal.ule pv d) (d - pv) d

/-- Multiply by a compile-time residue, Barrett reduced.

    `q = (x·c·m) >> 2w` under-estimates `x·c/p` by less than 3, so
    three conditional subtracts suffice — the same bound the value-level
    `Zp.mul` relies on, and the tests check the two against each
    other. -/
def mulCR (p w : Nat) (c : BitVec RtlM) (a : Signal dom (BitVec RtlW)) :
    Signal dom (BitVec RtlW) :=
  let x : Signal dom (BitVec RtlM) := (0#32 : BitVec 32) ++ a
  let prod := x * (Signal.pure c : Signal dom (BitVec RtlM))
  let mv : Signal dom (BitVec RtlM) := mC p w
  let pv : Signal dom (BitVec RtlM) := pM p
  let q := (prod * mv) >>> (BitVec.ofNat RtlM (2 * w))
  let r0 := prod - q * pv
  let r3 := condSubM p (condSubM p (condSubM p r0))
  Signal.map (fun v => v.extractLsb' 0 RtlW) r3

end RTL

/-- The synthesisable carrier: raw 16-bit wires carrying residues mod
    `p`, with `Zp p w` as the coefficient type.

    Not an `instance` — `p` and `w` cannot be recovered from the
    carrier type, and in any case choosing "RTL vocabulary" over
    "lifted Lean functions" is a deliberate decision at the top of a
    design, not something to leave to instance search. -/
@[reducible] def algOnRtl (p w : Nat) {dom : DomainConfig} :
    AlgOn (Signal dom (BitVec RtlW)) (Zp p w) where
  czero := Signal.pure (BitVec.ofNat RtlW 0)
  cadd  := RTL.addR p
  csub  := RTL.subR p
  cmul  := fun c a => RTL.mulCR p w (BitVec.ofNat RtlM c.val.toNat) a
  creg  := id

/-- The same, with a register between stages. -/
@[reducible] def algOnRtlPipelined (p w : Nat) {dom : DomainConfig} :
    AlgOn (Signal dom (BitVec RtlW)) (Zp p w) where
  czero := Signal.pure (BitVec.ofNat RtlW 0)
  cadd  := RTL.addR p
  csub  := RTL.subR p
  cmul  := fun c a => RTL.mulCR p w (BitVec.ofNat RtlM c.val.toNat) a
  creg  := Signal.register (BitVec.ofNat RtlW 0)

/-! ## Synthesisable tops

    Ordinary Lean functions from signals to signals — what
    `#synthesizeVerilog` consumes.  They call the *unrolled* spellings
    from `FFT/Unrolled.lean`, which `ct8u_eq` / `fs8u_eq` prove are
    definitionally the recursive `ctWith` / `fourStepWith`, so these
    tops are the proved network, not a re-implementation of it. -/

/-- The twiddle ROM as a plain function, so the tops do not carry a
    `FFTRoot` dictionary into the synthesiser. -/
def twZ : Nat → Nat → Z12289 := FFTRoot.twiddle

/-- The constant multiplier used by every top here: `Zp` coefficient in,
    16-bit carrier out. -/
def mulZ {dom : DomainConfig} (c : Z12289) (a : Signal dom (BitVec RtlW)) :
    Signal dom (BitVec RtlW) :=
  RTL.mulCR 12289 14 (BitVec.ofNat RtlM c.val.toNat) a

/-- 4-point NTT over `Z_12289`, combinational. -/
def ntt4 {dom : DomainConfig} (x0 x1 x2 x3 : Signal dom (BitVec RtlW)) :
    Signal dom (BitVec RtlW) × Signal dom (BitVec RtlW) ×
    Signal dom (BitVec RtlW) × Signal dom (BitVec RtlW) :=
  ct4uOps (RTL.addR 12289) (RTL.subR 12289) mulZ id twZ x0 x1 x2 x3

/-- 8-point NTT over `Z_12289`, combinational: one 12-butterfly cone. -/
def ntt8 {dom : DomainConfig}
    (x0 x1 x2 x3 x4 x5 x6 x7 : Signal dom (BitVec RtlW)) :
    Signal dom (BitVec RtlW) × Signal dom (BitVec RtlW) ×
    Signal dom (BitVec RtlW) × Signal dom (BitVec RtlW) ×
    Signal dom (BitVec RtlW) × Signal dom (BitVec RtlW) ×
    Signal dom (BitVec RtlW) × Signal dom (BitVec RtlW) :=
  ct8uOps (RTL.addR 12289) (RTL.subR 12289) mulZ id twZ
    x0 x1 x2 x3 x4 x5 x6 x7

/-- The same 8-point transform as a four-step `2 × 4` decomposition:
    four 2-point column networks, a twiddle array, two 4-point row
    networks. -/
def ntt8fourStep {dom : DomainConfig}
    (x0 x1 x2 x3 x4 x5 x6 x7 : Signal dom (BitVec RtlW)) :
    Signal dom (BitVec RtlW) × Signal dom (BitVec RtlW) ×
    Signal dom (BitVec RtlW) × Signal dom (BitVec RtlW) ×
    Signal dom (BitVec RtlW) × Signal dom (BitVec RtlW) ×
    Signal dom (BitVec RtlW) × Signal dom (BitVec RtlW) :=
  fs8uOps (RTL.addR 12289) (RTL.subR 12289) mulZ id twZ
    x0 x1 x2 x3 x4 x5 x6 x7

/-- 8-point NTT, pipelined: one register per stage, latency 3. -/
def ntt8p {dom : DomainConfig}
    (x0 x1 x2 x3 x4 x5 x6 x7 : Signal dom (BitVec RtlW)) :
    Signal dom (BitVec RtlW) × Signal dom (BitVec RtlW) ×
    Signal dom (BitVec RtlW) × Signal dom (BitVec RtlW) ×
    Signal dom (BitVec RtlW) × Signal dom (BitVec RtlW) ×
    Signal dom (BitVec RtlW) × Signal dom (BitVec RtlW) :=
  ct8uOps (RTL.addR 12289) (RTL.subR 12289) mulZ
    (Signal.register (BitVec.ofNat RtlW 0)) twZ
    x0 x1 x2 x3 x4 x5 x6 x7

end FFTNTT
