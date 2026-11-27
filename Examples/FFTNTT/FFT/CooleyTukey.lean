/-
  FFT.CooleyTukey — the radix-2 butterfly network.

  ## Shape

  Decimation-in-time, expressed *structurally* rather than in place:

      X[k]       = E[k] + ω_N^k · O[k]
      X[k + N/2] = E[k] − ω_N^k · O[k]        for k < N/2

  where `E` is the transform of the even-indexed samples and `O` that
  of the odd-indexed ones.  Splitting by recursion instead of
  pre-permuting is what makes this version take natural-order input
  *and* produce natural-order output: the bit-reversal that the
  classic in-place loop needs is exactly the price of flattening this
  recursion into an array.  `bitrev` below is provided for people who
  want that flattened form anyway.

  ## Cost

  `N = 2^m`.  Fully unrolled: `(N/2)·m` butterflies, so `(N/2)·m`
  constant multipliers, `N·m` adders.  Every twiddle is a literal, so
  the multipliers are constant-coefficient — for the NTT instance that
  means a shift-add tree per butterfly, not a general modular
  multiplier.

  ## The two carriers

  `ct` is written once against `AlgOn`.  Instantiated at `β := α` it is
  the reference model; at `β := Signal dom α` it is a combinational
  cone; at the same type but with `algOnSignalPipelined` it grows one
  register per stage and a latency of `m` cycles.  `ctPipelined` picks
  the last of those explicitly.
-/
import FFT.Algebra
import FFT.Spec

namespace FFTNTT

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Index helpers -/

section Idx
variable {m : Nat}

theorem two_pow_succ (m : Nat) : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by
  rw [Nat.pow_succ]; omega

/-- `2i` as an index into a vector of twice the length. -/
@[inline] def evenIdx (i : Fin (2 ^ m)) : Fin (2 ^ (m + 1)) :=
  ⟨2 * i.val, by have h := i.isLt; have e := two_pow_succ m; omega⟩

/-- `2i + 1` as an index into a vector of twice the length. -/
@[inline] def oddIdx (i : Fin (2 ^ m)) : Fin (2 ^ (m + 1)) :=
  ⟨2 * i.val + 1, by have h := i.isLt; have e := two_pow_succ m; omega⟩

/-- Fold an index of the full transform into the half it addresses. -/
@[inline] def halfIdx (k : Fin (2 ^ (m + 1))) : Fin (2 ^ m) :=
  ⟨if k.val < 2 ^ m then k.val else k.val - 2 ^ m, by
    have h := k.isLt; have e := two_pow_succ m
    by_cases hk : k.val < 2 ^ m <;> simp [hk] <;> omega⟩

end Idx

/-! ## The network -/

variable {β α : Type} [AlgOn β α]

/-- Radix-2 decimation-in-time transform on `2^m` points,
    parameterised by the twiddle family so that the forward and
    inverse networks are literally the same hardware with a different
    ROM.

    `creg` is applied to each sub-transform's output, so with the
    pipelined carrier every recursion level becomes a pipeline stage
    (latency `m`, throughput one transform per cycle) and with the
    combinational carrier it disappears. -/
def ctWith (tw : Nat → Nat → α) : (m : Nat) → HVec β (2 ^ m) → HVec β (2 ^ m)
  | 0,     x => x
  | m + 1, x =>
    let E : HVec β (2 ^ m) := HVec.map creg (ctWith tw m (HVec.comap evenIdx x))
    let O : HVec β (2 ^ m) := HVec.map creg (ctWith tw m (HVec.comap oddIdx  x))
    fun k =>
      let j := halfIdx k
      let t := cmul (tw (2 ^ (m + 1)) j.val) (O j)
      if k.val < 2 ^ m then cadd (E j) t else csub (E j) t

/-- Forward radix-2 FFT / NTT on `2^m` points. -/
@[inline] def ct [FFTRoot α] (m : Nat) (x : HVec β (2 ^ m)) : HVec β (2 ^ m) :=
  ctWith FFTRoot.twiddle m x

/-- Unnormalised inverse transform: the same network driven from the
    conjugate/inverse twiddle ROM. -/
@[inline] def ictRaw [FFTRoot α] (m : Nat) (x : HVec β (2 ^ m)) : HVec β (2 ^ m) :=
  ctWith FFTRoot.invTwiddle m x

/-- Inverse transform, normalised by `1/N`.  One extra constant
    multiplier per output; for the NTT this is `N⁻¹ mod p`, for the
    fixed-point instance it is an arithmetic right shift by `m`. -/
@[inline] def ict [FFTRoot α] (m : Nat) (x : HVec β (2 ^ m)) : HVec β (2 ^ m) :=
  HVec.map (cmul (FFTRoot.scaleInv (2 ^ m) (FFTAlg.one : α))) (ictRaw m x)

/-! ## Pipelined instantiation -/

/-- The same network with a register between every stage.

    Written as an explicit instance application rather than an
    `instance`, because `instAlgOnSignal` and `algOnSignalPipelined`
    inhabit the same type and the choice between "one big cone of
    logic" and "one stage per cycle" is a design decision, not
    something to leave to instance search. -/
@[inline] def ctPipelined (α : Type) [FFTRoot α] {dom : DomainConfig}
    (m : Nat) (x : HVec (Signal dom α) (2 ^ m)) : HVec (Signal dom α) (2 ^ m) :=
  @ctWith (Signal dom α) α (algOnSignalPipelined α) FFTRoot.twiddle m x

/-- Latency of `ctPipelined` in clock cycles: one per radix-2 stage. -/
@[inline] def ctPipelinedLatency (m : Nat) : Nat := m

/-! ## Bit reversal

    Not needed by `ctWith` — it decimates structurally.  Provided
    because the flattened in-place form of the same algorithm needs
    it, and because it is the permutation that relates the two. -/

/-- Reverse the low `m` bits of `i`: bit `b` moves to bit `m−1−b`. -/
def bitrevNat : Nat → Nat → Nat
  | 0,     _ => 0
  | m + 1, i => bitrevNat m (i / 2) + (i % 2) * 2 ^ m

theorem bitrevNat_lt (m i : Nat) : bitrevNat m i < 2 ^ m := by
  induction m generalizing i with
  | zero => simp [bitrevNat]
  | succ n ih =>
    have h1 := ih (i / 2)
    have h2 : i % 2 < 2 := Nat.mod_lt _ (by omega)
    have e := two_pow_succ n
    have hh : i % 2 = 0 ∨ i % 2 = 1 := by omega
    have hb : (i % 2) * 2 ^ n ≤ 2 ^ n := by
      cases hh with
      | inl h => simp [h]
      | inr h => simp [h]
    simp only [bitrevNat]
    omega

/-- Bit-reversal permutation on a `2^m`-point vector. -/
@[inline] def bitrev {m : Nat} (x : HVec β (2 ^ m)) : HVec β (2 ^ m) :=
  fun i => x ⟨bitrevNat m i.val, bitrevNat_lt m i.val⟩

end FFTNTT
