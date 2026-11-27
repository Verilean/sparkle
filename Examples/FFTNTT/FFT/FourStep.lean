/-
  FFT.FourStep — the N = N₁·N₂ decomposition.

  ## The identity

  Index the input column-major and the output row-major:

      n = n₁·N₂ + n₂     (n₁ < N₁, n₂ < N₂)
      k = k₂·N₁ + k₁     (k₁ < N₁, k₂ < N₂)

  Then `ω_N^{nk}` splits into four factors, one of which is `1`:

      ω_N^{n₁N₂·k₂N₁} = ω_N^{N·n₁k₂}   = 1
      ω_N^{n₁N₂·k₁}   = ω_{N₁}^{n₁k₁}
      ω_N^{n₂·k₂N₁}   = ω_{N₂}^{n₂k₂}
      ω_N^{n₂·k₁}                        ← the "twiddle" proper

  leaving

      X[k₂N₁+k₁] = Σ_{n₂} ω_N^{n₂k₁} · (Σ_{n₁} x[n₁N₂+n₂] ω_{N₁}^{n₁k₁}) · ω_{N₂}^{n₂k₂}

  i.e. the four steps: **N₂ column transforms of length N₁**, a
  **pointwise twiddle**, **N₁ row transforms of length N₂**, and a
  **transpose** — here folded into the index arithmetic instead of
  being a separate pass, because in a fully spatial circuit a
  transpose is wiring, not work.

  ## Why it is worth having

  Cooley–Tukey unrolled to `N` points is `(N/2)·log₂N` butterflies in
  one cone; past a few dozen points that is no longer a sensible
  circuit.  The four-step form says: build *one* small transform, use
  it `N₁ + N₂` times, and pay for a twiddle multiplier array in
  between.  On a tiled array the transpose is exactly the inter-tile
  data movement — which is why the edge-shift dataflow and this
  decomposition tend to be designed together.

  The sub-transforms are parameters, not fixed: pass `ct m₁` and
  `ct m₂` for a radix-2^m split, pass `dft` for a reference model, or
  pass `fourStep` again to recurse further.

  ## The requirement on the coefficient ring

  The derivation above needs `ω_{N₁N₂}^{N₂} = ω_{N₁}` and
  `ω_{N₁N₂}^{N₁} = ω_{N₂}`.  That is the consistency law documented on
  `FFTRoot`.  It holds exactly for the `Zp` instance (both sides are
  `g^((p−1)/N₁)`) and up to rounding for the fixed-point instance
  (both sides round the same real number), which is precisely why the
  NTT version of the equivalence theorem is an equality and the
  fixed-point version can only be an error bound.
-/
import FFT.Algebra
import FFT.Spec
import FFT.CooleyTukey

namespace FFTNTT

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Index arithmetic -/

section Idx
variable {n1 n2 : Nat}

/-- A `Fin (n1 * n2)` witnesses that both factors are positive. -/
theorem fs_pos1 (k : Fin (n1 * n2)) : 0 < n1 := by
  cases n1 with
  | zero => have h := k.isLt; simp at h
  | succ n => exact Nat.succ_pos n

theorem fs_pos2 (k : Fin (n1 * n2)) : 0 < n2 := by
  cases n2 with
  | zero => have h := k.isLt; simp at h
  | succ n => exact Nat.succ_pos n

/-- Column-major flattening: row `r`, column `c` of an `n1 × n2`
    matrix lands at `r·n2 + c`. -/
theorem fs_flat_lt (r : Fin n1) (c : Fin n2) : r.val * n2 + c.val < n1 * n2 := by
  have h1 := r.isLt
  have h2 := c.isLt
  calc r.val * n2 + c.val < r.val * n2 + n2 := by omega
    _ = (r.val + 1) * n2 := by simp [Nat.succ_mul]
    _ ≤ n1 * n2 := Nat.mul_le_mul_right n2 (by omega)

theorem fs_mod_lt (k : Fin (n1 * n2)) : k.val % n1 < n1 :=
  Nat.mod_lt _ (fs_pos1 k)

theorem fs_div_lt (k : Fin (n1 * n2)) : k.val / n1 < n2 := by
  have hp := fs_pos1 k
  have h : k.val < n1 * n2 := k.isLt
  have e : n1 * n2 = n2 * n1 := Nat.mul_comm n1 n2
  exact (Nat.div_lt_iff_lt_mul hp).mpr (by omega)

/-- `x[n₁·N₂ + n₂]` as an index. -/
@[inline] def flatIdx (r : Fin n1) (c : Fin n2) : Fin (n1 * n2) :=
  ⟨r.val * n2 + c.val, fs_flat_lt r c⟩

/-- `k₁ = k mod N₁`. -/
@[inline] def outIdx1 (k : Fin (n1 * n2)) : Fin n1 := ⟨k.val % n1, fs_mod_lt k⟩

/-- `k₂ = k div N₁`. -/
@[inline] def outIdx2 (k : Fin (n1 * n2)) : Fin n2 := ⟨k.val / n1, fs_div_lt k⟩

end Idx

/-! ## The decomposition -/

variable {β α : Type} [AlgOn β α]

/-- Four-step transform of length `n1 * n2`, built from a transform of
    length `n1` and one of length `n2`.

    `f1` is instantiated `n2` times (the column transforms) and `f2`
    `n1` times (the row transforms).  In a spatial circuit those are
    `n1 + n2` physical instances; in a folded one they are the same
    instance revisited, with the intermediate matrix living in a
    transpose buffer.

    `creg` sits on the twiddle-multiplier output, so with the
    pipelined carrier the twiddle stage is a register boundary between
    the two transform banks — which is where you want it, since that
    is the deepest logic in the design. -/
def fourStepWith (tw : Nat → Nat → α) (n1 n2 : Nat)
    (f1 : HVec β n1 → HVec β n1)
    (f2 : HVec β n2 → HVec β n2)
    (x : HVec β (n1 * n2)) : HVec β (n1 * n2) :=
  -- Step 1: for each column `c`, an n1-point transform down the column.
  let B : Fin n2 → HVec β n1 := fun c => f1 (fun r => x (flatIdx r c))
  -- Steps 2+3: twiddle by ω_N^{c·k₁}, then an n2-point transform
  -- across the row of results for each k₁.
  let D : Fin n1 → HVec β n2 := fun k1 =>
    f2 (fun c => creg (cmul (tw (n1 * n2) (c.val * k1.val % (n1 * n2))) (B c k1)))
  -- Step 4: transpose on the way out — X[k₂N₁+k₁] = D[k₁][k₂].
  fun k => D (outIdx1 k) (outIdx2 k)

/-- Forward four-step transform. -/
@[inline] def fourStep [FFTRoot α] (n1 n2 : Nat)
    (f1 : HVec β n1 → HVec β n1) (f2 : HVec β n2 → HVec β n2)
    (x : HVec β (n1 * n2)) : HVec β (n1 * n2) :=
  fourStepWith FFTRoot.twiddle n1 n2 f1 f2 x

/-- Inverse four-step transform, unnormalised. -/
@[inline] def ifourStepRaw [FFTRoot α] (n1 n2 : Nat)
    (f1 : HVec β n1 → HVec β n1) (f2 : HVec β n2 → HVec β n2)
    (x : HVec β (n1 * n2)) : HVec β (n1 * n2) :=
  fourStepWith FFTRoot.invTwiddle n1 n2 f1 f2 x

/-! ## Power-of-two instantiation -/

/-- `2^(m1+m2) = 2^m1 * 2^m2`, as an index-set equality. -/
theorem pow_split (m1 m2 : Nat) : 2 ^ (m1 + m2) = 2 ^ m1 * 2 ^ m2 :=
  Nat.pow_add 2 m1 m2

/-- A `2^(m1+m2)`-point transform built as `2^m2` columns of a
    `2^m1`-point Cooley–Tukey network followed by `2^m1` rows of a
    `2^m2`-point one.

    This is the composition the equivalence theorem targets:

        ctFourStep m1 m2  =  ct (m1 + m2)

    same function, radically different circuit — `2^m1 + 2^m2` small
    networks plus a twiddle array, instead of one cone of
    `2^(m1+m2-1)·(m1+m2)` butterflies. -/
@[inline] def ctFourStep [FFTRoot α] (m1 m2 : Nat)
    (x : HVec β (2 ^ (m1 + m2))) : HVec β (2 ^ (m1 + m2)) :=
  let e := pow_split m1 m2
  fun k =>
    fourStep (2 ^ m1) (2 ^ m2) (ct m1) (ct m2)
      (fun i => x (Fin.cast e.symm i)) (Fin.cast e k)

/-- The same, with the reference DFT as both sub-transforms.  Useful
    as an intermediate rung when proving `ctFourStep = ct`: it isolates
    "is the four-step index algebra right" from "is the radix-2
    recursion right". -/
@[inline] def dftFourStep [FFTRoot α] (n1 n2 : Nat)
    (x : HVec β (n1 * n2)) : HVec β (n1 * n2) :=
  fourStep n1 n2 (dft n1) (dft n2) x

/-! ## Pipelined instantiation -/

/-- Four-step network with a register on the twiddle stage and inside
    each sub-transform. -/
@[inline] def ctFourStepPipelined (α : Type) [FFTRoot α] {dom : DomainConfig}
    (m1 m2 : Nat) (x : HVec (Signal dom α) (2 ^ (m1 + m2))) :
    HVec (Signal dom α) (2 ^ (m1 + m2)) :=
  @ctFourStep (Signal dom α) α (algOnSignalPipelined α) _ m1 m2 x

/-- Latency of `ctFourStepPipelined`: `m1` stages of column transform,
    one twiddle stage, `m2` stages of row transform. -/
@[inline] def ctFourStepLatency (m1 m2 : Nat) : Nat := m1 + 1 + m2

end FFTNTT
