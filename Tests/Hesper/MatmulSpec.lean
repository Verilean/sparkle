/-
  Sparkle ↔ Hesper Equivalence — shared abstract matmul spec.

  This is the "ground truth" that both Sparkle's BitLinear datapath
  and Hesper's `forwardRow` are proven to refine. We use `Int` (not
  `Float`, not `BitVec`) so the spec is exact and rounding-free —
  float / fixed-point bridges live in separate files.

  See docs/Hesper_Equivalence.md for the full plan.
-/

namespace Sparkle.Tests.Hesper.MatmulSpec

/-- Linear (left-fold) sum, identical to Hesper's `rangeSum` in
    `Hesper/Proofs/ReductionEquiv.lean`.
    `linearSum n f = f 0 + f 1 + … + f (n-1)`. -/
def linearSum : Nat → (Nat → Int) → Int
  | 0,     _ => 0
  | n + 1, f => linearSum n f + f n

/-- `linearSum` distributes over pointwise addition (mirrors the lemma
    Hesper uses to prove tree- vs. linear-reduction equivalence). -/
theorem linearSum_add (n : Nat) (f g : Nat → Int) :
    linearSum n (fun i => f i + g i) = linearSum n f + linearSum n g := by
  induction n with
  | zero => simp [linearSum]
  | succ n ih =>
    show linearSum n (fun i => f i + g i) + (f n + g n) =
         (linearSum n f + f n) + (linearSum n g + g n)
    rw [ih]; omega

/-- `linearSum` is zero when every summand is zero. -/
theorem linearSum_zero (n : Nat) (f : Nat → Int)
    (h : ∀ i, i < n → f i = 0) :
    linearSum n f = 0 := by
  induction n with
  | zero => simp [linearSum]
  | succ n ih =>
    have hn  : f n = 0 := h n (Nat.lt_succ_self n)
    have hlt : ∀ i, i < n → f i = 0 := fun i hi => h i (Nat.lt_succ_of_lt hi)
    simp [linearSum, ih hlt, hn]

/-- One row of `y = scale * (W · x)` with `Int` activations and
    ternary weights, indexed row-major: `W[i, j] = W.getD (i * inDim + j) 0`.
    Models the math both Sparkle and Hesper claim to compute. -/
def matmulRefRow (W : Array Int) (x : Array Int) (scale : Int)
    (inDim outDim : Nat) (i : Nat) : Int :=
  let _ := outDim
  scale * linearSum inDim (fun j =>
    (W.getD (i * inDim + j) 0) * (x.getD j 0))

/-- Full output: `outDim` rows. -/
def matmulRefAll (W : Array Int) (x : Array Int) (scale : Int)
    (inDim outDim : Nat) : Array Int :=
  (Array.range outDim).map (matmulRefRow W x scale inDim outDim)

/-- 2×2 sanity check: W = [[1, -1], [-1, 1]], x = [3, 5], scale = 1.
    Row 0: 1·3 + (-1)·5 = -2.   Row 1: (-1)·3 + 1·5 = 2. -/
example : matmulRefAll #[1, -1, -1, 1] #[3, 5] 1 2 2 = #[-2, 2] := by
  native_decide

/-- Scale factors out of `matmulRefRow`. -/
theorem matmulRefRow_scale (W : Array Int) (x : Array Int) (s k : Int)
    (inDim outDim i : Nat) :
    matmulRefRow W x (k * s) inDim outDim i
    = k * matmulRefRow W x s inDim outDim i := by
  simp [matmulRefRow, Int.mul_assoc]

end Sparkle.Tests.Hesper.MatmulSpec
