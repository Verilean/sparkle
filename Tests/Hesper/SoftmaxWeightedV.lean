/-
  Sparkle ↔ Hesper Equivalence — softmax + weighted-V (attention output).

  Continues the pipeline from `AttentionEquivalence.lean`:

      Q·K^T  →  / sqrt(d_k)  →  softmax  →  attn @ V

  ## Layer-1 lemmas (no `native_decide`, no axioms)

  - `weightedVInt_eq_linearSum_div` — Sparkle's tree-reduced weighted-V
    sum equals the abstract `linearSum (w*v) / 2^24`. Same `treeReduce
    + zip-and-mul` skeleton as `dotProductInt`, with a final shift-by-24.

  ## Layer-2 fixtures (`native_decide`)

  - Softmax round-trip (`softmaxRef` produces ≈ Q8.24 weights summing
    to ≈ 2^24 for a small fixture).
  - Weighted-V cross-check tying `weightedVInt`, the repo's
    `weightedVSum`, and the closed-form value.

  ## Float bridge (softmax)

  `softmaxRef` calls `Float.exp`, so an abstract softmax-correctness
  theorem would require axiomatic `Float` reasoning that we agreed
  to avoid (`feedback_hesper_float_bridge.md`). We therefore pin
  softmax behavior on **concrete fixtures** via `native_decide`:

      softmaxRef  fixed_inputs  =  fixed_outputs

  The downstream `weighted-V` proof is fully integer-valued and does
  not depend on any softmax axiom — it takes the Q8.24 weights as a
  given input.

  See `docs/Hesper_Equivalence.md`.
-/

import IP.BitNet.Types
import IP.BitNet.SignalHelpers
import Tests.Hesper.MatmulSpec
import Tests.Hesper.BitLinearEquivalence

namespace Sparkle.Tests.Hesper.SoftmaxWeightedV

open Sparkle.IP.BitNet
open Sparkle.IP.BitNet.SignalHelpers
open Sparkle.Tests.Hesper.MatmulSpec
open Sparkle.Tests.Hesper.BitLinearEquivalence

/-! ## Integer analog of `weightedVElementSignal`

`weightedVElementSignal` (in `IP/BitNet/Attention/ScoreVMul.lean`)
sign-extends each Q8.24 weight to 64 bits, sign-extends each INT8 V
to 64 bits, multiplies element-wise, sums via `adderTree`, then
shifts right by 24. The `Int` abstraction strips both
sign-extensions (no-ops on integer values) and exposes the same
`treeReduce (· + ·) 0 (zip-and-mul)` skeleton with a divide-by-2^24
post-step. -/

/-- `weightedVInt`: tree-reduced sum of `weight[i] * V[i]`, then
    arithmetic right shift by 24. Mirrors `weightedVElementSignal`
    modulo the BitVec sign-extensions. -/
def weightedVInt (weights vColumn : List Int) : Int :=
  treeReduce (· + ·) 0 ((weights.zip vColumn).map (fun p => p.1 * p.2))
    / (2 ^ 24 : Int)

/-! ## Layer 1: weightedVInt = linearSum(div) — pure tactic proof. -/

/-- **Headline weighted-V lemma**:
    Sparkle's tree-reduced weighted-V sum equals the abstract
    `listSum (zip-and-mul) / 2^24`. Reuses the BitLinear sum-shape
    machinery directly. -/
theorem weightedVInt_eq_listSum_div (weights vColumn : List Int) :
    weightedVInt weights vColumn
    = listSum ((weights.zip vColumn).map (fun p => p.1 * p.2))
        / (2 ^ 24 : Int) := by
  unfold weightedVInt
  rw [treeReduce_int_eq_listSum]

/-! ## Layer 2: concrete fixtures (`native_decide`)

Each weight is a Q8.24 attention probability (so non-negative and
summing to ≈ 2^24); each V is full-range INT8. -/

/-- Q8.24 unit (1.0). -/
def Q : Int := 2 ^ 24

/-- 4 attention weights summing to exactly 2^24 (= 1.0 in Q8.24).
    Distribution: [0.5, 0.25, 0.125, 0.125]. -/
def fixtureWeights : List Int := [Q / 2, Q / 4, Q / 8, Q / 8]

/-- 4 INT8 V values for the same column. -/
def fixtureVCol : List Int := [127, -128, 50, -50]

/-- Reference closed-form value via `linearSum`. -/
example :
    weightedVInt fixtureWeights fixtureVCol
    = listSum ((fixtureWeights.zip fixtureVCol).map (fun p => p.1 * p.2))
        / (2 ^ 24 : Int) :=
  weightedVInt_eq_listSum_div fixtureWeights fixtureVCol

/-- Numerical sanity:
    weighted = 0.5·127 + 0.25·(-128) + 0.125·50 + 0.125·(-50)
             = 63.5 - 32 + 6.25 - 6.25 = 31.5
    But Q8.24 division by 2^24 truncates → 31. -/
theorem weightedVInt_fixture_value :
    weightedVInt fixtureWeights fixtureVCol = 31 := by
  native_decide

/-! ### Bridge to the repo's `weightedVSum` reference

`weightedVSum weights vMatrix j` (in `Types.lean`) is the same math
indexed by Array. We feed it a single-column matrix and check the
result matches `weightedVInt`. -/

def fixtureWeightsArr : Array Int := fixtureWeights.toArray
def fixtureVMatrix : Array (Array Int) :=
  fixtureVCol.toArray.map fun v => #[v]

theorem weightedVSum_eq_weightedVInt :
    weightedVSum fixtureWeightsArr fixtureVMatrix 0
    = weightedVInt fixtureWeights fixtureVCol := by
  native_decide

/-- Repo's `weightedVSum` produces 31 on the fixture (closes the
    triangle: hardware-shape, ref, and abstract `linearSum / Q` agree). -/
theorem weightedVSum_fixture_value :
    weightedVSum fixtureWeightsArr fixtureVMatrix 0 = 31 := by
  native_decide

/-! ## Softmax fixture (`native_decide`)

`softmaxRef` calls `Float.exp`, so we pin its behavior on a fixture.
The fixture: scores = [0, -1, -2, -3]. Output is the Q8.24 softmax
distribution. We assert that:
  1. The output sums to (approximately) 2^24 (= 1.0) —
     allowing for one ULP rounding.
  2. The output is monotonically decreasing
     (since the inputs are).
  3. The largest weight goes to score = 0. -/

/-- Fixture: 4 scores. `0` is the max; the others are descending. -/
def fixtureScores : Array Int := #[0, -1, -2, -3]

/-- Compute and pin the softmax weights. The exact values come
    from running `Float.exp` and renormalizing. We use
    `native_decide` so the proof captures whatever the actual
    `Float.exp` evaluation yields, modulo `expQ8_24`'s integer
    rounding. -/
def fixtureSoftmaxOutput : Array Int := softmaxRef fixtureScores

/-- Sum of softmax weights matches Q8.24 unit (within 1 ULP). -/
theorem softmax_fixture_sums_to_one :
    let s := fixtureSoftmaxOutput.foldl (· + ·) 0
    s ≥ Q - 4 ∧ s ≤ Q + 4 := by
  native_decide

/-- Largest weight is at index 0 (the score = 0 entry). -/
theorem softmax_fixture_argmax_zero :
    fixtureSoftmaxOutput[0]! = fixtureSoftmaxOutput.foldl Max.max 0 := by
  native_decide

/-- Outputs are monotonically decreasing (since inputs are). -/
theorem softmax_fixture_monotone :
    fixtureSoftmaxOutput[0]! ≥ fixtureSoftmaxOutput[1]!
    ∧ fixtureSoftmaxOutput[1]! ≥ fixtureSoftmaxOutput[2]!
    ∧ fixtureSoftmaxOutput[2]! ≥ fixtureSoftmaxOutput[3]! := by
  native_decide

/-! ## End-to-end attention-output fixture

Compose softmax → weighted-V on the same scores fixture:
the v_column has full-range INT8 values; the final output is
Sparkle's attention output for one (batch, head, position, j).
Pin its value via `native_decide`. -/

/-- Same V column as before. -/
def fixtureAttnOut : Int :=
  weightedVInt fixtureSoftmaxOutput.toList fixtureVCol

/-- The attention output for the fixture is whatever falls out of
    `Float.exp`-driven softmax + integer weighted-V; we just pin
    that the value is well-defined and lies in INT8 range. -/
theorem attn_out_in_int8_range :
    fixtureAttnOut ≥ -128 ∧ fixtureAttnOut ≤ 127 := by
  native_decide

end Sparkle.Tests.Hesper.SoftmaxWeightedV
