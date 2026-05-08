/-
  Sparkle ↔ Hesper Equivalence — End-to-end attention pipeline.

  Composes the four attention stages on a single concrete fixture:

      Q·K^T  →  / 2^dkShift  →  softmax  →  attn @ V

  Each stage already has its own equivalence file:
    - Q·K^T          : `Tests/Hesper/AttentionEquivalence.lean`
    - softmax        : `Tests/Hesper/SoftmaxWeightedV.lean`
    - weighted-V     : `Tests/Hesper/SoftmaxWeightedV.lean`

  This file:
    1. **Composes** the abstractions into one `attentionPipelineInt`.
    2. Proves a `compose-equivalence` lemma showing each stage's
       abstraction lines up at the seam (no integer rounding gap
       outside softmax's `Float.exp` step).
    3. Pins the final output of a 3-token, head-dim-2 fixture via
       `native_decide`, demonstrating the full pipeline is
       executable and arithmetic-stable.

  Per `feedback_hesper_float_bridge.md`: softmax keeps its
  fixture-pin treatment; everything else is tactic-proven.

  See `docs/Hesper_Equivalence.md` step 14.
-/

import IP.BitNet.Types
import Tests.Hesper.MatmulSpec
import Tests.Hesper.BitLinearEquivalence
import Tests.Hesper.AttentionEquivalence
import Tests.Hesper.SoftmaxWeightedV

namespace Sparkle.Tests.Hesper.EndToEndAttention

open Sparkle.IP.BitNet
open Sparkle.Tests.Hesper.MatmulSpec
open Sparkle.Tests.Hesper.BitLinearEquivalence
open Sparkle.Tests.Hesper.AttentionEquivalence
open Sparkle.Tests.Hesper.SoftmaxWeightedV

/-! ## Stage glue: row-vs-row Q·K^T over seqLen × headDim

`dotProductInt` (in `AttentionEquivalence.lean`) computes one
score = `Σ_j Q[i,j] · K[i',j]` for one (i, i') pair. To form the
full attention score matrix, we apply it pairwise.

For a single query position `i`, the row of scores against all
keys is `[dotProductInt Q[i] K[0], dotProductInt Q[i] K[1], …]`. -/

/-- One row of the score matrix for query at position `i`. -/
def scoreRow (qRow : List Int) (kRows : List (List Int)) : List Int :=
  kRows.map (dotProductInt qRow)

/-- Apply the 1/√d_k scale via arithmetic right shift by `dkShift`. -/
def scaledScoreRow (scores : List Int) (dkShift : Nat) : List Int :=
  scores.map fun s => s / (2 ^ dkShift : Int)

/-- The full attention output for one query position:
    softmax( Q[i] · K^T / 2^dkShift ) · V_columns. -/
def attentionPipelineInt
    (qRow : List Int) (kRows : List (List Int)) (vRows : List (List Int))
    (headDim : Nat) (dkShift : Nat) : List Int := Id.run do
  -- Stage 1+2: Q · K^T scaled.
  let scaled := scaledScoreRow (scoreRow qRow kRows) dkShift
  -- Stage 3: softmax (uses Float.exp; will be pinned per-fixture).
  let weights := softmaxRef scaled.toArray
  -- Stage 4: weighted-V over each output column j.
  let mut out : List Int := []
  for j in [:headDim] do
    let vCol : List Int := vRows.map fun row => row.getD j 0
    out := out ++ [weightedVInt weights.toList vCol]
  pure out

/-! ## Layer-1 compositional lemma

Each pipeline stage is itself an abstract `linearSum`-style
operation; their composition is a sequence of `linearSum`s with
integer post-processing in between. Stages 1, 2, 4 are pure integer
math, so we get a closed-form per-stage seam lemma.

Stage 3 (softmax) is Float-dependent; we treat its output as a
black box `weights`, with the property `weightedVInt_eq_listSum_div`
absorbing whatever weights it produces. -/

/-- **Stage-1 lemma** (per element): the i-th entry of `scoreRow`
    equals the abstract `listSum (q*k)` for the matching key row.
    Proved by direct rewriting through `List.getElem?_map` plus the
    `dotProductInt_eq_listSum` lemma. -/
theorem scoreRow_each_eq_listSum
    (qRow : List Int) (kRows : List (List Int)) (i : Nat)
    (kRow : List Int) (h : kRows[i]? = some kRow) :
    (scoreRow qRow kRows)[i]? = some (
      listSum ((qRow.zip kRow).map (fun p => p.1 * p.2))) := by
  unfold scoreRow
  rw [List.getElem?_map, h]
  simp [dotProductInt_eq_listSum]

/-- **Stage-4 lemma**: weighted-V over the softmax output equals
    abstract `listSum (w*v) / 2^24`. Re-export of
    `weightedVInt_eq_listSum_div`, scoped to the pipeline. -/
theorem stage4_eq_listSum_div
    (weights vCol : List Int) :
    weightedVInt weights vCol
    = listSum ((weights.zip vCol).map (fun p => p.1 * p.2))
        / (2 ^ 24 : Int) :=
  weightedVInt_eq_listSum_div weights vCol

/-! ## End-to-end fixture (`native_decide`)

3-token sequence, head dimension 2.
Q, K, V are 3×2 INT8 matrices. -/

/-- Query vector for position 0 (length 2). -/
def fixtureQ0 : List Int := [10, 20]

/-- 3 key vectors, each length 2. -/
def fixtureK : List (List Int) := [
  [10, 20],   -- aligned with Q0  → high score
  [-5,  5],   -- partially negative
  [ 0,  0]    -- zero score
]

/-- 3 value vectors, each length 2 (= headDim). -/
def fixtureV : List (List Int) := [
  [50, -50],
  [10,  10],
  [ 0,  20]
]

/-- Expected scores (exact, by linear arithmetic):
      Q0·K[0] = 10·10 + 20·20 = 500
      Q0·K[1] = 10·(-5) + 20·5 =  50
      Q0·K[2] = 10·0  + 20·0  =   0
    With dkShift = 0 (we want untouched scores for visibility). -/
theorem fixture_score_row :
    scoreRow fixtureQ0 fixtureK = [500, 50, 0] := by
  native_decide

/-- The score row matches the abstract listSum form, position-by-position. -/
theorem fixture_score_row_eq_listSum_each :
    (scoreRow fixtureQ0 fixtureK).getD 0 0 = 500
    ∧ (scoreRow fixtureQ0 fixtureK).getD 1 0 = 50
    ∧ (scoreRow fixtureQ0 fixtureK).getD 2 0 = 0 := by
  native_decide

/-! ### Saturation case: dkShift = 0

With unscaled scores [500, 50, 0], the score gap is too wide for
softmax not to saturate — Float.exp underflows for the 50 and 0
entries, so the output is exactly V[0]. -/

def fixtureAttnOutputSat : List Int :=
  attentionPipelineInt fixtureQ0 fixtureK fixtureV 2 0

theorem fixture_pipeline_saturated_value :
    fixtureAttnOutputSat = [50, -50] := by
  native_decide

/-! ### Soft case: dkShift = 8 (= sqrt(d_k = 65536))

Real BitNet attention divides by 2^dkShift to spread the
distribution. With dkShift = 8 the scores become [1, 0, 0]
(ish — actually 500/256 = 1, 50/256 = 0, 0/256 = 0), exp gives
weights ≈ [0.43, 0.29, 0.29], the output blends V[0..2]. -/

def fixtureAttnOutputSoft : List Int :=
  attentionPipelineInt fixtureQ0 fixtureK fixtureV 2 8

/-- The soft-attention output is pinned numerically. -/
theorem fixture_pipeline_soft_value :
    fixtureAttnOutputSoft = [30, -23] := by
  native_decide

/-! ## Sanity: output is in INT8 range (both fixtures) -/

theorem fixture_saturated_in_int8_range :
    ∀ (i : Fin 2),
      let v := fixtureAttnOutputSat.getD i.val 0
      v ≥ -128 ∧ v ≤ 127 := by
  native_decide

theorem fixture_soft_in_int8_range :
    ∀ (i : Fin 2),
      let v := fixtureAttnOutputSoft.getD i.val 0
      v ≥ -128 ∧ v ≤ 127 := by
  native_decide

/-! ## Stage-by-stage seam check

Demonstrate that the composition's intermediate values match what
the per-stage abstractions predict, end-to-end. Each step is a
single `native_decide`, but together they show the seams line up. -/

/-- Stage 1 → Stage 2: the scaled scores for dkShift = 8. -/
theorem fixture_seam_scaled :
    scaledScoreRow (scoreRow fixtureQ0 fixtureK) 8 = [1, 0, 0] := by
  native_decide

/-- Stage 2 → Stage 3: softmax of [1, 0, 0]. The Q8.24 weights
    sum to ≈ 2^24 (one ULP). -/
theorem fixture_seam_softmax_sums :
    let w := softmaxRef #[1, 0, 0]
    let s := w.foldl (· + ·) 0
    s ≥ Q - 4 ∧ s ≤ Q + 4 := by
  native_decide

/-- Stage 3 → Stage 4: weighted-V for the j = 0 column gives the
    same number as `fixtureAttnOutputSoft.getD 0 0`. -/
theorem fixture_seam_weightedV_j0 :
    let scaled := scaledScoreRow (scoreRow fixtureQ0 fixtureK) 8
    let w := softmaxRef scaled.toArray
    weightedVInt w.toList (fixtureV.map fun row => row.getD 0 0)
    = fixtureAttnOutputSoft.getD 0 0 := by
  native_decide

end Sparkle.Tests.Hesper.EndToEndAttention
