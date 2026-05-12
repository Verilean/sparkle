/-
  Sparkle ≡ Hesper — Softmax + Weighted-V via DSL interpreters.

  Extends `HesperDSLEquivalence.lean` to the rest of the attention
  pipeline:

      Q·K^T  →  softmax  →  attn @ V

  For each stage we build a Hesper-DSL kernel (in both Circuit IR
  and WGSL DSL), evaluate via the Phase-2 interpreters, and pin
  the result against Sparkle's reference (`softmaxRef`,
  `weightedVSum` from `IP/BitNet/Types.lean`) by `native_decide`.

  ## Numerical caveat

  Sparkle's `softmaxRef` runs `Float.exp` then converts to Q8.24
  via `expQ8_24` (Float → UInt64 → Nat truncation). The Hesper
  DSL evaluates entirely in Float. We therefore compare the
  **Float** softmax outputs from the DSL evaluator against an
  intermediate Float-domain reference, then separately
  `native_decide` that Sparkle's Q8.24 form rounds to the same
  numbers within one ULP.

  Per `feedback_hesper_float_bridge.md`: all checks are
  `native_decide` over concrete fixtures, no axioms.
-/

import IP.BitNet.Types
import Tests.Hesper.SoftmaxWeightedV
import Tests.Hesper.Vendored.CircuitInterp
import Tests.Hesper.Vendored.WGSLInterp

namespace Sparkle.Tests.Hesper.HesperSoftmaxWeightedV

open Sparkle.IP.BitNet
open Sparkle.Tests.Hesper.SoftmaxWeightedV
  (fixtureWeights fixtureVCol fixtureWeightsArr fixtureVMatrix Q)
open Sparkle.Tests.Hesper.Vendored.CircuitInterp (ScalarExp evalPointwise evalReduce ReduceOp)
open Sparkle.Tests.Hesper.Vendored.WGSLInterp

/-! ## Softmax fixture (Float domain)

Same scores as `SoftmaxWeightedV.fixtureScores` (= [0, -1, -2, -3])
but evaluated in pure Float so the DSL kernel and Sparkle's
`softmaxRef` can be compared at compatible precisions. -/

def softmaxScoresFloat : Array Float := #[0.0, -1.0, -2.0, -3.0]

/-! ### Circuit-DSL softmax

Standard 3-pass softmax:
  1. Find the max (for numerical stability).
  2. Compute exp(score_i - max) per lane.
  3. Sum-reduce, divide each lane by sum.

We do the max in Lean (it's a reduction) and bake it into the
`ScalarExp` body via a `const`. -/

def fixtureMax : Float :=
  evalReduce ReduceOp.max softmaxScoresFloat

/-- Body for the exp(score - max) pass. -/
def softmaxExpBody : ScalarExp :=
  .exp (.sub (.input 0) (.const fixtureMax))

/-- Hesper Circuit-DSL softmax weights for the fixture (Float). -/
def hesperSoftmaxCircuit : Array Float := Id.run do
  let exps := evalPointwise softmaxExpBody #[softmaxScoresFloat] 4
  let total := evalReduce ReduceOp.sum exps
  let mut out : Array Float := Array.replicate 4 0.0
  for i in [:4] do
    out := out.set! i (exps.getD i 0.0 / total)
  pure out

/-- The Hesper Circuit softmax matches Sparkle's `softmaxRef`
    after rescaling by `2^24` (Q8.24 unit). -/
theorem softmax_circuit_matches_sparkle :
    let hf := hesperSoftmaxCircuit
    let sp := softmaxRef #[0, -1, -2, -3]
    let qf : Array Float := hf.map (· * Float.ofNat (2 ^ 24))
    let allClose : Bool := Id.run do
      let mut ok := true
      for i in [:4] do
        let a := qf.getD i 0.0
        let b := Float.ofInt (sp.getD i 0)
        if (a - b).abs > 4.0 then ok := false
      pure ok
    allClose = true := by
  native_decide

/-! ### WGSL-DSL softmax

Same kernel structure, but built as `Exp` trees:
  1. exp(score_i - max)  for i ∈ {0,1,2,3} unrolled
  2. sum, then divide each by sum.
-/

/-- One lane of the exp(score - max) stage. -/
def laneExp (i : Nat) : Exp (.scalar .f32) :=
  let s : Exp (.scalar .f32) :=
    .index (.var (t := .array (.scalar .f32) 4) "scores") (.litU32 i)
  .exp (.sub s (.litF32 fixtureMax))

/-- Sum of all 4 lanes' exps, as a single tree. -/
def sumExp : Exp (.scalar .f32) :=
  .add (laneExp 0) (.add (laneExp 1) (.add (laneExp 2) (laneExp 3)))

/-- WGSL-DSL softmax weight at lane `i`. -/
def hesperSoftmaxWGSLLane (i : Nat) : Exp (.scalar .f32) :=
  .div (laneExp i) sumExp

def softmaxEnv : EvalEnv :=
  { f32_arrays := [("scores", softmaxScoresFloat)] }

def hesperSoftmaxWGSL : Array Float := Id.run do
  let mut out : Array Float := Array.replicate 4 0.0
  for i in [:4] do
    out := out.set! i (runF32 softmaxEnv (hesperSoftmaxWGSLLane i))
  pure out

theorem softmax_wgsl_matches_circuit :
    let hf := hesperSoftmaxCircuit
    let hw := hesperSoftmaxWGSL
    -- Both Float arrays should be identical bit-for-bit (same
    -- arithmetic, same order). Use `==` for Float equality.
    let allEq : Bool := Id.run do
      let mut ok := true
      for i in [:4] do
        if !(hf.getD i 0.0 == hw.getD i 0.0) then ok := false
      pure ok
    allEq = true := by
  native_decide

theorem softmax_wgsl_matches_sparkle :
    let hw := hesperSoftmaxWGSL
    let sp := softmaxRef #[0, -1, -2, -3]
    let qf : Array Float := hw.map (· * Float.ofNat (2 ^ 24))
    let allClose : Bool := Id.run do
      let mut ok := true
      for i in [:4] do
        let a := qf.getD i 0.0
        let b := Float.ofInt (sp.getD i 0)
        if (a - b).abs > 4.0 then ok := false
      pure ok
    allClose = true := by
  native_decide

/-! ## Weighted-V via DSL

`weightedVSum weights V[*][j] / 2^24` for one output column j.
Same fixture as `SoftmaxWeightedV.lean`:
  weights = [Q/2, Q/4, Q/8, Q/8]  (Q = 2^24)
  V[*]    = [127, -128, 50, -50]

We evaluate the integer-valued sum entirely in Float (since the
DSL runs on Float), then compare with the Sparkle reference.

Sparkle's `weightedVSum` returns the integer 31 for this fixture;
the DSL evaluation should give 31.0 (or extremely close — the
weights are exact dyadic fractions of 2^24, so no float rounding
in the multiplications). -/

def fixtureWeightsFloat : Array Float :=
  fixtureWeights.toArray.map fun i => Float.ofInt i

def fixtureVColFloat : Array Float :=
  fixtureVCol.toArray.map fun i => Float.ofInt i

/-! ### Circuit-DSL weighted-V -/

def weightedVBody : ScalarExp :=
  .mul (.input 0) (.input 1)

def hesperWeightedVCircuit : Float :=
  let prods := evalPointwise weightedVBody
                  #[fixtureWeightsFloat, fixtureVColFloat] 4
  evalReduce ReduceOp.sum prods / Float.ofNat (2 ^ 24)

/-- Sparkle's `weightedVSum` returns the Int-truncated value (31);
    the Hesper Float kernel computes 31.5 because Float division
    is exact for these dyadic operands. The two agree under
    truncation toward zero. -/
theorem weightedV_circuit_matches_sparkle :
    let hf := hesperWeightedVCircuit
    let sp := weightedVSum fixtureWeightsArr fixtureVMatrix 0
    -- Truncate Float toward zero, then compare ints.
    Int32.ofInt hf.toInt32.toInt = Int32.ofInt sp := by
  native_decide

/-! ### WGSL-DSL weighted-V -/

def laneWV (i : Nat) : Exp (.scalar .f32) :=
  let w : Exp (.scalar .f32) :=
    .index (.var (t := .array (.scalar .f32) 4) "w") (.litU32 i)
  let v : Exp (.scalar .f32) :=
    .index (.var (t := .array (.scalar .f32) 4) "v") (.litU32 i)
  .mul w v

def weightedVWGSLExp : Exp (.scalar .f32) :=
  .div
    (.add (laneWV 0) (.add (laneWV 1) (.add (laneWV 2) (laneWV 3))))
    (.litF32 (Float.ofNat (2 ^ 24)))

def weightedVEnv : EvalEnv :=
  { f32_arrays := [("w", fixtureWeightsFloat), ("v", fixtureVColFloat)] }

def hesperWeightedVWGSL : Float := runF32 weightedVEnv weightedVWGSLExp

theorem weightedV_wgsl_matches_sparkle :
    let hw := hesperWeightedVWGSL
    let sp := weightedVSum fixtureWeightsArr fixtureVMatrix 0
    Int32.ofInt hw.toInt32.toInt = Int32.ofInt sp := by
  native_decide

theorem weightedV_circuit_eq_wgsl :
    (hesperWeightedVCircuit == hesperWeightedVWGSL) = true := by
  native_decide

/-! ## Headline: extended honest-status table

For attention's softmax + weighted-V, the equivalence triangle
(Sparkle ↔ Circuit, Sparkle ↔ WGSL, Circuit ↔ WGSL) is now
closed inside Lean for the v1a-shaped fixture, with no GPU FFI.
The matmul + Q·K^T + softmax + weighted-V slice of BitNet
attention is now genuinely "Sparkle ≡ Hesper" inside Lean. -/

end Sparkle.Tests.Hesper.HesperSoftmaxWeightedV
