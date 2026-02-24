/-
  Hespera Attention — Softmax

  Fully combinational softmax for fixed seqLen.

  Architecture:
    scores[0..seqLen-1]
      │
      ├─ [Max Reduction] ── comparator tree (gt_s + mux)
      │         │
      │      max_val
      │         │
      ├─ [Subtract Max] ── diff_i = score_i - max (non-positive)
      │         │
      ├─ [Exp LUT × seqLen] ── 256-entry exp(-|diff|) lookup (mux tree)
      │         │
      ├─ [Sum Reduction] ── adder tree over exp values
      │         │
      ├─ [Reciprocal LUT] ── 256-entry 1/sum lookup (mux tree)
      │         │
      └─ [Normalize × seqLen] ── weight_i = exp_i × recip >> 24

  No FSM — pure combinational datapath for small seqLen.
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.BitNet.Config
import Examples.BitNet.BitLinear.BitWidth
import Examples.BitNet.BitLinear.Core

namespace Sparkle.Examples.BitNet.Attention

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Examples.BitNet.BitLinear
open CircuitM

/-- Generate a 256-entry exp(-i) LUT in Q8.24.
    Index i maps to round(exp(-i) × 2^24).
    For i ≥ ~20, exp(-i) ≈ 0. -/
def generateExpLUT : Array Int := Id.run do
  let mut lut : Array Int := #[]
  for i in [:256] do
    if i == 0 then
      lut := lut.push ((2^softmaxFracBits : Nat) : Int)  -- exp(0) = 1.0 = 2^24
    else
      let val : Float := Float.exp (-(Float.ofNat i))
      let q8_24 := (val * Float.ofNat (2^softmaxFracBits)).toUInt64.toNat
      lut := lut.push (q8_24 : Int)
  return lut

/-- Generate a 256-entry reciprocal LUT in Q8.24.
    Indexed by the top 8 bits of the exp sum.
    Entry i ≈ 2^24 / mapped_sum_value.
    Index 0 clamps to 2^24 (avoid div/0). -/
def generateRecipLUT (maxSumBits : Nat) : Array Int := Id.run do
  let mut lut : Array Int := #[]
  let shift := if maxSumBits > 8 then maxSumBits - 8 else 0
  for i in [:256] do
    if i == 0 then
      -- Clamp: avoid division by zero, return max weight
      lut := lut.push ((2^softmaxFracBits : Nat) : Int)
    else
      -- Map index back to approximate sum value
      let sumApprox : Nat := i <<< shift
      if sumApprox == 0 then
        lut := lut.push ((2^softmaxFracBits : Nat) : Int)
      else
        -- recip = 2^24 / sumApprox
        let recip := (2^softmaxFracBits : Nat) / sumApprox
        lut := lut.push (recip : Int)
  return lut

/-- Build a binary max-reduction tree using gt_s + mux.
    Returns the maximum value as a SizedExpr. -/
partial def buildMaxTree (inputs : Array SizedExpr) (level : Nat)
    : CircuitM SizedExpr := do
  if inputs.size == 0 then
    return { expr := .const 0 32, width := 32 }
  if inputs.size == 1 then
    return inputs[0]!

  let mut results : Array SizedExpr := #[]
  let pairs := inputs.size / 2

  for i in [:pairs] do
    let a := inputs[2 * i]!
    let b := inputs[2 * i + 1]!
    -- Compare: a > b (signed)
    let cmpWire ← makeWire s!"max_cmp_L{level}_{i}" (.bitVector 1)
    emitAssign cmpWire (Expr.op .gt_s [a.expr, b.expr])
    -- Select max
    let maxWire ← makeWire s!"max_L{level}_{i}" (.bitVector a.width)
    emitAssign maxWire (Expr.mux (.ref cmpWire) a.expr b.expr)
    results := results.push { expr := .ref maxWire, width := a.width }

  -- Handle odd element
  if inputs.size % 2 == 1 then
    results := results.push inputs[inputs.size - 1]!

  buildMaxTree results (level + 1)

/-- Build a LUT as a mux tree: if idx==N-1 then lut[N-1] else if idx==N-2 ...
    Same pattern as RMSNorm rsqrt LUT. -/
def buildLUTMuxTree (entries : Array Int) (indexExpr : Expr)
    (indexBits outputBits : Nat) (namePrefix : String)
    : CircuitM SizedExpr := do
  -- Build chained mux tree
  let mut lutExpr := Expr.const (entries[0]!) outputBits
  for i in [:entries.size] do
    let entry := entries[i]!
    lutExpr := Expr.mux
      (Expr.op .eq [indexExpr, .const i indexBits])
      (.const entry outputBits)
      lutExpr
  let outWire ← makeWire s!"{namePrefix}_out" (.bitVector outputBits)
  emitAssign outWire lutExpr
  return { expr := .ref outWire, width := outputBits }

/-- Generate the complete softmax module.

    Inputs:  score_0..score_{seqLen-1}[scoreBits-1:0]
    Outputs: weight_0..weight_{seqLen-1}[31:0] (Q8.24) -/
def generateSoftmax (seqLen scoreBits : Nat) : CircuitM Unit := do
  -- ==========================================
  -- Input declarations
  -- ==========================================
  let mut scoreRefs : Array SizedExpr := #[]
  for i in [:seqLen] do
    addInput s!"score_{i}" (.bitVector scoreBits)
    scoreRefs := scoreRefs.push { expr := .ref s!"score_{i}", width := scoreBits }

  -- ==========================================
  -- Stage 1: Max reduction (signed comparator tree)
  -- ==========================================
  let maxVal ← buildMaxTree scoreRefs 0

  -- ==========================================
  -- Stage 2: Subtract max from each score (diff_i = score_i - max, non-positive)
  -- ==========================================
  let mut diffs : Array SizedExpr := #[]
  for i in [:seqLen] do
    let diffWire ← makeWire s!"diff_{i}" (.bitVector scoreBits)
    emitAssign diffWire (Expr.sub scoreRefs[i]!.expr maxVal.expr)
    diffs := diffs.push { expr := .ref diffWire, width := scoreBits }

  -- ==========================================
  -- Stage 3: Exp LUT lookup for each diff
  -- ==========================================
  -- Take absolute value of diff (diff is non-positive, so negate)
  -- Then use lower 8 bits as LUT index (saturate for large values)
  let expLUT := generateExpLUT

  let mut expVals : Array SizedExpr := #[]
  for i in [:seqLen] do
    -- Negate diff to get positive index (diff ≤ 0, so -diff ≥ 0)
    let absDiffWire ← makeWire s!"abs_diff_{i}" (.bitVector scoreBits)
    emitAssign absDiffWire (Expr.sub (.const 0 scoreBits) diffs[i]!.expr)

    -- LUT index: lower 8 bits of |diff|, clamped by checking upper bits
    -- If |diff| ≥ 256, exp ≈ 0, so we saturate index to 255
    let idxWire ← makeWire s!"exp_idx_{i}" (.bitVector expLutBits)
    if scoreBits > expLutBits then
      -- Check if upper bits are non-zero (overflow → saturate to 255)
      let upperBits ← makeWire s!"exp_upper_{i}" (.bitVector (scoreBits - expLutBits))
      emitAssign upperBits (Expr.slice (.ref absDiffWire) (scoreBits - 1) expLutBits)
      let isLarge ← makeWire s!"exp_large_{i}" (.bitVector 1)
      emitAssign isLarge (Expr.op .not [Expr.op .eq [.ref upperBits, .const 0 (scoreBits - expLutBits)]])
      let lowBits ← makeWire s!"exp_low_{i}" (.bitVector expLutBits)
      emitAssign lowBits (Expr.slice (.ref absDiffWire) (expLutBits - 1) 0)
      emitAssign idxWire (Expr.mux (.ref isLarge)
        (.const 255 expLutBits)
        (.ref lowBits))
    else
      emitAssign idxWire (Expr.slice (.ref absDiffWire) (expLutBits - 1) 0)

    -- LUT lookup
    let expResult ← buildLUTMuxTree expLUT (.ref idxWire)
      expLutBits softmaxTotalBits s!"exp_lut_{i}"
    expVals := expVals.push expResult

  -- ==========================================
  -- Stage 4: Sum reduction over exp values
  -- ==========================================
  -- Use adder tree (reuse from BitLinear)
  let noPipelineCfg : GeneratorConfig := {
    baseBitWidth := softmaxTotalBits
    pipelineEvery := 0
  }
  let expSum ← buildAdderTree expVals 0 noPipelineCfg

  -- ==========================================
  -- Stage 5: Reciprocal LUT (1/sum)
  -- ==========================================
  let recipLUT := generateRecipLUT expSum.width

  -- Index: top 8 bits of the sum
  let recipIdx ← makeWire "recip_idx" (.bitVector recipLutBits)
  if expSum.width > recipLutBits then
    emitAssign recipIdx (Expr.slice expSum.expr (expSum.width - 1) (expSum.width - recipLutBits))
  else
    emitAssign recipIdx (Expr.slice expSum.expr (recipLutBits - 1) 0)

  let recipVal ← buildLUTMuxTree recipLUT (.ref recipIdx)
    recipLutBits softmaxTotalBits "recip_lut"

  -- ==========================================
  -- Stage 6: Normalize — weight_i = (exp_i × recip) >> 24
  -- ==========================================
  let mulWidth := softmaxTotalBits * 2  -- 64-bit product
  for i in [:seqLen] do
    -- Multiply exp_i × recip (unsigned: both are non-negative Q8.24)
    let expExt ← signExtendExpr expVals[i]! mulWidth
    let recipExt ← signExtendExpr recipVal mulWidth
    let prodWire ← makeWire s!"norm_prod_{i}" (.bitVector mulWidth)
    emitAssign prodWire (Expr.mul expExt.expr recipExt.expr)

    -- Shift right by 24 (Q8.24 × Q8.24 → Q8.24)
    let shiftWire ← makeWire s!"norm_shift_{i}" (.bitVector mulWidth)
    emitAssign shiftWire (Expr.op .asr [.ref prodWire, .const softmaxFracBits mulWidth])

    -- Take lower 32 bits as Q8.24 weight
    let weightWire ← makeWire s!"norm_weight_{i}" (.bitVector softmaxTotalBits)
    emitAssign weightWire (Expr.slice (.ref shiftWire) (softmaxTotalBits - 1) 0)

    addOutput s!"weight_{i}" (.bitVector softmaxTotalBits)
    emitAssign s!"weight_{i}" (.ref weightWire)

/-- Build a standalone softmax module -/
def buildSoftmax (seqLen scoreBits : Nat) : Module :=
  CircuitM.runModule s!"Softmax_{seqLen}seq" do
    generateSoftmax seqLen scoreBits

end Sparkle.Examples.BitNet.Attention
