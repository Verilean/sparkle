/-
  Hespera Attention — INT8 Q·K^T Dot Product

  Fully pipelined dot product between INT8 Q and K vectors.
  Unlike BitLinear (ternary → multiplier-less), this uses actual signed
  INT8×INT8 multipliers because Q and K are dynamic activations.

  Architecture:
    1. Sign-extend q[i], k[i] from 8 → 16 bits
    2. Multiply: prod[i] = q_ext[i] * k_ext[i]  (16-bit signed)
    3. Adder tree reduction (reuses BitLinear.buildAdderTree)
    4. Scale by 1/sqrt(d_k) via arithmetic right shift

  No FSM — pure datapath with configurable pipeline register insertion.
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

/-- Generate the INT8 multiplier array.

    For each element i in [0, headDim):
      1. Sign-extend q_i and k_i from 8 to 16 bits
      2. Multiply → 16-bit signed product

    Returns an array of 16-bit SizedExprs (one per element). -/
def generateInt8MulArray (headDim : Nat) : CircuitM (Array SizedExpr) := do
  let mut products : Array SizedExpr := #[]
  for i in [:headDim] do
    -- Sign-extend q_i from 8 to 16 bits
    let qRef : SizedExpr := { expr := .ref s!"q_{i}", width := qkvBits }
    let qExt ← signExtendExpr qRef productBits

    -- Sign-extend k_i from 8 to 16 bits
    let kRef : SizedExpr := { expr := .ref s!"k_{i}", width := qkvBits }
    let kExt ← signExtendExpr kRef productBits

    -- Signed multiply: 16-bit × 16-bit → 16-bit (both already same width)
    let prodWire ← makeWire s!"qk_prod_{i}" (.bitVector productBits)
    emitAssign prodWire (Expr.mul qExt.expr kExt.expr)

    products := products.push { expr := .ref prodWire, width := productBits }
  return products

/-- Generate the complete Q·K^T dot product pipeline.

    Inputs:  clk, rst, q_0..q_{headDim-1}[7:0], k_0..k_{headDim-1}[7:0]
    Output:  score[resultWidth-1:0]

    The result width is productBits + ceil(log2(headDim)):
    - headDim=64: 16 + 6 = 22 bits
    - headDim=4:  16 + 2 = 18 bits

    Optionally scaled by 1/sqrt(d_k) via arithmetic right shift. -/
def generateInt8DotProduct (headDim : Nat) (dkShift : Nat)
    (cfg : GeneratorConfig) : CircuitM Unit := do
  -- Clock and reset for pipeline registers
  addInput cfg.clockName .bit
  addInput cfg.resetName .bit

  -- Q and K vector inputs (INT8 each)
  for i in [:headDim] do
    addInput s!"q_{i}" (.bitVector qkvBits)
    addInput s!"k_{i}" (.bitVector qkvBits)

  -- Stage 1: INT8 multiplier array
  let products ← generateInt8MulArray headDim

  if products.size == 0 then
    addOutput "score" (.bitVector productBits)
    emitAssign "score" (.const 0 productBits)
    return

  -- Stage 2: Binary adder tree reduction (reuses BitLinear infrastructure)
  let dotSum ← buildAdderTree products 0 cfg

  -- Stage 3: Scale by 1/sqrt(d_k) = arithmetic right shift
  if dkShift > 0 then
    let scoreWire ← makeWire "score_scaled" (.bitVector dotSum.width)
    emitAssign scoreWire (Expr.op .asr [dotSum.expr, .const dkShift dotSum.width])
    addOutput "score" (.bitVector dotSum.width)
    emitAssign "score" (.ref scoreWire)
  else
    addOutput "score" (.bitVector dotSum.width)
    emitAssign "score" dotSum.expr

/-- Build a standalone Q·K^T dot product module.

    Parameters:
    - headDim: number of elements in Q and K vectors
    - dkShift: right-shift amount for 1/sqrt(d_k) scaling
    - cfg: pipeline configuration -/
def buildDotProduct (headDim : Nat) (dkShift : Nat) (cfg : GeneratorConfig)
    : Module :=
  CircuitM.runModule s!"QK_DotProduct_{headDim}elem" do
    generateInt8DotProduct headDim dkShift cfg

end Sparkle.Examples.BitNet.Attention
