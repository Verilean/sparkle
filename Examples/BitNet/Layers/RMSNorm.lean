/-
  Hespera RMSNorm Layer

  Sequential FSM-based RMSNorm implementation:
    y_i = x_i × rsqrt(mean(x²)) × scale_i

  States: IDLE → ACCUM_SQ → COMPUTE_MEAN → LUT_RSQRT → NORMALIZE → DONE

  - Sum of squares: 76-bit accumulator (each x² up to 2⁶², sum of 5632 < 2⁷⁵)
  - Division by N: precompute 1/N as Q8.24 constant, multiply instead of divide
  - rsqrt: 256-entry LUT indexed by top 8 significant bits, Q8.24 output
  - Normalize: y_i = x_i × rsqrt_val × scale_i
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.BitNet.Config
import Examples.BitNet.BitLinear.BitWidth

namespace Sparkle.Examples.BitNet.Layers

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Examples.BitNet.BitLinear
open CircuitM

/-- Configuration for RMSNorm layer -/
structure RMSNormConfig where
  dim       : Nat         -- Input dimension (e.g., 2048)
  sqAccBits : Nat := 76   -- Accumulator width for sum of squares
  lutBits   : Nat := 8    -- LUT index width (256 entries)
  deriving Repr, BEq

/-- Compute 1/N as a Q8.24 fixed-point constant (truncated integer) -/
def reciprocalQ8_24 (n : Nat) : Int :=
  (2^scaleFracBits : Int) / n

/-- Generate a 256-entry rsqrt LUT.
    For index i (0..255), the entry approximates rsqrt(value) in Q8.24.
    Index 0 maps to the largest magnitude, index 255 to the smallest. -/
def generateRsqrtLUT : Array Int := Id.run do
  let mut lut : Array Int := #[]
  for i in [:256] do
    if i == 0 then
      -- Avoid division by zero; maximum clamped value
      lut := lut.push ((2^scaleFracBits : Nat) : Int)
    else
      -- Map index to a representative value in range [1, 2^24)
      -- LUT indexed by top 8 bits of the mean-of-squares value
      let val : Float := Float.ofNat (i * (2^16))  -- Scale to meaningful range
      let rsqrt := 1.0 / Float.sqrt val
      let q8_24 := (rsqrt * Float.ofNat (2^scaleFracBits)).toUInt64.toNat
      lut := lut.push (q8_24 : Int)
  return lut

/-- Generate the RMSNorm module as a sequential FSM.

    The FSM processes one element per cycle:
    1. ACCUM_SQ: accumulate x_i² into sum
    2. COMPUTE_MEAN: multiply sum by 1/N
    3. LUT_RSQRT: look up rsqrt in LUT
    4. NORMALIZE: compute y_i = x_i × rsqrt_val

    I/O:
    - Inputs: clk, rst, start, x_in[31:0], scale_in[31:0]
    - Outputs: y_out[31:0], done, elem_idx[addr_bits-1:0] -/
def generateRMSNorm (config : RMSNormConfig) (genCfg : GeneratorConfig) : CircuitM Unit := do
  let addrBits := ceilLog2 config.dim

  -- Inputs
  addInput genCfg.clockName .bit
  addInput genCfg.resetName .bit
  addInput "start" .bit
  addInput "x_in" (.bitVector actTotalBits)
  addInput "scale_in" (.bitVector scaleTotalBits)

  -- Outputs
  addOutput "y_out" (.bitVector actTotalBits)
  addOutput "done" .bit
  addOutput "elem_idx" (.bitVector addrBits)
  addOutput "reading" .bit  -- High when FSM needs input data

  -- FSM state encoding (3 bits for 5 states)
  let stateBits := 3
  let sIdle      := 0
  let sAccumSq   := 1
  let sCompMean  := 2
  let sLutRsqrt  := 3
  let sNormalize := 4

  -- State register
  let stateNext ← makeWire "state_next" (.bitVector stateBits)
  let _stateReg ← emitRegister "state" genCfg.clockName genCfg.resetName
    (.ref stateNext) sIdle (.bitVector stateBits)

  -- Element counter register
  let cntNext ← makeWire "cnt_next" (.bitVector addrBits)
  let _cntReg ← emitRegister "cnt" genCfg.clockName genCfg.resetName
    (.ref cntNext) 0 (.bitVector addrBits)

  -- Sum-of-squares accumulator (76 bits)
  let sqAccNext ← makeWire "sq_acc_next" (.bitVector config.sqAccBits)
  let _sqAccReg ← emitRegister "sq_acc" genCfg.clockName genCfg.resetName
    (.ref sqAccNext) 0 (.bitVector config.sqAccBits)

  -- rsqrt value register (Q8.24)
  let rsqrtNext ← makeWire "rsqrt_next" (.bitVector scaleTotalBits)
  let _rsqrtReg ← emitRegister "rsqrt_val" genCfg.clockName genCfg.resetName
    (.ref rsqrtNext) 0 (.bitVector scaleTotalBits)

  -- Compute x_in² (sign-extend to 64, multiply, result in 64 bits)
  let xRef : SizedExpr := { expr := .ref "x_in", width := actTotalBits }
  let xExt ← signExtendExpr xRef squaredBits
  let xSqWire ← makeWire "x_sq" (.bitVector squaredBits)
  emitAssign xSqWire (Expr.mul xExt.expr xExt.expr)

  -- Sign-extend x² to sqAccBits for accumulation
  let xSqRef : SizedExpr := { expr := .ref xSqWire, width := squaredBits }
  let xSqExt ← signExtendExpr xSqRef config.sqAccBits

  -- Accumulate: sq_acc + x²
  let sqAccSum ← makeWire "sq_acc_sum" (.bitVector config.sqAccBits)
  emitAssign sqAccSum (Expr.add (.ref _sqAccReg) xSqExt.expr)

  -- Multiply sum by 1/N (Q8.24): mean = sum × (1/N)
  let recipN := reciprocalQ8_24 config.dim
  let meanWire ← makeWire "mean_val" (.bitVector config.sqAccBits)
  emitAssign meanWire (Expr.op .asr
    [Expr.mul (.ref _sqAccReg) (.const recipN config.sqAccBits),
     .const scaleFracBits config.sqAccBits])

  -- LUT index: top 8 significant bits of mean value
  -- Use bits [23:16] of the mean (after shift) as LUT index
  let lutIndex ← makeWire "lut_idx" (.bitVector config.lutBits)
  emitAssign lutIndex (Expr.slice (.ref meanWire) 23 16)

  -- Generate rsqrt LUT as a case/mux tree
  -- For RTL, we emit a combinational lookup using nested muxes
  let rsqrtLUT := generateRsqrtLUT
  let lutOut ← makeWire "lut_out" (.bitVector scaleTotalBits)

  -- Build LUT as chained mux: if idx==255 then lut[255] else if idx==254 ...
  let mut lutExpr := Expr.const (rsqrtLUT[0]!) scaleTotalBits
  for i in [:256] do
    let entry := rsqrtLUT[i]!
    lutExpr := Expr.mux
      (Expr.op .eq [.ref lutIndex, .const i config.lutBits])
      (.const entry scaleTotalBits)
      lutExpr
  emitAssign lutOut lutExpr

  -- Normalize: y_i = x_in × rsqrt_val (Q16.16 × Q8.24, shift right 24)
  let normProd ← makeWire "norm_prod" (.bitVector squaredBits)
  let xExtNorm ← signExtendExpr xRef squaredBits
  let rsqrtRef : SizedExpr := { expr := .ref _rsqrtReg, width := scaleTotalBits }
  let rsqrtExt ← signExtendExpr rsqrtRef squaredBits
  emitAssign normProd (Expr.mul xExtNorm.expr rsqrtExt.expr)

  let normShifted ← makeWire "norm_shifted" (.bitVector squaredBits)
  emitAssign normShifted (Expr.op .asr [.ref normProd, .const scaleFracBits squaredBits])

  -- Apply scale: norm_shifted × scale_in (Q16.16 × Q8.24, shift right 24)
  let normSlice ← makeWire "norm_slice" (.bitVector actTotalBits)
  emitAssign normSlice (Expr.slice (.ref normShifted) (actTotalBits - 1) 0)

  let scaledProd ← makeWire "scaled_prod" (.bitVector squaredBits)
  let normRef : SizedExpr := { expr := .ref normSlice, width := actTotalBits }
  let normExt ← signExtendExpr normRef squaredBits
  let scaleRef : SizedExpr := { expr := .ref "scale_in", width := scaleTotalBits }
  let scaleExtN ← signExtendExpr scaleRef squaredBits
  emitAssign scaledProd (Expr.mul normExt.expr scaleExtN.expr)

  let scaledShifted ← makeWire "scaled_shifted" (.bitVector squaredBits)
  emitAssign scaledShifted (Expr.op .asr [.ref scaledProd, .const scaleFracBits squaredBits])

  let yResult ← makeWire "y_result" (.bitVector actTotalBits)
  emitAssign yResult (Expr.slice (.ref scaledShifted) (actTotalBits - 1) 0)

  -- Counter increment
  let cntInc ← makeWire "cnt_inc" (.bitVector addrBits)
  emitAssign cntInc (Expr.add (.ref _cntReg) (.const 1 addrBits))

  -- Counter at max (dim - 1)
  let cntDone ← makeWire "cnt_done" (.bitVector 1)
  emitAssign cntDone (Expr.op .eq [.ref _cntReg, .const (config.dim - 1) addrBits])

  -- FSM next-state logic
  -- Default: hold current state
  let stateHold := Expr.ref _stateReg

  -- IDLE → ACCUM_SQ on start
  let idleNext := Expr.mux (.ref "start")
    (.const sAccumSq stateBits)
    (.const sIdle stateBits)

  -- ACCUM_SQ → COMPUTE_MEAN when counter done
  let accumNext := Expr.mux (.ref cntDone)
    (.const sCompMean stateBits)
    (.const sAccumSq stateBits)

  -- COMPUTE_MEAN → LUT_RSQRT (single cycle)
  let compMeanNext := Expr.const sLutRsqrt stateBits

  -- LUT_RSQRT → NORMALIZE (single cycle)
  let lutNext := Expr.const sNormalize stateBits

  -- NORMALIZE → IDLE when counter done (reuses counter)
  let normNext := Expr.mux (.ref cntDone)
    (.const sIdle stateBits)
    (.const sNormalize stateBits)

  -- State mux tree
  emitAssign stateNext
    (Expr.mux (Expr.op .eq [stateHold, .const sIdle stateBits])
      idleNext
      (Expr.mux (Expr.op .eq [stateHold, .const sAccumSq stateBits])
        accumNext
        (Expr.mux (Expr.op .eq [stateHold, .const sCompMean stateBits])
          compMeanNext
          (Expr.mux (Expr.op .eq [stateHold, .const sLutRsqrt stateBits])
            lutNext
            (Expr.mux (Expr.op .eq [stateHold, .const sNormalize stateBits])
              normNext
              (.const sIdle stateBits))))))

  -- Counter next-state logic
  let isAccumSq := Expr.op .eq [.ref _stateReg, .const sAccumSq stateBits]
  let isNormalize := Expr.op .eq [.ref _stateReg, .const sNormalize stateBits]
  let isCompMean := Expr.op .eq [.ref _stateReg, .const sCompMean stateBits]

  -- Reset counter at transitions: start, COMPUTE_MEAN (before normalize pass)
  let cntReset := Expr.mux (Expr.op .or [isCompMean, Expr.op .and [
      Expr.op .eq [.ref _stateReg, .const sIdle stateBits], .ref "start"]])
    (.const 0 addrBits)
    (Expr.mux (Expr.op .or [isAccumSq, isNormalize])
      (.ref cntInc)
      (.ref _cntReg))

  emitAssign cntNext cntReset

  -- Accumulator next: clear on start, accumulate during ACCUM_SQ
  emitAssign sqAccNext
    (Expr.mux (Expr.op .and [
        Expr.op .eq [.ref _stateReg, .const sIdle stateBits], .ref "start"])
      (.const 0 config.sqAccBits)
      (Expr.mux isAccumSq
        (.ref sqAccSum)
        (.ref _sqAccReg)))

  -- rsqrt register: latch LUT output during LUT_RSQRT state
  let isLutState := Expr.op .eq [.ref _stateReg, .const sLutRsqrt stateBits]
  emitAssign rsqrtNext
    (Expr.mux isLutState (.ref lutOut) (.ref _rsqrtReg))

  -- Output assignments
  emitAssign "y_out" (.ref yResult)
  emitAssign "done" (Expr.op .and
    [isNormalize, .ref cntDone])
  emitAssign "elem_idx" (.ref _cntReg)
  emitAssign "reading" (Expr.op .or [isAccumSq, isNormalize])

/-- Build a standalone RMSNorm module -/
def buildRMSNorm (config : RMSNormConfig) (genCfg : GeneratorConfig) : Module :=
  CircuitM.runModule s!"RMSNorm_{config.dim}" do
    generateRMSNorm config genCfg

end Sparkle.Examples.BitNet.Layers
