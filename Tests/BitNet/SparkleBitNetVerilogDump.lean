/-
  Dump Sparkle BitNet-generated Verilog to files for cross-validation.
-/

import Examples.BitNet.Config
import Examples.BitNet.Types
import Examples.BitNet.BitLinear.Core
import Examples.BitNet.BitLinear.Top
import Examples.BitNet.BitLinear.Scale
import Examples.BitNet.Layers.ReLUSq
import Examples.BitNet.Layers.ResidualAdd
import Examples.BitNet.Layers.ElemMul
import Examples.BitNet.Layers.FFN
import Examples.BitNet.Attention.Quantize
import Examples.BitNet.Attention.DotProduct
import Examples.BitNet.Attention.Softmax
import Examples.BitNet.Attention.ScoreVMul
import Examples.BitNet.SoC.Top

import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.Backend.Verilog

open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Backend.Verilog
open Sparkle.Examples.BitNet

def main : IO Unit := do
  let outDir := "/tmp/bitnet_cross_validation/sparkle"
  IO.FS.createDirAll outDir

  let cfg8 : GeneratorConfig := { baseBitWidth := 8, pipelineEvery := 2 }
  let cfg32 : GeneratorConfig := { baseBitWidth := 32, pipelineEvery := 0 }

  -- BitLinear
  let weights : Array Int := #[-1, 1, 0, 1, -1, 0, 0, 1, 1, -1, 0, 0, 1, -1, 1, 0]
  IO.FS.writeFile s!"{outDir}/bitlinear.sv" (toVerilog (BitLinear.buildTop weights cfg8))
  IO.FS.writeFile s!"{outDir}/bitlinear_zero.sv" (toVerilog (BitLinear.buildTop #[0,0,0,0] cfg8))
  IO.FS.writeFile s!"{outDir}/bitlinear_single.sv" (toVerilog (BitLinear.buildTop #[1] cfg8))

  -- Scale
  IO.FS.writeFile s!"{outDir}/scale.sv" (toVerilog (BitLinear.buildScaleMultiply cfg32))

  -- Layers
  IO.FS.writeFile s!"{outDir}/relusq.sv" (toVerilog Layers.buildReLUSq)
  IO.FS.writeFile s!"{outDir}/residualadd.sv" (toVerilog Layers.buildResidualAdd)
  IO.FS.writeFile s!"{outDir}/elemmul.sv" (toVerilog Layers.buildElemMul)

  -- Attention
  IO.FS.writeFile s!"{outDir}/quantize.sv" (toVerilog (Attention.buildQuantize 10))
  IO.FS.writeFile s!"{outDir}/dotproduct.sv" (toVerilog (Attention.buildDotProduct 4 1 cfg8))
  IO.FS.writeFile s!"{outDir}/softmax.sv" (toVerilog (Attention.buildSoftmax 4 18))
  IO.FS.writeFile s!"{outDir}/scorevmul.sv" (toVerilog (Attention.buildScoreVMul 4 2))

  -- FFN Block
  let ffnCfg : Layers.FFNConfig := {
    hiddenDim := 4, ffnDim := 4, baseBitWidth := 32, pipelineEvery := 0
  }
  IO.FS.writeFile s!"{outDir}/ffnblock.sv" (toVerilog (Layers.buildFFNBlock ffnCfg cfg32 #[1,-1,0,1] #[-1,1,1,0] #[1,0,-1,1]))

  -- SoC
  let layerWeights : Array LayerWeights := #[
    { gateWeights := #[1, -1, 0, 1], upWeights := #[-1, 1, 1, 0], downWeights := #[1, 0, -1, 1] },
    { gateWeights := #[0, 1, -1, -1], upWeights := #[1, 0, 0, 1], downWeights := #[-1, 1, 1, 0] }
  ]
  let layerScales : Array LayerScales := #[
    { gateScale := 0x01000000, upScale := 0x01000000, downScale := 0x01000000 },
    { gateScale := 0x00800000, upScale := 0x01000000, downScale := 0x00C00000 }
  ]
  let hwCfg : SoCConfig := { archMode := .HardwiredUnrolled, nLayers := 2, dim := 4, ffnDim := 4 }
  let tmCfg : SoCConfig := { archMode := .TimeMultiplexed, nLayers := 2, dim := 4, ffnDim := 4 }

  IO.FS.writeFile s!"{outDir}/soc_hw.sv" (toVerilog (SoC.buildBitNetSoC hwCfg layerWeights layerScales cfg32))
  IO.FS.writeFile s!"{outDir}/soc_tm.sv" (toVerilog (SoC.buildBitNetSoC tmCfg layerWeights layerScales cfg32))

  -- Spec values
  let acc : BitVec 48 := BitVec.ofNat 48 0x10000
  let scale : BitVec 32 := BitVec.ofNat 32 0x01000000
  IO.FS.writeFile s!"{outDir}/spec_values.txt" (
    s!"fixedPointScale(1.0,1.0) = {(fixedPointScale acc scale).toNat}\n" ++
    s!"reluSquared(2.0) = {(reluSquared (BitVec.ofNat 32 0x20000)).toNat}\n" ++
    s!"residualAdd(1.0,1.0) = {(residualAdd (BitVec.ofNat 32 0x10000) (BitVec.ofNat 32 0x10000)).toNat}\n" ++
    s!"elemMul(2.0,3.0) = {(elemMul (BitVec.ofNat 32 0x20000) (BitVec.ofNat 32 0x30000)).toNat}\n" ++
    s!"quantizeToInt8(1.0,10) = {(quantizeToInt8 (BitVec.ofNat 32 0x10000) 10).toInt}\n" ++
    s!"int8DotProduct([1,2,3],[4,5,6]) = {int8DotProduct #[BitVec.ofInt 8 1, BitVec.ofInt 8 2, BitVec.ofInt 8 3] #[BitVec.ofInt 8 4, BitVec.ofInt 8 5, BitVec.ofInt 8 6]}\n"
  )

  IO.println s!"Sparkle BitNet Verilog dumped to {outDir}/"
