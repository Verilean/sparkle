/-
  Hespera Top-Level

  SystemVerilog generation entry point.
  Uses Sparkle CircuitM.runModule + toVerilog to emit the pipelined BitLinear module.
  Invoked via `lake exe hespera`.
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.Backend.Verilog
import Examples.BitNet.Config
import Examples.BitNet.BitLinear.Core
import Examples.BitNet.BitLinear.Top
import Examples.BitNet.BitLinear.Scale
import Examples.BitNet.Layers.ReLUSq
import Examples.BitNet.Layers.ResidualAdd
import Examples.BitNet.Layers.ElemMul
import Examples.BitNet.Layers.RMSNorm
import Examples.BitNet.Layers.FFN
import Examples.BitNet.Attention.Quantize
import Examples.BitNet.Attention.DotProduct
import Examples.BitNet.Attention.QKVProjection
import Examples.BitNet.Attention.Softmax
import Examples.BitNet.Attention.ScoreVMul
import Examples.BitNet.Attention.MultiHead
import Examples.BitNet.Attention.Top
import Examples.BitNet.BitLinear.Dynamic
import Examples.BitNet.SoC.Top

open Sparkle.Examples.BitNet
open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.Backend.Verilog

/-- Output directory for generated RTL -/
def rtlDir : System.FilePath := "hw" / "rtl" / "gen"

def main : IO Unit := do
  -- Create output directory
  IO.FS.createDirAll rtlDir

  IO.println "=== Hespera RTL Generator (Full FFN Datapath) ==="
  IO.println ""

  -- ============================================================
  -- 1. BitLinear pipelined module (existing demo)
  -- ============================================================
  let weights : Array Int := #[-1, 1, 0, 1, -1, 0, 0, 1, 1, -1, 0, 0, 1, -1, 1, 0]
  let cfg : GeneratorConfig := {
    baseBitWidth := 8
    pipelineEvery := 2
  }

  let activeCount := weights.foldl (fun acc w => if w != 0 then acc + 1 else acc) 0
  let zeroCount := weights.size - activeCount
  IO.println s!"[BitLinear] Weights: {weights.size} total, {activeCount} active, {zeroCount} pruned"

  let m := BitLinear.buildTop weights cfg
  let verilog := toVerilog m
  let filename := rtlDir / "bitlinear_pipelined.sv"
  IO.FS.writeFile filename verilog
  IO.println s!"  Generated: {filename}"

  -- ============================================================
  -- 2. Scale Multiply module
  -- ============================================================
  let scaleMod := BitLinear.buildScaleMultiply cfg
  let scaleVerilog := toVerilog scaleMod
  let scaleFile := rtlDir / "scale_multiply.sv"
  IO.FS.writeFile scaleFile scaleVerilog
  IO.println s!"  Generated: {scaleFile}"

  -- ============================================================
  -- 3. ReLU² module
  -- ============================================================
  let reluMod := Layers.buildReLUSq
  let reluVerilog := toVerilog reluMod
  let reluFile := rtlDir / "relusq.sv"
  IO.FS.writeFile reluFile reluVerilog
  IO.println s!"  Generated: {reluFile}"

  -- ============================================================
  -- 4. Residual Add module
  -- ============================================================
  let residMod := Layers.buildResidualAdd
  let residVerilog := toVerilog residMod
  let residFile := rtlDir / "residual_add.sv"
  IO.FS.writeFile residFile residVerilog
  IO.println s!"  Generated: {residFile}"

  -- ============================================================
  -- 5. Element Multiply module
  -- ============================================================
  let emulMod := Layers.buildElemMul
  let emulVerilog := toVerilog emulMod
  let emulFile := rtlDir / "elem_mul.sv"
  IO.FS.writeFile emulFile emulVerilog
  IO.println s!"  Generated: {emulFile}"

  -- ============================================================
  -- 6. RMSNorm module (small demo dimension)
  -- ============================================================
  let rmsCfg : Layers.RMSNormConfig := { dim := 16 }
  let rmsMod := Layers.buildRMSNorm rmsCfg cfg
  let rmsVerilog := toVerilog rmsMod
  let rmsFile := rtlDir / "rmsnorm_16.sv"
  IO.FS.writeFile rmsFile rmsVerilog
  IO.println s!"  Generated: {rmsFile}"

  -- ============================================================
  -- 7. FFN Block (small demo)
  -- ============================================================
  let gateWeights : Array Int := #[1, -1, 0, 1, -1, 0, 0, 1]
  let upWeights   : Array Int := #[-1, 1, 1, 0, 1, -1, 0, 1]
  let downWeights : Array Int := #[1, 0, -1, 1, 0, 1, -1, 0]

  let ffnCfg : Layers.FFNConfig := {
    hiddenDim := 8
    ffnDim := 8
    baseBitWidth := 32
    pipelineEvery := 0
  }
  let ffnMod := Layers.buildFFNBlock ffnCfg cfg gateWeights upWeights downWeights
  let ffnVerilog := toVerilog ffnMod
  let ffnFile := rtlDir / "ffn_block_8x8.sv"
  IO.FS.writeFile ffnFile ffnVerilog
  IO.println s!"  Generated: {ffnFile}"

  -- ============================================================
  -- 8. INT8 Quantizer
  -- ============================================================
  let quantMod := Attention.buildQuantize 10
  let quantVerilog := toVerilog quantMod
  let quantFile := rtlDir / "quantize_int8.sv"
  IO.FS.writeFile quantFile quantVerilog
  IO.println s!"  Generated: {quantFile}"

  -- ============================================================
  -- 9. Q·K^T Dot Product (headDim=4 demo)
  -- ============================================================
  let dotCfg : GeneratorConfig := { baseBitWidth := 8, pipelineEvery := 1 }
  let dotMod := Attention.buildDotProduct 4 1 dotCfg
  let dotVerilog := toVerilog dotMod
  let dotFile := rtlDir / "qk_dotproduct_4.sv"
  IO.FS.writeFile dotFile dotVerilog
  IO.println s!"  Generated: {dotFile}"

  -- ============================================================
  -- 10. Full Attention Head Pipeline (headDim=2, inDim=4 demo)
  -- ============================================================
  let attnQW : Array (Array Int) := #[#[1, -1, 0, 1], #[0, 1, -1, 0]]
  let attnKW : Array (Array Int) := #[#[-1, 0, 1, 1], #[1, 1, 0, -1]]
  let attnVW : Array (Array Int) := #[#[0, 1, 1, -1], #[-1, 0, 0, 1]]
  let attnScales : Array Int := #[0x01000000, 0x01000000]

  let headCfg : Attention.AttentionHeadConfig := {
    headDim := 2, inDim := 4, quantShift := 10, dkShift := 1
  }
  let attnMod := Attention.buildAttentionHead headCfg attnQW attnKW attnVW
    attnScales attnScales attnScales cfg
  let attnVerilog := toVerilog attnMod
  let attnFile := rtlDir / "attention_head_2x4.sv"
  IO.FS.writeFile attnFile attnVerilog
  IO.println s!"  Generated: {attnFile}"

  -- ============================================================
  -- 11. Softmax module (seqLen=4)
  -- ============================================================
  let smMod := Attention.buildSoftmax 4 18
  let smVerilog := toVerilog smMod
  let smFile := rtlDir / "softmax_4seq.sv"
  IO.FS.writeFile smFile smVerilog
  IO.println s!"  Generated: {smFile}"

  -- ============================================================
  -- 12. Score-V Multiply module (seqLen=4, headDim=2)
  -- ============================================================
  let svMod := Attention.buildScoreVMul 4 2
  let svVerilog := toVerilog svMod
  let svFile := rtlDir / "scorevmul_4x2.sv"
  IO.FS.writeFile svFile svVerilog
  IO.println s!"  Generated: {svFile}"

  -- ============================================================
  -- 13. Full Attention Head (with softmax + V output)
  -- ============================================================
  let fullAttnCfg : Attention.FullAttentionConfig := {
    headDim := 2, inDim := 4, quantShift := 10, dkShift := 1, seqLen := 4
  }
  let fullAttnMod := Attention.buildFullAttentionHead fullAttnCfg
    attnQW attnKW attnVW attnScales attnScales attnScales cfg
  let fullAttnVerilog := toVerilog fullAttnMod
  let fullAttnFile := rtlDir / "full_attention_head_2x4.sv"
  IO.FS.writeFile fullAttnFile fullAttnVerilog
  IO.println s!"  Generated: {fullAttnFile}"

  -- ============================================================
  -- 14. Multi-Head Attention (nHeads=2, headDim=2, seqLen=4)
  -- ============================================================
  let mhaCfg : Attention.MultiHeadConfig := {
    nHeads := 2, headDim := 2, inDim := 4, seqLen := 4,
    quantShift := 10, dkShift := 1
  }
  let qW1 : Array (Array Int) := #[#[0, 1, 1, 0], #[1, 0, 0, -1]]
  let kW1 : Array (Array Int) := #[#[1, -1, 0, 0], #[0, 0, 1, 1]]
  let vW1 : Array (Array Int) := #[#[1, 0, -1, 0], #[0, 1, 0, -1]]
  let outProjW : Array (Array Int) := #[
    #[1, -1, 0, 1], #[0, 1, 1, 0], #[-1, 0, 1, -1], #[1, 1, 0, 0]
  ]
  let outProjS : Array Int := #[0x01000000, 0x01000000, 0x01000000, 0x01000000]

  let mhaMod := Attention.buildMultiHeadAttention mhaCfg
    #[attnQW, qW1] #[attnKW, kW1] #[attnVW, vW1]
    #[attnScales, attnScales] #[attnScales, attnScales] #[attnScales, attnScales]
    outProjW outProjS cfg
  let mhaVerilog := toVerilog mhaMod
  let mhaFile := rtlDir / "multihead_attention_2h_2d.sv"
  IO.FS.writeFile mhaFile mhaVerilog
  IO.println s!"  Generated: {mhaFile}"

  -- ============================================================
  -- 15. Dynamic BitLinear module (dim=4)
  -- ============================================================
  let dynCfg : GeneratorConfig := { baseBitWidth := 32, pipelineEvery := 0 }
  let dynMod := BitLinear.buildDynamicBitLinear 4 dynCfg
  let dynVerilog := toVerilog dynMod
  let dynFile := rtlDir / "dynamic_bitlinear_4.sv"
  IO.FS.writeFile dynFile dynVerilog
  IO.println s!"  Generated: {dynFile}"

  -- ============================================================
  -- 16. HardwiredUnrolled SoC (2 layers, dim=4)
  -- ============================================================
  let socLayerWeights : Array LayerWeights := #[
    { gateWeights := #[1, -1, 0, 1],
      upWeights   := #[-1, 1, 1, 0],
      downWeights := #[1, 0, -1, 1] },
    { gateWeights := #[0, 1, -1, -1],
      upWeights   := #[1, 0, 0, 1],
      downWeights := #[-1, 1, 1, 0] }
  ]
  let socLayerScales : Array LayerScales := #[
    { gateScale := 0x01000000, upScale := 0x01000000, downScale := 0x01000000 },
    { gateScale := 0x00800000, upScale := 0x01000000, downScale := 0x00C00000 }
  ]

  let hwSocCfg : SoCConfig := {
    archMode := .HardwiredUnrolled, nLayers := 2, dim := 4, ffnDim := 4
  }
  let hwSocMod := SoC.buildBitNetSoC hwSocCfg socLayerWeights socLayerScales dynCfg
  let hwSocVerilog := toVerilog hwSocMod
  let hwSocFile := rtlDir / "bitnet_soc_hw_2L_4d.sv"
  IO.FS.writeFile hwSocFile hwSocVerilog
  IO.println s!"  Generated: {hwSocFile}"

  -- ============================================================
  -- 17. TimeMultiplexed SoC (2 layers, dim=4)
  -- ============================================================
  let tmSocCfg : SoCConfig := {
    archMode := .TimeMultiplexed, nLayers := 2, dim := 4, ffnDim := 4
  }
  let tmSocMod := SoC.buildBitNetSoC tmSocCfg socLayerWeights socLayerScales dynCfg
  let tmSocVerilog := toVerilog tmSocMod
  let tmSocFile := rtlDir / "bitnet_soc_tm_2L_4d.sv"
  IO.FS.writeFile tmSocFile tmSocVerilog
  IO.println s!"  Generated: {tmSocFile}"

  IO.println ""
  IO.println "=== Generation complete (17 modules) ==="
