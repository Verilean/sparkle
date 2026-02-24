/-
  Hespera SoC Top-Level Generator

  Generates complete SoC modules in two architecture modes:

  1. HardwiredUnrolled: N distinct hardwired FFN layers chained in sequence.
     Each layer has unique weight patterns with zero-weight pruning.
     Maximum performance, maximum area.

  2. TimeMultiplexed: One generic FFN core with dynamic BitLinear rows,
     a weight ROM (mux-tree LUT), and an FSM that loops through layers.
     Minimum area, sequential execution.
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.BitNet.Config
import Examples.BitNet.BitLinear.BitWidth
import Examples.BitNet.BitLinear.Core
import Examples.BitNet.BitLinear.Dynamic
import Examples.BitNet.BitLinear.Scale
import Examples.BitNet.Layers.ReLUSq
import Examples.BitNet.Layers.ResidualAdd
import Examples.BitNet.Layers.ElemMul
import Examples.BitNet.Layers.FFN

namespace Sparkle.Examples.BitNet.SoC

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Examples.BitNet.BitLinear
open CircuitM

/-- Encode an Int ternary weight to its 2-bit i2_s code.
    -1 → 0b00, 0 → 0b01, +1 → 0b10 -/
def encodeTernary (w : Int) : Int :=
  if w == -1 then 0b00
  else if w == 1 then 0b10
  else 0b01  -- 0

-- ============================================================================
-- HardwiredUnrolled Mode
-- ============================================================================

/-- Generate a HardwiredUnrolled SoC: chain N hardwired FFN layers.

    Each layer uses `emitInstance` to wire a pre-generated FFN block.
    Layer i output feeds into layer i+1 input.

    Inputs: clk, rst, start, x_in[31:0], per-layer scale inputs
    Outputs: y_out[31:0], done -/
def generateHardwiredSoC (cfg : SoCConfig) (layerWeights : Array LayerWeights)
    (layerScales : Array LayerScales) (genCfg : GeneratorConfig) : CircuitM Unit := do
  -- Top-level I/O
  addInput genCfg.clockName .bit
  addInput genCfg.resetName .bit
  addInput "start" .bit
  addInput "x_in" (.bitVector actTotalBits)
  addOutput "y_out" (.bitVector actTotalBits)
  addOutput "done" .bit

  -- Chain layers: output of layer i → input of layer i+1
  let mut prevOutput := "x_in"
  let mut prevDone := "start"

  for i in [:cfg.nLayers] do
    if i < layerWeights.size then
      let _lw : LayerWeights := layerWeights[i]!
      let ls : LayerScales :=
        if i < layerScales.size then layerScales[i]!
        else { gateScale := 0x01000000, upScale := 0x01000000, downScale := 0x01000000 }

      -- Create per-layer scale constant wires
      let gateScaleWire ← makeWire s!"layer{i}_gate_scale" (.bitVector scaleTotalBits)
      emitAssign gateScaleWire (.const ls.gateScale scaleTotalBits)

      let upScaleWire ← makeWire s!"layer{i}_up_scale" (.bitVector scaleTotalBits)
      emitAssign upScaleWire (.const ls.upScale scaleTotalBits)

      let downScaleWire ← makeWire s!"layer{i}_down_scale" (.bitVector scaleTotalBits)
      emitAssign downScaleWire (.const ls.downScale scaleTotalBits)

      let rmsnormScaleWire ← makeWire s!"layer{i}_rmsnorm_scale" (.bitVector scaleTotalBits)
      emitAssign rmsnormScaleWire (.const 0x01000000 scaleTotalBits)

      -- Inter-layer wires
      let layerOut ← makeWire s!"layer{i}_out" (.bitVector actTotalBits)
      let layerDone ← makeWire s!"layer{i}_done" .bit

      -- Compute FFN module name (follows FFN.lean naming convention)
      let ffnModName := s!"FFNBlock_{cfg.dim}x{cfg.ffnDim}_L{i}"

      emitInstance ffnModName s!"u_layer{i}" [
        (genCfg.clockName, .ref genCfg.clockName),
        (genCfg.resetName, .ref genCfg.resetName),
        ("start", .ref prevDone),
        ("x_in", .ref prevOutput),
        ("rmsnorm_scale", .ref rmsnormScaleWire),
        ("gate_scale", .ref gateScaleWire),
        ("up_scale", .ref upScaleWire),
        ("down_scale", .ref downScaleWire),
        ("y_out", .ref layerOut),
        ("done", .ref layerDone)
      ]

      prevOutput := layerOut
      prevDone := layerDone

  -- Connect final output
  emitAssign "y_out" (.ref prevOutput)
  emitAssign "done" (.ref prevDone)

-- ============================================================================
-- TimeMultiplexed Mode
-- ============================================================================

/-- Generate a weight ROM as a mux-tree LUT.

    For each layer, concatenate all weights (gate + up + down) into a flat vector
    of 2-bit codes. The ROM is indexed by `layerRegName`.

    Returns the wire names for gate/up/down weight outputs. -/
def generateWeightROM (nLayers : Nat) (dim : Nat) (layerWeights : Array LayerWeights)
    (layerRegName : String) (_genCfg : GeneratorConfig)
    : CircuitM (Array String × Array String × Array String) := do
  let layerBits := ceilLog2 (max nLayers 2)

  -- Gate weights: dim elements
  let mut gateWires : Array String := #[]
  for j in [:dim] do
    let wireName ← makeWire s!"rom_gate_w_{j}" (.bitVector 2)
    let mut muxExpr := Expr.const 0b01 2  -- default: zero weight
    for i in [:nLayers] do
      if i < layerWeights.size then
        let lw : LayerWeights := layerWeights[i]!
        let wVal := if j < lw.gateWeights.size then encodeTernary lw.gateWeights[j]! else 0b01
        muxExpr := Expr.mux
          (Expr.op .eq [.ref layerRegName, .const i layerBits])
          (.const wVal 2)
          muxExpr
    emitAssign wireName muxExpr
    gateWires := gateWires.push wireName

  -- Up weights
  let mut upWires : Array String := #[]
  for j in [:dim] do
    let wireName ← makeWire s!"rom_up_w_{j}" (.bitVector 2)
    let mut muxExpr := Expr.const 0b01 2
    for i in [:nLayers] do
      if i < layerWeights.size then
        let lw : LayerWeights := layerWeights[i]!
        let wVal := if j < lw.upWeights.size then encodeTernary lw.upWeights[j]! else 0b01
        muxExpr := Expr.mux
          (Expr.op .eq [.ref layerRegName, .const i layerBits])
          (.const wVal 2)
          muxExpr
    emitAssign wireName muxExpr
    upWires := upWires.push wireName

  -- Down weights
  let mut downWires : Array String := #[]
  for j in [:dim] do
    let wireName ← makeWire s!"rom_down_w_{j}" (.bitVector 2)
    let mut muxExpr := Expr.const 0b01 2
    for i in [:nLayers] do
      if i < layerWeights.size then
        let lw : LayerWeights := layerWeights[i]!
        let wVal := if j < lw.downWeights.size then encodeTernary lw.downWeights[j]! else 0b01
        muxExpr := Expr.mux
          (Expr.op .eq [.ref layerRegName, .const i layerBits])
          (.const wVal 2)
          muxExpr
    emitAssign wireName muxExpr
    downWires := downWires.push wireName

  return (gateWires, upWires, downWires)

/-- Generate a scale ROM as a mux-tree LUT indexed by `layerRegName`.
    Returns wire names for gate/up/down scale outputs. -/
def generateScaleROM (nLayers : Nat) (layerScales : Array LayerScales)
    (layerRegName : String) (_genCfg : GeneratorConfig)
    : CircuitM (String × String × String) := do
  let layerBits := ceilLog2 (max nLayers 2)

  -- Gate scale mux
  let gateScaleWire ← makeWire "rom_gate_scale" (.bitVector scaleTotalBits)
  let mut gMux := Expr.const 0x01000000 scaleTotalBits
  for i in [:nLayers] do
    if i < layerScales.size then
      let ls : LayerScales := layerScales[i]!
      gMux := Expr.mux
        (Expr.op .eq [.ref layerRegName, .const i layerBits])
        (.const ls.gateScale scaleTotalBits)
        gMux
  emitAssign gateScaleWire gMux

  -- Up scale mux
  let upScaleWire ← makeWire "rom_up_scale" (.bitVector scaleTotalBits)
  let mut uMux := Expr.const 0x01000000 scaleTotalBits
  for i in [:nLayers] do
    if i < layerScales.size then
      let ls : LayerScales := layerScales[i]!
      uMux := Expr.mux
        (Expr.op .eq [.ref layerRegName, .const i layerBits])
        (.const ls.upScale scaleTotalBits)
        uMux
  emitAssign upScaleWire uMux

  -- Down scale mux
  let downScaleWire ← makeWire "rom_down_scale" (.bitVector scaleTotalBits)
  let mut dMux := Expr.const 0x01000000 scaleTotalBits
  for i in [:nLayers] do
    if i < layerScales.size then
      let ls : LayerScales := layerScales[i]!
      dMux := Expr.mux
        (Expr.op .eq [.ref layerRegName, .const i layerBits])
        (.const ls.downScale scaleTotalBits)
        dMux
  emitAssign downScaleWire dMux

  return (gateScaleWire, upScaleWire, downScaleWire)

/-- Generate a TimeMultiplexed SoC with FSM-driven layer sequencing.

    Architecture:
      - One generic FFN core with DynamicBitLinear rows
      - Weight ROM (mux-tree LUT) indexed by layer_idx
      - Scale ROM (mux-tree LUT) indexed by layer_idx
      - FSM: IDLE → COMPUTE → NEXT_LAYER → (loop or DONE)
      - Activation register for inter-layer storage

    Inputs: clk, rst, start, x_in[31:0]
    Outputs: y_out[31:0], done -/
def generateTimeMultiplexedSoC (cfg : SoCConfig) (layerWeights : Array LayerWeights)
    (layerScales : Array LayerScales) (genCfg : GeneratorConfig) : CircuitM Unit := do
  -- Top-level I/O
  addInput genCfg.clockName .bit
  addInput genCfg.resetName .bit
  addInput "start" .bit
  addInput "x_in" (.bitVector actTotalBits)
  addOutput "y_out" (.bitVector actTotalBits)
  addOutput "done" .bit

  -- FSM state encoding (2 bits for 4 states)
  let stateBits := 2
  let sIdle      := 0
  let sCompute   := 1
  let sNextLayer := 2
  let sDone      := 3

  let layerBits := ceilLog2 (max cfg.nLayers 2)

  -- State register
  let stateNext ← makeWire "state_next" (.bitVector stateBits)
  let _stateReg ← emitRegister "state" genCfg.clockName genCfg.resetName
    (.ref stateNext) sIdle (.bitVector stateBits)

  -- Layer counter register
  let layerNext ← makeWire "layer_next" (.bitVector layerBits)
  let _layerReg ← emitRegister "layer_idx" genCfg.clockName genCfg.resetName
    (.ref layerNext) 0 (.bitVector layerBits)

  -- Activation register (stores intermediate result between layers)
  let actNext ← makeWire "act_next" (.bitVector actTotalBits)
  let _actReg ← emitRegister "act_reg" genCfg.clockName genCfg.resetName
    (.ref actNext) 0 (.bitVector actTotalBits)

  -- Weight ROM (pass generated layer register name)
  let (gateWWires, upWWires, downWWires) ←
    generateWeightROM cfg.nLayers cfg.dim layerWeights _layerReg genCfg

  -- Scale ROM (pass generated layer register name)
  let (gateScaleW, upScaleW, downScaleW) ←
    generateScaleROM cfg.nLayers layerScales _layerReg genCfg

  -- Dynamic BitLinear instances for gate, up, down paths
  -- DynamicBitLinear output width: baseBitWidth + ceil(log2(dim))
  let dynOutputWidth := genCfg.baseBitWidth + ceilLog2 (max cfg.dim 2)

  -- Build gate BitLinear instance connections
  let mut gateConns : List (String × Expr) := [
    (genCfg.clockName, .ref genCfg.clockName),
    (genCfg.resetName, .ref genCfg.resetName)
  ]
  for j in [:cfg.dim] do
    gateConns := gateConns ++ [
      (s!"w_{j}", .ref gateWWires[j]!),
      (s!"act_{j}", .ref _actReg)
    ]

  let _gateResultRaw ← makeWire "gate_result_raw" (.bitVector dynOutputWidth)
  gateConns := gateConns ++ [("result", .ref _gateResultRaw)]
  emitInstance s!"DynamicBitLinear_{cfg.dim}" "u_gate_dyn" gateConns

  -- Sign-extend DynamicBitLinear output to accBits for ScaleMultiply
  let gateResultSE ← signExtendExpr
    { expr := .ref _gateResultRaw, width := dynOutputWidth } accBits
  let _gateResult ← makeWire "gate_result" (.bitVector accBits)
  emitAssign _gateResult gateResultSE.expr

  -- Gate scale
  let _gateScaled ← makeWire "gate_scaled" (.bitVector actTotalBits)
  emitInstance "ScaleMultiply" "u_gate_scale" [
    (genCfg.clockName, .ref genCfg.clockName),
    (genCfg.resetName, .ref genCfg.resetName),
    ("acc", .ref _gateResult),
    ("scale", .ref gateScaleW),
    ("result", .ref _gateScaled)
  ]

  -- Gate ReLU²
  let _gateRelu ← makeWire "gate_relu" (.bitVector actTotalBits)
  emitInstance "ReLUSq" "u_gate_relusq" [
    ("x", .ref _gateScaled),
    ("y", .ref _gateRelu)
  ]

  -- Up path: DynamicBitLinear + Scale
  let mut upConns : List (String × Expr) := [
    (genCfg.clockName, .ref genCfg.clockName),
    (genCfg.resetName, .ref genCfg.resetName)
  ]
  for j in [:cfg.dim] do
    upConns := upConns ++ [
      (s!"w_{j}", .ref upWWires[j]!),
      (s!"act_{j}", .ref _actReg)
    ]

  let _upResultRaw ← makeWire "up_result_raw" (.bitVector dynOutputWidth)
  upConns := upConns ++ [("result", .ref _upResultRaw)]
  emitInstance s!"DynamicBitLinear_{cfg.dim}" "u_up_dyn" upConns

  let upResultSE ← signExtendExpr
    { expr := .ref _upResultRaw, width := dynOutputWidth } accBits
  let _upResult ← makeWire "up_result" (.bitVector accBits)
  emitAssign _upResult upResultSE.expr

  let _upScaled ← makeWire "up_scaled" (.bitVector actTotalBits)
  emitInstance "ScaleMultiply" "u_up_scale" [
    (genCfg.clockName, .ref genCfg.clockName),
    (genCfg.resetName, .ref genCfg.resetName),
    ("acc", .ref _upResult),
    ("scale", .ref upScaleW),
    ("result", .ref _upScaled)
  ]

  -- Element-wise multiply (gate × up)
  let _elemMulOut ← makeWire "elem_mul_out" (.bitVector actTotalBits)
  emitInstance "ElemMul" "u_elem_mul" [
    ("a", .ref _gateRelu),
    ("b", .ref _upScaled),
    ("y", .ref _elemMulOut)
  ]

  -- Down path: DynamicBitLinear + Scale
  let mut downConns : List (String × Expr) := [
    (genCfg.clockName, .ref genCfg.clockName),
    (genCfg.resetName, .ref genCfg.resetName)
  ]
  for j in [:cfg.dim] do
    downConns := downConns ++ [
      (s!"w_{j}", .ref downWWires[j]!),
      (s!"act_{j}", .ref _elemMulOut)
    ]

  let _downResultRaw ← makeWire "down_result_raw" (.bitVector dynOutputWidth)
  downConns := downConns ++ [("result", .ref _downResultRaw)]
  emitInstance s!"DynamicBitLinear_{cfg.dim}" "u_down_dyn" downConns

  let downResultSE ← signExtendExpr
    { expr := .ref _downResultRaw, width := dynOutputWidth } accBits
  let _downResult ← makeWire "down_result" (.bitVector accBits)
  emitAssign _downResult downResultSE.expr

  let _downScaled ← makeWire "down_scaled" (.bitVector actTotalBits)
  emitInstance "ScaleMultiply" "u_down_scale" [
    (genCfg.clockName, .ref genCfg.clockName),
    (genCfg.resetName, .ref genCfg.resetName),
    ("acc", .ref _downResult),
    ("scale", .ref downScaleW),
    ("result", .ref _downScaled)
  ]

  -- Residual add (act_reg + down_scaled)
  let _residOut ← makeWire "resid_out" (.bitVector actTotalBits)
  emitInstance "ResidualAdd" "u_residual" [
    ("a", .ref _actReg),
    ("b", .ref _downScaled),
    ("y", .ref _residOut)
  ]

  -- Layer counter increment
  let layerInc ← makeWire "layer_inc" (.bitVector layerBits)
  emitAssign layerInc (Expr.add (.ref _layerReg) (.const 1 layerBits))

  -- Layer counter at max
  let layerDone ← makeWire "layer_done" (.bitVector 1)
  emitAssign layerDone (Expr.op .eq [.ref _layerReg, .const (cfg.nLayers - 1) layerBits])

  -- State conditions
  let isIdle := Expr.op .eq [.ref _stateReg, .const sIdle stateBits]
  let isCompute := Expr.op .eq [.ref _stateReg, .const sCompute stateBits]
  let isNextLayer := Expr.op .eq [.ref _stateReg, .const sNextLayer stateBits]
  let isDone := Expr.op .eq [.ref _stateReg, .const sDone stateBits]

  -- FSM next-state logic
  let idleNext := Expr.mux (.ref "start")
    (.const sCompute stateBits)
    (.const sIdle stateBits)

  let computeNext := Expr.const sNextLayer stateBits

  let nextLayerNext := Expr.mux (.ref layerDone)
    (.const sDone stateBits)
    (.const sCompute stateBits)

  let doneNext := Expr.const sIdle stateBits

  emitAssign stateNext
    (Expr.mux isIdle idleNext
      (Expr.mux isCompute computeNext
        (Expr.mux isNextLayer nextLayerNext
          (Expr.mux isDone doneNext
            (.const sIdle stateBits)))))

  -- Layer counter next
  emitAssign layerNext
    (Expr.mux (Expr.op .and [isIdle, .ref "start"])
      (.const 0 layerBits)  -- Reset on start
      (Expr.mux isNextLayer
        (.ref layerInc)      -- Increment after each layer
        (.ref _layerReg)))   -- Hold

  -- Activation register next
  emitAssign actNext
    (Expr.mux (Expr.op .and [isIdle, .ref "start"])
      (.ref "x_in")          -- Load input on start
      (Expr.mux isNextLayer
        (.ref _residOut)      -- Update with layer output
        (.ref _actReg)))      -- Hold

  -- Output assignments
  emitAssign "y_out" (.ref _actReg)
  emitAssign "done" isDone

-- ============================================================================
-- Top-level SoC Builder
-- ============================================================================

/-- Generate the SoC in the selected architecture mode -/
def generateBitNetSoC (cfg : SoCConfig) (layerWeights : Array LayerWeights)
    (layerScales : Array LayerScales) (genCfg : GeneratorConfig) : CircuitM Unit :=
  match cfg.archMode with
  | .HardwiredUnrolled => generateHardwiredSoC cfg layerWeights layerScales genCfg
  | .TimeMultiplexed => generateTimeMultiplexedSoC cfg layerWeights layerScales genCfg

/-- Build a complete SoC module -/
def buildBitNetSoC (cfg : SoCConfig) (layerWeights : Array LayerWeights)
    (layerScales : Array LayerScales) (genCfg : GeneratorConfig) : Module :=
  let suffix := match cfg.archMode with
    | .HardwiredUnrolled => "HW"
    | .TimeMultiplexed => "TM"
  CircuitM.runModule s!"BitNet_SoC_{suffix}_{cfg.nLayers}L_{cfg.dim}d" do
    generateBitNetSoC cfg layerWeights layerScales genCfg

end Sparkle.Examples.BitNet.SoC
