# YOLOv8n-WorldV2 RTL Implementation Plan

## Context

We are implementing YOLOv8n-WorldV2 (open-vocabulary object detection) as synthesizable RTL using Sparkle's Signal DSL (Lean 4 → Verilog). The goal is a complete hardware inference accelerator with:
- **Golden values** from Python (ultralytics YOLOWorld) for validation
- **LSpec tests** comparing RTL simulation output vs Python golden values
- **Weights stored in ROM** via `Signal.memoryWithInit`

### Design Decisions
- **Model**: YOLOv8n-WorldV2 (~3.2M params, same arch as YOLOv8s but reduced channels)
- **Input**: 160x160x3 (RGB)
- **Quantization**: Mixed INT4 weights / INT8 activations, INT32 accumulator
- **Text encoder**: Pre-compute CLIP text embeddings in Python, store as ROM
- **Architecture**: Time-multiplexed single conv engine (following BitNet SoC pattern)

---

## Phase 0: Infrastructure & Python Golden Value Pipeline

### 0.1 Python: `scripts/yolo_golden_gen.py`
- Load `yolov8n-worldv2.pt` via `ultralytics.YOLOWorld`
- Post-training quantize: INT4 weights (per-channel), INT8 activations (per-tensor)
- Fold BatchNorm into conv weights offline (eliminates runtime division)
- Hook each layer to capture intermediate activations on a 160x160 test image
- Export per-layer:
  - `weights/layer_XX_weights.bin` — INT4 packed (2 weights per byte)
  - `weights/layer_XX_bias.bin` — INT32 pre-scaled biases
  - `weights/layer_XX_scale.bin` — requantization scale + shift (multiply-shift replaces division)
  - `activations/layer_XX_input.bin` — INT8 input activations
  - `activations/layer_XX_output.bin` — INT8 output activations
  - `text_embeddings.bin` — Pre-computed CLIP text embeddings (INT8)
  - `input_image.bin` — INT8 quantized 160x160x3 input
  - `detection_output.bin` — Final bounding boxes + class scores
- Also export `.hex` files for `Signal.memoryWithInit` / `$readmemh`

### 0.2 Lean infrastructure
- **`Examples/YOLOv8/Config.lean`** — Model dimensions (channels per stage, kernel sizes, layer count)
- **`Examples/YOLOv8/Types.lean`** — Type aliases:
  ```
  abbrev WeightInt4 := BitVec 4      -- signed 4-bit weight
  abbrev ActivationInt8 := BitVec 8  -- signed 8-bit activation
  abbrev Accumulator := BitVec 32    -- INT32 accumulator
  abbrev ScaleShift := BitVec 16     -- requantization scale
  ```
- **`Tests/YOLOv8/GoldenLoader.lean`** — Load `.bin` files (reuse `RTLGoldenValidation.lean` patterns: `loadFloatArrayFromFile`, binary loading, cosine similarity metrics)
- **`lakefile.lean`** — Add `lean_lib Examples.YOLOv8` and `lean_exe yolov8-test`

### Key files to reuse
- `Tests/BitNet/RTLGoldenValidation.lean` — Binary file loading, cosine similarity, test reporting pattern
- `Sparkle/Utils/HexLoader.lean` — `$readmemh` format loading
- `Examples/BitNet/Config.lean` — Config struct pattern

---

## Phase 1: Primitive Building Blocks

### 1.1 INT4 Dequantization — `Examples/YOLOv8/Primitives/Dequant.lean`
INT4 weights are stored packed (2 per byte). At runtime, dequantize INT4 → INT8 by sign-extension before MAC:
```lean
def dequantInt4ToInt8 (w4 : Signal dom (BitVec 4)) : Signal dom (BitVec 8) :=
  -- Sign-extend 4-bit to 8-bit (reuse signExtendSignal from SignalHelpers)
  signExtendSignal 4 w4
```

### 1.2 Requantization — `Examples/YOLOv8/Primitives/Requantize.lean`
After accumulation, convert INT32 → INT8 using multiply-and-shift (no division):
```lean
def requantize (acc : Signal dom (BitVec 32))
    (scale : Signal dom (BitVec 16)) (shift : Signal dom (BitVec 5))
    : Signal dom (BitVec 8)
-- output = clamp((acc * scale) >> shift, -128, 127)
```
Pattern: `(· * ·) <$> acc <*> scale` then shift-right then clamp via `Signal.mux`.

### 1.3 Activation Functions — `Examples/YOLOv8/Primitives/Activation.lean`
- **ReLU** (trivial): `Signal.mux isNeg (Signal.pure 0#8) x`
- **SiLU** (ROM-based LUT): 128-entry sigmoid ROM via `Signal.memoryWithInit`, then multiply:
  `silu(x) = x * sigmoid_lut[|x|]`
  - Note: `Signal.memoryWithInit` has 1-cycle latency (registered read)

### 1.4 Conv2D MAC Engine — `Examples/YOLOv8/Primitives/Conv2DEngine.lean`
Sequential single-MAC engine (follows `Examples/RV32/Divider.lean` pattern):
```lean
Signal.loop fun state =>
  let accReg := projN! state 6 0       -- BitVec 32 accumulator
  let macCounter := projN! state 6 1   -- counts through kernel*Cin
  let fsmState := projN! state 6 2     -- IDLE/ACCUMULATE/REQUANTIZE/OUTPUT
  let resultReg := projN! state 6 3    -- BitVec 8 output
  let doneFlag := projN! state 6 4     -- Bool
  let channelCtr := projN! state 6 5   -- output channel counter
  -- MAC: acc += dequant(weight_int4) * activation_int8
  -- ... FSM via Signal.mux cascade ...
  bundleAll! [Signal.register ... , ...]
```

### 1.5 Line Buffer — `Examples/YOLOv8/Primitives/LineBuffer.lean`
3-row line buffer for 3x3 convolutions using `Signal.memory`:
- Two `Signal.memory` instances (each stores one row of width 160)
- 9 registers for the 3x3 sliding window
- Position counters for row/column tracking

### 1.6 Max Pooling 2x2 — `Examples/YOLOv8/Primitives/MaxPool.lean`
1-line buffer + 2x2 signed comparison tree (reuse `maxTree` from `Examples/BitNet/SignalHelpers.lean`)

### 1.7 Nearest-Neighbor Upsample 2x — `Examples/YOLOv8/Primitives/Upsample.lean`
FSM: duplicate each pixel horizontally, repeat each row. Uses column/row counters.

### Key files to reuse
- `Examples/BitNet/SignalHelpers.lean` — `signExtendSignal`, `adderTree`, `maxTree`, `lutMuxTree`
- `Examples/RV32/Divider.lean` — Multi-cycle FSM with `Signal.loop`, `projN!`/`bundleAll!` pattern
- `Sparkle/Core/Signal.lean` — `Signal.memory`, `Signal.memoryWithInit`, `Signal.register`

---

## Phase 2: Composite Blocks

### 2.1 ConvBnSiLU — `Examples/YOLOv8/Blocks/ConvBnSiLU.lean`
Fused Conv + BatchNorm (folded into weights) + SiLU activation. This is the fundamental YOLOv8 building block. Composes: Conv2DEngine → Requantize → SiLU.

### 2.2 Bottleneck — `Examples/YOLOv8/Blocks/Bottleneck.lean`
1x1 ConvBnSiLU → 3x3 ConvBnSiLU, with optional residual connection (add input to output).

### 2.3 C2f Block — `Examples/YOLOv8/Blocks/C2f.lean`
Cross Stage Partial with 2 convolutions:
1. 1x1 conv splits channels
2. N bottleneck blocks on one half
3. Concatenate all intermediate outputs
4. Final 1x1 conv to merge
Controller FSM manages the data flow through these sub-operations.

### 2.4 SPPF — `Examples/YOLOv8/Blocks/SPPF.lean`
Spatial Pyramid Pooling - Fast: three sequential 5x5 max pools (reuse MaxPool engine 3 times with controller), then channel concatenation + 1x1 conv.

---

## Phase 3: YOLOv8n Backbone

### `Examples/YOLOv8/Backbone.lean`
Controller FSM sequences through backbone layers:
```
Stage 0: Conv 3x3, 3→16 channels (stem)
Stage 1: Conv 3x3 s2, 16→32 + C2f(32, n=1)  → P1
Stage 2: Conv 3x3 s2, 32→64 + C2f(64, n=2)  → P2/P3
Stage 3: Conv 3x3 s2, 64→128 + C2f(128, n=2) → P4
Stage 4: Conv 3x3 s2, 128→256 + C2f(256, n=1) + SPPF → P5
```

### Weight ROMs
- INT4 weights: ~3.2M params × 4 bits = ~1.6MB total
- Split across multiple `Signal.memoryWithInit` ROMs (one per stage or per conv layer)
- Each ROM has `addrWidth ≤ 20` (1M entries max)
- At INT4 packed (2 per byte), 1M entries = 2M weights per ROM — sufficient for any single layer

### Activation Buffers
- Double-buffered `Signal.memory` for ping-pong:
  - Buffer A: read current layer's input
  - Buffer B: write current layer's output
  - Swap after each layer
- Max single-layer: 160×160×64 = 1,638,400 bytes → needs `addrWidth = 21`
  - **Solution**: Process channels in groups (e.g., 16 at a time), reducing buffer to 160×160×16 = 409,600 (addrWidth=19)

---

## Phase 4: Neck (FPN + PAN)

### `Examples/YOLOv8/Neck.lean`
Feature Pyramid Network + Path Aggregation:
```
P5 → Upsample 2x → Concat(P4) → C2f → N4
N4 → Upsample 2x → Concat(P3) → C2f → N3   (FPN top-down)
N3 → Conv s2      → Concat(N4) → C2f → N4'
N4'→ Conv s2      → Concat(P5) → C2f → N5'  (PAN bottom-up)
```
Reuses the same conv engine, line buffer, and upsample primitives from Phase 1-2. Controller FSM manages the multi-scale data routing.

---

## Phase 5: Detection Head

### `Examples/YOLOv8/Head.lean`
Decoupled detection head at 3 scales (N3, N4', N5'):
- **Bbox regression branch**: 2× Conv 3x3 → Conv 1x1 → 4×(reg_max+1) outputs
- **Classification branch**: 2× Conv 3x3 → Conv 1x1 → num_classes outputs
- **Text embedding dot product**: pre-computed CLIP embeddings in ROM, dot product for open-vocabulary classification (reuse `adderTree` from SignalHelpers)

### Text Embedding ROM — `Examples/YOLOv8/TextEmbedding.lean`
- Pre-computed CLIP text embeddings stored as INT8 in `Signal.memoryWithInit`
- Classification = dot product between visual features and text embeddings
- Pattern follows BitNet's `dynamicMACStage` but with INT8×INT8 instead of ternary

---

## Phase 6: Top-Level Integration

### `Examples/YOLOv8/Top.lean`
Full SoC following `Examples/BitNet/SoC/Top.lean` pattern:
```lean
def yolov8nWorldV2 {dom : DomainConfig}
    (pixelIn : Signal dom (BitVec 8))
    (pixelValid : Signal dom Bool)
    : Signal dom (DetectionOutput) :=
  Signal.loop fun state =>
    -- ~25-30 state registers: layer_idx, phase, counters, buffer_sel, FSM
    let layerIdx := projN! state N 0
    let phase := projN! state N 1
    -- ... controller FSM sequences through all layers ...
    bundleAll! [Signal.register ..., ...]
```

Use `Signal.loopMemo` for simulation (following RV32 SoC pattern to avoid stack overflow).

### Verilog synthesis
```lean
#synthesizeVerilog yolov8nWorldV2
```
Synthesize sub-modules individually if full model hits `maxHeartbeats` limits.

---

## Testing Strategy

### Layer-by-layer golden value tests (`Tests/YOLOv8/`)

Each test file follows the `RTLGoldenValidation.lean` pattern:
1. Load golden input/output from `.bin` files
2. Construct the Signal DSL circuit
3. Simulate for N cycles using `.atTime`
4. Compare output vs golden values

| Test File | What it tests | Pass criteria |
|-----------|--------------|---------------|
| `TestDequant.lean` | INT4→INT8 dequantization | Exact match |
| `TestRequantize.lean` | INT32→INT8 multiply-shift-clamp | Exact match |
| `TestActivation.lean` | ReLU, SiLU LUT approximation | Max abs error < 2 LSB |
| `TestConv2D.lean` | 1x1 and 3x3 conv engine | Exact match (integer arithmetic) |
| `TestMaxPool.lean` | 2x2 max pooling | Exact match |
| `TestUpsample.lean` | 2x nearest-neighbor upsampling | Exact match |
| `TestBottleneck.lean` | Bottleneck block | Cosine similarity ≥ 0.999 |
| `TestC2f.lean` | C2f block | Cosine similarity ≥ 0.999 |
| `TestBackbone.lean` | Full backbone (image → P3/P4/P5) | Cosine similarity ≥ 0.99 |
| `TestNeck.lean` | FPN + PAN | Cosine similarity ≥ 0.99 |
| `TestHead.lean` | Detection head + text embedding | Cosine similarity ≥ 0.99 |
| `TestEndToEnd.lean` | Full image → detections | Detection mAP within 10% of float |

### LSpec test structure
```lean
def testConv3x3 : IO LSpec.TestSeq := do
  let goldenIn ← loadInt8Array "Tests/yolo-golden/conv3x3_input.bin"
  let goldenOut ← loadInt8Array "Tests/yolo-golden/conv3x3_output.bin"
  let goldenWeights ← loadInt4Array "Tests/yolo-golden/conv3x3_weights.bin"
  -- Build circuit, simulate, compare
  return LSpec.test "conv3x3 output matches golden" (maxAbsError < 2)
```

---

## File Structure Summary

```
Examples/YOLOv8/
├── Config.lean                  -- Model dimensions, quantization params
├── Types.lean                   -- Type aliases (WeightInt4, ActivationInt8, etc.)
├── Primitives/
│   ├── Dequant.lean             -- INT4 → INT8 sign extension
│   ├── Requantize.lean          -- INT32 → INT8 multiply-shift-clamp
│   ├── Activation.lean          -- ReLU, SiLU (ROM LUT)
│   ├── Conv2DEngine.lean        -- Sequential MAC engine (Signal.loop)
│   ├── LineBuffer.lean          -- 3-row line buffer (Signal.memory)
│   ├── MaxPool.lean             -- 2x2 max pooling
│   └── Upsample.lean            -- 2x nearest-neighbor
├── Blocks/
│   ├── ConvBnSiLU.lean          -- Fused Conv+BN+SiLU
│   ├── Bottleneck.lean          -- 1x1 → 3x3 bottleneck
│   ├── C2f.lean                 -- Cross Stage Partial
│   └── SPPF.lean                -- Spatial Pyramid Pooling Fast
├── Backbone.lean                -- Backbone controller FSM
├── Neck.lean                    -- FPN + PAN
├── Head.lean                    -- Detection head
├── TextEmbedding.lean           -- CLIP text embedding ROM + dot product
└── Top.lean                     -- Full SoC top-level

Tests/YOLOv8/
├── GoldenLoader.lean            -- Binary file loading, metrics
├── TestDequant.lean
├── TestRequantize.lean
├── TestActivation.lean
├── TestConv2D.lean
├── TestMaxPool.lean
├── TestUpsample.lean
├── TestBottleneck.lean
├── TestC2f.lean
├── TestBackbone.lean
├── TestNeck.lean
├── TestHead.lean
└── TestEndToEnd.lean

scripts/
└── yolo_golden_gen.py           -- Python golden value generator
```

## Verification
1. `python scripts/yolo_golden_gen.py` — Generate golden values
2. `lake build` — Compile all Lean modules
3. `lake test` — Run LSpec tests (AllTests.lean updated to include YOLOv8 tests)
4. `#synthesizeVerilog` on each primitive — Verify Verilog generation
5. Compare RTL simulation output at each layer against Python golden `.bin` files
