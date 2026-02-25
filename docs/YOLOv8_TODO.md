# YOLOv8n-WorldV2 RTL — TODO List

## Phase 0: Infrastructure & Python Golden Value Pipeline

- [ ] **0.1** Write `scripts/yolo_golden_gen.py`
  - Load `yolov8n-worldv2.pt` via ultralytics
  - Post-training quantize: INT4 weights / INT8 activations
  - Fold BatchNorm into conv weights
  - Hook layers, capture intermediate activations on 160x160 test image
  - Export per-layer `.bin` and `.hex` files (weights, biases, scales, activations)
  - Export `text_embeddings.bin`, `input_image.bin`, `detection_output.bin`

- [ ] **0.2** Create `Examples/YOLOv8/Config.lean`
  - Model dimensions (channels per stage, kernel sizes, layer count)

- [ ] **0.3** Create `Examples/YOLOv8/Types.lean`
  - Type aliases: `WeightInt4`, `ActivationInt8`, `Accumulator`, `ScaleShift`

- [ ] **0.4** Create `Tests/YOLOv8/GoldenLoader.lean`
  - Binary file loading (`.bin`), cosine similarity, max abs error metrics
  - Reuse patterns from `Tests/BitNet/RTLGoldenValidation.lean`

- [ ] **0.5** Update `lakefile.lean`
  - Add `lean_lib Examples.YOLOv8` and test targets

---

## Phase 1: Primitive Building Blocks

- [ ] **1.1** `Examples/YOLOv8/Primitives/Dequant.lean` — INT4→INT8 sign extension
- [ ] **1.2** `Examples/YOLOv8/Primitives/Requantize.lean` — INT32→INT8 multiply-shift-clamp
- [ ] **1.3** `Examples/YOLOv8/Primitives/Activation.lean` — ReLU + SiLU (ROM LUT)
- [ ] **1.4** `Examples/YOLOv8/Primitives/Conv2DEngine.lean` — Sequential MAC engine (Signal.loop FSM)
- [ ] **1.5** `Examples/YOLOv8/Primitives/LineBuffer.lean` — 3-row line buffer (Signal.memory)
- [ ] **1.6** `Examples/YOLOv8/Primitives/MaxPool.lean` — 2x2 max pooling
- [ ] **1.7** `Examples/YOLOv8/Primitives/Upsample.lean` — 2x nearest-neighbor

### Phase 1 Tests
- [ ] **1.T1** `Tests/YOLOv8/TestDequant.lean` — Exact match vs golden
- [ ] **1.T2** `Tests/YOLOv8/TestRequantize.lean` — Exact match vs golden
- [ ] **1.T3** `Tests/YOLOv8/TestActivation.lean` — Max abs error < 2 LSB
- [ ] **1.T4** `Tests/YOLOv8/TestConv2D.lean` — Exact match (integer arith)
- [ ] **1.T5** `Tests/YOLOv8/TestMaxPool.lean` — Exact match
- [ ] **1.T6** `Tests/YOLOv8/TestUpsample.lean` — Exact match

---

## Phase 2: Composite Blocks

- [ ] **2.1** `Examples/YOLOv8/Blocks/ConvBnSiLU.lean` — Fused Conv+BN+SiLU
- [ ] **2.2** `Examples/YOLOv8/Blocks/Bottleneck.lean` — 1x1→3x3 bottleneck + residual
- [ ] **2.3** `Examples/YOLOv8/Blocks/C2f.lean` — Cross Stage Partial block
- [ ] **2.4** `Examples/YOLOv8/Blocks/SPPF.lean` — Spatial Pyramid Pooling Fast

### Phase 2 Tests
- [ ] **2.T1** `Tests/YOLOv8/TestBottleneck.lean` — Cosine sim ≥ 0.999
- [ ] **2.T2** `Tests/YOLOv8/TestC2f.lean` — Cosine sim ≥ 0.999

---

## Phase 3: Backbone

- [ ] **3.1** `Examples/YOLOv8/Backbone.lean` — Controller FSM for 5 stages
  - Stage 0: Conv 3x3, 3→16 (stem)
  - Stage 1: Conv 3x3 s2, 16→32 + C2f(32, n=1) → P1
  - Stage 2: Conv 3x3 s2, 32→64 + C2f(64, n=2) → P2/P3
  - Stage 3: Conv 3x3 s2, 64→128 + C2f(128, n=2) → P4
  - Stage 4: Conv 3x3 s2, 128→256 + C2f(256, n=1) + SPPF → P5
- [ ] **3.2** Weight ROMs — `Signal.memoryWithInit` per layer/stage
- [ ] **3.3** Double-buffered activation memory (ping-pong)

### Phase 3 Tests
- [ ] **3.T1** `Tests/YOLOv8/TestBackbone.lean` — Cosine sim ≥ 0.99

---

## Phase 4: Neck (FPN + PAN)

- [ ] **4.1** `Examples/YOLOv8/Neck.lean` — FPN top-down + PAN bottom-up
  - P5 → Upsample 2x → Concat(P4) → C2f → N4
  - N4 → Upsample 2x → Concat(P3) → C2f → N3
  - N3 → Conv s2 → Concat(N4) → C2f → N4'
  - N4' → Conv s2 → Concat(P5) → C2f → N5'

### Phase 4 Tests
- [ ] **4.T1** `Tests/YOLOv8/TestNeck.lean` — Cosine sim ≥ 0.99

---

## Phase 5: Detection Head

- [ ] **5.1** `Examples/YOLOv8/Head.lean` — Decoupled head (bbox + cls branches)
- [ ] **5.2** `Examples/YOLOv8/TextEmbedding.lean` — CLIP text embedding ROM + dot product

### Phase 5 Tests
- [ ] **5.T1** `Tests/YOLOv8/TestHead.lean` — Cosine sim ≥ 0.99

---

## Phase 6: Top-Level Integration

- [ ] **6.1** `Examples/YOLOv8/Top.lean` — Full SoC (Signal.loopMemo)
- [ ] **6.2** Verilog synthesis (`#synthesizeVerilog` per module)

### Phase 6 Tests
- [ ] **6.T1** `Tests/YOLOv8/TestEndToEnd.lean` — Detection mAP within 10% of float

---

## Cross-Cutting

- [ ] Update `Tests/AllTests.lean` to include YOLOv8 test suite
- [ ] Verify `lake build` compiles all modules
- [ ] Verify `lake test` passes all YOLOv8 tests
- [ ] Verify `#synthesizeVerilog` on each primitive generates valid Verilog
