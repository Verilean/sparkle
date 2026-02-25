# YOLOv8n-WorldV2 RTL — TODO List

## Phase 0: Infrastructure & Python Golden Value Pipeline

- [x] **0.1** Write `scripts/yolo_golden_gen.py`
  - Load `yolov8s-worldv2.pt` via ultralytics (nano variant unavailable)
  - Post-training quantize: INT4 weights / INT8 activations
  - Fold BatchNorm into conv weights
  - Hook layers, capture intermediate activations on 160x160 test image
  - Export per-layer `.bin` files (weights, biases, scales, activations)
  - Export `input_image.bin`, `detection_output.bin`
  - Generated 69 conv layers, 207 weight files, 68 activation files (9.8MB)

- [x] **0.2** Create `Examples/YOLOv8/Config.lean`
  - Model dimensions (channels per stage, kernel sizes, layer count)

- [x] **0.3** Create `Examples/YOLOv8/Types.lean`
  - Type aliases: `WeightInt4`, `ActivationInt8`, `Accumulator`, `ScaleShift`

- [x] **0.4** Create `Tests/YOLOv8/GoldenLoader.lean`
  - Binary file loading (`.bin`), cosine similarity, max abs error metrics
  - `loadInt8Array`, `loadInt4Array`, `loadInt32Array`, `loadFloat32Array`
  - `maxAbsError`, `meanAbsError`, `cosineSimilarity`, `cosineSimilarityInt8`

- [x] **0.5** Update `lakefile.lean`
  - Add `lean_lib Examples.YOLOv8` with roots

---

## Phase 1: Primitive Building Blocks

- [x] **1.1** `Examples/YOLOv8/Primitives/Dequant.lean` — INT4→INT8 sign extension
- [x] **1.2** `Examples/YOLOv8/Primitives/Requantize.lean` — INT32→INT8 multiply-shift-clamp
- [x] **1.3** `Examples/YOLOv8/Primitives/Activation.lean` — ReLU + SiLU (ROM LUT)
- [x] **1.4** `Examples/YOLOv8/Primitives/Conv2DEngine.lean` — Sequential MAC engine (Signal.loop FSM)
- [x] **1.5** `Examples/YOLOv8/Primitives/LineBuffer.lean` — 3-row line buffer (Signal.memory)
- [x] **1.6** `Examples/YOLOv8/Primitives/MaxPool.lean` — 2x2 max pooling
- [x] **1.7** `Examples/YOLOv8/Primitives/Upsample.lean` — 2x nearest-neighbor (**synthesizes to Verilog**)

### Phase 1 Tests
- [x] **1.T1** `Tests/YOLOv8/TestDequant.lean` — 7/7 pass (sign extension, packed, full pipeline)
- [x] **1.T2** `Tests/YOLOv8/TestRequantize.lean` — 4/4 pass (positive, small, negative, zero)
- [x] **1.T3** `Tests/YOLOv8/TestActivation.lean` — 5/5 pass (ReLU: positive, negative, zero, max, min)
- [x] **1.T4** `Tests/YOLOv8/TestConv2D.lean` — Written (Signal.loop causes stack overflow; needs loopMemo)
- [x] **1.T5** `Tests/YOLOv8/TestMaxPool.lean` — 4/4 pass (positive, mixed, negative, identical)
- [x] **1.T6** `Tests/YOLOv8/TestUpsample.lean` — Written (Signal.loop causes stack overflow; needs loopMemo)

### Golden Value Validation
- [x] **1.G1** `Tests/YOLOv8/TestGoldenValues.lean` — 9/9 pass
  - Binary file loading (weights, biases, activations, input image)
  - Dequantization of golden INT4 weights
  - Self-similarity metric validation
  - Layer weight diversity check

---

## Phase 2: Composite Blocks

- [x] **2.1** `Examples/YOLOv8/Blocks/ConvBnSiLU.lean` — Fused Conv+BN+SiLU
- [x] **2.2** `Examples/YOLOv8/Blocks/Bottleneck.lean` — 1x1→3x3 bottleneck + residual
- [x] **2.3** `Examples/YOLOv8/Blocks/C2f.lean` — Cross Stage Partial block
- [x] **2.4** `Examples/YOLOv8/Blocks/SPPF.lean` — Spatial Pyramid Pooling Fast

### Phase 2 Tests
- [ ] **2.T1** `Tests/YOLOv8/TestBottleneck.lean` — Cosine sim ≥ 0.999
- [ ] **2.T2** `Tests/YOLOv8/TestC2f.lean` — Cosine sim ≥ 0.999

---

## Phase 3: Backbone

- [x] **3.1** `Examples/YOLOv8/Backbone.lean` — Controller FSM for 5 stages
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

- [x] **4.1** `Examples/YOLOv8/Neck.lean` — FPN top-down + PAN bottom-up

### Phase 4 Tests
- [ ] **4.T1** `Tests/YOLOv8/TestNeck.lean` — Cosine sim ≥ 0.99

---

## Phase 5: Detection Head

- [x] **5.1** `Examples/YOLOv8/Head.lean` — Decoupled head (**synthesizes to Verilog**)
- [x] **5.2** `Examples/YOLOv8/TextEmbedding.lean` — CLIP text embedding ROM + dot product

### Phase 5 Tests
- [ ] **5.T1** `Tests/YOLOv8/TestHead.lean` — Cosine sim ≥ 0.99

---

## Phase 6: Top-Level Integration

- [x] **6.1** `Examples/YOLOv8/Top.lean` — Full SoC (**synthesizes to Verilog**)
- [ ] **6.2** Verilog synthesis (`#synthesizeVerilog` per module)
  - 3/15 modules synthesize: upsample2x, headController, yolov8nTop
  - 12/15 need pattern refactoring (replace `decide`/`signExtend` with MSB checks)

### Phase 6 Tests
- [ ] **6.T1** `Tests/YOLOv8/TestEndToEnd.lean` — Detection mAP within 10% of float

---

## Cross-Cutting

- [x] Update `Tests/AllTests.lean` to include YOLOv8 test suite
- [x] Verify `lake build` compiles all modules (155 jobs)
- [x] Verify `lake test` passes all YOLOv8 tests (20 primitive + 9 golden = 29 pass)
- [ ] Verify `#synthesizeVerilog` on each primitive generates valid Verilog
  - Needs: refactor `decide` in lambdas → MSB bit-check pattern
  - Needs: refactor `.map (BitVec.signExtend ·)` → explicit bit concat
  - Needs: refactor `ashr` → synthesizable shift pattern

## Known Issues

- **Stack overflow with Signal.loop tests**: TestConv2D and TestUpsample use `Signal.loop`
  and `atTime` evaluation causes stack overflow. Fix: use `Signal.loopMemo` for simulation.
- **12/15 modules unsynthesizable**: Patterns like `decide`, `signExtend`, `ashr` not
  supported by `#synthesizeVerilog`. Need refactoring to use MSB-check comparisons
  and explicit bit concatenation.
