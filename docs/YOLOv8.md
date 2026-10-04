# YOLOv8n-WorldV2: Object Detection Accelerator
## YOLOv8n-WorldV2: Open-Vocabulary Object Detection Accelerator

A **complete YOLOv8n-WorldV2 inference accelerator** — all 15 modules synthesize to Verilog from the same Lean 4 Signal DSL. INT4 weights / INT8 activations with pre-computed CLIP text embeddings for open-vocabulary detection.

### Architecture

```
160x160x3 RGB ──► Backbone (5 stages) ──► Neck (FPN+PAN) ──► Head (3 scales) ──► Detections
                     │                        │                    │
                     ├─ Conv 3x3 stem         ├─ Upsample 2x      ├─ Bbox regression
                     ├─ C2f blocks            ├─ Concat            ├─ Classification
                     └─ SPPF                  └─ C2f               └─ CLIP text dot product
```

**Key specs:**
- **Input**: 160x160x3 RGB (INT8 quantized)
- **Quantization**: INT4 weights (packed 2 per byte) / INT8 activations / INT32 accumulators
- **Backbone**: 5 stages — Conv stem → 4x (Conv stride-2 + C2f) + SPPF, producing P3/P4/P5
- **Neck**: FPN top-down (P5→P4→P3) + PAN bottom-up (N3→N4'→N5')
- **Head**: Decoupled detection at 3 scales with CLIP text embedding dot product
- **All 15 modules synthesize** to SystemVerilog via `#synthesizeVerilog`

### Module Hierarchy (15 synthesizable modules)

| Module | Description | Key technique |
|--------|-------------|---------------|
| `dequantPacked` | INT4→INT8 sign extension | MSB check + bit concat |
| `requantize` | INT32→INT8 multiply-shift-clamp | `BitVec.slt` + `ashr` |
| `relu` | ReLU activation | MSB extraction |
| `siluLut` | SiLU via 256-entry ROM LUT | `lutMuxTree` |
| `conv2DEngine` | Sequential MAC engine | `Signal.loop` FSM |
| `lineBuffer3x3` | 3-row sliding window | `Signal.memory` |
| `maxPool2x2` | 2x2 signed max pooling | `BitVec.slt` |
| `upsample2x` | 2x nearest-neighbor | Counter FSM |
| `convBnSiLU` | Fused Conv+BN+SiLU | Composes primitives |
| `bottleneckController` | 1x1→3x3 + residual | FSM sequencer |
| `c2fController` | Cross Stage Partial | N-bottleneck loop |
| `sppfController` | Spatial Pyramid Pooling | 3-pass max pool |
| `backboneController` | 5-stage backbone FSM | Stage sequencer |
| `neckController` | FPN+PAN sequencer | Bidirectional path |
| `headController` | 3-scale detection head | Scale/branch FSM |
| `yolov8nTop` | Full SoC top-level | Master controller |
| `dotProductEngine` | INT8 dot product for CLIP | MAC accumulator |

### Golden Value Validation

Golden values extracted from real YOLOv8s-WorldV2 model (ultralytics) with INT4/INT8 quantization:

```
--- YOLOv8 Golden Value Validation ---
  [PASS] Golden value files exist (weights, biases, activations, input image)
  [PASS] INT4 weight dequantization preserves signed values
  [PASS] Cosine self-similarity = 1.0
  [PASS] Layer weight diversity check
  9/9 golden value tests pass
```

```python
# Generate golden values from Python
python scripts/yolo_golden_gen.py
# Produces 207 weight files + 68 activation files (9.8MB)
```

---
