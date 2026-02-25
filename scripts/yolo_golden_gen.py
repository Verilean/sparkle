#!/usr/bin/env python3
"""
YOLOv8n-WorldV2 Golden Value Generator

Generates golden values for RTL validation:
- Per-layer INT4 weights (packed), INT32 biases, requant scales
- Per-layer INT8 input/output activations
- Pre-computed CLIP text embeddings (INT8)
- Final detection outputs

Usage:
    pip install ultralytics torch numpy
    python scripts/yolo_golden_gen.py

Output directory: Tests/yolo-golden/
"""

import os
import struct
import numpy as np

# Try importing ultralytics, but allow script to work without it for testing
try:
    from ultralytics import YOLOWorld
    import torch
    import torch.nn as nn
    HAS_ULTRALYTICS = True
except ImportError:
    HAS_ULTRALYTICS = False
    print("WARNING: ultralytics not installed. Generating synthetic golden values.")

# ============================================================================
# Configuration
# ============================================================================

IMG_SIZE = 160
NUM_CHANNELS = 3
OUTPUT_DIR = "Tests/yolo-golden"

# YOLOv8n backbone channel widths
STAGE_CHANNELS = [16, 32, 64, 128, 256]

# ============================================================================
# Quantization Utilities
# ============================================================================

def quantize_int8(tensor: np.ndarray, per_tensor: bool = True) -> tuple:
    """Quantize float tensor to INT8 with scale factor.
    Returns (quantized_int8, scale, zero_point)."""
    if per_tensor:
        max_val = np.max(np.abs(tensor))
        scale = max_val / 127.0 if max_val > 0 else 1.0
    else:
        # Per-channel: quantize along axis 0
        max_val = np.max(np.abs(tensor), axis=tuple(range(1, tensor.ndim)), keepdims=True)
        scale = max_val / 127.0
        scale[scale == 0] = 1.0

    quantized = np.clip(np.round(tensor / scale), -128, 127).astype(np.int8)
    return quantized, scale.astype(np.float32)


def quantize_int4(tensor: np.ndarray) -> tuple:
    """Quantize float tensor to INT4 (per-channel) with scale factor.
    Returns (quantized_int4, scale). INT4 range: [-8, 7]."""
    # Per-channel quantization (axis 0 = output channels)
    if tensor.ndim >= 2:
        max_val = np.max(np.abs(tensor), axis=tuple(range(1, tensor.ndim)), keepdims=True)
    else:
        max_val = np.max(np.abs(tensor))
    scale = max_val / 7.0
    scale[scale == 0] = 1.0

    quantized = np.clip(np.round(tensor / scale), -8, 7).astype(np.int8)
    return quantized, scale.astype(np.float32)


def pack_int4(arr: np.ndarray) -> np.ndarray:
    """Pack INT4 values: two per byte (lower nibble first)."""
    flat = arr.flatten()
    if len(flat) % 2 != 0:
        flat = np.append(flat, 0)  # Pad with zero

    packed = np.zeros(len(flat) // 2, dtype=np.uint8)
    for i in range(0, len(flat), 2):
        lo = int(flat[i]) & 0x0F
        hi = int(flat[i + 1]) & 0x0F
        packed[i // 2] = lo | (hi << 4)
    return packed


def fold_batchnorm(conv_weight, conv_bias, bn_weight, bn_bias, bn_mean, bn_var, eps=1e-5):
    """Fold BatchNorm parameters into conv weights and biases.
    Returns (folded_weight, folded_bias)."""
    bn_std = np.sqrt(bn_var + eps)
    scale = bn_weight / bn_std

    if conv_weight.ndim == 4:
        # Conv2d: [out_ch, in_ch, kH, kW]
        folded_weight = conv_weight * scale.reshape(-1, 1, 1, 1)
    else:
        folded_weight = conv_weight * scale.reshape(-1, 1)

    if conv_bias is not None:
        folded_bias = (conv_bias - bn_mean) * scale + bn_bias
    else:
        folded_bias = -bn_mean * scale + bn_bias

    return folded_weight, folded_bias


def compute_requant_params(weight_scale, act_scale, target_scale):
    """Compute requantization multiply-shift parameters.
    output = clamp((acc * mult) >> shift, -128, 127)
    """
    combined_scale = (weight_scale * act_scale) / target_scale
    # Find shift such that mult fits in 16 bits
    shift = 0
    mult = combined_scale
    while mult < 1.0 and shift < 31:
        mult *= 2
        shift += 1

    mult_int = int(np.clip(np.round(mult), -32768, 32767))
    return mult_int, shift


# ============================================================================
# File I/O
# ============================================================================

def save_int8_bin(data: np.ndarray, path: str):
    """Save INT8 array as binary file."""
    data.astype(np.int8).tofile(path)


def save_int4_bin(data: np.ndarray, path: str):
    """Save packed INT4 array as binary file."""
    packed = pack_int4(data)
    packed.tofile(path)


def save_int32_bin(data: np.ndarray, path: str):
    """Save INT32 array as binary file (little-endian)."""
    data.astype(np.int32).tofile(path)


def save_float32_bin(data: np.ndarray, path: str):
    """Save float32 array as binary file."""
    data.astype(np.float32).tofile(path)


def save_hex(data: np.ndarray, path: str, width: int = 8):
    """Save array as hex file for $readmemh."""
    with open(path, 'w') as f:
        for val in data.flatten():
            if width == 8:
                f.write(f"{int(val) & 0xFF:02x}\n")
            elif width == 32:
                f.write(f"{int(val) & 0xFFFFFFFF:08x}\n")
            elif width == 4:
                f.write(f"{int(val) & 0xF:01x}\n")


# ============================================================================
# Golden Value Generation
# ============================================================================

def generate_synthetic_golden():
    """Generate synthetic golden values for testing when ultralytics is not available."""
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    os.makedirs(f"{OUTPUT_DIR}/weights", exist_ok=True)
    os.makedirs(f"{OUTPUT_DIR}/activations", exist_ok=True)

    np.random.seed(42)

    # Generate test input image (160x160x3, INT8)
    input_image = np.random.randint(-128, 128, (IMG_SIZE, IMG_SIZE, NUM_CHANNELS), dtype=np.int8)
    save_int8_bin(input_image, f"{OUTPUT_DIR}/input_image.bin")
    print(f"  Saved input image: {input_image.shape}")

    # Generate per-layer golden values for a simplified model
    layer_configs = [
        # (name, in_ch, out_ch, kernel_size, stride)
        ("stem", 3, 16, 3, 1),
        ("stage1_conv", 16, 32, 3, 2),
        ("stage1_c2f_cv1", 32, 32, 1, 1),
        ("stage1_c2f_bn0_cv1", 16, 16, 1, 1),
        ("stage1_c2f_bn0_cv2", 16, 16, 3, 1),
        ("stage1_c2f_cv2", 48, 32, 1, 1),
        ("stage2_conv", 32, 64, 3, 2),
        ("stage2_c2f_cv1", 64, 64, 1, 1),
        ("stage3_conv", 64, 128, 3, 2),
        ("stage3_c2f_cv1", 128, 128, 1, 1),
        ("stage4_conv", 128, 256, 3, 2),
        ("stage4_c2f_cv1", 256, 256, 1, 1),
        ("sppf_cv1", 256, 128, 1, 1),
        ("sppf_cv2", 512, 256, 1, 1),
    ]

    for idx, (name, in_ch, out_ch, ks, stride) in enumerate(layer_configs):
        # Random weights (will be replaced by real model weights)
        weights_float = np.random.randn(out_ch, in_ch, ks, ks).astype(np.float32) * 0.1
        bias_float = np.random.randn(out_ch).astype(np.float32) * 0.01

        # Quantize
        weights_int4, w_scale = quantize_int4(weights_float)
        bias_int32 = np.round(bias_float / (w_scale.flatten() * (1.0/127.0))).astype(np.int32)

        # Requant params
        mult_int = 64  # placeholder
        shift_val = 6  # placeholder
        scale_data = np.array([mult_int], dtype=np.int16)
        shift_data = np.array([shift_val], dtype=np.int8)

        # Save weights
        save_int4_bin(weights_int4, f"{OUTPUT_DIR}/weights/layer_{idx:02d}_weights.bin")
        save_int32_bin(bias_int32, f"{OUTPUT_DIR}/weights/layer_{idx:02d}_bias.bin")
        save_float32_bin(w_scale, f"{OUTPUT_DIR}/weights/layer_{idx:02d}_scale.bin")

        # Random activations
        h = IMG_SIZE // (2 ** min(idx, 4))
        w = h
        input_act = np.random.randint(-128, 128, (h, w, in_ch), dtype=np.int8)
        output_act = np.random.randint(-128, 128, (h // stride, w // stride, out_ch), dtype=np.int8)
        save_int8_bin(input_act, f"{OUTPUT_DIR}/activations/layer_{idx:02d}_input.bin")
        save_int8_bin(output_act, f"{OUTPUT_DIR}/activations/layer_{idx:02d}_output.bin")

        print(f"  Layer {idx:02d} ({name}): {in_ch}→{out_ch}, k={ks}, s={stride}")

    # Generate text embeddings (80 classes × 512 dims, INT8)
    text_embeddings = np.random.randint(-128, 128, (80, 512), dtype=np.int8)
    save_int8_bin(text_embeddings, f"{OUTPUT_DIR}/text_embeddings.bin")
    print(f"  Saved text embeddings: {text_embeddings.shape}")

    # Generate dummy detection output
    num_detections = 10
    # [x1, y1, x2, y2, score, class_id] per detection
    detection_output = np.random.rand(num_detections, 6).astype(np.float32)
    detection_output[:, :4] *= IMG_SIZE  # Scale bbox to image size
    detection_output[:, 4] = np.random.rand(num_detections)  # Confidence
    detection_output[:, 5] = np.random.randint(0, 80, num_detections)  # Class
    save_float32_bin(detection_output, f"{OUTPUT_DIR}/detection_output.bin")
    print(f"  Saved detection output: {detection_output.shape}")


def generate_real_golden():
    """Generate golden values from the real YOLOv8n-WorldV2 model."""
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    os.makedirs(f"{OUTPUT_DIR}/weights", exist_ok=True)
    os.makedirs(f"{OUTPUT_DIR}/activations", exist_ok=True)

    print("Loading YOLOv8s-WorldV2 (auto-downloads if not present)...")
    model = YOLOWorld("yolov8s-worldv2.pt")
    model.set_classes(["person", "car", "dog", "cat", "bicycle"])

    # Generate test image
    np.random.seed(42)
    test_image = np.random.randint(0, 256, (IMG_SIZE, IMG_SIZE, 3), dtype=np.uint8)

    # Quantize input to INT8
    input_int8 = (test_image.astype(np.float32) / 255.0 * 254 - 128).astype(np.int8)
    save_int8_bin(input_int8, f"{OUTPUT_DIR}/input_image.bin")

    # Hook layers to capture activations
    activations = {}
    hooks = []

    def make_hook(name):
        def hook_fn(module, input, output):
            if isinstance(output, torch.Tensor):
                activations[name] = output.detach().cpu().numpy()
        return hook_fn

    # Register hooks on conv layers
    layer_idx = 0
    for name, module in model.model.named_modules():
        if isinstance(module, (nn.Conv2d,)):
            hooks.append(module.register_forward_hook(make_hook(f"layer_{layer_idx:02d}_{name}")))
            layer_idx += 1

    # Run inference to capture activations
    print("Running inference...")
    input_tensor = torch.from_numpy(test_image).float().permute(2, 0, 1).unsqueeze(0) / 255.0
    input_tensor = torch.nn.functional.interpolate(input_tensor, size=(IMG_SIZE, IMG_SIZE))

    with torch.no_grad():
        results = model.predict(source=test_image, imgsz=IMG_SIZE, verbose=False)

    # Extract and save per-layer data
    print("Extracting per-layer data...")
    layer_idx = 0
    for name, module in model.model.named_modules():
        if isinstance(module, nn.Conv2d):
            # Get weights
            weight = module.weight.detach().cpu().numpy()

            # Check for following BatchNorm
            # (In practice, we'd need to walk the module tree more carefully)
            bias = module.bias.detach().cpu().numpy() if module.bias is not None else np.zeros(weight.shape[0])

            # Quantize weights to INT4
            weights_int4, w_scale = quantize_int4(weight)
            save_int4_bin(weights_int4, f"{OUTPUT_DIR}/weights/layer_{layer_idx:02d}_weights.bin")

            # Quantize bias to INT32
            bias_int32 = np.round(bias / (w_scale.flatten() * (1.0/127.0))).astype(np.int32)
            save_int32_bin(bias_int32, f"{OUTPUT_DIR}/weights/layer_{layer_idx:02d}_bias.bin")

            # Save scale
            save_float32_bin(w_scale, f"{OUTPUT_DIR}/weights/layer_{layer_idx:02d}_scale.bin")

            # Save activations if captured
            act_key = f"layer_{layer_idx:02d}_{name}"
            if act_key in activations:
                act = activations[act_key]
                act_int8, _ = quantize_int8(act)
                save_int8_bin(act_int8, f"{OUTPUT_DIR}/activations/layer_{layer_idx:02d}_output.bin")

            print(f"  Layer {layer_idx:02d}: {name} [{weight.shape}]")
            layer_idx += 1

    # Save detection results
    if results and len(results) > 0:
        boxes = results[0].boxes
        if boxes is not None and len(boxes) > 0:
            det = np.column_stack([
                boxes.xyxy.cpu().numpy(),
                boxes.conf.cpu().numpy().reshape(-1, 1),
                boxes.cls.cpu().numpy().reshape(-1, 1)
            ]).astype(np.float32)
            save_float32_bin(det, f"{OUTPUT_DIR}/detection_output.bin")
            print(f"  Saved {len(det)} detections")

    # Clean up hooks
    for h in hooks:
        h.remove()


# ============================================================================
# Main
# ============================================================================

def main():
    print("=" * 60)
    print("YOLOv8n-WorldV2 Golden Value Generator")
    print("=" * 60)

    if HAS_ULTRALYTICS:
        print("\nGenerating golden values from real model...")
        try:
            generate_real_golden()
        except Exception as e:
            print(f"\nFailed to load real model: {e}")
            print("Falling back to synthetic golden values...")
            generate_synthetic_golden()
    else:
        print("\nGenerating synthetic golden values (install ultralytics for real model)...")
        generate_synthetic_golden()

    print("\nDone! Golden values saved to:", OUTPUT_DIR)
    print("\nNext steps:")
    print("  1. lake build")
    print("  2. lake test")


if __name__ == "__main__":
    main()
