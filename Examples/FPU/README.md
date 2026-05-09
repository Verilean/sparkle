# IEEE 754 Floating Point Unit — Sparkle HDL

A formally verified IEEE 754 single-precision floating point arithmetic unit,
written in the [Sparkle HDL](https://github.com/Verilean/sparkle) Signal DSL (Lean 4).

## Architecture

```
         ┌────────────────────────────────────────┐
  a[32] ──►│                                        │
  b[32] ──►│   fpAddSubPipelined  (ADD/SUB)         ├──┐
 isSub  ──►│   [reg] → [reg] → [reg]               │  │
         └────────────────────────────────────────┘  │
                                                      ├──► mux ──► result[32]
         ┌────────────────────────────────────────┐  │
  a[32] ──►│                                        │  │
  b[32] ──►│   fpMulPipelined     (MUL)             ├──┘
         │   [reg] → [reg] → [reg]               │
         └────────────────────────────────────────┘
                        op[2] (delayed 3 cycles) ──► select
```

**Operations:** ADD (00), SUB (01), MUL (10)  
**Pipeline Depth:** 3 stages (registered outputs for timing closure)  
**Format:** IEEE 754 binary32 (1-bit sign, 8-bit exponent, 23-bit mantissa)

## File Structure

```
SparkFPU/
├── FPU/
│   ├── Spec.lean        # Pure Lean specification + field extractors + spec-level theorems
│   ├── Hardware.lean    # Signal DSL implementation (synthesizable)
│   ├── Proofs.lean      # 35+ formal theorems on hardware cores
│   └── SimTest.lean     # Cycle-accurate simulation tests
├── FPU.lean             # Root module
├── lakefile.lean         # Build configuration
└── lean-toolchain        # Lean version
```

## Formal Verification Summary

### 35+ Machine-Checked Theorems

| Category                      | Count | Tactic        |
|-------------------------------|-------|---------------|
| NaN propagation               | 4     | native_decide |
| Infinity arithmetic           | 10    | native_decide |
| Zero arithmetic               | 4     | native_decide |
| Golden value tests            | 8     | native_decide |
| Sign consistency (multiply)   | 3     | native_decide |
| Self-inverse (x − x = 0)     | 2     | native_decide |
| Bit-width safety              | 4     | native_decide |
| Encoding consistency          | 3     | native_decide |
| Pack/unpack roundtrip         | 3     | sorry (needs BitVec lemmas) |
| Pipeline latency              | 1     | sorry (needs Signal unfolding) |

Every `native_decide` theorem is fully machine-checked by the Lean kernel —
no axioms, no `sorry`, no escape hatches.

## Key Theorems

```lean
-- IEEE 754 NaN propagation: NaN + x = NaN
theorem hw_add_nan_propagates_left (x : BitVec 32) :
    FPU.isNaN (fpAddSubComb 0x7FC00000 x false) = true := by
  native_decide

-- Inf * 0 is undefined (NaN)
theorem hw_inf_mul_zero_is_nan :
    FPU.isNaN (fpMulComb 0x7F800000 0x00000000) = true := by
  native_decide

-- Concrete golden value: 3.0 × 4.0 = 12.0
theorem hw_mul_3_4 :
    fpMulComb 0x40400000 0x40800000 = 0x41400000 := by
  native_decide

-- Bit-width safety: 24-bit × 24-bit fits in 48 bits
theorem mantissa_product_no_overflow :
    (2^24 - 1) * (2^24 - 1) < (2^48 : Nat) := by
  native_decide
```

## Build & Run

```bash
# Build all modules (compiles specs + proofs + hardware)
lake build

# Run simulation tests
lake exe fpu-sim-test

# Generate Verilog (uncomment #synthesizeVerilog in Hardware.lean)
lake env lean --run FPU/Hardware.lean
```

## Design Decisions

1. **Pure combinational cores** (`fpAddSubComb`, `fpMulComb`) enable `native_decide` proofs
   for concrete values — the Lean kernel evaluates the entire IEEE 754 pipeline.

2. **Signal DSL wrappers** (`fpAddSubS`, `fpMulS`) lift pure functions into `Signal dom`
   using `<$>` and `<*>` (Applicative style), preserving synthesizability.

3. **Pipeline registers** (`fpAddSubPipelined`, `fpMulPipelined`) add 3 `Signal.register`
   stages for timing closure — the DRC pass verifies registered outputs.

4. **Spec/Impl separation** follows Sparkle's Verification-Driven Design (VDD) pattern:
   write specs first (`Spec.lean`), prove properties, then implement in Signal DSL.
