# Sparkle ↔ Hesper BitNet Kernel Equivalence

This document plans and tracks proofs that **Sparkle's hardware BitNet
kernels** compute the same function as **Hesper's GPU/CPU BitNet
kernels** ([Verilean/hesper](https://github.com/Verilean/hesper)).

The two stacks were written independently:

|              | Sparkle                                    | Hesper                                             |
| ------------ | ------------------------------------------ | -------------------------------------------------- |
| Domain       | Synthesizable HDL (Lean → Verilog/JIT)     | GPU shaders (Lean → WGSL) + pure CPU spec          |
| Numerics     | `BitVec` fixed-point (Q16.16 / Q8.24)      | `Float` (CPU spec); `f32` (GPU)                    |
| Weight type  | `Array Int` ternary (-1, 0, +1)            | `ByteArray` i2_s packed (codes 0,1,2 → -1,0,+1)    |
| Datapath     | Combinational `macStage` + `adderTree`     | Iterative `forwardRow` over `[:outDim] × [:inDim]` |
| Entry point  | `IP.BitNet.SignalHelpers.bitLinearSignal`  | `Hesper.Layers.BitLinearSpec.forwardRow`           |

The goal is to relate them through a **shared abstract semantics**, not
to translate one DSL into the other. The plan is **two-layered**, as the
user asked: first datapath equivalence, then data equivalence. We do
matmul (BitLinear) first; attention is the same plan applied to a more
complex composition.

---

## Honest status (read this first)

The original ask was "prove the Sparkle BitNet kernel and the Hesper
BitNet kernel are equivalent." The current state is **partially that**:

| Stage              | Strategy                                    | "Sparkle ≡ Hesper on a fixture" claim       | Status                    |
| ------------------ | ------------------------------------------- | ------------------------------------------- | ------------------------- |
| BitLinear (matmul) | (4) fixture (v1a, integer inputs)           | YES — `hesper_eq_sparkle_v1a` (vendored CPU spec) | **proved**          |
| Q·K^T dot product  | (4) fixture (length-8 INT8)                 | YES — `sparkle_eq_hesper_circuit` + `_wgsl` (DSL interp) | **proved**     |
| Softmax            | (3) ε-bound, ULP-tolerant                   | YES — `softmax_circuit_matches_sparkle` + `_wgsl` | **proved**           |
| Weighted-V (attn@V)| (3) ε-bound, truncation-aware              | YES — `weightedV_circuit_matches_sparkle` + `_wgsl` | **proved**         |
| End-to-end attn    | (3) ε-bound, full pipeline                  | YES — `circuit_{saturated,soft}_matches_sparkle` + `wgsl_*` | **proved** |

The **Strategy** column refers to the four-way classification of FP /
quantisation equivalence proofs documented in
[*Equivalence proof strategies*](#equivalence-proof-strategies-fp--quantisation)
below — read that section first if it's the first time you see the
notation `(1)` / `(2)` / `(3)` / `(4)`.

**The honest summary**:

- For **matmul/BitLinear**, `Tests/Hesper/BitLinearEquivalence.lean`
  proves that Hesper's `forwardRowInt` and Sparkle's `bitLinearInt`
  return the same `Int` value on the v1a-shaped fixture
  (`inDim = 128`, scale = 1, integer inputs). This is the real
  Sparkle ↔ Hesper claim.

- For **attention's Q·K^T dot product**,
  `Tests/Hesper/HesperDSLEquivalence.lean` builds the same
  computation in Hesper's **Circuit IR** (`ScalarExp`) and
  Hesper's **WGSL DSL** (`Exp`), evaluates each via the Phase-1
  interpreters, and checks `native_decide`-style that both equal
  Sparkle's `dotProductInt` on the length-8 INT8 fixture. The two
  Hesper layers are also cross-checked against each other. So this
  is a **real Sparkle ≡ Hesper claim** at two independent layers.

- For the rest of attention (softmax, weighted-V, end-to-end), the
  files in this repo currently prove only **Sparkle ↔ shared
  abstract spec** — extending them to use the DSL interpreters
  the same way step 17 does is the natural next step (see step
  table for line items).

To upgrade the attention work to a real Sparkle ↔ Hesper claim, the
plan is now to use the **DSL interpreters** in
`Tests/Hesper/Vendored/CircuitInterp.lean` and
`Tests/Hesper/Vendored/WGSLInterp.lean`. Both interpreters are:

  - **Pure-Lean**: no GPU FFI, no string parsing.
  - **Type-safe**: WGSL evaluator is type-indexed on `WGSLType`.
  - **PR-ready**: written so they could be upstreamed into Hesper.

The two interpreters give us **two independent layers** at which to
pin "Sparkle ≡ Hesper":

  1. **Circuit IR** (high-level, scope-aware tensor IR, ~30
     constructors): the layer Hesper uses as the canonical
     mathematical reference. If Hesper's lowering Circuit → WGSL/PTX
     is correct, equivalence at the Circuit level implies equivalence
     at the GPU level.
  2. **WGSL DSL** (low-level, ~226 constructors, GADT): the layer
     immediately above the GPU. Pinning here removes the Circuit
     lowering from the trusted base.

Phase 1 of the WGSL interpreter handles scalar f32/i32/u32/bool plus
vec2/3/4 of f32 — enough for BitLinear and attention dot products.
Phase 2 (matrices, atomics, subgroup matrix, textures, bitcast) is
listed as pending in the implementation table.

Until step 17 lands (a fixture-level cross-check using these
interpreters), the "Hesper" side of the attention claim remains
**aspirational, not proved** — but the *machinery* for proving it
inside Lean is now in place.

---

## Equivalence proof strategies (FP / quantisation)

Comparing two implementations of the same kernel at *different
numerical types* (Sparkle's `BitVec` Q-format vs. Hesper's `Float` /
`f32` / FP16) cannot in general be a single literal-equality
theorem.  There are four standard tactics; each Sparkle ↔ Hesper
theorem in this repo picks one (see the **Strategy** column above).

### (1) Shared denotational spec

Lift both implementations into the *same* mathematical object —
typically `ℝ` plus a quantisation function — and prove each refines
that spec.  Equivalence is a corollary of "both refine the same
abstract semantics".

```
              shared spec : ℝ ←————————————————————————┐
                                                       │
Sparkle (Q16.16)  ───quantise→  ℝ  ────────────refines─┘
Hesper  (Float)   ───identity→  ℝ  ────────────refines─┤
                                                       │
                                  ⇒ Sparkle ≡ Hesper at the spec level
```

Strongest form when it works.  Used in `Tests/Hesper/MatmulSpec.lean`
to factor BitLinear through a single algebraic
`scale * Σ ι(code) * x[j]` definition.

### (2) Domain restriction (exactly-representable subset)

Restrict the input domain so both representations round-trip
exactly:

```
def OnQ4Grid (x : Float) : Prop :=
  ∃ k : Int, x = (k : Float) * scale ∧ -8 ≤ k ∧ k < 8
```

Then prove unconditional equality on inputs satisfying the
predicate.  Useful as the kernel of a larger proof: outside the
predicate's domain you fall back to (3).

### (3) Bounded error (ε-equivalence)

Drop literal equality and prove a tolerance bound:

```
∀ inputs, |sparkle(inputs) - hesper(inputs)| ≤ ε(InDim, scale)
```

The bound `ε` is derived from per-operation ULPs and accumulation
depth:

  - FP16 accumulation: `inDim * 2^-10 * max|partial sum|`
  - Q4 round: `scale / 2`

This is what TorchLean (arXiv:2602.22631) does for FP32 — wrap an
executable IEEE-754 binary32 kernel in Lean and use IBP / CROWN
bound propagation to discharge the resulting inequality.  Sparkle
does the same shape of proof at smaller scale: see the softmax /
weighted-V theorems above which carry an ULP-tolerant or
truncation-aware ε.

### (4) Fixture / property-based testing

Pick a finite set of representative inputs (golden vectors,
random seeds, edge cases — `0`, `±1`, `max`, `min`,
`subnormal`, single-hot, all-`1`s, BitNet-shaped ternary
weights) and discharge the equality on each via `decide` /
`native_decide`.  Not a "for-all" proof, but extremely effective
as a regression check and very cheap to write — Lean's
`native_decide` runs the comparison concretely.

This is what `Tests/Hesper/BitLinearEquivalence.lean` and
`Tests/Hesper/HesperDSLEquivalence.lean` actually use today: a
hand-picked fixture (the v1a layer shape and the length-8 INT8
attention shape) plus `native_decide`.  A literal `∀ inputs`
generalisation is left to a future strategy-(1) lift.

### Picking a strategy

| Layer of the kernel    | Best fit | Why                                         |
| ---------------------- | -------- | ------------------------------------------- |
| Pure integer kernels (BitLinear with `Int` inputs) | (4)      | Inputs are small; `native_decide` closes the proof literally on the fixture. |
| Float-domain kernels with quantisation grid that both sides land on | (1) + (2) | Lift both into ℝ, restrict to grid points, prove unconditional equality on the restricted domain. |
| Float-domain kernels off-grid (softmax, exp, division) | (3)      | An exact-equality theorem is unprovable; the right object is the ε.  Pair with a Lean-level `ulp` / `relError` lemma library. |
| Regression coverage / acceptance gates | (4)      | Even when (1) / (3) hold, a fixture suite catches infrastructure-level breakage faster than re-running the formal proof. |

In practice every Sparkle ↔ Hesper theorem is written in **one of
the four**.  The **Strategy** column in the status table makes that
choice explicit so a reader knows what kind of guarantee they're
getting.

### Relationship to TorchLean

[TorchLean](https://arxiv.org/abs/2602.22631) treats *floating-point
neural-network execution and verification* as a single Lean object:
an executable IEEE-754 binary32 kernel plus a proof-relevant rounding
model, with IBP / CROWN / LiRPA bound propagation as the verification
layer.  In the four-strategy taxonomy above this is **(1) + (3)** —
shared denotational spec providing a common type for both sides, and
ε-bound propagation for the actual safety / equivalence claim.

The Sparkle side aims at the same shape of proof but with a wider
type spread on the implementation side: `BitVec` Q-format on the HDL
side, `Float` (Lean's binary64) on the Hesper CPU spec side, plus
GPU-targeted `f32` and FP16 in the WGSL DSL.  Lifting all of those
into one `ℝ`-valued spec is the long-term plan; the per-layer
strategy column tracks how far each kernel has gotten along that
path.

---

## Shared abstract semantics (the contract)

Both sides refine the same mathematical operation:

```
y[i] = scale * Σ_{j=0..inDim-1}  W[i, j] * x[j]      with W[i,j] ∈ {-1, 0, +1}
```

We name this in Lean as a small reference function — totally independent
of either DSL — and prove that *each* DSL refines it.

```lean
-- Tests/Hesper/MatmulSpec.lean (shared reference)
def matmulRefRow (W : Array (Array Int)) (x : Array Int) : Array Int := ...
```

`Int` (not `Float`, not `BitVec`) is the right ground truth: ternary
× integer activations are exactly representable, no rounding noise.
Floating-point IEEE-754 non-associativity (Hesper) and fixed-point
saturation (Sparkle) become *separate, stated* refinement steps.

## Layer 1 — datapath equivalence

> "the *order* and *shape* of operations match — what gets multiplied,
> what gets summed, in what nesting structure."

Both sides decompose `y[i] = scale * Σ_j W[i,j] * x[j]` into the same
3-step pipeline:

```
                      ┌───────────┐    ┌─────────────┐    ┌──────────┐
   x[j], W[i,j]  ─→   │ macStage  │ →  │  reduce-sum │ →  │  scale   │  ─→ y[i]
                      └───────────┘    └─────────────┘    └──────────┘
```

| Stage         | Sparkle (`SignalHelpers.lean`)            | Hesper (`BitLinearSpec.lean`)                       |
| ------------- | ----------------------------------------- | --------------------------------------------------- |
| `macStage`    | `macOneList` (+1→x, -1→-x, 0→drop)        | `acc + w * x` inside `for j in [:inDim]`            |
| `reduce-sum`  | `treeReduce (· + ·)` (binary adder tree)  | `acc := acc + ...`  (linear)                        |
| `scale`       | `scaleQ8_24` fixed-point mult             | `scale * acc`  (Float)                              |

The **sum-shape gap** (tree vs. linear) is exactly the gap that
Hesper's own `Hesper/Proofs/ReductionEquiv.lean` already closes in the
abstract `Int` setting:

```lean
theorem treeReduce_eq_rangeSum (k : Nat) (f : Nat → Int) :
    treeReduce k f = rangeSum (2 ^ k) f
```

So Layer 1 reuses Hesper's existing theorem on the abstract side, and
adds the **Sparkle-side bridge**:

> Sparkle's `bitLinearSignal weights activations` over Int-lifted
> activations equals `matmulRefRow [weights] activations`, taken
> column-wise.

**Concretely the Layer-1 obligations are**:

1. `Sparkle.bitLinearSignal_eq_matmulRef` — Sparkle's tree-reduced
   ternary MAC equals the reference `matmulRefRow` for one output
   column. Proof goes through `treeReduce_eq_rangeSum` adapted to
   Sparkle's helper (the tree shape is the same).
2. `Hesper.forwardRow_eq_matmulRef_int` — Hesper's `forwardRow` equals
   `matmulRefRow` *under the assumption activations and scale are
   integers* (no float rounding). Proof unfolds the `Id.run` for-loop.
3. `decodeI2S_eq_ternary` — Hesper's `decodeI2S packed rowStart j`
   returns the same `Int` value that Sparkle's `weights[i, j] : Int`
   has at the corresponding position, given a packed-bytes-from-ternary
   construction (Hesper's `packI2S` is its right-inverse).

Output of Layer 1: a single composable theorem
`bitLinear_sparkle_eq_hesper_int`.

## Layer 2 — data equivalence

> "for the actual inputs we ship in BitNet v1a, the Sparkle output bits
> and the Hesper output bits are the same."

Layer 1 is purely about operation structure; Layer 2 grounds it in the
concrete numerics that both stacks expose to users. Two sub-steps:

### 2a. Float ↔ fixed-point bridge

Hesper computes in `Float`; Sparkle computes in Q16.16 fixed-point. We
prove that for the **integer-valued, scale=1, in-range** inputs used by
the BitNet v1a tests, both representations agree bit-for-bit when
projected through `Float.toInt32 / BitVec.ofInt`.

```lean
theorem hesper_forwardRow_eq_sparkle_q16_16
  (W : Array (Array Int)) (x : Array Int)
  (h_in_range : ∀ a ∈ x, -32768 ≤ a ∧ a < 32768)
  (h_dim_ok   : ∀ row ∈ W, row.size = x.size)
  : (Hesper.forwardRow_packed_int W x).map Float.toInt
    = (Sparkle.bitLinearSignal_int W x)
```

The `_in_range` hypothesis is the only real constraint: outside the
±2^15 window the `Float` mantissa is still exact, but Sparkle's Q16.16
saturates. The hypothesis matches the v1a fixture.

### 2b. The 8 golden vectors

`Tests/Integration/BitNetSoCTest.lean:43–51` already pins 8 input/output
pairs through the full Sparkle SoC. Layer 2's concrete check is:

```lean
example : ∀ (vec : Vec) ∈ goldenVectors,
    (Hesper.forwardRow ... vec.input).toQ16_16 = vec.expectedOutput := by
  decide
```

This is mechanical (`native_decide`) but extremely high-signal: it
discharges the abstract proof against the same numbers running on the
JIT'd RV32 + BitNet peripheral.

## Attention status (added 2026-05-05)

Layer 1 + 2 closed for attention's Q·K^T dot product, in
`Tests/Hesper/AttentionEquivalence.lean`. The headline lemma
`dotProductInt_eq_listSum` carries **without the ternary
precondition** that BitLinear needed — attention multiplies
arbitrary INT8 values, so no zero-pruning case-split.

Hesper has no pure-CPU attention reference (its
`Hesper/Layers/Attention.lean` is GPU shaders only), so attention
is **not** at parity with BitLinear here: only the Sparkle ↔
shared-spec edge is proved. The Hesper edge — the one that would
make this a real "Sparkle ≡ Hesper" claim for attention — is
deferred until a CPU spec exists. See the "Honest status" block
at the top of this file for the consequences.

## Why matmul first, attention second

Attention = matmul ∘ softmax ∘ matmul ∘ scale. Once `bitLinearSignal`
is proven equivalent, the attention proof is **structural composition**
plus separate equivalence proofs for `softmax` and the `Q·K^T` scale —
each of which is the same Layer-1 / Layer-2 pattern at a smaller scale.
Doing matmul first establishes the bridge infrastructure (shared
spec module, the `decodeI2S ↔ Array Int` lemma, the float-fixed bridge)
that attention then reuses.

## Implementation order

The "scope" column is the important one — it makes explicit whether
each step compares Sparkle to Hesper, or only to a Sparkle-internal
abstract reference.

| Step | File                                                    | Status   | Scope                        |
| ---- | ------------------------------------------------------- | -------- | ---------------------------- |
| 1    | `Tests/Hesper/MatmulSpec.lean`                          | **done** | shared spec                  |
| 2    | `Tests/Hesper/Vendored/BitLinearSpecInt.lean` (vendor)  | **done** | Hesper port                  |
| 3    | Abstract Sparkle sum-shape (`treeReduce_int_eq_listSum`)| **done** | Sparkle internal             |
| 4    | `bitLinearInt_eq_listSum` (Sparkle, ternary precond)    | **done** | Sparkle ↔ shared spec        |
| 5    | Hesper ↔ ref + Sparkle ↔ ref on v1a fixtures            | **done** | both sides ↔ shared spec     |
| 6    | Hesper ↔ Sparkle transitivity (`hesper_eq_sparkle_v1a`) | **done** | **Sparkle ≡ Hesper** ✓       |
| 7    | Layer-2 Sparkle BitVec ↔ math reference on v1a fixture  | **done** | Sparkle internal             |
| 8    | 8 golden vectors `native_decide` + `y = x + 64x³` check | **done** | Sparkle internal             |
| 9    | Attention dot product: `dotProductInt_eq_listSum`       | **done** | Sparkle ↔ shared spec        |
| 10   | Attention fixture cross-checks (`int8DotProduct`, etc.) | **done** | Sparkle internal             |
| 11   | Weighted-V: `weightedVInt_eq_listSum_div`               | **done** | Sparkle ↔ shared spec        |
| 12   | Softmax fixture pins (sum-to-1, argmax, monotone)       | **done** | Sparkle internal             |
| 13   | Single-stage attention-output fixture                   | **done** | Sparkle internal             |
| 14   | End-to-end Q·K^T → softmax → attn @ V composition       | **done** | Sparkle internal             |
| 15   | Hesper Circuit DSL interpreter (`CircuitInterp.lean`)   | **done** | Hesper-PR ready              |
| 16   | Hesper WGSL DSL interpreter Phase 1 (`WGSLInterp.lean`) | **done** | Hesper-PR ready              |
| 17   | Apply step 6's pattern to attention via DSL interpreters| **done** | **Sparkle ≡ Hesper** for attn ✓ |
| 18   | WGSL interpreter Phase 2 (math, bitwise, vec dot, subgroup-collapsed) | **done** | ~90 of 225 constructors |
| 19   | Softmax + Weighted-V via DSL interps                    | **done** | both layers ↔ Sparkle ✓     |
| 20   | WGSL interpreter Phase 3 (matrices, atomics, textures, subgroup matrix, all aliases) | **done** | full 225/225 constructors |
| 21   | WGSL interpreter Phase 4 (stateful atomics, real textures, 4×4 det, typed bitcast) | **done** | full semantics, no stubs    |
| 22   | End-to-end attention via DSL interps                    | **done** | full pipeline ↔ Sparkle ✓   |

Only **step 6** currently delivers the original "Sparkle and Hesper
return the same value on a fixture" claim. Steps 9–14 establish that
Sparkle's attention kernel matches the abstract `linearSum`-based
contract, which is the *Sparkle half* of the equivalence; the *Hesper
half* awaits steps 15–16.

## Hesper as a dependency

Hesper is **not** added to `lakefile.lean` as a library dependency —
that pulls in WebGPU + WGSL + Quantization headers we do not need. The
two source files we care about (`BitLinearSpec.lean` ~145 lines,
`Proofs/ReductionEquiv.lean` ~113 lines) are self-contained pure-Lean
files. We **vendor copies** of the relevant definitions into
`Tests/Hesper/Vendored/`, with a header comment pointing at the upstream
commit. Hesper is MIT-licensed; vendoring is fine. This keeps the build
hermetic and prevents Hesper's GPU stack from leaking into Sparkle's
synthesis path.

If/when Hesper extracts a `Hesper.Spec` lakefile target with no GPU
deps, switch the vendored copies to a real dependency.

## Open questions

- **Which Sparkle BitLinear function is canonical for the equivalence?**
  `bitLinearSignal` (combinational, hardwired weights) is the v1a path.
  `bitLinearPipelinedSignal` (Top.lean) currently delegates to it. The
  proof targets `bitLinearSignal`; pipelined variants get a separate
  "register-insertion preserves IO function" lemma later.
- **Float-LUT step.** Hesper has an optional scale-encoded-in-LUT path
  for some kernels. v1a uses scale=1, so this lookup is the identity;
  for v1b (real BitNet weights with non-unit scales) we'll need a
  per-scale lemma.
- **Ternary-zero pruning.** Sparkle's `macOneList` *drops* zero
  contributions; Hesper's `forwardRow` adds `0 * x` explicitly. They're
  equal up to associativity of `+ 0`, which is the cheapest non-trivial
  step in Layer 1.

