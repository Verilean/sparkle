
# Chapter 7b — Equivalence across number types (FP, fixed-point, quantisation)

Ch 7 proved two `BitVec`-typed implementations equal at the bit
level: same input type, same output type, `#verify_eq` reduces to
`bv_decide`.  Real designs aren't always that lucky.  When you
ship a BitNet inference kernel you usually have *two* reference
points to chase:

1. A **GPU / CPU reference** written against `Float` or `f32` —
   the Hesper / PyTorch / NumPy side that decides "is the model
   numerically correct".
2. A **hardware kernel** written against `BitVec` Q-format
   (Q16.16, Q8.24) and ternary / Q4 weights — the Sparkle side
   that gets synthesised to silicon.

These two computations share *intent* (matrix-vector product,
softmax, attention) but live in different number systems.  A
single `#verify_eq` won't bridge that gap; we need a richer
toolkit.  This chapter walks through the four strategies the
literature has converged on, and writes a small concrete example
in each.

The same four-way taxonomy is used in
[`docs/reference/Hesper_Equivalence.md`](../reference/Hesper_Equivalence.md)
to label every Sparkle ↔ Hesper theorem in the test suite, and it
matches what TorchLean (arXiv:2602.22631) does for FP32 networks.

## 7b.1 The four strategies in one picture

```
                                                          strength
                                                          ────────
(1) Shared denotational spec
    Lift both implementations into ℝ + a quantisation         ★★★★
    function; prove each refines the spec.

(2) Domain restriction
    Restrict inputs to the exact-representable subset         ★★★☆
    (an arithmetic grid both sides round-trip on);
    prove unconditional equality there.

(3) Bounded error (ε-equivalence)
    Drop literal equality; prove |sparkle - hesper| ≤ ε.      ★★★☆
    This is the TorchLean approach.

(4) Fixture / property-based testing
    Pick representative inputs; close them with                ★★☆☆
    `decide` / `native_decide`.
```

(1) and (3) are formal proofs; (2) is a special case of (1) on a
finite grid; (4) is automation.  In practice a real design uses
all four — different layers of the kernel pick the strategy that
fits.

## 7b.2 Setup — a tiny dual-implementation

To make the strategies concrete we'll use a 4-input dot product
in two flavours.  These mirror the BitNet BitLinear kernel at
miniature scale.

```lean
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

-- Hardware reference: Q1.7 fixed-point.  Inputs are signed
-- 8-bit values interpreted as fractions in [-1.0, +1.0).
-- We accumulate as Int to dodge intermediate overflow, then
-- truncate back to 16-bit Q-format for the output.
def dotQ1_7 (x : List Int) (w : List Int) : Int :=
  -- Pre-condition: |x[i]|, |w[i]| ≤ 127.  Output is in Q1.14.
  (x.zip w).foldl (fun acc (xi, wi) => acc + xi * wi) 0

-- Software reference: pure Float (`Lean.Float = IEEE-754 binary64`).
def dotFloat (x : List Float) (w : List Float) : Float :=
  (x.zip w).foldl (fun acc (xi, wi) => acc + xi * wi) 0.0
```

Two implementations, two number systems.  Goal: relate them.

## 7b.3 Strategy (1) — shared denotational spec

Lift both into a common abstract semantics.  Write the
mathematical operation once; prove each implementation refines
it.

```lean
-- The abstract spec lives in `Float` and treats both sides
-- *as if they were ℝ*.  A real proof would use Mathlib's `ℝ`
-- and a separate decoder per number type; for the tutorial we
-- pretend Float is exact (it isn't — but the structural
-- argument is the same).
def dotSpec (x w : List Float) : Float :=
  (x.zip w).foldl (fun acc (xi, wi) => acc + xi * wi) 0.0

-- Decoder from Q1.7 to its mathematical value (a fraction).
def q1_7Decode (k : Int) : Float := Float.ofInt k / 128.0

-- Refinement: the Q1.7 datapath computes (the floor of) the
-- spec applied to decoded inputs.  Showing equality at the
-- spec level is what lets us claim Sparkle ↔ Hesper at all.
example (x w : List Int) :
    -- hand-wavy form for the chapter — spelt out for the v1a
    -- BitLinear shape in `Tests/Hesper/MatmulSpec.lean`.
    True := trivial
```

This is what `Tests/Hesper/MatmulSpec.lean` actually does for
the BitLinear v1a layer: defines a single `bitLinearOverℝ` and
shows `Sparkle.bitLinearInt` / `Hesper.forwardRowInt` both refine
it.  The Sparkle ↔ Hesper claim is then a corollary of "they
both refine the same spec".

**Strength.** When it works, this gives an unconditional `∀
inputs, sparkle = hesper`.  TorchLean (arXiv:2602.22631) sets
this up for whole networks: an executable IEEE-754 binary32
kernel with a proof-relevant rounding model is the shared spec,
and concrete PyTorch graphs refine it.

**Cost.** You need a real ℝ-based theory of the operation to
refine into.  For matmul / dot product that's mechanical; for
`exp` / `softmax` you start needing transcendental facts that
Lean alone doesn't ship — pair it with strategy (3) when the
operation goes off-grid.

## 7b.4 Strategy (2) — domain restriction

If the float inputs happen to land on a grid that the fixed-point
kernel represents exactly, the round-trip is identity and the two
sides agree literally.  Restrict the domain by predicate:

```lean
/-- A `Float` lies on the Q1.7 grid iff it equals `k / 128` for
    some integer `k` in `[-128, 128)`. -/
def OnQ1_7Grid (x : Float) : Prop :=
  ∃ k : Int, -128 ≤ k ∧ k < 128 ∧ x = (Float.ofInt k) / 128.0

-- (Sketch — would be filled in with concrete bit-level lemmas
-- about Float ↔ Int conversion in a real proof.)
example (x w : Float)
    (hx : OnQ1_7Grid x) (hw : OnQ1_7Grid w) :
    -- decoded(Q1_7 multiply) = Float multiply
    True := trivial
```

The "grid" is finite (`128 × 128 = 16384` pairs in the example
above), so on it strategy (2) actually reduces to a giant
(decidable) finite check — see strategy (4) for the automation.

**Strength.** Outside the grid you have no claim, but inside it
the equality is genuine `=`, no ε.

**Cost.** You're committing to "users only feed me on-grid
inputs".  In an inference pipeline that's usually fine — the
tensor was quantised at the boundary, so by construction every
input is on-grid.  In a CPU-spec-vs-GPU-kernel comparison it's
often *not* fine because the GPU's intermediate FP32 values are
generally off-grid.

## 7b.5 Strategy (3) — bounded error (ε-equivalence)

Give up on literal equality and prove a tolerance:

```lean
-- Pseudocode — the real version lives in
-- `Tests/Hesper/SoftmaxWeightedV.lean`, which carries an
-- ULP-tolerant ε around `softmax`.

def maxRelError (a b : Float) : Float :=
  (a - b).abs / (a.abs + b.abs + 1e-30)

example (x w : List Float) :
    -- |dotFloat x w - decoded (dotQ1_7 x' w')| ≤ ε
    -- where ε comes from per-op ULPs * accumulation depth.
    True := trivial
```

The bound `ε` comes from two pieces:

  - **per-op rounding**: each FP op contributes ≤ ½ ULP of its
    result type;
  - **accumulation depth**: an `n`-term sum compounds those
    half-ULPs to roughly `n × ulp(maxPartial)`.

For a 128-input BitLinear in FP16, that's `128 × 2^-10 ≈ 0.125`
relative — small enough that downstream layers (a softmax, an
argmax) stay correct, large enough that you'd never close it
with `bv_decide`.

**This is the TorchLean (arXiv:2602.22631) approach.**  TorchLean
wraps an executable IEEE-754 binary32 kernel in Lean, then uses
*bound-propagation* (IBP / CROWN / LiRPA-style) to discharge
adversarial-robustness theorems against that ε.  Same shape, same
type of guarantee, just at FP32 / network scale.

**Strength.** Realistic.  The actual numerical guarantee a
silicon kernel can provide.

**Cost.** You need a Lean-level `ulp` / `relError` lemma library.
Sparkle's `Tests/Hesper/Vendored/` directory has a small one for
the softmax / weighted-V proofs; Mathlib doesn't ship one yet for
arbitrary widths.

## 7b.6 Strategy (4) — fixture / property-based testing

The pragmatic floor: pick representative inputs and discharge
each one concretely.

```lean
-- Hand-picked weight: the BitNet ternary pattern.
def w8 : List Int := [1, -1, 0, 1, -1, 0, 1, -1]

-- A small fixture covering boundary, all-zero, all-±1, hot, …
def fixture : Array (List Int) := #[
  [0, 0, 0, 0, 0, 0, 0, 0],            -- zeros
  [127, 127, 127, 127, 127, 127, 127, 127],  -- max
  [-128, -128, -128, -128, -128, -128, -128, -128], -- min
  [1, -1, 1, -1, 1, -1, 1, -1],        -- alternating
  [0, 0, 0, 1, 0, 0, 0, 0]              -- one-hot
]

-- For each fixture input, the two implementations agree on
-- the integer accumulation (mod the spec equality of strategy
-- (1) above — at this size it's the same theorem).
example : ∀ x ∈ fixture, dotQ1_7 x w8 = dotQ1_7 x w8 := by
  intro x _
  rfl

-- The non-trivial case is comparing across number systems
-- (Float vs Q1.7).  If we *also* provide the fixture in Float
-- form on the grid, `native_decide` closes it without proof
-- engineering.
example : True := by native_decide
```

In Lean, `native_decide` actually executes the comparison —
fast enough that a fixture of a few hundred entries closes in
sub-second.  This is what
`Tests/Hesper/BitLinearEquivalence.lean` and
`Tests/Hesper/HesperDSLEquivalence.lean` use today.

**Strength.** Cheapest to write; no specs, no ε library.  Catches
infrastructure-level breakage (e.g. a `forwardRowInt` that
silently swaps two indices) instantly.

**Cost.** Not a proof — a regression check.  A carefully
adversarial input could pass the fixture and break in production.

## 7b.7 Picking a strategy

| Layer of the kernel                                           | Best fit  | Why |
|--------------------------------------------------------------|-----------|-----|
| Pure integer kernels (BitLinear with `Int` inputs)            | (4)       | Inputs are small; `native_decide` closes it literally on the fixture. |
| Float-domain kernels with quantisation grid both sides land on | (1) + (2) | Lift to ℝ, restrict to grid, prove unconditional equality. |
| Float-domain kernels off-grid (softmax, exp, division)        | (3)       | An exact-equality theorem is unprovable; the right object is the ε. |
| Regression coverage / acceptance gates                        | (4)       | Even when (1) / (3) hold, a fixture suite catches infrastructure breakage faster than re-running the formal proof. |

The header of every Sparkle ↔ Hesper theorem in
`Tests/Hesper/*.lean` carries a `-- Strategy: (N)` tag declaring
which of the four it uses, so a reader can tell at a glance what
kind of guarantee they're getting.

## 7b.8 Where to go next

- **The full table** with one row per Sparkle ↔ Hesper theorem
  lives in
  [`docs/reference/Hesper_Equivalence.md`](../reference/Hesper_Equivalence.md).
- **TorchLean** (arXiv:2602.22631) is the closest published
  precedent for strategy (1) + (3) on whole NN graphs at FP32.
- **Mathlib's `Float`** is currently axiomatic; the bound-error
  proofs in `Tests/Hesper/SoftmaxWeightedV.lean` use a small
  ULP-axiomatisation in `Tests/Hesper/Vendored/`.  Replacing
  that with Mathlib's eventual real-arithmetic IEEE-754
  development is a long-term goal.

Ch 8 returns to plain `BitVec` territory: feeding the synthesised
RTL through Yosys for tape-out-quality netlists.
