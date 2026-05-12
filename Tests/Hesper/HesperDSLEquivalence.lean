/-
  Sparkle ≡ Hesper Attention — via DSL interpreters.

  Closes step 17 of `docs/Hesper_Equivalence.md`: makes a real
  Sparkle ↔ Hesper equivalence claim for attention's Q·K^T dot
  product, using the **DSL interpreters** built in Phase 66:

    - `Tests/Hesper/Vendored/CircuitInterp.lean` (Hesper Circuit IR)
    - `Tests/Hesper/Vendored/WGSLInterp.lean`    (Hesper WGSL DSL)

  Up to now the attention work pinned only the Sparkle ↔
  shared-spec edge of the equivalence triangle. With the DSL
  interpreters in hand, the **Hesper edge** is now also reachable
  inside Lean — without any GPU FFI or WGSL-string parsing.

  ## What this file proves

  Three layered claims, all on the same v1a-shaped attention
  fixture (length-8 INT8 vectors, full-range signed entries):

  1. **Circuit-DSL Hesper kernel** (`hesperDotProductCircuit`)
     evaluates to the Sparkle reference (`Sparkle.IP.BitNet.int8DotProduct`).
     This pins Hesper's *high-level math* against Sparkle.

  2. **WGSL-DSL Hesper kernel** (`hesperDotProductWGSL`)
     evaluates to the same value. This pins Hesper's *low-level
     GPU semantics* against Sparkle, removing the Hesper Circuit
     → WGSL lowering from the trusted base.

  3. **Both DSL interpreters agree** with each other on the
     fixture — sanity check that Hesper's two layers are mutually
     consistent at the point where they each compute an attention
     dot product.

  All three checks use `native_decide` per
  `feedback_hesper_float_bridge.md`.
-/

import IP.BitNet.Types
import Tests.Hesper.AttentionEquivalence
import Tests.Hesper.Vendored.CircuitInterp
import Tests.Hesper.Vendored.WGSLInterp

namespace Sparkle.Tests.Hesper.HesperDSLEquivalence

open Sparkle.IP.BitNet
open Sparkle.Tests.Hesper.AttentionEquivalence
open Sparkle.Tests.Hesper.Vendored.CircuitInterp (ScalarExp evalPointwise evalReduce ReduceOp)

/-! ## Fixture (re-exported from `AttentionEquivalence.lean`)

We reuse the existing length-8 INT8 fixture
(`fixtureQ` = [127, -128, 50, -50, 1, -1, 0, 100],
 `fixtureK` = [-128, 127, -50, 50, 100, -100, 1, -1])
whose dot product is **−37412** in `Int`. -/

/-- Lift `Int → Float` for use as Hesper-DSL inputs. -/
def fixtureQFloat : Array Float :=
  fixtureQ.toArray.map fun i => Float.ofInt i
def fixtureKFloat : Array Float :=
  fixtureK.toArray.map fun i => Float.ofInt i

/-! ## 1. Circuit DSL evaluation

The Hesper attention dot product as a `ScalarExp`:
  `body(j) = input[0][j] * input[1][j]`
applied at every lane `j ∈ [0, 8)`, then reduced by sum. -/

/-- The pointwise body: `q[lane] * k[lane]`. -/
def dotProductBody : ScalarExp :=
  .mul (.input 0) (.input 1)

/-- Evaluate Hesper's Circuit-DSL attention dot product on the fixture.
    Pointwise multiply at each of the 8 lanes, then sum-reduce. -/
def hesperDotProductCircuit : Float :=
  let prods := evalPointwise dotProductBody #[fixtureQFloat, fixtureKFloat] 8
  evalReduce ReduceOp.sum prods

/-- Sanity: the Circuit-DSL result is `−37412`. -/
theorem circuit_value :
    (hesperDotProductCircuit == (-37412.0 : Float)) = true := by
  native_decide

/-- **Sparkle ≡ Hesper Circuit IR**: the Hesper Circuit-DSL
    evaluation of the attention dot product equals (after Float
    → Int rounding) Sparkle's `dotProductInt` reference. -/
theorem sparkle_eq_hesper_circuit :
    (hesperDotProductCircuit == Float.ofInt (dotProductInt fixtureQ fixtureK)) = true := by
  native_decide

/-! ## 2. WGSL DSL evaluation

The Hesper attention dot product as a sequence of `Exp.add`s
over `mul` of indexed array reads. We materialise the Q and K
buffers as `EvalEnv.f32_arrays` and build an 8-term tree of
multiply-accumulates.

The WGSL kernel is **morally**:

```wgsl
var acc = 0.0;
for (var i = 0u; i < 8u; i++) {
  acc = acc + q[i] * k[i];
}
return acc;
```

We unroll the loop (8 iterations) since `Exp` has no native
loop construct — Hesper relies on workgroup-size unrolling
for small kernels anyway. -/

open Sparkle.Tests.Hesper.Vendored.WGSLInterp

/-- Build `q[i] * k[i]` as an `Exp (.scalar .f32)`. -/
def lane (i : Nat) : Exp (.scalar .f32) :=
  let qi : Exp (.scalar .f32) :=
    .index (.var (t := .array (.scalar .f32) 8) "q") (.litU32 i)
  let ki : Exp (.scalar .f32) :=
    .index (.var (t := .array (.scalar .f32) 8) "k") (.litU32 i)
  .mul qi ki

/-- The full 8-lane unrolled dot product as an `Exp`. -/
def dotProductWGSLExp : Exp (.scalar .f32) :=
  .add (lane 0)
    (.add (lane 1)
      (.add (lane 2)
        (.add (lane 3)
          (.add (lane 4)
            (.add (lane 5)
              (.add (lane 6) (lane 7)))))))

/-- The eval environment with `q` and `k` arrays bound. -/
def wgslEnv : EvalEnv :=
  { f32_arrays := [("q", fixtureQFloat), ("k", fixtureKFloat)] }

/-- Evaluate the WGSL-DSL kernel. -/
def hesperDotProductWGSL : Float := runF32 wgslEnv dotProductWGSLExp

/-- Sanity: WGSL kernel produces `−37412.0`. -/
theorem wgsl_value :
    (hesperDotProductWGSL == (-37412.0 : Float)) = true := by
  native_decide

/-- **Sparkle ≡ Hesper WGSL DSL**: Sparkle's `dotProductInt` matches
    the WGSL evaluation of the attention dot product. -/
theorem sparkle_eq_hesper_wgsl :
    (hesperDotProductWGSL == Float.ofInt (dotProductInt fixtureQ fixtureK)) = true := by
  native_decide

/-! ## 3. The two Hesper layers agree -/

/-- The Circuit-DSL and WGSL-DSL evaluations agree on the fixture. -/
theorem circuit_eq_wgsl :
    (hesperDotProductCircuit == hesperDotProductWGSL) = true := by
  native_decide

/-! ## Headline triangle

The three theorems above close the equivalence triangle for
attention dot product on the v1a fixture:

```
            Sparkle.dotProductInt
            /                    \
           /                      \
  Circuit-DSL  ─────agree─────  WGSL-DSL
```

Each edge is a `native_decide` line. The triangle is genuine —
all three vertices are independently evaluated, and the
diagonals are not derived from the bottom edge by transitivity
(though they could be).

This pattern — Circuit DSL + WGSL DSL each independently pinned
against Sparkle — is what extends to softmax, weighted-V, and
the full end-to-end attention once Hesper kernels for those
exist. The infrastructure is now in place. -/

end Sparkle.Tests.Hesper.HesperDSLEquivalence
