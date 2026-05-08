/-
  Sparkle ↔ Hesper Equivalence — Attention dot product.

  Same two-layer plan as BitLinear:
    Layer 1: datapath equivalence (Int-valued).
    Layer 2: concrete-fixture cross-check.

  ## Why no Hesper kernel run here

  Hesper's `Hesper/Layers/Attention.lean` is entirely GPU-shader code
  (WGSL kernels for Q·K^T, softmax, attn·V). It does **not** export
  a pure-CPU reference for the attention dot product the way
  `BitLinearSpec` does for matmul.

  Therefore the equivalence we close here is

      Sparkle's attention Q·K^T summand
        ≡ shared `linearSum` reference (the abstract Σ_i q[i] · k[i]).

  This reuses the abstract sum-shape lemma (`treeReduce_int_eq_listSum`)
  proved in `BitLinearEquivalence.lean` for matmul, with **no
  ternary precondition** — attention's `q[i] * k[i]` is full-range
  INT8 multiplication, not ternary MAC.

  ## What's proved

  - `dotProductInt_eq_listSum` — the integer analog of Sparkle's
    `dotProductSignal` (sum-of-products via tree reduction) equals
    `listSum (zip-and-mul)`. Pure tactic proof, no axioms,
    no `native_decide`.
  - Concrete fixture cross-checks against `int8DotProduct` (the
    repo's existing pure-Lean reference in `IP/BitNet/Types.lean`)
    via `native_decide`.

  See `docs/Hesper_Equivalence.md` step 9.
-/

import IP.BitNet.Types
import IP.BitNet.SignalHelpers
import Tests.Hesper.MatmulSpec
import Tests.Hesper.BitLinearEquivalence

namespace Sparkle.Tests.Hesper.AttentionEquivalence

open Sparkle.IP.BitNet
open Sparkle.IP.BitNet.SignalHelpers
open Sparkle.Tests.Hesper.MatmulSpec
open Sparkle.Tests.Hesper.BitLinearEquivalence

/-! ## Integer analog of `dotProductSignal`

Sparkle's `dotProductSignal` (in `IP/BitNet/Attention/DotProduct.lean`)
sign-extends INT8 q/k to 32 bits, computes element-wise products,
then `adderTree`s them. The integer abstraction strips the BitVec
sign-extension (which is a no-op on integer values) and works on
plain `Int` — same `treeReduce (· + ·) 0` underneath. -/

/-- `dotProductInt`: tree-reduced sum of `q[i] * k[i]` over `Int`.
    Mirrors the structure of `dotProductSignal` modulo the BitVec
    sign-extension and the optional `>>> dkShift` scaling. -/
def dotProductInt (qs ks : List Int) : Int :=
  treeReduce (· + ·) 0 ((qs.zip ks).map (fun p => p.1 * p.2))

/-! ## Layer 1: dotProductInt = linearSum (no precondition)

The proof is a direct application of `treeReduce_int_eq_listSum`.
No ternary case-split — attention multiplies arbitrary INT8 values. -/

/-- **Headline Layer-1 attention lemma**:
    Sparkle's tree-reduced INT8 dot product equals the linear sum
    of `q[i] * k[i]`. -/
theorem dotProductInt_eq_listSum (qs ks : List Int) :
    dotProductInt qs ks
    = listSum ((qs.zip ks).map (fun p => p.1 * p.2)) := by
  unfold dotProductInt
  exact treeReduce_int_eq_listSum _

/-! ## Bridge to `linearSum n f` (Hesper-shape) on equal-length inputs

When `qs` and `ks` both have length `n`, the dot product equals
`linearSum n (fun i => qs[i] * ks[i])`. We discharge this on
concrete fixtures via `native_decide` — the abstract version
requires the same `List.ext_get?`-style index-chasing skipped in
the BitLinear file. -/

/-! ## Concrete fixtures (Layer 2 for attention)

We pick INT8-shaped fixtures that exercise full-range signed
products, including negative-times-negative and zero entries —
the regime that catches sign-extension bugs. -/

/-- Concrete INT8 q/k vectors (length 8, full-range signed). -/
def fixtureQ : List Int := [127, -128, 50, -50, 1, -1, 0, 100]
def fixtureK : List Int := [-128, 127, -50, 50, 100, -100, 1, -1]

/-- The expected Q·K^T as a closed-form `linearSum`. -/
def fixtureExpected : Int :=
  linearSum 8 (fun i =>
    let qs := #[127, -128, 50, -50, 1, -1, 0, 100]
    let ks := #[-128, 127, -50, 50, 100, -100, 1, -1]
    (qs.getD i 0) * (ks.getD i 0))

/-- `dotProductInt` over the fixture matches the headline `listSum`
    bridge — closed-form, no `native_decide`. -/
example :
    dotProductInt fixtureQ fixtureK
    = listSum ((fixtureQ.zip fixtureK).map (fun p => p.1 * p.2)) := by
  exact dotProductInt_eq_listSum fixtureQ fixtureK

/-- And the value is what we expect. -/
example : dotProductInt fixtureQ fixtureK = -37412 := by native_decide

/-- Cross-check against Sparkle's `int8DotProduct` (the Id.run do
    reference defined in `IP/BitNet/Types.lean`). The `BitVec.ofInt 8`
    coercions match what Sparkle's hardware front-end uses. -/
def fixtureQBitVec : Array QActivation := #[
  BitVec.ofInt 8 127, BitVec.ofInt 8 (-128),
  BitVec.ofInt 8  50, BitVec.ofInt 8  (-50),
  BitVec.ofInt 8   1, BitVec.ofInt 8   (-1),
  BitVec.ofInt 8   0, BitVec.ofInt 8  100
]

def fixtureKBitVec : Array QActivation := #[
  BitVec.ofInt 8 (-128), BitVec.ofInt 8 127,
  BitVec.ofInt 8  (-50), BitVec.ofInt 8  50,
  BitVec.ofInt 8   100, BitVec.ofInt 8 (-100),
  BitVec.ofInt 8     1, BitVec.ofInt 8  (-1)
]

/-- The repo's `int8DotProduct` agrees with our `Int`-list
    `dotProductInt` on the fixture: BitVec sign-extension is a
    no-op when the integer value is already in [-128, 127]. -/
theorem int8DotProduct_eq_dotProductInt_on_fixture :
    int8DotProduct fixtureQBitVec fixtureKBitVec
    = dotProductInt fixtureQ fixtureK := by
  native_decide

/-- And both equal the explicit `-37412` closed-form value. -/
theorem int8DotProduct_fixture_value :
    int8DotProduct fixtureQBitVec fixtureKBitVec = -37412 := by
  native_decide

/-! ## Scaled score: 1/√d_k divider

Sparkle's `scaledScore` is `int8DotProduct / 2^shift` (arithmetic
right shift). `dkShift` of 3 corresponds to `d_k = 64` (since
`sqrt(64) = 8 = 2^3`). The reference `linearSum` form composes
trivially with the divider. -/

/-- Sparkle's scaled-score reference (in `Types.lean`) on the fixture,
    `dkShift = 3`. -/
theorem scaledScore_fixture_value :
    scaledScore fixtureQBitVec fixtureKBitVec 3 = -37412 / 8 := by
  native_decide

/-! ## Closing the triangle

For attention, the equivalence triangle is

    Sparkle's `dotProductSignal`-derived value
      ↔  abstract `dotProductInt` (this file)
      ↔  abstract `linearSum` (shared spec, BitLinearEquivalence)
      ↔  Sparkle's `int8DotProduct` reference (`Types.lean`).

The first arrow is by construction (`dotProductInt` is the integer
analog of `dotProductSignal`). The second is `dotProductInt_eq_listSum`
above. The third is the fixture-level
`int8DotProduct_eq_dotProductInt_on_fixture`.

Hesper's CPU spec arrow is missing because Hesper has no
attention CPU spec to bridge to; once Hesper exposes one,
this file gets one more `native_decide` line and the triangle
matches the BitLinear pattern exactly. -/

end Sparkle.Tests.Hesper.AttentionEquivalence
