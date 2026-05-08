/-
  Sparkle ↔ Hesper Equivalence — Layer 1 (datapath, Int-valued).

  Goal: prove that Sparkle's tree-reduced ternary BitLinear computes
  the same `Int` value as Hesper's linear-summed `forwardRow` for the
  same weights and activations. We work entirely over `Int`; float
  and fixed-point bridges live in later files.

  See docs/Hesper_Equivalence.md.

  This file establishes the **abstract sum-shape equivalence**:
  Sparkle's `treeReduce (· + ·) 0 xs` over a list of `Int` summands is
  the same as `linearSum xs.length f` (= Hesper's `rangeSum`).
-/

import IP.BitNet.SignalHelpers
import Tests.Hesper.MatmulSpec
import Tests.Hesper.Vendored.BitLinearSpecInt

namespace Sparkle.Tests.Hesper.BitLinearEquivalence

open Sparkle.IP.BitNet.SignalHelpers
open Sparkle.Tests.Hesper.MatmulSpec
open Sparkle.Tests.Hesper.Vendored.BitLinearSpecInt

/-! ## Sum-shape: tree reduction = linear sum (over Int)

The Sparkle adder tree reduces an `n`-element list with binary `+`.
For an associative-and-commutative `+ : Int → Int → Int`, the result
is independent of pairing — it equals `List.foldr (· + ·) 0 xs`.

We avoid Hesper's `2^k` restriction (Sparkle's lists are arbitrary
length); the proof below uses ordinary list induction.
-/

/-- Sum a list of Ints. -/
def listSum : List Int → Int
  | []       => 0
  | x :: xs  => x + listSum xs

/-- A pair-reducing pass at most halves the list length (rounded up). -/
theorem pairwiseReduceList_length_le {α : Type _} (f : α → α → α)
    (xs : List α) : (pairwiseReduceList f xs).length ≤ xs.length := by
  induction xs using pairwiseReduceList.induct with
  | case1 => simp [pairwiseReduceList]
  | case2 _ => simp [pairwiseReduceList]
  | case3 x y rest ih =>
    show (f x y :: pairwiseReduceList f rest).length ≤ (x :: y :: rest).length
    simp [List.length]
    omega

/-- One pair-reducing pass preserves the linear sum. -/
theorem listSum_pairwiseReduce (xs : List Int) :
    listSum (pairwiseReduceList (· + ·) xs) = listSum xs := by
  induction xs using pairwiseReduceList.induct with
  | case1 => simp [listSum]
  | case2 x => simp [listSum]
  | case3 x y rest ih =>
    -- pairwiseReduceList (x::y::rest) = (x+y) :: pairwiseReduceList rest
    show listSum ((x + y) :: pairwiseReduceList (· + ·) rest)
       = listSum (x :: y :: rest)
    simp [listSum, ih, Int.add_assoc]

/-- Tree reduction (with sufficient fuel) equals linear sum. -/
theorem treeReduceAux_eq_listSum (xs : List Int) (fuel : Nat)
    (h : xs.length ≤ fuel) :
    treeReduceAux (· + ·) 0 fuel xs = listSum xs := by
  induction fuel generalizing xs with
  | zero =>
    -- xs.length ≤ 0 ⇒ xs = []
    have hzero : xs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
    subst hzero
    simp [treeReduceAux, listSum]
  | succ n ih =>
    cases xs with
    | nil => simp [treeReduceAux, listSum]
    | cons a as =>
      cases as with
      | nil => simp [treeReduceAux, listSum]
      | cons b bs =>
        show treeReduceAux (· + ·) 0 (n+1) (a :: b :: bs) = listSum (a :: b :: bs)
        unfold treeReduceAux
        simp only
        have hrest := pairwiseReduceList_length_le (· + ·) bs
        have hlen : (pairwiseReduceList (· + ·) (a :: b :: bs)).length ≤ n := by
          show (((· + ·) a b) :: pairwiseReduceList (· + ·) bs).length ≤ n
          simp [List.length] at h ⊢
          omega
        rw [ih _ hlen]
        exact listSum_pairwiseReduce (a :: b :: bs)

/-- The headline sum-shape lemma: Sparkle's `treeReduce (· + ·) 0`
    over an `Int` list equals the linear `listSum`. -/
theorem treeReduce_int_eq_listSum (xs : List Int) :
    treeReduce (· + ·) 0 xs = listSum xs := by
  unfold treeReduce
  exact treeReduceAux_eq_listSum xs xs.length (Nat.le_refl _)

/-! ## Sanity check on small lists -/

example : treeReduce (· + ·) 0 [1, 2, 3, 4, 5] = 15 := by native_decide
example : listSum     [1, 2, 3, 4, 5]                = 15 := by native_decide

/-! ## Bridge to `linearSum` (Hesper's `rangeSum`)

The shared spec uses `linearSum n f`, indexed by `Nat → Int`. The
list and function views are interchangeable for any `xs` of the form
`(List.range n).map f`.
-/

/-- `listSum` of `xs ++ [a]` equals `listSum xs + a`. -/
theorem listSum_append_singleton (xs : List Int) (a : Int) :
    listSum (xs ++ [a]) = listSum xs + a := by
  induction xs with
  | nil => simp [listSum]
  | cons x xs ih => simp [listSum, ih]; omega

/-- `listSum` of `(List.range n).map f` equals `linearSum n f`. -/
theorem listSum_range_map_eq_linearSum (n : Nat) (f : Nat → Int) :
    listSum ((List.range n).map f) = linearSum n f := by
  induction n with
  | zero =>
    show listSum ((List.range 0).map f) = linearSum 0 f
    rw [List.range_zero]
    simp [List.map, listSum, linearSum]
  | succ n ih =>
    have hr : List.range (n+1) = List.range n ++ [n] := List.range_succ
    rw [hr, List.map_append, List.map_singleton, listSum_append_singleton, ih]
    rfl

/-- Headline Layer-1 lemma (Int-valued, abstract):

    Sparkle's `treeReduce` over `(List.range n).map f` equals Hesper's
    `linearSum n f`, which equals one row of the shared `matmulRefRow`
    when `f j = W[i,j] * x[j]`. -/
theorem treeReduce_eq_linearSum (n : Nat) (f : Nat → Int) :
    treeReduce (· + ·) 0 ((List.range n).map f) = linearSum n f := by
  rw [treeReduce_int_eq_listSum]
  exact listSum_range_map_eq_linearSum n f

/-! ## Sparkle side: ternary MAC + tree-sum on `Int`

The Sparkle hardware computes `Σ_j w[j] * x[j]` via:
  1. `macStageList`: drop `w == 0`, negate `w == -1`, pass `w == +1`
  2. `treeReduce (· + ·) 0`: binary adder tree

We instantiate that pipeline on `Int` (no `Signal` / `BitVec` wrapping)
so the abstract sum-shape lemma applies directly. This is the
"datapath equivalence on Int" that the project plan calls Layer 1.

The Signal-DSL version (`bitLinearSignal`) is just this with the
operands lifted to `Signal dom (BitVec n)` constants, so the same
proof structure carries over once a `BitVec.toInt` bridge is added —
that bridge is the Layer 2 fixed-point work.
-/

/-- Int analog of Sparkle's `macOneList`: the contribution list for
    one (weight, activation) pair. Mirrors `macOneList` exactly modulo
    the `Signal` wrapper. -/
def macOneListInt (w : Int) (act : Int) : List Int :=
  if w == 1 then [act]
  else if w == -1 then [-act]
  else []

/-- Int analog of Sparkle's `macStageList`. -/
def macStageListInt : List (Int × Int) → List Int
  | []                => []
  | (w, act) :: rest  => macOneListInt w act ++ macStageListInt rest

/-- Int analog of Sparkle's `bitLinearSignal`: ternary MAC + tree sum,
    over plain `Int` instead of `Signal dom (BitVec n)`. -/
def bitLinearInt (weights : List Int) (activations : List Int) : Int :=
  treeReduce (· + ·) 0 (macStageListInt (weights.zip activations))

/-! ### Sparkle-Int = matmulRefRow

The proof has two phases:
  * `macStageListInt_listSum` — pruning zeros and negating −1 entries
    is sum-preserving; the remaining `listSum` equals the full
    weight·activation sum.
  * `bitLinearInt_eq_listSum` — combines that with `treeReduce_int_eq_listSum`.

Then a thin wrapper proves the relation to `matmulRefRow`. -/

/-- A weight is ternary if it is `-1`, `0`, or `+1`. -/
def isTernary (w : Int) : Prop := w = -1 ∨ w = 0 ∨ w = 1

instance : DecidablePred isTernary := fun w => by
  unfold isTernary; exact inferInstance

/-- `listSum` of `xs ++ ys` splits as expected. -/
theorem listSum_append (xs ys : List Int) :
    listSum (xs ++ ys) = listSum xs + listSum ys := by
  induction xs with
  | nil => simp [listSum]
  | cons x xs ih => simp [listSum, ih]; omega

/-- The ternary-MAC stage preserves the weight·activation sum. -/
theorem macStageListInt_listSum
    (pairs : List (Int × Int))
    (h : ∀ p ∈ pairs, isTernary p.1) :
    listSum (macStageListInt pairs)
    = listSum (pairs.map (fun p => p.1 * p.2)) := by
  induction pairs with
  | nil => simp [macStageListInt, listSum, List.map]
  | cons p rest ih =>
    obtain ⟨w, a⟩ := p
    have hw : isTernary w := h _ (List.mem_cons_self ..)
    have hrest : ∀ q ∈ rest, isTernary q.1 := fun q hq =>
      h q (List.mem_cons_of_mem _ hq)
    have ihrest := ih hrest
    show listSum (macOneListInt w a ++ macStageListInt rest)
       = listSum (((w, a) :: rest).map (fun p => p.1 * p.2))
    rw [listSum_append]
    rcases hw with hneg | hzero | hpos
    · subst hneg
      simp [macOneListInt, listSum, List.map_cons, ihrest]
    · subst hzero
      simp [macOneListInt, listSum, List.map_cons, ihrest]
    · subst hpos
      simp [macOneListInt, listSum, List.map_cons, ihrest]

/-- **Headline Sparkle-side lemma (Int)**:
    Sparkle's `bitLinearInt` (ternary MAC + adder tree) over an `Int`
    list equals the linear sum `listSum (zip-and-multiply)`. -/
theorem bitLinearInt_eq_listSum
    (weights activations : List Int)
    (h : ∀ w ∈ weights, isTernary w) :
    bitLinearInt weights activations
    = listSum ((weights.zip activations).map (fun p => p.1 * p.2)) := by
  unfold bitLinearInt
  rw [treeReduce_int_eq_listSum]
  apply macStageListInt_listSum
  intro p hp
  -- p ∈ zip weights activations ⇒ p.1 ∈ weights
  have : p.1 ∈ weights := by
    have := List.of_mem_zip hp
    exact this.1
  exact h _ this

/-! ### Sparkle ↔ ref triangle (concrete fixture form)

`bitLinearInt_eq_listSum` is the abstract statement. Tying it to
`matmulRefRow` for an arbitrary `Array Int` requires a `zip` ↔
`range-map` bridge that involves a non-trivial `List.ext_get?` /
`getD`-chasing argument. Per the project preference for
`native_decide` on concrete fixtures, we discharge that bridge
per-fixture below (the v1a-shaped tests share the same
`fixtureWeights1x128` / `fixtureInput128`). -/

/-! ## Layer 1.5: Hesper `forwardRowInt` ↔ shared `matmulRefRow`

Strategy: per the project's preference for `native_decide` over
axiomatic generality, we prove the Hesper-side ↔ shared-spec bridge
on **concrete fixtures** rather than as a universal theorem. The
fixtures are sized to the BitNet v1a config (`inDim = 128`,
`outDim` ∈ {1, 4}, `scale = 1`), which is exactly the regime the
hardware actually exercises — see `IP/RV32/BitNetPeripheral.lean`.

The chain we close, end-to-end:

  Hesper.forwardRowInt (packI2SInt W ...) scale ... input
    = matmulRefAll W input scale inDim outDim
    = (Sparkle's BitLinear over Int with the same W, input, scale)

This file does the first equality (Hesper ↔ ref). The Sparkle ↔ ref
direction is the abstract `treeReduce_eq_linearSum` above —
specialized to `f j = W[i,j] * x[j]`.

For each fixture: one `native_decide` line discharges the round-trip.
This is by design — see `feedback_hesper_float_bridge.md`.
-/

/-! ### v1a-shaped fixture: `inDim = 128`, `outDim = 1`, scale = 1

Weights and activations follow the same `(j % 3 - 1)` ternary pattern
plus a small input perturbation; the expected output is computed from
`matmulRefRow` so divergence in either direction would `false`-out the
proof. -/

/-- v1a fixture weights, row 0: `(j % 3 - 1)` for `j ∈ [0, 128)`. -/
def fixtureWeights1x128 : Array Int := patternRow 128

/-- v1a fixture activations: `(j % 5 - 2)` for `j ∈ [0, 128)`. -/
def fixtureInput128 : Array Int :=
  (Array.range 128).map (fun i => ((i % 5 : Nat) : Int) - 2)

/-- Concrete cross-check: Hesper's `forwardRowInt` on the v1a-shaped
    fixture equals one row of the shared `matmulRefRow`.

    This is the central round-trip the user asked for — datapath
    equivalence between Hesper and the shared spec on the same input
    set the v1a hardware uses. -/
theorem forwardRowInt_eq_matmulRefRow_v1a :
    (forwardRowInt (packI2SInt fixtureWeights1x128 128 1) 1 128 1
       fixtureInput128).getD 0 0
    = matmulRefRow fixtureWeights1x128 fixtureInput128 1 128 1 0 := by
  native_decide

/-! ### Same fixture, scale ≠ 1.  Verifies that scaling propagates. -/

theorem forwardRowInt_eq_matmulRefRow_v1a_scale3 :
    (forwardRowInt (packI2SInt fixtureWeights1x128 128 1) 3 128 1
       fixtureInput128).getD 0 0
    = matmulRefRow fixtureWeights1x128 fixtureInput128 3 128 1 0 := by
  native_decide

/-! ### Negative-scale check (catches sign bugs). -/

theorem forwardRowInt_eq_matmulRefRow_v1a_negScale :
    (forwardRowInt (packI2SInt fixtureWeights1x128 128 1) (-1) 128 1
       fixtureInput128).getD 0 0
    = matmulRefRow fixtureWeights1x128 fixtureInput128 (-1) 128 1 0 := by
  native_decide

/-! ### `outDim = 4` fixture (cross-row sanity).

    Same input, four weight rows. Tests that Hesper's row-major byte
    layout (rows are `bytesPerRow = 32` apart) matches `matmulRefRow`'s
    row-major Array layout. -/

/-- 4 weight rows, each a `patternRow 128` shifted by row index `i`:
    row `i`, col `j` = `((i + j) % 3 - 1)`. Total array length 512. -/
def fixtureWeights4x128 : Array Int :=
  (Array.range (4 * 128)).map fun ij =>
    let i := ij / 128
    let j := ij % 128
    (((i + j) % 3 : Nat) : Int) - 1

theorem forwardRowInt_eq_matmulRefAll_4x128_row0 :
    (forwardRowInt (packI2SInt fixtureWeights4x128 128 4) 1 128 4
       fixtureInput128).getD 0 0
    = matmulRefRow fixtureWeights4x128 fixtureInput128 1 128 4 0 := by
  native_decide

theorem forwardRowInt_eq_matmulRefAll_4x128_row1 :
    (forwardRowInt (packI2SInt fixtureWeights4x128 128 4) 1 128 4
       fixtureInput128).getD 1 0
    = matmulRefRow fixtureWeights4x128 fixtureInput128 1 128 4 1 := by
  native_decide

theorem forwardRowInt_eq_matmulRefAll_4x128_row2 :
    (forwardRowInt (packI2SInt fixtureWeights4x128 128 4) 1 128 4
       fixtureInput128).getD 2 0
    = matmulRefRow fixtureWeights4x128 fixtureInput128 1 128 4 2 := by
  native_decide

theorem forwardRowInt_eq_matmulRefAll_4x128_row3 :
    (forwardRowInt (packI2SInt fixtureWeights4x128 128 4) 1 128 4
       fixtureInput128).getD 3 0
    = matmulRefRow fixtureWeights4x128 fixtureInput128 1 128 4 3 := by
  native_decide

/-! ### Whole-output bridge: full Array equality on the 4×128 fixture.

    Sums up the per-row checks into a single Array equality, which is
    what the higher layers (LinearSignal, BitNet SoC) consume. -/

theorem forwardRowInt_eq_matmulRefAll_4x128 :
    forwardRowInt (packI2SInt fixtureWeights4x128 128 4) 1 128 4
        fixtureInput128
    = matmulRefAll fixtureWeights4x128 fixtureInput128 1 128 4 := by
  native_decide

/-! ### Sparkle ↔ shared spec on the same fixtures

We've shown abstractly (`bitLinearInt_eq_listSum`) that Sparkle's
ternary MAC + tree sum equals `listSum (zip-and-multiply)` for any
ternary weights. To pin Sparkle to `matmulRefRow` on the v1a
fixtures, we use `native_decide` again — same pattern as the
Hesper-side bridge above. Together with
`forwardRowInt_eq_matmulRefRow_v1a*`, this closes the triangle:

    Sparkle.bitLinearInt ↔ matmulRefRow ↔ Hesper.forwardRowInt
-/

/-- Sparkle's ternary tree-MAC equals `matmulRefRow` for one row of
    the v1a-shaped fixture. -/
theorem bitLinearInt_eq_matmulRefRow_v1a :
    bitLinearInt fixtureWeights1x128.toList fixtureInput128.toList
    = matmulRefRow fixtureWeights1x128 fixtureInput128 1 128 1 0 := by
  native_decide

/-- Per-row Sparkle ↔ ref check on the 4×128 fixture, row 0. -/
theorem bitLinearInt_eq_matmulRefRow_4x128_row0 :
    bitLinearInt
        (fixtureWeights4x128.toList.take 128)
        fixtureInput128.toList
    = matmulRefRow fixtureWeights4x128 fixtureInput128 1 128 4 0 := by
  native_decide

/-- Per-row Sparkle ↔ ref check on the 4×128 fixture, row 1. -/
theorem bitLinearInt_eq_matmulRefRow_4x128_row1 :
    bitLinearInt
        ((fixtureWeights4x128.toList.drop 128).take 128)
        fixtureInput128.toList
    = matmulRefRow fixtureWeights4x128 fixtureInput128 1 128 4 1 := by
  native_decide

/-! ### Closure of the Hesper ↔ Sparkle triangle (one row, v1a)

By transitivity through `matmulRefRow`, Hesper's `forwardRowInt` and
Sparkle's `bitLinearInt` compute the same `Int` value on the v1a
fixture. -/

theorem hesper_eq_sparkle_v1a :
    (forwardRowInt (packI2SInt fixtureWeights1x128 128 1) 1 128 1
       fixtureInput128).getD 0 0
    = bitLinearInt fixtureWeights1x128.toList fixtureInput128.toList := by
  rw [forwardRowInt_eq_matmulRefRow_v1a, ← bitLinearInt_eq_matmulRefRow_v1a]

end Sparkle.Tests.Hesper.BitLinearEquivalence
