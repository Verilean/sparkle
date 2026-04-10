/-
  BitNet Signal DSL Helpers

  Reusable utilities for building hardware in the Signal DSL:
  - Sign extension
  - Binary adder tree (recursive pairwise addition)
  - Mux-tree LUT (lookup table via chained Signal.mux)
  - Max-tree (signed comparator tree)
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.BitNet.SignalHelpers

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

-- ============================================================================
-- Sign Extension
-- ============================================================================

/-- Sign-extend a BitVec signal from n bits to (ext + n) bits.
    Uses BitVec.signExtend internally. -/
def signExtendSignal (ext : Nat) (x : Signal dom (BitVec n))
    : Signal dom (BitVec (ext + n)) :=
  x.map (fun v => (v.signExtend (ext + n)).cast (by omega))

-- ============================================================================
-- Binary Adder Tree
-- ============================================================================

/-- Pairwise-reduce an array: pair adjacent elements with `f`, carry the
    odd tail element unchanged. Pure-functional (no Id.run / let mut). -/
def pairwiseReduce [Inhabited α] (f : α → α → α) (xs : Array α) : Array α :=
  let pairs := (List.range (xs.size / 2)).toArray.map fun i =>
    f xs[2 * i]! xs[2 * i + 1]!
  if xs.size % 2 == 1 then pairs.push xs[xs.size - 1]!
  else pairs

/-- Build a binary adder tree over a list of signals.
    Recursively reduces by pairwise addition until one signal remains.
    Returns Signal.pure 0 for empty input.

    Note: All inputs must have the same BitVec width. The output width
    equals the input width (no automatic width growth — caller is responsible
    for sign-extending inputs to the desired accumulator width first). -/
partial def adderTree (signals : Array (Signal dom (BitVec n)))
    : Signal dom (BitVec n) :=
  if signals.size == 0 then Signal.pure 0
  else if signals.size == 1 then signals[0]!
  else adderTree (pairwiseReduce (· + ·) signals)

-- ============================================================================
-- Mux-Tree LUT (Lookup Table)
-- ============================================================================

/-- Build a mux-tree lookup table: for each entry in the table,
    chain Signal.mux to select the matching entry based on index.

    Given table[0..N-1] and index signal, returns:
      if index == N-1 then table[N-1]
      else if index == N-2 then table[N-2]
      ...
      else table[0]  (default)

    All table entries are constant signals (Signal.pure). -/
def lutMuxTree (table : Array (BitVec n)) (index : Signal dom (BitVec k))
    : Signal dom (BitVec n) :=
  if table.size == 0 then Signal.pure 0
  else
    let init := Signal.pure table[0]!
    (List.range table.size).toArray.foldl (init := init) fun acc i =>
      let isMatch := index === (BitVec.ofNat k i)
      Signal.mux isMatch (Signal.pure table[i]!) acc

-- ============================================================================
-- Max-Tree (Signed Comparator Reduction)
-- ============================================================================

/-- Build a binary max-reduction tree using signed comparison.
    Recursively finds the maximum value via pairwise comparison + mux.

    Uses signed greater-than comparison (toInt-based) for correct
    handling of negative values in two's complement. -/
partial def maxTree (signals : Array (Signal dom (BitVec n)))
    : Signal dom (BitVec n) :=
  if signals.size == 0 then Signal.pure 0
  else if signals.size == 1 then signals[0]!
  else
    let reduced := pairwiseReduce (fun a b =>
      let aGtB : Signal dom Bool := (fun x y => x.toInt > y.toInt) <$> a <*> b
      Signal.mux aGtB a b) signals
    maxTree reduced

-- ============================================================================
-- Ternary MAC Stage (Hardwired Weights)
-- ============================================================================

/-- Build the MAC (Multiply-Accumulate) stage for ternary BitLinear.
    For each weight:
    - w = 0: pruned (no hardware)
    - w = +1: pass-through
    - w = -1: negate (0 - x)

    Returns only non-zero contributions as an array of signals.
    Activations are provided as an array of signals. -/
def macStage (weights : Array Int) (activations : Array (Signal dom (BitVec n)))
    : Array (Signal dom (BitVec n)) :=
  let pairs := (List.range weights.size).toArray.filterMap fun i =>
    if i < activations.size then
      let w := weights[i]!
      if w == 1 then some activations[i]!
      else if w == -1 then some (-activations[i]!)
      else none
    else none
  pairs

/-- Build a complete ternary BitLinear layer as a Signal function.
    Applies MAC stage (pruning zeros, negating -1s) then adder tree.
    Returns the accumulated result. -/
def bitLinearSignal (weights : Array Int) (activations : Array (Signal dom (BitVec n)))
    : Signal dom (BitVec n) :=
  let macs := macStage weights activations
  adderTree macs  -- adderTree returns Signal.pure 0 for empty input

-- ============================================================================
-- Dynamic MAC Stage (Runtime Weights)
-- ============================================================================

/-- Build the dynamic MAC stage: weights are 2-bit signals (runtime, from ROM).
    Decoding: 0b10 → +1 (pass-through), 0b00 → -1 (negate), else → 0.
    Returns one decoded signal per input element (no pruning). -/
def dynamicMACStage (weightCodes : Array (Signal dom (BitVec 2)))
    (activations : Array (Signal dom (BitVec n)))
    : Array (Signal dom (BitVec n)) :=
  let len := min weightCodes.size activations.size
  (List.range len).toArray.map fun i =>
    let wCode := weightCodes[i]!
    let act := activations[i]!
    let neg := -act
    let isPosOne := wCode === 0b10#2
    let isNegOne := wCode === 0b00#2
    Signal.mux isPosOne act (Signal.mux isNegOne neg (Signal.pure 0))

end Sparkle.IP.BitNet.SignalHelpers
