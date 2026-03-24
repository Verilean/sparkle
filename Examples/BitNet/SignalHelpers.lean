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

namespace Sparkle.Examples.BitNet.SignalHelpers

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
  else
    let results : Array (Signal dom (BitVec n)) := Id.run do
      let mut res : Array (Signal dom (BitVec n)) := #[]
      let pairs := signals.size / 2
      for i in [:pairs] do
        let a := signals[2 * i]!
        let b := signals[2 * i + 1]!
        res := res.push (a + b)
      if signals.size % 2 == 1 then
        res := res.push signals[signals.size - 1]!
      return res
    adderTree results

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
  else Id.run do
    let mut result : Signal dom (BitVec n) := Signal.pure table[0]!
    for i in [:table.size] do
      let isMatch := index === Signal.pure (BitVec.ofNat k i)
      result := Signal.mux isMatch (Signal.pure table[i]!) result
    return result

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
    let results : Array (Signal dom (BitVec n)) := Id.run do
      let mut res : Array (Signal dom (BitVec n)) := #[]
      let pairs := signals.size / 2
      for i in [:pairs] do
        let a := signals[2 * i]!
        let b := signals[2 * i + 1]!
        -- Signed comparison: a > b (using toInt for signed semantics)
        let aGtB : Signal dom Bool := (fun x y => x.toInt > y.toInt) <$> a <*> b
        res := res.push (Signal.mux aGtB a b)
      if signals.size % 2 == 1 then
        res := res.push signals[signals.size - 1]!
      return res
    maxTree results

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
    : Array (Signal dom (BitVec n)) := Id.run do
  let mut results : Array (Signal dom (BitVec n)) := #[]
  for i in [:weights.size] do
    let w := weights[i]!
    if i < activations.size then
      if w == 1 then
        results := results.push activations[i]!
      else if w == -1 then
        let neg := (fun x => 0 - x) <$> activations[i]!
        results := results.push neg
  return results

/-- Build a complete ternary BitLinear layer as a Signal function.
    Applies MAC stage (pruning zeros, negating -1s) then adder tree.
    Returns the accumulated result. -/
def bitLinearSignal (weights : Array Int) (activations : Array (Signal dom (BitVec n)))
    : Signal dom (BitVec n) :=
  let macs := macStage weights activations
  if macs.size == 0 then Signal.pure 0
  else adderTree macs

-- ============================================================================
-- Dynamic MAC Stage (Runtime Weights)
-- ============================================================================

/-- Build the dynamic MAC stage: weights are 2-bit signals (runtime, from ROM).
    Decoding: 0b10 → +1 (pass-through), 0b00 → -1 (negate), else → 0.
    Returns one decoded signal per input element (no pruning). -/
def dynamicMACStage (weightCodes : Array (Signal dom (BitVec 2)))
    (activations : Array (Signal dom (BitVec n)))
    : Array (Signal dom (BitVec n)) := Id.run do
  let mut results : Array (Signal dom (BitVec n)) := #[]
  for i in [:weightCodes.size] do
    if i < activations.size then
      let wCode := weightCodes[i]!
      let act := activations[i]!
      let neg := (fun x => 0 - x) <$> act
      let isPosOne := wCode === Signal.pure 0b10#2
      let isNegOne := wCode === Signal.pure 0b00#2
      -- If +1: act, if -1: neg, else: 0
      let decoded := Signal.mux isPosOne act (Signal.mux isNegOne neg (Signal.pure 0))
      results := results.push decoded
  return results

end Sparkle.Examples.BitNet.SignalHelpers
