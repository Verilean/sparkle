/-
  BitNet Signal DSL Helpers

  Reusable utilities for building hardware in the Signal DSL:
  - Sign extension
  - Binary adder tree (recursive pairwise addition)
  - Mux-tree LUT (lookup table via chained Signal.mux)
  - Max-tree (signed comparator tree)

  Design principle: all helpers are `@[reducible]` and use `List`-based
  structural recursion so they fully reduce at elaboration time. The
  Verilog backend sees only concrete `Signal` combinators, never Array
  operations (which internally use `Id.run` and break synthesis).
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
    Uses `BitVec.signExtend` in a `Signal.map` lambda — the Verilog
    backend translates this to `{{ext{MSB}}, signal}`. -/
def signExtendSignal (ext : Nat) (x : Signal dom (BitVec n))
    : Signal dom (BitVec (ext + n)) :=
  Signal.map (BitVec.signExtend (ext + n) ·) x

-- ============================================================================
-- List-based tree reduction (synthesizable)
-- ============================================================================

/-- Pairwise-reduce a list: pair adjacent elements with `f`, carry the
    odd tail element unchanged. Structural recursion on the list. -/
@[reducible] def pairwiseReduceList (f : α → α → α) : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: rest => f x y :: pairwiseReduceList f rest

/-- Reduce a list to a single element by repeatedly pairing with `f`.
    Uses fuel (= input length) for termination. -/
@[reducible] def treeReduceAux (f : α → α → α) (zero : α) (fuel : Nat) : List α → α
  | [] => zero
  | [x] => x
  | xs => match fuel with
    | 0 => xs.headD zero
    | fuel' + 1 => treeReduceAux f zero fuel' (pairwiseReduceList f xs)

@[reducible] def treeReduce (f : α → α → α) (zero : α) (xs : List α) : α :=
  treeReduceAux f zero xs.length xs

-- ============================================================================
-- Binary Adder Tree
-- ============================================================================

/-- Build a binary adder tree over a list of signals.
    Returns Signal.pure 0 for empty input. Fully reduces at elab time. -/
@[reducible] def adderTree (signals : Array (Signal dom (BitVec n)))
    : Signal dom (BitVec n) :=
  treeReduce (· + ·) (Signal.pure 0) signals.toList

-- ============================================================================
-- Mux-Tree LUT (Lookup Table)
-- ============================================================================

/-- Build a mux-tree LUT from a list of (index, value) entries. -/
@[reducible] def lutMuxTreeList (index : Signal dom (BitVec k))
    (dflt : Signal dom (BitVec n))
    : List (BitVec n × Nat) → Signal dom (BitVec n)
  | [] => dflt
  | (v, i) :: rest =>
    let isMatch := index === (BitVec.ofNat k i)
    Signal.mux isMatch (Signal.pure v) (lutMuxTreeList index dflt rest)

/-- Build a mux-tree lookup table from an array of BitVec constants. -/
def lutMuxTree (table : Array (BitVec n)) (index : Signal dom (BitVec k))
    : Signal dom (BitVec n) :=
  if table.size == 0 then Signal.pure 0
  else
    let entries := table.toList.zipIdx
    let dflt : BitVec n := table.toList.headD 0
    lutMuxTreeList index (Signal.pure dflt) entries

-- ============================================================================
-- Max-Tree (Signed Comparator Reduction)
-- ============================================================================

/-- Build a binary max-reduction tree using signed comparison + mux. -/
@[reducible] def maxTree (signals : Array (Signal dom (BitVec n)))
    : Signal dom (BitVec n) :=
  treeReduce
    (fun a b =>
      let aGtB : Signal dom Bool := (fun x y => x.toInt > y.toInt) <$> a <*> b
      Signal.mux aGtB a b)
    (Signal.pure 0)
    signals.toList

-- ============================================================================
-- Ternary MAC Stage (Hardwired Weights)
-- ============================================================================

/-- Process one weight-activation pair: +1 → pass, -1 → negate, 0 → skip. -/
@[reducible] def macOneList (w : Int) (act : Signal dom (BitVec n))
    : List (Signal dom (BitVec n)) :=
  if w == 1 then [act]
  else if w == -1 then [-act]
  else []

/-- Build MAC contributions from weight-activation pairs (List-based). -/
@[reducible] def macStageList : List (Int × Signal dom (BitVec n))
    → List (Signal dom (BitVec n))
  | [] => []
  | (w, act) :: rest => macOneList w act ++ macStageList rest

/-- Build the MAC stage for ternary BitLinear.
    Returns only non-zero contributions as a list of signals. -/
def macStage (weights : Array Int) (activations : Array (Signal dom (BitVec n)))
    : Array (Signal dom (BitVec n)) :=
  let pairs := weights.toList.zip activations.toList
  (macStageList pairs).toArray

/-- Build a complete ternary BitLinear layer as a Signal function.
    Applies MAC stage (pruning zeros, negating -1s) then adder tree.
    Returns the accumulated result. -/
@[reducible] def bitLinearSignal (weights : Array Int) (activations : Array (Signal dom (BitVec n)))
    : Signal dom (BitVec n) :=
  let pairs := weights.toList.zip activations.toList
  let macs := macStageList pairs
  treeReduce (· + ·) (Signal.pure 0) macs

-- ============================================================================
-- Dynamic MAC Stage (Runtime Weights)
-- ============================================================================

/-- Build one decoded dynamic MAC element. -/
@[reducible] def dynamicMACOne (wCode : Signal dom (BitVec 2))
    (act : Signal dom (BitVec n)) : Signal dom (BitVec n) :=
  let neg := -act
  let isPosOne := wCode === 0b10#2
  let isNegOne := wCode === 0b00#2
  Signal.mux isPosOne act (Signal.mux isNegOne neg (Signal.pure 0))

/-- Build the dynamic MAC stage from a list of (weight-code, activation) pairs. -/
@[reducible] def dynamicMACStageList : List (Signal dom (BitVec 2) × Signal dom (BitVec n))
    → List (Signal dom (BitVec n))
  | [] => []
  | (w, act) :: rest => dynamicMACOne w act :: dynamicMACStageList rest

/-- Build the dynamic MAC stage: weights are 2-bit signals (runtime, from ROM). -/
def dynamicMACStage (weightCodes : Array (Signal dom (BitVec 2)))
    (activations : Array (Signal dom (BitVec n)))
    : Array (Signal dom (BitVec n)) :=
  let pairs := weightCodes.toList.zip activations.toList
  (dynamicMACStageList pairs).toArray

end Sparkle.IP.BitNet.SignalHelpers
