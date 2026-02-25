/-
  Weight ROM Helpers

  Utilities for building read-only memory (ROM) from weight arrays,
  and converting float32 quantization scales to integer mult+shift pairs.
-/

import Sparkle
import Examples.YOLOv8.Types

namespace Sparkle.Examples.YOLOv8.Tests.WeightROM

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Convert array to init function for Signal.memoryWithInit.
    Addresses beyond the array size return 0. -/
def arrayToInitFn {n addrWidth : Nat} (arr : Array (BitVec n)) : BitVec addrWidth → BitVec n :=
  fun addr =>
    let idx := addr.toNat
    if h : idx < arr.size then arr[idx] else 0#n

/-- Build a read-only ROM signal from an array.
    Uses Signal.memoryWithInit with writeEnable permanently false. -/
def makeROM {dom : DomainConfig} {n addrWidth : Nat}
    (data : Array (BitVec n))
    (readAddr : Signal dom (BitVec addrWidth))
    : Signal dom (BitVec n) :=
  Signal.memoryWithInit (arrayToInitFn data)
    (Signal.pure 0) (Signal.pure 0) (Signal.pure false) readAddr

/-- Convert a float32 quantization scale to integer multiplier + shift pair.
    Approximates: output ≈ (input * mult) >> shift
    Uses the standard fixed-point conversion: find shift such that
    scale * 2^shift fits in 16 bits. -/
def scaleToMultShift (scale : Float) : BitVec 16 × BitVec 5 :=
  -- Find the best shift (try 0..31)
  let bestShift := Id.run do
    let mut bestS : Nat := 0
    let mut bestErr : Float := Float.ofScientific 1 false 10  -- large initial error
    for s in List.range 32 do
      let mult := scale * Float.ofNat (2 ^ s)
      if mult >= 1.0 && mult < 32768.0 then
        let rounded := mult.round
        let err := Float.abs (mult - rounded)
        if err < bestErr then
          bestErr := err
          bestS := s
    return bestS
  let mult := (scale * Float.ofNat (2 ^ bestShift)).round
  let multBv := BitVec.ofNat 16 mult.toUInt64.toNat
  let shiftBv := BitVec.ofNat 5 bestShift
  (multBv, shiftBv)

end Sparkle.Examples.YOLOv8.Tests.WeightROM
