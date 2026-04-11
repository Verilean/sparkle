/-
  FFN Pipeline Golden Value Test.

  Verifies each stage of the FFN pipeline (combinational version)
  produces expected results, and that the full pipeline matches
  the bitNetPeripheral golden values from the integration test.

  Run: lake exe ffn-golden-test
-/

import Sparkle
import IP.BitNet.SignalHelpers
import IP.BitNet.BitLinear.Scale
import IP.BitNet.Layers.FFN
import IP.BitNet.Layers.ReLUSq
import IP.BitNet.Layers.ElemMul
import IP.BitNet.Layers.ResidualAdd
import IP.RV32.BitNetPeripheral

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.BitNet.SignalHelpers
open Sparkle.IP.BitNet.BitLinear
open Sparkle.IP.BitNet.Layers
open Sparkle.IP.RV32.BitNetPeripheral

abbrev S32 := Signal defaultDomain (BitVec 32)
def s32 (v : BitVec 32) : S32 := Signal.pure v
def ev (sig : S32) : BitVec 32 := sig.atTime 0

def main : IO UInt32 := do
  IO.println "=== FFN Pipeline Golden Value Test ==="
  IO.println ""

  let mut allPass := true

  -- Test inputs (same as bitnet-soc-test)
  let testInputs : List (BitVec 32 × BitVec 32) := [
    (0x00010000#32, 0x00410000#32),
    (0x00020000#32, 0x02020000#32),
    (0x00030000#32, 0x06C30000#32),
    (0x00040000#32, 0x10040000#32),
    (0x00000000#32, 0x00000000#32)
  ]

  IO.println "  Stage 1: BitLinear (all +1 weights, dim=4)"
  for (inp, _) in testInputs do
    let act := s32 inp
    let blResult := bitLinearSignal #[1,1,1,1] #[act, act, act, act]
    let r := ev blResult
    -- dim=4, all +1 → sum = 4 × input
    let expected := BitVec.ofNat 32 (inp.toNat * 4 % (2^32))
    let ok := r == expected
    if !ok then allPass := false
    IO.println s!"    in=0x{Nat.toDigits 16 inp.toNat |>.asString} bl=0x{Nat.toDigits 16 r.toNat |>.asString} exp=0x{Nat.toDigits 16 expected.toNat |>.asString} {if ok then "✅" else "❌"}"

  IO.println ""
  IO.println "  Stage 2: Scale (unit scale 0x01000000)"
  let testAcc := s32 0x00040000#32  -- 4 × 0x10000 = 0x40000
  let acc48 : Signal defaultDomain (BitVec (16 + 32)) := signExtendSignal 16 testAcc
  let scaled := scaleMultiplySignal acc48 (s32 (BitVec.ofInt 32 0x01000000))
  let scaledVal := ev scaled
  IO.println s!"    acc=0x40000, scale=1.0 → scaled=0x{Nat.toDigits 16 scaledVal.toNat |>.asString}"

  IO.println ""
  IO.println "  Stage 3: ReLU²"
  let reluPos := ev (reluSqSignal (s32 0x00020000#32))
  let reluNeg := ev (reluSqSignal (s32 0x80020000#32))
  let reluZero := ev (reluSqSignal (s32 0x00000000#32))
  IO.println s!"    relu²(+0x20000) = 0x{Nat.toDigits 16 reluPos.toNat |>.asString}"
  IO.println s!"    relu²(-x)       = 0x{Nat.toDigits 16 reluNeg.toNat |>.asString} (should be 0)"
  IO.println s!"    relu²(0)        = 0x{Nat.toDigits 16 reluZero.toNat |>.asString} (should be 0)"
  if reluNeg != 0#32 then allPass := false
  if reluZero != 0#32 then allPass := false

  IO.println ""
  IO.println "  Stage 4: ElemMul"
  let elemResult := ev (elemMulSignal (s32 0x00020000#32) (s32 0x00030000#32))
  IO.println s!"    0x20000 × 0x30000 >> 16 = 0x{Nat.toDigits 16 elemResult.toNat |>.asString}"

  IO.println ""
  IO.println "  Stage 5: ResidualAdd"
  let residResult := ev (residualAddSignal (s32 0x10000#32) (s32 0x20000#32))
  let residOk := residResult == 0x30000#32
  if !residOk then allPass := false
  IO.println s!"    0x10000 + 0x20000 = 0x{Nat.toDigits 16 residResult.toNat |>.asString} (expected 0x30000) {if residOk then "✅" else "❌"}"

  IO.println ""
  IO.println "  Full FFN Pipeline: bitNetPeripheral golden values"
  for (inp, expected) in testInputs do
    let result := ev (bitNetPeripheral (s32 inp))
    let ok := result == expected
    if !ok then allPass := false
    IO.println s!"    in=0x{Nat.toDigits 16 inp.toNat |>.asString} out=0x{Nat.toDigits 16 result.toNat |>.asString} exp=0x{Nat.toDigits 16 expected.toNat |>.asString} {if ok then "✅" else "❌"}"

  IO.println ""
  if allPass then
    IO.println "=== ALL FFN GOLDEN TESTS PASS ==="
    return 0
  else
    IO.println "=== SOME FFN GOLDEN TESTS FAILED ==="
    return 1
