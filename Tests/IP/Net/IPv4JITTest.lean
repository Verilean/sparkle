/-
  JIT-backed sim test for IP.Net.IPv4, also doubles as a
  regression guard for Issue #75 (> 64-bit packed JIT
  outputs).
-/

import IP.Net.IPv4
import Sparkle.Core.JIT
import Sparkle.Core.SimTyped

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.Net.IPv4

namespace Sparkle.Tests.IP.Net.IPv4JITTest

abbrev D := defaultDomain

private def srcIp : BitVec 32 := 0x0A00000A
private def dstIp : BitVec 32 := 0x0A000014
private def proto : BitVec 8  := 0x01
private def totLen : BitVec 16 := 84

@[hardware_module] def rxSrcIpSig
    (b : Signal D (BitVec 8)) (v : Signal D Bool) (sop : Signal D Bool) :
    Signal D (BitVec 32) :=
  (ipv4RxParser b v sop).srcIp

/-- Wide output: replicate srcIp three times via Signal.append
    chain.  Exercises Issue #75's > 64-bit read path. -/
@[hardware_module] def rxWideSig
    (b : Signal D (BitVec 8)) (v : Signal D Bool) (sop : Signal D Bool) :
    Signal D (BitVec 96) :=
  let s := rxSrcIpSig b v sop
  let s64 : Signal D (BitVec 64) := (· ++ ·) <$> s <*> s
  (· ++ ·) <$> s <*> s64

#sim rxWideSig

private def expectedHeader : List (BitVec 8) :=
  [ 0x45#8, 0x00#8, 0#8, 84#8, 0#8, 0#8, 0x40#8, 0#8, 0x40#8, 0x01#8
  , 0#8, 0#8
  , 0x0A#8, 0#8, 0#8, 0x0A#8
  , 0x0A#8, 0#8, 0#8, 0x14#8 ]

def main : IO Unit := do
  let rxSim ← rxWideSig.Sim.load
  let expArr := expectedHeader.toArray
  let mut lastOut : Nat := 0
  for t in [:25] do
    let b : BitVec 8 :=
      if t < 20 then expArr.getD t 0#8 else 0#8
    let v : BitVec 1 := if t < 20 then 1#1 else 0#1
    let sop : BitVec 1 := if t = 0 then 1#1 else 0#1
    let inp : rxWideSig.Sim.SimInput :=
      { _gen_b := b, _gen_v := v, _gen_sop := sop }
    Sparkle.Core.Sim.Sim.step rxSim inp
    let out ← Sparkle.Core.Sim.Sim.read rxSim
    if t = 22 then lastOut := out.out.toNat
  Sparkle.Core.Sim.Sim.destroy rxSim

  IO.println s!"  raw out = 0x{Nat.toDigits 16 lastOut |> String.ofList}"
  let part0 : BitVec 32 := BitVec.ofNat 32 (lastOut &&& 0xFFFFFFFF)
  let part1 : BitVec 32 := BitVec.ofNat 32 ((lastOut >>> 32) &&& 0xFFFFFFFF)
  let part2 : BitVec 32 := BitVec.ofNat 32 ((lastOut >>> 64) &&& 0xFFFFFFFF)
  IO.println s!"  part0 = 0x{Nat.toDigits 16 part0.toNat |> String.ofList}"
  IO.println s!"  part1 = 0x{Nat.toDigits 16 part1.toNat |> String.ofList}"
  IO.println s!"  part2 = 0x{Nat.toDigits 16 part2.toNat |> String.ofList}"

  if part0 = srcIp ∧ part1 = srcIp ∧ part2 = srcIp then
    IO.println "ALL PASS"
  else
    IO.println "FAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.IPv4JITTest
