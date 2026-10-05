import Tests.RunCircuitHTest
import Tools.ShippingMachineCommand
import Tests.CircuitDoTest

/-! Hand-written `runCircuitH` bodies on the machine route.

`let (r₀, …, rest) := regs` (a pair-destructuring matcher), `Circuit.read r`
and the monad's `bind`/`pure` are read as the `circuit do` forms they are
definitionally (`Sparkle.Compiler.MachRawSurface`): each declaration gets
its kernel-checked endpoint. (`threeCountForM`, a `List.forM` over the
handles, is not read.) -/
namespace Sparkle.Tests.Compiler.ShippingMachineRawTest
open Sparkle.Tests.RunCircuitHTest

#machine_endpoint counterH
#machine_endpoint twoCountH
#machine_endpoint mixedWidthH
#machine_endpoint tripleCountH
#machine_endpoint fourCountH

/-! Negation is `0 - x` by the definitions of `BitVec.neg`/`BitVec.sub`
(`machNorm`); a pair of Signals is two ports `out_0`, `out_1`. -/
open Sparkle.Core.Domain Sparkle.Core.Signal in
def negSig (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := -a
open Sparkle.Core.Domain Sparkle.Core.Signal in
def negLift (a : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) := (- ·) <$> a

#machine_endpoint negSig
#machine_endpoint negLift
#machine_endpoint Sparkle.Tests.CircuitDoTest.pairCounterCdo

/-! A projection of a bundle is its component (`MachRawSurface.bundleIota`,
definitional by structure eta): the half-adder chains of
Tests/TupleProjectionTest.lean and Tests/TestUnbundle2.lean, and a
`bundle3`. -/
section Bundles
open Sparkle.Core.Domain Sparkle.Core.Signal
def halfAdder {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8 × BitVec 8) :=
  let sum := a ^^^ b
  let carry := a &&& b
  bundle2 sum carry
def addThree {dom : DomainConfig} (a b c : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  let ab := halfAdder a b
  let abc := halfAdder ab.fst c
  abc.fst
def useHalf {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  let result := halfAdder a b
  result.fst ||| result.snd
def triBundle {dom : DomainConfig} (a b c : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  let t := bundle3 (a + b) (b ^^^ c) c
  t.proj3_1 - t.proj3_2 + t.proj3_3
end Bundles

#machine_endpoint addThree
#machine_endpoint useHalf
#machine_endpoint triBundle

/-! A tuple-typed input is ONE packed port, the first component in the high
bits (`MachTupleIn`, the legacy interface): the theorem is about the port
carrying the packed tuple. -/
section TupleInputs
open Sparkle.Core.Domain Sparkle.Core.Signal
def tupFst {dom : DomainConfig} (ab : Signal dom (BitVec 8 × BitVec 8)) : Signal dom (BitVec 8) :=
  ab.fst
def tupMapFst {dom : DomainConfig} (ab : Signal dom (BitVec 16 × BitVec 16)) :
    Signal dom (BitVec 16) :=
  Signal.map Prod.fst ab
def tupSum {dom : DomainConfig} (input : Signal dom (BitVec 8 × BitVec 8 × BitVec 8)) :
    Signal dom (BitVec 8) :=
  input.proj3_1 + input.proj3_2 + input.proj3_3
def tupReg (ab : Signal defaultDomain (BitVec 4 × BitVec 12)) : Signal defaultDomain (BitVec 12) :=
  circuit do
    let r ← Signal.reg 0#12
    let rs := (r : Signal defaultDomain (BitVec 12))
    r <~ rs + ab.snd
    return rs
end TupleInputs

#machine_endpoint tupFst
#machine_endpoint tupMapFst
#machine_endpoint tupSum
#machine_endpoint tupReg

run_cmd do
  if (← get).messages.hasErrors then throwError "machine raw-surface regression failed"

end Sparkle.Tests.Compiler.ShippingMachineRawTest
