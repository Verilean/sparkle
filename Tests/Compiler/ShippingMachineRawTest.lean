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

run_cmd do
  if (← get).messages.hasErrors then throwError "machine raw-surface regression failed"

end Sparkle.Tests.Compiler.ShippingMachineRawTest
