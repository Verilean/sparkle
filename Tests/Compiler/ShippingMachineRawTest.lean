import Tests.RunCircuitHTest
import Tools.ShippingMachineCommand

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

run_cmd do
  if (← get).messages.hasErrors then throwError "machine raw-surface regression failed"

end Sparkle.Tests.Compiler.ShippingMachineRawTest
