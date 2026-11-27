/-
  Regression test: a field of a multi-output `@[hardware_module]` call used
  directly as a register input (`dR <~ c.done`) reached the raw `Expr.proj`
  case of the elaborator, whose packed-product fallback sliced the
  sub-module's FIRST output port, so `dR` latched `val[0:0]` instead of `done`.
-/
import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.Tests.Compiler.ProjRegisterInputTest

open Sparkle.Core.Domain
open Sparkle.Core.Signal

structure TwoOut (dom : DomainConfig) where
  val  : Signal dom (BitVec 8)
  done : Signal dom Bool

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (TwoOut dom) dom := ⟨⟩

/-- Counter whose `done` is high when the count is 3. -/
@[hardware_module]
def counter {dom : DomainConfig} (start : Signal dom Bool) : TwoOut dom := circuit do
  let cR ← Signal.reg (0#8)
  let c := (cR : Signal dom (BitVec 8))
  cR <~ Signal.mux start (Signal.pure 0#8) (c + (Signal.pure 1#8 : Signal dom (BitVec 8)))
  return ({ val := c, done := (c === 3#8) } : TwoOut dom)

/-- Registers the counter's second field. -/
@[hardware_module]
def doneReg {dom : DomainConfig} (start : Signal dom Bool) : Signal dom Bool := circuit do
  let dR ← Signal.reg false
  let c := counter start
  dR <~ c.done
  return (dR : Signal dom Bool)

open Lean Elab Command in
/-- Synthesize `id` and assert one of its registers takes the wire on port `port`
    of its sub-module instance.  Fails elaboration (and hence the build) otherwise. -/
elab "#assertRegReadsPort" id:ident port:str : command => do
  let declName ← liftCoreM (Lean.resolveGlobalConstNoOverload id)
  liftTermElabM do
    let (module, _) ← Sparkle.Compiler.Elab.synthesizeCombinational declName
    let portWires := module.body.filterMap fun
      | .inst _ _ conns => conns.lookup port.getString
      | _ => none
    let regInputs := module.body.filterMap fun
      | .register _ _ _ input _ => some input
      | _ => none
    unless regInputs.any (portWires.contains ·) do
      throwError "expected a register of {declName} to read port '{port.getString}' \
        ({portWires}), register inputs are {regInputs}"

#assertRegReadsPort doneReg "done"

/-- Field 0 taken straight off the call (no `let`), registered. -/
@[hardware_module]
def valDirectReg {dom : DomainConfig} (start : Signal dom Bool) : Signal dom (BitVec 8) := circuit do
  let vR ← Signal.reg (0#8)
  vR <~ (counter start).val
  return (vR : Signal dom (BitVec 8))

/-- Field 1 taken straight off the call (no `let`), registered. -/
@[hardware_module]
def doneDirectReg {dom : DomainConfig} (start : Signal dom Bool) : Signal dom Bool := circuit do
  let dR ← Signal.reg false
  dR <~ (counter start).done
  return (dR : Signal dom Bool)

#assertRegReadsPort valDirectReg "val"
#assertRegReadsPort doneDirectReg "done"

def main : IO Unit := do
  IO.println "ProjRegisterInputTest: build-only regression test."
  IO.println "  ✓ doneReg latches the counter's `done` port (was `val[0:0]`)"

end Sparkle.Tests.Compiler.ProjRegisterInputTest
