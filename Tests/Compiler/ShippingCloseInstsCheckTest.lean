import Tests.Compiler.ShippingMachineInstTest
import Tools.ShippingMachineCommand

/-! The one-output closing's checks (`closeInsts`, `97952d0` and after), on the
real artifacts of `caller` (one call of the gate child `pick`).

`closeInsts` resolves each child's module BY NAME in the merged design
`designWith children d₀`, which keeps the FIRST module of a name. It now
checks that every child (and every module of a child's design) resolves to
itself, that nothing instantiates the module being closed, and that the
children are combinational, local and wired (`kidsCombB`). Here, with the
real transition and the real child:

* the actual design: accepted, the instance's module IS the child's;
* a design already holding a DIFFERENT module under the child's name (the
  case that used to be wired to the wrong module): rejected;
* a design holding the SAME module under that name: accepted (identical
  content resolves to itself);
* a child that is not combinational (a register in its body): rejected.

A rejection makes `synthesizeMachineCertified` return `none`, and the entry
then takes the legacy route (`Sparkle/Compiler/Elab.lean`, the `machineResult?`
match): the success of the compile is kept, the certified route is not taken.
On the real compile of `caller` the machine route is taken (checked below). -/
namespace Sparkle.Tests.Compiler.ShippingCloseInstsCheckTest
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST

run_cmd Lean.Elab.Command.liftTermElabM do
  let n := ``Sparkle.Tests.Compiler.ShippingMachineInstTest.caller
  let r ← Tools.ShippingMachineCommand.readMachine n
  let shape := r.shape
  let translate : TranslateFn := fun e h t nm => translateExprToWire e h t nm
  let (t, d₀) ← synthesizeMixedCertified translate (fun _ => pure ()) n shape.binders shape.body
  let some t' := Sparkle.IR.Machine.closeLets shape.layout.lets t | throwError "closeLets"
  let m₀ := Sparkle.IR.Machine.closeMachine shape.layout t'
  let some (c, _, _) := shape.insts.head? | throwError "no call"
  let (child, _) ← synthesizeCombinational c
  -- the actual design
  let some (m, d) ← closeInstsM shape t m₀ d₀ | throwError "the actual closing was rejected"
  let instMods := m.body.filterMap fun st => match st with
    | .inst mn _ _ => Sparkle.IR.Machine.moduleByName d.modules mn
    | _ => none
  unless instMods == [child] do throwError "the instance's module is not the child's"
  -- a different module under the child's name, first in the design
  let impostor : Sparkle.IR.AST.Module := { child with body := [], wires := [] }
  unless impostor != child do throwError "the impostor is the child"
  if (← closeInstsM shape t m₀ { d₀ with modules := impostor :: d₀.modules }).isSome then
    throwError "a name collision with a different module was accepted"
  -- the same module under that name: accepted
  unless (← closeInstsM shape t m₀ { d₀ with modules := child :: d₀.modules }).isSome do
    throwError "an identical module under the child's name was rejected"
  -- a design module instantiating the module being closed: rejected
  let cyc : Sparkle.IR.AST.Module :=
    { child with name := "cyc_mod", body := [.inst m₀.name "u0" []] }
  if (← closeInstsM shape t m₀ { d₀ with modules := d₀.modules ++ [cyc] }).isSome then
    throwError "a design instantiating the closed module was accepted"
  -- the real entry takes the machine route on caller
  let (b, _) ← synthesizeCombinationalCore n [] false
  unless b == m do throwError "the core entry's module is not the machine route's"
  Lean.logInfo m!"CLOSEINSTS CHECKS: actual design accepted (instance = child), a different same-name module rejected, an identical one accepted, a cycle back to the closed module rejected; the core entry is the machine route's"

-- `kidsCombB` rejects a child that is not combinational
run_cmd Lean.Elab.Command.liftTermElabM do
  let n := ``Sparkle.Tests.Compiler.ShippingMachineInstTest.caller
  let (_, D) ← synthesizeCombinationalCore n [] false
  let (m, _) ← synthesizeCombinationalCore n [] false
  unless Sparkle.IR.Machine.kidsCombB D.modules m.body do throwError "kidsCombB rejects caller"
  let regChild (c : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
    { c with body := c.body ++ [.register "r" "clk" ("rst", .asynchronous) (.ref "x") 0] }
  let D' := D.modules.map fun c => if m.body.any (fun st => match st with
      | .inst mn _ _ => mn == c.name | _ => false) then regChild c else c
  if Sparkle.IR.Machine.kidsCombB D' m.body then throwError "a register child passed kidsCombB"
  Lean.logInfo m!"KIDSCOMB: a child with a register is rejected"

end Sparkle.Tests.Compiler.ShippingCloseInstsCheckTest
