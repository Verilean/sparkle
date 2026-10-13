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

/-! ### The legacy fallback, on a real source

A one-output call of a SEQUENTIAL child: the one-output closing never took
it — before the checks of `97952d0`/`ffe0259` as after (its instance statement
refuses a child with a clock or reset, `instStmt`) — so the machine route
returns `none` and the real entry succeeds on the legacy route. The legacy
route's output is not covered by the certified theorems. -/

open Sparkle.Core.Domain Sparkle.Core.Signal in
/-- A sequential child with one plain output. -/
@[hardware_module] def ctr1 {dom : DomainConfig} (en : Signal dom Bool) : Signal dom (BitVec 8) :=
  circuit do
    let c ← Signal.reg 0#8
    let cs := (c : Signal dom (BitVec 8))
    c <~ Signal.mux en (cs + (Signal.pure 1#8 : Signal dom (BitVec 8))) cs
    return cs

open Sparkle.Core.Domain Sparkle.Core.Signal in
def useCtr1 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let k := ctr1 en
    r <~ rs + k
    return rs

run_cmd Lean.Elab.Command.liftTermElabM do
  let n := ``useCtr1
  let r ← Tools.ShippingMachineCommand.readMachine n
  unless r.shape.instFields.isEmpty && r.shape.insts.length == 1 do throwError "not a one-output call"
  let translate : TranslateFn := fun e h t nm => translateExprToWire e h t nm
  if (← synthesizeMachineCertified translate (fun _ => pure ()) n r.shape).isSome then
    throwError "the machine route took a one-output sequential call"
  let (b, _) ← synthesizeCombinational n
  unless b.name == Sparkle.IR.ModuleName.ofDecl n do throwError "the entry did not produce the module"
  Lean.logInfo m!"LEGACY FALLBACK: useCtr1 (one-output call of a sequential child) — machine route none, entry succeeds ({b.body.length} statements)"

/-! ### The legacy route's children after the single-writer change

A legacy-route parent's child is now what `synthesizeChild` returns — the
real entry with the full translator — where it used to be the block's own
miss path on the fuel-truncated translator. The two differ only when the
remaining fuel would run out inside the child (the old path then failed), so
equal outputs on these cases are evidence for these cases, not an equivalence
of the two routes. Checked here on the legacy route: a fallback parent, the
same child called twice, and a nested legacy chain — the parent's design holds
ONE module per child, equal to a fresh top-level run of the entry on it, and
so does the cache. -/

open Sparkle.Core.Domain Sparkle.Core.Signal in
/-- The same sequential one-output child twice (legacy route). -/
def useCtr1Twice (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let k := ctr1 en
    let j := ctr1 (Signal.map (fun b => !b) en)
    r <~ rs + k + j
    return rs

open Sparkle.Core.Domain Sparkle.Core.Signal in
/-- A legacy-route child that itself calls `ctr1` on the legacy route. -/
@[hardware_module] def mid1 {dom : DomainConfig} (en : Signal dom Bool) : Signal dom (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let k := ctr1 en
    r <~ rs + k
    return rs

open Sparkle.Core.Domain Sparkle.Core.Signal in
def useMid1 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let k := mid1 en
    r <~ rs + k
    return rs

run_cmd Lean.Elab.Command.liftTermElabM do
  let dg (m : Sparkle.IR.AST.Module) : String := toString (hash (repr m).pretty)
  let translate : TranslateFn := fun e h t nm => translateExprToWire e h t nm
  for (f, kids) in [(``useCtr1, [``ctr1]), (``useCtr1Twice, [``ctr1]), (``useMid1, [``mid1, ``ctr1])] do
    -- on the legacy route: the machine route refuses the parent
    let legacy ← try
        let r ← Tools.ShippingMachineCommand.readMachine f
        pure (← synthesizeMachineCertified translate (fun _ => pure ()) f r.shape).isNone
      catch _ => pure true
    unless legacy do throwError "{f}: not on the legacy route"
    let (_, D) ← synthesizeCombinational f
    let cache ← sparkleChildCache.get
    for c in kids do
      -- one module of the child in the parent's design
      let ms := D.modules.filter (·.name == Sparkle.IR.ModuleName.ofDecl c)
      let [dm] := ms | throwError "{f}: {ms.length} modules named {c}"
      -- the cache holds it
      let some (cm, _) := cache.get? c | throwError "{f}: {c} is not cached"
      -- and both equal a fresh top-level run of the entry on the child
      let (fm, _) ← synthesizeCombinational c
      unless dg cm == dg fm do throwError "{f}: the cached {c} differs from a fresh run"
      unless dg dm == dg fm do throwError "{f}: the design's {c} differs from a fresh run"
    Lean.logInfo m!"LEGACY CHILDREN: {f} — {kids} one module each, cached, equal to a fresh run"

end Sparkle.Tests.Compiler.ShippingCloseInstsCheckTest
