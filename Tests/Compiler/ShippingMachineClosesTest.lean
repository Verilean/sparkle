import Tests.Compiler.ShippingReflectCtxTest
import Tools.ShippingMachineCommand
import Tools.ShippingMachineClosesGen

/-! # `MachineCloses` derived for `let` shapes without calls

`closes_of_data` on real declarations: the machine endpoint generator adds
`f.machine_closes` and the endpoints without the `MachineCloses` premise
(`_closed`) where the data give it. What is checked here is the TYPE of the
closed endpoints (no `MachineCloses`), their axioms, and — on data — which
`let` shapes the check `aliasOk` accepts. Declarations with calls are not
examples of this (their `MachineCloses` stays a premise). -/

open Lean Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingMachineClosesData

/-- A `let` that is an input, and a `let` that is that `let`. -/
def closesInputLet (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let a := x
    let b := a
    r <~ (a + b) + rs
    return rs

/-- A `let` after an operation, and a `let` that is that `let`. -/
def closesOpAlias (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let a := x + 1#8
    let b := a
    r <~ (a + b) + rs
    return rs

/-- A `let` used by a later `let` under an operation. -/
def closesChain (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let a := rs + x
    let b := a + x
    let c := b + a
    r <~ c + b
    return rs

#machine_endpoint reflSharedLet
#machine_endpoint reflAliasLet
#machine_endpoint closesInputLet
#machine_endpoint closesOpAlias
#machine_endpoint closesChain

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let std (n : Name) : MetaM Unit := do
    for a in ← Lean.collectAxioms n do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        throwError "{n} depends on {a}"
  for n in [``Tools.ShippingMachineCloses.machineCloses_of_lets,
      ``Tools.ShippingMachineCloses.transition_closes,
      ``Tools.ShippingMachineClosesData.closes_of_data,
      ``Tools.ShippingMachineClosesData.aliasOk_sound] do std n
  -- the theorem about data asks no run and no closing fact
  let t ← Lean.Meta.inferType (mkConst ``Tools.ShippingMachineClosesData.closes_of_data)
  Lean.Meta.forallTelescope t fun xs _ => do
    for x in xs do
      let ty ← Lean.Meta.inferType x
      for c in [``Tools.ShippingMachineEntry.MachineCloses, ``Tools.ShippingEntrySoundness.RunsTo,
          ``Sparkle.IR.Machine.closeLets, ``Tools.ShippingMachineEntry.MachineDefines] do
        if (ty.find? (·.isConstOf c)).isSome then throwError "closes_of_data assumes {c}"
  let mut report := #[]
  for f in [``reflSharedLet, ``reflAliasLet, ``closesInputLet, ``closesOpAlias, ``closesChain] do
    let r ← Tools.ShippingMachineCommand.readMachine f
    unless r.shape.insts.isEmpty do throwError "{f}: has calls"
    unless env.contains (f ++ `machine_closes) do throwError "{f}: no machine_closes"
    std (f ++ `machine_closes)
    let mut closed := #[]
    for s in ["machine_sound", "machine_ships", "machine_ships_wired"] do
      let orig := f ++ Name.mkSimple s
      let n := f ++ Name.mkSimple (s ++ "_closed")
      unless env.contains orig do continue
      -- the generated endpoint asks `MachineCloses`; its closed form does not
      let some ci := env.find? orig | throwError "{orig}"
      unless (ci.type.find? (·.isConstOf ``Tools.ShippingMachineEntry.MachineCloses)).isSome do
        throwError "{orig}: no MachineCloses premise to discharge"
      let some ci := env.find? n | throwError "{n}: not generated"
      if (ci.type.find? (·.isConstOf ``Tools.ShippingMachineEntry.MachineCloses)).isSome then
        throwError "{n}: MachineCloses is still in the type"
      unless (ci.type.find? (·.isConstOf ``Tools.ShippingEntrySoundness.RunsTo)).isSome &&
          (ci.type.find? (·.isConstOf ``Tools.ShippingMachineEntry.MachineDefines)).isSome do
        throwError "{n}: not about a run of the entry"
      std n
      closed := closed.push s
    unless closed.contains "machine_sound" do throwError "{f}: machine_sound_closed missing"
    report := report.push m!"{f}: lets={r.shape.layout.lets} closed={closed}"
  -- a declaration with a call: not derived here, the premise stays
  for f in [``Sparkle.Tests.Compiler.ShippingMachineInstTest.caller] do
    if env.contains (f ++ `machine_closes) || env.contains (f ++ `machine_sound_closed) then
      throwError "{f}: a shape with calls is closed"
  Lean.logInfo m!"MACHINE CLOSES FROM DATA (let shapes, no call; MachineCloses absent from the closed endpoints' types, standard axioms): {report}; with calls: premise kept"

/-! The check on `let`s that are variables, on data (two inputs at binder
positions 0, 1; `let`s from position 2):

* a field that is an input — accepted;
* a field that is the variable of an earlier `let` whose field is a variable —
  accepted (the real `closeLets` puts both aliases at the front, in order);
* a field that is the variable of a `let` with a driven field — NOT accepted:
  the real `closeLets` refuses that transition (the regression in
  `ShippingReflectCtxTest`), so `MachineCloses` is false there. The shape
  reader resolves `let b := a` to `a`'s definition (`closesOpAlias` has one
  hardware `let`), so no source tried reaches it. -/
example : aliasOk (fun _ => 0) (fun j => j) 2 [⟨8, .bitsInput 8 0⟩] = true := by decide
example : aliasOk (fun _ => 0) (fun j => j) 2 [⟨8, .bitsInput 8 0⟩, ⟨8, .bitsInput 8 2⟩] = true := by
  decide
example : aliasOk (fun _ => 0) (fun j => j) 2
    [⟨8, .binary .add (.bitsInput 8 0) (.bitsInput 8 0)⟩, ⟨8, .bitsInput 8 2⟩] = false := by decide
example : aliasOk (fun _ => 0) (fun j => j) 2
    [⟨8, .binary .add (.bitsInput 8 0) (.bitsInput 8 1)⟩,
     ⟨8, .binary .add (.bitsInput 8 2) (.bitsInput 8 0)⟩] = true := by decide
