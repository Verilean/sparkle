import Sparkle

/-! # Probe: a `@[hardware_module]` declaration under a memory placeholder name

PROBE (never-failing; prints). Reviewer 2026-10-18 item 3 (`MemR1` audit).

The machine reader names a memory call `MachMemory.memChildName combo aw dw`
(`SparkleMem.{combo|sync}.<aw>.<dw>`, two NUMERIC name components), and
`closeInstsGM` (Elab.lean ~5213) builds the child of every entry whose name
decodes with `MachMemory.memChild?` as the memory module, WITHOUT looking at the
environment. Source syntax cannot write a numeric name component, but
metaprogramming can (`addDecl`). This probe adds such a declaration (a copy of
`fakeSrc`, which is NOT a memory) tagged `@[hardware_module]`, builds a parent
that calls it next to a real memory (so the parent closes through
`closeInstsGM`), and prints which child modules the compiled design holds — for
the parent calling `fakeSrc` under its own name (control) and under the
placeholder name. -/
namespace Sparkle.Tests.Compiler.MemNameCollisionProbe
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- The memory's interface, but NOT a memory: the output is `wd + 1`. -/
@[hardware_module]
def fakeSrc (_wa : Signal defaultDomain (BitVec 4)) (wd : Signal defaultDomain (BitVec 8))
    (_we : Signal defaultDomain Bool) (_ra : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8) :=
  wd + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))

/-- Control parent: a combinational-read memory (aw 4, dw 8) and a call of `fakeSrc`. -/
def ctlParent (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let r1 := Signal.memoryComboRead wa wd we addr
    let r2 := fakeSrc wa wd we addr
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 (r1 ^^^ r2))
  Signal.snd st

/-- The synchronous placeholder name for aw 4, dw 8 (the memory above is the
COMBINATIONAL one, so the two calls are different entries). -/
def collName : Name := Sparkle.Compiler.MachMemory.memChildName false 4 8

-- `fakeSrc` copied under the placeholder name and tagged; `collParent` =
-- `ctlParent` with every `fakeSrc` replaced by it.
run_cmd liftTermElabM do
  let src ← getConstInfo ``fakeSrc
  addDecl (Declaration.defnDecl
    (mkDefinitionValEx collName [] src.type src.value! .abbrev .safe [collName]))
  Sparkle.Compiler.hardwareModuleAttr.setTag collName
  let par ← getConstInfo ``ctlParent
  let v := par.value!.replace fun e =>
    if e.isConstOf ``fakeSrc then some (.const collName []) else none
  let pn := `Sparkle.Tests.Compiler.MemNameCollisionProbe.collParent
  addDecl (Declaration.defnDecl (mkDefinitionValEx pn [] par.type v .abbrev .safe [pn]))

run_cmd liftTermElabM do
  let env ← getEnv
  logInfo m!"inst sig of {collName}: {repr (Sparkle.Compiler.Elab.instSignature? env collName)}"
  logInfo m!"memChild? {collName} isSome: {(Sparkle.Compiler.MachMemory.memChild? collName).isSome}"
  for n in [``ctlParent, `Sparkle.Tests.Compiler.MemNameCollisionProbe.collParent] do
    let ci ← getConstInfo n
    let senv := Sparkle.Compiler.Elab.structEnv env
    match Sparkle.Compiler.Elab.machineShape? false [] ci senv with
    | some sp =>
      logInfo m!"{n}: machine shape, insts {sp.insts.map (fun i => (i.1, i.2.1))}, instFields {sp.instFields}"
    | none => logInfo m!"{n}: NO machine shape (original constant)"
    try
      let (_, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore n [] false
      logInfo m!"{n}: design modules {D.modules.map (·.name)}"
      for m in D.modules do
        if m.name != D.topModule then
          logInfo m!"  child {m.name}: inputs {m.inputs.map (·.name)} outputs {m.outputs.map (·.name)} memParams {repr (Sparkle.Compiler.MachMemory.memParams? m)}"
    catch e => logInfo m!"{n}: synthesis threw: {e.toMessageData}"

/-- No memory: a parent whose only call is `fakeSrc` (closes through `closeInstsM`). -/
def ctlPlain (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let r2 := fakeSrc wa wd we addr
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 r2)
  Signal.snd st

/-- A placeholder name whose declaration's result kind is NOT `.bits dw`
(`dw = 16`, result `BitVec 8`): `MemR1 (structEnv env)` is false here. -/
def collName16 : Name := Sparkle.Compiler.MachMemory.memChildName false 4 16

run_cmd liftTermElabM do
  let src ← getConstInfo ``fakeSrc
  addDecl (Declaration.defnDecl
    (mkDefinitionValEx collName16 [] src.type src.value! .abbrev .safe [collName16]))
  Sparkle.Compiler.hardwareModuleAttr.setTag collName16
  let par ← getConstInfo ``ctlPlain
  let v := par.value!.replace fun e =>
    if e.isConstOf ``fakeSrc then some (.const collName []) else none
  let pn := `Sparkle.Tests.Compiler.MemNameCollisionProbe.collPlain
  addDecl (Declaration.defnDecl (mkDefinitionValEx pn [] par.type v .abbrev .safe [pn]))

run_cmd liftTermElabM do
  let env ← getEnv
  logInfo m!"MemR1 instance: inst sig of {collName16}: {repr (Sparkle.Compiler.Elab.instSignature? env collName16)} (MemR1 needs result bits 16)"
  for n in [``ctlParent, `Sparkle.Tests.Compiler.MemNameCollisionProbe.collParent, ``ctlPlain,
      `Sparkle.Tests.Compiler.MemNameCollisionProbe.collPlain] do
    for cfe in [true, false] do
      try
        let (top, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCoreWith (fun env e h t n => Sparkle.Compiler.Elab.translateExprToWire env e h t n) n [] false (certifiedFrontEnd := cfe)
        logInfo m!"{n} certifiedFrontEnd={cfe}: top {top.name} insts {top.body.filterMap (fun s => match s with | .inst mn _ _ => some mn | _ => none)} modules {D.modules.map (·.name)}"
        for m in D.modules do
          if m.name != D.topModule then
            logInfo m!"  child {m.name}: memParams {repr (Sparkle.Compiler.MachMemory.memParams? m)}"
      catch e => logInfo m!"{n} certifiedFrontEnd={cfe}: threw: {e.toMessageData}"

end Sparkle.Tests.Compiler.MemNameCollisionProbe
