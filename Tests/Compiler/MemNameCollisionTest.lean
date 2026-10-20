import Sparkle

/-! # Regression: a `@[hardware_module]` declaration under a memory placeholder name

ASSERTING (an elaboration error when a case is wrong). Reviewer 2026-10-19,
`docs/parallel/S-memname-collision.md`, `Tests/Compiler/MemNameCollisionProbe.lean`.

A memory call is a machine call entry under the placeholder name
`MachMemory.memChildName combo aw dw`. Metaprogramming can declare a
`@[hardware_module]` under that name. Every case below compiles a parent on the
certified route and checks the instances of its top module: each memory
instance is the memory module of the memory's parameters, each call of the
colliding declaration an instance of THAT declaration's own compile (its module
name `ModuleName.ofDecl`, no memory statement, the same module as the
declaration compiled alone), and there are exactly as many instances as distinct
calls (a memory and a declaration call with the same name and argument `let`s
are two calls).

Cases (each with a control: the same parent calling the declaration under its
own name):
* `mixDiff` — combinational memory 4/8 and the declaration at the SYNCHRONOUS
  name 4/8 (general closing);
* `mixArgs` — synchronous memory 4/8 and the declaration at that name, other
  arguments;
* `mixSame` — synchronous memory 4/8 and the declaration at that name, the SAME
  arguments;
* `plain` — the declaration alone (one-output closing);
* `width` — combinational memory 4/8 and a declaration with a 4-bit result at
  that memory's own name, the same arguments. -/
namespace Sparkle.Tests.Compiler.MemNameCollisionTest
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- The memory's interface, not a memory: `wd + 1`. -/
@[hardware_module]
def fakeSrc (_wa : Signal defaultDomain (BitVec 4)) (wd : Signal defaultDomain (BitVec 8))
    (_we : Signal defaultDomain Bool) (_ra : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8) :=
  wd + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))

/-- The memory's operands, a 4-bit result: `ra + 1`. -/
@[hardware_module]
def fakeN (_wa : Signal defaultDomain (BitVec 4)) (_wd : Signal defaultDomain (BitVec 8))
    (_we : Signal defaultDomain Bool) (ra : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 4) :=
  ra + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))

def mixDiff (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let r1 := Signal.memoryComboRead wa wd we addr
    let r2 := fakeSrc wa wd we addr
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 (r1 ^^^ r2))
  Signal.snd st

def mixArgs (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let r1 := Signal.memory wa wd we addr
    let r2 := fakeSrc wa wd we wa
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 (r1 ^^^ r2))
  Signal.snd st

def mixSame (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let r1 := Signal.memory wa wd we addr
    let r2 := fakeSrc wa wd we addr
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 (r1 ^^^ r2))
  Signal.snd st

def plain (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let r2 := fakeSrc wa wd we addr
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 r2)
  Signal.snd st

def width (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let r1 := Signal.memoryComboRead wa wd we addr
    let r2 := fakeN wa wd we addr
    bundle2 (Signal.register 0#4 (addr + r2))
      (Signal.register 0#8 r1)
  Signal.snd st

/-- `src` copied under `nm`, tagged `@[hardware_module]`. -/
def copyAs (src nm : Name) : CoreM Unit := do
  let ci ← getConstInfo src
  addDecl (Declaration.defnDecl (mkDefinitionValEx nm [] ci.type ci.value! .abbrev .safe [nm]))
  Sparkle.Compiler.hardwareModuleAttr.setTag nm

/-- `par` with `src` replaced by `nm`, declared as `out`. -/
def renameIn (par src nm out : Name) : CoreM Unit := do
  let ci ← getConstInfo par
  let v := ci.value!.replace fun e => if e.isConstOf src then some (.const nm []) else none
  addDecl (Declaration.defnDecl (mkDefinitionValEx out [] ci.type v .abbrev .safe [out]))

def syncName : Name := Sparkle.Compiler.MachMemory.memChildName false 4 8
def comboName : Name := Sparkle.Compiler.MachMemory.memChildName true 4 8

def ns : Name := `Sparkle.Tests.Compiler.MemNameCollisionTest

run_cmd liftCoreM do
  copyAs ``fakeSrc syncName
  copyAs ``fakeN comboName
  renameIn ``mixDiff ``fakeSrc syncName (ns ++ `collMixDiff)
  renameIn ``mixArgs ``fakeSrc syncName (ns ++ `collMixArgs)
  renameIn ``mixSame ``fakeSrc syncName (ns ++ `collMixSame)
  renameIn ``plain ``fakeSrc syncName (ns ++ `collPlain)
  renameIn ``width ``fakeN comboName (ns ++ `collWidth)

/-- The certified route's top module and design. -/
def compileCert (n : Name) : TermElabM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) :=
  Sparkle.Compiler.Elab.synthesizeCombinationalCoreWith
    (fun env e h t n => Sparkle.Compiler.Elab.translateExprToWire env e h t n) n [] false
    (certifiedFrontEnd := true)

/-- The failures of one case: the top's instances must be exactly the memory
modules `mems` and the declarations `decls` (each the declaration compiled
alone, under its own module name, without a memory statement). -/
def checkCase (n : Name) (mems : List (Bool × Nat × Nat)) (decls : List Name) :
    TermElabM (List String) := do
  let (top, D) ← compileCert n
  let insts := top.body.filterMap fun s => match s with | .inst mn _ _ => some mn | _ => none
  let find (mn : String) := D.modules.find? (·.name == mn)
  let mut errs : List String := []
  if insts.length != mems.length + decls.length then
    errs := errs ++ [s!"{n}: {insts.length} instances {insts}, expected {mems.length + decls.length}"]
  for (cb, aw, dw) in mems do
    let mn := Sparkle.IR.ModuleName.ofMem cb aw dw
    match find mn with
    | some m =>
      if !insts.contains mn then errs := errs ++ [s!"{n}: no instance of memory {mn}"]
      if Sparkle.Compiler.MachMemory.memParams? m != some (cb, aw, dw) then
        errs := errs ++ [s!"{n}: module {mn} is not the memory {(cb, aw, dw)}"]
    | none => errs := errs ++ [s!"{n}: no memory module {mn}"]
  for c in decls do
    let mn := Sparkle.IR.ModuleName.ofDecl c
    let (alone, _) ← compileCert c
    match find mn with
    | some m =>
      if !insts.contains mn then errs := errs ++ [s!"{n}: no instance of {c} ({mn})"]
      if (Sparkle.Compiler.MachMemory.memParams? m).isSome then
        errs := errs ++ [s!"{n}: the child of {c} is a memory"]
      if m.body.length != alone.body.length || m.outputs.map (·.ty) != alone.outputs.map (·.ty) ||
          m.inputs.map (·.name) != alone.inputs.map (·.name) then
        errs := errs ++ [s!"{n}: the child {mn} is not {c} compiled alone"]
    | none => errs := errs ++ [s!"{n}: no module {mn} for {c}"]
  -- no instance of a module the case does not expect (a memory built for a call)
  for mn in insts do
    if !(mems.map (fun (cb, aw, dw) => Sparkle.IR.ModuleName.ofMem cb aw dw) ++
        decls.map Sparkle.IR.ModuleName.ofDecl).contains mn then
      errs := errs ++ [s!"{n}: unexpected instance of {mn}"]
  return errs

run_cmd liftTermElabM do
  let cases : List (Name × List (Bool × Nat × Nat) × List Name) :=
    [ (``mixDiff, [(true, 4, 8)], [``fakeSrc]),
      (ns ++ `collMixDiff, [(true, 4, 8)], [syncName]),
      (``mixArgs, [(false, 4, 8)], [``fakeSrc]),
      (ns ++ `collMixArgs, [(false, 4, 8)], [syncName]),
      (``mixSame, [(false, 4, 8)], [``fakeSrc]),
      (ns ++ `collMixSame, [(false, 4, 8)], [syncName]),
      (``plain, [], [``fakeSrc]),
      (ns ++ `collPlain, [], [syncName]),
      (``width, [(true, 4, 8)], [``fakeN]),
      (ns ++ `collWidth, [(true, 4, 8)], [comboName]) ]
  let mut errs : List String := []
  for (n, mems, decls) in cases do
    let e ← try checkCase n mems decls catch ex => pure [s!"{n}: threw {← ex.toMessageData.toString}"]
    if e.isEmpty then logInfo m!"{n}: ok"
    errs := errs ++ e
  unless errs.isEmpty do
    throwError m!"memory-name collision regression failed:\n{String.intercalate "\n" errs}"

end Sparkle.Tests.Compiler.MemNameCollisionTest
