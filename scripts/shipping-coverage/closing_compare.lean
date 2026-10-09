-- Old (12e84834) vs current closing acceptance, on the machine declarations
-- with calls of the imported test modules. Run: lake env lean scripts/shipping-coverage/closing_compare.lean
-- (writes closing_compare.out next to the working directory).
import Tests.Compiler.ShippingChildBoundaryTest
namespace Sparkle.IR.Machine
open Sparkle.IR.AST
def closeInstsOld (nIn kI n : Nat) (portNames : List String) (insts : List (List Nat))
    (children : List (Module × Design)) (md : Module × Design) : Option (Module × Design) := do
  let (m, d) := md
  let d' := designWith children d
  let stmts ← (List.range insts.length).mapM fun k => do
    let args ← insts[k]?
    let child ← children[k]?
    -- the module the name resolves to in the shipped design
    let mc ← moduleByName d'.modules child.1.name
    instStmt nIn kI n portNames k args mc m
  let outWs ← (List.range insts.length).mapM fun k => portNames[nIn + k]?
  let m' : Module := { m with
    inputs := m.inputs.filter fun p => !outWs.contains p.name
    body := m.body ++ stmts }
  let body ← topoBody m'.body
  if stmts.all isInst && decide portNames.Nodup && Sparkle.IR.Reorder.woCheck [] m'.body &&
      Sparkle.IR.Reorder.woCheck [] body && Sparkle.IR.Reorder.isPermOf m'.body body &&
      decide (seqOf m'.body = seqOf body) &&
      decide (Sparkle.IR.Reorder.nextKeys m'.body).Nodup &&
      decide (m'.body.filterMap Sparkle.IR.Reorder.stmtMemName).Nodup &&
      linkedOk (moduleByName d'.modules) body then
    some ({ m' with body := body }, d')
  else none

def closeInstsGOld (nIn kI n : Nat) (portNames : List String) (insts : List (List Nat))
    (fields : List String) (children : List (Module × Design)) (md : Module × Design) :
    Option (Module × Design) := do
  let (m0, d) := md
  let d' := designWith children d
  let m := withClockFor children m0
  let stmts ← stmtsG nIn kI n portNames insts fields children m d'
  let outWs ← (List.range insts.length).mapM fun k => portNames[nIn + k]?
  let m' : Module := { m with
    inputs := m.inputs.filter fun p => !outWs.contains p.name
    body := m.body ++ stmts }
  let body ← topoBody m'.body
  if stmts.all isInst && decide portNames.Nodup && Sparkle.IR.Reorder.woCheck [] m'.body &&
      Sparkle.IR.Reorder.woCheck [] body && Sparkle.IR.Reorder.isPermOf m'.body body &&
      decide (seqOf m'.body = seqOf body) &&
      decide (Sparkle.IR.Reorder.nextKeys m'.body).Nodup &&
      decide (m'.body.filterMap Sparkle.IR.Reorder.stmtMemName).Nodup &&
      linkedOk (moduleByName d'.modules) body &&
      -- each instance its own name, none feeding itself (the stateful
      -- linked run's conditions; always so for the statements above)
      decide (body.filterMap instNameOf).Nodup && noSelfFeed (moduleByName d'.modules) body &&
      -- a memory child's name finds that memory module
      children.all (fun c => Sparkle.Compiler.MachMemory.memSelf (moduleByName d'.modules) c.1) &&
      -- every child module, and every module of a child's design, is found by
      -- its name in the merged design as itself (the designs agree)
      children.all (fun c => decide (moduleByName d'.modules c.1.name = some c.1) &&
        c.2.modules.all (fun m => decide (moduleByName d'.modules m.name = some m))) then
    some ({ m' with body := body }, d')
  else none
end Sparkle.IR.Machine

open Lean Meta Sparkle.Compiler.Elab in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut decls : Array Name := #[]
  for (n, _) in env.constants.toList do
    if n.getString! == "machineData" && (`Sparkle.Tests).isPrefixOf n then decls := decls.push n.getPrefix
  let mut lines : Array String := #[]
  for n in decls do
    let some r ← (try some <$> Tools.ShippingMachineCommand.readMachine n catch _ => pure none) | continue
    let shape := r.shape
    if shape.insts.isEmpty then continue
    let translate : TranslateFn := fun e h t nm => translateExprToWire e h t nm
    let some (t, d₀) ← (try some <$> synthesizeMixedCertified translate (fun _ => pure ()) n shape.binders shape.body
        catch _ => pure none) | lines := lines.push s!"{n}: harness failed"; continue
    let some t' := Sparkle.IR.Machine.closeLets shape.layout.lets t | lines := lines.push s!"{n}: closeLets none"; continue
    let m₀ := Sparkle.IR.Machine.closeMachine shape.layout t'
    let children ← shape.insts.mapM fun (c, _, _) => do
      match Sparkle.Compiler.MachMemory.memChild? c with
      | some md => pure md
      | none => synthesizeCombinational c
    let kI := shape.insts.length
    let nn := shape.layout.slots.length
    let nDecl := shape.binders.length - kI - nn - shape.layout.lets
    let nIn := ((shape.binders.take nDecl).filter (fun b => b.2 != .domain)).length
    let pn := t.inputs.map (·.name)
    let args := shape.insts.map (·.2.1)
    let (old, new) := if shape.instFields.isEmpty then
        ((Sparkle.IR.Machine.closeInstsOld nIn kI nn pn args children (m₀, d₀)).isSome,
         (Sparkle.IR.Machine.closeInsts nIn kI nn pn args children (m₀, d₀)).isSome)
      else
        ((Sparkle.IR.Machine.closeInstsGOld nIn kI nn pn args shape.instFields children (m₀, d₀)).isSome,
         (Sparkle.IR.Machine.closeInstsG nIn kI nn pn args shape.instFields children (m₀, d₀)).isSome)
    lines := lines.push s!"{n}: route {if shape.instFields.isEmpty then "one-output" else "general"} old {old} new {new}"
  IO.FS.writeFile "closing_compare.out" (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"done {lines.size}"
