import Lean
import Sparkle.Compiler.Elab

/-!
# `#ved_mem_classify decl`: split a design's memory statements from its instance statements

Runs `synthesizeCombinational decl` ONCE (the pair the checking entries get) and prints, per module
of the returned artifact (top module and every child of the design), the memory statements
(address / data width, read kind, extra ports, write-port wire forms) and the instance statements.
Read-only; it checks nothing.
-/

namespace Tools.VedMemClassify

open Lean Elab Command Meta
open Sparkle.IR.AST

def exprHead : Sparkle.IR.AST.Expr → String
  | .ref n => s!"ref {n}"
  | .const v w => s!"const {v}:{w}"
  | e => (toString e).take 40 |>.toString

def showStmt : Stmt → Option String
  | .memory name aw dw _ wa wd we ra rd cr ew er =>
    some s!"MEM {name} aw={aw} dw={dw} read={if cr then "combo" else "sync"} extraW={ew.length} extraR={er.length} wa=({exprHead wa}) wd=({exprHead wd}) we=({exprHead we}) ra=({exprHead ra}) rd={rd}"
  | .inst mn inst conns => some s!"INST {mn} as {inst} ports={conns.length}"
  | _ => none

def classifyModule (m : Sparkle.IR.AST.Module) : List String :=
  let ls := m.body.filterMap showStmt
  let nMem := m.body.countP fun s => match s with | .memory .. => true | _ => false
  let nInst := m.body.countP fun s => match s with | .inst .. => true | _ => false
  let nReg := m.body.countP fun s => match s with | .register .. => true | _ => false
  s!"module {m.name}: regs={nReg} mems={nMem} insts={nInst}" :: ls.map ("  " ++ ·)

elab "#ved_mem_classify " id:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverload id
  let (m, d) ← liftTermElabM <| Sparkle.Compiler.Elab.synthesizeCombinational decl
  logInfo m!"VED MEM CLASSIFY {decl} children={d.modules.map (·.name)}"
  for l in classifyModule m do logInfo m!"VED MEM {l}"
  for c in d.modules do
    unless c.name == m.name do
      for l in classifyModule c do logInfo m!"VED MEM child {l}"

end Tools.VedMemClassify
