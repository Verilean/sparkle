import Lean
import Sparkle.Compiler.Elab
import Tools.VedU1Entry
import Tools.VedStrictAudit

/-!
# `#ved_u1_write`: the `#writeDesign` argument form for the U1 entry

The H.264 / SoC synthesis files end in
`#writeDesign decl "x.sv" "x_cppsim.h" [wires]`.  That command resolves `decl`, calls
`synthesizeHierarchical decl` (= `synthesizeCombinational decl` plus `addModule` of the returned
module when the design lacks it), and writes Verilog / C++ / JIT files.  The circuit it
synthesizes is the one `#synthesizeVerilog decl` synthesizes: the returned module is the very
`(m, design)` of `synthesizeCombinational decl`.

`#ved_u1_write decl "x.sv" "x_cppsim.h" [wires]` accepts exactly that argument list (the paths
and the wires constant are not used: nothing is written, the wires constant is not evaluated)
and runs `vedU1EntryS decl`, i.e. the same entry as `#ved_u1 decl`: the same declaration, the
same returned module, the same stored statement `U1Stmt decl.ved_contract decl.ved_mod @decl`,
the same strict audit and the same refusals (multi-output, registers, …).  So a harness can
append the original command's argument text unchanged.  It is a different command form, not a
different circuit and not a different statement.
-/

namespace Tools.VedInvocation

open Lean Elab Command Term Meta Tools.VedU1Entry

/-- the common elaboration: `#ved_u1 decl`'s body -/
def runWrite (id : Syntax) : CommandElabM Unit := do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverload id
  Command.liftTermElabM do
    let (m, _, thm, nDom) ← vedU1EntryS decl
    let r ← Tools.VedStrictAudit.strictAudit thm
    let spec := if nDom > 0 then " (specialised at defaultDomain)" else ""
    logInfo m!"VED U1 OK {thm}{spec}: {Tools.VedStrictAudit.showNames r.axioms}\n{repr m}"

elab "#ved_u1_write " id:ident svPath:str cppPath:str : command => do
  let _ := svPath; let _ := cppPath
  runWrite id

elab "#ved_u1_write " id:ident svPath:str cppPath:str wiresId:ident : command => do
  let _ := svPath; let _ := cppPath; let _ := wiresId
  runWrite id

end Tools.VedInvocation
