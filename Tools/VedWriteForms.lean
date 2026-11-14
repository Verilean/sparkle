import Lean
import Sparkle.Compiler.Elab
import Tools.VedStrictAudit
import Tools.VedU1PackedEntry
import Tools.VedU1HierEntry
import Tools.VedU2HierRegEntry

/-!
# `#writeDesign` argument forms for the packed / hierarchical entries

`Tools/VedInvocation.lean` gives `#ved_u1_write decl "x.sv" "x_cppsim.h" [wires]` for the single
module entry.  The H.264 / SoC synthesis files return a packed `Signal d (A × B × …)` (`bundleAll!`)
and contain submodules, which `#ved_u1` refuses at `[multi-output]`; the entries for those are
`#ved_u1_packed`, `#ved_u1_hier` and `#ved_u2_hier`.  Each form here accepts the same argument list as
`#writeDesign` (the paths and the wires constant are not used: nothing is written, the wires
constant is not evaluated) and runs the BODY of the corresponding entry command on the same
declaration, so it is the same declaration, the same module returned by `synthesizeCombinational`
(`synthesizeHierarchical` returns that very module), the same stored statement and the same refusals.
-/

namespace Tools.VedWriteForms

open Lean Elab Command Term Meta

def runPacked (id : Syntax) : CommandElabM Unit := do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverload id
  Command.liftTermElabM do
    let (m, thm, nDom) ← Tools.VedU1PackedEntry.vedU1PackedS decl
    let r ← Tools.VedStrictAudit.strictAudit thm
    let spec := if nDom > 0 then " (specialised at defaultDomain)" else ""
    logInfo m!"VED U1 PACKED OK {thm}{spec}: {Tools.VedStrictAudit.showNames r.axioms}\n{repr m}"

def runU1Hier (id : Syntax) : CommandElabM Unit := do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverload id
  Command.liftTermElabM do
    let (m, d, thm, nDom, st) ← Tools.VedU1HierEntry.vedU1HierEntry decl
    let r ← Tools.VedStrictAudit.strictAudit thm
    let spec := if nDom > 0 then " (specialised at defaultDomain)" else ""
    logInfo m!"VED U1 HIER OK {thm}{spec}: {Tools.VedStrictAudit.showNames r.axioms}\nchildren: {d.modules.map (·.name)}\nsynthesis {st.synthMs} ms, children {st.childMs} ms, parent proof {st.proofMs} ms, peak {st.peakKb} kB\n{repr m}"

def runU2Hier (id : Syntax) : CommandElabM Unit := do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverload id
  let (m, d, thm, nDom, st) ← Tools.VedU2HierRegEntry.vedU2HierEntryR decl
  Command.liftTermElabM do
    let r ← Tools.VedStrictAudit.strictAudit thm
    let spec := if nDom > 0 then " (specialised at defaultDomain)" else ""
    logInfo m!"VED U2 HIER OK {thm}{spec}: {Tools.VedStrictAudit.showNames r.axioms}\nchildren: {d.modules.map (·.name)}\nsynthesis {st.synthMs} ms, children {st.childMs} ms, parent proof {st.proofMs} ms, peak {st.peakKb} kB\n{repr m}"

elab "#ved_u1_packed_write " id:ident svPath:str cppPath:str : command => do
  let _ := svPath; let _ := cppPath
  runPacked id

elab "#ved_u1_packed_write " id:ident svPath:str cppPath:str wiresId:ident : command => do
  let _ := svPath; let _ := cppPath; let _ := wiresId
  runPacked id

elab "#ved_u1_hier_write " id:ident svPath:str cppPath:str : command => do
  let _ := svPath; let _ := cppPath
  runU1Hier id

elab "#ved_u1_hier_write " id:ident svPath:str cppPath:str wiresId:ident : command => do
  let _ := svPath; let _ := cppPath; let _ := wiresId
  runU1Hier id

elab "#ved_u2_hier_write " id:ident svPath:str cppPath:str : command => do
  let _ := svPath; let _ := cppPath
  runU2Hier id

elab "#ved_u2_hier_write " id:ident svPath:str cppPath:str wiresId:ident : command => do
  let _ := svPath; let _ := cppPath; let _ := wiresId
  runU2Hier id

end Tools.VedWriteForms
