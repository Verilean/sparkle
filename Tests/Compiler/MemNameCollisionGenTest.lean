import Tests.Compiler.MemNameCollisionCertTest
import Tests.Compiler.NoPortsTest
import Tools.ShippingMachineSeqCommandR
import Tools.ShippingNoPortsMemSeqCommand

/-! # `#machine_no_ports_memseq` on the two COLLISION parents (round par/o-kidt2)

`collSameR` / `collArgsR` (`Tests/Compiler/MemNameCollisionCertTest.lean`): a synchronous 4/8
memory (origin `.mem false 4 8`) and a call of a leaf register machine declared under the memory's
placeholder name `SparkleMem.sync.4.8` (origin `.ord`), on the same / on other argument `let`s.
Before this round the generator REFUSED them ("an entry whose name does not say what its origin
builds … TagsAgree is false"). Its TAG MODE (`Scope.tagMode`, taken exactly when some entry's name
does not say what its origin builds) keys the tables by `keyAt` (callee, memory key of the ORIGIN)
and uses the origin-based chain (`KidFactsT`, `kidsM_*T`, `machineClosesAt_of_kidsDMT`): no
`TagsAgree`. Every other shape takes the previous name-keyed path, unchanged.

Expected (asserted below): both parents GENERATED; the closed endpoints
`f.machine_design_noPortsR0_closed` on standard axioms, mentioning no checker constant, no
`TagsAgree` / `tagAgrees`, no `MachineClosesAt` / `MachineCloses` / `ChildRanIn`; their Prop
binders: the run, `MachineDefines f`, `MachineDefines SparkleMem.sync.4.8`. -/

namespace Sparkle.Tests.Compiler.MemNameCollisionCertTest

#machine_endpoint collSameR
#machine_endpoint collArgsR
#machine_design_svR0 collSameR
#machine_design_svR0 collArgsR

#machine_no_ports_memseq_try collSameR "GENERATED"
#machine_no_ports_memseq_try collArgsR "GENERATED"

end Sparkle.Tests.Compiler.MemNameCollisionCertTest

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  for f in [``Sparkle.Tests.Compiler.MemNameCollisionCertTest.collSameR,
      ``Sparkle.Tests.Compiler.MemNameCollisionCertTest.collArgsR] do
    let openN := f ++ `machine_design_noPortsR0
    let closed := Tools.ShippingMachineClosesGen.closedName openN
    for n in [openN, closed, f ++ `noPortsMemSeq_closes, f ++ `noPortsMemSeq_kids] do
      unless (← Lean.getEnv).contains n do throwError "{n}: missing"
      Tests.Compiler.NoPortsTest.stdAxioms n
    let t := (← Lean.getConstInfo closed).type
    for k in Tests.Compiler.NoPortsTest.checkers ++ Tools.ShippingNoPortsMemCommand.forbiddenMem ++
        [``Tools.ShippingInstTagged.TagsAgree, ``Tools.ShippingInstTagged.tagAgrees,
         ``Tools.ShippingChildInv.MachineClosesAt, ``Tools.ShippingMachineEntry.MachineCloses,
         ``Tools.ShippingChildInv.ChildRanIn] do
      if (t.find? (·.isConstOf k)).isSome then throwError "{closed}: mentions {k}"
    -- the kids are taken by ORIGIN
    let kt := (← Lean.getConstInfo (f ++ `noPortsMemSeq_kids)).type
    unless (kt.find? (·.isConstOf ``Tools.ShippingMemKid.KidFactsT)).isSome do
      throwError "{f}.noPortsMemSeq_kids: not over KidFactsT (tag mode not taken)"
    let bs ← Lean.Meta.forallTelescope t fun xs _ => do
      let mut out : Array String := #[]
      for x in xs do
        let ty ← Lean.instantiateMVars (← Lean.Meta.inferType x)
        if ← Lean.Meta.isProp ty then out := out.push (toString (← Lean.Meta.ppExpr ty))
      return out
    Lean.logInfo m!"COLLGEN {closed}: {bs.size} Prop binders {bs}"
    unless bs.size == 3 do throwError "{closed}: {bs.size} Prop binders, expected 3"
