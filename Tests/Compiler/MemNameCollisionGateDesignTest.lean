import Tests.Compiler.MemNameCollisionGateCertTest
import Tests.Compiler.NoPortsTest
import Tools.ShippingMachineGateMemCommand

/-! # Design-level endpoints of parents with a register, a MEMORY and a GATE-route child (round par/o-gdes, unit "1")

WRITTEN, NOT BUILT.

`mixSame` (control: the combinational `@[hardware_module]` `fakeSrc` called under its own name)
and `collMixSame` (collision: the same declaration copied under the synchronous memory's
placeholder name `SparkleMem.sync.4.8`, origin `.ord`, next to the memory entry of origin
`.mem false 4 8`), from `Tests/Compiler/MemNameCollisionGateCertTest.lean`. Before this unit
`#machine_design_svR0` refused both ("seq child …: no machine_sound"): every non-memory entry was
read as a SEQUENTIAL child.

`Tools/ShippingMachineGateMemCommand.lean` dispatches the entries by ORIGIN (memory) and, for a
non-memory entry, by the callee's declaration (a `machine_sound`: sequential; none: gate, its
`c.gate_kid_run` from `Tools.ShippingMachineCallsLinkedTG.gateKidRun_of_gateRun`), and composes
with `machine_linkedT_callsRG` (a third, gate, kind of call). The gate child's run boundary
(`GateRun`) is DERIVED from `ServedReal` (under `ChildBnd`) and the callee's reflection
`EntryDefines c c.gateValue`, which joins the children's reflection premise `hrefl`.

Generated: `f.machine_composedTRG` (composed level, all-worlds closing `MachineCloses` of `f`
from the head), `f.machine_composedTRGA`, `f.machine_ships_hierRG`, `f.machine_design_svRG0`
(`DesignSV` of the shipped module list at depth 0, as `#machine_design_svR0`). For `collMixSame`
the closing binder `MachineClosesAt collMixSame` is replaced (`addDesignG`) by the colliding
declaration's reflection `EntryDefines SparkleMem.sync.4.8 fakeSrc.gateValue`, the closing given
by `collMixSame_closes` (`collMixSame_designG`). The audit below asserts standard axioms, no
`TagsAgree` / `tagAgrees`, and logs the Prop binders. -/

namespace Sparkle.Tests.Compiler.MemNameCollisionGateCertTest

#machine_endpoint mixSame
#machine_endpoint collMixSame

#machine_composedTRG mixSame
#machine_composedTRG collMixSame

#machine_design_svRG0 mixSame
#machine_design_svRG0 collMixSame

set_option maxHeartbeats 4000000 in
/-- `collMixSame_closes` at the endpoint's data constant (the same reader data). -/
theorem collMixSame_closesR {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``collMixSame
      (collMixSame.machineData).shape :=
  collMixSame_closes hR0

end Sparkle.Tests.Compiler.MemNameCollisionGateCertTest

namespace Sparkle.Tests.Compiler.MemNameCollisionGateDesignTest
open Lean Meta

/-- **`collMixSame_designG`**: `collMixSame.machine_design_svRG0` with its `MachineClosesAt`
binder replaced by the colliding declaration's reflection `hR0` (same contexts), the closing
given by `collMixSame_closesR hR0`. -/
def addDesignG : MetaM Unit := do
  let ns := `Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
  let base := ns ++ `collMixSame ++ `machine_design_svRG0
  let name := `Sparkle.Tests.Compiler.MemNameCollisionGateDesignTest.collMixSame_designG
  let ci ← getConstInfo base
  unless ci.levelParams.isEmpty do throwError "{base}: universe parameters"
  let (type, value) ← forallTelescope ci.type fun xs body => do
    let mut idx? : Option Nat := none
    for i in [0:xs.size] do
      if (← instantiateMVars (← inferType xs[i]!)).isAppOf ``Tools.ShippingChildInv.MachineClosesAt then
        if idx?.isSome then throwError "{base}: two MachineClosesAt binders"
        idx? := some i
    let some i := idx? | throwError "{base}: no MachineClosesAt binder"
    let clT ← instantiateMVars (← inferType xs[i]!)
    let a := clT.getAppArgs
    let hR0T := mkAppN (mkConst ``Tools.ShippingInlineSoundness.EntryDefines)
      #[a[0]!, a[1]!, a[2]!, a[3]!, mkConst (ns ++ `syncName), mkConst (ns ++ `fakeSrc ++ `gateValue)]
    withLocalDeclD `hR0 hR0T fun hR0 => do
      let pf ← mkAppOptM (ns ++ `collMixSame_closesR) #[a[0]!, a[1]!, a[2]!, a[3]!, hR0]
      unless ← isDefEq (← inferType pf) clT do
        throwError "collMixSame_closesR does not prove the binder{indentExpr clT}"
      let args := xs.set! i pf
      let newXs := (xs.extract 0 i).push hR0 ++ xs.extract (i + 1) xs.size
      let v := mkAppN (mkConst base) args
      if body.hasAnyFVar (· == xs[i]!.fvarId!) then
        throwError "{base}: the conclusion depends on the closing binder"
      for x in xs.extract (i + 1) xs.size do
        if (← inferType x).hasAnyFVar (· == xs[i]!.fvarId!) then
          throwError "{base}: a later binder depends on the closing binder"
      pure (← mkForallFVars newXs body, ← mkLambdaFVars newXs v)
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  Lean.addDecl (.thmDecl { name, levelParams := [], type, value })

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM <|
  Lean.withOptions (fun o => Lean.Elab.async.set o false) addDesignG

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ns := `Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
  let syncName := Sparkle.Compiler.MachMemory.memChildName false 4 8
  let thms : List Name :=
    [``Tools.ShippingMachineCallsLinkedTG.gateKidRun_of_gateRun,
     ``Tools.ShippingMachineCallsLinkedTG.gate_inst_run,
     ``Tools.ShippingMachineCallsLinkedTG.calls_hchildRG,
     ``Tools.ShippingMachineCallsLinkedTG.machine_linkedT_callsRG,
     ns ++ `fakeSrc ++ `gate_kid_run, syncName ++ `gate_kid_run] ++
    ([ns ++ `mixSame, ns ++ `collMixSame].flatMap fun f =>
      [f ++ `machine_composedTRG, f ++ `machine_composedTRGA, f ++ `machine_ships_hierRG,
       f ++ `machine_design_svRG0]) ++
    [`Sparkle.Tests.Compiler.MemNameCollisionGateDesignTest.collMixSame_designG]
  for n in thms do
    unless (← Lean.getEnv).contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  for n in thms.drop 6 do
    let t := (← Lean.getConstInfo n).type
    for k in [``Tools.ShippingInstTagged.TagsAgree, ``Tools.ShippingInstTagged.tagAgrees] do
      if (t.find? (·.isConstOf k)).isSome then throwError "{n}: mentions {k}"
    -- the gate children's boundary is derived: no `GateRun` binder
    let bs ← Lean.Meta.forallTelescope t fun xs _ => do
      let mut out : Array String := #[]
      for x in xs do
        let ty ← Lean.instantiateMVars (← Lean.Meta.inferType x)
        if ← Lean.Meta.isProp ty then
          if ty.isAppOf ``Tools.ShippingGateChild.GateRun then
            throwError "{n}: a GateRun binder"
          out := out.push (toString (← Lean.Meta.ppExpr ty))
      return out
    Lean.logInfo m!"GATEDESIGN {n}: {bs.size} Prop binders {bs}"
  -- the collision design endpoint: no closing binder; the colliding declaration's reflection is one
  let t := (← Lean.getConstInfo `Sparkle.Tests.Compiler.MemNameCollisionGateDesignTest.collMixSame_designG).type
  if (t.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
    throwError "collMixSame_designG: mentions MachineClosesAt"
  unless (t.find? (·.isConstOf ``Tools.ShippingInlineSoundness.EntryDefines)).isSome do
    throwError "collMixSame_designG: no EntryDefines of the colliding declaration"

end Sparkle.Tests.Compiler.MemNameCollisionGateDesignTest
