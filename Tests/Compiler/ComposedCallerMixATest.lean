-- BUILT (unit SR2c, par/u-sr2c): s4 exit 0 (in-test audit + conclusion comparison THROW on failure); co-import check co1 exit 0.
import Tests.Compiler.ShippingPremiseEvalTest
import Tests.Compiler.ChildVertAuditTest
import Tools.ShippingMachineComposeRACommand

/-! # Unit SR2c: `callerMix` — the composed head on the new boundary with `hcalls`/`hfn` PROVED

`callerMix` (two distinct one-output gate children `pick`, `pickD`) has the old composed theorem
`callerMix.machine_composedR` (`ChildBnd` + two `EntryDefines` → `ComposedH`). `generateComposedRN` builds
`callerMix.machine_composedRN` = `machine_linked_callsRA` with `hcalls` (reused from the old generator: it does not
mention the boundary) and `hfn` (PROVED from `pick.gate_linked` / `pickD.gate_linked`, i.e. the child's own
`gate_child_full` on the run `realChildA_inv` supplies). Remaining premises: `O`, the ServedRealA trace `h`,
`hR0 hR1 : EntryDefines`. Not runtime fit; `RealChildA` is a history. -/
namespace Tests.Compiler.ComposedCallerMixATest
open Lean Elab Meta Term
open Sparkle.Tests.Compiler.ShippingPremiseEvalTest

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
  withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) do
  let n ← Tools.ShippingMachineComposeRACommand.generateComposedRN ``callerMix
  logInfo m!"{n}: {(← getConstInfo n).type}"

open Tests.Compiler.ChildVertAuditTest in
/-- AUDIT (THROWS): standard axioms; the outer Prop premises are exactly the ServedRealA trace `h`
(`MachineTraceLBX`) and one `EntryDefines` per callee — NO `hfn`/`hcalls` binder, no `ChildBnd`/`InvW`;
one data binder `O : RefLawsAOps MkRefd _ _`, no `RefLawsATele`; closure free of RefLaws/RefLawsCore/toAOps/toA/
`ChildBnd`/`StartV`/`InvW`; the old head `machine_linked_callsR` is not used. Opaque counts are structural. -/
def auditRN (n : Name) : TermElabM Unit := do
  stdAxioms n
  let ty := (← getConstInfo n).type
  let (heads, nO) : Array (Option Name) × Nat ← forallTelescope ty fun xs _ => do
    let mut ps : Array (Option Name) := #[]
    let mut a : Nat := 0
    for x in xs do
      let t ← inferType x
      if ← isProp t then ps := ps.push t.getAppFn.constName?
      if t.getAppFn.constName? == some ``Tools.ShippingChildInvA.RefLawsAOps then
        unless (t.getAppArgs[0]?.bind (·.constName?)) == some ``Tools.ShippingChildFresh.MkRefd do
          throwError "{n}: RefLawsAOps binder with Fresh ≠ MkRefd"
        a := a + 1
    return (ps, a)
  unless nO == 1 do throwError "{n}: {nO} RefLawsAOps binders"
  unless heads.toList == [some ``Tools.ShippingMachineTraceX.MachineTraceLBX,
      some ``Tools.ShippingInlineSoundness.EntryDefines, some ``Tools.ShippingInlineSoundness.EntryDefines] do
    throwError "{n}: outer premises {heads}"
  let cl ← depClosure n
  let bad := hits cl ++ cl.toList.filter fun c =>
    [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingChildInv.InvW,
     `Tools.ShippingMachineComposeR.machine_linked_callsR].any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "{n}: old boundary in closure: {bad}"
  unless cl.contains ``Tools.ShippingMachineComposeRA.machine_linked_callsRA do
    throwError "{n}: does not use machine_linked_callsRA"
  let (axs, ops, exts, impls) ← boundary cl
  logInfo m!"RN AUDIT OK: {n}: standard axioms; outer premises = ServedRealA trace + 2 EntryDefines (no hfn/hcalls); one O; closure {cl.size} constants, none of RefLaws/RefLawsCore/toAOps/toA/ChildBnd/StartV/InvW/machine_linked_callsR; boundary (structural): {axs.length} axioms, {ops.length} opaque, {exts.length} extern, {impls.length} implemented_by"

/-- OLD vs NEW conclusion (THROWS): after identifying the module `m` and design `design`, the conclusion
`ComposedH (fun _ _ => True) callerMix d 1 m design dom src ext` of `machine_composedR` is `isDefEq` to the one of
`machine_composedRN`, and the old conclusion mentions no other binder. NOT compared: the premises (they differ by
construction: `ChildBnd`-based vs `O` + ServedRealA trace). -/
def sameConclusionRN (old new : Name) : TermElabM Unit := do
  let tyN := (← getConstInfo new).type
  let tyO := (← getConstInfo old).type
  forallTelescope tyN fun xs cn =>
  forallTelescope tyO fun ys co => do
    let find (as : Array Lean.Expr) (nm : Name) : MetaM Lean.Expr := do
      let some x ← as.findM? (fun x => do return (← x.fvarId!.getUserName) == nm)
        | throwError "no binder {nm}"
      return x
    let co' := co.replaceFVars #[← find ys `m, ← find ys `design] #[← find xs `m, ← find xs `design]
    for y in ys do
      if co'.containsFVar y.fvarId! then throwError "old conclusion mentions old binder {y}"
    unless ← isDefEq co' cn do throwError "conclusions differ"
    logInfo m!"CONCLUSION: old {old} and new {new} have the same ComposedH conclusion (isDefEq, over m, design)"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  auditRN ``callerMix.machine_composedRN
  sameConclusionRN ``callerMix.machine_composedR ``callerMix.machine_composedRN

#print axioms callerMix.machine_composedRN

end Tests.Compiler.ComposedCallerMixATest
