-- BUILT (unit SR2e): sr2e5 exit 0 (in-test audit + #print axioms: standard only).
import Tests.Compiler.ComposedCallerMixATest
import Tests.Compiler.ComposedCallerMixEntryTest

/-! # callerMix's two `EntryDefines`, reduced to `EnvDefines` (unit SR2e)

`EntryDefines c v` is an ALL-WORLD run property (`getConstInfo` / `getEnv` runs from every start world), so it
is NOT removed by evaluating anything in the current elaboration environment.  What IS decided here: the
GATE half of `EntryDefines.of_env` — for the value `pick.gateValue` (resp. `pickD.gateValue`) the mixed gate
accepts EVERY definition with that value, whatever its type and whatever instance predicate
(the disjunct `unifiedGateRoot` reads neither).  What is left: `EnvDefines c c.gateValue` — the environment
the run reads defines `c` with that value (a run fact about the Core state behind an `ST.Ref`; its
consistency with the real environment is a SEPARATE OPEN item, recorded as such). -/
namespace Tests.Compiler.EntryGateCallerMixTest
open Lean Meta Sparkle.Compiler.Elab Sparkle.Tests.Compiler.ShippingMachineInstTest
open Sparkle.Tests.Compiler.ShippingPremiseEvalTest
open Tools.ShippingInlineSoundness
open Tools.ShippingEntrySoundness (EnvDefines RunsTo)

theorem pick_gate : ∀ d : DefinitionVal, d.value = pick.gateValue → ∀ isInst,
    (mixedCertifiedShape? false [] (.defnInfo d) isInst).isSome = true := by
  intro d hd isInst
  have h : (match mixedGatePeel pick.gateValue with
    | some (bs, body) => unifiedGateRoot (bs.map (·.2)).toArray body | none => false) = true := by decide
  cases hp : mixedGatePeel pick.gateValue with
  | none => rw [hp] at h; cases h
  | some p =>
    obtain ⟨bs, body⟩ := p
    rw [hp] at h
    have h' : unifiedGateRoot (bs.map (·.2)).toArray body = true := h
    simp [mixedCertifiedShape?, hd, hp, h']

theorem pickD_gate : ∀ d : DefinitionVal, d.value = pickD.gateValue → ∀ isInst,
    (mixedCertifiedShape? false [] (.defnInfo d) isInst).isSome = true := by
  intro d hd isInst
  have h : (match mixedGatePeel pickD.gateValue with
    | some (bs, body) => unifiedGateRoot (bs.map (·.2)).toArray body | none => false) = true := by decide
  cases hp : mixedGatePeel pickD.gateValue with
  | none => rw [hp] at h; cases h
  | some p =>
    obtain ⟨bs, body⟩ := p
    rw [hp] at h
    have h' : unifiedGateRoot (bs.map (·.2)).toArray body = true := h
    simp [mixedCertifiedShape?, hd, hp, h']

theorem entryDefines_pick {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (env : EnvDefines mctx mref cctx cref ``pick pick.gateValue) :
    EntryDefines mctx mref cctx cref ``pick pick.gateValue :=
  EntryDefines.of_env env pick_gate

theorem entryDefines_pickD {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (env : EnvDefines mctx mref cctx cref ``pickD pickD.gateValue) :
    EntryDefines mctx mref cctx cref ``pickD pickD.gateValue :=
  EntryDefines.of_env env pickD_gate

open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA

noncomputable local instance : Inhabited (Sparkle.Core.HList (Tools.ShippingMachineDenote.tys callerMix.machineData.ss)) :=
  ⟨callerMix.machineInits⟩

set_option maxHeartbeats 0 in
/-- callerMix's ONE chain with the two `EntryDefines` replaced by `EnvDefines pick` / `EnvDefines pickD`. -/
theorem callerMix_entryComposed_env
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (T : RefLawsATele O.quiet mref cref)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``callerMix [] false) mctx mref cctx cref w (m, design) w')
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``callerMix callerMix.machineData.shape)
    (hw : JQ O.quiet 0 w)
    (hE0 : EnvDefines mctx mref cctx cref ``pick pick.gateValue)
    (hE1 : EnvDefines mctx mref cctx cref ``pickD pickD.gateValue) :
    Tools.ShippingMachineShipsHierH.ComposedH (fun _ _ => True) ``callerMix callerMix.machineData 1 m design
      (fun _ => Sparkle.Core.Domain.defaultDomain) callerMix.machineSource
      (fun i bools bits => callerMix.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop callerMix.machineInits (callerMix.machineBody i bools bits))) :=
  Tests.Compiler.ComposedCallerMixEntryTest.callerMix_entryComposed O hA T hr entry hw
    (entryDefines_pick hE0) (entryDefines_pickD hE1)

open Tests.Compiler.ChildVertAuditTest in
run_cmd Lean.Elab.Command.liftTermElabM do
  stdAxioms ``callerMix_entryComposed_env
  let ty := (← getConstInfo ``callerMix_entryComposed_env).type
  let heads : Array (Option Name) ← forallTelescope ty fun xs _ => do
    let mut ps : Array (Option Name) := #[]
    for x in xs do ps := ps.push (← inferType x).getAppFn.constName?
    return ps
  let want : List (Option Name) := [some ``Tools.ShippingChildInvA.RefLawsAOps,
    some ``Tools.ShippingChildInvA.AdmCtx, some ``Tools.ShippingChildInvA.RefLawsATele,
    some ``Tools.ShippingEntrySoundness.RunsTo, some ``Tools.ShippingMachineEntry.MachineDefines,
    some ``Tools.ShippingChildVCA.JQ, some ``Tools.ShippingEntrySoundness.EnvDefines,
    some ``Tools.ShippingEntrySoundness.EnvDefines]
  unless heads.toList.drop 8 == want do throwError "binders {heads}"
  let cl ← depClosure ``callerMix_entryComposed_env
  unless cl.contains ``Tools.ShippingInlineSoundness.EntryDefines.of_env do throwError "no of_env"
  logInfo m!"SR2e AUDIT OK: premises = O, hA, T, core run, MachineDefines, JQ O.quiet 0 w, EnvDefines pick, EnvDefines pickD (EntryDefines gone; the gate half decided by pick_gate/pickD_gate); EnvDefines is a run fact, NOT discharged"

#print axioms callerMix_entryComposed_env
end Tests.Compiler.EntryGateCallerMixTest
