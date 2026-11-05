import Lean
import Tools.ShippingGen5AP17
import Tools.ShippingGen5AuditE3B3ND
import Tools.ShippingGen5T2OutTy
set_option autoImplicit false
-- A.P-17 re-threading scan: every Tools constant with a binder whose type uses `T1Hyp` has an ND counterpart without `T1Hyp`.

/-! Scan of this environment (imported constants `map₁` and local `map₂`): each `Tools.*` constant one of whose binders (premises
or arguments, by `forallTelescope`) uses the constant `Tools.ShippingGen2.T1Hyp` must be either the adapter `T1Hyp.toND`, a
field/structure item of `T1Hyp` itself, or a key of `ndOf` whose value exists and has NO binder using `T1Hyp`. Unmapped users are
printed and fail the check. Positive control: the known user `Tools.ShippingGen2.ih_allPF` is found. -/
open Lean Meta

namespace Tests.Gen5.AP17ScanCheck

def ndOf : List (Name × Name) :=
  [(``Tools.ShippingGen2.ihAt_stepPF, ``Tools.ShippingGen2.ihAt_stepPF_ND),
   (``Tools.ShippingGen2.ih_allPF, ``Tools.ShippingGen2.ih_allPF_ND),
   (``Tools.ShippingGen2.t1_of_stepPF, ``Tools.ShippingGen2.t1_of_stepPF_ND),
   (``Tools.ShippingGen5ClosingRun4.closingRun0_of_runT1, ``Tools.ShippingGen2.closingRun0_of_runT1_ND),
   (``Tools.ShippingGen5ClosingRun4.closingRun_of_runT1, ``Tools.ShippingGen2.closingRun_of_runT1_ND),
   (``Tools.ShippingGen2.houtTy_of_realChild, ``Tools.ShippingGen2.houtTy_of_realChildND),
   (``Tools.ShippingGen2.reach_callee_of_t1, ``Tools.ShippingGen2.reach_callee_of_t1ND),
   (``Tools.ShippingGen2.houtTy_of_closing, ``Tools.ShippingGen2.houtTy_of_closingND),
   (``Tools.ShippingGen2.callTie_of_served_oneOut_t1, ``Tools.ShippingGen2.callTie_of_served_oneOut_t1ND),
   (``Tools.ShippingGen2.callTie_of_served_kidW_closing_t1, ``Tools.ShippingGen2.callTie_of_served_kidW_closing_t1ND),
   (``Tools.ShippingGen5AuditE3B3.machPrem3R_of_t1hyp, ``Tools.ShippingGen5AuditE3B3.machPrem3R_of_t1hypND),
   (``Tools.ShippingGen5AuditE3B3.auditE3B3_of_t1hyp_run, ``Tools.ShippingGen5AuditE3B3.auditE3B3_of_t1hypND_run)]

def usesT1Hyp (ty : Expr) : MetaM Bool :=
  forallTelescope ty fun xs _ => xs.anyM fun x => do
    return (← x.fvarId!.getDecl).type.getUsedConstants.contains ``Tools.ShippingGen2.T1Hyp

run_meta do
  let env ← getEnv
  let mut users : List Name := []
  for (n, c) in env.constants.map₁.toList ++ env.constants.map₂.toList do
    if (`Tools).isPrefixOf n && !n.isInternal then
      if (`Tools.ShippingGen2.T1Hyp).isPrefixOf n then continue
      if ← usesT1Hyp c.type then users := users ++ [n]
  unless users.contains ``Tools.ShippingGen2.ih_allPF do throwError "CONTROL: the known user ih_allPF was not found"
  let allowed : List Name := [``Tools.ShippingGen2.T1Hyp.toND]
  let mut unmapped : List Name := []
  for u in users do
    if allowed.contains u then continue
    match ndOf.lookup u with
    | some nd =>
      let ci ← getConstInfo nd
      if ← usesT1Hyp ci.type then throwError "{nd} (ND of {u}) still has a T1Hyp binder"
    | none => unmapped := unmapped ++ [u]
  logInfo m!"T1Hyp users: {users.length}; mapped {ndOf.length}; unmapped {unmapped}"
  unless unmapped.isEmpty do throwError "unmapped T1Hyp users: {unmapped}"

end Tests.Gen5.AP17ScanCheck
