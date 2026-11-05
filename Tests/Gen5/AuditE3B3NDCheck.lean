import Lean
import Tools.ShippingGen5AuditE3B3ND
set_option autoImplicit false
-- A.P-17 re-threading check: the ND copies differ from the T1Hyp originals only in the type of `H` (structural Expr ==).

/-! The telescope of the ND copy is opened once; each binder of the original is instantiated with the ND free variable of the
same name and its type compared with `Expr` `==`. Expected: removed [], added [], changed [H] (`T1Hyp` → `T1HypND`, checked by
head constant), conclusions `==`. NEGATIVE controls: self-comparison has no change; the original's `H` is `T1Hyp`; no binder of the
ND copy uses `T1Hyp`. -/
open Lean Meta

namespace Tests.Gen5.AuditE3B3NDCheck

abbrev Res := List Name × List Name × List Name × Bool

partial def walkOld (ys : Array (Name × BinderInfo × Expr × Expr)) :
    Expr → List Name → List Name → (Expr → List Name → List Name → MetaM Res) → MetaM Res
  | .forallE n d b bi, rm, ch, k =>
    match ys.find? (·.1 == n) with
    | some (_, bi', fv, ty') =>
      walkOld ys (b.instantiate1 fv) rm (if bi == bi' && d == ty' then ch else ch ++ [n]) k
    | none => withLocalDecl n bi d fun x => walkOld ys (b.instantiate1 x) (rm ++ [n]) ch k
  | body, rm, ch, k => k body rm ch

def diff (old new : Name) : MetaM Res := do
  let oci ← getConstInfo old
  let nci ← getConstInfo new
  let oNames ← forallTelescope oci.type fun xs _ => xs.toList.mapM fun x => return (← x.fvarId!.getDecl).userName
  forallTelescope nci.type fun xs nbody => do
    let mut ys : Array (Name × BinderInfo × Expr × Expr) := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      ys := ys.push (d.userName, d.binderInfo, x, d.type)
    let ys' := ys
    walkOld ys' oci.type [] [] fun obody rm ch => do
      let added := (ys'.toList.filter fun y => !oNames.contains y.1).map (·.1)
      return (rm, added, ch, obody == nbody)

def headOf (c : Name) (nm : Name) : MetaM (Option Name) := do
  let ci ← getConstInfo c
  forallTelescope ci.type fun xs _ => do
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.userName == nm then return d.type.getAppFn.constName?
    return none

def usesT1Hyp (c : Name) : MetaM Bool := do
  let ci ← getConstInfo c
  forallTelescope ci.type fun xs _ => xs.anyM fun x => do
    return (← x.fvarId!.getDecl).type.getUsedConstants.contains ``Tools.ShippingGen2.T1Hyp

run_meta do
  let pairs : List (Name × Name) :=
    [(``Tools.ShippingGen5AuditE3B3.machPrem3R_of_t1hyp, ``Tools.ShippingGen5AuditE3B3.machPrem3R_of_t1hypND),
     (``Tools.ShippingGen5AuditE3B3.auditE3B3_of_t1hyp_run, ``Tools.ShippingGen5AuditE3B3.auditE3B3_of_t1hypND_run)]
  for (o, n) in pairs do
    let (rm, ad, ch, same) ← diff o n
    logInfo m!"{n}: removed {rm} added {ad} changed {ch} sameConcl {same}"
    unless rm == [] && ad == [] && ch == [`H] && same do
      throwError "{n}: unexpected diff: removed {rm} added {ad} changed {ch} sameConcl {same}"
    unless (← headOf o `H) == some ``Tools.ShippingGen2.T1Hyp do throwError "CONTROL: {o}.H is not T1Hyp"
    unless (← headOf n `H) == some ``Tools.ShippingGen2.T1HypND do throwError "{n}.H is not T1HypND"
    if ← usesT1Hyp n then throwError "{n}: a binder still uses T1Hyp"
    let (rmS, adS, chS, sameS) ← diff n n
    unless rmS == [] && adS == [] && chS == [] && sameS do throwError "NEG: self-comparison of {n} not empty"
  logInfo m!"AUDITE3B3ND COUNTS: pairs 2, controls 2 (original H = T1Hyp), self 2"

#print axioms Tools.ShippingGen5AuditE3B3.machPrem3R_of_t1hypND
#print axioms Tools.ShippingGen5AuditE3B3.auditE3B3_of_t1hypND_run

end Tests.Gen5.AuditE3B3NDCheck
