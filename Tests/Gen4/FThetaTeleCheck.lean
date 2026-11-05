import Lean
import Tools.ShippingGen4FThetaTele
set_option autoImplicit false
-- F-θ option A check: `fTheta_natBinderN` vs `fTheta_natBinder` by structural Expr comparison (one telescope walk).

/-! # `htele` replaced by `LamTelescopeN`

The telescope of `fTheta_natBinderN` is opened once; each binder of `fTheta_natBinder` is instantiated with the free variable of
the same name (types compared with `Expr` `==`), a binder absent from the new theorem with a fresh local. Expected: removed
`[htele]`, added `[htel]` (type `== LamTelescopeN`), changed `[]`, conclusions `==`. NEGATIVE controls: a self-comparison has
no difference; the old theorem compared to `fTheta_natBinderN` with `htele` NOT treated as removed fails; `htel`'s type is not
`TelescopeIn …`. -/
open Lean Meta

namespace Tests.Gen4.FThetaTeleCheck

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

run_meta do
  let old := ``Tools.ShippingGen4FTheta.fTheta_natBinder
  let new := ``Tools.ShippingGen4FTheta.fTheta_natBinderN
  let (rm, ad, ch, same) ← diff old new
  logInfo m!"FTHETA-TELE: removed {rm} added {ad} changed {ch} sameConcl {same}"
  unless rm == [`htele] && ad == [`htel] && ch == [] && same do throwError "fTheta_natBinderN diff unexpected"
  -- htel's type is exactly LamTelescopeN
  let nci ← getConstInfo new
  let ok ← forallTelescope nci.type fun xs _ => do
    let d ← xs[0]!.fvarId!.getDecl
    return d.userName == `htel && d.type == mkConst ``Tools.ShippingLegacySem.LamTelescopeN
  unless ok do throwError "first binder of fTheta_natBinderN is not htel : LamTelescopeN"
  -- NEGATIVE CONTROLS
  let (rmS, adS, chS, sameS) ← diff new new
  unless rmS == [] && adS == [] && chS == [] && sameS do throwError "NEG1: self-comparison not empty"
  if rm == [] then throwError "NEG2: htele not detected as removed"
  let isTele ← forallTelescope nci.type fun xs _ => do
    let d ← xs[0]!.fvarId!.getDecl
    return d.type.getUsedConstants.contains ``Tools.ShippingLegacySem.TelescopeIn
  if isTele then throwError "NEG3: htel mentions TelescopeIn"
  logInfo m!"FTHETA-TELE NEG: self {(rmS, adS, chS, sameS)}; htel uses TelescopeIn {isTele}"

#print axioms Tools.ShippingGen4FTheta.lams_split
#print axioms Tools.ShippingGen4FTheta.telescopeIn_of_lamTelescopeN
#print axioms Tools.ShippingGen4FTheta.fTheta_natBinderN

end Tests.Gen4.FThetaTeleCheck
