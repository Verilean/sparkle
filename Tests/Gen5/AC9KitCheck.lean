import Tools.ShippingGen5AccKit
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Pod target build OK at 424e27a6 (Tests.Gen5.AC9KitCheck, 766 jobs); clean issue-linked build is the coder's. No sorry / axiom / native_decide.

/-! # Check for `accServed0_of_cover_gatesK` (scripts/gen5/AC9KIT_FREEZE.md)

Against `accServed0_of_cover_gates` (Tools/ShippingGen5AccRoute.lean):
* `hDS` and `hK` are not binders of the new theorem, nor is `K`; the added binders are exactly `lvl initsOf hs genData₀`.
* every other old binder has, after replacing `K` by the `mkKit …` term found in the new conclusion and the other old binders by the
  new binder of the same name, a type `==` to the new binder's type.
* the conclusion is `AccServed0Stmt (mkKit …) L Reach` (head `AccServed0Stmt`, kit argument headed by `mkKit`).
* the type of `hs` is `==` to the type of `hs` of `factsOf_genS_assembled''` (existing row C.SM-1) at `dataOf := dataOfAt lvl`.
Controls: comparing without substituting `K` fails; `hs` is not `DataSoundAt (dataOfAt lvl)` (that def lacks `initOk`).
Names are compared; mutants here are rejections by `==` on types, not semantic counterexamples. Axioms. -/

namespace Tests.Gen5.AC9KitCheck
open Lean Meta
open Tests.Gen3.ExpectedType (stmtOf checkAxioms)

def binders (t : Expr) : MetaM (Array (Name × Expr) × Expr) :=
  forallTelescope t fun xs b => do
    let mut r := #[]
    for x in xs do r := r.push ((← x.fvarId!.getUserName).eraseMacroScopes, ← inferType x)
    pure (r, b)

run_cmd Lean.Elab.Command.liftTermElabM do
  let a ← stmtOf ``Tools.ShippingGen5Acc.accServed0_of_cover_gatesK
  let e ← stmtOf ``Tools.ShippingGen5Acc.accServed0_of_cover_gates
  forallTelescope a fun xa ca => forallTelescope e fun xe ce => do
    let na ← xa.mapM fun x => do pure (← x.fvarId!.getUserName).eraseMacroScopes
    let ne ← xe.mapM fun x => do pure (← x.fvarId!.getUserName).eraseMacroScopes
    for nm in [`hDS, `hK, `K] do
      if na.contains nm then throwError "AC9KIT CHECK FAILED: {nm} is a binder of the new theorem"
    let added := na.filter (!ne.contains ·)
    let removed := ne.filter (!na.contains ·)
    unless added == #[`lvl, `initsOf, `hs, `genData₀] do throwError "AC9KIT CHECK FAILED: added binders {added}"
    unless removed == #[`K, `hDS] do throwError "AC9KIT CHECK FAILED: removed binders {removed}"
    -- conclusion
    unless ca.isAppOf ``Tools.ShippingGen5Acc.AccServed0Stmt do throwError "AC9KIT CHECK FAILED: conclusion head"
    let kit := ca.getAppArgs.filter (·.isAppOf ``Tools.ShippingGen5Acc.mkKit)
    unless kit.size == 1 do throwError "AC9KIT CHECK FAILED: conclusion kit is not one mkKit term"
    let kit := kit[0]!
    -- substitution old -> new
    let idx (n : Name) : Nat := (na.findIdx? (· == n)).getD 0
    let mut from_ : Array Expr := #[]
    let mut to_ : Array Expr := #[]
    for i in [0:xe.size] do
      if ne[i]! == `K then from_ := from_.push xe[i]!; to_ := to_.push kit
      else if ne[i]! != `hDS then from_ := from_.push xe[i]!; to_ := to_.push xa[idx ne[i]!]!
    let mut cnt : Nat := 0
    for i in [0:xe.size] do
      if ne[i]! == `K || ne[i]! == `hDS then continue
      let te := (← inferType xe[i]!).replaceFVars from_ to_
      let ta ← inferType xa[idx ne[i]!]!
      unless te == ta do throwError "AC9KIT CHECK FAILED: binder {ne[i]!} type"
      cnt := cnt + 1
    unless (ce.replaceFVars from_ to_) == ca do throwError "AC9KIT CHECK FAILED: conclusion differs from the old one at K := mkKit …"
    logInfo m!"AC9KIT BINDERS: {cnt} common binders == after K := mkKit …; removed {removed}; added {added}; conclusion AccServed0Stmt (mkKit …) L Reach"
    -- control: the type of `hcov` without substituting K is not the new one
    let i := (ne.findIdx? (· == `hcov)).getD 0
    let mut from2 : Array Expr := #[]
    let mut to2 : Array Expr := #[]
    for j in [0:xe.size] do
      if ne[j]! != `K && ne[j]! != `hDS then from2 := from2.push xe[j]!; to2 := to2.push xa[idx ne[j]!]!
    let unsub := (← inferType xe[i]!).replaceFVars from2 to2
    if unsub == (← inferType xa[idx `hcov]!) then throwError "AC9KIT CHECK CONTROL: unsubstituted comparison accepted"
    logInfo "AC9KIT CONTROL: comparison without K := mkKit … rejected"
  -- hs against C.SM-1
  let c ← stmtOf ``Tools.ShippingGen5Acc.factsOf_genS_assembled''
  forallTelescope c fun xs _ => do
    let mut hs0 : Option Expr := none
    let mut df : Option Expr := none
    let mut io : Option Expr := none
    for x in xs do
      match (← x.fvarId!.getUserName).eraseMacroScopes with
      | `hs => hs0 := some x
      | `dataOf => df := some x
      | `initsOf => io := some x
      | _ => pure ()
    let (some hs1, some df1, some io1) := (hs0, df, io) | throwError "AC9KIT CHECK FAILED: factsOf_genS_assembled'' binders"
    forallTelescope (← stmtOf ``Tools.ShippingGen5Acc.accServed0_of_cover_gatesK) fun ys _ => do
      let mut lvl? := none
      let mut ini? := none
      for y in ys do
        match (← y.fvarId!.getUserName).eraseMacroScopes with
        | `lvl => lvl? := some y
        | `initsOf => ini? := some y
        | _ => pure ()
      let (some lvl, some ini) := (lvl?, ini?) | throwError "AC9KIT CHECK FAILED: lvl/initsOf"
      let want := (← inferType hs1).replaceFVars #[df1, io1] #[mkApp (mkConst ``Tools.ShippingGen5DataOf.dataOfAt) lvl, ini]
      let some hsY ← ys.findM? fun y => do pure ((← y.fvarId!.getUserName).eraseMacroScopes == `hs) | throwError "no hs"
      unless (← inferType hsY) == want do throwError "AC9KIT CHECK FAILED: hs type differs from C.SM-1's DataOfSound (factsOf_genS_assembled'')"
      unless (← inferType hsY).isAppOf ``Tools.ShippingGen5Sem.DataOfSound do throwError "AC9KIT CHECK FAILED: hs is not DataOfSound"
      logInfo "AC9KIT HS: type of hs == DataOfSound (dataOfAt lvl) initsOf == hs of factsOf_genS_assembled'' (C.SM-1)"
      let dsa := mkApp (mkConst ``Tools.ShippingGen5Acc.DataSoundAt) (mkApp (mkConst ``Tools.ShippingGen5DataOf.dataOfAt) lvl)
      if (← inferType hsY) == dsa then throwError "AC9KIT CHECK CONTROL: hs equals DataSoundAt"
      logInfo "AC9KIT CONTROL: hs type differs from DataSoundAt (dataOfAt lvl) (no initOk conjunct there)"
  checkAxioms ``Tools.ShippingGen5Acc.accServed0_of_cover_gatesK
  logInfo "AC9KIT COUNTS: BINDERS 1, HS 1, CONTROLS 2, AXIOMS 1"

end Tests.Gen5.AC9KitCheck
