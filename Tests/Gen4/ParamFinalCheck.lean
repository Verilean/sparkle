import Lean
import Tests.Gen4.ParamAssemblyCheck
import Tools.ShippingGen4ParamFinal
set_option autoImplicit false
-- Check of Tools/ShippingGen4ParamFinal.lean (scripts/gen4/PARAM_ASSEMBLY.md §Final). No sorry / axiom / native_decide.

/-! # Binder difference of the FG-binder roots, and the crosswalk of the carrier / start binders

`paramFinal_old` and `paramFinal_run` are the two roots over the FG binders (`L : Laws`, `hS : Start L ..`, the run). Walked as in
`ParamAssemblyCheck` (`diffTy`): expected removed `[hL, hpos]` (B.P-8, B.P-1), added `[M, hmsg, htel]` and nothing else, changed `[]`,
conclusions `==`. The carrier `O` and the start binders `hA`, `hw` of `paramRoot_run` are NOT binders here: `start_kwd` (conclusion
`AdmCtx L.O.quiet mctx cctx ∧ KWD L.O (fun _ _ => True) 0 w` from `Start L mctx cctx w`) supplies them, and the Check compares the
types of those two conjuncts with the types of `hA` / `hw` in `paramRoot_run` (at `O := L.O`) by `Expr ==`. The gen5 side
(`FGLedgerPremisesStmtG/H`, `EntryWitness`) is on another branch (its `Elab.lean` differs); there `Tests/Gen5/ParamFinalScan.lean`
fingerprints `Laws`/`Start` for comparison with the fingerprints printed here. -/

open Lean Meta
open Tests.Gen4.ParamAssemblyCheck

namespace Tests.Gen4.ParamFinalCheck

def expectedRemoved : List Name := [`hL, `hpos]
def expectedAdded : List (Name × Name) :=
  [(`M, ``Tools.Assume.MemoFamily.MemoFamily), (`hmsg, ``Tools.ShippingGen4KWalkDiag.MsgMvK),
   (`htel, ``Tools.ShippingLegacySem.LamTelescopeN)]

def verdict (oty nty : Expr) : MetaM Bool := do
  let (rm, ad, ch, same) ← diffTy oty nty
  let hs ← headsOf nty ad
  return rm == expectedRemoved && ad == expectedAdded.map (·.1) && ch == [] && same && hs == expectedAdded

/-- the fvars of a telescope by user name -/
def byName (xs : Array Expr) : MetaM (List (Name × Expr)) :=
  xs.toList.mapM fun x => return ((← x.fvarId!.getDecl).userName, x)

run_meta do
  let oci ← getConstInfo ``Tools.ShippingGen4ParamFinal.paramFinal_old
  let nci ← getConstInfo ``Tools.ShippingGen4ParamFinal.paramFinal_run
  let (rm, ad, ch, same) ← diffTy oci.type nci.type
  let hs ← headsOf nci.type ad
  unless (← verdict oci.type nci.type) do
    throwError "paramFinal_run vs paramFinal_old unexpected: removed {rm} added {ad} changed {ch} same {same} heads {hs}"
  -- B.P-8 / B.P-1 are in the old type, not in the new type
  for c in [``Tools.ShippingGen4ParamIface.LegalBinding, ``Tools.ShippingGen4ParamLayerA.AllPos] do
    unless usesConst oci.type c do throwError "old root type does not mention {c}"
    if usesConst nci.type c then throwError "new root type still mentions {c}"
  -- the FG binders are shared and unchanged: L and hS are neither removed, added nor changed
  let names ← forallTelescope nci.type fun xs _ => xs.toList.mapM fun x => return (← x.fvarId!.getDecl).userName
  for n in [`L, `hS, `h, `hok] do unless names.contains n do throwError "FG binder {n} missing"
  -- O, hA, hw are not binders of the final form
  for n in [`O, `hA, `hw] do if names.contains n then throwError "{n} is still a free binder"
  -- the head of hS is Start, the head of L's type is Laws
  let heads ← forallTelescope nci.type fun xs _ => do
    let mut out : List (Name × Name) := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if [`L, `hS].contains d.userName then out := out ++ [(d.userName, d.type.getAppFn.constName?.getD `none)]
    return out
  unless heads == [(`L, ``Tools.ShippingGen2.Laws), (`hS, ``Tools.ShippingGen2.Start)] do
    throwError "FG binder heads unexpected: {heads}"
  logInfo m!"PARAM-FINAL COUNTS: removed {rm.length} {rm} (B.P-8, B.P-1), added {ad.length} {ad} (shared +1 [htel] = N4-a / M4.MEMO-01 [M] / conditional leaf [hmsg]), changed {ch.length}, concl {same}, FG binders L (A.P-01) and hS : Start (A.P-02) shared; O, hA, hw not binders; FG -0 +0 / T1 -0 +0 recorded"
  -- the removed rows
  let rows ← forallTelescope oci.type fun xs _ => do
    let mut out : List (Name × Name) := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if expectedRemoved.contains d.userName then out := out ++ [(d.userName, d.type.getAppFn.constName?.getD `none)]
    return out
  unless rows == [(`hL, ``Tools.ShippingGen4ParamIface.LegalBinding), (`hpos, ``Tools.ShippingGen4ParamLayerA.AllPos)] do
    throwError "removed rows unexpected: {rows}"

-- CROSSWALK by Expr ==: the conjuncts of `start_kwd` are the types of `hA` / `hw` of `paramRoot_run` at `O := L.O`
run_meta do
  let sci ← getConstInfo ``Tools.ShippingGen4ParamFinal.start_kwd
  let rci ← getConstInfo ``Tools.ShippingGen4ParamAssembly.paramRoot_run
  forallTelescope sci.type fun sxs sbody => do
    let some (tA, tK) := (match sbody.getAppFn.constName?, sbody.getAppArgs with
      | some ``And, #[a, b] => some (a, b)
      | _, _ => none) | throwError "start_kwd conclusion is not a conjunction"
    let sn ← byName sxs
    -- the term `L.O` as it occurs in the conclusion of start_kwd
    let some lo := (tA.find? fun e => e.isAppOf ``Tools.ShippingGen2.Laws.O) | throwError "no L.O in start_kwd"
    forallTelescope rci.type fun rxs _ => do
      let rn ← byName rxs
      let some O := rn.lookup `O | throwError "no O"
      let some hA := rn.lookup `hA | throwError "no hA"
      let some hw := rn.lookup `hw | throwError "no hw"
      -- map the run-form fvars (same names) to the start_kwd fvars, and O to L.O
      let from_ := (rn.filter fun p => p.1 != `O && (sn.lookup p.1).isSome).map (·.2)
      let to_ := (rn.filter fun p => p.1 != `O && (sn.lookup p.1).isSome).map fun p => (sn.lookup p.1).get!
      let conv := fun (e : Expr) => (e.replaceFVars (#[O] ++ from_.toArray) (#[lo] ++ to_.toArray))
      let tAr := conv (← hA.fvarId!.getDecl).type
      let tKr := conv (← hw.fvarId!.getDecl).type
      unless tAr == tA do throwError "CROSSWALK hA: {tAr} vs {tA}"
      unless tKr == tK do throwError "CROSSWALK hw: {tKr} vs {tK}"
      -- NEGATIVE: a wrong depth in the start world (0 -> 1) is rejected
      let tK1 := tKr.replace fun e => if e == mkNatLit 0 || e == toExpr (0:Nat) then some (toExpr (1:Nat)) else none
      if tK1 == tK then throwError "NEG: depth mutation not detected (no literal 0 found)"
      -- NEGATIVE: the unconstrained quiet predicate (hA at the wrong O) is rejected
      if (← hA.fvarId!.getDecl).type == tA then throwError "NEG: unrenamed hA matches"
      -- the premise of start_kwd is `Start ..`
      let hd ← forallTelescope sci.type fun xs _ => do
        let some h := (← byName xs).lookup `h | throwError "no h"
        return (← h.fvarId!.getDecl).type.getAppFn.constName?
      unless hd == some ``Tools.ShippingGen2.Start do throwError "start_kwd premise is not Start"
      logInfo m!"PARAM-FINAL CROSSWALK: start_kwd conjuncts == types of hA / hw of paramRoot_run at O := L.O (Expr ==); premise head Start; depth-mutation and unrenamed controls rejected"

-- fingerprints for the gen5 side (Tests/Gen5/ParamFinalScan.lean prints the same for the gen5 environment)
run_meta do
  for n in [``Tools.ShippingGen2.Laws, ``Tools.ShippingGen2.Start, ``Tools.ShippingChildInvA.AdmCtx,
            ``Tools.ShippingGen4KWalkDepth.KWD, ``Tools.ShippingChildCacheA.JQC] do
    let ci ← getConstInfo n
    let v : UInt64 := match ci with
      | .defnInfo d => d.value.hash
      | _ => 0
    logInfo m!"FINGERPRINT {n}: type {toString ci.type.hash} value {toString v}"

-- canonical forms of the FG binders `hS` and `h` (free variables replaced by constants named after the variables; the gen5 names
-- `parameters`, `b`, `D` of `EntryWitness` are aliases of `θ`, `M'`, `D'`); Tests/Gen5/ParamFinalScan.lean prints the same for
-- the corresponding parts of `EntryWitness`, the hashes must agree
def canonName (n : Name) : Name :=
  if n == `parameters then `θ else if n == `b then `M' else if n == `D then `D' else n

def canon (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun x => do
    if x.isFVar then return .done (mkConst (Name.mkSimple ("fv_" ++ (canonName (← x.fvarId!.getDecl).userName).toString)))
    else return .continue)

run_meta do
  let nci ← getConstInfo ``Tools.ShippingGen4ParamFinal.paramFinal_run
  forallTelescope nci.type fun xs _ => do
    for x in xs do
      let d ← x.fvarId!.getDecl
      if [`hS, `h].contains d.userName then
        let c ← canon d.type
        logInfo m!"CANON {d.userName}: hash {toString c.hash} {c}"

-- NEGATIVE controls for the difference
run_meta do
  let oci ← getConstInfo ``Tools.ShippingGen4ParamFinal.paramFinal_old
  let nci ← getConstInfo ``Tools.ShippingGen4ParamFinal.paramFinal_run
  let (rmS, adS, chS, sameS) ← diffTy nci.type nci.type
  unless rmS == [] && adS == [] && chS == [] && sameS do throwError "NEG1: self-comparison not empty"
  let bad2 ← forallTelescope nci.type fun xs body => do
    let nm ← byName xs
    let some M' := nm.lookup `M' | throwError "no M'"
    let some D' := nm.lookup `D' | throwError "no D'"
    let some θ := nm.lookup `θ | throwError "no θ"
    let sd := mkApp2 (mkConst ``Tools.ShippingGen4Shape.SpecDesign) M' D'
    let hLty ← mkAppM ``Tools.ShippingGen4ParamIface.LegalBinding #[sd, θ]
    withLocalDecl `hL .default hLty fun hL => mkForallFVars (xs.push hL) body
  unless !(← verdict oci.type bad2) do throwError "NEG2: root keeping hL accepted"
  let (rm2, _, _, _) ← diffTy oci.type bad2
  unless rm2 == [`hpos] do throwError "NEG2: expected removed [hpos], got {rm2}"
  let eq0 ← mkEq (mkConst ``Nat) (mkNatLit 0)
  let bad3 ← forallTelescope nci.type fun xs body =>
    withLocalDecl `hx .default eq0 fun hx => mkForallFVars (xs.push hx) body
  unless !(← verdict oci.type bad3) do throwError "NEG3: extra binder accepted"
  let bad4 ← forallTelescope nci.type fun xs _ => mkForallFVars xs (mkConst ``True)
  unless !(← verdict oci.type bad4) do throwError "NEG4: different conclusion accepted"
  unless !(← verdict nci.type oci.type) do throwError "NEG5: reversed pair accepted"
  -- NEG6: the assembly-level run form (free O, hA, hw) is NOT the FG-binder form
  let ar ← getConstInfo ``Tools.ShippingGen4ParamAssembly.paramRoot_run
  unless !(← verdict oci.type ar.type) do throwError "NEG6: free-carrier root accepted"
  let (_, adA, _, _) ← diffTy oci.type ar.type
  unless adA.length == 6 do throwError "NEG6: expected 6 added in the assembly root, got {adA}"
  logInfo m!"PARAM-FINAL NEG: self empty, keep-hL rejected (removed {rm2}), extra binder rejected, other conclusion rejected, reversed rejected, free-carrier root rejected (added {adA})"

-- hypotheses of the final-form run root: Start, MemoFamily, MsgMvK, LamTelescopeN, the run, ExprOK; axioms; closure
run_meta do
  let ci ← getConstInfo ``Tools.ShippingGen4ParamFinal.paramFinal_run
  let hs ← hypHeads ci.type
  let exp : List Name := [``Tools.ShippingGen2.Start, ``Tools.Assume.MemoFamily.MemoFamily, ``Tools.ShippingGen4KWalkDiag.MsgMvK,
    ``Tools.ShippingLegacySem.LamTelescopeN, ``Tools.ShippingEntrySoundness.RunsTo, ``Tools.ShippingGen4ParamBridgeSpecExpr.ExprOK]
  let sorted := fun (l : List Name) => l.toArray.qsort (fun a b => a.toString < b.toString) |>.toList
  unless sorted hs == sorted exp do throwError "paramFinal_run hypotheses {hs}"
  let hsOld ← hypHeads (← getConstInfo ``Tools.ShippingGen4ParamFinal.paramFinal_old).type
  unless hsOld.contains ``Tools.ShippingGen4ParamIface.LegalBinding && hsOld.contains ``Tools.ShippingGen4ParamLayerA.AllPos do
    throwError "NEG: hypothesis detector missed hL / hpos in paramFinal_old: {hsOld}"
  for n in [``Tools.ShippingGen4ParamFinal.start_kwd, ``Tools.ShippingGen4ParamFinal.paramFinal_old,
      ``Tools.ShippingGen4ParamFinal.paramFinal_run] do
    let axs ← collectAxioms n
    let bad := axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a)
    unless bad.isEmpty do throwError "{n}: axioms {bad}"
  let env ← getEnv
  let forbidden : List Name := [`Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND]
  let seen := closure env [``Tools.ShippingGen4ParamFinal.paramFinal_run] {}
  let bad := seen.toList.filter fun m => forbidden.any fun f => f.isPrefixOf m
  unless bad.isEmpty do throwError "closure reaches {bad}"
  logInfo m!"PARAM-FINAL HYPS: paramFinal_run binds exactly Start, MemoFamily, MsgMvK, LamTelescopeN, RunsTo, ExprOK; paramFinal_old detector positive; axioms standard; closure reaches no T1Hyp / T1HypND"

#print axioms Tools.ShippingGen4ParamFinal.start_kwd
#print axioms Tools.ShippingGen4ParamFinal.paramFinal_old
#print axioms Tools.ShippingGen4ParamFinal.paramFinal_run

end Tests.Gen4.ParamFinalCheck
