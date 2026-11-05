import Lean
import Tools.ShippingGen4ParamAssembly
set_option autoImplicit false
-- Check of Tools/ShippingGen4ParamAssembly.lean (scripts/gen4/PARAM_ASSEMBLY.md). No sorry / axiom / native_decide.

/-! # Binder difference of the two roots, by structural `Expr ==`

`paramRoot_old` carries `hL : LegalBinding (SpecDesign M' D') θ` (B.P-8, ParamIface:91) and `hpos : AllPos θ` (B.P-1,
ParamLayerA:43) as binders; `paramRoot_run` does not. One walk of the two telescopes (as `Tests/Gen4/FThetaTeleCheck.lean`): each
old binder is instantiated by the same-named new fvar (types compared with `==`), a binder absent from the new root gets a fresh
local. Expected: removed `[hL, hpos]`, added `[O, M, hmsg, htel, hA, hw]`, changed `[]`, conclusions `==`. The added binders are
classified by the head constant of their type: `htel : LamTelescopeN` is the shared +1 candidate N4-a (ledger §12.17, counted once in
the final FG); `M : MemoFamily` (rev3) and `hmsg : MsgMvK` are the F-kids assumptions the reviewer allowed (MsgMvK is a conditional
leaf, not TRUSTED); `O : RefLawsAOps`, `hA : AdmCtx`, `hw : KWD` are the carrier and the Start rows (A.P-02 / C.RR-1) the run form
needs. NEGATIVE controls: self-comparison is empty; a root that keeps `hL` fails the verdict; a root with an extra non-row binder
fails the verdict; a root with a different conclusion fails the verdict. -/

open Lean Meta

namespace Tests.Gen4.ParamAssemblyCheck

abbrev Res := List Name × List Name × List Name × Bool

partial def walkOld (ys : Array (Name × BinderInfo × Expr × Expr)) :
    Expr → List Name → List Name → (Expr → List Name → List Name → MetaM Res) → MetaM Res
  | .forallE n d b bi, rm, ch, k =>
    match ys.find? (·.1 == n) with
    | some (_, bi', fv, ty') =>
      walkOld ys (b.instantiate1 fv) rm (if bi == bi' && d == ty' then ch else ch ++ [n]) k
    | none => withLocalDecl n bi d fun x => walkOld ys (b.instantiate1 x) (rm ++ [n]) ch k
  | body, rm, ch, k => k body rm ch

def diffTy (oty nty : Expr) : MetaM Res := do
  let oNames ← forallTelescope oty fun xs _ => xs.toList.mapM fun x => return (← x.fvarId!.getDecl).userName
  forallTelescope nty fun xs nbody => do
    let mut ys : Array (Name × BinderInfo × Expr × Expr) := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      ys := ys.push (d.userName, d.binderInfo, x, d.type)
    walkOld ys oty [] [] fun obody rm ch => do
      let added := (ys.toList.filter fun y => !oNames.contains y.1).map (·.1)
      return (rm, added, ch, obody == nbody)

def diff (old new : Name) : MetaM Res := do
  diffTy (← getConstInfo old).type (← getConstInfo new).type

/-- the head constant of the type of each added binder -/
def headsOf (ty : Expr) (names : List Name) : MetaM (List (Name × Name)) :=
  forallTelescope ty fun xs _ => do
    let mut out := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if names.contains d.userName then out := out ++ [(d.userName, d.type.getAppFn.constName?.getD `none)]
    return out


def expectedRemoved : List Name := [`hL, `hpos]
def expectedAdded : List (Name × Name) :=
  [(`O, ``Tools.ShippingChildInvA.RefLawsAOps), (`M, ``Tools.Assume.MemoFamily.MemoFamily),
   (`hmsg, ``Tools.ShippingGen4KWalkDiag.MsgMvK), (`htel, ``Tools.ShippingLegacySem.LamTelescopeN),
   (`hA, ``Tools.ShippingChildInvA.AdmCtx), (`hw, ``Tools.ShippingGen4KWalkDepth.KWD)]

/-- the verdict on a pair of root TYPES: removed / added / changed / conclusion, and the heads of the added binders -/
def verdict (oty nty : Expr) : MetaM Bool := do
  let (rm, ad, ch, same) ← diffTy oty nty
  let hs ← headsOf nty ad
  return rm == expectedRemoved && ad == expectedAdded.map (·.1) && ch == [] && same && hs == expectedAdded

def usesConst (e : Expr) (c : Name) : Bool := e.getUsedConstants.contains c

run_meta do
  let old := ``Tools.ShippingGen4ParamAssembly.paramRoot_old
  let new := ``Tools.ShippingGen4ParamAssembly.paramRoot_run
  let oci ← getConstInfo old
  let nci ← getConstInfo new
  let (rm, ad, ch, same) ← diff old new
  let hs ← headsOf nci.type ad
  unless (← verdict oci.type nci.type) do
    throwError "paramRoot_run vs paramRoot_old unexpected: removed {rm} added {ad} changed {ch} same {same} heads {hs}"
  -- B.P-8 / B.P-1 are in the old type, not in the new type (the proof may use them)
  for c in [``Tools.ShippingGen4ParamIface.LegalBinding, ``Tools.ShippingGen4ParamLayerA.AllPos] do
    unless usesConst oci.type c do throwError "old root type does not mention {c}"
    if usesConst nci.type c then throwError "new root type still mentions {c}"
  -- the removed binders are exactly the rows: hL : LegalBinding .., hpos : AllPos ..
  let rows ← forallTelescope oci.type fun xs _ => do
    let mut out : List (Name × Name) := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if expectedRemoved.contains d.userName then out := out ++ [(d.userName, d.type.getAppFn.constName?.getD `none)]
    return out
  unless rows == [(`hL, ``Tools.ShippingGen4ParamIface.LegalBinding), (`hpos, ``Tools.ShippingGen4ParamLayerA.AllPos)] do
    throwError "removed rows unexpected: {rows}"
  -- counts: shared +1 = binders whose head is LamTelescopeN
  let plus1 := ad.filter fun n => n == `htel
  let existing := ad.filter fun n => [`O, `hA, `hw].contains n
  let allowed := ad.filter fun n => [`M, `hmsg].contains n
  logInfo m!"PARAM-ASSEMBLY COUNTS: removed {rm.length} {rm} (B.P-8, B.P-1), added {ad.length} {ad} (shared +1 {plus1} / Start rows and carrier {existing} / F-kids assumptions {allowed}), changed {ch.length}, concl {same}, FG -0 +0 / T1 -0 +0 recorded"
  -- NEGATIVE controls
  let (rmS, adS, chS, sameS) ← diffTy nci.type nci.type
  unless rmS == [] && adS == [] && chS == [] && sameS do throwError "NEG1: self-comparison not empty"
  -- NEG2: a run-form root that keeps hL
  let bad2 ← forallTelescope nci.type fun xs body => do
    let mut byName : List (Name × Expr) := []
    for x in xs do byName := byName ++ [((← x.fvarId!.getDecl).userName, x)]
    let some M' := byName.lookup `M' | throwError "no M'"
    let some D' := byName.lookup `D' | throwError "no D'"
    let some θ := byName.lookup `θ | throwError "no θ"
    let sd := mkApp2 (mkConst ``Tools.ShippingGen4Shape.SpecDesign) M' D'
    let hLty ← mkAppM ``Tools.ShippingGen4ParamIface.LegalBinding #[sd, θ]
    withLocalDecl `hL .default hLty fun hL => mkForallFVars (xs.push hL) body
  unless !(← verdict oci.type bad2) do throwError "NEG2: root keeping hL accepted"
  let (rm2, _, _, _) ← diffTy oci.type bad2
  unless rm2 == [`hpos] do throwError "NEG2: expected removed [hpos], got {rm2}"
  -- NEG3: an extra non-row binder
  let bad3 ← forallTelescope nci.type fun xs body => do
    let nat := mkConst ``Nat
    withLocalDecl `hx .default (← mkEq nat (mkNatLit 0)) fun hx => mkForallFVars (xs.push hx) body
  unless !(← verdict oci.type bad3) do throwError "NEG3: extra binder accepted"
  -- NEG4: a different conclusion
  let bad4 ← forallTelescope nci.type fun xs _ => mkForallFVars xs (mkConst ``True)
  unless !(← verdict oci.type bad4) do throwError "NEG4: different conclusion accepted"
  -- NEG5: swapped roles (new compared to old as `old`) is not the expected difference
  unless !(← verdict nci.type oci.type) do throwError "NEG5: reversed pair accepted"
  logInfo m!"PARAM-ASSEMBLY NEG: self empty, keep-hL rejected (removed {rm2}), extra binder rejected, other conclusion rejected, reversed rejected"

/-! ## The assembly theorems: hypotheses, axioms, closure -/

/-- the head constants of the explicit Prop binders (hypotheses) of a theorem type, `RunsTo` runs set aside -/
def hypHeads (ty : Expr) : MetaM (List Name) :=
  forallTelescope ty fun xs _ => do
    let mut out : List Name := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo == .default && (← isProp d.type) then
        out := out ++ [d.type.getAppFn.constName?.getD `none]
    return out

run_meta do
  let exp : List (Name × List Name) :=
    [(``Tools.ShippingGen4ParamAssembly.run_facts,
        [``Tools.ShippingGen4KWalkDepth.KWD, ``Tools.ShippingEntrySoundness.RunsTo]),
     (``Tools.ShippingGen4ParamAssembly.legal_assembly,
        [``Tools.ShippingGen4KWalkDepth.KWD, ``Tools.ShippingEntrySoundness.RunsTo]),
     (``Tools.ShippingGen4ParamAssembly.paramRoot_run,
        [``Tools.ShippingGen4KWalkDepth.KWD, ``Tools.ShippingEntrySoundness.RunsTo,
         ``Tools.ShippingGen4ParamBridgeSpecExpr.ExprOK])]
  let fixed : List Name := [``Tools.Assume.MemoFamily.MemoFamily, ``Tools.ShippingGen4KWalkDiag.MsgMvK,
    ``Tools.ShippingLegacySem.LamTelescopeN, ``Tools.ShippingChildInvA.AdmCtx]
  for (n, extra) in exp do
    let ci ← getConstInfo n
    let hs ← hypHeads ci.type
    -- Prop binders = MemoFamily, MsgMvK, LamTelescopeN, AdmCtx (fixed) + the run facts; nothing else
    let sorted := fun (l : List Name) => l.toArray.qsort (fun a b => a.toString < b.toString) |>.toList
    unless sorted hs == sorted (fixed ++ extra) do throwError "{n}: hypotheses {hs}"
    for c in [``Tools.ShippingGen4ParamIface.LegalBinding, ``Tools.ShippingGen4ParamLayerA.AllPos] do
      if n == ``Tools.ShippingGen4ParamAssembly.paramRoot_run && usesConst ci.type c then throwError "{n}: type mentions {c}"
  -- NEGATIVE: the detector sees the standard rows in paramRoot_old
  let hsOld ← hypHeads (← getConstInfo ``Tools.ShippingGen4ParamAssembly.paramRoot_old).type
  unless hsOld.contains ``Tools.ShippingGen4ParamIface.LegalBinding && hsOld.contains ``Tools.ShippingGen4ParamLayerA.AllPos do
    throwError "NEG: hypothesis detector missed hL / hpos in paramRoot_old: {hsOld}"
  -- axioms
  for n in [``Tools.ShippingGen4ParamAssembly.legal_of_facts, ``Tools.ShippingGen4ParamAssembly.run_facts,
      ``Tools.ShippingGen4ParamAssembly.legal_assembly, ``Tools.ShippingGen4ParamAssembly.paramRoot_old,
      ``Tools.ShippingGen4ParamAssembly.paramRoot_run] do
    let axs ← collectAxioms n
    let bad := axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a)
    unless bad.isEmpty do throwError "{n}: axioms {bad}"
  logInfo m!"PARAM-ASSEMBLY HYPS: run_facts / legal_assembly / paramRoot_run bind exactly MemoFamily, MsgMvK, LamTelescopeN, AdmCtx, KWD, RunsTo (paramRoot_run also ExprOK); paramRoot_old detector positive; axioms standard"

/-- Transitive constant closure (types and values of theorems and definitions). -/
partial def closure (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest seen else
    let seen := seen.insert n
    match env.find? n with
    | none => closure env rest seen
    | some ci =>
      let body : List Name := match ci with
        | .thmInfo v => v.value.getUsedConstants.toList
        | .defnInfo v => v.value.getUsedConstants.toList
        | _ => []
      closure env (ci.type.getUsedConstants.toList ++ body ++ rest) seen

run_meta do
  let env ← getEnv
  let forbidden : List Name := [`Tools.ShippingGen2.Laws, `Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND]
  for n in [``Tools.ShippingGen4ParamAssembly.legal_assembly, ``Tools.ShippingGen4ParamAssembly.paramRoot_run] do
    let seen := closure env [n] {}
    let bad := seen.toList.filter fun m => forbidden.any fun f => f.isPrefixOf m
    unless bad.isEmpty do throwError "{n}: closure reaches {bad}"
  -- positive control: the detector sees `Laws` from a declaration that mentions it
  let seenL := closure env [``Tools.ShippingGen2.T1Hyp] {}
  unless seenL.contains `Tools.ShippingGen2.T1Hyp do throwError "closure control failed"
  logInfo m!"PARAM-ASSEMBLY CLOSURE: legal_assembly and paramRoot_run reach no Laws / T1Hyp / T1HypND constant"

#print axioms Tools.ShippingGen4ParamAssembly.legal_of_facts
#print axioms Tools.ShippingGen4ParamAssembly.run_facts
#print axioms Tools.ShippingGen4ParamAssembly.legal_assembly
#print axioms Tools.ShippingGen4ParamAssembly.paramRoot_old
#print axioms Tools.ShippingGen4ParamAssembly.paramRoot_run

end Tests.Gen4.ParamAssemblyCheck
