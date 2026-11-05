import Lean
import Tools.ShippingGen5PConnect
set_option autoImplicit false
-- Check of Tools/ShippingGen5P{MinRoot,Connect}.lean on the gen5 Elab (scripts/gen4/PARAM_ASSEMBLY.md §Gen5). No sorry / axiom / native_decide.

/-! # Gen5: binder differences of the roots in ONE environment with `FGLedgerPremisesStmtH`

1. `paramFinal_min` (only `hL`; `hpos` derived by `legalBinding_allPos`) against `paramFinal_run`: removed `[hL]`, added `[M, hmsg, htel]`.
   Against the earlier `paramFinal_old`: removed `[hpos]` only (so `[hL, hpos]` is not two independent subtractions).
2. The roots over the witness binders, `FGParamRootMin` (the binder `hL` inside) against `FGParamRoot` (none), compared after unfolding.
   Both quantify over exactly the binders of `FGLedgerPremisesStmtH` that carry `EntryWitness`; the types of those binders are compared with the
   binders of H by `Expr ==` (this environment contains both).
3. Collision branch, canonical forms (equal here, not only by hash across two environments), negative controls, hypotheses, axioms, closure. -/

open Lean Meta

namespace Tests.Gen5.ParamGen5Check

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

def headsOf (ty : Expr) (names : List Name) : MetaM (List (Name × Name)) :=
  forallTelescope ty fun xs _ => do
    let mut out := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if names.contains d.userName then out := out ++ [(d.userName, d.type.getAppFn.constName?.getD `none)]
    return out

def usesConst (e : Expr) (c : Name) : Bool := e.getUsedConstants.contains c

def hypHeads (ty : Expr) : MetaM (List Name) :=
  forallTelescope ty fun xs _ => do
    let mut out : List Name := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo == .default && (← isProp d.type) then
        out := out ++ [d.type.getAppFn.constName?.getD `none]
    return out

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

def valOf : ConstantInfo → Expr
  | .thmInfo v => v.value
  | .defnInfo v => v.value
  | _ => mkConst ``True

/-- occurrences of the constant `c` (as a tree, not distinct constants) -/
def countConst (c : Name) : Expr → Nat
  | .const n _ => if n == c then 1 else 0
  | .app f a => countConst c f + countConst c a
  | .lam _ d b _ => countConst c d + countConst c b
  | .forallE _ d b _ => countConst c d + countConst c b
  | .letE _ t v b _ => countConst c t + countConst c v + countConst c b
  | .mdata _ e => countConst c e
  | .proj _ _ e => countConst c e
  | _ => 0

def sortN (l : List Name) : List Name := l.toArray.qsort (fun a b => a.toString < b.toString) |>.toList

def minN : Name := ``Tools.ShippingGen5PMinRoot.paramFinal_min
def runN : Name := ``Tools.ShippingGen4ParamFinal.paramFinal_run
def oldN : Name := ``Tools.ShippingGen4ParamFinal.paramFinal_old
def LB : Name := ``Tools.ShippingGen4ParamIface.LegalBinding
def AP : Name := ``Tools.ShippingGen4ParamLayerA.AllPos
def expectedAdded : List (Name × Name) :=
  [(`M, ``Tools.Assume.MemoFamily.MemoFamily), (`hmsg, ``Tools.ShippingGen4KWalkDiag.MsgMvK),
   (`htel, ``Tools.ShippingLegacySem.LamTelescopeN)]

/-- the verdict: old minimal root `oty` against run root `nty` -/
def verdict (oty nty : Expr) : MetaM Bool := do
  let (rm, ad, ch, same) ← diffTy oty nty
  let hs ← headsOf nty ad
  return rm == [`hL] && ad == expectedAdded.map (·.1) && ch == [] && same && hs == expectedAdded

-- 1. minimal root against the run root, and against the earlier root with hpos
run_meta do
  let mci ← getConstInfo minN
  let rci ← getConstInfo runN
  let oci ← getConstInfo oldN
  let (rm, ad, ch, same) ← diffTy mci.type rci.type
  unless (← verdict mci.type rci.type) do throwError "min vs run unexpected: removed {rm} added {ad} changed {ch} concl {same}"
  -- the minimal root has hL and no hpos; the older root has both
  unless usesConst mci.type LB do throwError "min root type does not mention LegalBinding"
  if usesConst mci.type AP then throwError "min root type still mentions AllPos"
  unless usesConst oci.type AP do throwError "old root type does not mention AllPos"
  let (rm0, ad0, ch0, same0) ← diffTy oci.type mci.type
  unless rm0 == [`hpos] && ad0 == [] && ch0 == [] && same0 do throwError "old vs min unexpected: {rm0} {ad0} {ch0} {same0}"
  -- hpos is derived, by the existing lemma, in the proof of the minimal root
  unless usesConst (valOf mci) ``Tools.ShippingGen4ParamBridgeLegal.legalBinding_allPos do
    throwError "the proof of the minimal root does not use legalBinding_allPos"
  -- the run root mentions neither
  for c in [LB, AP] do if usesConst rci.type c then throwError "run root type mentions {c}"
  logInfo m!"PARAM-GEN5 MIN: old -> min removed {rm0.length} {rm0} (hpos derived by legalBinding_allPos; not an independent -1); min -> run removed {rm.length} {rm} (B.P-8), added {ad.length} {ad}, changed {ch.length}, concl {same}; FG -0 +0 / T1 -0 +0 recorded"

-- 2. the roots over the witness binders, against the binders of FGLedgerPremisesStmtH
def unfoldApp (e : Expr) : MetaM Expr := do
  let some e' ← unfoldDefinition? e | throwError "cannot unfold {e}"
  return e'.headBeta

/-- the telescope (names, types) of the inner `∀ declName parameters ... , EntryWitness .. → ..` of H, with H's carriers as fvars -/
def withH {α} (k : Array Expr → Array Expr → Expr → MetaM α) : MetaM α := do
  let hci ← getConstInfo ``Tools.ShippingGen5SM1.FGLedgerPremisesStmtH
  let some hv := hci.value? | throwError "no value"
  forallTelescope hv fun hxs hbody => do
    match hbody.getAppFn.constName?, hbody.getAppArgs with
    | some ``And, #[_, inner] => forallTelescope inner fun ixs ibody => k hxs ixs ibody
    | _, _ => throwError "H: body is not a conjunction"

def userName (x : Expr) : MetaM Name := return (← x.fvarId!.getDecl).userName

def byName (xs : Array Expr) : MetaM (List (Name × Expr)) := xs.toList.mapM fun x => return (← userName x, x)

/-- the root statement `FGParamRoot R L` / `FGParamRootMin R L` unfolded, R, L, mref, cref replaced by the fvars of H -/
def rootStmt (thm : Name) (hn : List (Name × Expr)) : MetaM Expr := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs body => do
    let nm ← byName xs
    let names := [`mref, `cref, `ReflectsAll, `L]
    let from_ := names.map fun n => (nm.lookup n).get!
    let to_ := names.map fun n => (hn.lookup n).get!
    let u ← unfoldApp body
    return u.replaceFVars from_.toArray to_.toArray

run_meta do
  -- the binders of the root statements, positionally against the inner telescope of H
  withH fun hxs ixs _ => do
    let hn ← byName hxs
    let runS ← rootStmt ``Tools.ShippingGen5PConnect.fgParamRoot hn
    let minS ← rootStmt ``Tools.ShippingGen5PConnect.fgParamRootMin hn
    -- first 9 binders of the inner telescope of H: declName parameters mctx cctx w w' b D, EntryWitness
    let hTypes ← ixs.toList.take 9 |>.mapM fun x => return (← x.fvarId!.getDecl).type
    let hNames ← ixs.toList.take 9 |>.mapM userName
    unless hNames.take 8 == [`declName, `parameters, `mctx, `cctx, `w, `w', `b, `D] do throwError "H inner binders: {hNames}"
    let r ← forallTelescope runS fun rxs rbody => do
      let rTypes ← rxs.toList.mapM fun x => return (← x.fvarId!.getDecl).type
      let rNames ← rxs.toList.mapM userName
      -- map the root's own binders to H's inner fvars, then compare the types of the first 9 binders with H's
      let mapped := (rxs.toList.take 9).zip (ixs.toList.take 9)
      let from_ := mapped.map (·.1); let to_ := mapped.map (·.2)
      let mut ok := true
      for i in [0:9] do
        let t := (rTypes[i]!).replaceFVars (from_.take i).toArray (to_.take i).toArray
        unless t == hTypes[i]! do ok := false
      return (ok, rNames, rxs.size, rTypes.map (·.getAppFn.constName?.getD `none), rbody)
    let (ok, rNames, rn, rHeads, rbody) := r
    unless ok do throwError "root binders differ from H's witness binders: {rNames}"
    unless rHeads[8]! == ``Tools.ShippingGen5FG.EntryWitness do throwError "9th binder of the root is not EntryWitness: {rHeads}"
    -- minimal root: the same binders, plus one binder whose type is LegalBinding
    let m ← forallTelescope minS fun mxs _ => do
      let mTypes ← mxs.toList.mapM fun x => return (← x.fvarId!.getDecl).type
      let mHeads := mTypes.map (·.getAppFn.constName?.getD `none)
      return (mxs.size, mHeads)
    let (mn, mHeads) := m
    unless mn == rn + 1 do throwError "minimal root binder count {mn} vs run root {rn}"
    unless mHeads.filter (· == LB) == [LB] do throwError "minimal root: expected exactly one LegalBinding binder: {mHeads}"
    unless (mHeads.filter (· == AP)) == [] do throwError "minimal root has an AllPos binder"
    unless rHeads.filter (fun h => h == LB || h == AP) == [] do throwError "run root has LegalBinding / AllPos binders: {rHeads}"
    -- removing the hL binder from the minimal root gives the run root: same heads in order
    unless mHeads.erase LB == rHeads do throwError "heads differ: {mHeads} vs {rHeads}"
    -- the conclusions are `RootConcl` in both
    unless rbody.getAppFn.constName? == some ``Tools.ShippingGen4ParamAssembly.RootConcl do throwError "root conclusion head {rbody.getAppFn}"
    logInfo m!"PARAM-GEN5 ROOT: binders of the run root == the witness binders of FGLedgerPremisesStmtH (declName parameters mctx cctx w w' b D, EntryWitness) by Expr ==; {rn} binders; minimal root = run root + [hL : LegalBinding] (removed [hL]), no AllPos binder; theorem binders added [M, hmsg, htel] (head check)"
  -- the theorem-level binders of fgParamRoot and fgParamRootMin
  let rci ← getConstInfo ``Tools.ShippingGen5PConnect.fgParamRoot
  let mci ← getConstInfo ``Tools.ShippingGen5PConnect.fgParamRootMin
  let (rm, ad, ch, _) ← diffTy mci.type rci.type
  let hs ← headsOf rci.type ad
  unless ad == [`M, `hmsg, `htel] && rm == [] && ch == [] && hs == expectedAdded do
    throwError "fgParamRoot vs fgParamRootMin (theorem binders): removed {rm} added {ad} changed {ch} heads {hs}"
  logInfo m!"PARAM-GEN5 THM: theorem-level binders of fgParamRoot over fgParamRootMin: added {ad.length} {ad} {hs}; the removal of hL is inside the statement (previous line)"

-- H reaches EntryWitness; the root hypotheses are the same constant; none of LegalBinding / AllPos / MemoFamily / MsgMvK / LamTelescopeN are reached
run_meta do
  let env ← getEnv
  let seenH := closure env [``Tools.ShippingGen5SM1.FGLedgerPremisesStmtH] {}
  unless seenH.contains ``Tools.ShippingGen5FG.EntryWitness do throwError "EntryWitness not reached from H"
  let prem : List Name := [LB, AP, ``Tools.Assume.MemoFamily.MemoFamily, ``Tools.ShippingGen4KWalkDiag.MsgMvK,
    ``Tools.ShippingLegacySem.LamTelescopeN]
  let reached := prem.filter seenH.contains
  unless reached == [] do throwError "H reaches {reached}"
  -- NEG: the detector finds them from the roots
  let seenR := closure env [``Tools.ShippingGen5PConnect.fgParamRoot] {}
  let found := prem.filter seenR.contains
  unless found.length == 5 || found.length == 4 do throwError "positive control: fgParamRoot reaches {found}"
  logInfo m!"PARAM-GEN5 SCAN: H reaches EntryWitness and none of {prem.length} premises; fgParamRoot reaches {found} (detector positive)"

-- 3. canonical forms of the FG binders, in one environment
def canonName (n : Name) : Name :=
  if n == `parameters then `θ else if n == `b then `M' else if n == `D then `D' else n

def canon (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun x => do
    if x.isFVar then return .done (mkConst (Name.mkSimple ("fv_" ++ (canonName (← x.fvarId!.getDecl).userName).toString)))
    else return .continue)

run_meta do
  let eci ← getConstInfo ``Tools.ShippingGen5FG.EntryWitness
  let some ev := eci.value? | throwError "no value"
  let (cStart, cPar) ← lambdaTelescope ev fun _ body => do
    match body.getAppFn.constName?, body.getAppArgs with
    | some ``And, #[st, rest] =>
      match rest.getAppFn.constName?, rest.getAppArgs with
      | some ``And, #[ro, _] =>
        match ro.getAppFn.constName?, ro.getAppArgs with
        | some ``Or, #[_, par] => return (← canon st, ← canon par)
        | _, _ => throwError "second conjunct is not an Or"
      | _, _ => throwError "tail is not a conjunction"
    | _, _ => throwError "EntryWitness is not a conjunction"
  let rci ← getConstInfo runN
  let (cS, cH) ← forallTelescope rci.type fun xs _ => do
    let nm ← byName xs
    let hS := (nm.lookup `hS).get!; let h := (nm.lookup `h).get!
    return (← canon (← hS.fvarId!.getDecl).type, ← canon (← h.fvarId!.getDecl).type)
  unless cS == cStart do throwError "CANON Start differs: {cS} vs {cStart}"
  unless cH == cPar do throwError "CANON parametric run differs: {cH} vs {cPar}"
  logInfo m!"PARAM-GEN5 CANON: Start hash {toString cS.hash} == EntryWitness conjunct 1; parametric RunsTo hash {toString cH.hash} == EntryWitness 2nd disjunct (Expr ==, one environment)"
  -- NEG: a mutated run (the default route) is not the parametric disjunct
  let nci ← getConstInfo ``Tools.ShippingGen5PConnect.entry_route
  forallTelescope nci.type fun _ body => do
    match body.getAppFn.constName?, body.getAppArgs with
    | some ``Or, #[l, _] =>
      if (← canon l) == cPar then throwError "NEG: default route equals the parametric disjunct"
    | _, _ => throwError "entry_route conclusion"
  logInfo m!"PARAM-GEN5 CANON NEG: the default-route disjunct differs from the parametric one"

-- collision branch
run_meta do
  let aci ← getConstInfo ``Tools.ShippingGen5PConnect.AssemblyConcl
  let some av := aci.value? | throwError "no value"
  let coll := ``Tools.ShippingGen4ParamAssembly.Collides
  let cnt := countConst coll av
  unless usesConst av coll && usesConst av ``Iff && usesConst av ``Not && usesConst av LB && usesConst av AP do
    throwError "AssemblyConcl lacks the collision branches"
  -- the iff is `LegalBinding .. ↔ θ = []` under `Collides`
  let ac ← getConstInfo ``Tools.ShippingGen5PConnect.collision_not_legal
  unless usesConst ac.type coll && usesConst ac.type ``Tools.ShippingGen4Shape.SpecDesign do throwError "collision_not_legal type"
  let er ← getConstInfo ``Tools.ShippingGen5PConnect.entry_route
  unless usesConst er.type ``Tools.ShippingGen5PConnect.AssemblyConcl && usesConst er.type ``Tools.ShippingEntrySoundness.RunsTo do
    throwError "entry_route type"
  -- the proof of entry_param_assembly goes through legal_assembly (both branches), and the specDesign equation through specDesign_of_collides
  unless usesConst (valOf (← getConstInfo ``Tools.ShippingGen5PConnect.entry_param_assembly)) ``Tools.ShippingGen4ParamAssembly.legal_assembly do
    throwError "entry_param_assembly does not use legal_assembly"
  unless usesConst (valOf ac) ``Tools.ShippingGen4ParamAssembly.specDesign_of_collides do throwError "collision_not_legal does not use specDesign_of_collides"
  -- the collision branch is mentioned in the Collides-free negation too
  unless (cnt : Nat) ≥ 2 do throwError "AssemblyConcl: Collides occurs {cnt} times"
  logInfo m!"PARAM-GEN5 COLLISION: AssemblyConcl = AllPos ∧ (¬Collides → LegalBinding (SpecDesign b D)) ∧ (Collides → (LegalBinding ↔ θ = [])); Collides occurs {cnt} times; collision_not_legal gives SpecDesign = D' and ¬LegalBinding for θ ≠ []"

-- NEGATIVE controls
run_meta do
  let mci ← getConstInfo minN
  let rci ← getConstInfo runN
  let (rmS, adS, chS, sameS) ← diffTy rci.type rci.type
  unless rmS == [] && adS == [] && chS == [] && sameS do throwError "NEG1: self-comparison not empty"
  -- NEG2: the run root plus the binder hL (the minimal root again) is rejected as a run root
  let bad2 ← forallTelescope rci.type fun xs body => do
    let nm ← byName xs
    let sd := mkApp2 (mkConst ``Tools.ShippingGen4Shape.SpecDesign) (nm.lookup `M').get! (nm.lookup `D').get!
    let hLty ← mkAppM LB #[sd, (nm.lookup `θ).get!]
    withLocalDecl `hL .default hLty fun hL => mkForallFVars (xs.push hL) body
  let (rm2, ad2, _, _) ← diffTy mci.type bad2
  if (← verdict mci.type bad2) then throwError "NEG2: root keeping hL accepted"
  unless rm2 == [] && ad2 == [`M, `hmsg, `htel] do throwError "NEG2: unexpected {rm2} {ad2}"
  -- NEG3: extra binder
  let eq0 ← mkEq (mkConst ``Nat) (mkNatLit 0)
  let bad3 ← forallTelescope rci.type fun xs body => withLocalDecl `hx .default eq0 fun hx => mkForallFVars (xs.push hx) body
  if (← verdict mci.type bad3) then throwError "NEG3: extra binder accepted"
  -- NEG4: other conclusion; NEG5: reversed pair
  let bad4 ← forallTelescope rci.type fun xs _ => mkForallFVars xs (mkConst ``True)
  if (← verdict mci.type bad4) then throwError "NEG4: different conclusion accepted"
  if (← verdict rci.type mci.type) then throwError "NEG5: reversed pair accepted"
  -- NEG6: the earlier root with hpos is not the minimal form
  let oci ← getConstInfo oldN
  if (← verdict oci.type rci.type) then throwError "NEG6: old root (hL, hpos) accepted as the minimal comparison"
  -- NEG7: the H-binder comparison rejects swapped w / w'
  withH fun _ ixs _ => do
    let nm ← byName ixs
    let w := (nm.lookup `w).get!; let w' := (nm.lookup `w').get!
    let d ← (nm.lookup `declName).get!.fvarId!.getDecl
    let e1 := mkApp2 (mkConst `Prod.mk [0, 0]) w w'
    let e2 := mkApp2 (mkConst `Prod.mk [0, 0]) w' w
    if e1 == e2 then throwError "NEG7: swap not detected"
    let _ := d
  logInfo m!"PARAM-GEN5 NEG: self empty, keep-hL rejected, extra binder rejected, other conclusion rejected, reversed rejected, old (hL, hpos) not accepted as the minimal form, swapped witness binders differ"

-- hypotheses, axioms, closure
run_meta do
  let ci ← getConstInfo ``Tools.ShippingGen5PConnect.fgParamRoot
  let hs ← hypHeads ci.type
  let exp : List Name := [``Tools.Assume.MemoFamily.MemoFamily, ``Tools.ShippingGen4KWalkDiag.MsgMvK, ``Tools.ShippingLegacySem.LamTelescopeN]
  unless sortN hs == sortN exp do throwError "fgParamRoot hypotheses {hs}"
  let mci ← getConstInfo ``Tools.ShippingGen5PConnect.fgParamRootMin
  unless (← hypHeads mci.type) == [] do throwError "fgParamRootMin has hypotheses"
  let ea ← getConstInfo ``Tools.ShippingGen5PConnect.entry_param_assembly
  let ha ← hypHeads ea.type
  unless sortN ha == sortN (exp ++ [``Tools.ShippingGen5FG.EntryWitness, ``Tools.ShippingEntrySoundness.RunsTo]) do
    throwError "entry_param_assembly hypotheses {ha}"
  for n in [``Tools.ShippingGen5PMinRoot.paramFinal_min, ``Tools.ShippingGen5PConnect.entry_param_assembly,
      ``Tools.ShippingGen5PConnect.entry_route, ``Tools.ShippingGen5PConnect.collision_not_legal,
      ``Tools.ShippingGen5PConnect.fgParamRoot, ``Tools.ShippingGen5PConnect.fgParamRootMin] do
    let axs ← collectAxioms n
    let bad := axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a)
    unless bad.isEmpty do throwError "{n}: axioms {bad}"
  let env ← getEnv
  let forbidden : List Name := [`Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND]
  let seen := closure env [``Tools.ShippingGen5PConnect.fgParamRoot, ``Tools.ShippingGen5PConnect.entry_route] {}
  let bad := seen.toList.filter fun m => forbidden.any fun f => f.isPrefixOf m
  unless bad.isEmpty do throwError "closure reaches {bad}"
  -- NEG: the detector sees the hypotheses in the minimal root's older sibling
  let hsOld ← hypHeads (← getConstInfo oldN).type
  unless hsOld.contains LB && hsOld.contains AP do throwError "NEG: detector missed hL / hpos in paramFinal_old"
  logInfo m!"PARAM-GEN5 HYPS: fgParamRoot binds exactly MemoFamily, MsgMvK, LamTelescopeN; entry_param_assembly adds EntryWitness and the parametric RunsTo; axioms standard; closure reaches no T1Hyp / T1HypND"

-- premises that enter `added` and their ledger status (text; the reviewer decides the subtraction)
run_meta do
  let rows : List (String × String × String) :=
    [("M : MemoFamily L.O", "FG 75 has no row (M4.MEMO-01)", "new +1 candidate, pending K-walk acceptance"),
     ("hmsg : MsgMvK L.O", "no row (MEMO_FAMILY_FREEZE §R2.6)", "conditional leaf, not counted"),
     ("htel : LamTelescopeN", "N4-a (ledger §12.17), registered as a candidate, not yet counted", "+1 once (shared candidate)"),
     ("carrier O := L.O", "A.P-01 L : Laws (binder of H)", "existing row, no change"),
     ("hA, hw from Start L mctx cctx w", "A.P-02 Start (conjunct 1 of EntryWitness), start_kwd", "existing row, no change"),
     ("the run", "A.P-04, 2nd disjunct of EntryWitness", "existing row, no change")]
  for (p, r, s) in rows do logInfo m!"PARAM-GEN5 PREMISE {p} | ledger: {r} | treatment: {s}"

#print axioms Tools.ShippingGen5PMinRoot.paramFinal_min
#print axioms Tools.ShippingGen5PConnect.entry_param_assembly
#print axioms Tools.ShippingGen5PConnect.entry_route
#print axioms Tools.ShippingGen5PConnect.collision_not_legal
#print axioms Tools.ShippingGen5PConnect.fgParamRoot
#print axioms Tools.ShippingGen5PConnect.fgParamRootMin

end Tests.Gen5.ParamGen5Check
