import Lean
import Tools.ShippingGen5SM1
set_option autoImplicit false
-- Scan of the gen5 final statements for the parametric-assembly premises (Issue sparkle-gen4-param-assembly, PARAM_ASSEMBLY.md §Final).
-- No sorry / axiom / native_decide. Companion of Tests/Gen4/ParamFinalCheck.lean (gen4 branch): the two use the same canonical forms.

open Lean Meta

namespace Tests.Gen5.ParamFinalScan

/-- constants of the type and of the values/types of the definitions reachable from `todo` -/
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

def canonName (n : Name) : Name :=
  if n == `parameters then `θ else if n == `b then `M' else if n == `D then `D' else n

def canon (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun x => do
    if x.isFVar then return .done (mkConst (Name.mkSimple ("fv_" ++ (canonName (← x.fvarId!.getDecl).userName).toString)))
    else return .continue)

def premiseNames : List Name :=
  [`Tools.ShippingGen4ParamIface.LegalBinding, `Tools.ShippingGen4ParamLayerA.AllPos,
   `Tools.Assume.MemoFamily.MemoFamily, `Tools.ShippingGen4KWalkDiag.MsgMvK, `Tools.ShippingLegacySem.LamTelescopeN,
   `Sparkle.IR.Specialize.specializeDesign]

run_meta do
  let env ← getEnv
  -- 1. the final statements G and H: which parametric-assembly premises are reachable from their types
  let roots : List Name := [``Tools.ShippingGenFGLedgerPremises.FGLedgerPremisesStmtG, ``Tools.ShippingGen5SM1.FGLedgerPremisesStmtH]
  for r in roots do
    let seen := closure env [r] {}
    let reached := premiseNames.filter seen.contains
    let present := premiseNames.filter env.contains
    logInfo m!"SCAN {r}: reachable constants {seen.size}; parametric premises reached {reached}; present in this environment {present}"
    unless reached == [] do throwError "{r} reaches {reached}"
  -- 2. the same detector finds a constant that IS reachable (positive control), and a non-reachable one (negative)
  let seenH := closure env [``Tools.ShippingGen5SM1.FGLedgerPremisesStmtH] {}
  for c in [``Tools.ShippingGen2.Start, ``Tools.ShippingGen2.Laws, ``Sparkle.Compiler.Elab.synthesizeCombinationalWithParameters] do
    unless seenH.contains c do throwError "positive control failed: {c} not reached from H"
  -- 3. the binders of H (names and head constants of their types)
  let ci ← getConstInfo ``Tools.ShippingGen5SM1.FGLedgerPremisesStmtH
  let some body := ci.value? | throwError "no value"
  let ty ← whnfD body
  forallTelescope ty fun xs _ => do
    let mut out : List (Name × Name) := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      out := out ++ [(d.userName, d.type.getAppFn.constName?.getD `none)]
    logInfo m!"H BINDERS {out}"

-- 4. EntryWitness: its first conjunct and its parametric disjunct, in the canonical form of ParamFinalCheck
run_meta do
  let ci ← getConstInfo ``Tools.ShippingGen5FG.EntryWitness
  let some v := ci.value? | throwError "no value"
  lambdaTelescope v fun _ body => do
    match body.getAppFn.constName?, body.getAppArgs with
    | some ``And, #[st, rest] =>
      match rest.getAppFn.constName?, rest.getAppArgs with
      | some ``And, #[ro, _] =>
        match ro.getAppFn.constName?, ro.getAppArgs with
        | some ``Or, #[_, par] =>
          let cs ← canon st
          let cp ← canon par
          logInfo m!"CANON Start: hash {toString cs.hash} {cs}"
          logInfo m!"CANON RunsTo(parametric): hash {toString cp.hash} {cp}"
        | _, _ => throwError "EntryWitness: second conjunct is not an Or"
      | _, _ => throwError "EntryWitness: tail is not a conjunction"
    | _, _ => throwError "EntryWitness is not a conjunction"

-- 5. fingerprints of the carrier definitions (compare with Tests/Gen4/ParamFinalCheck.lean)
run_meta do
  for n in [``Tools.ShippingGen2.Laws, ``Tools.ShippingGen2.Start, ``Tools.ShippingChildInvA.AdmCtx,
            `Tools.ShippingGen4KWalkDepth.KWD, ``Tools.ShippingChildCacheA.JQC] do
    match (← getEnv).find? n with
    | none => logInfo m!"FINGERPRINT {n}: not in this environment"
    | some ci =>
      let v : UInt64 := match ci with
        | .defnInfo d => d.value.hash
        | _ => 0
      logInfo m!"FINGERPRINT {n}: type {toString ci.type.hash} value {toString v}"

end Tests.Gen5.ParamFinalScan
