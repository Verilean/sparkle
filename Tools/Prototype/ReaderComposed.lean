import Tools.Prototype.ReaderClosed
import Tools.Prototype.StartDomOk2
import Tools.Prototype.NormRangeLetOk

/-! # Unit LCC: ONE composed corollary on the SAME `p`/`en`/`st`/`v`, without `ShapeInOk`

BUILT (unit GAUD): a1 exit 0 (checkConclusion now runs Meta.check on the compared and mutation terms, asserts no mvars / stray fvars).
BUILT (unit LCC): b1 exit 1 (missing opens), b2 exit 1 (binder audit list lacked the second Eq for hpe), b3 exit 0. No sorry/axiom/native_decide.

`machineShapeN_typed_all` composes, on the single successful run `machineShapeN … = some (some sp)` (one `machineShapeN_steps`
unpacking, hence ONE fuel `n` and the same `h0..h3`):
* the SUCCESS-RUN start domain `startDom_succ_w` (premise `EqvLetOk0`) in place of `StartDomOk`/`ShapeInOk.startDom`;
* `normRange_of` (premises `RawNodeRange`, `NormNodeRange`, plus `Inst1Range`) in place of `NormRange`;
* `shapeMid_ok` (premises `RootFloatRange`, `ZeroLitAgrees`, `hpe`) for the derived `rootLets`/`root`/`runBody` fields;
* LCQ2 `shapeStart_clo`/`rootLets_clo`/`shapeBody_clo` for `NoLetBvar` (DERIVED, not an antecedent);
* `typed_letsAlias` / `letsClose_of_data` for the typed conclusion.
No `ShapeInOk`, `StartDomOk`, `NormRange`, `NoLetBvar` anywhere in the statement (throwing check below).
Remaining PREMISES (not proved): RootFloatRange, LiftRange, Inst1Range, SigTyRange, ZeroLitAgrees, RawNodeRange, NormNodeRange,
EqvLetOk0, hpe; `d.ok`/`hbody` stay the generation-path checks. About the prototype wrapper `machineShapeN`, NOT the shipped
`machineShape?` (`machNorm = execNorm`, `TwinCoverAt` OPEN). -/
namespace Tools.Prototype.ReaderComposed
open Lean Sparkle.Compiler.Elab Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv
open Tools.ShippingReaderFuelShapeR5 Tools.ShippingReaderLenOk Tools.ShippingCloInv
open Tools.Prototype.ReaderExec Tools.Prototype.ReaderTyped Tools.Prototype.PreprocLetOk
open Tools.Prototype.StartDomOk Tools.Prototype.NormRangeLetOk Tools.Prototype.ReaderClosed
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineEntry
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMixedSourceBridge

theorem machineShapeN_typed_all {senv : StructEnv}
    (hroot : RootFloatRange) (hlift : LiftRange) (hinst1 : Inst1Range) (hsig : SigTyRange senv)
    (hz : ZeroLitAgrees) (hraw : RawNodeRange senv) (hnode : NormNodeRange senv) (hE : EqvLetOk0)
    {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool} {sp : MachineShape}
    (hpe : ∀ p : ShapePre, shapePre sm ps ci senv = some p → LetOk 0 p.e = true)
    (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNorm senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      (∀ (d : MachineData), d.shape = sp → d.ok = true →
        d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
          (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed →
        d.letsAliasOk = true ∧
        ∀ {declName : Name} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
          (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State),
          Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape) := by
  obtain ⟨n, p, en, st0, env, st1, st, v, hp, hen, h0, h1, h2, h3⟩ := machineShapeN_steps h
  have hex : execNorm senv p.e = some en := (execNorm_iff senv).mpr ⟨n, hen⟩
  have hnorm : NormRange senv := normRange_of hraw hnode hinst1
  obtain ⟨hrl, hrt, hrb⟩ := shapeMid_ok hroot hz senv p en (hnorm _ _ (hpe p hp) hex)
  have hbundle := Tools.ShippingLetsReaderInv.bundleIotaRange
  have r0 : RdOk st0 := shapeStart_ok (n := n) (startDom_succ_w hE h0 h1 h2 h3) h0
  have r1 := rootLets_ok hroot hlift hinst1 hsig hbundle hrl r0 h1 (fun v hv => by cases hv)
  have r2 := shapeBody_ok hroot hlift hinst1 hsig hbundle r1.1 r1.2 hrt hrb
    (shapeMid_wrap_ok senv p en hrt) h2
  have c0 : CloSt st0 := shapeStart_clo h0
  have c1 := rootLets_clo c0 (fun v hv => by cases hv) h1
  have c2 : CloSt st := shapeBody_clo c1.1 c1.2 h2
  have hnb : NoLetBvar st.lets := letsClo_noLetBvar c2.1
  have hna : NoLetAlias st.lets := r2.1.1
  refine ⟨p, en, st, v, hp, hex, r2.1, hna, r2.2.2, h3, ?_⟩
  intro d hs hok hbody
  have halias := typed_letsAlias (shapePre_outs_ne hp) h3 hna hnb d hs hok hbody
  exact ⟨halias, fun mctx mref cctx cref => letsClose_of_data d hok hbody halias mctx mref cctx cref⟩

#print axioms machineShapeN_typed_all

open Lean in
/-- THROWING: the conclusion mentions none of the bundled/derived notions. -/
def checkNoBundleConsts (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  for c in [``Tools.Prototype.ReaderTyped.NoLetBvar, ``Tools.Prototype.ReaderExec.ShapeInOk,
      ``Tools.Prototype.PreprocLetOk.StartDomOk, ``Tools.Prototype.PreprocLetOk.NormRange] do
    if (ci.type.find? fun x => x.isConstOf c).isSome then
      throwError "COMPOSED CHECK FAILED: {n} mentions {c}"
  logInfo m!"composed check {n}: no NoLetBvar/ShapeInOk/StartDomOk/NormRange constant in the type"

run_meta checkNoBundleConsts ``machineShapeN_typed_all
run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``machineShapeN_typed_all
  ["RootFloatRange", "LiftRange", "Inst1Range", "SigTyRange", "ZeroLitAgrees", "RawNodeRange", "NormNodeRange", "EqvLetOk0", "Eq", "Eq"])

/-! ## Whole-conclusion check (unit LCC2, reviewer binding)

`ExpectedConcl` is the explicitly written expected conclusion (an `abbrev`, so the comparison below is at REDUCIBLE
transparency).  `checkConclusion` (THROWING) telescopes `machineShapeN_typed_all`, instantiates the binders of LCQ2's
`machineShapeN_typed_nb` by the SAME fvars (name + `isDefEq` type alignment: senv, sm, ps, ci, ai, sp, h; every other binder is a
fresh fvar), asserts the alignment lists, then requires (1) the two conclusions `isDefEq` and (2) each equal to `ExpectedConcl`. -/
abbrev ExpectedConcl (senv : StructEnv) (sm : Bool) (ps : List (String × Nat)) (ci : Lean.ConstantInfo)
    (ai : Bool) (sp : MachineShape) : Prop :=
  ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
    shapePre sm ps ci senv = some p ∧ execNorm senv p.e = some en ∧
    RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
    shapePost ai p (shapeMid senv p en) st v = some sp ∧
    (∀ (d : MachineData), d.shape = sp → d.ok = true →
      d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed →
      d.letsAliasOk = true ∧
      ∀ {declName : Name} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
        (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State),
        Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape)

open Lean Meta in
/-- Instantiate the binders of `ty`: a binder whose name matches a `shared` fvar and whose domain is defeq to its type becomes that fvar;
any other binder a fresh fvar.  Returns (conclusion, aligned names, fresh names). -/
partial def alignShared (shared : Array Expr) (ty : Expr) (al fr : Array String := #[]) :
    MetaM (Expr × Array String × Array String) := do
  match ty with
  | .forallE n d b bi =>
    let mut hit : Option Expr := none
    for x in shared do
      if hit.isNone && (← x.fvarId!.getUserName) == n then
        if ← isDefEq d (← inferType x) then hit := some x
    match hit with
    | some x => alignShared shared (b.instantiate1 x) (al.push n.toString) fr
    | none => withLocalDecl n bi d fun x => do
        let (c, a, f) ← alignShared shared (b.instantiate1 x) al (fr.push n.toString)
        pure (c, a, f)
  | _ => pure (ty, al, fr)

open Lean Meta in
def checkConclusion : MetaM Unit := do
  let ci ← getConstInfo ``machineShapeN_typed_all
  let cn ← getConstInfo ``machineShapeN_typed_nb
  forallTelescope ci.type fun xs concl => do
    let mut shared : Array Expr := #[]
    for x in xs do
      let nm := (← x.fvarId!.getUserName).toString
      if ["senv", "sm", "ps", "ci", "ai", "sp", "h"].contains nm then shared := shared.push x
    let names ← shared.mapM fun x => do pure (← x.fvarId!.getUserName).toString
    if names.toList != ["senv", "sm", "ps", "ci", "ai", "sp", "h"] then
      throwError "CONCLUSION CHECK FAILED: shared fvars of typed_all are {names}"
    let (concl2, al, fr) ← alignShared shared cn.type
    if al.toList != ["senv", "sm", "ps", "ci", "ai", "sp", "h"] then
      throwError "CONCLUSION CHECK FAILED: typed_nb aligned binders {al}"
    if fr.toList != ["hroot", "hlift", "hinst1", "hsig", "hin"] then
      throwError "CONCLUSION CHECK FAILED: typed_nb fresh binders {fr}"
    unless ← isDefEq concl concl2 do
      throwError "CONCLUSION CHECK FAILED: typed_all and typed_nb conclusions differ"
    let exp := mkAppN (mkConst ``ExpectedConcl) #[shared[0]!, shared[1]!, shared[2]!, shared[3]!, shared[4]!, shared[5]!]
    -- (unit GAUD) the compared terms and the mutation term are type-correct, have no metavariables and no stray free variables
    let bad := mkAppN (mkConst ``ExpectedConcl) #[shared[0]!, shared[1]!, shared[2]!, shared[3]!,
      mkApp (mkConst ``not) shared[4]!, shared[5]!]
    for (e, what) in [(concl, "typed_all conclusion"), (concl2, "typed_nb conclusion"), (exp, "ExpectedConcl term"), (bad, "mutation term")] do
      check e
      let e ← instantiateMVars e
      if e.hasMVar then throwError "CONCLUSION CHECK FAILED: metavariables in the {what}"
      for f in (collectFVars {} e).fvarIds do
        unless xs.any (·.fvarId! == f) do throwError "CONCLUSION CHECK FAILED: stray free variable in the {what}"
    unless ← withReducible (isDefEq concl exp) do
      throwError "CONCLUSION CHECK FAILED: typed_all conclusion differs from ExpectedConcl"
    unless ← withReducible (isDefEq concl2 exp) do
      throwError "CONCLUSION CHECK FAILED: typed_nb conclusion differs from ExpectedConcl"
    -- sensitivity: a mutated expectation (`ai` negated) must be rejected
    if ← withReducible (isDefEq concl bad) then
      throwError "CONCLUSION CHECK FAILED: check is insensitive (mutated expectation accepted)"
    logInfo m!"conclusion check: typed_all = typed_nb = ExpectedConcl (aligned {al}; typed_nb fresh {fr})"

run_meta checkConclusion

end Tools.Prototype.ReaderComposed
