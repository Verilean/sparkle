import Tools.Prototype.DGenConnect
import Tools.Prototype.NormStepModel

/-! # Unit NMC (b): consumer of the MODEL reader `machineShapeNM` for the generated `d`

BUILT: b1 exit 1 (wrong opens), b2 exit 1, b3 exit 0; NMCb: nmcb1 exit 1 (collectFVars), nmcb2 exit 0 (type-correct mutations, Meta.check, aligned binders). No sorry/axiom/native_decide.

`dgen_connect_gen_nm` is the analogue of `DGenConnect.dgen_connect_gen` with the prototype reader `machineShapeN` replaced by the
MODEL wrapper `machineShapeNM` (L6c25): from the generation facts for ONE `d` (`d.ok`, `hbody`, and the SAME shape on both sides,
`GenReadsShape E envG d`, i.e. `machineShape? … = some d.shape`) and the reader link `ShippedToModel` it derives
`machineShapeNM … = some (some d.shape)` and then A's typed conclusion for this `d` through
`NormStepModel.machineShapeNM_typed_all_rawNode'` (so WITHOUT `RawNodeRange`/`NormNodeRange`/`NodeCorr`; the lift/lower/beta ranges
take the place of `RawNodeRange`, as in that corollary).

Scope / wording:
* PREMISE (named, NOT proved): `ShippedToModel` — the shipped `machineShape?` answer is also the answer of the MODEL reader
  `machineShapeNM` on the same input. The 40-case comparison of `Tests/Compiler/NormStepModelWholeAgreeTest.lean` is evidence, not a proof.
* `E`, `envG` are binders; their PROVENANCE (the actual entry constant and generation environment of the generated declaration)
  is the subject of unit DGEN2 and is NOT supplied here. `GenReadsShape E envG d` is taken exactly as in `DGenConnect`; if DGEN2's
  provenance statement has the form `GenReadsShape E envG d` for the actual `E`, `envG`, `d`, it plugs in directly.
* Conclusion = `machineShapeNM … = some (some d.shape) ∧ d.letsAliasOk ∧ LetsClose …`, the conclusion of `dgen_connect_gen` with the
  reader replaced. About the model reader. -/
namespace Tools.Prototype.DGenConnectNM
open Lean Sparkle.Compiler.Elab Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingUnifiedSource
open Tools.ShippingMixedSourceBridge Tools.ShippingEntrySoundness Tools.Prototype.StartDomOk
open Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.Prototype.ReaderTyped
open Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk Tools.Prototype.ReaderClosed Tools.Prototype.ReaderComposed
open Tools.Prototype.RawNodeRangeLetOk Tools.Prototype.NormStepModel Tools.Prototype.DGenConnect

/-- PREMISE (OPEN): on the input `(E, senv)` a SHIPPED `machineShape?` answer `shape` is also the MODEL reader's
`machineShapeNM` answer (default `allowInsts := true`, as `MachineDefines`). The reader link is ONE named premise. -/
def ShippedToModel (E : Lean.ConstantInfo) (senv : StructEnv) (shape : MachineShape) : Prop :=
  machineShape? false [] E senv = some shape → machineShapeNM false [] E senv true = some (some shape)

theorem dgen_connect_gen_nm
    (hroot : RootFloatRange) (hinst1 : Inst1Range) (hz : ZeroLitAgrees)
    (hll : LiftLooseRange) (hlo : LowerLooseRange) (hbeta : BetaRange) (hE : EqvLetOk0)
    {E : Lean.ConstantInfo} {envG : Lean.Environment}
    (hsig : SigTyRange (structEnv envG))
    (d : MachineData) (hok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hgen : GenReadsShape E envG d)
    (hpe : ∀ p : ShapePre, shapePre false [] E (structEnv envG) = some p → LetOk 0 p.e = true)
    (hcorr : ShippedToModel E (structEnv envG) d.shape) :
    machineShapeNM false [] E (structEnv envG) true = some (some d.shape) ∧
    d.letsAliasOk = true ∧
    ∀ {declName : Name} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
      (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State),
      Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape := by
  have hN := hcorr hgen
  obtain ⟨p, en, st, v, _, _, _, _, _, _, hall⟩ :=
    machineShapeNM_typed_all_rawNode' hroot hinst1 hsig hz hll hlo hbeta hE hpe hN
  obtain ⟨ha, hc⟩ := hall d rfl hok hbody
  exact ⟨hN, ha, hc⟩

#print axioms dgen_connect_gen_nm

run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``dgen_connect_gen_nm
  ["RootFloatRange", "Inst1Range", "ZeroLitAgrees", "LiftLooseRange", "LowerLooseRange", "BetaRange", "EqvLetOk0",
    "SigTyRange", "Eq", "Eq", "GenReadsShape", "Eq", "ShippedToModel"])

/- THROWING: the conclusion of `dgen_connect_gen_nm` is `isDefEq` to the conclusion of `DGenConnect.dgen_connect_gen` with
`machineShapeN ↦ machineShapeNM`. The 7 shared binders `E envG d hok hbody hgen hpe` are checked to be present in BOTH telescopes
in the same order and with `isDefEq` domains (old domain after substituting the shared fvars). The compared terms are checked to have
no mvars and no stray fvars (every fvar is a binder of the new telescope). Every mutated conclusion is first run through
`Meta.check` (it must be TYPE-CORRECT), and is then required to be REJECTED by the defeq comparison with the tag `CONCL-NOT-DEFEQ`
(a type error would carry a different message and would NOT count as a rejection). Mutations: (1) no reader replacement,
(2) the whole proposition `LetsClose … d.shape` replaced by `True`, (3) the old `d` not identified with the new one. -/
open Meta in
def checkConcl (mutate : Nat) : MetaM Unit := do
  let newI ← getConstInfo ``dgen_connect_gen_nm
  let oldI ← getConstInfo ``dgen_connect_gen
  let shared : List Name := [`E, `envG, `d, `hok, `hbody, `hgen, `hpe]
  forallTelescope newI.type fun xs nb => forallTelescope oldI.type fun ys ob => do
    let mut froms : Array Expr := #[]
    let mut tos : Array Expr := #[]
    let mut oldPos : Array Nat := #[]
    let mut newPos : Array Nat := #[]
    let mut sharedYs : Array Expr := #[]
    let mut idx := 0
    for y in ys do
      let n ← y.fvarId!.getUserName
      idx := idx + 1
      if mutate == 3 && n == `d then continue
      if shared.contains n then
        let mut found := false
        let mut k := 0
        for x in xs do
          k := k + 1
          if (← x.fvarId!.getUserName) == n then
            froms := froms.push y; tos := tos.push x; found := true
            oldPos := oldPos.push idx; newPos := newPos.push k; sharedYs := sharedYs.push y
        unless found do throwError "shared binder {n} missing in new theorem"
    -- alignment in order and by type (not for mutation 3, which deliberately drops `d`)
    if mutate != 3 then
      unless froms.size == shared.length do throwError "expected {shared.length} shared binders, found {froms.size}"
      let isInc (a : Array Nat) := (List.range (a.size - 1)).all fun i => a[i]! < a[i+1]!
      unless isInc oldPos && isInc newPos do throwError "shared binders are not aligned in order"
      for y in sharedYs, x in tos do
        let yt := (← inferType y).replaceFVars froms tos
        unless (← isDefEq yt (← inferType x)) do
          throwError "shared binder {← y.fvarId!.getUserName}: domains are not defeq"
    let ob := ob.replaceFVars froms tos
    let ob := ob.replace fun x =>
      if mutate != 1 && x.isConstOf ``machineShapeN then some (.const ``machineShapeNM [])
      else if mutate == 2 && x.getAppFn.isConstOf ``Tools.ShippingClosesSplit.LetsClose then some (mkConst ``True)
      else none
    -- well-formedness of the compared terms
    if ob.hasMVar || nb.hasMVar then throwError "mvars in compared conclusions"
    if mutate != 3 then
      let isStray (f : FVarId) := !xs.any (·.fvarId! == f)
      if ob.hasAnyFVar isStray || nb.hasAnyFVar isStray then throwError "stray fvars in compared conclusions"
    Meta.check ob
    Meta.check nb
    unless (← isDefEq ob nb) do throwError "CONCL-NOT-DEFEQ"
    logInfo m!"NMC check (mutate={mutate}): conclusion defeq to dgen_connect_gen's with the reader replaced; {froms.size} shared fvars"

run_meta checkConcl 0
run_meta (do
  for m in [1, 2, 3] do
    let msg ← try checkConcl m; pure "" catch e => pure (← e.toMessageData.toString)
    if msg == "" then throwError "mutation {m} was NOT rejected"
    unless msg.endsWith "CONCL-NOT-DEFEQ" do throwError "mutation {m} failed for another reason: {msg}"
  logInfo m!"NMC check: mutations 1,2,3 type-correct (Meta.check) and rejected by the defeq comparison")

end Tools.Prototype.DGenConnectNM
