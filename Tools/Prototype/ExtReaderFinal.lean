import Tools.Prototype.ExtReaderGlue
import Tools.Prototype.ExtReaderShipped

/-! # Unit EXT2 (7/N): the typed corollary of the MODEL reader `machineShapeXM`, without the correspondence premises

STATUS: see REPORT-EXT2.md (run names and exits) and the ledger L6c28. No sorry / axiom / native_decide; `#print axioms` below.

`machineShapeXM` = `machineShapeX modelOps`: the wrapper of the NMI reader `machineShapeNM` whose phases CALL the models instead of the shipped
extern / partial operations — `liftM`, `lowerM`, `inst1M`, `betaM`, `eqvX`, `rootFloatS`, `zeroLitM`, `zetaAllM` (record `modelOps`) — at
every call site of the reader copies (`convStepX`, `nestedStepX`, `instStepX`, `instSStepX`, `chainStepX`, `loopRootStepX`, `normStepX`,
`rawNodeX`, `machReserveX`, `shapeMidX`, `domGuardX`, `instResX`). The copies are the text of the shipped phases with those call sites
turned into `O.…`; shared phases are not copied.

PROVED here (no correspondence premise, no `RootFloatRange`/`Inst1Range`/`LiftLooseRange`/`LowerLooseRange`/`BetaRange`/`EqvLetOk0`/
`ZeroLitAgrees`/`RawNodeRange`/`NormNodeRange`/`NodeCorr`): `machineShapeXM_typed_all`. Its remaining hypotheses and their KIND:
* `hsig : SigTyRange senv` — INPUT condition on the environment (`senv.instS` result types mention no `_machLet`); not derived.
* `hpe` — INPUT condition (the preprocessed term of the declaration has `LetOk 0`); not derived.
* `h : machineShapeXM … = some (some sp)` — the successful run (hypothesis of the theorem, not a premise about the code).
* inside the conclusion: `d.ok = true` and `hbody` — generation-path checks (antecedents of the typed conclusion, as in the NMI corollary).

What this is NOT: a statement about the shipped `machineShape?` (production switch is a separate decision; the 40-case comparison in
`Tests/Compiler/ExtReaderWholeAgreeTest.lean` is evidence of agreement of refusals/results, never an equivalence claim). OPEN, by kind:
* shipped extern / `partial` operations ↔ models: NOT proved and no longer needed by this theorem; evidence only
  (`Tests/Compiler/ExtReaderOpsAgreeTest.lean`). `rootFloat` ↔ `rootFloatS` stays LC6's premise `RootFloatAgrees`; the fuel model `rootFloatN` is shown
  adequate for `rootFloatS` (`ExtRootFloat`). `zetaAllM` is a fuel model (fuel `zetaAllFuel`; exhaustion answers the subterm unchanged).
* calls still going to the shipped functions inside shared helpers: `Expr.eqv` in `machBindLet`, `machBindLetNamed`, `machBindLetAlias`,
  `machLetIndex`; `machReserve` inside `shapeStart` (called on the empty state, where its `!=` test is never reached); `hasLooseBVars`;
  `getAppFn`/`getAppArgs`; `Expr.replace` is not used (zeroLit is `zeroLitM`). The proofs hold for any answer of these Bool/structural tests.
* `rawNodeX shippedOps = rawNode` is NOT proved (`Meta.isDefEq` does not match the two compiled name-literal matchers); named `RawNodeXShipped` in
  `ExtReaderShipped`, evidence-tested only. The other `…X shippedOps = …` identities are PROVED (`rfl` or short proofs).
* the reader copies are text copies of the shipped phases: transcription fidelity is not proved (as for LC9's `step`). -/

namespace Tools.Prototype.ExtReader
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.ShippingReaderFuel
  Tools.ShippingLetsAliasInv Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk
  Tools.Prototype.NormNodeModelLetOk Tools.Prototype.ReaderLfp Lean.Order
open Tools.ShippingReaderFuelShapeR5 Tools.ShippingReaderLenOk Tools.ShippingCloInv
open Tools.Prototype.ReaderTyped Tools.Prototype.ReaderClosed
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineEntry
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMixedSourceBridge
open Tools.Prototype.NormStepModel Tools.Prototype.ExtModelLetOk

/-- **Corollary for the MODEL reader** (PROVED; hypotheses: `hsig`, `hpe` — input conditions — and the successful run `h`). -/
theorem machineShapeXM_typed_all {senv : StructEnv} (hsig : SigTyRange senv)
    {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool} {sp : MachineShape}
    (hpe : ∀ p : ShapePre, shapePre sm ps ci senv = some p → LetOk 0 p.e = true)
    (h : machineShapeXM sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNormXM senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
      shapePost ai p (shapeMidXM senv p en) st v = some sp ∧
      (∀ (d : MachineData), d.shape = sp → d.ok = true →
        d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
          (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed →
        d.letsAliasOk = true ∧
        ∀ {declName : Name} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
          (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State),
          Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape) :=
  machineShapeX_typed_all modelOps_ok hsig hpe h

#print axioms modelOps_ok
#print axioms machineShapeX_typed_all
#print axioms machineShapeXM_typed_all

/- THROWING: the exact list of Prop binders (head constant of each conclusion), in order. SCOPE: it checks only the last name component of the
head constant of each OUTER Prop hypothesis; it does not check their full types. -/
run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``machineShapeXM_typed_all ["SigTyRange", "Eq", "Eq"])
run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``machineShapeX_typed_all ["OpsOk", "SigTyRange", "Eq", "Eq"])

open Meta in
/-- THROWING (run below): the type of `machineShapeXM_typed_all` mentions none of the premise constants of the previous corollary and
of its predecessors, and the axioms of the theorem are the three standard ones. -/
def checkNoPremises : MetaM Unit := do
  let i ← getConstInfo ``machineShapeXM_typed_all
  let bad : List Name :=
    [``RootFloatRange, ``Inst1Range, ``Tools.Prototype.RawNodeRangeLetOk.LiftLooseRange,
     ``Tools.Prototype.RawNodeRangeLetOk.LowerLooseRange, ``Tools.Prototype.RawNodeRangeLetOk.BetaRange,
     ``Tools.Prototype.StartDomOk.EqvLetOk0, ``ZeroLitAgrees, ``RawNodeRange, ``NormNodeRange,
     ``Tools.Prototype.NormNodeModelLetOk.NodeCorr, ``LiftCorr, ``LowerCorr, ``Inst1Corr, ``BetaCorr, ``EqvCorr,
     ``RootFloatCorr, ``OpsOk, ``RawNodeXShipped]
  for c in bad do
    if i.type.getUsedConstants.contains c then throwError "{c} occurs in the type of machineShapeXM_typed_all"
  let ax ← Lean.collectAxioms ``machineShapeXM_typed_all
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for a in ax do
    unless ok.contains a do throwError "unexpected axiom {a}"
  logInfo m!"EXT2 premise check: no premise constants in the type; axioms {ax.toList}"

run_meta checkNoPremises

/- THROWING whole-conclusion check against the previous corollary `machineShapeNM_typed_all_rawNode_corr` (EXT) with the reader replaced.
Aligned binders: the 9 shared ones (`senv hsig sm ps ci ai sp hpe h`; `h`'s type compared after replacing `machineShapeNM ↦ machineShapeXM`);
the 7 binders `hroot hinst1 hz hll hlo hbeta hE` of the old statement have no counterpart (fresh metavariables in the old type).
The old conclusion with `machineShapeNM ↦ machineShapeXM`, `execNormM ↦ execNormXM`, `shapeMid ↦ shapeMidXM` must be `isDefEq` (REDUCIBLE
transparency) to the new conclusion. Mutations are TYPE-CORRECT changes of the expected conclusion/hypothesis (each is `Meta.check`ed) and
each must be rejected with its own tag: the check has no other way to reject them. -/
open Meta in
def checkExt2 (mutate : Nat) : MetaM Unit := do
  let newI ← getConstInfo ``machineShapeXM_typed_all
  let oldI ← getConstInfo ``machineShapeNM_typed_all_rawNode_corr
  let replaced : List Name := [`hroot, `hinst1, `hz, `hll, `hlo, `hbeta, `hE]
  let rep (e : Expr) : Expr :=
    e.replace fun x =>
      if x.isConstOf ``machineShapeNM then (if mutate == 3 then none else some (.const ``machineShapeXM []))
      else if x.isConstOf ``execNormM then (if mutate == 1 then none else some (.const ``execNormXM []))
      else if x.isConstOf ``shapeMid then (if mutate == 2 then none else some (.const ``shapeMidXM []))
      else none
  forallTelescope newI.type fun xs nb => do
    let mut oty := oldI.type
    let mut j : Nat := 0
    let mut nrep : Nat := 0
    for _ in [0:xs.size + 10] do
      match oty with
      | .forallE n d b _ =>
        if replaced.contains n then
          nrep := nrep + 1
          oty := b.instantiate1 (← mkFreshExprMVar d)
        else
          unless j < xs.size do throwError "old type has more binders than new"
          unless (← xs[j]!.fvarId!.getUserName) == n do throwError "binder name mismatch at {j}: {n}"
          unless ← withReducible (isDefEq (rep d) (← xs[j]!.fvarId!.getType)) do
            throwError "REJECT:binder:{n}: hypothesis type differs"
          oty := b.instantiate1 xs[j]!
          j := j + 1
      | _ => break
    unless nrep == 7 && j == xs.size do throwError "binder bookkeeping failed ({nrep}, {j}, {xs.size})"
    let mut exp := rep oty
    -- mutation 4: a type-correct change of the expected conclusion (`ai` ↦ `!ai`)
    if mutate == 4 then
      let ai := xs[5]!
      exp := exp.replace fun x => if x == ai then some (mkApp (.const ``not []) ai) else none
    if mutate != 0 then
      Meta.check exp
    unless ← withReducible (isDefEq exp nb) do throwError "REJECT:conclusion: expected conclusion differs from the new one"
    logInfo m!"EXT2 check (mutate={mutate}): conclusion identical to the old one modulo 3 reader constants; {xs.size} shared binders, 7 dropped"

run_meta checkExt2 0

run_meta (do
  let expect : List (Nat × String) := [(1, "REJECT:conclusion"), (2, "REJECT:conclusion"), (3, "REJECT:binder:h"), (4, "REJECT:conclusion")]
  for (m, tag) in expect do
    let msg ← (try (do checkExt2 m; pure "ACCEPTED") catch e => pure (← e.toMessageData.toString))
    unless msg.startsWith tag do throwError "mutation {m} expected {tag} but got: {msg}"
  logInfo m!"EXT2 check: mutations 1 (execNormM kept), 2 (shapeMid kept), 3 (reader kept in h), 4 (ai ↦ !ai) rejected with their tags")

end Tools.Prototype.ExtReader
