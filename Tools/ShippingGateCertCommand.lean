import Tools.ShippingGateTypedCommand
import Tools.ShippingGateCert
import Tools.ShippingNoPortsTypedB
-- Round par/cert. BUILT: ce1 (Tools.ShippingGateCert, …CertCommand, exit 0 for both; the test failed on missing `open`s), ce2 (the test, exit 0, 662 jobs; integrator fix: the opens repeated in the second namespace block).

/-! # Generator from a CERTIFICATE: the typed design endpoint of a gate-collision parent (round par/cert)

`Tools.ShippingGateTypedCommand.generate` (kept unchanged) takes five hand-written per-parent run
lemmas. `generateCert` takes instead

* `cert`: a theorem `gateParentCertOk f.machineData nDecl kidOuts kidIns = true` (ONE `decide`
  per parent; `Tools.ShippingGateCert`);
* `kids`, `kidTyped`: the per-entry kid facts (implicit contexts, explicit `hR0`, as the
  per-parent `<p>_kids` / `<p>_kidTyped`; e.g. instances of `Tools.ShippingGateCert.memGate_kids`
  / `memGate_kidTyped`). Their `kidOuts` / `kidIns` / depth must be the certificate's (checked by
  `mkAppM`'s unification);
* `closesR`: the closing, as in `generate`;

and builds the five run-hypothesis proofs INLINE (no auxiliary declaration) from
`gateParent_runFacts` / `_outsG0` / `_typedRun` / `_designP0` / `_names` at
`f.machineData`, `f.machine_ok`, `f.machine_body`. Everything else (head application, boundary
discharge `dischargeWith`, the reflection merge `mergeBoundary`/`reflOf`, the refusal list,
`addTheorem`) is `generate`'s, reused or copied step for step. The head is
`machine_design_noPortsTB` (five run hypotheses, `hNames` last); `BoundOff` is refused. -/
namespace Tools.ShippingGateCertCommand
open Lean Meta
open Tools.ShippingGateTypedCommand (dischargeWith reflOf mergeBoundary refused)

/-- The generator's input (certificate route). -/
structure CertSpec where
  /-- The parent declaration (`f`); `f.machine_ships_hierRG`, `f.machineData`, `f.machine_ok`,
  `f.machine_body` are read. -/
  parent : Name
  /-- The theorem to add. -/
  name : Name
  childConst : Name
  gateValue : Name
  valueEq? : Option Name := none
  /-- `gateParentCertOk f.machineData nDecl kidOuts kidIns = true`. -/
  cert : Name
  /-- `{mctx mref cctx cref} (hR0) : ∀ k hk, KidFactsTC …`. -/
  kids : Name
  /-- `{mctx mref cctx cref} (hR0) : ∀ k hk y, KidT … → FlatOk y.1 ∨ KidTyped y.1`. -/
  kidTyped : Name
  /-- `{mctx mref cctx cref} (hR0) : MachineClosesAt … f f.machineData.shape`. -/
  closesR : Name
  /-- The head; the layout of `machine_design_noPortsTB` (20 leading arguments, 11 run
  binders, then `hFacts hOuts hTyped hDesign hNames`). -/
  head : Name := ``Tools.ShippingNoPortsTyped.machine_design_noPortsTB

/-- **The generator, certificate route.** Same steps as `generate` with `names? := some _`;
the five run lemmas built from the certificate. Returns the added theorem's name. -/
def generateCert (s : CertSpec) : MetaM Name := do
  let f := s.parent
  let ships := f ++ `machine_ships_hierRG
  let dataC := mkConst (f ++ `machineData)
  let okC := mkConst (f ++ `machine_ok)
  let bodyC := mkConst (f ++ `machine_body)
  let certC := mkConst s.cert
  let name := s.name
  if (← getEnv).contains name then throwError "{name}: exists already"
  for n in [s.childConst, s.gateValue, s.cert, s.kids, s.kidTyped, s.closesR, s.head,
      f ++ `machineData, f ++ `machine_ok, f ++ `machine_body] ++ s.valueEq?.toList do
    unless (← getEnv).contains n do throwError "{n}: unknown constant"
  -- the certificate is about THIS parent's data
  let certT ← whnfR (← inferType certC)
  let some (_, lhs, _) := certT.eq? | throwError "{s.cert}: not an equation:{indentExpr certT}"
  unless lhs.isAppOfArity ``Tools.ShippingGateCert.gateParentCertOk 4 do
    throwError "{s.cert}: not a gateParentCertOk certificate:{indentExpr certT}"
  unless ← isDefEq lhs.getAppArgs[0]! dataC do
    throwError "{s.cert}: certifies{indentExpr lhs.getAppArgs[0]!}\nnot {f}.machineData"
  let some (.thmInfo ti) := (← getEnv).find? ships
    | throwError "{ships}: not a theorem (run #machine_design_svRG0 first)"
  let v := ti.value
  unless v.isAppOf ``Tools.ShippingMachineShipsHier.machine_ships_hierC do
    throwError "{ships}: not built from machine_ships_hierC"
  let a := v.getAppArgs
  unless a.size == 25 do throwError "{ships}: {a.size} arguments of machine_ships_hierC, expected 25"
  unless (← instantiateMVars a[7]!).isConstOf ``Tools.ShippingMachineShipsHier.mixInv do
    throwError "{ships}: the invariant is not mixInv:{indentExpr a[7]!}"
  let (type, value) ← forallTelescope (← inferType (mkConst ships)) fun xs _ => do
    unless xs.size == 11 do throwError "{ships}: {xs.size} binders, expected 11"
    let clT ← instantiateMVars (← inferType xs[10]!)
    unless clT.isAppOf ``Tools.ShippingChildInv.MachineClosesAt do
      throwError "{ships}: the last binder is not MachineClosesAt:{indentExpr clT}"
    let hR0T := mkAppN (mkConst ``Tools.ShippingInlineSoundness.EntryDefines)
      #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, mkConst s.childConst, mkConst s.gateValue]
    withLocalDeclD `hR0 hR0T fun hR0 => do
    let ctxArgs : Array (Option Lean.Expr) := #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, hR0]
    let closesPf ← mkAppOptM s.closesR ctxArgs
    unless ← isDefEq (← inferType closesPf) clT do
      throwError "{s.closesR} does not prove the closing binder{indentExpr clT}"
    let kidsPf ← mkAppOptM s.kids ctxArgs
    let kidTypedPf ← mkAppOptM s.kidTyped ctxArgs
    let xs' := xs.set! 10 closesPf
    let args : Array (Option Lean.Expr) :=
      #[some a[3]!, some a[4]!, some a[5]!, some a[7]!, some a[9]!,
        some a[10]!, some a[11]!, some a[12]!, some a[13]!, some a[14]!, some a[15]!,
        some a[16]!, some a[17]!, some a[18]!, some a[19]!, some a[20]!, some a[21]!,
        some a[22]!, some a[23]!, some a[24]!] ++ xs'.map some
    let pre ← instantiateMVars (← mkAppOptM s.head args)
    if pre.hasMVar then throwError "{f}: the head's arguments were not all inferred"
    -- the common prefix of the certificate lemmas: d ok hbody hcert
    let base := #[dataC, okC, bodyC, certC]
    -- hFacts: zs = raw D w1 hcore hpost hBnd ; xs[9] = entry
    let .forallE _ TF _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's run-facts hypothesis is not where it is expected"
    let hFacts ← forallTelescope TF fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the run-facts hypothesis has {zs.size} binders"
      let p ← mkAppM ``Tools.ShippingGateCert.gateParent_runFacts
        (base ++ #[kidsPf, closesPf, zs[3]!, zs[4]!, xs[9]!])
      mkLambdaFVars zs (← dischargeWith ``Tools.ShippingGateCert.gateParent_runFacts p zs[5]! goal #[])
    let pre := mkApp pre hFacts
    -- hOuts: zs = raw D w1 hcore hpost hg hBnd
    let .forallE _ TO _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's output-check hypothesis is not where it is expected"
    let hOuts ← forallTelescope TO fun zs goal => do
      unless zs.size == 7 do throwError "{f}: the output-check hypothesis has {zs.size} binders"
      let p ← mkAppM ``Tools.ShippingGateCert.gateParent_outsG0
        (base ++ #[kidsPf, closesPf, zs[3]!, zs[4]!, xs[9]!, zs[5]!])
      mkLambdaFVars zs (← dischargeWith ``Tools.ShippingGateCert.gateParent_outsG0 p zs[6]! goal #[])
    let pre := mkApp pre hOuts
    -- hTyped: zs = raw D w1 hcore hpost hBnd (cut at 6)
    let .forallE _ TT _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's typed-bound hypothesis is not where it is expected"
    let hTyp ← forallBoundedTelescope TT (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the typed-bound hypothesis has {zs.size} binders"
      let p ← mkAppM ``Tools.ShippingGateCert.gateParent_typedRun
        (base ++ #[kidsPf, kidTypedPf, closesPf, zs[3]!, zs[4]!, xs[9]!])
      mkLambdaFVars zs (← dischargeWith ``Tools.ShippingGateCert.gateParent_typedRun p zs[5]! goal #[])
    let pre := mkApp pre hTyp
    -- hDesign: zs = raw D w1 hcore hpost hBnd (cut at 6)
    let .forallE _ TD _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's design-check hypothesis is not where it is expected"
    let hDesign ← forallBoundedTelescope TD (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the design-check hypothesis has {zs.size} binders"
      let p ← mkAppM ``Tools.ShippingGateCert.gateParent_designP0
        (base ++ #[kidsPf, closesPf, zs[3]!, zs[4]!, xs[9]!])
      mkLambdaFVars zs (← dischargeWith ``Tools.ShippingGateCert.gateParent_designP0 p zs[5]! goal #[])
    let pre ← instantiateMVars (mkApp pre hDesign)
    -- hNames: zs = raw D w1 hcore hpost hBnd (cut at 6)
    let .forallE _ TN _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's name-facts hypothesis is not where it is expected"
    let hN ← forallBoundedTelescope TN (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the name-facts hypothesis has {zs.size} binders"
      let p ← mkAppM ``Tools.ShippingGateCert.gateParent_names
        (base ++ #[closesPf, zs[3]!, zs[4]!, xs[9]!])
      mkLambdaFVars zs (← dischargeWith ``Tools.ShippingGateCert.gateParent_names p zs[5]! goal #[])
    let pre ← instantiateMVars (mkApp pre hN)
    -- the boundary's reflection conjunct, merged with `hR0`
    let (merged, mergedT) ← mergeBoundary pre (reflOf s.gateValue s.valueEq? hR0)
    if merged.containsFVar xs[10]!.fvarId! || mergedT.containsFVar xs[10]!.fvarId! then
      throwError "{name}: the closing binder is still used"
    let newXs := (xs.extract 0 10).push hR0
    pure (← mkForallFVars newXs mergedT, ← mkLambdaFVars newXs merged)
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  for c in refused ++ [``Tools.ShippingHierTyped.BoundOff] do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{name}: REFUSED, the statement still mentions {c}"
  Tools.ShippingMachineLinkedCommand.addTheorem name type value
  return name

/-- `generateCert` with elaboration-async off and a large recursion depth (as `generateTop`). -/
def generateCertTop (s : CertSpec) : MetaM Name :=
  withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
    withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) (generateCert s)

end Tools.ShippingGateCertCommand
