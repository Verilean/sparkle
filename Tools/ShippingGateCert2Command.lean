import Tools.ShippingGateCertCommand
import Tools.ShippingGateCert2
-- BUILT as written: cf1 (exit 0, 665 jobs; round par/cert2).

/-! # Generator from DATA ONLY: the typed design endpoint of a memory + one-gate-child parent (round par/cert2)

`Tools.ShippingGateCertCommand.generateCert` (kept unchanged) takes the certificate theorem and
the per-parent kid-fact theorems `<p>_kids` / `<p>_kidTyped` (which used the hand-written
`<p>_entry`, the binder-position `decide`s and `fakeSrc_width` / `fakeN_width`).
`generateCert2` takes instead the DATA:

* the gate child: `childConst` (the called name, a constant of type `Name`), `gateValue`, and
  the gate source namespace `src` (`src.gateBinders`, `src.gateSort`, `src.gateBpos`,
  `src.gateVpos`, `src.gateVw`, `src.gate_old`, `src.gate_peel`, `src.gate_wf`, as
  `#gate_child` / `gateDefs` write them);
* the memory origin `cb aw dw`, the per-origin tables `outsF` / `insF` (constants
  `InstOrigin → List …`), `nDecl`;
* optionally a certificate theorem `cert?`; when `none` the certificate is proved INLINE
  (`Eq.refl true` at `gateParentCertOk … = true`, evaluated by the kernel);

and proves INLINE (no auxiliary declaration)

* `memGateOk d cb aw dw childConst src.gateBinders src.gateBpos src.gateVpos src.gateVw
  src.gateSort.width = true` (`Eq.refl true`, evaluated by the kernel): the origin table, the
  binder positions, the width ≠ 1;
* the kid facts by `memGate_kidsS` / `memGate_kidTypedS` (`hmo hmi hgo hgi` by `Eq.refl`,
  checked by `mkAppM`'s unification: `outsF` / `insF` must reduce at `.mem cb aw dw` / `.ord`);
* the five run lemmas by `gateParent_*` (as `generateCert`).

STILL GIVEN per parent: the closing `closesR` (a theorem `{ctx} (hR0) : MachineClosesAt …`), the
reflection binder `hR0` (`EntryDefines … childConst gateValue`, a premise of the result), the
value equation `valueEq?`. A kernel-evaluation failure of an inline `Eq.refl true` surfaces as
the kernel's error at `addTheorem` (no earlier check). -/
namespace Tools.ShippingGateCert2Command
open Lean Meta
open Tools.ShippingGateTypedCommand (dischargeWith reflOf mergeBoundary refused)

/-- The generator's input (data route). -/
structure CertSpec2 where
  parent : Name
  name : Name
  /-- A constant of type `Lean.Name`: the gate child's (colliding) name, the `.ord` entries'
  callee. -/
  childConst : Name
  gateValue : Name
  valueEq? : Option Name := none
  closesR : Name
  /-- The gate source namespace (`src.gateBinders`, …, `src.gate_wf`). -/
  src : Name
  /-- `InstOrigin → List OutField`, `InstOrigin → List Nat`. -/
  outsF : Name
  insF : Name
  cb : Bool
  aw : Nat
  dw : Nat
  nDecl : Nat
  /-- A certificate theorem; `none`: proved inline. -/
  cert? : Option Name := none
  head : Name := ``Tools.ShippingNoPortsTyped.machine_design_noPortsTB

/-- `Eq.refl true` at `lhs = true` (the kernel evaluates `lhs`). -/
def reflTrue (lhs : Lean.Expr) : MetaM Lean.Expr := do
  mkExpectedTypeHint (← mkEqRefl (mkConst ``Bool.true)) (← mkEq lhs (mkConst ``Bool.true))

/-- **The generator, data route.** -/
def generateCert2 (s : CertSpec2) : MetaM Name := do
  let f := s.parent
  let ships := f ++ `machine_ships_hierRG
  let src := s.src
  let name := s.name
  if (← getEnv).contains name then throwError "{name}: exists already"
  for n in [s.childConst, s.gateValue, s.closesR, s.head, s.outsF, s.insF,
      f ++ `machineData, f ++ `machine_ok, f ++ `machine_body,
      src ++ `gateBinders, src ++ `gateSort, src ++ `gateBpos, src ++ `gateVpos, src ++ `gateVw,
      src ++ `gate_old, src ++ `gate_peel, src ++ `gate_wf] ++ s.valueEq?.toList ++ s.cert?.toList do
    unless (← getEnv).contains n do throwError "{n}: unknown constant"
  let dataC := mkConst (f ++ `machineData)
  let okC := mkConst (f ++ `machine_ok)
  let bodyC := mkConst (f ++ `machine_body)
  let outsFC := mkConst s.outsF
  let insFC := mkConst s.insF
  let cbE := toExpr s.cb
  let awE := mkNatLit s.aw
  let dwE := mkNatLit s.dw
  let cE := mkConst s.childConst
  -- the tables keyed by entry: `fun k => outsF (originAt d.shape k)`
  let shapeE ← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[dataC]
  let byEntry (tbl : Lean.Expr) : MetaM Lean.Expr :=
    withLocalDeclD `k (mkConst ``Nat) fun k => do
      mkLambdaFVars #[k] (mkApp tbl (← mkAppM ``Tools.ShippingInstTagged.originAt #[shapeE, k]))
  let kidOutsE ← byEntry outsFC
  let kidInsE ← byEntry insFC
  -- the certificate: given, or `Eq.refl true` (kernel-evaluated)
  let certLhs := mkAppN (mkConst ``Tools.ShippingGateCert.gateParentCertOk)
    #[dataC, mkNatLit s.nDecl, kidOutsE, kidInsE]
  let certPf ← match s.cert? with
    | some n => do
      let want ← mkEq certLhs (mkConst ``Bool.true)
      unless ← isDefEq (← inferType (mkConst n)) want do
        throwError "{n} does not prove{indentExpr want}"
      pure (mkConst n)
    | none => reflTrue certLhs
  -- the kid side: one Bool, `Eq.refl true` (kernel-evaluated)
  let widthE := mkApp (mkConst ``Tools.ShippingUnifiedSource.SType.width) (mkConst (src ++ `gateSort))
  let okLhs := mkAppN (mkConst ``Tools.ShippingGateCert2.memGateOk)
    #[dataC, cbE, awE, dwE, cE, mkConst (src ++ `gateBinders), mkConst (src ++ `gateBpos),
      mkConst (src ++ `gateVpos), mkConst (src ++ `gateVw), widthE]
  let hokPf ← reflTrue okLhs
  let memE := mkApp3 (mkConst ``Sparkle.Compiler.MachInstOrigin.InstOrigin.mem) cbE awE dwE
  let ordE := mkConst ``Sparkle.Compiler.MachInstOrigin.InstOrigin.ord
  let hmo ← mkEqRefl (mkApp outsFC memE)
  let hmi ← mkEqRefl (mkApp insFC memE)
  let hgo ← mkEqRefl (mkApp outsFC ordE)
  let hgi ← mkEqRefl (mkApp insFC ordE)
  let gateFacts := #[mkConst (src ++ `gate_old), mkConst (src ++ `gate_peel), mkConst (src ++ `gate_wf)]
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
      #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, cE, mkConst s.gateValue]
    withLocalDeclD `hR0 hR0T fun hR0 => do
    let ctxArgs : Array (Option Lean.Expr) := #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, hR0]
    let closesPf ← mkAppOptM s.closesR ctxArgs
    unless ← isDefEq (← inferType closesPf) clT do
      throwError "{s.closesR} does not prove the closing binder{indentExpr clT}"
    let kidsPf ← mkAppM ``Tools.ShippingGateCert2.memGate_kidsS
      (#[dataC, cbE, awE, dwE, cE, outsFC, insFC, hokPf, hmo, hmi, hgo, hgi, hR0] ++ gateFacts)
    let kidTypedPf ← mkAppM ``Tools.ShippingGateCert2.memGate_kidTypedS
      (#[dataC, cbE, awE, dwE, cE, hokPf, hR0] ++ gateFacts)
    let xs' := xs.set! 10 closesPf
    let args : Array (Option Lean.Expr) :=
      #[some a[3]!, some a[4]!, some a[5]!, some a[7]!, some a[9]!,
        some a[10]!, some a[11]!, some a[12]!, some a[13]!, some a[14]!, some a[15]!,
        some a[16]!, some a[17]!, some a[18]!, some a[19]!, some a[20]!, some a[21]!,
        some a[22]!, some a[23]!, some a[24]!] ++ xs'.map some
    let pre ← instantiateMVars (← mkAppOptM s.head args)
    if pre.hasMVar then throwError "{f}: the head's arguments were not all inferred"
    let base := #[dataC, okC, bodyC, certPf]
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

/-- `generateCert2` with elaboration-async off and a large recursion depth. -/
def generateCert2Top (s : CertSpec2) : MetaM Name :=
  withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
    withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) (generateCert2 s)

end Tools.ShippingGateCert2Command
