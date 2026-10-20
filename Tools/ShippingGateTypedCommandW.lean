import Tools.ShippingGateTypedCommand
import Tools.ShippingNoPortsTypedBW
-- Round par/sat. BUILT: sa1 (ComposedGW, NoPortsTypedBW exit ok; SatInputs failed: 7 tactic/term errors, fixed by the worker), sa2 (all, exit 0, 669 jobs).

/-! # Generator: the typed design endpoint EXPORTING THE WIRING (round par/sat)

`Tools.ShippingGateTypedCommand.generate` builds `<p>_designClosedB` from `f.machine_ships_hierRG`,
whose `composed` argument is

    fun (11 run binders) hBnd hm => composedG_of_T (f.machine_composedTRGA … projections of hBnd) hm

(`Tools.ShippingMachineShipsHierCommand.generateWith`, route `.seq`), and `f.machine_composedTRGA`
is `machine_linkedT_callsRG h … hcalls (reflection proofs)` (`generateCoreSRG`, `atW := true`),
possibly under one `Eq.mpr` source transport (`endpointParts`' `back?`).

Here:

* `composedTRGAW f`: `f.machine_composedTRGAW`, the value of `f.machine_composedTRGA` with the head
  constant `machine_linkedT_callsRG` replaced by `machine_linkedT_callsRGW` (identical binders; a
  strengthened conclusion). The `Eq.mpr` transport, when present, is REBUILT for the new type (as
  `generateCoreSRG` builds it). The kernel checks the result.
* `composedW f e`: `e` (the composed argument above) with `composedG_of_T ↦ composedGW_of_T` and
  `f.machine_composedTRGA ↦ f.machine_composedTRGAW`.
* `generateW`: `generate`, copied, with `a[23] := composedW f a[23]` and the head
  `machine_design_noPortsTBW` (same binder layout as `machine_design_noPortsT`).

Only the memory-free one-level route (`composedG_of_T`, reset `Reset1`) is handled: an argument
built with `composedG_of_Tmem` is refused. -/
namespace Tools.ShippingGateTypedCommandW
open Lean Meta
open Tools.ShippingGateTypedCommand

/-- Replace the constant `old` by `new` (same universe levels) everywhere in `e`; the number of
replaced occurrences is returned too. -/
def swapConst (old new : Name) (e : Lean.Expr) : Lean.Expr × Nat :=
  let n := (e.foldConsts 0 fun c k => if c == old then k + 1 else k)
  (e.replace fun x => match x with
    | .const c ls => if c == old then some (.const new ls) else none
    | _ => none, n)
-- (writing-time guess, accepted by build sa1/sa2: `Expr.foldConsts` visits each distinct constant ONCE, so `n` is 0 or 1 —
-- it is used only as "occurs / does not occur")

/-- `f.machine_composedTRGAW` (reused when present). -/
def composedTRGAW (f : Name) : MetaM Name := do
  let src := f ++ `machine_composedTRGA
  let name := f ++ `machine_composedTRGAW
  if (← getEnv).contains name then return name
  let some (.thmInfo ti) := (← getEnv).find? src
    | throwError "{src}: not a theorem (run #machine_design_svRG0 first)"
  let v := ti.value
  let swap (e : Lean.Expr) : MetaM Lean.Expr := do
    let (e', n) := swapConst ``Tools.ShippingMachineCallsLinkedTG.machine_linkedT_callsRG
      ``Tools.ShippingMachineCallsLinkedTG.machine_linkedT_callsRGW e
    unless n > 0 do throwError "{src}: not built from machine_linkedT_callsRG"
    pure e'
  let value ← if v.isAppOfArity ``Eq.mpr 4 then do
      -- the source transport of `generateCoreSRG`: `Eq.mpr (congrArg motive heq) inner`
      let args := v.getAppArgs
      let hT := args[2]!
      unless hT.isAppOfArity ``congrArg 6 do throwError "{src}: the transport's shape"
      let heq := hT.getAppArgs[5]!
      let some (_, _, srcN) := (← inferType heq).eq? | throwError "{src}: the transport's equation"
      let inner ← swap args[3]!
      let T ← inferType inner
      let motT ← kabstract T srcN
      unless motT.hasLooseBVars do throwError "{src}: the new theorem does not read the source"
      let hT' ← mkCongrArg (.lam `s (← inferType srcN) motT .default) heq
      mkEqMPR hT' inner
    else swap v
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  Tools.ShippingMachineLinkedCommand.addTheorem name type value
  return name

/-- The composed argument of `f.machine_ships_hierRG`, rewritten to its `ComposedGW` twin. -/
def composedW (f : Name) (e : Lean.Expr) : MetaM Lean.Expr := do
  let cW ← composedTRGAW f
  let (e1, n1) := swapConst ``Tools.ShippingMachineShipsHier.composedG_of_T
    ``Tools.ShippingComposedGW.composedGW_of_T e
  unless n1 > 0 do
    throwError "{f}: the composed argument is not built from composedG_of_T (memory-only route not handled)"
  let (e2, n2) := swapConst (f ++ `machine_composedTRGA) cW e1
  unless n2 > 0 do throwError "{f}: the composed argument does not read {f}.machine_composedTRGA"
  let e2 ← instantiateMVars e2
  try check e2 catch ex => throwError "{f}: the rewritten composed argument is ill-typed: {ex.toMessageData}"
  pure e2

/-- **`Tools.ShippingGateTypedCommand.generate`, copied, with the wiring-exporting head**: the
same steps, except that `machine_ships_hierC`'s `composed` argument (`a[23]`) is rewritten to its
`ComposedGW` twin (`composedW`) before the head is applied; the head defaults to
`machine_design_noPortsTBW` and `names?` is required. -/
def generateW (s : Spec) : MetaM Name := do
  unless s.names?.isSome do throwError "generateW: the wiring head needs `names?`"
  let f := s.parent
  let ships := f ++ `machine_ships_hierRG
  let name := s.name
  if (← getEnv).contains name then throwError "{name}: exists already"
  for n in [s.childConst, s.gateValue, s.runFacts, s.outsG0, s.typedRun, s.designP0, s.closesR,
      s.head] ++ s.valueEq?.toList ++ s.names?.toList do
    unless (← getEnv).contains n do throwError "{n}: unknown constant"
  let some (.thmInfo ti) := (← getEnv).find? ships
    | throwError "{ships}: not a theorem (run #machine_design_svRG0 first)"
  let v := ti.value
  unless v.isAppOf ``Tools.ShippingMachineShipsHier.machine_ships_hierC do
    throwError "{ships}: not built from machine_ships_hierC"
  let a := v.getAppArgs
  unless a.size == 25 do throwError "{ships}: {a.size} arguments of machine_ships_hierC, expected 25"
  -- (par/sat) the composed argument, rewritten to the wiring-exporting twin
  let cW ← composedW f a[23]!
  let a := a.set! 23 cW
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
    let closesPf ← mkAppOptM s.closesR #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, hR0]
    unless ← isDefEq (← inferType closesPf) clT do
      throwError "{s.closesR} does not prove the closing binder{indentExpr clT}"
    let xs' := xs.set! 10 closesPf
    -- machine_design_noPortsT: Reset Bnd C Inv hRI declName d kD ι dom src ext extB lsrc srcL
    -- extL extBL soundL composed houtTy, then the run's binders
    let args : Array (Option Lean.Expr) :=
      #[some a[3]!, some a[4]!, some a[5]!, some a[7]!, some a[9]!,
        some a[10]!, some a[11]!, some a[12]!, some a[13]!, some a[14]!, some a[15]!,
        some a[16]!, some a[17]!, some a[18]!, some a[19]!, some a[20]!, some a[21]!,
        some a[22]!, some a[23]!, some a[24]!] ++ xs'.map some
    let pre ← instantiateMVars (← mkAppOptM s.head args)
    if pre.hasMVar then throwError "{f}: the head's arguments were not all inferred"
    -- the run's facts: zs = raw D w1 hcore hpost hBnd ; xs[9] = entry
    let .forallE _ TF _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's run-facts hypothesis is not where it is expected"
    let hFacts ← forallTelescope TF fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the run-facts hypothesis has {zs.size} binders"
      let p ← mkAppM s.runFacts #[zs[3]!, zs[4]!, xs[9]!, hR0]
      mkLambdaFVars zs (← dischargeWith s.runFacts p zs[5]! goal #[])
    let pre := mkApp pre hFacts
    -- the output check under the gate: zs = raw D w1 hcore hpost hg hBnd
    let .forallE _ TO _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's output-check hypothesis is not where it is expected"
    let hOuts ← forallTelescope TO fun zs goal => do
      unless zs.size == 7 do throwError "{f}: the output-check hypothesis has {zs.size} binders"
      let p ← mkAppM s.outsG0 #[zs[3]!, zs[4]!, xs[9]!, hR0, zs[5]!]
      mkLambdaFVars zs (← dischargeWith s.outsG0 p zs[6]! goal #[])
    let pre := mkApp pre hOuts
    -- the typed children bound: zs = raw D w1 hcore hpost hBnd (cut at 6)
    let .forallE _ TT _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's typed-bound hypothesis is not where it is expected"
    let hTyp ← forallBoundedTelescope TT (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the typed-bound hypothesis has {zs.size} binders"
      let p ← mkAppM s.typedRun #[zs[3]!, zs[4]!, xs[9]!, hR0]
      mkLambdaFVars zs (← dischargeWith s.typedRun p zs[5]! goal #[])
    let pre := mkApp pre hTyp
    -- `designCheck` with no check premise: zs = raw D w1 hcore hpost hBnd (cut at 6)
    let .forallE _ TD _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's design-check hypothesis is not where it is expected"
    let hDesign ← forallBoundedTelescope TD (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the design-check hypothesis has {zs.size} binders"
      let p ← mkAppM s.designP0 #[zs[3]!, zs[4]!, xs[9]!, hR0]
      mkLambdaFVars zs (← dischargeWith s.designP0 p zs[5]! goal #[])
    let pre ← instantiateMVars (mkApp pre hDesign)
    -- the name facts (TB head only): zs = raw D w1 hcore hpost hBnd (cut at 6)
    let pre ← match s.names? with
      | none => pure pre
      | some nm => do
        let .forallE _ TN _ _ ← whnfR (← inferType pre)
          | throwError "{f}: the head's name-facts hypothesis is not where it is expected"
        let hN ← forallBoundedTelescope TN (some 6) fun zs goal => do
          unless zs.size == 6 do throwError "{f}: the name-facts hypothesis has {zs.size} binders"
          let p ← mkAppM nm #[zs[3]!, zs[4]!, xs[9]!, hR0]
          mkLambdaFVars zs (← dischargeWith nm p zs[5]! goal #[])
        instantiateMVars (mkApp pre hN)
    -- the boundary's reflection conjunct, merged with `hR0`
    let (merged, mergedT) ← mergeBoundary pre (reflOf s.gateValue s.valueEq? hR0)
    if merged.containsFVar xs[10]!.fvarId! || mergedT.containsFVar xs[10]!.fvarId! then
      throwError "{name}: the closing binder is still used"
    let newXs := (xs.extract 0 10).push hR0
    pure (← mkForallFVars newXs mergedT, ← mkLambdaFVars newXs merged)
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  for c in refused ++ (if s.names?.isSome then [``Tools.ShippingHierTyped.BoundOff] else []) do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{name}: REFUSED, the statement still mentions {c}"
  Tools.ShippingMachineLinkedCommand.addTheorem name type value
  return name


/-- `generateW` with elaboration-async off and a large recursion depth. -/
def generateTopW (s : Spec) : MetaM Name :=
  withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
    withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) (generateW s)

end Tools.ShippingGateTypedCommandW
