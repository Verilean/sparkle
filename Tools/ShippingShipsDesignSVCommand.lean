import Tools.ShippingMachineDepthCommand
import Tools.ShippingShipsDesignSVAll
import Tools.ShippingMachineShipsHierHCommand

/-! # `#machine_design_svN f n` (and `_sv0`, `_svH`)

`f.machine_design_svN{n}`: `ships_design_svN_all` applied to
`f.machine_ships_hierN{n}` (generated first if absent) — from the source,
through the real full entry and the checked optimizer, to a closed run of
the shipped design's emitted texts showing the source AND to every closed
run showing it (`design_sv_all`, under `outsCheck`), for every run of the compiler, every
input sequence and every length. Kernel-checked; standard axioms only. -/
namespace Tools.ShippingShipsDesignSVCommand
open Lean Meta Elab
open Tools.ShippingMachineLinkedCommand (addTheorem)

/-- A run boundary in the run's contexts (`CtxBnd`) at the shipping theorem's
own context binders `xs` and the run's start world, as a predicate of the core
module and design. -/
def bndAt (ships : Name) (xs : Array Lean.Expr) (bnd : Lean.Expr) : MetaM Lean.Expr := do
  let ctxOf (n : Name) : MetaM Lean.Expr := do
    for x in xs do
      if (← whnfR (← inferType x)).isAppOf n then return x
    throwError "{ships}: no binder of type {n}"
  let mctx ← ctxOf ``Lean.Meta.Context
  let cctx ← ctxOf ``Lean.Core.Context
  let refOf (st : Name) : MetaM Lean.Expr := do
    for x in xs do
      let t ← whnfR (← inferType x)
      if t.isAppOf ``ST.Ref && (t.getAppArgs.back?.map (·.isConstOf st)).getD false then return x
    throwError "{ships}: no reference to {st}"
  let mref ← refOf ``Lean.Meta.State
  let cref ← refOf ``Lean.Core.State
  -- the run's start world: the first world binder
  let mut w? : Option Lean.Expr := none
  for x in xs do
    if w?.isNone && (← whnfR (← inferType x)).isAppOf ``Void then w? := some x
  let some w := w? | throwError "{ships}: no world binder"
  withLocalDeclD `raw (mkConst ``Sparkle.IR.AST.Module) fun raw =>
    withLocalDeclD `D (mkConst ``Sparkle.IR.AST.Design) fun D =>
      mkLambdaFVars #[raw, D] (mkAppN bnd #[mctx, mref, cctx, cref, w, raw, D]).headBeta

/-- `ships_design_svN n` applied to a generated shipping theorem `ships`
(`machine_ships_hier` at depth 0 — `KS = flatKS = KSn _ 0` — or
`_hierN{n}`), with the theorem's OWN reset, run boundary and child bound,
read off its proof term (the arguments `Reset`, `Bnd`, `Bd` of
`machine_ships_hier`). -/
def compose (declName ships name : Name) (n : Nat) : MetaM Name := do
  if (← getEnv).contains name then return name
  let some (.thmInfo ti) := (← getEnv).find? ships | throwError "{ships}: not a theorem"
  let v := ti.value
  unless v.isAppOf ``Tools.ShippingMachineShipsHier.machine_ships_hier do
    throwError "{ships}: not built from machine_ships_hier"
  let args := v.getAppArgs
  let (reset, bnd, bd) := (args[3]!, args[4]!, args[5]!)
  let ty ← inferType (mkConst ships)
  let value ← forallTelescope ty fun xs _ => do
    let h := mkAppN (mkConst ships) xs
    -- the boundary at the run's own contexts (the theorem's context binders)
    let bnd ← bndAt ships xs bnd
    let v ← mkAppOptM ``Tools.ShippingShipsDesignSVAll.ships_design_svN_all
      #[mkNatLit n, reset, bnd, bd, none, none, none, none, none, none, none, none, none, h]
    let v ← instantiateMVars v
    if v.hasMVar then throwError "{declName}: the composition's arguments were not all inferred"
    mkLambdaFVars xs v
  addTheorem name (← inferType value) value
  for ax in ← Lean.collectAxioms name do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{name} uses a non-standard axiom: {ax}"
  return name

/-- `f.machine_design_svN{n}` from `f.machine_ships_hierN{n}` (generated if absent). -/
def generate (declName : Name) (n : Nat) : MetaM Name := do
  let ships ← Tools.ShippingMachineDepthCommand.generateShipsN declName n
  compose declName ships (declName ++ Name.mkSimple s!"machine_design_svN{n}") n

/-- `f.machine_design_sv0` from `f.machine_ships_hier` (the depth-0 route:
sequential children `Reset1`/`kidsMixed`, or memory reads `ResetM`/`kidsMem`;
generated if absent). -/
def generate0 (declName : Name) : MetaM Name := do
  let ships ← Tools.ShippingMachineShipsHierCommand.generate declName
  compose declName ships (declName ++ `machine_design_sv0) 0

/-- `f.machine_design_svH` from `f.machine_ships_hierH` (the combinational
route; generated if absent), its calls' premise `R` read off its proof term. -/
def generateH (declName : Name) : MetaM Name := do
  let name := declName ++ `machine_design_svH
  if (← getEnv).contains name then return name
  let ships ← Tools.ShippingMachineShipsHierHCommand.generate declName
  let some (.thmInfo ti) := (← getEnv).find? ships | throwError "{ships}: not a theorem"
  unless ti.value.isAppOf ``Tools.ShippingMachineShipsHierH.machine_ships_hierH do
    throwError "{ships}: not built from machine_ships_hierH"
  let r := ti.value.getAppArgs[0]!
  let bnd0 := ti.value.getAppArgs[1]!
  let ty ← inferType (mkConst ships)
  let value ← forallTelescope ty fun xs _ => do
    let h := mkAppN (mkConst ships) xs
    let bnd ← bndAt ships xs bnd0
    let v ← mkAppOptM ``Tools.ShippingShipsDesignSVAll.ships_design_svH_all
      #[r, bnd, none, none, none, none, none, none, none, none, h]
    let v ← instantiateMVars v
    if v.hasMVar then throwError "{declName}: the composition's arguments were not all inferred"
    mkLambdaFVars xs v
  addTheorem name (← inferType value) value
  for ax in ← Lean.collectAxioms name do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{name} uses a non-standard axiom: {ax}"
  return name

elab "#machine_design_svH " d:ident : command => do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← Command.liftTermElabM <|
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 })
        (generateH declName)
  logInfo m!"{name}: source → shipped design's closed emitted texts (DesignSV, combinational children), checked by the kernel"

elab "#machine_design_sv0 " d:ident : command => do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← Command.liftTermElabM <|
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 })
        (generate0 declName)
  logInfo m!"{name}: source → shipped design's closed emitted texts (DesignSV, depth 0), checked by the kernel"

elab "#machine_design_svN " d:ident n:num : command => do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← Command.liftTermElabM <|
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 })
        (generate declName n.getNat)
  logInfo m!"{name}: source → shipped design's closed emitted texts (DesignSV), checked by the kernel"

end Tools.ShippingShipsDesignSVCommand
