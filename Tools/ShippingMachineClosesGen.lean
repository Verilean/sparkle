import Tools.ShippingMachineClosesData
import Tools.ShippingReflectCtx

/-! # Generating `f.machine_closes`

For a declaration with a machine endpoint (`f.machineData`, `f.machine_ok`,
`f.machine_body`): the theorem

  `f.machine_closes : ∀ mctx mref cctx cref, MachineCloses mctx mref cctx cref f f.machineData.shape`

where it is provable from the data (`closes_of_data`: no call, the check
`MachineData.letsOk`, decided by the kernel), and the endpoint theorems with
their `MachineCloses` premise discharged by it. Where it is not, nothing is
added and the premise stays in the endpoint. -/
namespace Tools.ShippingMachineClosesGen
open Lean Meta
open Tools.ShippingMachineAuto Tools.ShippingMachineEntry

/-- `c.machine_closes`, generated if it is not there; `none` where the data
do not give it (a shape with calls, a `let` that is the variable of a `let`
with a driven field, or no machine endpoint). -/
def closesTheorem? (c : Name) : MetaM (Option Name) := do
  let name := c ++ `machine_closes
  if (← getEnv).contains name then return some name
  unless (← getEnv).contains (c ++ `machineData) do return none
  let saved ← getEnv
  let d := mkConst (c ++ `machineData)
  let shape ← mkAppM ``MachineData.shape #[d]
  let ctxT := #[(`mctx, mkConst ``Lean.Meta.Context),
    (`mref, ← mkAppM ``ST.Ref #[mkConst ``IO.RealWorld, mkConst ``Lean.Meta.State]),
    (`cctx, mkConst ``Lean.Core.Context),
    (`cref, ← mkAppM ``ST.Ref #[mkConst ``IO.RealWorld, mkConst ``Lean.Core.State])]
  let type ← withLocalDeclsDND ctxT fun xs =>
    mkForallFVars xs (mkAppN (mkConst ``MachineCloses) (xs ++ #[toExpr c, shape]))
  let add (value : Lean.Expr) : MetaM Bool := do
    try
      withOptions (fun o => Lean.Elab.async.set o false) do
        addDecl (.thmDecl { name, levelParams := [], type, value })
      for ax in ← Lean.collectAxioms name do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "{name} uses a non-standard axiom: {ax}"
      return true
    catch _ =>
      setEnv saved
      return false
  -- from the endpoint's own checks and `letsOk` (evaluated by the kernel)
  if (← getEnv).contains (c ++ `machine_ok) && (← getEnv).contains (c ++ `machine_body) then
    let ok ← try
        let prop ← mkEq (← mkAppM ``MachineData.letsOk #[d]) (mkConst ``Bool.true)
        let hl ← mkExpectedTypeHint (← mkEqRefl (mkConst ``Bool.true)) prop
        add (mkAppN (mkConst ``Tools.ShippingMachineClosesData.closes_of_data)
          #[toExpr c, d, mkConst (c ++ `machine_ok), mkConst (c ++ `machine_body), hl])
      catch _ => pure false
    if ok then return some name
  -- no `let` and no call (`machineCloses_of_noLets`)
  if ← Tools.ShippingReflectCtx.closesFree shape then
    let ok ← try
        let value ← withLocalDeclsDND ctxT fun xs => do
          let lets ← mkAppM ``Sparkle.IR.Machine.Layout.lets
            #[← mkAppM ``Sparkle.Compiler.Elab.MachineShape.layout #[shape]]
          let insts ← mkAppM ``Sparkle.Compiler.Elab.MachineShape.insts #[shape]
          let p1 ← mkEq lets (mkNatLit 0)
          let p2 ← mkEq insts (← mkAppOptM ``List.nil #[some (← whnfR (← inferType insts)).appArg!])
          mkLambdaFVars xs (← mkAppOptM ``machineCloses_of_noLets
            #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, toExpr c, shape, ← mkDecideProof p1, ← mkDecideProof p2])
        add value
      catch _ => pure false
    if ok then return some name
  return none

/-- The theorem `thm` (an endpoint of `c`) with its `MachineCloses` premises
about `c` discharged by `c.machine_closes`: added as `newName`. `false`
where `thm` has no such premise or `c.machine_closes` is not there. -/
def closeEndpoint (c thm newName : Name) : MetaM Bool := do
  if (← getEnv).contains newName then return true
  let some cl ← closesTheorem? c | return false
  let info ← getConstInfo thm
  let saved ← getEnv
  try
    let value? ← forallTelescope info.type fun xs _ => do
      let mut keep : Array Lean.Expr := #[]
      let mut olds : Array Lean.Expr := #[]
      let mut news : Array Lean.Expr := #[]
      for x in xs do
        let t ← instantiateMVars (← inferType x)
        if t.isAppOfArity ``MachineCloses 6 && t.getArg! 4 == toExpr c then
          olds := olds.push x
          news := news.push (mkAppN (mkConst cl) (t.getAppArgs.extract 0 4))
        else keep := keep.push x
      if olds.isEmpty then return none
      let body := (mkAppN (mkConst thm (info.levelParams.map mkLevelParam)) xs).replaceFVars olds news
      return some (← mkLambdaFVars keep body)
    let some value := value? | return false
    let type ← inferType value
    if (type.find? (·.isConstOf ``MachineCloses)).isSome then return false
    withOptions (fun o => Lean.Elab.async.set o false) do
      addDecl (.thmDecl { name := newName, levelParams := info.levelParams, type, value })
    for ax in ← Lean.collectAxioms newName do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{newName} uses a non-standard axiom: {ax}"
    return true
  catch _ =>
    setEnv saved
    return false

/-- `name_closed`. -/
def closedName (thm : Name) : Name :=
  match thm with
  | .str p s => .str p (s ++ "_closed")
  | n => n ++ `closed

open Lean.Elab Lean.Elab.Command in
/-- `#machine_closes f` adds `f.machine_closes` (an error where the data do
not give it) and, for each endpoint of `f` there is, its `_closed` form. -/
elab "#machine_closes " d:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  liftTermElabM do
    let some n ← closesTheorem? c
      | throwError "{c}: MachineCloses is not derived from the data (a call, a `let` that is the variable of a `let` with a driven field, or no machine endpoint)"
    let mut made := #[n]
    for s in [`machine_sound, `machine_ships, `machine_ships_wired, `machine_ships_comb] do
      if (← getEnv).contains (c ++ s) then
        if ← closeEndpoint c (c ++ s) (closedName (c ++ s)) then made := made.push (closedName (c ++ s))
    logInfo m!"{made}: MachineCloses proved from the data"

end Tools.ShippingMachineClosesGen
