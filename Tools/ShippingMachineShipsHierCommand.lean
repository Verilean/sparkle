import Tools.ShippingMachineSeqCommand
import Tools.ShippingMachineShipsHier

/-! # `#machine_ships_hier f`

For a machine with sequential children whose composed theorem
`f.machine_composedT` is generated (`#machine_composedTS`), the theorem
`f.machine_ships_hier`: `machine_ships_hier` at the one-level step, with
`f`'s wired endpoint for the cleanup facts and its composed theorem (its run
boundaries gathered into one premise). -/
namespace Tools.ShippingMachineShipsHierCommand
open Lean Meta Elab
open Tools.ShippingMachineSeqCommand

/-- `B₀ ∧ (B₁ ∧ …)`, `True` for none. -/
def conj : List Lean.Expr → MetaM Lean.Expr
  | [] => pure (mkConst ``True)
  | [b] => pure b
  | b :: bs => do mkAppM ``And #[b, ← conj bs]

/-- The components of a proof of `conj bs`. -/
def projs (h : Lean.Expr) : List Lean.Expr → MetaM (List Lean.Expr)
  | [] => pure []
  | [_] => pure [h]
  | _ :: bs => do
    let l ← mkAppM ``And.left #[h]
    let r ← mkAppM ``And.right #[h]
    pure (l :: (← projs r bs))

def generate (declName : Name) : MetaM Name := do
  let (headL, args, back?) ← endpointParts declName
  if back?.isSome then throwError "{declName}: a transported endpoint (not yet)"
  let soundL := mkAppN (mkConst headL) args
  let cT := mkConst (declName ++ `machine_composedT)
  let data := mkConst (declName ++ `machineData)
  forallTelescope (← inferType cT) fun ys _ => do
    unless ys.size ≥ 11 do throwError "{declName}: the composed theorem's binders"
    let base := ys.extract 0 11
    let hBs := (ys.extract 11 ys.size).toList
    let m := ys[6]!
    let design := ys[7]!
    let bTys ← hBs.mapM inferType
    let bnd ← conj bTys
    let Bnd ← mkLambdaFVars #[m, design] bnd
    let memF ← mkAppM ``Tools.ConeFold.memFree #[← mkAppM ``Sparkle.IR.AST.Module.body #[m]]
    -- the one-level step with sequential children, or memory reads only
    let (composed, reset) ← withLocalDeclD `hBnd bnd fun hBnd => withLocalDeclD `hm memF fun hm => do
      let ps ← projs hBnd bTys
      let hC := mkAppN cT (base ++ ps.toArray)
      let (inner, reset) ← try
          pure (← mkAppM ``Tools.ShippingMachineShipsHier.composedG_of_T #[hC, hm],
            mkConst ``Tools.ShippingMachineShipsHier.Reset1)
        catch _ =>
          pure (← mkAppM ``Tools.ShippingMachineShipsHier.composedG_of_Tmem #[hC, hm],
            mkConst ``Tools.ShippingMachineShipsHier.ResetM)
      pure (← mkLambdaFVars (base ++ #[hBnd, hm]) inner, reset)
    let KS ← withLocalDeclD `D (mkConst ``Sparkle.IR.AST.Design) fun D =>
      mkLambdaFVars #[D] (mkConst ``Tools.ShippingHierStateG.flatKS)
    let hloc ← withLocalDeclD `D (mkConst ``Sparkle.IR.AST.Design) fun D =>
      mkLambdaFVars #[D] (mkConst ``Tools.ShippingHierStateG.flatKS_local)
    let thm ← mkAppM ``Tools.ShippingMachineShipsHier.machine_ships_hier
      #[KS, hloc, reset, Bnd, data, soundL, composed]
    let ty ← inferType thm
    let .forallE _ hT _ _ ← whnfR ty | throwError "{declName}: the output-width premise"
    let thm := mkApp thm (← mkExpectedTypeHint (← mkDecideProof hT) hT)
    let name := declName ++ `machine_ships_hier
    addDecl (.thmDecl { name, levelParams := [], type := ← inferType thm, value := thm })
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
    return name

elab "#machine_ships_hier " d:ident : command => do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← Command.liftTermElabM <|
    withOptions (fun o => Lean.Elab.async.set o false) (generate declName)
  logInfo m!"{name}: the shipped (optimized) module's stateful linked run shows the source, checked by the kernel"

end Tools.ShippingMachineShipsHierCommand
