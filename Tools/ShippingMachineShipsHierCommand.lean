import Tools.ShippingMachineSeqCommand
import Tools.ShippingMachineShipsHier
import Tools.ShippingMachineTraceX

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

/-- The route of a machine with instances at depth 0, decided ONCE and
shared by the generator and the premise evaluator: memory reads only
(`machine_composedT` from the memory composition, `composedG_of_Tmem`,
reset `ResetM`, bound `kidsMem`) or sequential children
(`composedG_of_T`, `Reset1`, `kidsMixed`). The same test as the composed
theorem's generator (`generateAny`). -/
inductive HierRoute | seq | mem
  deriving BEq, Repr

def hierRoute (declName : Name) : MetaM HierRoute := do
  let r ← Tools.ShippingMachineCommand.readMachine declName
  -- by the entries' ORIGINS, not their names
  if ← Tools.ShippingMachineMemCommand.allMemOrigins r.shape then return .mem else return .seq

/-- `machine_ships_hier` from the composed theorem `cName` (its premises after
the run's eleven binders become the run boundary `Bnd`, in the run's
contexts), as `shipsName`. -/
def generateWith (declName cName shipsName : Name) (headA? : Option Name := none) : MetaM Name := do
  if (← getEnv).contains shipsName then return shipsName
  -- a transported endpoint: the wired twin of its untransported head serves
  -- the cleanup facts; the composed theorem is already transported
  let (headL, args, _) ← endpointParts declName
  let route ← hierRoute declName
  let soundL := mkAppN (mkConst headL) args
  let cT := mkConst cName
  let data := mkConst (declName ++ `machineData)
  forallTelescope (← inferType cT) fun ys _ => do
    unless ys.size ≥ 11 do throwError "{declName}: the composed theorem's binders"
    let base := ys.extract 0 11
    let hBs := (ys.extract 11 ys.size).toList
    let m := ys[6]!
    let design := ys[7]!
    let bTys ← hBs.mapM inferType
    let bnd ← conj bTys
    let Bnd ← mkLambdaFVars #[ys[0]!, ys[1]!, ys[2]!, ys[3]!, ys[4]!, m, design] bnd
    let memF ← mkAppM ``Tools.ConeFold.memFree #[← mkAppM ``Sparkle.IR.AST.Module.body #[m]]
    -- the one-level step with sequential children, or memory reads only
    let (composed, reset) ← withLocalDeclD `hBnd bnd fun hBnd => withLocalDeclD `hm memF fun hm => do
      let ps ← projs hBnd bTys
      let hC := mkAppN cT (base ++ ps.toArray)
      let (inner, reset) ← match route with
        | .seq => pure (← mkAppM ``Tools.ShippingMachineShipsHier.composedG_of_T #[hC, hm],
            mkConst ``Tools.ShippingMachineShipsHier.Reset1)
        | .mem => pure (← mkAppM ``Tools.ShippingMachineShipsHier.composedG_of_Tmem #[hC, hm],
            mkConst ``Tools.ShippingMachineShipsHier.ResetM)
      pure (← mkLambdaFVars (base ++ #[hBnd, hm]) inner, reset)
    -- the children's output bound: decidable checks, `kidsMixed` for sequential
    -- children (memory children among them, instance by instance, with the
    -- read-latch invariant `mixInv`), `kidsMem` for memory children only
    let modT := mkConst ``Sparkle.IR.AST.Module
    let desT := mkConst ``Sparkle.IR.AST.Design
    let isSeq := reset.isConstOf ``Tools.ShippingMachineShipsHier.Reset1
    let (Bd, hBd) ← withLocalDeclD `b modT fun b => withLocalDeclD `D desT fun D => do
      let cm ← mkAppM ``Tools.ShippingMachineLinked.childMap #[← mkAppM ``Sparkle.IR.AST.Design.modules #[D]]
      let body ← mkAppM ``Sparkle.IR.AST.Module.body #[b]
      let chk := if isSeq then ``Tools.ShippingMachineShipsHier.kidsMixed
        else ``Tools.ShippingMachineShipsHier.kidsMem
      let lem := if isSeq then ``Tools.ShippingMachineShipsHier.mixKS_boundedIn
        else ``Tools.ShippingMachineShipsHier.memKS_boundedIn
      let bd ← mkEq (← mkAppM chk #[cm, body]) (mkConst ``Bool.true)
      let Bd ← mkLambdaFVars #[b, D] bd
      let hBd ← withLocalDeclD `h bd fun h => do
        mkLambdaFVars #[b, D, h] (← mkAppM lem #[cm, body, h])
      pure (Bd, hBd)
    let inv := if isSeq then mkConst ``Tools.ShippingMachineShipsHier.mixInv
      else mkConst ``Tools.ShippingMachineShipsHier.memInv
    let hRI := if isSeq then mkConst ``Tools.ShippingMachineShipsHier.reset1_mixInv
      else mkConst ``Tools.ShippingMachineShipsHier.resetM_inv
    let KS ← withLocalDeclD `D desT fun D =>
      mkLambdaFVars #[D] (mkConst ``Tools.ShippingHierStateG.flatKS)
    let hloc ← withLocalDeclD `D desT fun D =>
      mkLambdaFVars #[D] (mkConst ``Tools.ShippingHierStateG.flatKS_local)
    let thm ← do
      if let some headA := headA? then
        -- the closing premise of the composed theorem (`MachineClosesAt`), and
        -- the wired endpoint from the head asking the same, under the run boundary
        let C ← mkLambdaFVars #[ys[0]!, ys[1]!, ys[2]!, ys[3]!] (← inferType ys[10]!)
        let pLA := mkAppN (mkConst headA) args
        let soundA ← forallTelescope (← inferType pLA) fun zs _ => do
          unless zs.size == 12 do throwError "{declName}: the head's binders ({zs.size})"
          let bndT := (Bnd.beta #[zs[0]!, zs[1]!, zs[2]!, zs[3]!, zs[4]!, zs[6]!, zs[7]!]).headBeta
          withLocalDeclD `hB bndT fun hB => do
            let hsynT ← inferType zs[11]!
            let hsyn ← if ← isDefEq bndT hsynT then pure hB else mkAppM ``And.left #[hB]
            let tr ← mkAppM ``Tools.ShippingMachineTraceX.MachineTraceLBX.toLB
              #[(mkAppN pLA zs).replaceFVar zs[11]! hsyn]
            mkLambdaFVars (zs.pop ++ #[hB]) tr
        let thm ← mkAppOptM ``Tools.ShippingMachineShipsHier.machine_ships_hierC
          #[none, KS, hloc, reset, Bnd, C, Bd, inv, hBd, hRI, none, data, none, none, none, none,
            none, none, none, none, none, none, soundA, composed]
        instantiateMVars thm
      else
        mkAppM ``Tools.ShippingMachineShipsHier.machine_ships_hier
          #[KS, hloc, reset, Bnd, Bd, inv, hBd, hRI, data, soundL, composed]
    let ty ← inferType thm
    let .forallE _ hT _ _ ← whnfR ty | throwError "{declName}: the output-width premise"
    let thm := mkApp thm (← mkExpectedTypeHint (← mkDecideProof hT) hT)
    let name := shipsName
    addDecl (.thmDecl { name, levelParams := [], type := ← inferType thm, value := thm })
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
    return name

def generate (declName : Name) : MetaM Name :=
  generateWith declName (declName ++ `machine_composedT) (declName ++ `machine_ships_hier)

elab "#machine_ships_hier " d:ident : command => do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← Command.liftTermElabM <|
    withOptions (fun o => Lean.Elab.async.set o false) (generate declName)
  logInfo m!"{name}: the shipped (optimized) module's stateful linked run shows the source, checked by the kernel"

end Tools.ShippingMachineShipsHierCommand
