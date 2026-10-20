import Tools.ShippingLeafInputWidths
import Tools.ShippingLeafEntryCommand
-- BUILT by the integrator: ld1 exit 1 (test helper name), ld2 exit 1 (audit flagged the uniqueness clause's DesignSV run; refined), ld3 exit 0 (608 jobs). Integrator-written.

/-! # `#machine_leaf_design_closed f`: the leaf design endpoint with no checker antecedent

For a leaf register machine `f` with `f.machine_ships_wired` (from `#machine_endpoint`) and
`f.machine_leafKid` / `f.machine_closes` (from `#machine_leaf_entry f`), adds

    f.machine_design_closed :
      ∀ {mctx mref cctx cref w w' b design},
        RunsTo (synthesizeCombinational f) … (b, design) w' →
        MachineDefines … f f.machineData.shape →
        ChildBnd mref cref w →
        ∃ raw D, (b = drop raw ∨ b = mergeChecked (drop raw)) ∧ ∃ ids cache regs, (MachineWired …) ∧
          ∀ typed stream, T, mems, SourceInputs … ∧ ∃ envsO, (runs of checkedOptimize b from
          tgtSt2 … (slotInit …)) ∧ DesignSV … ∧ length ∧ outputs = source ∧ uniqueness

the kernel-checked application of `Tools.ShippingLeafInputWidths.leaf_sat_design_closed5` to the
endpoint's first 11 arguments (taken from `f.machine_ships_wired`'s value), the two data conditions
(`hlen`, `hinitW`, decided), `f.machine_closes` and `f.machine_leafKid`. The statement is the inferred type.
Refuses (throws) when an ingredient is absent or a data condition does not decide. -/
namespace Tools.ShippingLeafDesignClosedCommand
open Lean Elab Command Meta

def generate (f : Name) : TermElabM Name := do
  let wiredN := f ++ `machine_ships_wired
  let ci ← getConstInfo wiredN
  let some v := ci.value? (allowOpaque := true) | throwError "{wiredN}: no value"
  let some app := v.find? (·.isAppOf ``Tools.ShippingMachineShipsW.machine_ships_wired)
    | throwError "{wiredN}: no machine_ships_wired application in its value"
  let args := app.getAppArgs
  if args.size < 11 then throwError "{wiredN}: only {args.size} arguments"
  let pre := args.extract 0 11
  if pre.any (·.hasLooseBVars) then throwError "{wiredN}: open arguments"
  let e0 := mkAppN (mkConst ``Tools.ShippingLeafInputWidths.leaf_sat_design_closed5
    app.getAppFn.constLevels!) pre
  let t0 ← whnf (← inferType e0)
  let .forallE _ tLen _ _ := t0 | throwError "closed5: hlen binder expected"
  let e1 := mkApp e0 (← mkDecideProof tLen)
  let t1 ← whnf (← inferType e1)
  let .forallE _ tInit _ _ := t1 | throwError "closed5: hinitW binder expected"
  let e2 := mkApp e1 (← mkDecideProof tInit)
  let closesN := f ++ `machine_closes
  let kidN := f ++ `machine_leafKid
  unless (← getEnv).contains closesN do throwError "{closesN} absent (run #machine_leaf_entry {f})"
  unless (← getEnv).contains kidN do throwError "{kidN} absent (run #machine_leaf_entry {f})"
  -- binders of closed5 after the data: {mctx mref cctx cref w w' b design} hr entry closes K hbnd
  let ty2 ← inferType e2
  let val ← forallTelescopeReducing ty2 fun xs _ => do
    if xs.size < 13 then throwError "closed5: {xs.size} binders, 13 expected"
    let mctx := xs[0]!; let mref := xs[1]!; let cctx := xs[2]!; let cref := xs[3]!
    let hr := xs[8]!; let entry := xs[9]!; let hbnd := xs[12]!
    let closes ← mkAppOptM closesN #[mctx, mref, cctx, cref]
    let kid ← mkAppOptM kidN #[none, none, none, none, entry]
    let body := mkAppN e2 #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, xs[4]!, xs[5]!, xs[6]!, xs[7]!,
      hr, entry, closes, kid, hbnd]
    mkLambdaFVars (xs.extract 0 8 ++ #[hr, entry, hbnd]) body
  let val ← instantiateMVars val
  let ty ← instantiateMVars (← inferType val)
  let n := f ++ `machine_design_closed
  addDecl (.thmDecl { name := n, levelParams := ci.levelParams, type := ty, value := val })
  return n

elab "#machine_leaf_design_closed " f:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
  let n ← liftTermElabM <| generate f
  logInfo m!"{n}: leaf design endpoint at wofOf (checkedOptimize b), no checker antecedent, checked by the kernel"

end Tools.ShippingLeafDesignClosedCommand
