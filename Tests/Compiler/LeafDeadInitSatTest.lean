import Tests.Compiler.LeafDeadInitTest
import Tools.ShippingLeafSat

/-! # `dead7`'s run hypotheses discharged by theorem (`leaf_sat`)

BUILT by the integrator: ls1 exit 0 (574 jobs; audit passed). Registered in `Tests.AllTests` (all8 exit 0, 1453 jobs).

`dead7` (Tests/Compiler/LeafDeadInitTest.lean): a leaf with registers of reset values 5 and 7
whose optimizer removes the reset-7 register (asserted there). Here
`Tools.ShippingLeafSat.leaf_sat` is applied at `dead7`'s data and wired endpoint (`soundL`,
read off the value of `dead7.machine_ships_wired`, as `dead7.machine_ships_wiredS` is built),
with the data conditions `hlen` and `hinitW` decided by the kernel. The result
`dead7.machine_sat`:

* premises: only the outer run `hr` (`synthesizeCombinational`), `MachineDefines` and
  `MachineCloses` (with their implicit contexts);
* conclusion: for every wof passing the emitted-text checks, every typed input stream and
  every `T`, the stream's seeding carries the source inputs and the optimized module and its
  emitted Verilog, run from `tgtSt2 … (slotInit regs slots)` (`0` at the removed register),
  show the source.

AUDIT (throws): standard axioms; no premise mentions `seedIn`, `Bounded`, `slotInit`,
`SlotField.init`, `streamEnv`.

Writing-time guesses: `Meta.mkDecideProof` for `hlen` / `hinitW` checked by the kernel at
`dead7.machineData` (the instance test used `decide`/`decide +kernel`); `leaf_sat` has no
universe parameters beyond those of `machine_ships_wired`'s application.
-/
namespace Sparkle.Tests.Compiler.LeafDeadInitSatTest
open Lean Elab Command Meta

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.LeafDeadInitTest.dead7
  let wiredN := f ++ `machine_ships_wired
  let ci ← getConstInfo wiredN
  let some v := ci.value? (allowOpaque := true) | throwError "{wiredN}: no value"
  let some app := v.find? (·.isAppOf ``Tools.ShippingMachineShipsW.machine_ships_wired)
    | throwError "{wiredN}: no machine_ships_wired application in its value"
  let args := app.getAppArgs
  if args.size < 11 then throwError "{wiredN}: only {args.size} arguments"
  let pre := args.extract 0 11
  if pre.any (·.hasLooseBVars) then throwError "{wiredN}: open arguments"
  let e0 := mkAppN (mkConst ``Tools.ShippingLeafSat.leaf_sat app.getAppFn.constLevels!) pre
  -- the two data conditions, decided
  let t0 ← whnf (← inferType e0)
  let .forallE _ tLen _ _ := t0 | throwError "leaf_sat: hlen binder expected"
  let pLen ← mkDecideProof tLen
  let e1 := mkApp e0 pLen
  let t1 ← whnf (← inferType e1)
  let .forallE _ tInit _ _ := t1 | throwError "leaf_sat: hinitW binder expected"
  let pInit ← mkDecideProof tInit
  let e := mkApp e1 pInit
  let ty ← instantiateMVars (← inferType e)
  let n := f ++ `machine_sat
  addDecl (.thmDecl { name := n, levelParams := ci.levelParams, type := ty, value := e })
  Sparkle.Tests.Compiler.LeafDeadInitTest.stdAx n
  -- the premises: no seeding, bound, start state or init equation
  let bad := [``Tools.ShippingSeqOptSoundness.seedIn, ``Sparkle.IR.Semantics.Bounded,
    ``Tools.ShippingSatAssemblyS.slotInit, ``Sparkle.IR.Machine.SlotField.init,
    ``Tools.ShippingSatInputs.streamEnv, ``Tools.ShippingLeafSat.leafIns]
  let premTys ← forallTelescope ty fun xs _ => xs.mapM fun x => inferType x
  for pt in premTys do
    for k in bad do
      if (pt.find? (fun e => e.isConstOf k)).isSome then
        throwError "{n}: a premise mentions {k}: {pt}"
  logInfo m!"LEAFDEADSAT: {n} kernel-checked (leaf_sat at dead7's data and soundL; hlen, hinitW decided), standard axioms, {premTys.size} premises, none mentions {bad}"

end Sparkle.Tests.Compiler.LeafDeadInitSatTest
