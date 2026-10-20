import Sparkle
import Lean.Util.CollectAxioms
import Tools.ShippingMachineCommand
import Tools.ShippingMachineShipsS
import Tools.ShippingDesignSV

/-! # A leaf register machine whose optimizer REMOVES a nonzero-init register

BUILT by the integrator: lf2 exit 1 (stuck `Decidable` instance; theorem value needs `value? (allowOpaque := true)`), lf3 exit 1 (same `Decidable`, -> `Nat.blt`), lf4 exit 0 (370 jobs) (round par/leafnz, base aa35e8a6). Registered in `Tests.AllTests` (all7).

`dead7` (copied from Tests/Compiler/NonzeroInitProbe.lean into this namespace): two
registers, reset values 5 and 7; the output reads only the first. Probe nz3 measured that
`checkedOptimize b` drops the reset-7 register (`weS opt = 0`), so the one-state
`MachineShips` (`f.machine_ships_wired`) is vacuous here at the emitter's widths
(docs/parallel/leaf-nonzero-init.md §2).

Steps:
1. `#machine_endpoint dead7` (the leaf endpoint, `dead7.machine_ships_wired`).
2. ASSERT on the compiled module: `simpleBody b = false`; `refineCheck b opt = true` with
   `opt = checkedOptimize b ≠ b`; some register of `b` has a NONZERO reset value, is not a
   register of `opt` and has `weS opt r = 0` (the removal); `tgtSt b opt st0 r = 0` and every
   name's `tgtSt` value at the slot-init state is below `2 ^ weS opt` on the registers of
   `b` (evaluated), while `st0 r = 7` is not (the old obstacle, evaluated).
3. `dead7.machine_ships_wiredS`: `machine_ships_wiredS data soundL …` rebuilt from the
   arguments of `machine_ships_wired` inside `dead7.machine_ships_wired`'s value and added
   by the kernel; standard axioms.

Writing-time guesses: that `#machine_endpoint` produces `dead7.machine_ships_wired` for this
shape (pair loop, `Signal.fst` outside the loop); that its value contains the application
`Tools.ShippingMachineShipsW.machine_ships_wired d soundL hnoI hsl hSS houtTy` with closed
first 11 arguments.

OPEN (not shown here): a leaf "sat" lemma discharging every source hypothesis of
`MachineShipsS` at `st0 = slot inits` as a theorem (step 2 evaluates it instead).
-/
namespace Sparkle.Tests.Compiler.LeafDeadInitTest
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- Leaf: two registers; the second (reset 7) never reaches the output. -/
def dead7 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 8 × BitVec 8)) =>
    let a := Signal.fst st
    let d := Signal.snd st
    bundle2
      (Signal.register 5#8 (Signal.mux en (a + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))) a))
      (Signal.register 7#8 (d + (Signal.pure 3#8 : Signal defaultDomain (BitVec 8))))
  Signal.fst st

end Sparkle.Tests.Compiler.LeafDeadInitTest

/-! ## Step 1 -/

#machine_endpoint Sparkle.Tests.Compiler.LeafDeadInitTest.dead7

namespace Sparkle.Tests.Compiler.LeafDeadInitTest
open Lean Elab Command Meta

/-- Throw unless `n` exists and depends only on the standard axioms. -/
def stdAx (n : Name) : CoreM Unit := do
  unless (← getEnv).contains n do throwError "{n}: absent"
  let axs ← Lean.collectAxioms n
  for a in axs do
    unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
      throwError "{n}: non-standard axiom {a}"

/-! ## Step 2: the optimizer removes the reset-7 register (ASSERTED) -/

open Sparkle.Compiler.Elab in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let _saved ← Meta.saveState
  try
    sparkleSynthDepth.set 0
    sparkleChildCache.set {}
    let (b, _) ← synthesizeCombinational ``dead7
    let opt := Sparkle.IR.OptCheck.checkedOptimize b
    unless Sparkle.IR.OptCheck.simpleBody b == false do throwError "LEAFDEAD: simpleBody b"
    unless Sparkle.IR.RefineCheck.hierGate b == false do throwError "LEAFDEAD: hierGate b (not a leaf)"
    unless Sparkle.IR.RefineCheck.refineCheck b opt do
      throwError "LEAFDEAD: refineCheck b opt = false (optimizer output rejected)"
    if opt == b then throwError "LEAFDEAD: checkedOptimize b = b (nothing removed)"
    let regsB := Sparkle.IR.OptCheck.seqRegs b
    let keptO := (Sparkle.IR.OptCheck.seqRegs opt).map (·.1)
    -- the slot-init start state of the source
    let st0 : String → Nat := fun n =>
      match regsB.find? (·.1 == n) with
      | some r => r.2.2.2.2.toNat
      | none => 0
    let removed := regsB.filter fun r =>
      r.2.2.2.2 != 0 && !keptO.contains r.1 && Tools.ShippingDesignSV.weS opt r.1 == 0
    if removed.isEmpty then
      throwError "LEAFDEAD: no nonzero-init register of b is removed by checkedOptimize"
    for r in removed do
      let t := Tools.ShippingMachineShipsS.tgtSt b opt st0 r.1
      unless t == 0 do throwError "LEAFDEAD: tgtSt at removed {r.1} = {t}"
      -- the old one-state obstacle: st0 r < 2 ^ weS opt r is false
      if Nat.blt (st0 r.1) ((2 : Nat) ^ Tools.ShippingDesignSV.weS opt r.1) then
        throwError "LEAFDEAD: the one-state bound holds at {r.1} (no obstacle)"
    for r in regsB do
      let t := Tools.ShippingMachineShipsS.tgtSt b opt st0 r.1
      unless Nat.blt t ((2 : Nat) ^ Tools.ShippingDesignSV.weS opt r.1) do
        throwError "LEAFDEAD: tgtSt not bounded at {r.1}"
    logInfo m!"LEAFDEAD: removed nonzero-init registers {removed.map fun r => (r.1, r.2.2.2.2)}; kept {keptO}; refineCheck b opt = true; tgtSt = 0 there and bounded on every register of b; one-state bound fails there"
  finally
    sparkleSynthDepth.set 0
    sparkleChildCache.set {}

/-! ## Step 3: the two-state leaf theorem for `dead7`, kernel-checked -/

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let f := ``dead7
  let wiredN := f ++ `machine_ships_wired
  let ci ← getConstInfo wiredN
  let some v := ci.value? (allowOpaque := true) | throwError "{wiredN}: no value"
  let some app := v.find? (·.isAppOf ``Tools.ShippingMachineShipsW.machine_ships_wired)
    | throwError "{wiredN}: no machine_ships_wired application in its value"
  let args := app.getAppArgs
  if args.size < 11 then throwError "{wiredN}: only {args.size} arguments"
  let pre := args.extract 0 11
  if pre.any (·.hasLooseBVars) then throwError "{wiredN}: open arguments"
  let e := mkAppN (mkConst ``Tools.ShippingMachineShipsS.machine_ships_wiredS
    app.getAppFn.constLevels!) pre
  let ty ← instantiateMVars (← inferType e)
  let n := f ++ `machine_ships_wiredS
  addDecl (.thmDecl { name := n, levelParams := ci.levelParams, type := ty, value := e })
  stdAx n
  logInfo m!"LEAFDEAD: {n} kernel-checked (machine_ships_wiredS at the endpoint's data and soundL), standard axioms"

end Sparkle.Tests.Compiler.LeafDeadInitTest
