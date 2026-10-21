import Tests.Compiler.ParentSeqComposedATest
import Tests.Compiler.ShippingChildBoundaryTest
import Tools.ShippingSeqParentGen
import Tools.ShippingShipsFreeMaskedCommand
-- BUILT (unit SR3l): l5 exit 0 — depth-2 probe on `grand` (REFUSED with a stated reason; old chain svNR2 exists, old noShipsMasked 2 refused), ResetNk n asserted.
-- BUILT (unit SR3k): k6 exit 0 (`parent`, `chained`, and now `two` = two DIFFERENT children cnt/acc, GENERATED, with asserted call-position -> child -> data map).
-- BUILT (unit SR3i): see REPORT-SR3i.md for the run names / exits (build of Tests.Compiler.SeqParentGenTest). In-test audits THROW on failure.
-- SCOPE (binding): `#machine_seq_parent_endpoint f` (Tools/ShippingSeqParentGen.lean) GENERATES, for a declaration `f` of the class stated in that
-- file's header (non-memory parent; every call instance calls a generated sequential LEAF child — one or SEVERAL different child declarations since SR3k; depth n = 1, kD = number of the parent's own inputs),
-- the new-boundary design endpoint `f.epA_endpoint` with the same shape as the hand-wired `parent_noShips_noBdA_dcHL` of units SR3c-SR3h:
-- premises `hr`, `entry`, `closes : True`; `f.epA_Bnd` (existential over O / T : RefLawsATele / AdmCtx / MachineDefines child / JQ start world)
-- stays in the conclusion, NOT a proof that it holds.  Applied here to `parent` (type checked `isDefEq` to the hand-wired endpoint) and to
-- `chained` (the same child `cnt` called twice, the second call's argument another call's field) and (unit SR3k) `two` (two DIFFERENT children).  NOT unconditional semantic equivalence;
-- RealChildA is a history; T is an ADDED boundary; not runtime fit.
namespace Tests.Compiler.SeqParentGenTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest

set_option maxHeartbeats 0 in
#machine_seq_parent_endpoint Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let new := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.epA_endpoint
  let hand := ``Tests.Compiler.ParentSeqComposedATest.parent_noShips_noBdA_dcHL
  let nt := (← getConstInfo new).type
  let ht := (← getConstInfo hand).type
  unless ← isDefEq nt ht do throwError "SR3i AUDIT FAILED: generated parent endpoint differs from the hand-wired parent_noShips_noBdA_dcHL"
  logInfo m!"SR3i: the GENERATED parent endpoint has a type isDefEq to the hand-wired parent_noShips_noBdA_dcHL (its BndA is epA_Bnd unfolded)"

set_option maxHeartbeats 0 in
#machine_seq_parent_endpoint Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained

-- unit SR3k: two DIFFERENT sequential children (`cnt` and `acc`): now GENERATED.  The old generator `#machine_design_svNR` provides the
-- reused pieces (and the old endpoint `two.machine_design_noShipsNoMaskedNR1`, against which the audit compares the conclusion).
set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two 1

-- the OLD endpoint for `two` (the old command takes one `hR_j : MachineDefines` per distinct kid): generated so that the audit compares with it
set_option maxHeartbeats 0 in
#machine_no_ships_masked Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two 1

set_option maxHeartbeats 0 in
#machine_seq_parent_endpoint Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two

-- (`two` has FOUR call instances: one per (call, used output field): cnt twice, acc twice)
theorem two_nm0 : Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.epA_nm 0 = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt := by decide
theorem two_nm1 : Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.epA_nm 1 = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt := by decide
theorem two_nm2 : Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.epA_nm 2 = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc := by decide
theorem two_nm3 : Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.epA_nm 3 = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc := by decide

-- the call position -> child declaration -> that child's data map of `two`, ASSERTED (the second call's data come from `acc`, not `cnt`)
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let two := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two
  let cnt := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let acc := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc
  -- position k ↦ callee: KERNEL-checked theorems below (`two_nm0`, `two_nm1`); here the instance list is also read back
  let callees ← Tools.ShippingSeqParentGen.readNames
    (← Tools.ShippingSeqParentGen.elabText s!"({two}.machineData.shape.insts.map (·.1))")
  unless callees == [cnt, cnt, acc, acc] do throwError "SR3k AUDIT FAILED: call positions of `two` map to {callees}, expected [cnt, cnt, acc, acc]"
  -- the generated key tables at position k are the data of THAT child: `epA_K_j` (the proved equation for child j) mentions
  -- only child j's `epA_nk` / `machineData`, never the other child's
  let mut seen : Array String := #[]
  for (j, c, other) in [(0, cnt, acc), (1, acc, cnt)] do
    let ty := (← getConstInfo (two ++ Name.mkSimple s!"epA_K_{j}")).type
    unless (ty.find? (·.isConstOf (c ++ `epA_nk))).isSome && (ty.find? (·.isConstOf (c ++ `machineData))).isSome do
      throwError "SR3k AUDIT FAILED: epA_K_{j} does not mention the data of {c}"
    if (ty.find? (·.isConstOf (other ++ `epA_nk))).isSome || (ty.find? (·.isConstOf (other ++ `machineData))).isSome then
      throwError "SR3k AUDIT FAILED: epA_K_{j} mentions the data of {other}"
    seen := seen.push s!"child {j} = {c}: epA_K_{j} mentions exactly {c}'s epA_nk / machineData"
  -- the boundary: one `MachineDefines` per distinct child, and both children's `MachineDefines` arguments in the epA_closes hypotheses
  let cl := (← getConstInfo (two ++ `epA_closes)).type
  let hyps ← forallTelescope cl fun xs _ => xs.filterMapM fun x => do
    let t ← inferType x
    if t.getAppFn.isConstOf ``Tools.ShippingMachineEntry.MachineDefines then return some (← ppExpr t).pretty else return none
  unless hyps.size == 2 && (hyps.any fun s => (s.splitOn "cnt").length > 1) && (hyps.any fun s => (s.splitOn "acc").length > 1) do
    throwError "SR3k AUDIT FAILED: epA_closes should ask MachineDefines for exactly cnt and acc, found {hyps}"
  logInfo m!"SR3k: `two` call positions -> children {callees}; {seen}; epA_closes asks exactly one MachineDefines per distinct child: {hyps}. (`chained` repeats ONE child: a single MachineDefines, shared child data; `two` has one per DIFFERENT child.)"

-- unit SR3l: DEPTH 2.  `grand -> mid -> cnt` (Tests/Compiler/ShippingMachineSeqTest.lean) is the corpus's depth-2 sequential hierarchy.
-- OLD chain at depth 2: `#machine_design_svNR grand 2` (heads `kidsMaskedN`, `ResetNk 2`, `machine_linkedT_callsRNA 2`) and the old
-- `#machine_no_ships_masked_try grand 2` (a refusal is LOGGED, not an error; see the log of the build).  The NEW generator REFUSES `grand`
-- with a stated reason (the child `mid` has call instances); the lemma that would be needed is OPEN (message of the command).
set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand 1
set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand 2
set_option maxHeartbeats 0 in
#machine_no_ships_masked_try Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand 2

open Lean Meta Elab Command in
run_cmd do
  let saved := (← get).messages
  elabCommand (← `(command| #machine_seq_parent_endpoint Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand))
  let ms := (← get).messages
  let errs ← ms.toList.filterM fun m => pure (m.severity == .error)
  let txts ← errs.mapM fun m => m.data.toString
  modify fun s => { s with messages := saved }
  unless txts.length == 1 && (txts.head!.splitOn "DEPTH 2 REFUSED").length > 1 &&
      (txts.head!.splitOn "Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid").length > 1 do
    throwError "SR3l AUDIT FAILED: expected exactly one refusal naming the child `mid` (depth 2), got {txts}"
  unless !(← getEnv).contains (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand ++ `epA_endpoint) do
    throwError "SR3l AUDIT FAILED: grand.epA_endpoint exists although refused"
  logInfo m!"SR3l: `grand` (child `mid` calls `cnt`) is REFUSED by #machine_seq_parent_endpoint at depth 2; no grand.epA_endpoint; reason: {txts.head!.take 300}…"

-- unit SR3l (review item 2): the depth <-> `ResetNk n` correspondence, READ from the old generated theorems (type and value): `parent.machine_ships_hierNR1`
-- (parent -> leaf `cnt`: height of the instance tree below the head = 1) carries `ResetNk 1`; `grand.machine_ships_hierNR2` (grand -> mid -> cnt: height 2)
-- carries `ResetNk 2`.  So `n` = number of instance levels beneath the head declaration; the new generator is written for n = 1 only.
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let natAfter (nm : Name) : MetaM (List Nat) := do
    let ci ← getConstInfo nm
    let ty := ci.type
    let mut out : List Nat := []
    let mut todo : Array Expr := #[ty] ++ (match ci.value? with | some v => #[v] | none => #[])
    while !todo.isEmpty do
      let e := todo.back!
      todo := todo.pop
      if e.getAppFn.isConstOf ``Tools.ShippingMachineShipsDepth.ResetNk then
        if let some n := e.getAppArgs[0]? >>= (fun x => x.nat? <|> x.rawNatLit?) then out := n :: out
      match e with
      | .app f a => todo := todo.push f |>.push a
      | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
      | .mdata _ b => todo := todo.push b
      | _ => pure ()
    return out.eraseDups
  let p ← natAfter ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_ships_hierNR1
  let g ← natAfter ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_ships_hierNR2
  unless p == [1] && g == [2] do throwError "SR3l AUDIT FAILED: ResetNk levels: parent {p}, grand {g}, expected [1] and [2]"
  logInfo m!"SR3l: ResetNk n = height of the instance tree below the head: parent (-> cnt) n = {p}, grand (-> mid -> cnt) n = {g}"

#print axioms Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.epA_endpoint
#print axioms Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained.epA_endpoint
#print axioms Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.epA_endpoint

end Tests.Compiler.SeqParentGenTest
