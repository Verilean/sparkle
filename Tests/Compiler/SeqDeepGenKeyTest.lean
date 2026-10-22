import Tests.Compiler.SeqDeepGenArgsTest
-- BUILT (unit SR3v): k5 exit 0.
-- SCOPE (binding, unit SR3v): the depth-2 generator now numbers the groups of the old generated `hcalls` by the old generator's FULL key
-- (callee, argument lets, the call's argument Signals read from `machineExt`/`machineExtB`), not by the argument list alone, and refuses up
-- front if the key cannot be computed or the group count differs from the `gfL` bundles of the old term.  Concrete examples only:
--   * `tf1`, `tf2`, `tf3`: two calls of `wrap` whose arguments are expressions / constants (generated; groups ASSERTED below);
--   * `tf4`: the CHILD `wrap3` calls the leaf `acc` twice with different arguments (generated; whole conclusion in SeqDeepGenKeyConclTest).
-- A case with EQUAL argument-let lists but DIFFERENT argument Signals could NOT be constructed from the surface language (an expression or a
-- constant argument becomes its own let, so a different Signal gives a different let list): the full key then coincides with the argument list
-- on every example here, and the shifted-numbering case is NOT exercised by a test.  The refusal paths (Signal unreadable / group count
-- mismatch) are not triggered by any test either.
namespace Tests.Compiler.SeqDeepGenKeyTest
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Sparkle.Tests.Compiler.ShippingChildBoundaryTest
open Tests.Compiler.SeqDeepGenInstTest

def tf1 (en : Signal defaultDomain Bool) (v w : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let m := wrap (v + w) w
    let m2 := wrap (v - w) w
    r <~ Signal.mux (m.odd &&& m2.odd &&& en) (rs + v) rs
    return rs

#machine_endpoint tf1

def tf2 (en : Signal defaultDomain Bool) (v w : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let a := v + w
    let m := wrap a w
    let m2 := wrap a v
    r <~ Signal.mux (m.odd &&& m2.odd &&& en) (rs + v) rs
    return rs

#machine_endpoint tf2

set_option maxHeartbeats 0 in
#machine_design_svNR Tests.Compiler.SeqDeepGenKeyTest.tf1 2
set_option maxHeartbeats 0 in
#machine_seq_parent_endpoint Tests.Compiler.SeqDeepGenKeyTest.tf1
set_option maxHeartbeats 0 in
#machine_design_svNR Tests.Compiler.SeqDeepGenKeyTest.tf2 2
set_option maxHeartbeats 0 in
#machine_seq_parent_endpoint Tests.Compiler.SeqDeepGenKeyTest.tf2

def tf3 (en : Signal defaultDomain Bool) (v w : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let m := wrap (Signal.pure 1#8) w
    let m2 := wrap (Signal.pure 2#8) w
    r <~ Signal.mux (m.odd &&& m2.odd &&& en) (rs + v) rs
    return rs

#machine_endpoint tf3

/-- the child calls the leaf SEVERAL times (two calls of `acc`, different arguments) -/
@[hardware_module] def wrap3 {dom : DomainConfig} (x y : Signal dom (BitVec 8)) : AccOut dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let a := acc y
    let b := acc x
    r <~ a.s + b.s
    return ({ s := rs, odd := a.odd &&& b.odd } : AccOut dom)

def tf4 (en : Signal defaultDomain Bool) (v w : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let m := wrap3 v w
    r <~ Signal.mux (m.odd &&& en) (rs + v) rs
    return rs

#machine_endpoint tf4

set_option maxHeartbeats 0 in
#machine_design_svNR Tests.Compiler.SeqDeepGenKeyTest.tf3 2
set_option maxHeartbeats 0 in
#machine_seq_parent_endpoint Tests.Compiler.SeqDeepGenKeyTest.tf3
set_option maxHeartbeats 0 in
#machine_design_svNR Tests.Compiler.SeqDeepGenKeyTest.tf4 2
set_option maxHeartbeats 0 in
#machine_seq_parent_endpoint Tests.Compiler.SeqDeepGenKeyTest.tf4

theorem tf1_args : tf1.machineData.shape.insts.map (·.2.1) = [[0, 1], [0, 1], [2, 1], [2, 1]] := by decide
theorem tf2_args : tf2.machineData.shape.insts.map (·.2.1) = [[0, 1], [0, 1], [0, 2], [0, 2]] := by decide
theorem tf3_args : tf3.machineData.shape.insts.map (·.2.1) = [[0, 1], [0, 1], [2, 1], [2, 1]] := by decide
theorem wrap3_args : wrap3.machineData.shape.insts.map (·.2.1) = [[0], [0], [1], [1]] := by decide
theorem tf4_args : tf4.machineData.shape.insts.map (·.2.1) = [[0, 1], [0, 1]] := by decide

open Lean Meta Elab Command in
def groupsOf (fn C : Name) (al : List (List Nat)) : MetaM (List Nat × List (List Nat)) := do
  match ← Tools.ShippingSeqParentGenD2.oldGroupKeys fn C 3 al with
  | .ok r => pure r
  | .error e => throwError "key not computed: {e}"

-- the recomputed full key and the group count of the OLD generated term agree on every example
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let wrapN := ``Tests.Compiler.SeqDeepGenInstTest.wrap
  for (fn, C, al, inst, grp) in [
      (``tf1, wrapN, [[0,1],[0,1],[2,1],[2,1]], [0,0,1,1], [[0,1],[2,1]]),
      (``tf2, wrapN, [[0,1],[0,1],[0,2],[0,2]], [0,0,1,1], [[0,1],[0,2]]),
      (``tf3, wrapN, [[0,1],[0,1],[2,1],[2,1]], [0,0,1,1], [[0,1],[2,1]]),
      (``tf4, ``wrap3, [[0,1],[0,1]], [0,0], [[0,1]])] do
    let (i, g) ← groupsOf fn C al
    unless i == inst && g == grp do throwError "SR3v AUDIT FAILED: {fn}: groups {i} {g}, expected {inst} {grp}"
    let n ← Tools.ShippingSeqParentGenD2.oldGroupCount (fn ++ `machine_composedNR2)
    unless n == grp.length do throwError "SR3v AUDIT FAILED: {fn}: old term has {n} gfL groups, expected {grp.length}"
  logInfo m!"SR3v: full-key groups of tf1/tf2/tf3/tf4 asserted, and equal to the gfL group counts of the old generated terms"

end Tests.Compiler.SeqDeepGenKeyTest
