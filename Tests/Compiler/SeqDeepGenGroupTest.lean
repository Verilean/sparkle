import Tests.Compiler.SeqDeepGenDiffTest
import Tests.Compiler.SeqDeepGenKeyTest
-- BUILT (unit SR3w): see the report (run names and exits).
-- SCOPE (binding; per the review of par/int-r44 on SR3v): DIRECT tests of the group-numbering helpers of the depth-2 generators.
--   * `groupPartition` (PURE, `Tools/ShippingSeqParentGenD2.lean`): same argument list but DIFFERENT Signals gives different groups; a different
--     CALLEE gives a different group; the same group COUNT can come with a DIFFERENT partition (so a count check alone does not detect a
--     different partition); interleaved groups.
--   * `groupKeysOf` (PURE): the key of each group of a given partition; the numbering is kept as given; disagreeing members / gaps / length mismatches
--     are rejected.
--   * `oldInstGroups` (reads the partition from the old generated term, structural: the chain `forall_getElem?_cons`, the `gf*` binder names), which the
--     generators now USE as their numbering: its result equals the recomputed call-argument approximation (a diagnostic only) on every example below (`oldGroupKeys` / `oldGroupKeysM`); its error branches
--     (a name that is no theorem; a theorem without `machine_linkedT_callsRN`) are exercised.
-- A case with EQUAL argument-let lists but DIFFERENT call Signals could NOT be built from the surface language (an expression or a constant
-- argument becomes its own let), so the "same argument list, different Signals" case is a test of the PURE helper on synthetic keys, not of real code.
-- What is NOT tested: a real old term whose partition differs from the approximation (none was found), the refusal text of `analyse` on such a
-- mismatch (the comparison is inline), and the reading of an old term of a different shape.
namespace Tests.Compiler.SeqDeepGenGroupTest
open Tools.ShippingSeqParentGenD2 (groupPartition groupKeysOf oldInstGroups oldGroupKeys)

/-- A stand-in key: (callee, argument lets, the call's argument Signals as strings). -/
abbrev K := String × List Nat × List String

-- same argument list, DIFFERENT Signals: two groups (the argument list alone would give one)
theorem sig_differs : (groupPartition ([("w", [0, 1], ["a", "b"]), ("w", [0, 1], ["a", "c"])] : List K)).1 = [0, 1] := by decide
theorem sig_same : (groupPartition ([("w", [0, 1], ["a", "b"]), ("w", [0, 1], ["a", "b"])] : List K)).1 = [0, 0] := by decide
-- a different CALLEE with the same arguments: two groups
theorem callee_differs : (groupPartition ([("w", [0, 1], ["a"]), ("w2", [0, 1], ["a"])] : List K)).1 = [0, 1] := by decide
-- the same COUNT, a DIFFERENT partition
theorem same_count : (groupPartition [1, 1, 2]).2.length = (groupPartition [1, 2, 2]).2.length := by decide
theorem diff_partition : (groupPartition [1, 1, 2]).1 ≠ (groupPartition [1, 2, 2]).1 := by decide
theorem part_a : (groupPartition [1, 1, 2]).1 = [0, 0, 1] := by decide
theorem part_b : (groupPartition [1, 2, 2]).1 = [0, 1, 1] := by decide
-- interleaved groups, and the distinct keys in order of first occurrence
theorem interleaved : groupPartition [7, 8, 7, 8, 9] = ([0, 1, 0, 1, 2], [7, 8, 9]) := by decide
theorem empty_case : groupPartition ([] : List Nat) = ([], []) := by decide

-- `groupKeysOf`: the key of each group of a GIVEN partition (the generators now take the partition from the old term)
theorem gk_basic : groupKeysOf [0, 0, 1] [[0, 1], [0, 1], [1, 0]] = some [[0, 1], [1, 0]] := by decide
-- the numbering of the given partition is kept AS IS (here NOT first-occurrence order)
theorem gk_kept : groupKeysOf [1, 0, 1] [[5], [7], [5]] = some [[7], [5]] := by decide
-- members of one group with different keys: rejected
theorem gk_disagree : groupKeysOf [0, 0] [[0, 1], [1, 0]] = (none : Option (List (List Nat))) := by decide
-- an unused group index below the maximum: rejected
theorem gk_gap : groupKeysOf [0, 2] [[1], [2]] = (none : Option (List (List Nat))) := by decide
-- length mismatch: rejected
theorem gk_len : groupKeysOf [0] [[1], [2]] = (none : Option (List (List Nat))) := by decide

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  -- the partition READ from the old generated term equals the recomputed call-argument approximation, example by example
  let wrapN := ``Tests.Compiler.SeqDeepGenInstTest.wrap
  for (fn, C, kP, al, expected) in [
      (``Tests.Compiler.SeqDeepGenInstTest.topw, wrapN, 3, [[0,1],[0,1]], [0,0]),
      (``Tests.Compiler.SeqDeepGenArgsTest.topargs, wrapN, 3, [[0,1],[0,1],[1,0],[1,0]], [0,0,1,1]),
      (``Tests.Compiler.SeqDeepGenArgsTest.toptwo, wrapN, 3, [[0,1],[0,1],[1,0],[1,0],[0,0],[0,0]], [0,0,1,1,2,2]),
      (``Tests.Compiler.SeqDeepGenKeyTest.tf1, wrapN, 3, [[0,1],[0,1],[2,1],[2,1]], [0,0,1,1]),
      (``Tests.Compiler.SeqDeepGenKeyTest.tf2, wrapN, 3, [[0,1],[0,1],[0,2],[0,2]], [0,0,1,1])] do
    let .ok og ← oldInstGroups (fn ++ `machine_composedNR2) | throwError "SR3w AUDIT FAILED: {fn}: the old partition cannot be read"
    let .ok (inst, _) ← oldGroupKeys fn C kP al | throwError "SR3w AUDIT FAILED: {fn}: the key cannot be computed"
    unless og == expected && inst == expected do
      throwError "SR3w AUDIT FAILED: {fn}: old partition {og}, recomputed {inst}, expected {expected}"
  -- the several-callees keys of `topdiff2` / `topdiff3`
  let cs3 := [``Tests.Compiler.SeqDeepGenInstTest.wrap, ``Tests.Compiler.SeqDeepGenInstTest.wrap, ``Tests.Compiler.SeqDeepGenDiffTest.wrap2,
    ``Tests.Compiler.SeqDeepGenDiffTest.wrap2, ``Tests.Compiler.SeqDeepGenInstTest.wrap, ``Tests.Compiler.SeqDeepGenInstTest.wrap,
    ``Tests.Compiler.SeqDeepGenDiffTest.wrap2, ``Tests.Compiler.SeqDeepGenDiffTest.wrap2]
  let al3 := [[0,1],[0,1],[1,0],[1,0],[0,0],[0,0],[0,1],[0,1]]
  let fn3 := ``Tests.Compiler.SeqDeepGenDiffTest.topdiff3
  let .ok og3 ← oldInstGroups (fn3 ++ `machine_composedNR2) | throwError "SR3w AUDIT FAILED: topdiff3: the old partition cannot be read"
  let .ok (inst3, grp3) ← Tools.ShippingSeqParentGenD2M.oldGroupKeysM fn3 cs3 3 al3 | throwError "SR3w AUDIT FAILED: topdiff3: the key cannot be computed"
  unless og3 == [0,0,1,1,2,2,3,3] && inst3 == og3 && grp3.length == 4 do
    throwError "SR3w AUDIT FAILED: topdiff3: old {og3}, recomputed {inst3} {grp3}"
  -- the error branches of the reader
  match ← oldInstGroups ``Nat.add_comm with
  | .error _ => pure ()
  | .ok r => throwError "SR3w AUDIT FAILED: a theorem without the consumer head was read: {r}"
  match ← oldInstGroups ``Nat.zero_add with
  | .error _ => pure ()
  | .ok r => throwError "SR3w AUDIT FAILED: a theorem without the consumer head was read: {r}"
  match ← oldInstGroups ``Nat.succ with
  | .error _ => pure ()
  | .ok r => throwError "SR3w AUDIT FAILED: a non-theorem was read: {r}"
  logInfo m!"SR3w: the partition read from the old term equals the recomputed one on topw/topargs/toptwo/tf1/tf2/topdiff3; the reader's error branches are exercised; the pure helper separates different Signals / callees and keeps same-count partitions apart"

end Tests.Compiler.SeqDeepGenGroupTest
