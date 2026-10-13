import Lean.Elab.Command
import Tests.Compiler.ShippingCallsCloseDeepTest
import Tests.Compiler.NoPortsTwoTest
import Tests.Compiler.NoPortsMidTest
import Tests.Compiler.NoPortsKidsMid2Test
import Tests.Compiler.NoPortsLoopParentTest
import Tests.Compiler.NoPortsSlotlessEngineOnceTest
import Tests.Compiler.NoPortsSlotlessTwinCallsTest
import Tests.Compiler.NoPortsSlotlessMesh2x2Test

/-! # Fingerprints of the depth endpoints' statements across the switch — SECONDARY check (round par/b-23)

WRITTEN, NOT BUILT. TARGET-ONLY.

A FINGERPRINT comparison: `(Expr.hash of the theorem's type, number of its
leading binders)` for the 51 statements (17 endpoints × `machine_composedNR{n}`,
`machine_ships_hierNR{n}`, `machine_design_svNR{n}`) against a table recorded
on the tree BEFORE the switch. Equal fingerprints are NOT evidence of type
equality or of `isDefEq`, and are never to be reported as such; a differing
hash is a different term, not necessarily a different statement. The check of
the TYPES is `Tests/Compiler/DepthSwitchTypeTest.lean` (old loop against
switched loop by `isDefEq`, on one tree). What this file adds to it: the old
side here comes from the frozen tree `edd9496c` itself, not from old code
kept on the switched tree.

It imports nothing of the generators and elaborates unchanged on `edd9496c`.

## Modes (`DEPTH_PIN_MODE`, read when the file is elaborated)

* `assert` (the DEFAULT, also when the variable is unset): `pins` must have
  exactly 51 rows, no name twice, every endpoint's statement in it with equal
  hash and binder count, no row without a statement. An EMPTY table is an
  ERROR. There is no mode in which this file succeeds without asserting.
* `record`: prints the table as a Lean list literal and then THROWS ("record
  mode is never acceptance"). The build fails on purpose; the table is in
  the build's messages.

A missing theorem, or a count other than 51, is an error in both modes.
The variable is not a build input that lake tracks; a failed build writes no
olean, so the next build elaborates the file again.

## Procedure (the integrator's)

1. On the frozen tree: a worktree at `edd9496c` with only this file added
   (checked out from `par/b-23`);
   `DEPTH_PIN_MODE=record lake build Tests.Compiler.DepthSwitchPinTest`
   (fails on purpose; copy the list from the message).
2. On `par/b-23`: paste the list as the value of `pins`, and write the SHA
   of the tree it was recorded on and the run's id in the comment above
   `pins`. Commit.
3. On `par/b-23`: `lake build Tests.Compiler.DepthSwitchPinTest` (no
   variable) — `DEPTH PIN: 51 of 51 FINGERPRINTS EQUAL …` or an error naming
   each differing statement.

Coverage: the 17 endpoints of `DepthSwitchTypeTest`. The Keccak sponge is
not here.
-/

namespace Tests.Compiler.DepthSwitchPinTest
open Lean

/-- The fingerprints recorded BEFORE the switch: `(theorem, Expr.hash of its
type, number of leading binders)`.

RECORDED ON TREE: poc 25f68ea2 (the depth generator files
`Tools/ShippingMachineDepthCommand.lean` and `…CommandR.lean` are byte-identical to edd9496c there:
`git diff edd9496c 25f68ea2` on them is empty), run `20261013-144930-pin-record` (`DEPTH_PIN_MODE=record`).

An empty table is an ERROR in the default mode. -/
def pins : List (Name × UInt64 × Nat) :=
  [
   (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_composedNR1, 3806310197, 12),
   (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_ships_hierNR1, 2603641402, 11),
   (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_svNR1, 775503135, 11),
   (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained.machine_composedNR1, 1686671341, 12),
   (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained.machine_ships_hierNR1, 3211064729, 11),
   (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained.machine_design_svNR1, 2019951348, 11),
   (`Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_composedNR1, 3703413477, 12),
   (`Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_ships_hierNR1, 2131524145, 11),
   (`Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_design_svNR1, 3188290752, 11),
   (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1, 1903175178, 12),
   (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_ships_hierNR1, 1466245838, 11),
   (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_design_svNR1, 2668439245, 11),
   (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2, 3241457573, 12),
   (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_ships_hierNR2, 1457379173, 11),
   (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_design_svNR2, 2736187016, 11),
   (`Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent.machine_composedNR1, 176614720, 12),
   (`Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent.machine_ships_hierNR1, 2499615973, 11),
   (`Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent.machine_design_svNR1, 3872311708, 11),
   (`Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_composedNR1, 131566955, 12),
   (`Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_ships_hierNR1, 4203154352, 11),
   (`Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_svNR1, 3539619286, 11),
   (`Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_composedNR2, 2454868286, 12),
   (`Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_ships_hierNR2, 736515015, 11),
   (`Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_svNR2, 4088468383, 11),
   (`Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machine_composedNR1, 1587875193, 12),
   (`Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machine_ships_hierNR1, 64110983, 11),
   (`Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machine_design_svNR1, 1628952474, 11),
   (`Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_composedNR1, 3372902074, 12),
   (`Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_ships_hierNR1, 2301282515, 11),
   (`Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_svNR1, 861311906, 11),
   (`Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_composedNR2, 131347659, 12),
   (`Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_ships_hierNR2, 2543048802, 11),
   (`Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_svNR2, 3487859115, 11),
   (`Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_composedNR2, 1001075177, 12),
   (`Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_ships_hierNR2, 3032819790, 11),
   (`Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_svNR2, 1388393982, 11),
   (`Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_composedNR3, 3382395632, 12),
   (`Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_ships_hierNR3, 191630386, 11),
   (`Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_svNR3, 4025646973, 11),
   (`Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_composedNR2, 378977350, 12),
   (`Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_ships_hierNR2, 4224889835, 11),
   (`Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_design_svNR2, 1337744565, 11),
   (`Sparkle.Tests.Compiler.MultiInstance.engineOnce.machine_composedNR1, 3801280993, 12),
   (`Sparkle.Tests.Compiler.MultiInstance.engineOnce.machine_ships_hierNR1, 2697664911, 11),
   (`Sparkle.Tests.Compiler.MultiInstance.engineOnce.machine_design_svNR1, 81458612, 11),
   (`Sparkle.Tests.Compiler.MultiInstance.twinCalls.machine_composedNR1, 3154440017, 12),
   (`Sparkle.Tests.Compiler.MultiInstance.twinCalls.machine_ships_hierNR1, 444608975, 11),
   (`Sparkle.Tests.Compiler.MultiInstance.twinCalls.machine_design_svNR1, 3058126545, 11),
   (`Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machine_composedNR1, 3829026054, 12),
   (`Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machine_ships_hierNR1, 3269999998, 11),
   (`Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machine_design_svNR1, 408867054, 11)]

/-- The declarations and depths whose endpoints are pinned. -/
def endpoints : List (Name × Nat) :=
  [(``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent, 1),
   (``Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained, 1),
   (``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two, 1),
   (``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid, 1),
   (``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand, 2),
   (``Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent, 1),
   (``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH, 1),
   (``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH, 2),
   (``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2, 1),
   (``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1, 1),
   (``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1, 2),
   (``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2, 2),
   (``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2, 3),
   (``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep, 2),
   (``Sparkle.Tests.Compiler.MultiInstance.engineOnce, 1),
   (``Sparkle.Tests.Compiler.MultiInstance.twinCalls, 1),
   (``Sparkle.Tests.Compiler.MultiInstance.mesh2x2, 1)]

/-- The three theorems of an endpoint at depth `dep`. -/
def namesOfEndpoint (f : Name) (dep : Nat) : List Name :=
  [f ++ Name.mkSimple s!"machine_composedNR{dep}",
   f ++ Name.mkSimple s!"machine_ships_hierNR{dep}",
   f ++ Name.mkSimple s!"machine_design_svNR{dep}"]

/-- The number of leading binders of a statement (its premises and the
variables they are about). -/
partial def binderCount : Lean.Expr → Nat
  | Lean.Expr.forallE _ _ b _ => binderCount b + 1
  | Lean.Expr.mdata _ e => binderCount e
  | _ => 0

/-- The fingerprints of the endpoints' statements in this environment. -/
def current : CoreM (List (Name × UInt64 × Nat)) := do
  let env ← getEnv
  let mut cur : List (Name × UInt64 × Nat) := []
  for (f, dep) in endpoints do
    for n in namesOfEndpoint f dep do
      match env.find? n with
      | some (Lean.ConstantInfo.thmInfo ti) =>
        cur := cur ++ [(n, ti.type.hash, binderCount ti.type)]
      | _ => throwError "DEPTH PIN: {n} is not a theorem of this environment (the imported tests no longer generate it — the table would be incomplete)"
  return cur

/-- A table as a Lean list literal (the value of `pins`). -/
def tableText (t : List (Name × UInt64 × Nat)) : String :=
  let rows : List String := t.map fun (row : Name × UInt64 × Nat) =>
    s!"   (`{row.1}, {row.2.1.toNat}, {row.2.2})"
  "  [\n" ++ ",\n".intercalate rows ++ "]"

end Tests.Compiler.DepthSwitchPinTest

run_cmd Lean.Elab.Command.liftCoreM do
  let cur ← Tests.Compiler.DepthSwitchPinTest.current
  let pinned := Tests.Compiler.DepthSwitchPinTest.pins
  let mode : String := (← IO.getEnv "DEPTH_PIN_MODE").getD "assert"
  unless cur.length == 51 do
    throwError "DEPTH PIN: {cur.length} statements in this environment, expected 51"
  if mode == "record" then
    throwError "DEPTH PIN: record mode is never acceptance — this build fails on purpose (unset DEPTH_PIN_MODE to assert). DEPTH PIN TABLE, {cur.length} statements; a pin ONLY if this build is of the tree edd9496c (Tools/ShippingMachineDepthCommandR.lean before the switch). Paste as the value of `pins`:\n{Tests.Compiler.DepthSwitchPinTest.tableText cur}"
  unless mode == "assert" do
    throwError "DEPTH PIN: DEPTH_PIN_MODE={mode}; it is record or assert (the default)"
  if pinned.isEmpty then
    throwError "DEPTH PIN: the table `pins` is EMPTY — nothing would be asserted, and that is an error. Record it on the tree edd9496c with DEPTH_PIN_MODE=record (see the header)"
  unless pinned.length == 51 do
    throwError "DEPTH PIN: the table has {pinned.length} rows, expected 51"
  let pinNames : List Lean.Name := pinned.map fun (row : Lean.Name × UInt64 × Nat) => row.1
  unless pinNames.eraseDups.length == pinNames.length do
    throwError "DEPTH PIN: a name is twice in the table"
  let mut bad : List String := []
  for (n, h, k) in cur do
    match pinned.find? (fun (row : Lean.Name × UInt64 × Nat) => row.1 == n) with
    | some (_, h0, k0) =>
      unless h == h0 && k == k0 do
        bad := bad ++ [s!"{n}: pinned (hash {h0.toNat}, {k0} binders), now (hash {h.toNat}, {k} binders)"]
    | none => bad := bad ++ [s!"{n}: not in the table"]
  for n in pinNames do
    unless cur.any (fun (row : Lean.Name × UInt64 × Nat) => row.1 == n) do
      bad := bad ++ [s!"{n}: in the table, not among the endpoints of this file"]
  unless bad.isEmpty do
    throwError "DEPTH PIN: {bad.length} fingerprints differ from the table (a differing hash is a different TERM; whether the statements are isDefEq is decided by DepthSwitchTypeTest, not here): {bad}"
  Lean.logInfo m!"DEPTH PIN: 51 of 51 FINGERPRINTS EQUAL (Expr.hash of the type, number of leading binders) to the table. A fingerprint is NOT a proof of type equality or of isDefEq (that is DepthSwitchTypeTest); that the table was recorded on edd9496c is the integrator's record, not checked here"
