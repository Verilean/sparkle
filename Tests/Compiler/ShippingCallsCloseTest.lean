import Tests.Compiler.ShippingChildBoundaryTest
import Tools.ShippingMachineClosesAtGen

/-! # `MachineClosesAt` derived: parents of one-output gate children

`#machine_closes_at f` adds `f.machine_closes_at`
(`machineClosesAt_of_gateKids` at `f`'s data) and `f`'s endpoints without the
closing premise (`_closed`; here the closed-SV endpoint
`f.machine_design_svHR_closed`). First unit: `caller` → `pick`.

Checked here, for `caller`, `callerTwice` (two identical calls, ONE instance
after deduplication), `callerNested` (a sub-machine's result as the
argument), `callerD` (a domain-polymorphic child), `midH` (two outputs) and
`callerMix` (two different children):

* the closed endpoint's statement, and every definition it unfolds to,
  mentions none of `MachineCloses` / `MachineClosesAt` / `CallsPure` /
  `CallsClose` / `LetsClose` (the open endpoint does: the audit sees it);
* what replaced the premise: the children's reflection (`EntryDefines`,
  already asked by the endpoint) and name conditions the kernel cannot
  evaluate (`Name.toString` does not reduce): no callee is named as the
  parent and, for `callerMix`, the two callees' names differ. They are
  evaluated here by the compiled code — evidence, not a proof;
* standard axioms;
* two INSTANCES of one declaration (`callerRep`) are REFUSED: their closing
  needs the child cache's witness (equal modules), which `ChildrenReal` does
  not record. Nothing is added; such a parent keeps `MachineClosesAt`.

Not covered: machine-route children (`callerL`, `callerLN`, `hftByte` keep
the premise), several-output / sequential children (`closeInstsG`), parents
without a `let`.

These are conditional theorems under the generic runtime laws (`ChildBnd`);
that does not make the laws consistent with the runtime (G5), and the shape
reader's correspondence (S3, `letsAliasOk` on data) is evaluated per
declaration, not proved of the reader (G3). -/

open Lean Meta
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingMachineInstTest

/-- Two instances of one child. -/
def callerRep (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let sel ← Signal.reg 0#2
    let acc ← Signal.reg 0#8
    let selS := (sel : Signal defaultDomain (BitVec 2))
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let y := pick selS (accS + x)
    let z := pick selS y
    sel <~ selS + (Signal.pure 1#2 : Signal defaultDomain (BitVec 2))
    acc <~ z
    return z

set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.ShippingMachineInstTest.caller
set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.ShippingMachineInstTest.callerTwice
set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.ShippingMachineInstTest.callerNested
set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.ShippingMachineInstTest.callerD
set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix

/-- The constants a statement reaches: its own and, transitively, those of
the definitions (not theorems) it mentions. -/
partial def reach (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then reach env rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | some (.defnInfo d) =>
        reach env (d.type.getUsedConstants.toList ++ d.value.getUsedConstants.toList ++ rest) seen
      | some ci => reach env (ci.type.getUsedConstants.toList ++ rest) seen
      | none => reach env rest seen

def banned : List Name :=
  [``Tools.ShippingMachineEntry.MachineCloses, ``Tools.ShippingChildInv.MachineClosesAt,
   ``Tools.ShippingChildInv.CallsPure, ``Tools.ShippingClosesSplit.CallsClose,
   ``Tools.ShippingClosesSplit.LetsClose]

/-- The Prop premises of a theorem. -/
def premises (thm : Name) : MetaM (Array Lean.Expr) := do
  let info ← getConstInfo thm
  forallTelescope info.type fun xs _ => do
    let ts ← xs.mapM fun x => inferType x
    ts.filterM fun t => isProp t

@[noinline] def nameStr (n : Name) : String := Name.toString n

/-- The name conditions, evaluated (not a proof). -/
def namesHold (f : Name) : MetaM Bool := do
  let r ← Tools.ShippingMachineCommand.readMachine f
  let ks := r.shape.insts.map fun c => nameStr c.1
  return !ks.contains (nameStr f) && ks.eraseDups.length == ks.length

/-- The closed endpoint of `f` reaches no closing premise; the open one does. -/
def auditClosed (f : Name) (nPremises : Nat) : MetaM (Array Lean.Expr) := do
  let env ← getEnv
  let e := f ++ `machine_design_svHR_closed
  let info ← getConstInfo e
  let open0 ← getConstInfo (f ++ `machine_design_svHR)
  let seen := reach env info.type.getUsedConstants.toList {}
  let seen0 := reach env open0.type.getUsedConstants.toList {}
  if banned.any fun b => !env.contains b then throwError "the audit's list is stale"
  if banned.any fun b => seen.contains b then throwError "{e} still reaches a closing premise"
  if !seen0.contains ``Tools.ShippingChildInv.MachineClosesAt then
    throwError "the audit does not see MachineClosesAt in the open endpoint"
  let axs ← Lean.collectAxioms e
  if axs.any fun a => !(a == ``propext || a == ``Classical.choice || a == ``Quot.sound) then
    throwError "{e} depends on a non-standard axiom: {axs}"
  let hyps ← premises (f ++ `machine_closes_at)
  if hyps.size != nPremises then throwError "{f}.machine_closes_at has {hyps.size} premises: {hyps}"
  if !hyps[0]!.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines then
    throwError "the first premise is not a child's reflection: {hyps[0]!}"
  if !(← namesHold f) then throwError "{f}: a name condition is false"
  return hyps

run_cmd Lean.Elab.Command.liftTermElabM do
  let hyps ← auditClosed ``caller 2
  discard <| auditClosed ``callerTwice 2
  discard <| auditClosed ``callerNested 2
  discard <| auditClosed ``callerD 2
  discard <| auditClosed ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH 2
  let hypsMix ← auditClosed ``Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix 4
  Lean.logInfo m!"ONE-OUTPUT GATE CHILDREN CLOSED (caller, callerTwice, callerNested, callerD, midH, callerMix): machine_design_svHR_closed reaches none of MachineCloses / MachineClosesAt / CallsPure / CallsClose / LetsClose (statement and every definition under it); standard axioms. Premises of caller.machine_closes_at: {hyps}; of callerMix.machine_closes_at: {hypsMix}. The name conditions are evaluated true, not proved (Name.toString does not reduce in the kernel)."

/-- Two instances of one declaration: refused (the cache's witness is not
derived), nothing is added. -/
def refused (f : Name) : Lean.Elab.Command.CommandElabM Unit := do
  let r ← try
      discard <| Tools.ShippingMachineClosesAtGen.closesAtTheorem f
      pure none
    catch ex => pure (some (← ex.toMessageData.toString))
  match r with
  | none => throwError "{f}: machine_closes_at was generated"
  | some msg =>
    if (msg.splitOn "two calls of one declaration").length ≤ 1 then
      throwError "{f} failed otherwise: {msg}"
  if (← getEnv).contains (f ++ `machine_closes_at) then throwError "{f}: a theorem was left"

run_cmd do
  refused ``callerRep
  Lean.logInfo m!"REPEATED CALLEE (callerRep, two instances of pick): refused — equal modules for two instances of one declaration come from the child cache, not recorded by ChildrenReal; such a parent keeps MachineClosesAt"
