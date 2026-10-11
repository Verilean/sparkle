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
* two INSTANCES of one declaration (`callerRep`: `pick` twice, consecutive)
  are closed too: the second call is a cache hit of the first, from the order
  the closing's `mapM` runs (`closeInstsM_run_adj`) — not from an assumption
  that two real compiles agree;
* calls of one declaration with ANOTHER call between (`callerABA`) are
  REFUSED: the cache entry's survival through the middle call's synthesis is
  not derived. Nothing is added; such a parent keeps `MachineClosesAt`.

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

/-- `pick`, `pickD`, `pick`: the two `pick` instances are not consecutive. -/
def callerABA (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let sel ← Signal.reg 0#2
    let acc ← Signal.reg 0#8
    let selS := (sel : Signal defaultDomain (BitVec 2))
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let y := pick selS (accS + x)
    let z := pickD selS y
    let u := pick selS z
    sel <~ selS + (Signal.pure 1#2 : Signal defaultDomain (BitVec 2))
    acc <~ u
    return u

set_option maxHeartbeats 0 in
#machine_endpoint callerRep
set_option maxHeartbeats 0 in
#machine_design_svHR callerRep
set_option maxHeartbeats 0 in
#machine_closes_at callerRep

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
  -- no callee prints as the parent; different callees print differently
  let ds := (r.shape.insts.map (·.1)).eraseDups
  return !ks.contains (nameStr f) && (ds.map nameStr).eraseDups.length == ds.length

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
  -- NOT premise-free: the closed endpoint states the name separation (an
  -- obligation about the compiler's module names, tracked — not proved)
  if (info.type.find? (·.isConstOf ``Lean.Name.toString)).isNone then
    throwError "{e}: the name-separation obligation is not stated"
  if !(← namesHold f) then throwError "{f}: a name condition is false"
  return hyps

run_cmd Lean.Elab.Command.liftTermElabM do
  let hyps ← auditClosed ``caller 2
  discard <| auditClosed ``callerTwice 2
  discard <| auditClosed ``callerNested 2
  discard <| auditClosed ``callerD 2
  discard <| auditClosed ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH 2
  let hypsMix ← auditClosed ``Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix 4
  -- two instances of one child
  let rep ← Tools.ShippingMachineCommand.readMachine ``callerRep
  if (rep.shape.insts.map (·.1)) != [``pick, ``pick] then
    throwError "callerRep does not have two instances of pick: {rep.shape.insts.map (·.1)}"
  discard <| auditClosed ``callerRep 2
  Lean.logInfo m!"ONE-OUTPUT GATE CHILDREN CLOSED (caller, callerTwice, callerNested, callerD, midH, callerMix, callerRep): machine_design_svHR_closed reaches none of MachineCloses / MachineClosesAt / CallsPure / CallsClose / LetsClose (statement and every definition under it); standard axioms. Premises of caller.machine_closes_at: {hyps}; of callerMix.machine_closes_at: {hypsMix}. NAME SEPARATION stays an obligation of every closed endpoint (stated with Name.toString; evaluated true here by compiled code, not proved: the escaping renderer does not reduce in the kernel, and no theorem bridges it to the unescaped one, which does)."

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
    if (msg.splitOn "with other calls between").length ≤ 1 then
      throwError "{f} failed otherwise: {msg}"
  if (← getEnv).contains (f ++ `machine_closes_at) then throwError "{f}: a theorem was left"

run_cmd do
  refused ``callerABA
  Lean.logInfo m!"REPEATED CALLEE: callerRep (pick, pick) closed from the run's order (the second call is a cache hit); callerABA (pick, pickD, pick) refused — the cache entry's survival through the middle call's synthesis is not derived; such a parent keeps MachineClosesAt"

/-! ### A failed generation leaves nothing

`callerBad` has a machine endpoint; stated at a wrong number of declaration
binders the generated proof does not check (the data check is false), after
the theorem command has run. `callerNoEndpoint` has no generated data at all.
In both cases: an error, no declaration, no message left — and the real
generation of `callerBad` then succeeds. -/

def callerBad (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let sel ← Signal.reg 0#2
    let acc ← Signal.reg 0#8
    let selS := (sel : Signal defaultDomain (BitVec 2))
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let y := pick selS (accS + x)
    sel <~ selS + (Signal.pure 1#2 : Signal defaultDomain (BitVec 2))
    acc <~ y
    return y

def callerNoEndpoint (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let y := pick (Signal.pure 1#2 : Signal defaultDomain (BitVec 2)) (accS + x)
    acc <~ y
    return y

set_option maxHeartbeats 0 in
#machine_endpoint callerBad

/-- The generation fails with `why` in its error, and leaves no declaration
of `f` and no message. -/
def failsClean (f : Name) (nDecl? : Option Nat) (why : String) : Lean.Elab.Command.CommandElabM Unit := do
  let env0 ← getEnv
  let msgs0 := (← get).messages.toList.length
  let r ← try
      discard <| Tools.ShippingMachineClosesAtGen.closesAtTheorem f nDecl?
      pure none
    catch ex => pure (some (← ex.toMessageData.toString))
  match r with
  | none => throwError "{f}: machine_closes_at was generated"
  | some msg =>
    if (msg.splitOn why).length ≤ 1 then throwError "{f} failed otherwise: {msg}"
  if (← get).messages.toList.length != msgs0 then throwError "{f}: messages were left"
  let env ← getEnv
  let left : Nat := env.constants.fold (init := (0 : Nat)) fun (n : Nat) c _ =>
    if f.isPrefixOf c && !env0.contains c then n + 1 else n
  if left != 0 then throwError "{f}: {left} declarations were left"

run_cmd do
  failsClean ``callerBad (some 0) "the generated proof fails"
  failsClean ``callerNoEndpoint none "the generated proof fails"
  discard <| Tools.ShippingMachineClosesAtGen.closesAtTheorem ``callerBad
  Lean.logInfo m!"FAILED GENERATION LEAVES NOTHING: a false data check (callerBad at 0 declaration binders) and missing data (callerNoEndpoint) fail after the theorem command ran; no declaration under the name, no message; callerBad then generates"
