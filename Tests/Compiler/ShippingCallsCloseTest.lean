import Tests.Compiler.ShippingChildBoundaryTest
import Tools.ShippingMachineClosesAtGen
import Tools.ShippingChildIfaceGen

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
* calls of one declaration with ANOTHER call between (`callerABA`: `pick`,
  `pickD`, `pick`) are closed too: the entry the first call left survives the
  middle call's synthesis (`synthesizeChild_pin`, at the positive depth a
  real compile runs the machine synthesis at), so the third call is a hit.

Slotless machine children (a combinational body with hardware `let`s, no
register, no call: `pickByteH`, the IP library's `httpGetByte`) are covered
too: `callerL`, `callerLN`, `hftByte` — the child's module is `closeMachine`
of `closeLets` of its transition, read-closed by `closeLets`' own order check
and the transition's closure (`Tools/ShippingMachineChildComb.lean`); the
child's premise is its machine reflection (`MachineDefines`), its own closing
is proved (`c.machine_closes`).

Not covered: machine children with calls of their own (B3), memory children.
Several-output / sequential children without calls (`closeInstsG`, B2): the
last section. (Parents without a `let`: see below.)

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

-- machine-route children: `pickByteH` is a slotless machine (hardware `let`s,
-- no register, no call), compiled by the machine route
set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL
set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN
-- a child from the IP library (`httpGetByte`: 12 hardware `let`s)
set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte

set_option maxHeartbeats 0 in
#machine_endpoint callerABA
set_option maxHeartbeats 0 in
#machine_design_svHR callerABA
set_option maxHeartbeats 0 in
#machine_closes_at callerABA
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
  for h in hyps do
    unless h.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines ||
        h.isAppOf ``Tools.ShippingMachineEntry.MachineDefines ||
        (h.find? (·.isConstOf ``Lean.Name.toString)).isSome do
      throwError "{f}.machine_closes_at: a premise that is neither a reflection nor a name obligation: {h}"
  if !hyps[0]!.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines &&
      !hyps[0]!.isAppOf ``Tools.ShippingMachineEntry.MachineDefines then
    throwError "the first premise is not a child's reflection: {hyps[0]!}"
  -- NOT premise-free: the closed endpoint states the name separation (an
  -- obligation about the compiler's module names, tracked — not proved)
  -- NAME SEPARATION: either an obligation in the statement, or PROVED — the
  -- closing theorem's proof goes through `Tools.ShippingNameSep` (the printed
  -- name is among finitely many candidates; `Name.toString` is not evaluated)
  let provedNames := match (← getEnv).find? (f ++ `machine_closes_at) with
    | some (.thmInfo ti) => ti.value.getUsedConstants.contains ``Tools.ShippingNameSep.hparent_of
    | _ => false
  let stated := (info.type.find? (·.isConstOf ``Lean.Name.toString)).isSome
  if !stated && !provedNames then
    throwError "{e}: the name separation is neither stated nor proved"
  if stated && provedNames && hyps.all (fun h => (h.find? (·.isConstOf ``Lean.Name.toString)).isNone) then
    pure ()
  if !(← namesHold f) then throwError "{f}: a name condition is false"
  return hyps

run_cmd Lean.Elab.Command.liftTermElabM do
  let hyps ← auditClosed ``caller 1
  discard <| auditClosed ``callerTwice 1
  discard <| auditClosed ``callerNested 1
  discard <| auditClosed ``callerD 1
  discard <| auditClosed ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH 1
  let hypsMix ← auditClosed ``Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix 2
  -- two instances of one child
  let rep ← Tools.ShippingMachineCommand.readMachine ``callerRep
  if (rep.shape.insts.map (·.1)) != [``pick, ``pick] then
    throwError "callerRep does not have two instances of pick: {rep.shape.insts.map (·.1)}"
  discard <| auditClosed ``callerRep 1
  -- the same child with another call between
  let aba ← Tools.ShippingMachineCommand.readMachine ``callerABA
  if (aba.shape.insts.map (·.1)) != [``pick, ``pickD, ``pick] then
    throwError "callerABA is not pick, pickD, pick: {aba.shape.insts.map (·.1)}"
  discard <| auditClosed ``callerABA 2
  -- machine-route (slotless) children: the child's reflection is its machine
  -- shape (`MachineDefines`), its own closing is proved (`pickByteH.machine_closes`)
  let hypsL ← auditClosed ``Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL 1
  discard <| auditClosed ``Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN 1
  discard <| auditClosed ``Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte 1
  unless hypsL[0]!.isAppOf ``Tools.ShippingMachineEntry.MachineDefines do
    throwError "callerL: the child's premise is not its machine reflection: {hypsL[0]!}"
  Lean.logInfo m!"ONE-OUTPUT COMBINATIONAL CHILDREN CLOSED (gate children: caller, callerTwice, callerNested, callerD, midH, callerMix, callerRep, callerABA; slotless machine children: callerL, callerLN, hftByte): machine_design_svHR_closed reaches none of MachineCloses / MachineClosesAt / CallsPure / CallsClose / LetsClose (statement and every definition under it); standard axioms. Premises of caller.machine_closes_at: {hyps}; of callerMix.machine_closes_at: {hypsMix}. NAME SEPARATION stays an obligation of every closed endpoint (stated with Name.toString; evaluated true here by compiled code, not proved: the escaping renderer does not reduce in the kernel, and no theorem bridges it to the unescaped one, which does)."

run_cmd do
  Lean.logInfo m!"REPEATED CALLEE: callerRep (pick, pick) and callerABA (pick, pickD, pick) closed from the run's order — the later call of a declaration is a cache hit of the entry the earlier call left, kept by the calls between at a positive synthesis depth (synthesizeChild_pin); no restriction on the call list"

/-! ### Parents without a `let`

The closing theorem no longer asks a `let` (`closeLets_eq'`: without `let`s
`closeLets` returns the module, the same shape with no alias;
`gateCallsOk` has no such condition). A call's arguments ARE hardware `let`s,
so a parent with calls and no `let` has only zero-argument calls. The one
such declaration tried is NOT a machine shape (the reader refuses it; the
entry compiles it by the legacy route, with the instance): there is no real
instance of the K = 0 case with calls here — the theorem covers it, a
positive endpoint is not shown. -/

/-- A zero-argument combinational child. -/
@[hardware_module]
def konst : Signal defaultDomain (BitVec 8) := (Signal.pure 5#8 : Signal defaultDomain (BitVec 8))

/-- A parent whose only call has no argument. -/
def callerK (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let y := konst
    acc <~ accS + y + x
    return accS

run_cmd Lean.Elab.Command.liftTermElabM do
  -- the closing theorem and the data check ask no `let`
  let t ← inferType (mkConst ``Tools.ShippingCallsAssembly.closeInsts_of_facts)
  let noLetPremise ← forallTelescope t fun xs _ => do
    let mut bad := false
    for x in xs do
      let ty ← whnfR (← inferType x)
      -- a premise `K ≠ 0`
      if ty.isAppOfArity ``Ne 3 && (ty.getArg! 2).isRawNatLit then bad := true
      if ty.isForall && ty.bindingDomain!.isAppOfArity ``Eq 3 && ty.bindingBody!.isConstOf ``False &&
          (ty.bindingDomain!.getArg! 2 == mkNatLit 0 || (ty.bindingDomain!.getArg! 2).isAppOf ``OfNat.ofNat) then
        bad := true
    pure (!bad)
  unless noLetPremise do throwError "closeInsts_of_facts still asks a let"
  -- the zero-argument caller is outside the machine route
  let r ← try
      discard <| Tools.ShippingMachineCommand.readMachine ``callerK
      pure true
    catch _ => pure false
  if r then throwError "callerK is a machine shape now: add its positive endpoint"
  let (m, D) ← Sparkle.Compiler.Elab.synthesizeCombinational ``callerK
  unless D.modules.any (fun c => (c.name.splitOn "konst").length > 1) &&
      m.body.any (fun st => match st with | .inst .. => true | _ => false) do
    throwError "callerK did not compile with an instance of konst"
  logInfo m!"NO-LET PARENTS: the closing theorem and gateCallsOk ask no let (K = 0 by closeLets_eq'); the zero-argument caller callerK is not a machine shape (legacy route, one instance of konst) — no real K = 0 instance with calls in the machine route was found, so no positive endpoint is shown for that branch"

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

/-- An EXISTING declaration under the generator's names is not trusted: an
unrelated theorem `True` put there (in a temporary environment) is refused —
for the closing theorem and for a closed endpoint — and the environment is
put back. Distinct from the rollback of a failed NEW generation above. -/
def refusesBogus : Lean.Elab.Command.CommandElabM Unit := do
  let saved ← getEnv
  let bogus (n : Name) : Lean.Elab.Command.CommandElabM Unit :=
    Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl
      { name := n, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro })
  let expectErr (what : String) (why : String) (act : Lean.Elab.Command.CommandElabM Unit) :
      Lean.Elab.Command.CommandElabM Unit := do
    let r ← try act; pure none catch ex => pure (some (← ex.toMessageData.toString))
    match r with
    | none => throwError "{what}: the unrelated theorem was accepted"
    | some msg => if (msg.splitOn why).length ≤ 1 then throwError "{what} failed otherwise: {msg}"
  -- the closing theorem's name
  bogus (``callerBad ++ `machine_closes_at)
  expectErr "callerBad.machine_closes_at" "another statement" do
    discard <| Tools.ShippingMachineClosesAtGen.closesAtTheorem ``callerBad
  setEnv saved
  -- a closed endpoint's name (a fresh name, so the real one is not disturbed)
  let nn := ``caller ++ `machine_design_svHR_bogus
  bogus nn
  expectErr "caller.machine_design_svHR_bogus" "another statement" do
    discard <| Lean.Elab.Command.liftTermElabM <|
      Tools.ShippingMachineClosesAtGen.closeEndpointAt ``caller (``caller ++ `machine_closes_at)
        (``caller ++ `machine_design_svHR) nn
  setEnv saved
  -- the real names are reused only as the generated statements
  discard <| Tools.ShippingMachineClosesAtGen.closesAtTheorem ``caller
  unless ← Lean.Elab.Command.liftTermElabM <|
      Tools.ShippingMachineClosesAtGen.closeEndpointAt ``caller (``caller ++ `machine_closes_at)
        (``caller ++ `machine_design_svHR) (``caller ++ `machine_design_svHR_closed) do
    throwError "the real closed endpoint was not accepted"
  if (← getEnv).contains nn || (← getEnv).contains (``callerBad ++ `machine_closes_at) then
    throwError "a temporary declaration was left"

run_cmd do
  refusesBogus
  Lean.logInfo m!"EXISTING NAMES ARE NOT TRUSTED: an unrelated theorem True under callerBad.machine_closes_at and under a closed endpoint's name is refused (statement compared with the generated one); the real caller.machine_closes_at / machine_design_svHR_closed are accepted as exactly the generated statements; the temporary environment is dropped"

run_cmd do
  failsClean ``callerBad (some 0) "the generated proof fails"
  failsClean ``callerNoEndpoint none "the generated proof fails"
  discard <| Tools.ShippingMachineClosesAtGen.closesAtTheorem ``callerBad
  Lean.logInfo m!"FAILED GENERATION LEAVES NOTHING: a false data check (callerBad at 0 declaration binders) and missing data (callerNoEndpoint) fail after the theorem command ran; no declaration under the name, no message; callerBad then generates"

/-! ### The law audit, FROM the generated endpoints

For each generated endpoint (the closed HR ones, R0, NR at every depth): the
constants its STATEMENT reaches — definitions unfolded, inductive types with
their constructors — and, of what it reaches there:

* it asks the boundary `ChildBnd`, which is one witness with the start world
  quiet for it;
* no reached `Framed` constructor (an unconditional frame law) is about a
  diagnostic operation or about throwing a message;
* the diagnostic law is conditioned on `quiet`, the rendering law on the
  message class, a captured context on its environment's printers, and the
  class has no arbitrary lazy message;
* there is no exception-cell law (the provenance of the rendered exception is
  a value: `Rec.tryInlineUnfold`);
* the cache-pinning auxiliary predicate is constrained by NO law field and by
  no start condition: it is not a runtime assumption.

This is an audit of the endpoints' own dependencies — not of the law
definitions in isolation. It does not show the laws hold of the runtime. -/

/-- `reach`, also through an inductive type's constructors. -/
partial def reachI (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then reachI env rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | some (.defnInfo d) =>
        reachI env (d.type.getUsedConstants.toList ++ d.value.getUsedConstants.toList ++ rest) seen
      | some (.inductInfo i) => reachI env (i.type.getUsedConstants.toList ++ i.ctors ++ rest) seen
      | some ci => reachI env (ci.type.getUsedConstants.toList ++ rest) seen
      | none => reachI env rest seen

def diagHeads : List Name :=
  [``Lean.Meta.ppExpr, ``IO.eprintln, ``Lean.MessageData.toString, ``IO.getStderr,
   ``Sparkle.Compiler.flushStderr, ``IO.FS.Handle.mk, ``IO.FS.Handle.putStrLn, ``IO.FS.Handle.flush,
   ``Tools.ShippingChildInv.profLogIO, ``Lean.throwError]

/-- No constructor of the frame-law class `framed` is about a diagnostic
operation or a throw. -/
def noDiagFrame (framed : Name) : MetaM Unit := do
  let some (.inductInfo fr) := (← getEnv).find? framed | throwError "{framed}: not an inductive"
  for c in fr.ctors do
    let t := (← getConstInfo c).type
    for d in diagHeads do
      if (t.find? (·.isConstOf d)).isSome then
        throwError "the unconditional frame law {c} is about {d}"

/-- The message class `ok` admits no arbitrary lazy message. -/
def noLazyMsg (ok : Name) : MetaM Unit := do
  let some (.inductInfo oi) := (← getEnv).find? ok | throwError "{ok}: not an inductive"
  for c in oi.ctors do
    if (((← getConstInfo c).type).find? (·.isConstOf ``Lean.MessageData.ofLazy)).isSome then
      throwError "{c} admits an arbitrary lazy message"

def lawAudit (e : Name) : MetaM Unit := do
  let env ← getEnv
  let info ← getConstInfo e
  let seen := reachI env info.type.getUsedConstants.toList {}
  let has (t : Lean.Expr) (c : Name) : Bool := (t.find? (·.isConstOf c)).isSome
  let tyOf (c : Name) : MetaM Lean.Expr := do pure (← getConstInfo c).type
  for c in [``Tools.ShippingChildInv.ChildBnd, ``Tools.ShippingChildInv.RefLaws,
      ``Tools.ShippingChildInv.RefLaws.quiet, ``Tools.ShippingChildInv.StartV,
      ``Tools.ShippingChildInv.Framed, ``Tools.ShippingChildInv.Diag, ``Tools.ShippingChildInv.OkMsg,
      ``Tools.ShippingChildInv.OkEnv] do
    unless seen.contains c do throwError "{e}: does not reach {c}"
  -- the unconditional frame laws it reaches
  let some (.inductInfo fr) := env.find? ``Tools.ShippingChildInv.Framed | throwError "Framed"
  for c in fr.ctors do
    unless seen.contains c do throwError "{e}: does not reach {c}"
  noDiagFrame ``Tools.ShippingChildInv.Framed
  -- the conditioned laws
  let proj (f : Name) : MetaM Lean.Expr := tyOf (``Tools.ShippingChildInv.RefLaws ++ f)
  let diagT ← proj `diag
  unless has diagT ``Tools.ShippingChildInv.Diag && has diagT ``Tools.ShippingChildInv.RefLaws.quiet do
    throwError "{e}: the diagnostic law is not conditioned on quiet"
  unless has (← tyOf ``Tools.ShippingChildInv.Diag.msgToString) ``Tools.ShippingChildInv.OkMsg do
    throwError "{e}: rendering is a law for every message"
  unless has (← tyOf ``Tools.ShippingChildInv.OkMsg.withContext) ``Tools.ShippingChildInv.OkEnv do
    throwError "{e}: a captured context is accepted whatever its environment"
  noLazyMsg ``Tools.ShippingChildInv.OkMsg
  -- no law field speaks of a ref of type `Option Exception` (a check of the
  -- field TYPES: there is no exception-cell law to read a provenance from)
  for f in getStructureFields env ``Tools.ShippingChildInv.RefLaws do
    let t ← proj f
    if (t.find? fun x => x.isAppOfArity ``Option 1 && x.appArg!.isConstOf ``Lean.Exception).isSome then
      throwError "{e}: the law {f} speaks of an exception cell"
  -- the auxiliary predicate: no law field and no start condition mentions it
  for f in getStructureFields env ``Tools.ShippingChildInv.RefLaws do
    if f == `aux || f == `auxInsert then continue
    if has (← proj f) ``Tools.ShippingChildInv.RefLaws.aux then
      throwError "{e}: the law {f} constrains the auxiliary predicate"
  let auxInsT ← proj `auxInsert
  for c in [``Tools.ShippingChildInv.RefLaws.val, ``Tools.ShippingChildInv.RefLaws.quiet,
      ``Tools.ShippingEntrySoundness.RunsTo, ``Tools.ShippingChildInv.endW] do
    if has auxInsT c then throwError "{e}: auxInsert speaks of the runtime ({c})"
  for c in [``Tools.ShippingChildInv.ChildBnd, ``Tools.ShippingChildInv.StartV,
      ``Tools.ShippingChildInv.InvW, ``Tools.ShippingChildInv.InvV] do
    let some (.defnInfo d) := env.find? c | throwError "{c}"
    if has d.value ``Tools.ShippingChildInv.RefLaws.aux then
      throwError "{e}: {c} asks the auxiliary predicate of a world"

/-- **Where the rendered exception comes from** — checked on the compiler's
handler and on its proof, not on the endpoints' types (an endpoint need not
mention the helper): the handler allocates no ref and reads no exception
cell, it calls the helper that returns the caught exception, and the proof
that the handler keeps the invariant uses the helper's result theorem
through the bind rule that hands the result's fact on. -/
def provenanceAudit : MetaM Unit := do
  let env ← getEnv
  let some (.defnInfo h) := env.find? ``Sparkle.Compiler.Elab.Rec.handleDefinitionUnfold
    | throwError "handleDefinitionUnfold"
  let used := h.value.getUsedConstants
  unless used.contains ``Sparkle.Compiler.Elab.Rec.tryInlineUnfold do
    throwError "the handler does not call the inline helper"
  -- the rendering site renders a VARIABLE bound by the helper's result
  -- pattern, and the handler has no `Option Exception` ref
  if (h.value.find? fun x => x.isAppOf ``IO.Ref &&
      (x.find? (·.isConstOf ``Lean.Exception)).isSome).isSome then
    throwError "the handler has an exception cell"
  let some (.defnInfo t) := env.find? ``Sparkle.Compiler.Elab.Rec.tryInlineUnfold | throwError "helper"
  if (t.value.find? fun x => x.isAppOf ``IO.Ref || x.isConstOf ``IO.mkRef || x.isConstOf ``ST.Ref.set).isSome then
    throwError "the inline helper uses a ref"
  let some (.thmInfo k) := env.find? ``Tools.ShippingChildInv.handleDefinitionUnfold_keeps
    | throwError "handleDefinitionUnfold_keeps"
  -- (through the proof's own auxiliary declarations)
  let rec deep (fuel : Nat) (todo : List Name) (acc : NameSet) : NameSet :=
    match fuel, todo with
    | 0, _ | _, [] => acc
    | fuel + 1, n :: rest =>
      if acc.contains n then deep fuel rest acc
      else
        let acc := acc.insert n
        if (``Tools.ShippingChildInv.handleDefinitionUnfold_keeps).isPrefixOf n then
          match env.find? n with
          | some (.thmInfo t) => deep fuel (t.value.getUsedConstants.toList ++ rest) acc
          | some (.defnInfo d) => deep fuel (d.value.getUsedConstants.toList ++ rest) acc
          | _ => deep fuel rest acc
        else deep fuel rest acc
  let usedK := deep 100000 k.value.getUsedConstants.toList {}
  for c in [``Tools.ShippingChildInv.tryInlineUnfold_tripleC, ``Tools.ShippingChildInv.KeepsC.bindCaught] do
    unless usedK.contains c do
      throwError "the handler's invariance proof does not use {c}"
  let some (.thmInfo r) := env.find? ``Tools.ShippingChildInv.tryInlineUnfold_tripleC | throwError "result thm"
  unless r.value.getUsedConstants.contains ``Tools.ShippingChildInv.TripleC.tryCatchQ do
    throwError "the helper's result theorem does not go through the catch rule"

/-! Negative cases: the audit's checks reject what they are meant to reject. -/

/-- A frame-law class with a diagnostic operation in it. -/
inductive BadFramed : {α : Type} → MetaM α → Prop
  | pp (e : Lean.Expr) : BadFramed (Lean.Meta.ppExpr e)

/-- A message class with an arbitrary lazy message. -/
inductive BadMsg : MessageData → Prop
  | lazy (f : Option PPContext → BaseIO Dynamic) (g : MetavarContext → Bool) :
      BadMsg (.ofLazy f g)

def rejects (what : String) (act : MetaM Unit) : MetaM Unit := do
  let r ← try act; pure false catch _ => pure true
  unless r do throwError "the audit accepted: {what}"

run_cmd Lean.Elab.Command.liftTermElabM do
  rejects "a frame law about ppExpr" (noDiagFrame ``BadFramed)
  rejects "a message class with an arbitrary lazy message" (noLazyMsg ``BadMsg)
  rejects "a statement that does not ask the boundary" (lawAudit ``Nat.add_comm)
  -- the open endpoint (it still asks the closing premise) passes the LAW
  -- audit — that audit is about the laws, not about closing
  lawAudit (``caller ++ `machine_design_svHR)
  provenanceAudit
  Lean.logInfo m!"AUDIT NEGATIVES: a frame-law class with a diagnostic operation, a message class with an arbitrary lazy message, and a statement not asking the boundary are rejected. PROVENANCE: the handler calls the inline helper and has no exception ref, the helper uses no ref, and the handler's invariance proof goes through the helper's result theorem (tryCatchQ) and the bind rule that hands the fact on"

run_cmd Lean.Elab.Command.liftTermElabM do
  let hr := [``caller, ``callerTwice, ``callerNested, ``callerD,
    ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH,
    ``Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix, ``callerRep, ``callerABA,
    ``Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL,
    ``Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN,
    ``Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte].map
      (· ++ `machine_design_svHR_closed)
  let nr := (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.nrEndpoints.map fun (f, n) =>
      f ++ Name.mkSimple s!"machine_design_svNR{n}") ++
    [``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_svNR2,
     ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_svNR2,
     ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_svNR3,
     ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_design_svNR2]
  let es := hr ++ Sparkle.Tests.Compiler.ShippingChildBoundaryTest.rEndpoints ++ nr
  for e in es do lawAudit e
  Lean.logInfo m!"LAW AUDIT FROM THE ENDPOINTS: {es.length} generated endpoints (closed HR, R0, NR at every depth) — each reaches ChildBnd and the law bundle; no reached unconditional frame law is about a diagnostic operation or a throw; the diagnostic law is under quiet, rendering under the message class, a captured context under its environment's printers; no exception-cell law; the cache-pinning auxiliary predicate is constrained by no law and no start condition. The laws themselves stay assumptions (no runtime model); the elaborator primitives and profLog remain unconditional / one constructor."

/-! ## The general closing (B2): several outputs, sequential children

`parent` reads two fields of ONE call of the sequential child `cnt`; `chained`
calls `cnt` twice, the second on a field of the first. The compiler closes
them by `closeInstsGM`; their `MachineClosesAt` is derived
(`machineClosesAt_of_seqKids`: the child read by the `RealChild` witness of
its own run, the entries of one call the same child by the cache pin), and
the depth endpoint's closing premise is replaced by the theorem's premises:
the child's reflection and the name condition (N1, an obligation). A parent
whose child has calls of its own (`mid2`) is REFUSED with that reason — its
closing stays a premise (B3). -/

set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent 1
set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent
set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained 1
set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained

/-- The closed depth endpoint of `f` reaches no closing premise, the open one
asks `MachineClosesAt`; standard axioms; the closing theorem's premises are
the child's reflection and the name condition, which holds when evaluated. -/
def auditClosedNR (f : Name) (n nPremises : Nat) : MetaM Unit := do
  let env ← getEnv
  let o := f ++ Name.mkSimple s!"machine_design_svNR{n}"
  let e := Tools.ShippingMachineClosesGen.closedName o
  let info ← getConstInfo e
  let open0 ← getConstInfo o
  let seen := reach env info.type.getUsedConstants.toList {}
  let seen0 := reach env open0.type.getUsedConstants.toList {}
  if banned.any fun b => seen.contains b then throwError "{e} still reaches a closing premise"
  if !seen0.contains ``Tools.ShippingChildInv.MachineClosesAt then
    throwError "the audit does not see MachineClosesAt in the open endpoint {o}"
  let axs ← Lean.collectAxioms e
  if axs.any fun a => !(a == ``propext || a == ``Classical.choice || a == ``Quot.sound) then
    throwError "{e} depends on a non-standard axiom: {axs}"
  let hyps ← premises (f ++ `machine_closes_at)
  if hyps.size != nPremises then throwError "{f}.machine_closes_at has {hyps.size} premises: {hyps}"
  for h in hyps do
    unless h.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines ||
        h.isAppOf ``Tools.ShippingMachineEntry.MachineDefines ||
        (h.find? (·.isConstOf ``Lean.Name.toString)).isSome do
      throwError "{f}.machine_closes_at: a premise that is neither a reflection nor a name obligation: {h}"
  if !hyps[0]!.isAppOf ``Tools.ShippingMachineEntry.MachineDefines then
    throwError "the first premise is not a child's reflection: {hyps[0]!}"
  -- NAME SEPARATION: either an obligation in the statement, or PROVED — the
  -- closing theorem's proof goes through `Tools.ShippingNameSep` (the printed
  -- name is among finitely many candidates; `Name.toString` is not evaluated)
  let provedNames := match (← getEnv).find? (f ++ `machine_closes_at) with
    | some (.thmInfo ti) => ti.value.getUsedConstants.contains ``Tools.ShippingNameSep.hparent_of
    | _ => false
  let stated := (info.type.find? (·.isConstOf ``Lean.Name.toString)).isSome
  if !stated && !provedNames then
    throwError "{e}: the name separation is neither stated nor proved"
  if stated && provedNames && hyps.all (fun h => (h.find? (·.isConstOf ``Lean.Name.toString)).isNone) then
    pure ()
  if !(← namesHold f) then throwError "{f}: a name condition is false"
  -- the general closing really is the route: the shape reads fields
  let r ← Tools.ShippingMachineCommand.readMachine f
  if r.shape.instFields.isEmpty then throwError "{f}: not a general-closing shape"
  lawAudit e

run_cmd do
  Lean.Elab.Command.liftTermElabM do
    auditClosedNR ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent 1 1
    auditClosedNR ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained 1 1
  -- a child with calls of its own: refused, nothing left behind
  failsClean ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 none "calls of its own"
  Lean.logInfo m!"GENERAL CLOSING (B2): parent (two fields of one call of the sequential child cnt) and chained (two calls, the second on a field of the first) — the depth SV endpoints closed: MachineClosesAt derived, premises the child's reflection and the name condition; mid2 (a child with calls of its own) refused"

/-! ## Children with calls of their own (B3)

`grand → mid → cnt`, `grandH → midH → rcH`, `mixD1 → {midH → rcH, cnt}`,
`topD2 → mid2 → midH → rcH`: the parent is closed by the general closing over
a child that has calls. `#machine_closes_deep` derives the parent's
`MachineClosesAt` (`machineClosesAt_of_kidsD`), each child with calls read by
its interface from its own run (`kidsChild_of_real`: ports, the design as the
join of its children, the post-passes), and closes the depth endpoints.
Premises: every descendant's reflection, and name separation per node (N1,
obligations). What is left, recorded exactly: `topD2`'s depth endpoint still
asks the closing of `mid2` in the contexts `mid2` is synthesised in — that
closing needs the reflection of `rcH` (a grandchild of `mid2`) there, which
the child's boundary does not carry. -/

set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand 2
set_option maxHeartbeats 0 in
#machine_closes_deep Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand
set_option maxHeartbeats 0 in
#machine_closes_deep Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH
set_option maxHeartbeats 0 in
#machine_closes_deep Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1
set_option maxHeartbeats 0 in
#machine_closes_deep Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2

/-- The declarations whose `MachineClosesAt` the statement of `thm` mentions
(anywhere), among `cands`. -/
def closingsLeft (thm : Name) (cands : List Name) : MetaM (List Name) := do
  let info ← getConstInfo thm
  let mut out : List Name := []
  -- every application of `MachineClosesAt` in the statement
  let rec go (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
    let acc := if e.isAppOfArity ``Tools.ShippingChildInv.MachineClosesAt 6 then acc.push (e.getArg! 4)
      else acc
    match e with
    | .app f a => go a (go f acc)
    | .lam _ t b _ => go b (go t acc)
    | .forallE _ t b _ => go b (go t acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ b => go b acc
    | .proj _ _ b => go b acc
    | _ => acc
  for a in go info.type #[] do
    let mut hit := false
    for c in cands do
      if !hit && (← isDefEq a (toExpr c)) then
        hit := true
        unless out.contains c do out := out ++ [c]
    unless hit do throwError "{thm}: a closing of an unlisted declaration: {a}"
  return out

run_cmd Lean.Elab.Command.liftTermElabM do
  let cands := [``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand,
    ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid,
    ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH,
    ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH,
    ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1,
    ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2,
    ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2]
  let std (e : Name) : MetaM Unit := do
    let axs ← Lean.collectAxioms e
    if axs.any fun a => !(a == ``propext || a == ``Classical.choice || a == ``Quot.sound) then
      throwError "{e} depends on a non-standard axiom: {axs}"
  let mut report : Array MessageData := #[]
  for (f, ns, want) in
      [(``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand, [2], ([] : List Name)),
       (``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH, [1, 2], []),
       (``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1, [1, 2], []),
       (``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2, [2, 3],
         [``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2])] do
    std (f ++ `closes_deep)
    unless (← closingsLeft (f ++ `closes_deep) cands) == [f] do
      throwError "{f}.closes_deep: its statement asks a closing"
    for n in ns do
      let o := f ++ Name.mkSimple s!"machine_design_svNR{n}"
      let e := Tools.ShippingMachineClosesGen.closedName o
      std e
      -- the open endpoint asks the parent's closing; the closed one does not
      unless (← closingsLeft o cands).contains f do
        throwError "{o}: the open endpoint does not ask {f}'s closing"
      let left ← closingsLeft e cands
      unless left == want do
        throwError "{e}: closings left {left}, expected {want}"
      lawAudit e
      report := report.push m!"{e}: closings left {left}"
    unless ← namesHold f do throwError "{f}: a name condition is false"
  Lean.logInfo m!"CHILDREN WITH CALLS (B3): {report} — MachineClosesAt derived through a child with calls; premises: the descendants' reflection and name separation per node; standard axioms"

-- Every premise of the deep closings is a descendant's reflection: the name
-- separation over the descendants is PROVED (`Tools.ShippingNameSep`).
run_cmd Lean.Elab.Command.liftTermElabM do
  for (f, nRefl) in [(``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand, 2),
      (``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH, 2),
      (``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1, 3),
      (``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2, 3)] do
    let hyps ← premises (f ++ `closes_deep)
    for h in hyps do
      unless h.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines ||
          h.isAppOf ``Tools.ShippingMachineEntry.MachineDefines do
        throwError "{f}.closes_deep: a premise that is not a reflection: {h}"
    unless hyps.size == nRefl do throwError "{f}.closes_deep: {hyps.size} premises"
  Lean.logInfo m!"DEEP CLOSINGS: grand, grandH, mixD1, topD2 — the only premises are the descendants' reflections (2, 2, 3, 3); name separation over the descendants proved from the candidate renderings"
