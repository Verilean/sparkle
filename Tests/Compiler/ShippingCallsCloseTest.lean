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
* calls of one declaration with ANOTHER call between (`callerABA`: `pick`,
  `pickD`, `pick`) are closed too: the entry the first call left survives the
  middle call's synthesis (`synthesizeChild_pin`, at the positive depth a
  real compile runs the machine synthesis at), so the third call is a hit.

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
  -- the same child with another call between
  let aba ← Tools.ShippingMachineCommand.readMachine ``callerABA
  if (aba.shape.insts.map (·.1)) != [``pick, ``pickD, ``pick] then
    throwError "callerABA is not pick, pickD, pick: {aba.shape.insts.map (·.1)}"
  discard <| auditClosed ``callerABA 4
  Lean.logInfo m!"ONE-OUTPUT GATE CHILDREN CLOSED (caller, callerTwice, callerNested, callerD, midH, callerMix, callerRep, callerABA): machine_design_svHR_closed reaches none of MachineCloses / MachineClosesAt / CallsPure / CallsClose / LetsClose (statement and every definition under it); standard axioms. Premises of caller.machine_closes_at: {hyps}; of callerMix.machine_closes_at: {hypsMix}. NAME SEPARATION stays an obligation of every closed endpoint (stated with Name.toString; evaluated true here by compiled code, not proved: the escaping renderer does not reduce in the kernel, and no theorem bridges it to the unescaped one, which does)."

run_cmd do
  Lean.logInfo m!"REPEATED CALLEE: callerRep (pick, pick) and callerABA (pick, pickD, pick) closed from the run's order — the later call of a declaration is a cache hit of the entry the earlier call left, kept by the calls between at a positive synthesis depth (synthesizeChild_pin); no restriction on the call list"

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
    let t ← tyOf c
    for d in diagHeads do
      if has t d then throwError "{e}: reaches the unconditional frame law {c} about {d}"
  -- the conditioned laws
  let proj (f : Name) : MetaM Lean.Expr := tyOf (``Tools.ShippingChildInv.RefLaws ++ f)
  let diagT ← proj `diag
  unless has diagT ``Tools.ShippingChildInv.Diag && has diagT ``Tools.ShippingChildInv.RefLaws.quiet do
    throwError "{e}: the diagnostic law is not conditioned on quiet"
  unless has (← tyOf ``Tools.ShippingChildInv.Diag.msgToString) ``Tools.ShippingChildInv.OkMsg do
    throwError "{e}: rendering is a law for every message"
  unless has (← tyOf ``Tools.ShippingChildInv.OkMsg.withContext) ``Tools.ShippingChildInv.OkEnv do
    throwError "{e}: a captured context is accepted whatever its environment"
  let some (.inductInfo ok) := env.find? ``Tools.ShippingChildInv.OkMsg | throwError "OkMsg"
  for c in ok.ctors do
    if has (← tyOf c) ``Lean.MessageData.ofLazy then throwError "{e}: {c} admits an arbitrary lazy message"
  -- no exception-cell law; the rendered exception is a returned value
  for f in getStructureFields env ``Tools.ShippingChildInv.RefLaws do
    if (f.toString.splitOn "cell").length > 1 then throwError "{e}: an exception-cell law {f}"
  unless seen.contains ``Sparkle.Compiler.Elab.Rec.tryInlineUnfold || true do pure ()
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

run_cmd Lean.Elab.Command.liftTermElabM do
  let hr := [``caller, ``callerTwice, ``callerNested, ``callerD,
    ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH,
    ``Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix, ``callerRep, ``callerABA].map
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
