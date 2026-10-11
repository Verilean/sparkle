import Tests.Compiler.ShippingReflectCtxTest
import Tools.ShippingMachineCommand
import Tools.ShippingMachineClosesGen
import Tools.ShippingCallsClose
import Tools.ShippingCloseMachineFacts
import Tools.ShippingCallsRank
import Tools.ShippingTransitionFields
import Tools.ShippingRankRun

/-! # `MachineCloses` derived for `let` shapes without calls

`closes_of_data` on real declarations: the machine endpoint generator adds
`f.machine_closes` and the endpoints without the `MachineCloses` premise
(`_closed`) where the data give it. What is checked here is the TYPE of the
closed endpoints (no `MachineCloses`), their axioms, and — on data — which
`let` shapes the check `aliasOk` accepts. Declarations with calls are not
examples of this (their `MachineCloses` stays a premise). -/

open Lean Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingMachineClosesData

/-- A `let` that is an input, and a `let` that is that `let`. -/
def closesInputLet (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let a := x
    let b := a
    r <~ (a + b) + rs
    return rs

/-- A `let` after an operation, and a `let` that is that `let`. -/
def closesOpAlias (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let a := x + 1#8
    let b := a
    r <~ (a + b) + rs
    return rs

/-- A `let` used by a later `let` under an operation. -/
def closesChain (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let a := rs + x
    let b := a + x
    let c := b + a
    r <~ c + b
    return rs

#machine_endpoint reflSharedLet
#machine_endpoint reflAliasLet
#machine_endpoint closesInputLet
#machine_endpoint closesOpAlias
#machine_endpoint closesChain

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let std (n : Name) : MetaM Unit := do
    for a in ← Lean.collectAxioms n do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        throwError "{n} depends on {a}"
  for n in [``Tools.ShippingMachineCloses.machineCloses_of_lets,
      ``Tools.ShippingMachineCloses.transition_closes,
      ``Tools.ShippingMachineClosesData.closes_of_data,
      ``Tools.ShippingMachineClosesData.aliasOk_sound] do std n
  -- the theorem about data asks no run and no closing fact
  let t ← Lean.Meta.inferType (mkConst ``Tools.ShippingMachineClosesData.closes_of_data)
  Lean.Meta.forallTelescope t fun xs _ => do
    for x in xs do
      let ty ← Lean.Meta.inferType x
      for c in [``Tools.ShippingMachineEntry.MachineCloses, ``Tools.ShippingEntrySoundness.RunsTo,
          ``Sparkle.IR.Machine.closeLets, ``Tools.ShippingMachineEntry.MachineDefines] do
        if (ty.find? (·.isConstOf c)).isSome then throwError "closes_of_data assumes {c}"
  let mut report := #[]
  for f in [``reflSharedLet, ``reflAliasLet, ``closesInputLet, ``closesOpAlias, ``closesChain] do
    let r ← Tools.ShippingMachineCommand.readMachine f
    unless r.shape.insts.isEmpty do throwError "{f}: has calls"
    unless env.contains (f ++ `machine_closes) do throwError "{f}: no machine_closes"
    std (f ++ `machine_closes)
    let mut closed := #[]
    for s in ["machine_sound", "machine_ships", "machine_ships_wired"] do
      let orig := f ++ Name.mkSimple s
      let n := f ++ Name.mkSimple (s ++ "_closed")
      unless env.contains orig do continue
      -- the generated endpoint asks `MachineCloses`; its closed form does not
      let some ci := env.find? orig | throwError "{orig}"
      unless (ci.type.find? (·.isConstOf ``Tools.ShippingMachineEntry.MachineCloses)).isSome do
        throwError "{orig}: no MachineCloses premise to discharge"
      let some ci := env.find? n | throwError "{n}: not generated"
      if (ci.type.find? (·.isConstOf ``Tools.ShippingMachineEntry.MachineCloses)).isSome then
        throwError "{n}: MachineCloses is still in the type"
      unless (ci.type.find? (·.isConstOf ``Tools.ShippingEntrySoundness.RunsTo)).isSome &&
          (ci.type.find? (·.isConstOf ``Tools.ShippingMachineEntry.MachineDefines)).isSome do
        throwError "{n}: not about a run of the entry"
      std n
      closed := closed.push s
    unless closed.contains "machine_sound" do throwError "{f}: machine_sound_closed missing"
    report := report.push m!"{f}: lets={r.shape.layout.lets} closed={closed}"
  -- a declaration with a call: not derived here, the premise stays
  for f in [``Sparkle.Tests.Compiler.ShippingMachineInstTest.caller] do
    if env.contains (f ++ `machine_closes) || env.contains (f ++ `machine_sound_closed) then
      throwError "{f}: a shape with calls is closed"
  Lean.logInfo m!"MACHINE CLOSES FROM DATA (let shapes, no call; MachineCloses absent from the closed endpoints' types, standard axioms): {report}; with calls: premise kept"

/-! The check on `let`s that are variables, on data (two inputs at binder
positions 0, 1; `let`s from position 2):

* a field that is an input — accepted;
* a field that is the variable of an earlier `let` whose field is a variable —
  accepted (the real `closeLets` puts both aliases at the front, in order);
* a field that is the variable of a `let` with a driven field — NOT accepted:
  the real `closeLets` refuses that transition (the regression in
  `ShippingReflectCtxTest`), so `MachineCloses` is false there. The shape
  reader resolves `let b := a` to `a`'s definition (`closesOpAlias` has one
  hardware `let`), so no source tried reaches it. -/
example : aliasOk (fun _ => 0) (fun j => j) 2 [⟨8, .bitsInput 8 0⟩] = true := by decide
example : aliasOk (fun _ => 0) (fun j => j) 2 [⟨8, .bitsInput 8 0⟩, ⟨8, .bitsInput 8 2⟩] = true := by
  decide
example : aliasOk (fun _ => 0) (fun j => j) 2
    [⟨8, .binary .add (.bitsInput 8 0) (.bitsInput 8 0)⟩, ⟨8, .bitsInput 8 2⟩] = false := by decide
example : aliasOk (fun _ => 0) (fun j => j) 2
    [⟨8, .binary .add (.bitsInput 8 0) (.bitsInput 8 1)⟩,
     ⟨8, .binary .add (.bitsInput 8 2) (.bitsInput 8 0)⟩] = true := by decide

/-! With calls: `MachineCloses` is `LetsClose ∧ CallsClose`
(`machineCloses_iff`), and `LetsClose` is proved from the same data. On the
real callers (2 `let`s and a call each) the `let` half holds in every
context; the calls' half (`CallsClose`) stays a premise — nothing here
discharges it. -/
section
open Sparkle.Tests.Compiler.ShippingMachineInstTest

theorem caller_letsClose (mctx mref cctx cref) :
    Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref ``caller caller.machineData.shape :=
  letsClose_of_data _ caller.machine_ok caller.machine_body (Eq.refl true) mctx mref cctx cref

theorem callerTwice_letsClose (mctx mref cctx cref) :
    Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref ``callerTwice
      callerTwice.machineData.shape :=
  letsClose_of_data _ callerTwice.machine_ok callerTwice.machine_body (Eq.refl true)
    mctx mref cctx cref

theorem callerNested_letsClose (mctx mref cctx cref) :
    Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref ``callerNested
      callerNested.machineData.shape :=
  letsClose_of_data _ callerNested.machine_ok callerNested.machine_body (Eq.refl true)
    mctx mref cctx cref

end

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``caller_letsClose, ``callerTwice_letsClose, ``callerNested_letsClose,
      ``Tools.ShippingClosesSplit.machineCloses_iff,
      ``Tools.ShippingMachineClosesData.closes_of_data_calls] do
    for a in ← Lean.collectAxioms n do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        throwError "{n} depends on {a}"
  -- what is left with calls is named in the type: `CallsClose`, a premise
  let t ← Lean.Meta.inferType (mkConst ``Tools.ShippingMachineClosesData.closes_of_data_calls)
  unless (t.find? (·.isConstOf ``Tools.ShippingClosesSplit.CallsClose)).isSome do
    throwError "closes_of_data_calls: CallsClose is not a premise"
  Lean.logInfo m!"WITH CALLS: closeLets accepts every harness run's transition of caller, callerTwice, callerNested (proved, every context); the calls' closing (CallsClose) remains a premise"

/-! The calls' closing from an invariant world (`Tools/ShippingCallsClose.lean`):
`MachineClosesAt` — no fallback from worlds satisfying the child-cache
invariant, with the compiler's logger — follows from `LetsClose` and
`CallsPure` under the generic runtime laws. `CallsPure` (the pure
`closeInsts` / `closeInstsG` succeed on real children) is a premise there; it
is not proved, and the endpoints still ask `MachineCloses`. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Tools.ShippingChildInv.closeInstsM_run, ``Tools.ShippingChildInv.closeInstsGM_run,
      ``Tools.ShippingChildInv.machineClosesAt_of_pure, ``Tools.ShippingChildInv.machineClosesAt_of_closes] do
    for a in ← Lean.collectAxioms n do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        throwError "{n} depends on {a}"
  let t ← Lean.Meta.inferType (mkConst ``Tools.ShippingChildInv.machineClosesAt_of_pure)
  Lean.Meta.forallTelescope t fun xs _ => do
    let mut pure := false
    for x in xs do
      let ty ← Lean.Meta.inferType x
      if (ty.find? (·.isConstOf ``Tools.ShippingMachineEntry.MachineCloses)).isSome then
        throwError "machineClosesAt_of_pure assumes MachineCloses"
      if (ty.find? (·.isConstOf ``Tools.ShippingChildInv.BodyRel)).isSome then
        throwError "machineClosesAt_of_pure assumes BodyRel"
      if ty.isAppOf ``Tools.ShippingChildInv.CallsPure then pure := true
    unless pure do throwError "machineClosesAt_of_pure: CallsPure is not a premise"
  Lean.logInfo m!"CALLS FROM AN INVARIANT WORLD: a run of closeInstsM / closeInstsGM is the pure closing of real children (module or nothing); MachineClosesAt from LetsClose + CallsPure under RefLaws; CallsPure is NOT proved"

/-! The pure side of the calls' closing (`closeInsts`): it returns a module
when its four steps succeed (`closeInsts_some_of`); the reordering succeeds
and the checks hold from facts about the closed body and the instance
statements (`closeChecks_of`, with `topoBody_some_rank`, `rank_of_names`,
`woCheck_ordered`, `linkedOk_ordered`); the closed machine's body gives the
static ones (`closeMachine_body`, `static_checks`). NOT proved, and still
premises of `closeChecks_of`: the rank on names for a real transition, the
instance statements (`instStmtsOf`), the agreement of each instance with its
child's ports, the design facts (name resolution, `noInstOfB`,
`kidsCombB`). No endpoint uses these theorems yet. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Tools.ShippingTopoBody.topoBody_some, ``Tools.ShippingTopoBody.topoBody_some_rank,
      ``Tools.ShippingTopoBody.rank_of_names, ``Tools.ShippingTopoChecks.woCheck_ordered,
      ``Tools.ShippingTopoChecks.isPermOf_complete, ``Tools.ShippingTopoLinked.linkedOk_ordered,
      ``Tools.ShippingCloseInstsSome.closeInsts_some_of, ``Tools.ShippingCloseChecks.closeChecks_of,
      ``Tools.ShippingCloseMachineFacts.closeMachine_body,
      ``Tools.ShippingCloseMachineFacts.static_checks] do
    for a in ← Lean.collectAxioms n do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        throwError "{n} depends on {a}"
  -- `closeInsts_some_of` concludes about the REAL `closeInsts`
  let t ← Lean.Meta.inferType (mkConst ``Tools.ShippingCloseInstsSome.closeInsts_some_of)
  unless (t.find? (·.isConstOf ``Sparkle.IR.Machine.closeInsts)).isSome do
    throwError "closeInsts_some_of is not about closeInsts"
  Lean.logInfo m!"CLOSEINSTS, PURE SIDE: four steps ⇒ a module; topoBody does not get stuck given a rank; woCheck / isPermOf / seqOf / linkedOk of its result; the closed machine's body is ordered assignments around registers — standard axioms. OPEN (premises, no endpoint uses this yet): the rank for a real transition, the instance statements, instance/child agreement, name resolution, noInstOfB, kidsCombB"

/-! The rank for the one-output closing: `rank_closed` (pure: `rho` orders the
closed body given what each kind of statement reads) and `transition_fields`
(a real harness run: the per-field read facts for any split of the binders —
the calls' output ports included). They are NOT yet joined: the hypotheses of
`rank_closed` are not derived from `transition_fields` for a real transition,
and the instance / child / design facts are open. `rank_of_names` and
`rank_closed` assume one driven name per statement: B1 only, not the
several-output closing. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Tools.ShippingCallsRank.rank_closed, ``Tools.ShippingTransitionFields.transition_fields,
      ``Tools.ShippingRankNames.lt_body_body, ``Tools.ShippingCloseMachineFacts.named_of_typed] do
    for a in ← Lean.collectAxioms n do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        throwError "{n} depends on {a}"
  -- `transition_fields` is about a run of the real harness and assumes no closing fact
  let t ← Lean.Meta.inferType (mkConst ``Tools.ShippingTransitionFields.transition_fields)
  Lean.Meta.forallTelescope t fun xs _ => do
    let mut run := false
    for x in xs do
      let ty ← Lean.Meta.inferType x
      if (ty.find? (·.isConstOf ``Sparkle.Compiler.Elab.bindMixedCertifiedInputs)).isSome then run := true
      for c in [``Sparkle.IR.Machine.closeLets, ``Sparkle.IR.Machine.closeInsts,
          ``Tools.ShippingMachineEntry.MachineCloses] do
        if (ty.find? (·.isConstOf c)).isSome then throwError "transition_fields assumes {c}"
    unless run do throwError "transition_fields is not about a harness run"
  Lean.logInfo m!"RANK (B1, one output per statement): rank_closed (pure) and transition_fields (real harness run, any binder split incl. call outputs) — standard axioms; NOT joined yet: the hypotheses of rank_closed are not derived for a real transition"

/-! The rank joined to a run's facts: `rank_of_facts` (from the `Facts` of
`letOperands_facts` under `okRule` — a call's output is read only once its
argument `let`s are passed) and `closed_classes` (the closed body's
statements by kind). Still hypotheses there: the instance statements and
that every call has a bound for its argument `let`s. NOT derived anywhere
yet, for the child: its module's interface at the FULL entry and
`kidsCombB` — `readsClosedB` asks that every name a child statement reads is
an input or driven EARLIER, which no proved invariant of the translator
states (the order invariant says "not driven later"). No endpoint has lost
its closing premise. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Tools.ShippingRankRun.rank_of_facts, ``Tools.ShippingRankRun.closed_classes,
      ``Tools.ShippingRankRun.facts_pres] do
    for a in ← Lean.collectAxioms n do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        throwError "{n} depends on {a}"
  Lean.logInfo m!"RANK OF A RUN (B1): rank_of_facts, closed_classes — standard axioms; open: instance statements, the child's interface and kidsCombB (needs a new invariant: every read is an input or driven earlier), design name resolution"
