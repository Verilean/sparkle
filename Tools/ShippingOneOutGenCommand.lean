import Tools.ShippingOneOutFullCommand
import Tools.ShippingOneOutConns
import Tools.ShippingGatePorts
import Tools.ShippingPortsMatchShipped
import Tools.ShippingHierGateAny
import Tools.ShippingChecksCoreGate
import Tools.ShippingChecksGate
import Tools.ShippingCombKidText
import Tools.ShippingMachineClosesAtGen
import Tools.ShippingReaderOutsInv
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md).

/-! # `#machine_oneout f`: the four per-declaration theorems of the one-output head, GENERATED (G1, round par/a-9)

`#machine_design_svH_full f [facts, typed, design, outs]` needs four
theorems per declaration; for `caller` they were written by hand
(`Tests/Compiler/OneOutCallerTest.lean`, `OneOutCallerPortsTest.lean`).
This command writes them for a declaration `f` in scope, as the SAME
applications of the SAME general theorems at `f`'s reflected data, and then
runs that command's `buildFull`.

## Scope (anything else is REFUSED, with its reason, before anything is generated)

* `f.machine_ships_hierHR` exists (`#machine_design_svHR f`), and
  `f.machineData`, `f.machine_ok`, `f.machine_body` (`#machine_endpoint f`);
* `f` is a machine shape with at least one call;
* the parent has a register: `shape.layout.slots ≠ []` (the head asks
  `"rst" ∈ b.inputs`). A slotless parent is REFUSED;
* `shape.instFields = []`: the ONE-OUTPUT closing `closeInsts`;
* no callee is a memory module; every callee is a GATE child with what
  `#gate_child` left (`gate_peel`, `gate_old`, `gate_wf`, `gateBinders`,
  `gateSort`, `gateValue`). A machine-route callee is REFUSED.

"The parent has a register" and "the child is combinational" are separate
conditions here, as in the general theorems.

## What is generated

Per distinct gate callee `c` (once; an existing constant of the name is
re-derived and compared):

    c.gate_full   : EntryDefines … c c.gateValue → RealChild … c y → ChildFull c c.gateBinders y.1 y.2
    c.gate_ports  : … → GateChildPorts c c.gateBinders (SType.width c.gateSort) y.1
    c.gate_kidK   : … → the children's text check of y (gate_real_kidK)
    c.gate_width  : SType.width c.gateSort = W        (W a numeral, by rfl / decide)

Per declaration `f`, the DATA CONDITIONS, each a named theorem proved by
the kernel's `decide` / `rfl` on the reflected `f.machineData` — a failed
one makes the command FAIL naming the condition; the endpoint then does not
exist for `f`, nothing false is proved:

    f.oneout_callsOk     d.callsOk nDecl = true
    f.oneout_slotLen     d.ss.length = d.shape.layout.slots.length
    f.oneout_domB        no domain binder after the first nDecl
    f.oneout_insts       d.shape.insts ≠ []
    f.oneout_instFields  d.shape.instFields = []
    f.oneout_outTy       every output's ty.bitWidth = width      (previous data path only, see below)
    f.oneout_nomem       no memory callee
    f.oneout_slots       d.shape.layout.slots ≠ []
    f.oneout_outChars    the output names are character-wise charOk
    f.oneout_outScalar   the output types are scalarTy           (previous data path only, see below)
    f.oneout_kidIns      (a definition) the argument widths per call entry,
                         NUMERALS computed by the generator from the widths of
                         the types of f's `let` binders of each call's arguments
    f.oneout_callArgs    callArgsOk d nDecl f.oneout_kidIns = true
    f.oneout_entries     for every entry k: its callee is c, f.oneout_kidIns k is
                         the list of the widths of c's declared non-domain
                         binders, and the width of the type of the result binder
                         binders[nDecl + k] is W (the numeral of c.gate_width);
                         with several callees a disjunction over them — no
                         entry count is written in a proof

`f.oneout_kidIns` is computed from the PARENT's data, so `f.oneout_callArgs`
alone would be circular; the check with content is `f.oneout_entries`, which
compares those numerals with the CALLEE's binders. Together they are the
hand instance's `callArgsOk caller.machineData 1 kidIns`.

Then the theorems (binders: the contexts, the worlds, `raw b D`, the core
run, the post-processing fact, `MachineDefines f`, `MachineClosesAt f`,
`ChildBnd`, and one `EntryDefines` per distinct callee where it is used):

    f.machine_factsH         RunFactsH D.modules b                       core_runFactsH
    f.machine_outsH          hierGate b → outsCheck … 0 (checkedOptimize b)   core_outsCheck_all_gate
    f.machine_portsRawH      portsMatchB (childMap D.modules) b          core_portsMatch_raw₁
    f.machine_portsShippedH  portsMatchB … (checkedOptimize b)           portsMatchB_shipped
    f.machine_hierTypedH     hierTyped (childMap D.modules) b            core_hierTyped₁
    f.machine_designFullH    designCheck … 0 (checkedOptimize b)         core_designCheckH

and `f.machine_design_svH_full` (+ `_closed` when `f.machine_closes_at`
exists) by `Tools.ShippingOneOutFullCommand.buildFull`.

## The generation contract

* Every run re-derives every statement from `f`'s data as read NOW.
* A name already present is never trusted and never silently reused: the
  constant is generated again under a scratch name, the two types (for the
  definition `f.oneout_kidIns` also the values) are compared by `isDefEq`,
  the scratch environment is dropped; any difference is an error.
* The endpoint: when `f.machine_design_svH_full` is free it is added with
  the record `fullMarker` of the four generated lemma names (GENERATED).
  When it exists, its statement must be `isDefEq` the statement rebuilt now
  from the four GENERATED lemmas, on standard axioms. If its record names
  the same four lemmas: PRESENT, verified. If it was recorded as built from
  OTHER lemmas (the hand instance of `caller`), the proof rebuilt now is
  additionally kernel-checked under `f.machine_design_svH_full_gen` (same
  statement, the generator's record) and the outcome says so: PRESENT,
  statement verified, the two records named. No silent return.
* The refuse scans of `Tools.ShippingOneOutCommand.refuse` (direct and the
  bounded delta expansion; their limits are in that file's header) run on
  the statement and on the closed form's, with no declared residual.
* On REFUSED or FAILED the environment and the message log are put back:
  nothing is left under `f`'s or the callees' names.

The command must be run under `set_option maxHeartbeats 0 in`.

## What a generated endpoint does NOT say (binding for any report)

The data conditions above are decided PER DECLARATION; they are conditions
on the reflected data, not reductions. `MachineDefines`, `EntryDefines`,
`ChildBnd` and the run stay premises (no runtime model). The conclusion is
about `DesignSV (childMap D.modules) 0 (checkedOptimize b)` — the module
list, not the SV string, not `#sim`. One declaration at a time: a register
parent, gate children, the one-output closing. NOT slotless parents, NOT
machine-route children, NOT several outputs, NOT "all successful inputs".

## The output facts from the reader (round par/r-5; WRITTEN, NOT BUILT)

`#machine_oneout f` no longer decides `f.oneout_outTy` and
`f.oneout_outScalar`. The six lemmas of the head pass, in their place,

    Tools.ShippingReaderOutsInv.outTy_of_core hcore entry       (all six)
    Tools.ShippingReaderOutsInv.outScalar_of_core hcore entry   (portsRawH, hierTypedH, designFullH)

— the general theorems over EVERY reader result (BUILT), at the run
hypotheses `hcore`, `entry` that `mkThm` binds in each of them. EVERY
generated STATEMENT is unchanged; only the six proofs differ, and the two
decided lemmas are not generated.

Consumers of the two names, READ: `Tools.ShippingNoPortsKidsCommand`
(`oneOutKidTheorem`: the `OneOutKid` fields `outTy` / `outScalar` of a
one-output CALLEE `k`, and the prerequisite list of its scope) and
`Tools.ShippingNoPortsDeepCommand` (the same prerequisite list). There is
NO run of the callee in scope (only `MachineDefines k`), so the reader
lemmas do not apply: those fields are now `first | exact k.oneout_outTy |
decide` (the decide moves to the consumer, for a consumed callee only), and
the two names left the prerequisite lists.

The PREVIOUS path stays reachable as `#machine_oneout_olddata f` /
`#machine_oneout_olddata_try f "…"`: it decides the two lemmas and passes
them, and — to leave something to compare — KEEPS the scratch constant of
every PARENT name it re-derives (`n.oneout_expected`: the data lemmas, the
definition `kidIns`, the six lemmas) instead of dropping it
(`emitOrVerify (keep := true)`); the callees' facts are compared and dropped
as before. Run after the default path on one declaration
(`Tests/Compiler/OneOutGenOldDataTest.lean`, target-only).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingOneOutGenCommand
open Lean Meta Elab Command

/-- What a run of the generator did. -/
inductive Outcome where
  | generated (made : List Name) (note : String)
  | present (made : List Name) (note : String)
  | refused (reason : String)
  | failed (cond : String)

/-- The class of an outcome, as the test names it. -/
def Outcome.tag : Outcome → String
  | .generated .. => "GENERATED"
  | .present .. => "PRESENT"
  | .refused .. => "REFUSED"
  | .failed .. => "FAILED"

/-- The log line. -/
def Outcome.line (f : Name) : Outcome → String
  | .generated made note => s!"ONEOUT GEN {f}: GENERATED {made} — {note}"
  | .present made note => s!"ONEOUT GEN {f}: PRESENT {made} — {note}"
  | .refused reason => s!"ONEOUT GEN {f}: REFUSED ({reason})"
  | .failed cond => s!"ONEOUT GEN {f}: FAILED ({cond})"

/-- What the scope test read. -/
structure Info where
  r : Tools.ShippingMachineCommand.Read
  /-- The callee of every entry. -/
  calls : List Name
  /-- The distinct callees. -/
  kids : List Name
  /-- Per entry: the widths of the types of the parent's `let` binders of the
  call's arguments. -/
  kidIns : List (List Nat)
  /-- Per distinct callee: the width of the type of the parent's result
  binder of its first entry. -/
  resW : List Nat

/-- The scope test; every `throwError` here is a REFUSAL. -/
def scope (f : Name) : CommandElabM Info := do
  let env ← getEnv
  let ships := f ++ `machine_ships_hierHR
  unless env.contains ships do
    throwError "no {ships}: run #machine_design_svHR {f} first"
  for s in [`machineData, `machine_ok, `machine_body] do
    let need := f ++ s
    unless env.contains need do
      throwError "no {need}: run #machine_endpoint {f} first"
  let r ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine f
  let calls := r.shape.insts.map (·.1)
  if calls.isEmpty then throwError "no call"
  if r.shape.layout.slots.isEmpty then
    throwError "parent without a register: the head needs shape.layout.slots ≠ [] (slotless parents are not covered)"
  unless r.shape.instFields.isEmpty do
    throwError "instFields ≠ []: not the one-output closing (several outputs or a sequential child)"
  let kids := calls.eraseDups
  for c in kids do
    if (Sparkle.Compiler.MachMemory.memChild? c).isSome then
      throwError "memory callee {c}"
    for s in [`gate_peel, `gate_old, `gate_wf, `gateBinders, `gateSort, `gateValue] do
      let need := c ++ s
      unless env.contains need do
        if env.contains (c ++ `machineData) then
          throwError "callee {c} is a machine-route child, not a gate child (no {need})"
        else
          throwError "callee {c} is not a gate child with #gate_child data (no {need})"
  -- the numerals, from the parent's reflected data
  let nD := r.nDecl
  let nI := r.shape.insts.length
  let nS := r.shape.layout.slots.length
  let wOf (p : Nat) : Option Nat :=
    (r.shape.binders[p]?).map fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth
  let mut kidIns : Array (List Nat) := #[]
  for c in r.shape.insts do
    let mut ws : Array Nat := #[]
    for a in c.2.1 do
      match wOf (nD + (nI + (nS + a))) with
      | some wd => ws := ws.push wd
      | none => throwError "the argument `let` {a} of a call of {c.1} has no binder in the reflected data"
    kidIns := kidIns.push ws.toList
  let mut resW : Array Nat := #[]
  for c in kids do
    match wOf (nD + calls.idxOf c) with
    | some wd => resW := resW.push wd
    | none => throwError "the result binder of the first call of {c} is not in the reflected data"
  return { r, calls, kids, kidIns := kidIns.toList, resW := resW.toList }

/-- Elaborate one generated command; an error message, a thrown error, a
missing constant or a non-standard axiom is a FAILURE naming `cond`. -/
def emit (name : Name) (cond : String) (stx : Syntax) : CommandElabM Unit := do
  let before := (← get).messages.toList.length
  try
    withScope (fun s => { s with opts := maxRecDepth.set (Lean.Elab.async.set s.opts false) 100000 })
      (elabCommand stx)
  catch ex =>
    throwError "{cond} [{name}]: {ex.toMessageData}"
  let msgs := (← get).messages.toList.drop before
  if msgs.any (·.severity == .error) || !(← getEnv).contains name then
    let errs ← (msgs.filter (·.severity == .error)).mapM fun m => m.data.toString
    throwError "{cond} [{name}]: {errs.take 2}"
  liftCoreM do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{cond} [{name}]: non-standard axiom {ax}"

/-- ADD `name` (`true`), or — when it exists — generate it again under a
scratch name, COMPARE and drop the scratch (`false`). Never a silent reuse.
`keep` (par/r-5, the previous data path of the comparison): the scratch
`name.oneout_expected` is KEPT (an error if it exists already). -/
def emitOrVerify (name : Name) (cond : String)
    (mk : Ident → CommandElabM (TSyntax `command)) (keep : Bool := false) :
    CommandElabM Bool := do
  if (← getEnv).contains name then
    let saved ← getEnv
    let scratch := name ++ `oneout_expected
    if keep && (← getEnv).contains scratch then
      throwError "{cond} [{name}]: the kept scratch {scratch} exists already (the previous data path was run twice)"
    emit scratch cond (← mk (mkIdent (`_root_ ++ scratch)))
    let some exp := (← getEnv).find? scratch
      | throwError "{cond} [{name}]: the scratch constant is missing"
    unless keep do setEnv saved
    let some cur := (← getEnv).find? name
      | throwError "{cond} [{name}]: lost"
    let same ← liftTermElabM do
      unless cur.levelParams.isEmpty && exp.levelParams.isEmpty do return false
      unless ← isDefEq cur.type exp.type do return false
      match cur, exp with
      | .thmInfo _, .thmInfo _ => return true
      | .defnInfo a, .defnInfo b => isDefEq a.value b.value
      | _, _ => return false
    unless same do
      throwError "{cond} [{name}]: exists with ANOTHER statement than the one generated now"
    liftCoreM do
      for ax in ← Lean.collectAxioms name do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "{cond} [{name}] (existing): non-standard axiom {ax}"
    return false
  else
    emit name cond (← mk (mkIdent (`_root_ ++ name)))
    return true

/-- A theorem of the four lemmas' form: the contexts, the worlds, `raw b D`,
the core run, the post-processing fact, the parent's reflection and closing,
(`gate`: the statement-kind gate,) `ChildBnd`, then `binders`. -/
def mkThm (id : Ident) (fq : Term) (data : Ident)
    (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (gate : Bool)
    (concl proof : Term) : CommandElabM (TSyntax `command) :=
  if gate then
    `(command|
      theorem $id {mctx : Lean.Meta.Context}
          {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
          {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
          {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
          (hcore : Tools.ShippingEntrySoundness.RunsTo
            (Sparkle.Compiler.Elab.synthesizeCombinationalCore $fq [] false)
            mctx mref cctx cref w (raw, D) w1)
          (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
            b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
          (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $fq ($data).shape)
          (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref $fq ($data).shape)
          (hg : Sparkle.IR.RefineCheck.hierGate b = true)
          (hB : Tools.ShippingChildInv.ChildBnd mref cref w) $binders* : $concl := $proof)
  else
    `(command|
      theorem $id {mctx : Lean.Meta.Context}
          {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
          {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
          {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
          (hcore : Tools.ShippingEntrySoundness.RunsTo
            (Sparkle.Compiler.Elab.synthesizeCombinationalCore $fq [] false)
            mctx mref cctx cref w (raw, D) w1)
          (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
            b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
          (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $fq ($data).shape)
          (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref $fq ($data).shape)
          (hB : Tools.ShippingChildInv.ChildBnd mref cref w) $binders* : $concl := $proof)

/-- The per-entry case split, with no entry count: `ent k hk` is the fact of
entry `k` (one callee) or a disjunction over the `n` distinct callees; in
case `i` the names `hc` (the callee is the `i`-th), `hki` (its argument
widths) and `hres` (the result binder's width) are bound and `body i` must
close the goal. The surrounding proof has introduced `k hk`. -/
def perEntry (ent : Ident) (n : Nat) (body : Nat → CommandElabM (TSyntax `tactic)) :
    CommandElabM (TSyntax `tactic) := do
  if n ≤ 1 then
    let b ← body 0
    `(tactic| (obtain ⟨hc, hki, hres⟩ := $ent k hk; $b:tactic))
  else
    let last ← body (n - 1)
    let mut tac ← `(tactic| (obtain ⟨hc, hki, hres⟩ := hcase; $last:tactic))
    for i' in [0:n - 1] do
      let i := n - 2 - i'
      let b ← body i
      tac ← `(tactic| (rcases hcase with ⟨hc, hki, hres⟩ | hcase; $b:tactic; $tac:tactic))
    `(tactic| (have hcase := $ent k hk; $tac:tactic))

/-- The endpoint from the four generated lemmas: ADDED, or VERIFIED against
an existing constant (see the header). Returns the name, whether it was
added now, and the note of the outcome. -/
def endpoint (f : Name) (facts typed design outs : Name) : MetaM (Name × Bool × String) := do
  let name := f ++ `machine_design_svH_full
  let (type, value) ← Tools.ShippingOneOutFullCommand.buildFull f facts typed design outs
  Tools.ShippingOneOutCommand.refuse name type (mkConst ``True)
  let marker := Tools.ShippingOneOutFullCommand.fullMarker facts typed design outs
  let std (n : Name) : MetaM Unit := do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  let recordedIn (n : Name) : MetaM (Bool × String) := do
    let doc? ← Lean.findDocString? (← getEnv) n
    match doc? with
    | some doc => return ((doc.splitOn marker).length > 1, doc)
    | none => return (false, "no record")
  if (← getEnv).contains name then
    let some (.thmInfo ni) := (← getEnv).find? name
      | throwError "{name} exists and is not a theorem"
    unless ni.levelParams.isEmpty do
      throwError "{name} exists with universe parameters"
    unless ← isDefEq ni.type type do
      throwError "{name}: it exists with ANOTHER statement than the one the generated lemmas produce.\nexisting:{indentExpr ni.type}\nrebuilt now:{indentExpr type}"
    std name
    let (same, doc) ← recordedIn name
    if same then
      return (name, false, s!"already present, statement verified against the generated lemmas (rebuilt, compared by isDefEq), recorded lemmas equal; {marker}")
    -- recorded as built from other lemmas: the proof rebuilt now is
    -- kernel-checked under its own name, with the generator's record
    let alt := f ++ `machine_design_svH_full_gen
    if (← getEnv).contains alt then
      let some (.thmInfo ai) := (← getEnv).find? alt
        | throwError "{alt} exists and is not a theorem"
      unless ai.levelParams.isEmpty && (← isDefEq ai.type type) do
        throwError "{alt}: it exists with ANOTHER statement than the one rebuilt now"
      let (sameAlt, docAlt) ← recordedIn alt
      unless sameAlt do
        throwError "{alt}: it exists but is not recorded as built from the generated lemmas.\nrecorded: {docAlt}\ngiven now: {marker}"
      std alt
    else
      Tools.ShippingMachineLinkedCommand.addTheorem alt type value
      addDocStringCore alt marker
    return (name, false, s!"already present, statement verified against the generated lemmas (rebuilt, compared by isDefEq); the existing constant is recorded as built from OTHER lemmas ({doc}); the proof rebuilt now from the generated lemmas is kernel-checked as {alt} (same statement); {marker}")
  Tools.ShippingMachineLinkedCommand.addTheorem name type value
  addDocStringCore name marker
  return (name, true, s!"the combinational endpoint with NO check antecedent and no residual, from generated lemmas; {marker}")

/-- Everything after the scope test; every `throwError` here is a FAILURE. -/
def oneOutCore (f : Name) (info : Info) (oldData : Bool := false) :
    CommandElabM (List Name × Bool × String) := do
  let r := info.r
  let kids := info.kids
  let nm (d : Name) (s : String) : Ident := mkIdent (`_root_ ++ d ++ Name.mkSimple s)
  let data := nm f "machineData"
  let okI := nm f "machine_ok"
  let bodyI := nm f "machine_body"
  let fq : Term := quote f
  let nDecl := Syntax.mkNumLit (toString r.nDecl)
  let dn (s : String) : Name := f ++ Name.mkSimple ("oneout_" ++ s)
  let dl (s : String) : Ident := nm f ("oneout_" ++ s)
  let hR (j : Nat) : Ident := mkIdent (Name.mkSimple s!"hR{j}")
  -- ## the gate callees' facts, once per callee
  for i in [0:kids.length] do
    let c := kids[i]!
    let cq : Term := quote c
    let wLit := Syntax.mkNumLit (toString (info.resW.getD i 0))
    discard <| emitOrVerify (c ++ `gate_full) s!"child facts {c}.gate_full" fun id =>
      `(command|
        theorem $id {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
            {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
            (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref $cq
              $(nm c "gateValue"))
            {y : Tools.ShippingChildInv.Res}
            (hy : Tools.ShippingChildInv.RealChild mref cref $cq y) :
            Tools.ShippingGateChildComb.ChildFull $cq $(nm c "gateBinders") y.1 y.2 :=
          Tools.ShippingCallsGate.childFull_of_real hR0 $(nm c "gate_old") $(nm c "gate_peel")
            $(nm c "gate_wf") (Tools.ShippingGateChild.bool_positions (by decide))
            (Tools.ShippingGateChild.bits_positions (by decide)) hy)
    discard <| emitOrVerify (c ++ `gate_ports) s!"child facts {c}.gate_ports" fun id =>
      `(command|
        theorem $id {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
            {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
            (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref $cq
              $(nm c "gateValue"))
            {y : Tools.ShippingChildInv.Res}
            (hy : Tools.ShippingChildInv.RealChild mref cref $cq y) :
            Tools.ShippingGatePorts.GateChildPorts $cq $(nm c "gateBinders")
              (Tools.ShippingUnifiedSource.SType.width $(nm c "gateSort")) y.1 :=
          Tools.ShippingGatePorts.gate_real_ports hR0 $(nm c "gate_old") $(nm c "gate_peel")
            $(nm c "gate_wf") (Tools.ShippingGateChild.bool_positions (by decide))
            (Tools.ShippingGateChild.bits_positions (by decide)) hy)
    discard <| emitOrVerify (c ++ `gate_kidK) s!"child facts {c}.gate_kidK" fun id =>
      `(command|
        theorem $id {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
            {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
            (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref $cq
              $(nm c "gateValue"))
            {y : Tools.ShippingChildInv.Res}
            (hy : Tools.ShippingChildInv.RealChild mref cref $cq y) :
            (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
                Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
              ∀ g ∈ y.2.modules,
                ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
                  (n : Nat), Tools.ShippingChecksDesign.kidCheck C n g = true :=
          Tools.ShippingCombKidText.gate_real_kidK hR0 $(nm c "gate_old") $(nm c "gate_peel")
            $(nm c "gate_wf") (Tools.ShippingGateChild.bool_positions (by decide))
            (Tools.ShippingGateChild.bits_positions (by decide)) hy)
    discard <| emitOrVerify (c ++ `gate_width)
        s!"data condition {c}.gateSort.width = {info.resW.getD i 0} (the width of the type of {f}'s result binder of its first call of {c})" fun id =>
      `(command|
        theorem $id : Tools.ShippingUnifiedSource.SType.width $(nm c "gateSort") = $wLit := by
          first | rfl | decide)
  -- ## the parent's data conditions, each named
  let dataLemma (s cond : String) (ty pf : Term) : CommandElabM Unit := do
    discard <| emitOrVerify (keep := oldData) (dn s) s!"data condition {cond}" fun id =>
      `(command| theorem $id : $ty := $pf)
  dataLemma "callsOk" s!"callsOk {f}.machineData {r.nDecl}"
    (← `(Tools.ShippingMachineAuto.MachineData.callsOk $data $nDecl = true)) (← `(by decide))
  dataLemma "slotLen" "ss.length = shape.layout.slots.length"
    (← `(($data).ss.length = ($data).shape.layout.slots.length)) (← `(by decide))
  dataLemma "domB" s!"no domain binder after the first {r.nDecl}"
    (← `(∀ b ∈ ($data).shape.binders.drop $nDecl,
      b.2 ≠ Sparkle.Compiler.Elab.MixedGateBinder.domain)) (← `(by decide))
  dataLemma "insts" "shape.insts ≠ []"
    (← `(($data).shape.insts ≠ []))
    (← `(fun h0 => absurd (congrArg List.length h0) (by decide)))
  dataLemma "instFields" "shape.instFields = []"
    (← `(($data).shape.instFields = []))
    (← `(by first | rfl | decide))
  -- par/r-5: `outTy` / `outScalar` only on the previous data path
  if oldData then
    dataLemma "outTy" "every output's ty.bitWidth = width"
      (← `(∀ o ∈ ($data).shape.layout.outs, o.ty.bitWidth = o.width)) (← `(by decide))
  dataLemma "nomem" "no memory callee"
    (← `(∀ x ∈ ($data).shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true))
    (← `(by decide))
  dataLemma "slots" "shape.layout.slots ≠ [] (the parent has a register)"
    (← `(($data).shape.layout.slots ≠ []))
    (← `(fun h0 => absurd (congrArg List.length h0) (by decide)))
  dataLemma "outChars" "the output names are character-wise charOk"
    (← `(∀ o ∈ ($data).shape.layout.outs, ∀ c ∈ o.name.toList,
      Sparkle.IR.NameHints.charOk c = true))
    (← `(by first | decide | decide +kernel))
  if oldData then
    dataLemma "outScalar" "the output types are scalarTy"
      (← `(∀ o ∈ ($data).shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true))
      (← `(by decide))
  -- the argument widths per entry: numerals computed from the parent's data
  let mut rows : Array Term := #[]
  for ws in info.kidIns do
    let mut lits : Array Term := #[]
    for wd in ws do
      let l : Term := ⟨(Syntax.mkNumLit (toString wd)).raw⟩
      lits := lits.push l
    let row : Term ← `([$lits,*])
    rows := rows.push row
  discard <| emitOrVerify (keep := oldData) (dn "kidIns") "the definition of the argument widths" fun id =>
    `(command| def $id : Nat → List Nat := fun k => List.getD [$rows,*] k [])
  let kidInsI := dl "kidIns"
  dataLemma "callArgs" s!"callArgsOk {f}.machineData {r.nDecl} {f}.oneout_kidIns with {f}.oneout_kidIns = {info.kidIns}"
    (← `(Tools.ShippingPortsMatchRaw.callArgsOk $data $nDecl $kidInsI = true)) (← `(by decide))
  -- per entry: the callee, its argument widths, the result binder's width
  let alt (i : Nat) : CommandElabM Term := do
    let c := kids[i]!
    let cq : Term := quote c
    let wLit := Syntax.mkNumLit (toString (info.resW.getD i 0))
    `(((($data).shape.insts[k]).1 = $cq ∧
        $kidInsI k = ((($(nm c "gateBinders")).filter fun x =>
          x.2 != Sparkle.Compiler.Elab.MixedGateBinder.domain).map fun x =>
            (Tools.ShippingMachineEntry.kindTy x.2).bitWidth) ∧
        (($data).shape.binders[$nDecl + k]?).map
          (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) = some $wLit))
  let mut disj ← alt (kids.length - 1)
  for i' in [0:kids.length - 1] do
    let i := kids.length - 2 - i'
    disj ← `($(← alt i) ∨ $disj)
  dataLemma "entries"
    s!"per call entry: the callee among {kids}, {f}.oneout_kidIns k = the widths of the callee's declared non-domain binders ({info.kidIns}), and the result binder's width = the callee's sort width ({info.resW} per callee)"
    (← `(∀ (k : Nat) (hk : k < ($data).shape.insts.length), $disj)) (← `(by decide))
  let ent := dl "entries"
  -- ## the lemmas of the head
  let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let mut hRs : Array Term := #[]
  for j in [0:kids.length] do
    let c := kids[j]!
    let cq : Term := quote c
    binders := binders.push (← `(bracketedBinder|
      ($(hR j) : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref $cq
        $(nm c "gateValue"))))
    let t : Term := ⟨(hR j).raw⟩
    hRs := hRs.push t
  let n := kids.length
  let gf (i : Nat) : Ident := nm kids[i]! "gate_full"
  let gp (i : Nat) : Ident := nm kids[i]! "gate_ports"
  let gk (i : Nat) : Ident := nm kids[i]! "gate_kidK"
  let gw (i : Nat) : Ident := nm kids[i]! "gate_width"
  let tacA ← perEntry ent n fun i =>
    `(tactic| (rw [hc] at hy; exact Tools.ShippingChecksGate.gate_kidA ($(gf i) $(hR i) hy)))
  let tacR ← perEntry ent n fun i =>
    `(tactic| (rw [hc] at hy; exact Tools.ShippingChecksGate.gate_kidR ($(gf i) $(hR i) hy)))
  let tacW ← perEntry ent n fun i =>
    `(tactic| (rw [hc] at hy;
               exact hres.trans (congrArg Option.some
                 ((((($(gp i) $(hR i) hy).outWidth p hp).2).trans $(gw i)).symm))))
  let tacT ← perEntry ent n fun i =>
    `(tactic| (rw [hc] at hy; exact ($(gp i) $(hR i) hy).portsIn))
  let tacIn ← perEntry ent n fun i =>
    `(tactic| (rw [hc] at hy; rw [hki];
               obtain ⟨wd, h1, h2, -⟩ := ($(gp i) $(hR i) hy).inWidths hq;
               exact ⟨wd, h1, h2⟩))
  let tacTy ← perEntry ent n fun i =>
    `(tactic| (rw [hc] at hy; exact ($(gp i) $(hR i) hy).childTyped_ok))
  let tacInD ← perEntry ent n fun i =>
    `(tactic| (rw [hc] at hy; rw [hki];
               obtain ⟨wd, h1, -, h3⟩ := ($(gp i) $(hR i) hy).inWidths hq;
               exact ⟨wd, h1, h3⟩))
  let tacK ← perEntry ent n fun i =>
    `(tactic| (rw [hc] at hy; exact $(gk i) $(hR i) hy))
  let hon : Term ← `(fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean ($(dl "outChars") o ho))
  -- par/r-5: the two output facts from the reader at the run's `hcore` / `entry`
  -- (bound by `mkThm`); the previous data path: the decided lemmas
  let outTyT : Term ← if oldData then pure ⟨(dl "outTy").raw⟩
    else `((Tools.ShippingReaderOutsInv.outTy_of_core hcore entry))
  let outScalarT : Term ← if oldData then pure ⟨(dl "outScalar").raw⟩
    else `((Tools.ShippingReaderOutsInv.outScalar_of_core hcore entry))
  let factsN := f ++ `machine_factsH
  let outsN := f ++ `machine_outsH
  let rawN := f ++ `machine_portsRawH
  let shippedN := f ++ `machine_portsShippedH
  let typedN := f ++ `machine_hierTypedH
  let designN := f ++ `machine_designFullH
  let rawI := nm f "machine_portsRawH"
  let shippedI := nm f "machine_portsShippedH"
  discard <| emitOrVerify (keep := oldData) factsN s!"{factsN} (core_runFactsH at {f}'s data)" fun id => do
    mkThm id fq data #[] false
      (← `(Tools.ShippingOneOutFacts.RunFactsH D.modules b))
      (← `(Tools.ShippingOneOutFacts.core_runFactsH (nDecl := $nDecl) $data $okI $bodyI
        $(dl "callsOk") $(dl "slotLen") $(dl "domB") $(dl "insts") $(dl "instFields")
        $outTyT $(dl "nomem") hB hcore hpost entry closes $(dl "slots")))
  discard <| emitOrVerify (keep := oldData) outsN s!"{outsN} (core_outsCheck_all_gate at {f}'s data)" fun id => do
    mkThm id fq data binders true
      (← `(Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
        (Sparkle.IR.OptCheck.checkedOptimize b) = true))
      (← `(Tools.ShippingChecksCoreGate.core_outsCheck_all_gate (nDecl := $nDecl) $data $okI $bodyI
        $(dl "callsOk") $(dl "slotLen") $(dl "domB") $(dl "insts") $outTyT $(dl "nomem")
        (by
          intro k hk y hy
          $tacA:tactic)
        (by
          intro k hk y hy
          $tacR:tactic)
        hB hcore hpost entry closes hg 0))
  discard <| emitOrVerify (keep := oldData) rawN s!"{rawN} (core_portsMatch_raw₁ at {f}'s data)" fun id => do
    mkThm id fq data binders false
      (← `(Tools.ShippingDesignSV.portsMatchB (Tools.ShippingMachineLinked.childMap D.modules) b =
        true))
      (← `(Tools.ShippingOneOutConns.core_portsMatch_raw₁ (nDecl := $nDecl) $data $okI $bodyI
        $(dl "callsOk") $(dl "slotLen") $(dl "domB") $(dl "insts") $(dl "instFields")
        $outTyT $(dl "nomem")
        (by
          intro k hk y hy p hp
          $tacW:tactic)
        (by
          intro k hk y hy
          $tacT:tactic)
        (kidIns := $kidInsI) $(dl "callArgs")
        (by
          intro k hk y hy j q hq
          $tacIn:tactic)
        hB hcore hpost entry closes $hon $outScalarT))
  discard <| emitOrVerify (keep := oldData) shippedN s!"{shippedN} (portsMatchB_shipped)" fun id => do
    mkThm id fq data binders false
      (← `(Tools.ShippingDesignSV.portsMatchB (Tools.ShippingMachineLinked.childMap D.modules)
        (Sparkle.IR.OptCheck.checkedOptimize b) = true))
      (← `(Tools.ShippingPortsMatchShipped.portsMatchB_shipped
        (Tools.ShippingHierGateAny.core_hierGate_any (nDecl := $nDecl) $data $okI $bodyI
          $(dl "callsOk") $(dl "slotLen") $(dl "domB") $(dl "insts") $outTyT $(dl "nomem")
          hB hcore hpost entry closes)
        ($rawI hcore hpost entry closes hB $hRs*)))
  discard <| emitOrVerify (keep := oldData) typedN s!"{typedN} (core_hierTyped₁ at {f}'s data)" fun id => do
    mkThm id fq data binders false
      (← `(Tools.ShippingHierTyped.hierTyped (Tools.ShippingMachineLinked.childMap D.modules) b =
        true))
      (← `(Tools.ShippingOneOutConns.core_hierTyped₁ (nDecl := $nDecl) $data $okI $bodyI
        $(dl "callsOk") $(dl "slotLen") $(dl "domB") $(dl "insts") $(dl "instFields")
        $outTyT $(dl "nomem")
        (by
          intro k hk y hy p hp
          $tacW:tactic)
        (by
          intro k hk y hy
          $tacTy:tactic)
        (kidIns := $kidInsI) $(dl "callArgs")
        (by
          intro k hk y hy j q hq
          $tacInD:tactic)
        hB hcore hpost entry closes $hon $outScalarT))
  discard <| emitOrVerify (keep := oldData) designN s!"{designN} (core_designCheckH at {f}'s data)" fun id => do
    mkThm id fq data binders false
      (← `(Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
        (Sparkle.IR.OptCheck.checkedOptimize b) = true))
      (← `(Tools.ShippingOneOutFacts.core_designCheckH (nDecl := $nDecl) $data $okI $bodyI
        $(dl "callsOk") $(dl "slotLen") $(dl "domB") $(dl "insts") $(dl "instFields")
        $outTyT $(dl "nomem") hB hcore hpost entry closes $(dl "slots")
        $hon $outScalarT
        (by
          intro k hk y hy
          $tacK:tactic)
        0 ($shippedI hcore hpost entry closes hB $hRs*)))
  -- ## the endpoint and its closed form
  let (name, fresh, note) ← liftTermElabM <|
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) do
        endpoint f factsN typedN designN outsN
  let cl := f ++ `machine_closes_at
  let mut made := [name]
  let mut closedNote := s!"no {cl}: no closed form"
  if (← getEnv).contains cl then
    let nn := Tools.ShippingMachineClosesGen.closedName name
    let ok ← liftTermElabM <|
      withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
        withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) do
          let ok ← Tools.ShippingMachineClosesAtGen.closeEndpointAt f cl name nn
          if ok then
            Tools.ShippingOneOutCommand.refuse nn (← getConstInfo nn).type (mkConst ``True)
          pure ok
    if ok then
      made := made ++ [nn]
      closedNote := s!"closed form {nn} (added or verified by closeEndpointAt)"
    else
      closedNote := s!"{name} has no MachineClosesAt premise: no closed form"
  let outNote : String := if oldData then "output width / name / scalar conditions"
    else "output name conditions (output width and scalar: outTy_of_core / outScalar_of_core, every reader result, not decided)"
  let dataNote := s!"data conditions decided by the kernel for {f}: callsOk {r.nDecl}, slot lengths, no late domain binder, insts ≠ [], instFields = [], slots ≠ [], {outNote}, no memory callee, callArgsOk with {f}.oneout_kidIns = {info.kidIns}, per entry the callee among {kids} with its argument widths and the result binder's width {info.resW}; for the callees: gateSort.width, what #gate_child left. These are conditions, not reductions; the run, MachineDefines, EntryDefines and ChildBnd remain premises"
  return (made, fresh, s!"{note}; {closedNote}; {dataNote}")

/-- The generator on `f`: never throws; on REFUSED / FAILED the environment
and the message log are put back. -/
def oneOut (f : Name) (oldData : Bool := false) : CommandElabM Outcome := do
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  let restore : CommandElabM Unit := do
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
  let info? : Except String Info ← try
      pure (Except.ok (← scope f))
    catch ex =>
      let msg ← ex.toMessageData.toString
      restore
      pure (Except.error msg)
  match info? with
  | .error reason => return .refused reason
  | .ok info =>
    try
      let (made, fresh, note) ← oneOutCore f info oldData
      if fresh then return .generated made note else return .present made note
    catch ex =>
      let msg ← ex.toMessageData.toString
      restore
      return .failed msg

/-- `#machine_oneout f`: an error where it is refused or fails. -/
elab "#machine_oneout " d:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← oneOut f
  match o with
  | .refused _ | .failed _ => throwError "{o.line f}"
  | _ => logInfo m!"{o.line f}"

/-- `#machine_oneout_try f "EXPECTED"`: the outcome is LOGGED (`ONEOUT GEN
f: GENERATED | PRESENT | REFUSED (reason) | FAILED (condition)`), and it is
an error when its class is not the expected one (`GENERATED`, `PRESENT`,
`REFUSED` or `FAILED`). -/
elab "#machine_oneout_try " d:ident ppSpace e:str : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← oneOut f
  logInfo m!"{o.line f}"
  unless o.tag == e.getString do
    throwError "ONEOUT GEN {f}: expected {e.getString}, found {o.tag}"

/-- `#machine_oneout_olddata f`: the generator with the PREVIOUS data path
(`f.oneout_outTy` / `_outScalar` decided and passed to the six lemmas;
the scratch of every re-derived parent name kept as `n.oneout_expected`).
Kept to compare the two paths on one tree (par/r-5). -/
elab "#machine_oneout_olddata " d:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← oneOut f (oldData := true)
  match o with
  | .refused _ | .failed _ => throwError "{o.line f}"
  | _ => logInfo m!"{o.line f}"

/-- `#machine_oneout_olddata_try f "EXPECTED"`: as `#machine_oneout_try`, on
the previous data path. -/
elab "#machine_oneout_olddata_try " d:ident ppSpace e:str : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← oneOut f (oldData := true)
  logInfo m!"{o.line f}"
  unless o.tag == e.getString do
    throwError "ONEOUT GEN {f}: expected {e.getString}, found {o.tag}"

end Tools.ShippingOneOutGenCommand
