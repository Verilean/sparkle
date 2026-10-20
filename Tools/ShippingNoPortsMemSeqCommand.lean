import Lean.Elab.Command
import Tools.ShippingNoPortsMemCommand
import Tools.ShippingNoPortsCommand
import Tools.ShippingNoPortsKidsCommand
import Tools.ShippingLeafKidFacts
import Tools.ShippingMemKidFacts
import Tools.ShippingMemClosesKids
import Tools.ShippingMemClosesKidsT
import Tools.ShippingSeqChildIface
import Tools.ShippingCallsKidsD
import Tools.ShippingCallsGate
import Tools.ShippingNameSep
import Tools.ShippingMemSeqNames
import Tools.ShippingNameMode
import Tools.ShippingMachineClosesGen
import Tools.ShippingReaderOutsInv
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md).

/-! # `#machine_no_ports_memseq f`: the check-free depth-0 endpoint of a parent whose call entries MIX leaf register machine children and memory placeholders, open and closed, GENERATED (round par/b-21)

`seqMem` (`Tests/Compiler/ShippingChildBoundaryTest.lean`) has its two
endpoints by hand: `Tests/Compiler/NoPortsMemSeqMemTest.lean` (open, 567
lines) and `Tests/Compiler/NoPortsMemSeqMemClosedTest.lean` (closed, 606
lines). This command produces the same two statements from the reader's
data, for any number of distinct leaf callees and of distinct placeholders.
NO general theorem is added: the proofs are those of the two hand files over
`Tools.ShippingMemKid` (`KidFactsM`, `kidFacts_toM`, `memKid_facts`,
`calleeAt`, `kidsM_*`), `Tools.ShippingLeafKidFacts.leafKid_facts`,
`Tools.ShippingMemCloses` (`ChildIfaceP`, `memKid_iface`,
`machineClosesAt_of_kidsDM`) and `Tools.ShippingNameSep`.

## Scope

A machine `f` with `f.machineData / machine_ok / machine_body`, the base
`f.machine_ships_hierR` and `f.machine_design_svR0` (`#machine_design_svR0`),
at least one register slot, the general closing (`instFields ≠ []`), whose
call entries are of

* **leaf register machines** (a machine with an endpoint, a register, no
  call, with `c.machine_closes`) — at least one, any number of different
  ones; and
* **memory placeholders** `SparkleMem.{combo|sync}.aw.dw` — at least one,
  either read kind, any number of different ones, EACH WITH ITS OWN
  `(aw, dw)`.

Depth 0 only; the at-form closing (`MachineClosesAt`) only.

PER-ENTRY WIDTHS. READ in the built statements: `KidFactsM mref cref c outs
ins n` is asked per entry with per-entry tables (`kidOuts k`, `kidIns k`),
and `memKid_facts (hc : memChild? c = some (memModule cb aw dw))` gives it
at `memOuts dw` / `memIns aw dw` for ITS `(cb, aw, dw)`
(`Tools/ShippingMemKidFacts.lean` 423–510, 564–739); the closing
`machineClosesAt_of_kidsDM` takes `nameK / nk / outsK / namesK` per entry and
`memKid_iface hc` gives `ChildIfaceP (memModule cb aw dw).1.name 4 ["out"]
[(memModule cb aw dw).1.name]` for its own `(cb, aw, dw)`
(`Tools/ShippingMemClosesKids.lean` 239–243, 419–452). Unlike `MemOnlyData d
nDecl aw dw` (ONE pair), nothing in this chain fixes one `(aw, dw)`: a width
difference is NOT refused here. No declaration of the repository exercised
it before this round.

## Refusals (`scope`; never a silent return), in the order tested

| condition | reason line (abridged) |
|---|---|
| no `f.machineData / machine_ok / machine_body` | not a machine with an endpoint |
| no call entry | no call |
| every entry a memory placeholder | memory-only: use `#machine_no_ports_mem` |
| a non-memory callee that is, or reaches, a machine with a memory child | memory at depth ≥ 1: not covered |
| no memory entry | no memory entry: use `#machine_no_ports` / `#machine_no_ports_kids` |
| a callee with `gate_peel`, or without a machine endpoint | a gate child / no machine endpoint: not covered |
| a machine callee with calls under the one-output closing | a one-output closing child: not covered |
| a machine callee with calls under the general closing | a child with calls of its own: not covered |
| a machine callee without a register | a slotless child: not covered |
| a leaf callee without `c.machine_closes` | its closing in every context is not derived |
| no register slot in `f` | parent without a register |
| `instFields = []` in `f` | not the general closing |
| `instFields` shorter than the entries | `hfieldOut` is false |
| an entry whose argument `let`s are not the callee's ports (leaf: its non-domain declared binders; memory: 4) | `hargsN` is false |
| an entry whose field is not an output of its callee (memory: `out`) | `hfieldOut` is false |
| two entries of one callee on one argument list reading one field | `hargsNd` is false |
| a leaf callee that IS the parent declaration (cannot occur: a leaf has no call, the parent has) | names not separated |
| ONLY under `shipping.nameCandidates` (the previous path): two module names not separated by the candidate renderings (leaf / leaf, leaf / memory module, leaf / parent, memory module / parent, memory module / memory module) | a shared descendant: names not separated |
| an output of `f` whose name starts with `i` | `hfresh` is not decided by the first character |
| no `f.machine_ships_hierR` / `f.machine_design_svR0` | run `#machine_design_svR0 f` first |

A shared descendant in the proper sense cannot occur in this scope (a leaf
child's design has no module, a memory module's design is the module
itself): what `hsep / hparent / hparentD / hdisjD` could fail on was a
coincidence of printed names.

ROUND par/b-30 (WRITTEN, NOT BUILT). Module names are `ofDecl` / `ofMem` of
the injective encoding, so in this scope NO coincidence is possible, and four
of the five generation-time name refusals are gone — each exactly where a
general lemma covers the whole case:

| refusal (previous path) | why it cannot fire | lemma |
|---|---|---|
| parent / memory module | no declaration has a memory module's name | `Tools.ShippingMemSeqNames.decl_not_mem_memName` |
| leaf / memory module | the same | the same |
| leaf / leaf (`sep`) | the leaves are DISTINCT declarations (`eraseDups`) | `Tools.ShippingModuleName.ofDecl_ne` |
| memory module / memory module | distinct placeholders have distinct `(combo, aw, dw)` | `Tools.ShippingMemSeqNames.memName_ne` |

The fifth (leaf / parent) is KEPT, on the names themselves (`c == f`): the
lemma `ofDecl_ne` needs `c ≠ f`. By reading it cannot fire (a leaf callee has
no call; `f` has), so nothing that was accepted is refused, and a
declaration that was refused only because the candidate renderings did not
separate two different names (`sep` false) is now accepted.

The name lemmas keep their NAMES and STATEMENTS; their proofs are the
general lemmas (no `name_not_mem`, no `Enc.sep_ne`, no string comparison).
`set_option shipping.nameCandidates true` gives the previous refusals and
proofs, for one round.

After the scope: a `machine_ships_hierR` that is not `machine_ships_hierC`
on 25 arguments with 11 binders, a decided data condition that is false, an
existing name with another statement — class `FAILED`, with its line.

## Generated, in this order (lemmas under `f.noPortsMemSeq_*`)

    [c.machine_leafKid                 per distinct leaf callee: USED if it exists (statement
                                       checked), else generated by the BUILT leafKidTheorem]
    f.noPortsMemSeq_{outsOf,insOf,nameOf,nkOf,outsNOf,namesOf}        the tables, keyed by the CALLEE
    f.noPortsMemSeq_{table}_at{i}      the table at key i (leaf callees first, then placeholders)
    f.noPortsMemSeq_entry              ONE decided ∀: every entry's callee is one of the keys
    f.noPortsMemSeq_calls / _slots / _domB / _callWidths / _callArgs / _outChars
                                       (`_outTy` / `_outScalar`: the previous data path only, see below)
    f.noPortsMemSeq_kids               KidFactsM of every entry's callee, depth 0
    f.noPortsMemSeq_runFacts / _outsG0 / _mixedG / _designP0          kidsM_* at f's data
    f.machine_design_noPortsR0         the head machine_design_noPorts at n = 0
    f.noPortsMemSeq_alias / _argsN / _fieldOut / _fieldsNd / _outHead (decided)
    f.noPortsMemSeq_notinP{j}          f does not print as placeholder j's module name
    f.noPortsMemSeq_leafNotin{i}_{j}   leaf i does not print as placeholder j's module name
    f.noPortsMemSeq_leafNeParent{i}    leaf i and f print differently
    f.noPortsMemSeq_leafNe{i}_{j}      (i < j) two leaf callees print differently
    f.noPortsMemSeq_memNe{i}_{j}       (i < j) two memory modules have different names
    f.noPortsMemSeq_iface{i}           ChildIfaceP of leaf i's real child
    f.noPortsMemSeq_kidsP / _sep / _parent / _parentD / _disj
    f.noPortsMemSeq_closes             MachineClosesAt f — premises: MachineDefines of each DISTINCT leaf callee, nothing else
    f.machine_design_noPortsR0_closed

The two endpoints carry the hand tests' names. The lemmas do not (the hand
ones are `Tests.Compiler.NoPortsMemSeqMemTest.seqMem_*`).

## The compare path (never a silent return)

For EVERY name of `f.*` above: if it EXISTS, it is rebuilt all the same,
added under `…_regen` (kernel-checked) and compared — a theorem's statement,
a table's value — by `isDefEq`; an ERROR otherwise. `c.machine_leafKid` is a
prerequisite of the CALLEE, not a name of `f`: when it exists its statement
is checked against the expected one (`isDefEq`) and it is USED (logged); it
is never re-added (two parents of one callee in one import closure would
clash on a `_regen` name).

## What is restated here, and what is imported

IMPORTED (BUILT): `Tools.ShippingNoPortsMemCommand.{memParamsOf, memBelow,
emit, orElim, forbiddenMem, premiseLines (and through it innerAntecedents),
Ctx.boolT}`; `Tools.ShippingNoPortsKidsCommand.{dischargeWith, closedTerm,
addOrCompare, regenName}`; `Tools.ShippingNoPortsCommand.leafKidTheorem`;
`Tools.ShippingShipsFreeCommand.checkMade`. The premise lines keep the
imported prefix `NOPORTS MEM PREMISE`.

RESTATED from `Tests/` (a `Tools/` file cannot import them):

* `endpointTerm` — `generateR0`, `Tests/Compiler/NoPortsMemSeqMemTest.lean`
  406–466 (61 lines): it returns the statement and the proof instead of
  adding them (the compare path adds them); `dischargeWith` is the built
  `Tools` one;
* the theorem texts: the hand files' theorems as syntax —
  `NoPortsMemSeqMemTest` 127–388 and `NoPortsMemSeqMemClosedTest` 104–412.

DIFFERENCES from the hand texts (each a place where the build may disagree):
the two-way `rcases` are nested `Or.elim` terms with `by` blocks in their
branches, over any number of keys; the tables are nested `if`s over ALL the
keys (the last key is the `else`), their lemmas proved by a chain of
`if_neg` / `if_pos` with the (in)equalities stated; `cnt_ne_mem` /
`mem_ne_seqMem` are inline (`List.mem_singleton`); `seqMem_fresh` is inline
(its statement has an interpolated string); the side conditions of `kidsM_*`
are named decided lemmas; every decided lemma is under `maxHeartbeats
4000000`.

## The output facts from the reader (round par/r-5; WRITTEN, NOT BUILT)

`#machine_no_ports_memseq f` no longer decides `f.noPortsMemSeq_outTy`
(`∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width`) and
`f.noPortsMemSeq_outScalar` (`∀ o ∈ …, scalarTy o.ty = true`). The four run
theorems pass, in their place,

    Tools.ShippingReaderOutsInv.outTy_of_core hcore entry
    Tools.ShippingReaderOutsInv.outScalar_of_core hcore entry     (designP0 only)

— the general theorems over EVERY reader result (BUILT), at the run
hypotheses `hcore`, `entry` each run theorem already binds. No other
generated name read the two lemmas (READ: `closingTheorems`, `leafKid`,
`endpointTerm`). EVERY generated STATEMENT is unchanged (the four run
theorems' included); only their proofs differ, and the two decided lemmas
are not generated.

The PREVIOUS path stays reachable as `#machine_no_ports_memseq_olddata f` /
`#machine_no_ports_memseq_olddata_try f "…"` (`Ctx.oldData`): it decides the
two lemmas and passes them. Run after the default path on one declaration,
it takes the compare path on every shared name
(`Tests/Compiler/NoPortsMemSeqGenOldDataTest.lean`, target-only).

WRITTEN, NOT BUILT (par/b-21; par/r-5).

## TAG MODE (round par/o-kidt2; BUILT: gt5, regression rg1 exit 0)

A shape some of whose entries' NAMES do not say what their ORIGINS build (a declaration declared under a
memory placeholder name next to the memory: a collision) was REFUSED ("TagsAgree is false"). It is now
generated in tag mode (`Scope.tagMode`): placeholders read off the origins; the tables keyed by
`Tools.ShippingMemCloses.keyAt` (callee × memory key of the origin) instead of `calleeAt`; `…_entry` states
name AND memory key; `…_kids` is `KidFactsT` by origin (`kidFactsT_of`, `memKidT_facts`); the four run
theorems use `kidsM_*T`; the closing `machineClosesAt_of_kidsDMT` (kids `KidT`, `sep` / `disj` / `fieldsNd`
over name AND memory key). No `TagsAgree` anywhere in tag mode. Every other shape takes the previous
name-keyed path, statements unchanged (`Tests/Compiler/NoPortsMemSeqGen*Test.lean` rebuilt in rg1).
Generated on `collSameR` / `collArgsR` (`Tests/Compiler/MemNameCollisionGenTest.lean`). -/
namespace Tools.ShippingNoPortsMemSeqCommand
open Lean Meta Elab Command
open Tools.ShippingShipsFreeCommand (checkMade)
open Tools.ShippingNoPortsKidsCommand (dischargeWith closedTerm addOrCompare regenName)
open Tools.ShippingNoPortsMemCommand (memParamsOf memBelow orElim forbiddenMem premiseLines)

/-- What the scope scan read. -/
structure Scope where
  nDecl : Nat
  /-- the call entries' callees, in the reader's order -/
  calls : List Name
  /-- the distinct leaf register machine callees, in the order of their first entry -/
  leaves : List Name
  /-- the distinct placeholders, in the order of their first entry: the
  name, the read kind (`true`: combinational), `aw`, `dw` -/
  mems : List (Name × Bool × Nat × Nat)
  slots : Nat
  /-- two placeholders with different `(aw, dw)` -/
  widthsDiffer : Bool
  /-- TAG MODE (round par/o-kidt2): some entry's NAME does not say what its
  ORIGIN builds (a declaration carrying a memory placeholder name: a
  collision). The tables are then keyed by (callee, memory key of the origin)
  and the chain is the origin-based one (`KidFactsT`, `kidsM_*T`,
  `machineClosesAt_of_kidsDMT`): no `TagsAgree`. Otherwise the previous
  (name-keyed) path, unchanged. -/
  tagMode : Bool := false
  deriving Inhabited

/-- The scope, with its reasons. -/
def scope (f : Name) : CommandElabM Scope := do
  let env ← getEnv
  unless env.contains (f ++ `machineData) && env.contains (f ++ `machine_ok) &&
      env.contains (f ++ `machine_body) do
    throwError "{f}: not a machine with an endpoint (no {f}.machineData / machine_ok / machine_body: #machine_endpoint was not run on it)"
  let r ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine f
  let calls := r.shape.insts.map (·.1)
  if calls.isEmpty then
    throwError "{f}: no call (no instance statement: there is no child to derive facts about)"
  -- origin dispatch (patched compiler): an entry is a memory by its ORIGIN;
  -- a shape whose names do not say what their origins build (a declaration
  -- carrying a memory placeholder name) is not generated (`TagsAgree` false)
  let tagged := r.shape.instTagged
  unless tagged.length == calls.length do
    throwError "{f}: {tagged.length} tagged entries for {calls.length} call entries (an origin tag is missing)"
  -- a collision (a declaration carrying a memory placeholder name): TAG MODE
  let tagMode := tagged.any (fun x => !Tools.ShippingInstTagged.tagAgrees x.1 x.2)
  let memCalls := ((tagged.filter fun x => x.2.child?.isSome).map (·.1)).eraseDups
  let others := ((tagged.filter fun x => x.2.child?.isNone).map (·.1)).eraseDups
  if others.isEmpty then
    throwError "{f}: memory-only (every call entry is a memory placeholder {memCalls}): use #machine_no_ports_mem"
  for c in others do
    let below ← liftTermElabM (memBelow c 8)
    match below with
    | Option.some h =>
      throwError "{f}: memory at depth ≥ 1 (its callee {c} reaches the machine {h}, which has a memory child): not covered — the depth chain's kidCheck rejects a memory statement at depth ≥ 1 (seqStmtOkI), and memKid_facts is at depth 0"
    | Option.none => pure ()
  if memCalls.isEmpty then
    throwError "{f}: no memory entry (its callees {others} are machine / gate children): use #machine_no_ports / #machine_no_ports_kids"
  -- the leaf callees: (name, number of argument ports, output names)
  let mut leafData : List (Name × Nat × List String) := []
  for k in others do
    if env.contains (k ++ `gate_peel) then
      throwError "{f}: the callee {k} is a gate child ({k}.gate_peel exists): not covered (the leaf side is leafKid_facts, about a register machine's data)"
    unless env.contains (k ++ `machineData) && env.contains (k ++ `machine_ok) &&
        env.contains (k ++ `machine_body) do
      throwError "{f}: the callee {k} has no machine endpoint (a gate child, or #machine_endpoint was not run on it): not covered"
    let cr ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine k
    unless cr.shape.insts.isEmpty do
      if cr.shape.instFields.isEmpty then
        throwError "{f}: the callee {k} is a one-output closing child (calls {(cr.shape.insts.map (·.1)).eraseDups} under instFields = []): not covered (KidFactsM of it would come from OneOutKid at depth 1; this command is at depth 0)"
      else
        throwError "{f}: the callee {k} has calls of its own ({(cr.shape.insts.map (·.1)).eraseDups}, general closing): not covered (LeafKid.leaf asks shape.insts = [])"
    if cr.shape.layout.slots.isEmpty then
      throwError "{f}: the callee {k} is slotless (no register): not covered (LeafKid.slots asks shape.layout.slots ≠ [])"
    unless env.contains (k ++ `machine_closes) do
      throwError "{f}: the leaf callee {k} has no {k}.machine_closes (its closing in every context is not derived): not covered"
    let nkC : Nat := ((cr.shape.binders.take (cr.shape.binders.length -
      cr.shape.layout.slots.length - cr.shape.layout.lets)).filter fun x => x.2 != .domain).length
    leafData := leafData ++ [(k, nkC, cr.shape.layout.outs.map (·.name))]
  if r.shape.layout.slots.isEmpty then
    throwError "{f}: parent without a register (kidsM_runFacts / kidsM_designCheck ask d.shape.layout.slots ≠ [])"
  if r.shape.instFields.isEmpty then
    throwError "{f}: instFields = [] — not the general closing (machineClosesAt_of_kidsDM asks d.shape.instFields ≠ [])"
  let mut mems : List (Name × Bool × Nat × Nat) := []
  if tagMode then
    -- the placeholders by their ORIGINS (a name alone does not say it)
    for x in tagged do
      if let .mem cb aw dw := x.2 then
        unless mems.contains (x.1, cb, aw, dw) do mems := mems ++ [(x.1, cb, aw, dw)]
  else
    for c in memCalls do
      match memParamsOf c with
      | Option.some (cb, aw, dw) => mems := mems ++ [(c, cb, aw, dw)]
      | Option.none => pure ()
  let widthsDiffer : Bool := match mems with
    | (_, _, aw, dw) :: rest => rest.any fun (_, _, aw', dw') => !(aw' == aw && dw' == dw)
    | [] => false
  -- the entries: argument counts, fields, repetitions
  let args := r.shape.insts.map (·.2.1)
  let fields := r.shape.instFields
  unless fields.length == calls.length do
    throwError "{f}: instFields = {fields} against {calls.length} entries (hfieldOut is false: getD reads \"\")"
  let mut seen : List (Name × Option (Bool × Nat × Nat) × List Nat × String) := []
  for (((c, a), fld), o) in ((calls.zip args).zip fields).zip (tagged.map (·.2)) do
    -- by the ORIGIN in tag mode, by the name otherwise (they agree there)
    let mp : Option (Bool × Nat × Nat) := if tagMode then
        (match o with | .mem cb aw dw => Option.some (cb, aw, dw) | _ => Option.none)
      else memParamsOf c
    match mp with
    | Option.some _ =>
      unless a.length == 4 do
        throwError "{f}: the memory entry {c} has the argument lets {a}, not 4 (hargsN is false)"
      unless fld == "out" do
        throwError "{f}: the memory entry {c} reads the field {fld}, not out (hfieldOut is false)"
    | Option.none =>
      match leafData.find? (fun x => x.1 == c) with
      | Option.some (_, nkC, outsC) =>
        unless a.length == nkC do
          throwError "{f}: the entry of {c} has the argument lets {a} against {nkC} non-domain declared binders of {c} (hargsN is false)"
        unless outsC.contains fld do
          throwError "{f}: the entry of {c} reads the field {fld}, not one of its outputs {outsC} (hfieldOut is false)"
      | Option.none => pure ()
    let mk : Option (Bool × Nat × Nat) := if tagMode then mp else Option.none
    if seen.contains (c, mk, a, fld) then
      throwError "{f}: hargsNd is false — two entries of {c} on the same argument lets {a} read the same field {fld} (hfieldsNd of machineClosesAt_of_kidsDM: entries of one callee on one argument list are one instance, told apart by their fields only)"
    seen := seen ++ [(c, mk, a, fld)]
  -- the module names
  let leaves := leafData.map (·.1)
  if shipping.nameCandidates.get (← getOptions) then
    -- THE PREVIOUS PATH: separated by the candidate renderings (decided the
    -- same way by the generated lemmas)
    let memNames := mems.map fun (p, cb, aw, dw) =>
      (p, (Sparkle.Compiler.MachMemory.memModule cb aw dw).1.name)
    for (p, mn) in memNames do
      unless Sparkle.IR.ModuleName.ofDecl f != mn do
        throwError "{f}: a shared descendant: names not separated — {f} may print as {mn}, the module of {p} (hparent / hparentD are not decided)"
      for c in leaves do
        unless Sparkle.IR.ModuleName.ofDecl c != mn do
          throwError "{f}: a shared descendant: names not separated — the callee {c} may print as {mn}, the module of {p} (hsep / hdisjD are not decided)"
    for c in leaves do
      unless Tools.ShippingNameSep.sep c f do
        throwError "{f}: a shared descendant: names not separated — the callee {c} and {f} are not told apart by their printed names (hparent is not decided)"
    for (c, i) in leaves.zipIdx do
      for (c', j) in leaves.zipIdx do
        if i < j then
          unless Tools.ShippingNameSep.sep c c' do
            throwError "{f}: a shared descendant: names not separated — the callees {c} and {c'} are not told apart by their printed names (hsep is not decided)"
    for ((p, mn), i) in memNames.zipIdx do
      for ((p', mn'), j) in memNames.zipIdx do
        if i < j && mn == mn' then
          throwError "{f}: a shared descendant: names not separated — the placeholders {p} and {p'} have one module name {mn} (hsep is not decided)"
  else
    -- the names are `ofDecl` / `ofMem` of the injective encoding: a
    -- declaration against a memory module, two distinct leaves, two distinct
    -- placeholders are separated by general lemmas (nothing to test). Leaf
    -- against parent needs `c ≠ f` (true by reading: a leaf has no call)
    for c in leaves do
      if c == f then
        throwError "{f}: names not separated — the callee {c} is the parent declaration itself (hparent is false)"
  for o in r.shape.layout.outs do
    if o.name.toList.head? == Option.some 'i' then
      throwError "{f}: the output {o.name} starts with 'i' (hfresh is false as tested: the freshness of the instance names is decided by the first character)"
  for s in [`machine_ships_hierR, `machine_design_svR0] do
    unless env.contains (f ++ s) do
      throwError "{f}: no {f ++ s} (run #machine_design_svR0 {f} first)"
  return { nDecl := r.nDecl, calls, leaves, mems, slots := r.shape.layout.slots.length,
           widthsDiffer, tagMode }

/-! ## The generated theorems (the hand files' texts) -/

private def nm (d : Name) (s : String) : Ident := mkIdent (`_root_ ++ d ++ Name.mkSimple s)

private def noAsync {α : Type} (x : CommandElabM α) : CommandElabM α :=
  withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false }) x

/-- One key of the tables: a distinct callee, with its data as terms. -/
structure Key where
  /-- a leaf register machine (else: a memory placeholder) -/
  leaf : Bool
  /-- its index among the leaves, resp. among the placeholders -/
  idx : Nat
  decl : Name
  /-- the callee, as a term of type `Lean.Name` -/
  key : Term
  /-- the memory key of its origin (`Option (Bool × Nat × Nat)`; tag mode) -/
  mkey : Term
  /-- its output fields (`List OutField`) -/
  outs : Term
  /-- the widths of its argument ports (`List Nat`) -/
  ins : Term
  /-- its module's name (`String`) -/
  name : Term
  /-- the number of its argument ports (`Nat`) -/
  nk : Term
  /-- its output names (`List String`) -/
  outsN : Term
  /-- the module names of its design (`List String`) -/
  names : Term
  /-- the placeholder test: a leaf — `memChild? key = none`; a placeholder —
  `memChild? key = some (memModule …)` -/
  isMem : Term
  deriving Inhabited

/-- The names and the log shared by the generated theorems of `f`. -/
structure Ctx where
  f : Name
  s : Scope
  log : IO.Ref (Array String)
  keys : Array Key
  /-- the built `emit`'s context (it reads the log only) -/
  m : Tools.ShippingNoPortsMemCommand.Ctx
  /-- the previous data path (`outTy` / `outScalar` decided per declaration,
  `…_olddata`; par/r-5) -/
  oldData : Bool := false

namespace Ctx

def data (c : Ctx) : Ident := nm c.f "machineData"

def lem (c : Ctx) (s : String) : Ident := nm c.f s!"noPortsMemSeq_{s}"

def lemName (c : Ctx) (s : String) : Name := c.f ++ Name.mkSimple s!"noPortsMemSeq_{s}"

def hR (j : Nat) : Ident := mkIdent (Name.mkSimple s!"hR{j}")

/-- The reflection binders: `MachineDefines` of every distinct LEAF callee. -/
def binders (c : Ctx) : CommandElabM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
  let mut bs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for (k, j) in c.s.leaves.zipIdx do
    let kq : Term := quote k
    bs := bs.push (← `(bracketedBinder|
      ($(hR j) : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $kq
        ($(nm k "machineData")).shape)))
  return bs

/-- The binders' names, in the binders' order. -/
def hyps (c : Ctx) : Array Term :=
  ((List.range c.s.leaves.length).map fun j => (⟨(hR j).raw⟩ : Term)).toArray

/-- The table key of entry `k`: `calleeAt`, in tag mode `keyAt` (the callee
and the memory key of its origin). -/
def keyFn (c : Ctx) : Ident :=
  if c.s.tagMode then mkIdent ``Tools.ShippingMemCloses.keyAt
  else mkIdent ``Tools.ShippingMemKid.calleeAt

/-- `keyFn d k = …` at an entry. -/
def keyEq (c : Ctx) : Ident :=
  if c.s.tagMode then mkIdent ``Tools.ShippingMemCloses.keyAt_eq
  else mkIdent ``Tools.ShippingMemKid.calleeAt_eq

/-- The table `tbl` at the callee of entry `k`, as a function of `k`. -/
def tblFn (c : Ctx) (tbl : String) : CommandElabM Term :=
  `((fun k => $(c.lem tbl) ($(c.keyFn) $(c.data) k)))

/-- A key as the tables take it. -/
def keyT (c : Ctx) (k : Key) : CommandElabM Term :=
  if c.s.tagMode then `(((($(k.key) : Lean.Name), $(k.mkey)) : Lean.Name × Option (Bool × Nat × Nat)))
  else pure k.key

/-- The type of the tables' keys. -/
def keyTy (c : Ctx) : CommandElabM Term :=
  if c.s.tagMode then `(Lean.Name × Option (Bool × Nat × Nat)) else `(Lean.Name)

/-- The rewriting rules of an entry hypothesis `h` (tag mode: a conjunction). -/
def hRules (c : Ctx) (h : Term) : CommandElabM (Array Term) := do
  if c.s.tagMode then pure #[← `(($h).1), ← `(($h).2)] else pure #[h]

end Ctx

/-- The keys: the leaf callees, then the placeholders. -/
def mkKeys (s : Scope) : CommandElabM (Array Key) := do
  let mut keys : Array Key := #[]
  for (k, i) in s.leaves.zipIdx do
    let kq : Term := quote k
    let D := nm k "machineData"
    keys := keys.push
      { leaf := true, idx := i, decl := k, key := kq
        mkey := ← `((Option.none : Option (Bool × Nat × Nat)))
        outs := ← `((($D).shape.layout.outs))
        ins := ← `((Tools.ShippingPortWidthsPure.declWidths $D))
        name := ← `(((Sparkle.IR.ModuleName.ofDecl ($kq : Lean.Name))))
        nk := ← `((((($D).shape.binders.take
          (($D).shape.binders.length - ($D).shape.layout.slots.length -
            ($D).shape.layout.lets)).filter (fun x => x.2 != .domain)).length))
        outsN := ← `((($D).shape.layout.outs.map (·.name)))
        names := ← `((([] : List String)))
        isMem := ← `((show Sparkle.Compiler.MachMemory.memChild? $kq = none from by
          first | rfl | decide)) }
  for ((p, cb, aw, dw), j) in s.mems.zipIdx do
    let cbT ← Tools.ShippingNoPortsMemCommand.Ctx.boolT cb
    let awL := Syntax.mkNumLit (toString aw)
    let dwL := Syntax.mkNumLit (toString dw)
    let pT ← `((Sparkle.Compiler.MachMemory.memChildName $cbT $awL $dwL))
    let M ← `((Sparkle.Compiler.MachMemory.memModule $cbT $awL $dwL))
    keys := keys.push
      { leaf := false, idx := j, decl := p, key := pT
        mkey := ← `((Option.some ($cbT, $awL, $dwL) : Option (Bool × Nat × Nat)))
        outs := ← `((Tools.ShippingMemKid.memOuts $dwL))
        ins := ← `((Tools.ShippingMemKid.memIns $awL $dwL))
        name := ← `((($M).1.name))
        nk := ← `(((4 : Nat)))
        outsN := ← `(((["out"] : List String)))
        names := ← `((([($M).1.name] : List String)))
        isMem := ← `((show Sparkle.Compiler.MachMemory.memChild? $pT = some $M from by
          first | rfl | decide)) }
  return keys

/-- The tables: the name, the value type, whether it is `noncomputable` (it
reads a callee's reflected data), the value at a key. -/
def tables : CommandElabM (Array (String × Term × Bool × (Key → Term))) := do
  return #[
    ("outsOf", ← `(List Sparkle.IR.Machine.OutField), true, fun k => k.outs),
    ("insOf", ← `(List Nat), true, fun k => k.ins),
    ("nameOf", ← `(String), false, fun k => k.name),
    ("nkOf", ← `(Nat), true, fun k => k.nk),
    ("outsNOf", ← `(List String), true, fun k => k.outsN),
    ("namesOf", ← `(List String), false, fun k => k.names)]

/-- A definition: added; if `name` EXISTS, added under `name_regen` and its
value must be `isDefEq` the existing one (an error otherwise). -/
def emitDef (c : Ctx) (name : Name) (mk : Ident → CommandElabM (TSyntax `command)) :
    CommandElabM Unit := do
  let env ← getEnv
  if env.contains name then
    let rn := regenName name
    if env.contains rn then
      throwError "{rn}: exists already (the compare path was run twice)"
    let before := (← get).messages.toList.length
    let cmd ← mk (mkIdent (`_root_ ++ rn))
    noAsync (elabCommand cmd)
    checkMade rn before
    let same ← liftTermElabM do
      let tyOk ← isDefEq (← getConstInfo name).type (← getConstInfo rn).type
      if tyOk then isDefEq (mkConst name) (mkConst rn) else pure false
    unless same do
      throwError "{name}: EXISTS with a different value than the rebuilt {rn}"
    c.log.modify fun a => a.push s!"REBUILT {name}: value isDefEq the existing one (kept as {rn})"
  else
    let before := (← get).messages.toList.length
    let cmd ← mk (mkIdent (`_root_ ++ name))
    noAsync (elabCommand cmd)
    checkMade name before
    c.log.modify fun a => a.push s!"GENERATED {name}"

/-- A theorem (the built `emit`: the compare path on its statement). -/
def emitThm (c : Ctx) (name : Name) (mk : Ident → CommandElabM (TSyntax `command)) :
    CommandElabM Unit :=
  Tools.ShippingNoPortsMemCommand.emit c.m name mk

/-- A theorem decided on the reflected data. -/
def decided (c : Ctx) (s : String) (stmt : Term) : CommandElabM Unit :=
  emitThm c (c.lemName s) fun tn => `(command|
    set_option maxHeartbeats 4000000 in
    theorem $tn : $stmt := by
      first | decide | decide +kernel)

/-- The proof of `(if kᵢ = k₀ then v₀ else if kᵢ = k₁ then v₁ else … else vₙ₋₁) = vᵢ`:
`i` steps `if_neg`, then `if_pos` (none for the last key: it is the `else`). -/
def atProof (keys : Array Term) (ty : Term) (i : Nat) : CommandElabM Term := do
  let n := keys.size
  let ki := keys[i]!
  let mut acc? : Option Term := Option.none
  if i + 1 < n then
    acc? := Option.some (← `(if_pos (show (($ki : $ty)) = ($ki) from rfl)))
  for j' in [0:i] do
    let j := i - 1 - j'
    let kj := keys[j]!
    let neg ← `(if_neg (show ¬ ((($ki : $ty)) = ($kj)) from by
      first | decide | decide +kernel))
    match acc? with
    | Option.some r => acc? := Option.some (← `(Eq.trans ($neg) ($r)))
    | Option.none => acc? := Option.some neg
  match acc? with
  | Option.some t => pure t
  | Option.none => throwError "atProof: one key only"

/-- The tables and their values at the keys. -/
def tableTheorems (c : Ctx) : CommandElabM Unit := do
  let n := c.keys.size
  unless n ≥ 2 do throwError "{c.f}: {n} distinct callee(s), expected a leaf callee and a placeholder"
  let cv := mkIdent `cv
  let keysT ← c.keys.mapM c.keyT
  let kTy ← c.keyTy
  for (tbl, ty, nc, sel) in ← tables do
    let mut body : Term := sel c.keys[n - 1]!
    for j' in [0:n - 1] do
      let j := n - 2 - j'
      let kj := c.keys[j]!
      body ← `(if $cv = ($(keysT[j]!)) then $(sel kj) else $body)
    let bodyF : Term := body
    emitDef c (c.lemName tbl) fun tn =>
      if nc then `(command| noncomputable def $tn ($cv : $kTy) : $ty := $bodyF)
      else `(command| def $tn ($cv : $kTy) : $ty := $bodyF)
    for i in [0:n] do
      let ki := c.keys[i]!
      let kiT := keysT[i]!
      let pf ← atProof keysT kTy i
      let plain := mkIdent (c.lemName tbl)
      emitThm c (c.lemName s!"{tbl}_at{i}") fun tn => `(command|
        set_option maxHeartbeats 4000000 in
        theorem $tn : $(c.lem tbl) ($kiT) = $(sel ki) := by
          first
            | unfold $(c.lem tbl)
            | unfold $plain
          exact $pf)

/-- `rw […]` with the hypothesis `h` and lemmas, then `exact t`, as a term. -/
def rwExact (rules : Array Term) (t : Term) : CommandElabM Term :=
  `((by
    rw [$[$rules:term],*]
    exact $t))

/-- `f.noPortsMemSeq_entry`, the data conditions, `f.noPortsMemSeq_kids`. -/
def dataTheorems (c : Ctx) : CommandElabM Unit := do
  let d := c.data
  let nD := Syntax.mkNumLit (toString c.s.nDecl)
  -- every call entry's callee is one of the keys
  let mut disj? : Option Term := Option.none
  for key in c.keys.toList.reverse do
    let a ← if c.s.tagMode then
        `(((($d).shape.insts[k]).1 = $(key.key) ∧
          Tools.ShippingMemCloses.memKey (Tools.ShippingInstTagged.originAt ($d).shape k) = $(key.mkey)))
      else `((($d).shape.insts[k]).1 = $(key.key))
    match disj? with
    | Option.none => disj? := Option.some a
    | Option.some r => disj? := Option.some (← `($a ∨ $r))
  let disj ← match disj? with
    | Option.some t => pure t
    | Option.none => throwError "{c.f}: no callee"
  decided c "entry" (← `(∀ (k : Nat) (hk : k < ($d).shape.insts.length), $disj))
  decided c "calls" (← `(($d).callsOk $nD = true))
  decided c "slots" (← `(($d).ss.length = ($d).shape.layout.slots.length))
  decided c "domB" (← `(∀ b ∈ ($d).shape.binders.drop $nD, b.2 ≠ .domain))
  -- par/r-5: `outTy` / `outScalar` only on the previous data path
  if c.oldData then
    decided c "outTy" (← `(∀ o ∈ ($d).shape.layout.outs, o.ty.bitWidth = o.width))
  let outsF ← c.tblFn "outsOf"
  let insF ← c.tblFn "insOf"
  decided c "callWidths" (← `(Tools.ShippingCallWidths.callWidthsOk $d $nD $outsF = true))
  decided c "callArgs" (← `(Tools.ShippingPortsMatchRaw.callArgsOk $d $nD $insF = true))
  decided c "outChars" (← `(∀ o ∈ ($d).shape.layout.outs, ∀ c ∈ o.name.toList,
    Sparkle.IR.NameHints.charOk c = true))
  if c.oldData then
    decided c "outScalar" (← `(∀ o ∈ ($d).shape.layout.outs,
      Tools.ShippingTextTyped.scalarTy o.ty = true))
  -- `KidFactsM` of every entry's callee, depth 0
  let h := mkIdent `h
  let hT : Term := ⟨h.raw⟩
  let mut branches : List Term := []
  for (key, i) in c.keys.toList.zipIdx do
    let atO : Term := ⟨(c.lem s!"outsOf_at{i}").raw⟩
    let atI : Term := ⟨(c.lem s!"insOf_at{i}").raw⟩
    let fact ← if c.s.tagMode then
        (if key.leaf then
          `(Tools.ShippingMemKid.kidFactsT_of
            (Tools.ShippingLeafKidFacts.leafKid_facts
              ($(nm key.decl "machine_leafKid") $(Ctx.hR key.idx)) 0)
            (Tools.ShippingMemCloses.child?_none_of_memKey ($hT).2))
        else
          `(Tools.ShippingMemKid.memKidT_facts (Tools.ShippingMemCloses.child?_of_memKey ($hT).2)))
      else if key.leaf then
        `(Tools.ShippingMemKid.kidFacts_toM
          (Tools.ShippingLeafKidFacts.leafKid_facts
            ($(nm key.decl "machine_leafKid") $(Ctx.hR key.idx)) 0)
          $(key.isMem))
      else
        `(Tools.ShippingMemKid.memKid_facts $(key.isMem))
    branches := branches ++ [← rwExact ((← c.hRules hT) ++ #[atO, atI]) fact]
  let kidsPf ← orElim h (← `($(c.lem "entry") k hk)) branches
  let bs ← c.binders
  if c.s.tagMode then
    emitThm c (c.lemName "kids") fun tn => `(command|
      set_option maxHeartbeats 4000000 in
      theorem $tn {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
          {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} $bs* :
          ∀ (k : Nat) (hk : k < ($d).shape.insts.length),
            Tools.ShippingMemKid.KidFactsT mref cref
              (Tools.ShippingInstTagged.originAt ($d).shape k) (($d).shape.insts[k]).1
              ($(c.lem "outsOf") ($(c.keyFn) $d k))
              ($(c.lem "insOf") ($(c.keyFn) $d k)) 0 := by
        intro k hk
        rw [$(c.keyEq) $d hk]
        exact $kidsPf)
  else
    emitThm c (c.lemName "kids") fun tn => `(command|
      set_option maxHeartbeats 4000000 in
      theorem $tn {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
          {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} $bs* :
          ∀ (k : Nat) (hk : k < ($d).shape.insts.length),
            Tools.ShippingMemKid.KidFactsM mref cref (($d).shape.insts[k]).1
              ($(c.lem "outsOf") ($(c.keyFn) $d k))
              ($(c.lem "insOf") ($(c.keyFn) $d k)) 0 := by
        intro k hk
        rw [$(c.keyEq) $d hk]
        exact $kidsPf)

/-- One of the four run theorems of `f`: binders `hcore hpost entry closes`,
then `hg` (if `gate`), then `hB`, then the leaf callees' reflections. -/
def runTheorem (c : Ctx) (s : String) (gate : Bool) (concl proof : Term) : CommandElabM Unit := do
  let d := c.data
  let fq : Term := quote c.f
  let mut tail : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  if gate then
    tail := tail.push (← `(bracketedBinder| (hg : Sparkle.IR.RefineCheck.hierGate b = true)))
  tail := tail.push (← `(bracketedBinder| (hB : Tools.ShippingChildInv.ChildBnd mref cref w)))
  tail := tail ++ (← c.binders)
  emitThm c (c.lemName s) fun tn => `(command|
    set_option maxHeartbeats 4000000 in
    theorem $tn {mctx : Lean.Meta.Context}
        {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
        {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
        {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
        (hcore : Tools.ShippingEntrySoundness.RunsTo
          (Sparkle.Compiler.Elab.synthesizeCombinationalCore $fq [] false)
          mctx mref cctx cref w (raw, D) w1)
        (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
          b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
        (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $fq ($d).shape)
        (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref $fq ($d).shape)
        $tail* : $concl :=
      $proof)

/-- `f.noPortsMemSeq_runFacts / _outsG0 / _mixedG / _designP0`. -/
def runTheorems (c : Ctx) : CommandElabM Unit := do
  let d := c.data
  let nD := Syntax.mkNumLit (toString c.s.nDecl)
  let ok := nm c.f "machine_ok"
  let body := nm c.f "machine_body"
  let hs := c.hyps
  let outsF ← c.tblFn "outsOf"
  let insF ← c.tblFn "insOf"
  let ne ← `((fun h0 => absurd (congrArg List.length h0) (by decide)))
  -- par/r-5: the two output facts from the reader at the run's `hcore` / `entry`
  -- (the previous data path: the decided lemmas)
  let outTyT : Term ← if c.oldData then pure ⟨(c.lem "outTy").raw⟩
    else `((Tools.ShippingReaderOutsInv.outTy_of_core hcore entry))
  let outScalarT : Term ← if c.oldData then pure ⟨(c.lem "outScalar").raw⟩
    else `((Tools.ShippingReaderOutsInv.outScalar_of_core hcore entry))
  runTheorem c "runFacts" false
    (← `(Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b))
    (← if c.s.tagMode then `(Tools.ShippingMemKid.kidsM_runFactsT (nDecl := $nD) $d $ok $body
      $(c.lem "calls") $(c.lem "slots") $(c.lem "domB") $ne $ne $ne $outTyT
      $outsF $insF 0 ($(c.lem "kids") $hs*) $(c.lem "callWidths")
      hB hcore hpost entry closes)
      else `(Tools.ShippingMemKid.kidsM_runFacts (nDecl := $nD)
      (hagree := by first | decide | decide +kernel) $d $ok $body
      $(c.lem "calls") $(c.lem "slots") $(c.lem "domB") $ne $ne $ne $outTyT
      $outsF $insF 0 ($(c.lem "kids") $hs*) $(c.lem "callWidths")
      hB hcore hpost entry closes))
  runTheorem c "outsG0" true
    (← `(Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true))
    (← if c.s.tagMode then `(Tools.ShippingMemKid.kidsM_outsCheckT (nDecl := $nD) $d $ok $body
      $(c.lem "calls") $(c.lem "slots") $(c.lem "domB") $ne $ne $outTyT
      $outsF $insF 0 ($(c.lem "kids") $hs*)
      hB hcore hpost entry closes hg)
      else `(Tools.ShippingMemKid.kidsM_outsCheck (nDecl := $nD)
      (hagree := by first | decide | decide +kernel) $d $ok $body
      $(c.lem "calls") $(c.lem "slots") $(c.lem "domB") $ne $ne $outTyT
      $outsF $insF 0 ($(c.lem "kids") $hs*)
      hB hcore hpost entry closes hg))
  runTheorem c "mixedG" false
    (← `(Tools.ShippingMachineShipsHier.kidsMixed (Tools.ShippingMachineLinked.childMap D.modules)
      b.body = true))
    (← if c.s.tagMode then `(Tools.ShippingMemKid.kidsM_mixedT (nDecl := $nD) $d $ok $body
      $(c.lem "calls") $(c.lem "slots") $(c.lem "domB") $ne $ne $outTyT
      $outsF $insF 0 ($(c.lem "kids") $hs*)
      hB hcore hpost entry closes)
      else `(Tools.ShippingMemKid.kidsM_mixed (nDecl := $nD)
      (hagree := by first | decide | decide +kernel) $d $ok $body
      $(c.lem "calls") $(c.lem "slots") $(c.lem "domB") $ne $ne $outTyT
      $outsF $insF 0 ($(c.lem "kids") $hs*)
      hB hcore hpost entry closes))
  runTheorem c "designP0" false
    (← `(Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true))
    (← if c.s.tagMode then `(Tools.ShippingMemKid.kidsM_designCheckT (nDecl := $nD) $d $ok $body
      $(c.lem "calls") $(c.lem "slots") $(c.lem "domB") $ne $ne $ne $outTyT
      $outsF $insF 0 ($(c.lem "kids") $hs*) $(c.lem "callWidths") $(c.lem "callArgs")
      hB hcore hpost entry closes
      (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean ($(c.lem "outChars") o ho))
      $outScalarT)
      else `(Tools.ShippingMemKid.kidsM_designCheck (nDecl := $nD)
      (hagree := by first | decide | decide +kernel) $d $ok $body
      $(c.lem "calls") $(c.lem "slots") $(c.lem "domB") $ne $ne $ne $outTyT
      $outsF $insF 0 ($(c.lem "kids") $hs*) $(c.lem "callWidths") $(c.lem "callArgs")
      hB hcore hpost entry closes
      (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean ($(c.lem "outChars") o ho))
      $outScalarT))

/-- The module names of two different keys differ. -/
def neT (c : Ctx) (a b : Key) : CommandElabM Term := do
  let stmt ← `($(a.name) ≠ $(b.name))
  match a.leaf, b.leaf with
  | true, true =>
    if a.idx < b.idx then `(($(c.lem s!"leafNe{a.idx}_{b.idx}")))
    else `((show $stmt from Ne.symm $(c.lem s!"leafNe{b.idx}_{a.idx}")))
  | true, false =>
    `((show $stmt from fun e =>
      $(c.lem s!"leafNotin{a.idx}_{b.idx}") (List.mem_singleton.mpr e)))
  | false, true =>
    `((show $stmt from fun e =>
      $(c.lem s!"leafNotin{b.idx}_{a.idx}") (List.mem_singleton.mpr e.symm)))
  | false, false =>
    if a.idx < b.idx then `(($(c.lem s!"memNe{a.idx}_{b.idx}")))
    else `((show $stmt from Ne.symm $(c.lem s!"memNe{b.idx}_{a.idx}")))

/-- The module name of a key is not the parent's printed name. -/
def neParentT (c : Ctx) (a : Key) : CommandElabM Term := do
  let fq : Term := quote c.f
  if a.leaf then `(($(c.lem s!"leafNeParent{a.idx}")))
  else
    `((show $(a.name) ≠ (Sparkle.IR.ModuleName.ofDecl ($fq : Lean.Name)) from fun e =>
      $(c.lem s!"notinP{a.idx}") (List.mem_singleton.mpr e.symm)))

/-- The data conditions of the closing, the name lemmas, the interfaces, and
`f.noPortsMemSeq_closes : (MachineDefines of each leaf callee) → MachineClosesAt f`. -/
def closingTheorems (c : Ctx) : CommandElabM Unit := do
  let d := c.data
  let fq : Term := quote c.f
  let nD := Syntax.mkNumLit (toString c.s.nDecl)
  let keys := c.keys.toList
  let leafKeys := keys.filter (fun x => x.leaf)
  let memKeys := keys.filter (fun x => !x.leaf)
  let nameF ← c.tblFn "nameOf"
  let nkF ← c.tblFn "nkOf"
  let outsNF ← c.tblFn "outsNOf"
  let namesF ← c.tblFn "namesOf"
  let nameOf := c.lem "nameOf"
  let nkOf := c.lem "nkOf"
  let outsNOf := c.lem "outsNOf"
  let namesOf := c.lem "namesOf"
  decided c "alias" (← `(($d).letsAliasOk = true))
  decided c "argsN" (← `(∀ (k : Nat) (hk : k < ($d).shape.insts.length),
    $nkOf ($(c.keyFn) $d k) = (($d).shape.insts[k]).2.1.length))
  decided c "fieldOut" (← `(∀ (k : Nat), k < ($d).shape.insts.length →
    ($d).shape.instFields.getD k "" ∈ $outsNOf ($(c.keyFn) $d k)))
  decided c "fieldsNd" (← if c.s.tagMode then `(∀ (k : Nat) (hk : k < ($d).shape.insts.length) (k' : Nat)
    (hk' : k' < ($d).shape.insts.length),
    (($d).shape.insts[k]).1 = (($d).shape.insts[k']).1 →
    Tools.ShippingMemCloses.memKey (Tools.ShippingInstTagged.originAt ($d).shape k) =
      Tools.ShippingMemCloses.memKey (Tools.ShippingInstTagged.originAt ($d).shape k') →
    (($d).shape.insts[k]).2.1 = (($d).shape.insts[k']).2.1 →
    ($d).shape.instFields.getD k "" = ($d).shape.instFields.getD k' "" → k = k')
    else `(∀ (k : Nat) (hk : k < ($d).shape.insts.length) (k' : Nat)
    (hk' : k' < ($d).shape.insts.length),
    (($d).shape.insts[k]).1 = (($d).shape.insts[k']).1 →
    (($d).shape.insts[k]).2.1 = (($d).shape.insts[k']).2.1 →
    ($d).shape.instFields.getD k "" = ($d).shape.instFields.getD k' "" → k = k'))
  decided c "outHead" (← `(∀ o ∈ ($d).shape.layout.outs, o.name.toList.head? ≠ some 'i'))
  -- names: the SAME lemma names and statements on both paths. Default: the
  -- general lemmas of the injective encoding (declaration / memory with no
  -- condition; declaration / declaration by `decide` on `Lean.Name`s; memory /
  -- memory by `decide` on the parameters). `shipping.nameCandidates`: the
  -- previous proofs (`name_not_mem`, the candidate renderings, a string `decide`).
  let oldNames := shipping.nameCandidates.get (← getOptions)
  let notMemPf : Term ← if oldNames then `((by name_not_mem))
    else `(Tools.ShippingMemSeqNames.decl_not_mem_memName _ _ _ _)
  let declNePf : Term ← if oldNames then
      `(Tools.ShippingNameSep.Enc.sep_ne (by first | decide | decide +kernel))
    else `(Tools.ShippingModuleName.ofDecl_ne (by first | decide | decide +kernel))
  for mk in memKeys do
    emitThm c (c.lemName s!"notinP{mk.idx}") fun tn => `(command|
      set_option maxHeartbeats 4000000 in
      theorem $tn : (Sparkle.IR.ModuleName.ofDecl ($fq : Lean.Name)) ∉ $(mk.names) :=
        $notMemPf)
    for lk in leafKeys do
      emitThm c (c.lemName s!"leafNotin{lk.idx}_{mk.idx}") fun tn => `(command|
        set_option maxHeartbeats 4000000 in
        theorem $tn : $(lk.name) ∉ $(mk.names) :=
          $notMemPf)
  for lk in leafKeys do
    emitThm c (c.lemName s!"leafNeParent{lk.idx}") fun tn => `(command|
      set_option maxHeartbeats 4000000 in
      theorem $tn : $(lk.name) ≠ (Sparkle.IR.ModuleName.ofDecl ($fq : Lean.Name)) :=
        $declNePf)
    for lk' in leafKeys do
      if lk.idx < lk'.idx then
        emitThm c (c.lemName s!"leafNe{lk.idx}_{lk'.idx}") fun tn => `(command|
          set_option maxHeartbeats 4000000 in
          theorem $tn : $(lk.name) ≠ $(lk'.name) :=
            $declNePf)
  for mk in memKeys do
    for mk' in memKeys do
      if mk.idx < mk'.idx then
        if oldNames then
          decided c s!"memNe{mk.idx}_{mk'.idx}" (← `($(mk.name) ≠ $(mk'.name)))
        else
          emitThm c (c.lemName s!"memNe{mk.idx}_{mk'.idx}") fun tn => `(command|
            set_option maxHeartbeats 4000000 in
            theorem $tn : $(mk.name) ≠ $(mk'.name) :=
              Tools.ShippingMemSeqNames.memName_ne (by first | decide | decide +kernel))
  -- the interface of a leaf callee's real child (the hand `cnt_iface`)
  for lk in leafKeys do
    let D := nm lk.decl "machineData"
    emitThm c (c.lemName s!"iface{lk.idx}") fun tn => `(command|
      set_option maxHeartbeats 4000000 in
      theorem $tn {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
          {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
          (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $(lk.key)
            ($D).shape)
          {y : Tools.ShippingChildInv.Res}
          (hy : Tools.ShippingChildInv.RealChild mref cref $(lk.key) y) :
          Tools.ShippingMemCloses.ChildIfaceP $(lk.name) $(lk.nk) $(lk.outsN) $(lk.names)
            y.1 y.2 := by
        have lk := $(nm lk.decl "machine_leafKid") hRc
        have hG := Tools.ShippingSeqChildIface.seqChild_of_real $D lk.ok lk.body lk.leaf
          lk.outTy lk.entry lk.closes hy
        exact Tools.ShippingCallsKidsD.ChildIfaceD.toP
          (Tools.ShippingCallsKidsD.ChildIfaceG.toD hG) (fun hx => nomatch hx))
  let h := mkIdent `h
  let h' := mkIdent `h'
  let hT : Term := ⟨h.raw⟩
  let hTp : Term := ⟨h'.raw⟩
  let entry := c.lem "entry"
  let eK ← `($entry k hk)
  let eK' ← `($entry k' hk')
  let at_ (tbl : String) (i : Nat) : Term := ⟨(c.lem s!"{tbl}_at{i}").raw⟩
  let idxKeys := keys.zipIdx
  -- every kid has the interface
  let mut brP : List Term := []
  for (key, i) in idxKeys do
    if c.s.tagMode then
      let fin ← if key.leaf then
          `($(c.lem s!"iface{key.idx}") $(Ctx.hR key.idx)
            (Tools.ShippingInstTagged.KidT.real hy
              (Tools.ShippingMemCloses.child?_none_of_memKey ($hT).2)))
        else
          `(Tools.ShippingMemCloses.memKidT_iface
            (Tools.ShippingMemCloses.child?_of_memKey ($hT).2) hy)
      brP := brP ++ [← `((by
        rw [($hT).1] at hy
        rw [($hT).1, ($hT).2, $(at_ "nameOf" i):term, $(at_ "nkOf" i):term,
          $(at_ "outsNOf" i):term, $(at_ "namesOf" i):term]
        exact $fin))]
    else
      let fin ← if key.leaf then
          `($(c.lem s!"iface{key.idx}") $(Ctx.hR key.idx) (hy.real $(key.isMem)))
        else
          `(Tools.ShippingMemCloses.memKid_iface $(key.isMem) hy)
      brP := brP ++ [← `((by
        rw [$hT:term] at hy ⊢
        rw [$(at_ "nameOf" i):term, $(at_ "nkOf" i):term, $(at_ "outsNOf" i):term,
          $(at_ "namesOf" i):term]
        exact $fin))]
  let kidsPPf ← orElim h eK brP
  let bs ← c.binders
  let hs := c.hyps
  let kidHyp ← if c.s.tagMode then
      `(Tools.ShippingInstTagged.KidT mref cref (Tools.ShippingInstTagged.originAt ($d).shape k)
        (($d).shape.insts[k]).1 y)
    else `(Tools.ShippingMemKid.Kid mref cref (($d).shape.insts[k]).1 y)
  emitThm c (c.lemName "kidsP") fun tn => `(command|
    set_option maxHeartbeats 4000000 in
    theorem $tn {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
        {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} $bs* :
        ∀ (k : Nat) (hk : k < ($d).shape.insts.length) (y : Tools.ShippingChildInv.Res),
          $kidHyp →
          Tools.ShippingMemCloses.ChildIfaceP
            ($nameOf ($(c.keyFn) $d k))
            ($nkOf ($(c.keyFn) $d k))
            ($outsNOf ($(c.keyFn) $d k))
            ($namesOf ($(c.keyFn) $d k)) y.1 y.2 := by
      intro k hk y hy
      rw [$(c.keyEq) $d hk]
      exact $kidsPPf)
  -- different callees have different module names
  let mut outerS : List Term := []
  for (a, i) in idxKeys do
    let mut inner : List Term := []
    for (b, j) in idxKeys do
      if i == j then
        inner := inner ++ [← if c.s.tagMode then
            `(⟨(($hT).1).trans (($hTp).1).symm, (($hT).2).trans (($hTp).2).symm⟩)
          else `(($hT).trans ($hTp).symm)]
      else
        let ne ← neT c a b
        let rules := (← c.hRules hT) ++ (← c.hRules hTp) ++ #[at_ "nameOf" i, at_ "nameOf" j]
        inner := inner ++ [← `((by
          rw [$[$rules:term],*] at he
          exact absurd he $ne))]
    outerS := outerS ++ [← orElim h' eK' inner]
  let sepPf ← orElim h eK outerS
  let sepC ← if c.s.tagMode then
      `((($d).shape.insts[k]).1 = (($d).shape.insts[k']).1 ∧
        Tools.ShippingMemCloses.memKey (Tools.ShippingInstTagged.originAt ($d).shape k) =
          Tools.ShippingMemCloses.memKey (Tools.ShippingInstTagged.originAt ($d).shape k'))
    else `((($d).shape.insts[k]).1 = (($d).shape.insts[k']).1)
  emitThm c (c.lemName "sep") fun tn => `(command|
    set_option maxHeartbeats 4000000 in
    theorem $tn : ∀ (k : Nat) (hk : k < ($d).shape.insts.length) (k' : Nat)
        (hk' : k' < ($d).shape.insts.length),
        $nameOf ($(c.keyFn) $d k) =
          $nameOf ($(c.keyFn) $d k') →
        $sepC := by
      intro k hk k' hk' he
      rw [$(c.keyEq) $d hk,
        $(c.keyEq) $d hk'] at he
      exact $sepPf)
  -- no child module is named as the parent
  let mut brPar : List Term := []
  for (a, i) in idxKeys do
    brPar := brPar ++ [← rwExact ((← c.hRules hT) ++ #[at_ "nameOf" i]) (← neParentT c a)]
  let parentPf ← orElim h eK brPar
  emitThm c (c.lemName "parent") fun tn => `(command|
    set_option maxHeartbeats 4000000 in
    theorem $tn : ∀ (k : Nat), k < ($d).shape.insts.length →
        $nameOf ($(c.keyFn) $d k) ≠ (Sparkle.IR.ModuleName.ofDecl ($fq : Lean.Name)) := by
      intro k hk
      rw [$(c.keyEq) $d hk]
      exact $parentPf)
  -- the parent's name is not a module name of a child's design
  let mut brPD : List Term := []
  for (a, i) in idxKeys do
    let fin ← if a.leaf then `((fun hx => nomatch hx))
      else `(($(c.lem s!"notinP{a.idx}")))
    brPD := brPD ++ [← rwExact ((← c.hRules hT) ++ #[at_ "namesOf" i]) fin]
  let parentDPf ← orElim h eK brPD
  emitThm c (c.lemName "parentD") fun tn => `(command|
    set_option maxHeartbeats 4000000 in
    theorem $tn : ∀ (k : Nat), k < ($d).shape.insts.length →
        (Sparkle.IR.ModuleName.ofDecl ($fq : Lean.Name)) ∉ $namesOf ($(c.keyFn) $d k) := by
      intro k hk
      rw [$(c.keyEq) $d hk]
      exact $parentDPf)
  -- two different callees share no module name
  let mut outerD : List Term := []
  for (a, i) in idxKeys do
    let mut inner : List Term := []
    for (b, j) in idxKeys do
      if i == j then
        inner := inner ++ [← if c.s.tagMode then
            `(absurd ⟨(($hT).1).trans (($hTp).1).symm, (($hT).2).trans (($hTp).2).symm⟩ hne)
          else `(absurd (($hT).trans ($hTp).symm) hne)]
      else
        let ne ← neT c a b
        let p1 ← if b.leaf then `((fun hx => nomatch hx))
          else `((fun hx => $ne (List.mem_singleton.mp hx)))
        let p2 ← if a.leaf then `((fun x hx => nomatch hx))
          else if b.leaf then `((fun x _ hx => nomatch hx))
          else `((fun x hx hx' =>
            $ne ((List.mem_singleton.mp hx).symm.trans (List.mem_singleton.mp hx'))))
        let rulesD := (← c.hRules hT) ++ (← c.hRules hTp) ++
          #[at_ "nameOf" i, at_ "namesOf" i, at_ "namesOf" j]
        inner := inner ++ [← `((by
          rw [$[$rulesD:term],*]
          exact ⟨$p1, $p2⟩))]
    outerD := outerD ++ [← orElim h' eK' inner]
  let disjPf ← orElim h eK outerD
  let disjH ← if c.s.tagMode then
      `(¬ ((($d).shape.insts[k]).1 = (($d).shape.insts[k']).1 ∧
        Tools.ShippingMemCloses.memKey (Tools.ShippingInstTagged.originAt ($d).shape k) =
          Tools.ShippingMemCloses.memKey (Tools.ShippingInstTagged.originAt ($d).shape k')))
    else `((($d).shape.insts[k]).1 ≠ (($d).shape.insts[k']).1)
  emitThm c (c.lemName "disj") fun tn => `(command|
    set_option maxHeartbeats 4000000 in
    theorem $tn : ∀ (k : Nat) (hk : k < ($d).shape.insts.length) (k' : Nat)
        (hk' : k' < ($d).shape.insts.length),
        $disjH →
        $nameOf ($(c.keyFn) $d k) ∉
            $namesOf ($(c.keyFn) $d k') ∧
          ∀ x ∈ $namesOf ($(c.keyFn) $d k),
            x ∉ $namesOf ($(c.keyFn) $d k') := by
      intro k hk k' hk' hne
      rw [$(c.keyEq) $d hk, $(c.keyEq) $d hk']
      exact $disjPf)
  -- the closing (M2): from the reflections of the leaf callees only
  if c.s.tagMode then
    emitThm c (c.lemName "closes") fun tn => `(command|
      set_option maxHeartbeats 4000000 in
      theorem $tn {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
          {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} $bs* :
          Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref $fq ($d).shape :=
        Tools.ShippingMemCloses.machineClosesAt_of_kidsDMT (nDecl := $nD) $d
          $(nm c.f "machine_ok") $(nm c.f "machine_body")
          $(c.lem "alias") $(c.lem "calls") $(c.lem "slots") $(c.lem "domB")
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          $nameF $nkF $outsNF $namesF
          ($(c.lem "kidsP") $hs*) $(c.lem "argsN") $(c.lem "fieldOut") $(c.lem "fieldsNd")
          $(c.lem "sep") $(c.lem "parent")
          (fun gi _ _ o ho =>
            Tools.ShippingCallsGate.instName_ne_of_head ($(c.lem "outHead") o ho) gi _)
          $(c.lem "parentD") $(c.lem "disj"))
  else
    emitThm c (c.lemName "closes") fun tn => `(command|
      set_option maxHeartbeats 4000000 in
      theorem $tn {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
          {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} $bs* :
          Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref $fq ($d).shape :=
        Tools.ShippingMemCloses.machineClosesAt_of_kidsDM (nDecl := $nD) $d
          $(nm c.f "machine_ok") $(nm c.f "machine_body")
          $(c.lem "alias") $(c.lem "calls") $(c.lem "slots") $(c.lem "domB")
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          $nameF $nkF $outsNF $namesF
          ($(c.lem "kidsP") $hs*) $(c.lem "argsN") $(c.lem "fieldOut") $(c.lem "fieldsNd")
          $(c.lem "sep") $(c.lem "parent")
          (fun gi _ _ o ho =>
            Tools.ShippingCallsGate.instName_ne_of_head ($(c.lem "outHead") o ho) gi _)
          $(c.lem "parentD") $(c.lem "disj")
          -- origin dispatch (patched compiler): names say what their origins build
          (show Tools.ShippingInstTagged.TagsAgree ($d).shape by
            first | decide | decide +kernel))

/-! ## The endpoint (the hand generator, restated) -/

/-- The statement and the proof of `f.machine_design_noPortsR0`
(`Tests.Compiler.NoPortsMemSeqMemTest.generateR0`, restated; nothing is added
to the environment): the head `machine_design_noPorts` at `n = 0` on the
arguments of `f.machine_ships_hierR` (where `KSn _ 0` is `flatKS` and the
theorem's own `Bd` / `Inv` — `kidsMixed` / `mixInv` — are passed through).
The four run theorems' extra hypotheses are discharged from the conjuncts of
the endpoint's boundary only (`dischargeWith … #[]`): NO binder is added. -/
def endpointTerm (f : Name) (facts outs mixed design : Name) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let ships := f ++ `machine_ships_hierR
  let name := f ++ `machine_design_noPortsR0
  let env ← getEnv
  let some (.thmInfo ti) := env.find? ships
    | throwError "{ships}: not a theorem (run #machine_design_svR0 first)"
  let v := ti.value
  unless v.isAppOf ``Tools.ShippingMachineShipsHier.machine_ships_hierC do
    throwError "{ships}: not built from machine_ships_hierC"
  let a := v.getAppArgs
  unless a.size == 25 do throwError "{ships}: {a.size} arguments of machine_ships_hierC, expected 25"
  let value ← forallTelescope (← inferType (mkConst ships)) fun xs _ => do
    unless xs.size == 11 do throwError "{ships}: {xs.size} binders, expected 11"
    let args : Array (Option Lean.Expr) :=
      #[some (mkNatLit 0), some a[3]!, some a[4]!, some a[5]!, some a[6]!, some a[7]!,
        some a[8]!, some a[9]!, some a[10]!, some a[11]!,
        some a[12]!, some a[13]!, some a[14]!, some a[15]!, some a[16]!, some a[17]!,
        some a[18]!, some a[19]!, some a[20]!, some a[21]!,
        some a[22]!, some a[23]!, some a[24]!] ++ xs.map some
    let pre ← instantiateMVars
      (← mkAppOptM ``Tools.ShippingNoPorts.machine_design_noPorts args)
    if pre.hasMVar then throwError "{f}: the head's arguments were not all inferred"
    -- the run's facts: zs = raw D w1 hcore hpost hBnd ; xs[9] = entry, xs[10] = closes
    let .forallE _ TF _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's run-facts hypothesis is not where it is expected"
    let hFacts ← forallTelescope TF fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the run-facts hypothesis has {zs.size} binders"
      let p ← mkAppM facts #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← dischargeWith facts p zs[5]! goal #[])
    let pre := mkApp pre hFacts
    -- the output check under the gate: zs = raw D w1 hcore hpost hg hBnd
    let .forallE _ TO _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's output-check hypothesis is not where it is expected"
    let hOuts ← forallTelescope TO fun zs goal => do
      unless zs.size == 7 do throwError "{f}: the output-check hypothesis has {zs.size} binders"
      let p ← mkAppM outs #[zs[3]!, zs[4]!, xs[9]!, xs[10]!, zs[5]!]
      mkLambdaFVars zs (← dischargeWith outs p zs[6]! goal #[])
    let pre := mkApp pre hOuts
    -- the children's bound: zs = raw D w1 hcore hpost hBnd (cut at 6 binders)
    let .forallE _ TM _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's children-bound hypothesis is not where it is expected"
    let hMixed ← forallBoundedTelescope TM (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the children-bound hypothesis has {zs.size} binders"
      let p ← mkAppM mixed #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← dischargeWith mixed p zs[5]! goal #[])
    let pre := mkApp pre hMixed
    -- `designCheck` with no check premise: zs = raw D w1 hcore hpost hBnd (cut at 6)
    let .forallE _ TD _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's design-check hypothesis is not where it is expected"
    let hDesign ← forallBoundedTelescope TD (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the design-check hypothesis has {zs.size} binders"
      let p ← mkAppM design #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← dischargeWith design p zs[5]! goal #[])
    mkLambdaFVars xs (mkApp pre hDesign)
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  for c in forbiddenMem do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{name}: REFUSED, the statement still mentions {c}"
  return (type, value)

/-- `c.machine_leafKid` of a leaf callee: generated by the BUILT
`leafKidTheorem` when absent; when present, its statement is checked against
the expected one and it is used. One log line either way. -/
def leafKid (c : Ctx) (k : Name) : CommandElabM Unit := do
  let name := k ++ `machine_leafKid
  let env ← getEnv
  if env.contains name then
    let kq : Term := quote k
    let D := nm k "machineData"
    let stx ← `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State},
      Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $kq ($D).shape →
      Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref $kq $D)
    let same ← liftTermElabM do
      let e ← instantiateMVars (← Lean.Elab.Term.elabType stx)
      isDefEq e (← getConstInfo name).type
    unless same do
      throwError "{name}: EXISTS with a statement that is not (MachineDefines {k} → LeafKid {k} {k}.machineData)"
    c.log.modify fun a => a.push s!"USED {name}: exists; its statement is the expected one (isDefEq), not re-added (a prerequisite of the callee, shared by its parents)"
  else
    discard <| noAsync (Tools.ShippingNoPortsCommand.leafKidTheorem k)
    c.log.modify fun a => a.push s!"GENERATED {name} (by the built leafKidTheorem)"

/-- The generation proper (after the scope): the lemmas, the two endpoints,
the premise lines. Returns the log lines, the premise lines and whether the
open endpoint was rebuilt (it existed). -/
def core (f : Name) (s : Scope) (oldData : Bool := false) :
    CommandElabM (Array String × Array String × Bool) := do
  let log ← IO.mkRef (#[] : Array String)
  let keys ← mkKeys s
  let c : Ctx := { f, s, log, keys, m := { f, s := default, log }, oldData }
  if oldData then
    log.modify fun a => a.push "OLDDATA: the previous data path (outTy / outScalar decided per declaration and passed to kidsM_*)"
  else
    log.modify fun a => a.push "DATA FROM THE READER: no outTy / outScalar decided; kidsM_* take outTy_of_core / outScalar_of_core at hcore, entry"
  for k in s.leaves do leafKid c k
  tableTheorems c
  dataTheorems c
  runTheorems c
  let name := f ++ `machine_design_noPortsR0
  let existed := (← getEnv).contains name
  let (openC, line1) ← liftTermElabM <|
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun k => { k with maxRecDepth := 1000000, maxHeartbeats := 0 }) do
        let (type, value) ← endpointTerm f (c.lemName "runFacts") (c.lemName "outsG0")
          (c.lemName "mixedG") (c.lemName "designP0")
        addOrCompare name type value
  log.modify fun a => a.push line1
  closingTheorems c
  let cl := c.lemName "closes"
  -- the closing theorem: its proposition premises are the leaf callees' reflections, no other
  let (nPrem, onlyRefl) ← liftTermElabM do
    forallTelescope (← getConstInfo cl).type fun xs _ => do
      let mut n : Nat := 0
      let mut ok : Bool := true
      for x in xs do
        let ty ← instantiateMVars (← inferType x)
        if ← isProp ty then
          n := n + 1
          unless ty.isAppOf ``Tools.ShippingMachineEntry.MachineDefines do ok := false
      pure (n, ok)
  unless onlyRefl && nPrem == s.leaves.length do
    throwError "{cl}: {nPrem} proposition premise(s) (all reflections: {onlyRefl}), expected the {s.leaves.length} reflection(s) of {s.leaves} and nothing else"
  let closedN := Tools.ShippingMachineClosesGen.closedName name
  let (closedC, line2) ← liftTermElabM <|
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun k => { k with maxRecDepth := 1000000, maxHeartbeats := 0 }) do
        let (type, value) ← closedTerm f openC cl 0
        for k in forbiddenMem ++ [``Tools.ShippingMachineEntry.MachineCloses,
            ``Tools.ShippingChildInv.MachineClosesAt, ``Tools.ShippingChildInv.ChildRanIn] do
          if (type.find? (·.isConstOf k)).isSome then
            throwError "{closedN}: REFUSED, the closed statement mentions {k}"
        addOrCompare closedN type value
  log.modify fun a => a.push (line2 ++ s!" (closing: {cl}, premises: MachineDefines of {s.leaves})")
  -- the premise lines: exactly one NOT ALLOWED in the open form, none in the closed one
  let (linesO, badO) ← liftTermElabM (premiseLines openC)
  let (linesC, badC) ← liftTermElabM (premiseLines closedC)
  unless badO.size == 1 do
    throwError "{openC}: {badO.size} premises NOT ALLOWED, expected exactly 1 (MachineClosesAt {f}):\n{String.intercalate "\n" badO.toList}"
  unless badC.isEmpty do
    throwError "{closedC}: {badC.size} premise(s) NOT ALLOWED, expected none:\n{String.intercalate "\n" badC.toList}"
  unless linesC.size + 1 == linesO.size + s.leaves.length do
    throwError "{closedC}: {linesC.size} premises listed against {linesO.size} of {openC}, expected one fewer plus {s.leaves.length} reflection(s)"
  let kinds := s.mems.map fun (p, cb, aw, dw) =>
    let kindS : String := if cb then "combinational" else "synchronous"
    s!"{p} ({kindS} read, aw {aw}, dw {dw})"
  let wS : String :=
    if s.widthsDiffer then "the placeholders have DIFFERENT (aw, dw): per-entry tables (KidFactsM / ChildIfaceP per entry)"
    else "one (aw, dw) for all placeholders"
  let summary := s!"mixed parent, nDecl {s.nDecl}, {s.slots} register slot(s), call entries {s.calls}; leaf register machine callees {s.leaves}; placeholders {kinds}; {wS}. {name}: {linesO.size} premises listed, 1 NOT ALLOWED (MachineClosesAt {f}); {closedN}: {linesC.size} premises listed, 0 NOT ALLOWED (the run, MachineDefines {f}, MachineDefines of {s.leaves}, and the boundary under the existentials). No statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN, hierCheck, kidsMixed, kidsMem or kidsMasked; the closed one no MachineCloses / MachineClosesAt / ChildRanIn. SCOPE: one declaration, depth 0, data conditions decided per declaration (conditions, not reductions), compiler guards with fallback, DesignSV of the module list — not the SV string, not #sim; the run, the reflections of {f} and of {s.leaves} and ChildBnd remain premises"
  return ((← log.get).push summary, linesO ++ linesC, existed)

/-- What the command did. -/
inductive Outcome where
  /-- the endpoint was not there: everything generated -/
  | generated (lines premises : Array String)
  /-- the endpoint was there: rebuilt and compared -/
  | rebuilt (lines premises : Array String)
  /-- outside the scope: the reason -/
  | refused (reason : String)
  /-- inside the scope, but a generated proof or a check failed -/
  | failed (reason : String)

def Outcome.tag (o : Outcome) : String :=
  match o with
  | Outcome.generated _ _ => "GENERATED"
  | Outcome.rebuilt _ _ => "REBUILT"
  | Outcome.refused _ => "REFUSED"
  | Outcome.failed _ => "FAILED"

/-- The log text of an outcome. -/
def line (f : Name) (o : Outcome) : String :=
  match o with
  | Outcome.generated ls ps =>
    s!"NOPORTS MEMSEQ {f}: GENERATED\n{String.intercalate "\n" ls.toList}\n{String.intercalate "\n" ps.toList}"
  | Outcome.rebuilt ls ps =>
    s!"NOPORTS MEMSEQ {f}: REBUILT (compare path)\n{String.intercalate "\n" ls.toList}\n{String.intercalate "\n" ps.toList}"
  | Outcome.refused r => s!"NOPORTS MEMSEQ {f}: REFUSED ({r})"
  | Outcome.failed r => s!"NOPORTS MEMSEQ {f}: FAILED ({r})"

/-- The generator on `f`: never throws; on REFUSED / FAILED the environment
and the message log are put back. -/
def noPortsMemSeq (f : Name) (oldData : Bool := false) : CommandElabM Outcome := do
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  let restore : CommandElabM Unit := do
    setEnv savedEnv
    modify fun st => { st with messages := savedMsgs }
  let sc? : Except String Scope ← try
      pure (Except.ok (← scope f))
    catch ex =>
      let msg ← ex.toMessageData.toString
      restore
      pure (Except.error msg)
  match sc? with
  | Except.error reason => return Outcome.refused reason
  | Except.ok sc =>
    try
      let (ls, ps, existed) ← core f sc oldData
      if existed then return Outcome.rebuilt ls ps else return Outcome.generated ls ps
    catch ex =>
      let msg ← ex.toMessageData.toString
      restore
      return Outcome.failed msg

/-- `#machine_no_ports_memseq f`: an error where it is refused or fails. -/
elab "#machine_no_ports_memseq " d:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← noPortsMemSeq f
  match o with
  | Outcome.refused _ => throwError "{line f o}"
  | Outcome.failed _ => throwError "{line f o}"
  | _ => logInfo m!"{line f o}"

/-- `#machine_no_ports_memseq_try f "EXPECTED"`: the outcome is LOGGED
(`NOPORTS MEMSEQ f: GENERATED | REBUILT | REFUSED (reason) | FAILED (condition)`),
and it is an error when its class is not the expected one. A refused or
failed declaration leaves nothing in the environment. -/
elab "#machine_no_ports_memseq_try " d:ident ppSpace e:str : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← noPortsMemSeq f
  logInfo m!"{line f o}"
  unless o.tag == e.getString do
    throwError "NOPORTS MEMSEQ {f}: expected {e.getString}, found {o.tag}"

/-- `#machine_no_ports_memseq_olddata f`: the generator with the PREVIOUS data
path (`f.noPortsMemSeq_outTy` / `_outScalar` decided and passed to the four
run theorems). Kept to compare the two paths on one tree (par/r-5). -/
elab "#machine_no_ports_memseq_olddata " d:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← noPortsMemSeq f (oldData := true)
  match o with
  | Outcome.refused _ => throwError "{line f o}"
  | Outcome.failed _ => throwError "{line f o}"
  | _ => logInfo m!"{line f o}"

/-- `#machine_no_ports_memseq_olddata_try f "EXPECTED"`: as
`#machine_no_ports_memseq_try`, on the previous data path. -/
elab "#machine_no_ports_memseq_olddata_try " d:ident ppSpace e:str : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← noPortsMemSeq f (oldData := true)
  logInfo m!"{line f o}"
  unless o.tag == e.getString do
    throwError "NOPORTS MEMSEQ {f}: expected {e.getString}, found {o.tag}"

end Tools.ShippingNoPortsMemSeqCommand
