import Lean.Elab.Command
import Tools.ShippingNoPortsKidsCommand
import Tools.ShippingMachineShipsHierCommand
import Tools.ShippingMachineSeqLinkedR
import Tools.ShippingMemOnly
import Tools.ShippingMemOnlyCloses
import Tools.ShippingMemOnlyNames
import Tools.ShippingMemTransport
import Tools.ShippingNameSep
import Tools.ShippingFinalGoalCommand
import Tools.ShippingMachineClosesGen
import Tools.ShippingReaderMemOnlyCloses
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

/-! # `#machine_no_ports_mem f`: the check-free depth-0 endpoint of a MEMORY-ONLY parent, open and closed, GENERATED (round par/b-20)

The six memory-only parents (`memCounter`, `syncNarrow`, `memWide`,
`twoMems`, `mixedMems`, and the transported `withMemory`) have their
endpoints by hand (`Tests/Compiler/NoPortsMemOnlyAt<Decl>Test`,
`NoPortsMemOnlyClosed<Decl>Test`, `NoPortsMemWithMemoryTest`). This command
produces the same two statements from the reader's data. NO general theorem
is added here: the proofs are those of the hand files, over
`Tools.ShippingMemOnly` (`MemOnlyData`, `memOnly_*`),
`Tools.ShippingMemOnlyCloses` (`machineClosesAt_of_memOnlyData`,
`MemOnlyCloseData`, `sep_of_one`, `parent_of_one`, `memNameAt_eq`) and
`Tools.ShippingMemTransport.composedG_src`.

## Scope

A machine `f` with `f.machineData / machine_ok / machine_body /
machine_sound / machine_composedT / machine_ships_hier` (route `.mem`), at
least one register slot, the general closing (`instFields ≠ []`), and EVERY
call entry a memory placeholder `SparkleMem.{combo|sync}.aw.dw` — either
read kind, any number of different placeholders, ONE `(aw, dw)` for all of
them (the built `MemOnlyData d nDecl aw dw` takes one pair). A transported
endpoint (fused loops, sign normalisation) is covered (`composedG_src`).
Depth 0 only; the at-form closing only.

## Refusals (`scope`; never a silent return)

| condition | reason line |
|---|---|
| no `f.machineData / machine_ok / machine_body` | not a machine with an endpoint |
| no call entry | no call |
| a non-memory callee that reaches a memory parent | memory at depth ≥ 1: not covered |
| no memory callee at all | no memory callee (machine / gate children: other commands) |
| memory entries AND other callees | mixed memory / machine children: the seqMem pattern, not generated here |
| no register slot | parent without a register |
| `instFields = []` | not the general closing |
| two placeholders of different `(aw, dw)` | entries with different widths: not covered |
| an entry without 4 argument `let`s / a field that is not `out` | `hargsN` / `hfield` false |
| two entries of one placeholder on the same argument `let`s | one memory read twice on the same argument lets (`hargsNd` false) |
| an output whose name starts with `i` | `hout` false |
| no `f.machine_sound / machine_composedT / machine_ships_hier` | the commands to run first |

The ALL-WORLDS endpoint `f.machine_design_noPorts0` (closing premise
`MachineCloses`) is never generated: that premise cannot be discharged for a
shape with calls (`Tools/ShippingMemOnlyAtAll.lean`). After the scope, a
`machine_ships_hier` that is not of the memory route (reset not `ResetM`,
child bound not `kidsMem`, boundary not `True`, closing not `MachineCloses`)
is an error with its own line (class `FAILED`).

## Generated, in this order

    f.noPortsMem_entry        every call entry is one of the placeholders (decided)
    f.noPortsMem_calls / _slots / _domB / _outTy / _callWidths / _callArgs /
      _outChars / _outScalar  the data conditions (decided)
    f.noPortsMem_data         MemOnlyData f.machineData nDecl aw dw
    f.noPortsMem_runFacts / _outsG0 / _kidsMemG / _designP0   memOnly_* at f's data
    f.machine_design_noPortsR0             the head machine_design_noPorts at n = 0
    f.noPortsMem_alias / _argsN / _field / _argsNd / _outHead   (decided)
    f.noPortsMem_closeData    MemOnlyCloseData f.machineData
    f.noPortsMem_closes       MachineClosesAt f — NO premise
    f.machine_design_noPortsR0_closed

## The name conditions (round par/b-30; WRITTEN, NOT BUILT)

`f.noPortsMem_closes` is
`Tools.ShippingMemOnlyNames.machineClosesAt_of_memOnlyData_names` (BUILT at
812061e5) on `f.noPortsMem_data` and `f.noPortsMem_closeData`: the closing's
two name hypotheses (`hsep`, `hparent`) follow from "every call entry is a
memory placeholder", a field of `MemOnlyData`. NO per-declaration name lemma
is generated any more.

The PREVIOUS path stays reachable for one round as
`#machine_no_ports_mem_oldnames f` / `#machine_no_ports_mem_oldnames_try f
"…"`: the same generator, with the closing by
`Tools.ShippingMemOnlyCloses.machineClosesAt_of_memOnlyData` and the lemmas

    f.noPortsMem_notin{j}     f's module name is not placeholder j's module's (name_not_mem)
    [several placeholders: f.noPortsMem_at{j}, f.noPortsMem_namesNe{i}_{j}
      (a kernel comparison of two module-name strings), f.noPortsMem_sep,
      f.noPortsMem_parent]

Every other generated name, and every generated STATEMENT, is the same in
the two paths (the statement of `f.noPortsMem_closes` and of the two
endpoints included); only the PROOF of `f.noPortsMem_closes` differs. Run
after the new path on one declaration, the old path takes the compare path
(below) on every shared name.

The two endpoints carry the hand tests' names. The lemmas do NOT: the hand
ones live in their test's namespace (`Tests.Compiler.NoPortsMemOnly…Test.
memCounter_data`, …); the generated ones are `f.noPortsMem_*`, so the two
sets never clash.

## The compare path (never a silent return)

If a name EXISTS, the theorem is rebuilt all the same, added under
`…_regen` (so its proof is kernel-checked) and its statement must be
`isDefEq` the existing one — otherwise an ERROR. The log says `REBUILT …
isDefEq` or `GENERATED` per name.

## What is restated here, and what is imported

IMPORTED (BUILT, `Tools/ShippingNoPortsKidsCommand.lean`): `dischargeWith`,
`closedTerm`, `addOrCompare`, `regenName`; `checkMade`
(`Tools/ShippingShipsFreeCommand.lean`); `endpointParts`
(`Tools/ShippingMachineSeqCommand.lean`).

RESTATED from `Tests/` (a `Tools/` file cannot import them):

* `forbiddenMem` — `Tests/Compiler/NoPortsMemOnlyCounterTest.lean` 149–152 (4 lines);
* `finish0` — `finishM0`, the same file 162–205 (44 lines), with the built
  `Tools` `dischargeWith` in place of the `Tests` copy;
* `endpointTerm` — `generateT0`, `Tests/Compiler/NoPortsMemWithMemoryLib.lean`
  141–227 (87 lines); it returns the statement and the proof instead of
  adding them (the compare path adds them). For an untransported parent it
  builds what `generateM0 (atForm := true)` builds;
* `innerAntecedents` / `premiseLines` — `Tests/Compiler/NoPortsTest.lean`
  114–160 (47 lines), with another log prefix;
* the theorem texts: the hand files' theorems as syntax (the single
  placeholder case is `NoPortsMemOnlyCounterTest` 407–563 +
  `NoPortsMemOnlyClosedMemCounterTest` 76–135; the several-placeholder case
  is `NoPortsMemOnlyAtMixedMemsTest` + `NoPortsMemOnlyClosedMixedMemsTest`
  75–198, its two-way `rcases` written as nested `Or.elim` over any number
  of placeholders).

## The output facts from the reader (round par/r-2; WRITTEN, NOT BUILT)

`#machine_no_ports_mem f` no longer decides `f.noPortsMem_outTy` and
`f.noPortsMem_outScalar`. It generates `f.noPortsMem_dataR :
MemOnlyDataR f.machineData nDecl aw dw` (`MemOnlyData` without those two
fields, `Tools/ShippingReaderOutsMemOnly.lean`, BUILT at 17560812) and

    f.noPortsMem_runFacts / _outsG0 / _kidsMemG / _designP0
        := memOnly_{runFacts,outsCheck,kidsMem,designCheck}_of_reader f.noPortsMem_dataR …
    f.noPortsMem_closes
        := Tools.ShippingReaderMemOnlyCloses.machineClosesAt_of_memOnlyDataR_names
             f.noPortsMem_dataR f.noPortsMem_closeData

The two output facts come from the general theorems `outTy_of_core` /
`outScalar_of_core` (every reader result) at the run hypotheses `hcore`,
`entry` the four run theorems already have; the closing never needed them.
EVERY generated STATEMENT shared by the two paths is the same text
(`runFacts`, `outsG0`, `kidsMemG`, `designP0`, `closes`, the two
endpoints); the new path has `dataR` in place of `outTy`, `outScalar`,
`data`.

The PREVIOUS path stays reachable as `#machine_no_ports_mem_olddata f` /
`#machine_no_ports_mem_olddata_try f "…"` (and `…_oldnames`, which is the
path before par/b-30 and therefore also the old data path). Run after the
new path on one declaration, the old path takes the compare path on every
shared name (`Tests/Compiler/NoPortsMemGenOldDataTest.lean`).

WRITTEN, NOT BUILT (par/b-20; par/r-2). -/
namespace Tools.ShippingNoPortsMemCommand
open Lean Meta Elab Command
open Tools.ShippingShipsFreeCommand (checkMade)
open Tools.ShippingNoPortsKidsCommand (dischargeWith closedTerm addOrCompare regenName)

/-- The parameters of a memory placeholder name `SparkleMem.{combo|sync}.aw.dw`
(the pattern of `Sparkle.Compiler.MachMemory.memChild?`). -/
def memParamsOf (c : Name) : Option (Bool × Nat × Nat) :=
  match c with
  | Name.num (Name.num (Name.str (Name.str Name.anonymous "SparkleMem") kd) aw) dw =>
    if kd == "combo" then Option.some (true, aw, dw)
    else if kd == "sync" then Option.some (false, aw, dw) else Option.none
  | _ => Option.none

/-- A machine below `k` (or `k` itself) one of whose call entries is a memory
placeholder, if any (searched `fuel` levels down through machine callees). -/
partial def memBelow (k : Name) (fuel : Nat) : MetaM (Option Name) := do
  if fuel == 0 then return Option.none
  let env ← getEnv
  unless env.contains (k ++ `machineData) do return Option.none
  let r? : Option Tools.ShippingMachineCommand.Read ← try
      pure (Option.some (← Tools.ShippingMachineCommand.readMachine k))
    catch _ => pure Option.none
  match r? with
  | Option.none => return Option.none
  | Option.some r =>
    let cs := (r.shape.insts.map (·.1)).eraseDups
    for c in cs do
      if (memParamsOf c).isSome then return Option.some k
    for c in cs do
      let below ← memBelow c (fuel - 1)
      if below.isSome then return below
    return Option.none

/-- What the scope scan read. -/
structure Scope where
  nDecl : Nat
  /-- the call entries' callees, in the reader's order -/
  calls : List Name
  /-- the distinct placeholders, in the order of their first entry:
  the name, the read kind (`true`: combinational), `aw`, `dw` -/
  mems : List (Name × Bool × Nat × Nat)
  aw : Nat
  dw : Nat
  slots : Nat
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
  let memCalls := (calls.filter fun c => (memParamsOf c).isSome).eraseDups
  let others := (calls.filter fun c => (memParamsOf c).isNone).eraseDups
  unless others.isEmpty do
    for c in others do
      let below ← liftTermElabM (memBelow c 8)
      match below with
      | Option.some h =>
        throwError "{f}: memory at depth ≥ 1 (its callee {c} reaches the machine {h}, which has a memory child): not covered — the depth chain's kidCheck rejects a memory statement at depth ≥ 1 (seqStmtOkI), and memKid_facts is at depth 0"
      | Option.none => pure ()
    if memCalls.isEmpty then
      throwError "{f}: no memory callee (its callees {others} are machine / gate children: #machine_no_ports, #machine_no_ports_kids, #machine_oneout_any are the commands for them)"
    else
      throwError "{f}: mixed memory / machine children (memory entries {memCalls}, other callees {others}): the seqMem pattern, not generated here"
  if r.shape.layout.slots.isEmpty then
    throwError "{f}: parent without a register (memOnly_runFacts / memOnly_designCheck ask d.shape.layout.slots ≠ [])"
  if r.shape.instFields.isEmpty then
    throwError "{f}: instFields = [] — not the general closing (machineClosesAt_memOnly asks d.shape.instFields ≠ [])"
  let mut mems : List (Name × Bool × Nat × Nat) := []
  for c in memCalls do
    match memParamsOf c with
    | Option.some (cb, aw, dw) => mems := mems ++ [(c, cb, aw, dw)]
    | Option.none => pure ()
  let (aw, dw) ← match mems with
    | (_, _, aw, dw) :: _ => pure (aw, dw)
    | [] => throwError "{f}: no memory callee"
  for (c, _, aw', dw') in mems do
    unless aw' == aw && dw' == dw do
      throwError "{f}: entries with different widths: not covered (the placeholders {mems.map (·.1)}: {c} is aw {aw'}, dw {dw'} against aw {aw}, dw {dw}; MemOnlyData takes ONE (aw, dw) — the per-entry generalisation is not written)"
  let args := r.shape.insts.map (·.2.1)
  for a in args do
    unless a.length == 4 do
      throwError "{f}: an entry has the argument lets {a}, not 4 (hargsN is false)"
  unless r.shape.instFields.length == calls.length do
    throwError "{f}: instFields = {r.shape.instFields} against {calls.length} entries (hfield is false: getD reads \"\")"
  for fld in r.shape.instFields do
    unless fld == "out" do
      throwError "{f}: instFields = {r.shape.instFields}; {fld} is not out (hfield is false)"
  let mut seen : List (Name × List Nat) := []
  for k in calls.zip args do
    if seen.contains k then
      throwError "{f}: one memory read twice on the same argument lets ({k.1} on {k.2}: hargsNd is false — two entries of one callee with one argument list are one instance, and the closing tells entries apart by their argument lets only)"
    seen := seen ++ [k]
  for o in r.shape.layout.outs do
    if o.name.toList.head? == Option.some 'i' then
      throwError "{f}: the output {o.name} starts with 'i' (hout is false: the freshness of the instance names is decided by the first character)"
  for s in [`machine_sound, `machine_composedT, `machine_ships_hier] do
    unless env.contains (f ++ s) do
      throwError "{f}: no {f ++ s} (run #machine_composedT {f} and #machine_ships_hier {f} first)"
  return { nDecl := r.nDecl, calls, mems, aw, dw, slots := r.shape.layout.slots.length }

/-! ## The generated theorems (the hand files' texts) -/

private def nm (d : Name) (s : String) : Ident := mkIdent (`_root_ ++ d ++ Name.mkSimple s)

private def noAsync {α : Type} (x : CommandElabM α) : CommandElabM α :=
  withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false }) x

/-- The names and the log shared by the generated theorems of `f`. -/
structure Ctx where
  f : Name
  s : Scope
  log : IO.Ref (Array String)
  /-- the previous closing path (per-declaration name lemmas; `…_oldnames`) -/
  oldNames : Bool := false
  /-- the previous data path (`outTy` / `outScalar` decided, `MemOnlyData`;
  `…_olddata`); implied by `oldNames` -/
  oldData : Bool := false

/-- Elaborate the theorem `mk name`. If `name` EXISTS: elaborate it under
`name_regen` and require the two statements to be `isDefEq` (an error
otherwise). One log word per name. -/
def emit (c : Ctx) (name : Name) (mk : Ident → CommandElabM (TSyntax `command)) :
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
      isDefEq (← getConstInfo name).type (← getConstInfo rn).type
    unless same do
      throwError "{name}: EXISTS with a different statement than the rebuilt {rn}"
    c.log.modify fun a => a.push s!"REBUILT {name}: statement isDefEq the existing one (proof kept as {rn})"
  else
    let before := (← get).messages.toList.length
    let cmd ← mk (mkIdent (`_root_ ++ name))
    noAsync (elabCommand cmd)
    checkMade name before
    c.log.modify fun a => a.push s!"GENERATED {name}"

namespace Ctx

def data (c : Ctx) : Ident := nm c.f "machineData"

def lem (c : Ctx) (s : String) : Ident := nm c.f s!"noPortsMem_{s}"

def lemName (c : Ctx) (s : String) : Name := c.f ++ Name.mkSimple s!"noPortsMem_{s}"

def boolT (b : Bool) : CommandElabM Term :=
  if b then `(true) else `(false)

/-- The placeholder name `j`, as a term. -/
def phT (c : Ctx) (j : Nat) : CommandElabM Term := do
  let (_, cb, aw, dw) := c.s.mems[j]!
  let cbT ← boolT cb
  `(Sparkle.Compiler.MachMemory.memChildName $cbT $(Syntax.mkNumLit (toString aw))
      $(Syntax.mkNumLit (toString dw)))

/-- The memory module of placeholder `j` (with its design), as a term. -/
def modT (c : Ctx) (j : Nat) : CommandElabM Term := do
  let (_, cb, aw, dw) := c.s.mems[j]!
  let cbT ← boolT cb
  `(Sparkle.Compiler.MachMemory.memModule $cbT $(Syntax.mkNumLit (toString aw))
      $(Syntax.mkNumLit (toString dw)))

/-- The placeholder's child is the built module (the hand `mem_isMem`). -/
def isMemT (c : Ctx) (j : Nat) : CommandElabM Term := do
  let p ← c.phT j
  let m ← c.modT j
  `((show Sparkle.Compiler.MachMemory.memChild? $p = some $m from by first | rfl | decide))

end Ctx

/-- The elimination of a hypothesis `e : A₀ ∨ A₁ ∨ … ∨ Aₙ₋₁` (right nested):
branch `i` is `branches[i]`, in which the hypothesis `Aᵢ` is named `h`. One
branch: `e` itself is the hypothesis `A₀`. -/
partial def orElim (h : Ident) (e : Term) (branches : List Term) : CommandElabM Term := do
  match branches with
  | [] => throwError "orElim: no branch"
  | [b] => `((have $h := $e; $b))
  | [b0, b1] => `((($e).elim (fun $h => $b0) (fun $h => $b1)))
  | b0 :: rest =>
    let hT : Term := ⟨h.raw⟩
    let inner ← orElim h hT rest
    `((($e).elim (fun $h => $b0) (fun $h => $inner)))

/-- A theorem decided on the reflected data. -/
def decided (c : Ctx) (s : String) (stmt : Term) : CommandElabM Unit :=
  emit c (c.lemName s) fun tn => `(command|
    set_option maxHeartbeats 4000000 in
    theorem $tn : $stmt := by
      first | decide | decide +kernel)

/-- `f.noPortsMem_entry` and the data conditions, then `f.noPortsMem_data`. -/
def dataTheorems (c : Ctx) : CommandElabM Unit := do
  let d := c.data
  let nD := Syntax.mkNumLit (toString c.s.nDecl)
  let aw := Syntax.mkNumLit (toString c.s.aw)
  let dw := Syntax.mkNumLit (toString c.s.dw)
  let n := c.s.mems.length
  -- every call entry is one of the placeholders
  let mut alts : List Term := []
  for j in [0:n] do
    let p ← c.phT j
    alts := alts ++ [← `((($d).shape.insts[k]).1 = $p)]
  let mut disj? : Option Term := Option.none
  for a in alts.reverse do
    match disj? with
    | Option.none => disj? := Option.some a
    | Option.some r => disj? := Option.some (← `($a ∨ $r))
  let disj ← match disj? with
    | Option.some t => pure t
    | Option.none => throwError "{c.f}: no memory placeholder"
  decided c "entry" (← `(∀ (k : Nat) (hk : k < ($d).shape.insts.length), $disj))
  decided c "calls" (← `(($d).callsOk $nD = true))
  decided c "slots" (← `(($d).ss.length = ($d).shape.layout.slots.length))
  decided c "domB" (← `(∀ b ∈ ($d).shape.binders.drop $nD, b.2 ≠ .domain))
  if c.oldData then
    decided c "outTy" (← `(∀ o ∈ ($d).shape.layout.outs, o.ty.bitWidth = o.width))
  decided c "callWidths" (← `(Tools.ShippingCallWidths.callWidthsOk $d $nD
    (fun _ => Tools.ShippingMemKid.memOuts $dw) = true))
  decided c "callArgs" (← `(Tools.ShippingPortsMatchRaw.callArgsOk $d $nD
    (fun _ => Tools.ShippingMemKid.memIns $aw $dw) = true))
  decided c "outChars" (← `(∀ o ∈ ($d).shape.layout.outs, ∀ c ∈ o.name.toList,
    Sparkle.IR.NameHints.charOk c = true))
  if c.oldData then
    decided c "outScalar" (← `(∀ o ∈ ($d).shape.layout.outs,
      Tools.ShippingTextTyped.scalarTy o.ty = true))
  -- `mem`: every entry's placeholder has the built module of its kind
  let h := mkIdent `h
  let mut branches : List Term := []
  for j in [0:n] do
    let cbT ← Ctx.boolT (c.s.mems[j]!).2.1
    let isMem ← c.isMemT j
    branches := branches ++ [← `(Exists.intro $cbT
      ((congrArg Sparkle.Compiler.MachMemory.memChild? $h).trans $isMem))]
  let memPf ← orElim h (← `($(c.lem "entry") k hk)) branches
  unless c.oldData do
    -- par/r-2: no `outTy` / `outScalar`; the run theorems take them from the reader
    emit c (c.lemName "dataR") fun tn => `(command|
      set_option maxHeartbeats 4000000 in
      theorem $tn : Tools.ShippingReaderOutsMemOnly.MemOnlyDataR $d $nD $aw $dw :=
        Tools.ShippingReaderOutsMemOnly.MemOnlyDataR.mk
          $(nm c.f "machine_ok") $(nm c.f "machine_body")
          $(c.lem "calls") $(c.lem "slots") $(c.lem "domB")
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (fun k hk => $memPf)
          $(c.lem "callWidths") $(c.lem "callArgs")
          (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean ($(c.lem "outChars") o ho)))
    return
  emit c (c.lemName "data") fun tn => `(command|
    set_option maxHeartbeats 4000000 in
    theorem $tn : Tools.ShippingMemOnly.MemOnlyData $d $nD $aw $dw :=
      Tools.ShippingMemOnly.MemOnlyData.mk
        $(nm c.f "machine_ok") $(nm c.f "machine_body")
        $(c.lem "calls") $(c.lem "slots") $(c.lem "domB")
        (fun h0 => absurd (congrArg List.length h0) (by decide))
        (fun h0 => absurd (congrArg List.length h0) (by decide))
        (fun h0 => absurd (congrArg List.length h0) (by decide))
        $(c.lem "outTy")
        (fun k hk => $memPf)
        $(c.lem "callWidths") $(c.lem "callArgs")
        (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean ($(c.lem "outChars") o ho))
        $(c.lem "outScalar"))

/-- One of the four run theorems of `f`: binders `hcore hpost entry closes`,
then `hg` (if `gate`), then `hB`. -/
def runTheorem (c : Ctx) (s : String) (gate : Bool) (concl proof : Term) : CommandElabM Unit := do
  let d := c.data
  let fq : Term := quote c.f
  let mut tail : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  if gate then
    tail := tail.push (← `(bracketedBinder| (hg : Sparkle.IR.RefineCheck.hierGate b = true)))
  tail := tail.push (← `(bracketedBinder| (hB : Tools.ShippingChildInv.ChildBnd mref cref w)))
  emit c (c.lemName s) fun tn => `(command|
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

/-- `f.noPortsMem_runFacts / _outsG0 / _kidsMemG / _designP0`. -/
def runTheorems (c : Ctx) : CommandElabM Unit := do
  -- the SAME four statements in the two paths; only the proofs differ
  let dat := if c.oldData then c.lem "data" else c.lem "dataR"
  let pRun : Term ← if c.oldData then
      `(Tools.ShippingMemOnly.memOnly_runFacts $dat hB hcore hpost entry closes)
    else
      `(Tools.ShippingReaderOutsMemOnly.memOnly_runFacts_of_reader $dat hB hcore hpost entry closes)
  let pOuts : Term ← if c.oldData then
      `(Tools.ShippingMemOnly.memOnly_outsCheck $dat hB hcore hpost entry closes hg)
    else
      `(Tools.ShippingReaderOutsMemOnly.memOnly_outsCheck_of_reader $dat hB hcore hpost entry closes hg)
  let pKids : Term ← if c.oldData then
      `(Tools.ShippingMemOnly.memOnly_kidsMem $dat hB hcore hpost entry closes)
    else
      `(Tools.ShippingReaderOutsMemOnly.memOnly_kidsMem_of_reader $dat hB hcore hpost entry closes)
  let pDesign : Term ← if c.oldData then
      `(Tools.ShippingMemOnly.memOnly_designCheck $dat hB hcore hpost entry closes)
    else
      `(Tools.ShippingReaderOutsMemOnly.memOnly_designCheck_of_reader $dat hB hcore hpost entry closes)
  runTheorem c "runFacts" false
    (← `(Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b))
    pRun
  runTheorem c "outsG0" true
    (← `(Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true))
    pOuts
  runTheorem c "kidsMemG" false
    (← `(Tools.ShippingMachineShipsHier.kidsMem (Tools.ShippingMachineLinked.childMap D.modules)
      b.body = true))
    pKids
  runTheorem c "designP0" false
    (← `(Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true))
    pDesign

/-- The data conditions of the closing, `f.noPortsMem_closeData`, and
`f.noPortsMem_closes : MachineClosesAt f` (NO premise) — by the general
theorem without name hypotheses; with `c.oldNames`, by the per-declaration
name lemmas (the previous path). The statement of `f.noPortsMem_closes` is
the same text in both. -/
def closingTheorems (c : Ctx) : CommandElabM Unit := do
  let d := c.data
  let fq : Term := quote c.f
  let n := c.s.mems.length
  decided c "alias" (← `(($d).letsAliasOk = true))
  decided c "argsN" (← `(∀ (k : Nat) (hk : k < ($d).shape.insts.length),
    (($d).shape.insts[k]).2.1.length = 4))
  decided c "field" (← `(∀ (k : Nat), k < ($d).shape.insts.length →
    ($d).shape.instFields.getD k "" = "out"))
  decided c "argsNd" (← `(∀ (k : Nat) (hk : k < ($d).shape.insts.length) (k' : Nat)
    (hk' : k' < ($d).shape.insts.length),
    (($d).shape.insts[k]).1 = (($d).shape.insts[k']).1 →
    (($d).shape.insts[k]).2.1 = (($d).shape.insts[k']).2.1 → k = k'))
  decided c "outHead" (← `(∀ o ∈ ($d).shape.layout.outs, o.name.toList.head? ≠ some 'i'))
  -- origin dispatch (patched compiler): every entry's name says what its origin builds
  decided c "agree" (← `(∀ x ∈ ($d).shape.instTagged,
    Tools.ShippingInstTagged.tagAgrees x.1 x.2 = true))
  emit c (c.lemName "closeData") fun tn => `(command|
    theorem $tn : Tools.ShippingMemOnlyCloses.MemOnlyCloseData $d :=
      Tools.ShippingMemOnlyCloses.MemOnlyCloseData.mk $(c.lem "alias") $(c.lem "argsN")
        $(c.lem "field") $(c.lem "argsNd") $(c.lem "outHead") $(c.lem "agree"))
  unless c.oldData do
    -- par/r-2: over `MemOnlyDataR`, no name lemma (the statement is the same text)
    emit c (c.lemName "closes") fun tn => `(command|
      set_option maxHeartbeats 4000000 in
      theorem $tn {mctx : Lean.Meta.Context}
          {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
          {cref : ST.Ref IO.RealWorld Lean.Core.State} :
          Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref $fq ($d).shape :=
        Tools.ShippingReaderMemOnlyCloses.machineClosesAt_of_memOnlyDataR_names
          $(c.lem "dataR") $(c.lem "closeData"))
    return
  unless c.oldNames do
    -- no name lemma: `hsep` / `hparent` follow from `MemOnlyData.mem`
    -- (`ofMem_injective`, `ofDecl_ne_ofMem`)
    emit c (c.lemName "closes") fun tn => `(command|
      set_option maxHeartbeats 4000000 in
      theorem $tn {mctx : Lean.Meta.Context}
          {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
          {cref : ST.Ref IO.RealWorld Lean.Core.State} :
          Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref $fq ($d).shape :=
        Tools.ShippingMemOnlyNames.machineClosesAt_of_memOnlyData_names
          $(c.lem "data") $(c.lem "closeData"))
    return
  -- THE PREVIOUS PATH (`…_oldnames`)
  -- `f`'s module name is not a memory module's name (`name_not_mem`)
  for j in [0:n] do
    let m ← c.modT j
    emit c (c.lemName s!"notin{j}") fun tn => `(command|
      set_option maxHeartbeats 4000000 in
      theorem $tn : (Sparkle.IR.ModuleName.ofDecl ($fq : Lean.Name)) ∉ [($m).1.name] :=
        (by name_not_mem))
  let entry := c.lem "entry"
  -- `hsep` / `hparent`: ONE placeholder — `sep_of_one` / `parent_of_one` (the
  -- hand `memCounter`); several — the lemmas `sep` / `parent` below (the hand `mixedMems`)
  let isMem0 ← c.isMemT 0
  let notin0 := c.lem "notin0"
  let mut sepT : Term ← `(Tools.ShippingMemOnlyCloses.sep_of_one $entry)
  let mut parentT : Term ←
    `(Tools.ShippingMemOnlyCloses.parent_of_one $entry $isMem0 $notin0)
  if n ≥ 2 then
    -- the module name of an entry of placeholder `j`
    for j in [0:n] do
      let p ← c.phT j
      let m ← c.modT j
      let isMem ← c.isMemT j
      emit c (c.lemName s!"at{j}") fun tn => `(command|
        theorem $tn (k : Nat) (hk : k < ($d).shape.insts.length)
            (h : (($d).shape.insts[k]).1 = $p) :
            Tools.ShippingMemOnlyCloses.memNameAt $d k = ($m).1.name :=
          Tools.ShippingMemOnlyCloses.memNameAt_eq $d hk
            ((congrArg Sparkle.Compiler.MachMemory.memChild? h).trans $isMem))
    -- two different placeholders have two different module names
    for i in [0:n] do
      for j in [0:n] do
        if i < j then
          let mi ← c.modT i
          let mj ← c.modT j
          let stmt ← `(($mi).1.name ≠ ($mj).1.name)
          decided c s!"namesNe{i}_{j}" stmt
    -- two entries with one module name have one callee
    let hI := mkIdent `h
    let hJ := mkIdent `h'
    let mut outer : List Term := []
    for i in [0:n] do
      let mut inner : List Term := []
      for j in [0:n] do
        let atI := c.lem s!"at{i}"
        let atJ := c.lem s!"at{j}"
        if i == j then
          inner := inner ++ [← `(($hI).trans ($hJ).symm)]
        else if i < j then
          let neL := c.lem s!"namesNe{i}_{j}"
          inner := inner ++ [← `(absurd
            (($atI k hk $hI).symm.trans (he.trans ($atJ k' hk' $hJ))) $neL)]
        else
          let neL := c.lem s!"namesNe{j}_{i}"
          inner := inner ++ [← `(absurd
            (($atJ k' hk' $hJ).symm.trans (he.symm.trans ($atI k hk $hI))) $neL)]
      let eJ ← `($entry k' hk')
      outer := outer ++ [← orElim hJ eJ inner]
    let eI ← `($entry k hk)
    let sepPf ← orElim hI eI outer
    emit c (c.lemName "sep") fun tn => `(command|
      set_option maxHeartbeats 4000000 in
      theorem $tn : ∀ (k : Nat) (hk : k < ($d).shape.insts.length) (k' : Nat)
          (hk' : k' < ($d).shape.insts.length),
          Tools.ShippingMemOnlyCloses.memNameAt $d k =
            Tools.ShippingMemOnlyCloses.memNameAt $d k' →
          (($d).shape.insts[k]).1 = (($d).shape.insts[k']).1 := by
        intro k hk k' hk' he
        exact $sepPf)
    -- no memory module is named as the parent
    let mut pbr : List Term := []
    for j in [0:n] do
      let notinJ := c.lem s!"notin{j}"
      let atJ := c.lem s!"at{j}"
      pbr := pbr ++ [← `($notinJ
        (List.mem_singleton.mpr ((($atJ k hk $hI).symm.trans e).symm)))]
    let parentPf ← orElim hI eI pbr
    emit c (c.lemName "parent") fun tn => `(command|
      set_option maxHeartbeats 4000000 in
      theorem $tn : ∀ (k : Nat), k < ($d).shape.insts.length →
          Tools.ShippingMemOnlyCloses.memNameAt $d k ≠ (Sparkle.IR.ModuleName.ofDecl ($fq : Lean.Name)) := by
        intro k hk e
        exact $parentPf)
    sepT := ⟨(c.lem "sep").raw⟩
    parentT := ⟨(c.lem "parent").raw⟩
  emit c (c.lemName "closes") fun tn => `(command|
    set_option maxHeartbeats 4000000 in
    theorem $tn {mctx : Lean.Meta.Context}
        {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
        {cref : ST.Ref IO.RealWorld Lean.Core.State} :
        Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref $fq ($d).shape :=
      Tools.ShippingMemOnlyCloses.machineClosesAt_of_memOnlyData
        $(c.lem "data") $(c.lem "closeData") $sepT $parentT)

/-! ## The endpoint (the hand generators, restated) -/

/-- The checker constants an endpoint of a memory parent must not mention
(`Tests.Compiler.NoPortsMemOnly.forbiddenMem`, restated). -/
def forbiddenMem : List Name :=
  Tools.ShippingNoPortsCommand.forbidden ++
    [``Tools.ShippingMachineShipsHier.kidsMixed, ``Tools.ShippingMachineShipsHier.kidsMem,
     ``Tools.ShippingMachineShipsHier.kidsMasked, ``Tools.ShippingHierPremisesBase.hierCheck]

/-- The head `machine_design_noPorts` at `n = 0` on the arguments `a` of a
memory-route `machine_ships_hier`, with the boundary `bndNew`, the closing
predicate `C`, the wired endpoint `soundL` and the composed theorem
`composed`, at the run binders `xs'`; the four run hypotheses discharged by
`facts` / `outs` / `mem` / `design` (`Tests.Compiler.NoPortsMemOnly.finishM0`,
restated). -/
def finish0 (f : Name) (a : Array Lean.Expr) (bndNew C soundL composed : Lean.Expr)
    (xs' : Array Lean.Expr) (closesAt : Lean.Expr) (facts outs mem design : Name) :
    MetaM Lean.Expr := do
  let args : Array (Option Lean.Expr) :=
    #[some (mkNatLit 0), some a[3]!, some bndNew, some C, some a[5]!, some a[6]!,
      some a[7]!, some a[8]!, some a[9]!, some a[10]!,
      some a[11]!, some a[12]!, some a[13]!, some a[14]!, some a[15]!, some a[16]!,
      some a[17]!, some a[18]!, some a[19]!, some a[20]!,
      some soundL, some composed, some a[23]!] ++ xs'.map some
  let pre ← instantiateMVars
    (← mkAppOptM ``Tools.ShippingNoPorts.machine_design_noPorts args)
  if pre.hasMVar then throwError "{f}: the head's arguments were not all inferred"
  -- the run's facts: zs = raw D w1 hcore hpost hBnd ; xs'[9] = entry
  let .forallE _ TF _ _ ← whnfR (← inferType pre)
    | throwError "{f}: the head's run-facts hypothesis is not where it is expected"
  let hFacts ← forallTelescope TF fun zs goal => do
    unless zs.size == 6 do throwError "{f}: the run-facts hypothesis has {zs.size} binders"
    let p ← mkAppM facts #[zs[3]!, zs[4]!, xs'[9]!, closesAt]
    mkLambdaFVars zs (← dischargeWith facts p zs[5]! goal #[])
  let pre := mkApp pre hFacts
  -- the output check under the gate: zs = raw D w1 hcore hpost hg hBnd
  let .forallE _ TO _ _ ← whnfR (← inferType pre)
    | throwError "{f}: the head's output-check hypothesis is not where it is expected"
  let hOuts ← forallTelescope TO fun zs goal => do
    unless zs.size == 7 do throwError "{f}: the output-check hypothesis has {zs.size} binders"
    let p ← mkAppM outs #[zs[3]!, zs[4]!, xs'[9]!, closesAt, zs[5]!]
    mkLambdaFVars zs (← dischargeWith outs p zs[6]! goal #[])
  let pre := mkApp pre hOuts
  -- the children's bound: zs = raw D w1 hcore hpost hBnd (cut at 6 binders)
  let .forallE _ TM _ _ ← whnfR (← inferType pre)
    | throwError "{f}: the head's children-bound hypothesis is not where it is expected"
  let hMem ← forallBoundedTelescope TM (some 6) fun zs goal => do
    unless zs.size == 6 do throwError "{f}: the children-bound hypothesis has {zs.size} binders"
    let p ← mkAppM mem #[zs[3]!, zs[4]!, xs'[9]!, closesAt]
    mkLambdaFVars zs (← dischargeWith mem p zs[5]! goal #[])
  let pre := mkApp pre hMem
  -- `designCheck` with no check premise: zs = raw D w1 hcore hpost hBnd (cut at 6)
  let .forallE _ TD _ _ ← whnfR (← inferType pre)
    | throwError "{f}: the head's design-check hypothesis is not where it is expected"
  let hDesign ← forallBoundedTelescope TD (some 6) fun zs goal => do
    unless zs.size == 6 do throwError "{f}: the design-check hypothesis has {zs.size} binders"
    let p ← mkAppM design #[zs[3]!, zs[4]!, xs'[9]!, closesAt]
    mkLambdaFVars zs (← dischargeWith design p zs[5]! goal #[])
  mkLambdaFVars xs' (mkApp pre hDesign)

/-- The statement and the proof of `f.machine_design_noPortsR0`, and whether
`f`'s endpoint is transported (`Tests.Compiler.NoPortsMemWithMemory.generateT0`,
restated; nothing is added to the environment): the head
`machine_design_noPorts` at `n = 0` on the arguments of `f.machine_ships_hier`,
closing predicate `MachineClosesAt`, boundary `ChildBnd` in place of the old
`True`; the wired endpoint is the `RA` twin of the endpoint's head on its
UNTRANSPORTED arguments; the composed theorem is `machine_linkedT_mem` on it
with the data arguments of the existing `f.machine_composedT` — read under
its `Eq.mpr` when the endpoint is transported — moved to the declaration's
source by `composedG_src` at the endpoint's own equation. -/
def endpointTerm (f : Name) (facts outs mem design : Name) :
    MetaM (Lean.Expr × Lean.Expr × Bool) := do
  let ships := f ++ `machine_ships_hier
  let name := f ++ `machine_design_noPortsR0
  let env ← getEnv
  let some (.thmInfo ti) := env.find? ships
    | throwError "{ships}: not a theorem (run #machine_ships_hier first)"
  let v := ti.value
  unless v.isAppOf ``Tools.ShippingMachineShipsHier.machine_ships_hier do
    throwError "{ships}: not built from machine_ships_hier"
  let a := v.getAppArgs
  unless a.size == 24 do
    throwError "{ships}: {a.size} arguments of machine_ships_hier, expected 24"
  unless a[3]!.isConstOf ``Tools.ShippingMachineShipsHier.ResetM do
    throwError "{ships}: its reset is{indentExpr a[3]!}\nnot ResetM — not the memory route"
  unless (a[5]!.find? (·.isConstOf ``Tools.ShippingMachineShipsHier.kidsMem)).isSome do
    throwError "{ships}: its child bound is{indentExpr a[5]!}\nnot kidsMem — not the memory route"
  -- the new boundary, over the old boundary's own binders; the old one must be `True`
  let bndNew ← lambdaTelescope a[4]! fun bs oldB => do
    unless bs.size == 7 do
      throwError "{ships}: its boundary has {bs.size} binders, expected 7:{indentExpr a[4]!}"
    unless oldB.isConstOf ``True do
      throwError "{ships}: the old boundary is{indentExpr oldB}\nnot True (this generator replaces True by ChildBnd and nothing else)"
    mkLambdaFVars bs (← mkAppM ``Tools.ShippingChildInv.ChildBnd #[bs[1]!, bs[3]!, bs[4]!])
  -- the endpoint: its wired twin's head, its UNTRANSPORTED arguments, its transport
  let (headL, eargs, back?) ← Tools.ShippingMachineSeqCommand.endpointParts f
  let headA := headL.appendAfter "RA"
  unless env.contains headA do throwError "{f}: no head {headA}"
  let pLA := mkAppN (mkConst headA) eargs
  -- the data arguments of the existing composed theorem, under its transport
  let some (.thmInfo ct) := env.find? (f ++ `machine_composedT)
    | throwError "{f}: no machine_composedT"
  let mut cv := ct.value
  if cv.isAppOfArity ``Eq.mpr 4 then
    if back?.isNone then
      throwError "{f}.machine_composedT is transported, {f}.machine_sound is not"
    cv := cv.getAppArgs[3]!
  else if back?.isSome then
    throwError "{f}.machine_sound is transported, {f}.machine_composedT is not an Eq.mpr on 4 arguments"
  let rest ← lambdaTelescope cv fun ys body => do
    unless ys.size == 11 do
      throwError "{f}.machine_composedT: {ys.size} binders under its transport, expected 11"
    unless body.isAppOfArity ``Tools.ShippingMachineMemLinked.machine_linkedT_mem 21 do
      throwError "{f}.machine_composedT: not machine_linkedT_mem on 21 arguments"
    let rest := body.getAppArgs.extract 11 21
    for r in rest do
      if r.hasAnyFVar (fun id => ys.any (·.fvarId! == id)) then
        throwError "{f}.machine_composedT: a data argument depends on the run"
    pure rest
  let value ← forallTelescope (← inferType (mkConst ships)) fun xs _ => do
    unless xs.size == 11 do throwError "{ships}: {xs.size} binders, expected 11"
    let cT ← instantiateMVars (← inferType xs[10]!)
    unless cT.isAppOfArity ``Tools.ShippingMachineEntry.MachineCloses 6 do
      throwError "{ships}: its closing premise is{indentExpr cT}\nnot MachineCloses"
    let atT := mkAppN (mkConst ``Tools.ShippingChildInv.MachineClosesAt) cT.getAppArgs
    let C ← mkLambdaFVars #[xs[0]!, xs[1]!, xs[2]!, xs[3]!] atT
    -- the wired endpoint under `MachineClosesAt` and `ChildBnd` (the rewritten source)
    let soundL ← forallTelescope (← inferType pLA) fun zs _ => do
      unless zs.size == 12 do
        throwError "{f}: {headA} has {zs.size} binders after its data, expected 12"
      mkLambdaFVars zs
        (← mkAppM ``Tools.ShippingMachineTraceX.MachineTraceLBX.toLB #[mkAppN pLA zs])
    -- the composed theorem, moved to the declaration's source
    let composed ← forallTelescope (← inferType pLA) fun zs _ => do
      let hNew ← mkAppM ``Tools.ShippingMachineTraceX.MachineTraceLBX.toLB #[mkAppN pLA zs]
      let linked ← mkAppM ``Tools.ShippingMachineMemLinked.machine_linkedT_mem (#[hNew] ++ rest)
      let memF ← mkAppM ``Tools.ConeFold.memFree
        #[← mkAppM ``Sparkle.IR.AST.Module.body #[zs[6]!]]
      withLocalDeclD `hm memF fun hm => do
        let cg0 ← mkAppM ``Tools.ShippingMachineShipsHier.composedG_of_Tmem #[linked, hm]
        let cg ← (match back? with
          | Option.some p => mkAppM ``Tools.ShippingMemTransport.composedG_src #[cg0, p.1]
          | Option.none => pure cg0)
        mkLambdaFVars (zs.push hm) cg
    withLocalDeclD `closes atT fun cl =>
      finish0 f a bndNew C soundL composed (xs.pop.push cl) cl facts outs mem design
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  for c in forbiddenMem do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{name}: REFUSED, the statement still mentions {c}"
  if (type.find? (·.isConstOf ``Tools.ShippingMachineEntry.MachineCloses)).isSome then
    throwError "{name}: REFUSED, the statement asks the all-worlds MachineCloses"
  -- a transported endpoint: the statement is about the declaration's source
  match back? with
  | Option.some p =>
    if (type.find? (· == p.2)).isSome then
      throwError "{name}: REFUSED, the statement reads the rewritten source{indentExpr p.2}"
  | Option.none => pure ()
  return (type, value, back?.isSome)

/-- The antecedents of an endpoint body `∃ w…, P ∧ (A₁ → … → C)`: the `Aᵢ`,
printed, each with whether the goal-gap classifier allows it
(`Tests.Compiler.NoPortsTest.innerAntecedents`, restated). -/
partial def innerAntecedents (ty : Lean.Expr) : MetaM (Array (String × Bool)) := do
  if ty.isAppOfArity ``Exists 2 then
    let α := ty.getArg! 0
    let p := ty.getArg! 1
    let wn := if p.isLambda then p.bindingName! else `w
    withLocalDeclD wn α fun w => innerAntecedents (mkApp p w).headBeta
  else if ty.isAppOfArity ``And 2 then
    let mut R := ty.getArg! 1
    let mut out : Array (String × Bool) := #[]
    while (← Tools.ShippingFinalGoalCommand.isPropArrow R) do
      let A := R.bindingDomain!
      out := out.push (toString (← ppExpr A), Tools.ShippingFinalGoalCommand.allowed A)
      R := R.bindingBody!
    return out
  else
    throwError "expected ∃ … , P ∧ (…), found{indentExpr ty}"

/-- The complete premise list of the endpoint `decl`: one line per binder and
per antecedent under its existentials; and the NOT ALLOWED lines
(`Tests.Compiler.NoPortsTest.premiseLines`, restated with another prefix). -/
def premiseLines (decl : Name) : MetaM (Array String × Array String) := do
  let ci ← getConstInfo decl
  forallTelescope ci.type fun xs body => do
    let mut lines : Array String := #[]
    let mut bad : Array String := #[]
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      let xn ← x.fvarId!.getUserName
      let pp := toString (← ppExpr t)
      if ← isProp t then
        if Tools.ShippingFinalGoalCommand.allowed t then
          lines := lines.push s!"NOPORTS MEM PREMISE {decl}: ALLOWED     binder {xn} : {pp}"
        else
          let l := s!"NOPORTS MEM PREMISE {decl}: NOT ALLOWED binder {xn} : {pp}"
          lines := lines.push l
          bad := bad.push l
      else
        lines := lines.push s!"NOPORTS MEM PREMISE {decl}: data        binder {xn} : {pp}"
    let inner ← innerAntecedents body
    for (s, ok) in inner do
      if ok then
        lines := lines.push s!"NOPORTS MEM PREMISE {decl}: ALLOWED     antecedent under the existentials : {s}"
      else
        let l := s!"NOPORTS MEM PREMISE {decl}: NOT ALLOWED antecedent under the existentials : {s}"
        lines := lines.push l
        bad := bad.push l
    return (lines, bad)

/-- The generation proper (after the scope): the lemmas, the two endpoints,
the premise lines. Returns the log lines, the premise lines and whether the
open endpoint was rebuilt (it existed). -/
def core (f : Name) (s : Scope) (oldNames : Bool := false) (oldData : Bool := false) :
    CommandElabM (Array String × Array String × Bool) := do
  let log ← IO.mkRef (#[] : Array String)
  -- the previous closing path is a path of the previous DATA (`MemOnlyData`)
  let c : Ctx := { f, s, log, oldNames, oldData := oldData || oldNames }
  if oldNames then
    log.modify fun a => a.push "OLDNAMES: the previous closing path (machineClosesAt_of_memOnlyData with per-declaration name lemmas)"
  if c.oldData then
    log.modify fun a => a.push "OLDDATA: the previous data path (outTy / outScalar decided, MemOnlyData, memOnly_*)"
  else
    log.modify fun a => a.push "DATA FROM THE READER: no outTy / outScalar decided; MemOnlyDataR, memOnly_*_of_reader (outTy_of_core / outScalar_of_core at hcore, entry), machineClosesAt_of_memOnlyDataR_names"
  dataTheorems c
  runTheorems c
  let name := f ++ `machine_design_noPortsR0
  let existed := (← getEnv).contains name
  let (openC, line1, transported) ← liftTermElabM <|
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun k => { k with maxRecDepth := 1000000, maxHeartbeats := 0 }) do
        let (type, value, tr) ← endpointTerm f (c.lemName "runFacts") (c.lemName "outsG0")
          (c.lemName "kidsMemG") (c.lemName "designP0")
        let (openC, line) ← addOrCompare name type value
        pure (openC, line, tr)
  log.modify fun a => a.push line1
  closingTheorems c
  let cl := c.lemName "closes"
  -- the closing theorem: NO proposition premise
  let nPrem ← liftTermElabM do
    forallTelescope (← getConstInfo cl).type fun xs _ => do
      let mut n : Nat := 0
      for x in xs do
        if ← isProp (← inferType x) then n := n + 1
      pure n
  unless nPrem == 0 do
    throwError "{cl}: {nPrem} proposition premise(s), expected none"
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
  log.modify fun a => a.push (line2 ++ s!" (closing: {cl}, no premise)")
  -- the premise lines: exactly one NOT ALLOWED in the open form, none in the closed one
  let (linesO, badO) ← liftTermElabM (premiseLines openC)
  let (linesC, badC) ← liftTermElabM (premiseLines closedC)
  unless badO.size == 1 do
    throwError "{openC}: {badO.size} premises NOT ALLOWED, expected exactly 1 (MachineClosesAt {f}):\n{String.intercalate "\n" badO.toList}"
  unless badC.isEmpty do
    throwError "{closedC}: {badC.size} premise(s) NOT ALLOWED, expected none:\n{String.intercalate "\n" badC.toList}"
  unless linesC.size + 1 == linesO.size do
    throwError "{closedC}: {linesC.size} premises listed against {linesO.size} of {openC}, expected one fewer"
  let kinds := s.mems.map fun (p, cb, aw, dw) =>
    let kindS : String := if cb then "combinational" else "synchronous"
    s!"{p} ({kindS} read, aw {aw}, dw {dw})"
  let trS : String :=
    if transported then
      "TRANSPORTED (composedG_src at its own equation; the statement reads the declaration's source)"
    else "not transported"
  let summary := s!"memory-only parent, nDecl {s.nDecl}, {s.slots} register slot(s), call entries {s.calls}, of the placeholder(s) {kinds}; endpoint {trS}. {name}: {linesO.size} premises listed, 1 NOT ALLOWED (MachineClosesAt {f}); {closedN}: {linesC.size} premises listed, 0 NOT ALLOWED (the run, MachineDefines {f}, and ChildBnd of the run's start world under the existentials). No statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN, hierCheck, kidsMixed, kidsMem, kidsMasked or MachineCloses. The all-worlds endpoint {f}.machine_design_noPorts0 is NOT generated (MachineCloses cannot be discharged for a shape with calls). SCOPE: one declaration, depth 0, data conditions decided per declaration (conditions, not reductions), compiler guards with fallback, DesignSV of the module list — not the SV string, not #sim; the run, the reflection of {f} and ChildBnd remain premises"
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
    s!"NOPORTS MEM {f}: GENERATED\n{String.intercalate "\n" ls.toList}\n{String.intercalate "\n" ps.toList}"
  | Outcome.rebuilt ls ps =>
    s!"NOPORTS MEM {f}: REBUILT (compare path)\n{String.intercalate "\n" ls.toList}\n{String.intercalate "\n" ps.toList}"
  | Outcome.refused r => s!"NOPORTS MEM {f}: REFUSED ({r})"
  | Outcome.failed r => s!"NOPORTS MEM {f}: FAILED ({r})"

/-- The generator on `f`: never throws; on REFUSED / FAILED the environment
and the message log are put back. -/
def noPortsMem (f : Name) (oldNames : Bool := false) (oldData : Bool := false) :
    CommandElabM Outcome := do
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
      let (ls, ps, existed) ← core f sc oldNames oldData
      if existed then return Outcome.rebuilt ls ps else return Outcome.generated ls ps
    catch ex =>
      let msg ← ex.toMessageData.toString
      restore
      return Outcome.failed msg

/-- `#machine_no_ports_mem f`: an error where it is refused or fails. -/
elab "#machine_no_ports_mem " d:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← noPortsMem f
  match o with
  | Outcome.refused _ => throwError "{line f o}"
  | Outcome.failed _ => throwError "{line f o}"
  | _ => logInfo m!"{line f o}"

/-- `#machine_no_ports_mem_try f "EXPECTED"`: the outcome is LOGGED
(`NOPORTS MEM f: GENERATED | REBUILT | REFUSED (reason) | FAILED (condition)`),
and it is an error when its class is not the expected one. A refused or
failed declaration leaves nothing in the environment. -/
elab "#machine_no_ports_mem_try " d:ident ppSpace e:str : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← noPortsMem f
  logInfo m!"{line f o}"
  unless o.tag == e.getString do
    throwError "NOPORTS MEM {f}: expected {e.getString}, found {o.tag}"

/-- `#machine_no_ports_mem_oldnames f`: the generator with the PREVIOUS
closing path (per-declaration name lemmas). Kept for one round, to compare
the two paths on one tree. -/
elab "#machine_no_ports_mem_oldnames " d:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← noPortsMem f (oldNames := true)
  match o with
  | Outcome.refused _ => throwError "{line f o}"
  | Outcome.failed _ => throwError "{line f o}"
  | _ => logInfo m!"{line f o}"

/-- `#machine_no_ports_mem_oldnames_try f "EXPECTED"`: as
`#machine_no_ports_mem_try`, on the previous closing path. -/
elab "#machine_no_ports_mem_oldnames_try " d:ident ppSpace e:str : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← noPortsMem f (oldNames := true)
  logInfo m!"{line f o}"
  unless o.tag == e.getString do
    throwError "NOPORTS MEM {f}: expected {e.getString}, found {o.tag}"

/-- `#machine_no_ports_mem_olddata f`: the generator with the PREVIOUS data
path (`outTy` / `outScalar` decided, `MemOnlyData`, `memOnly_*`; the closing
`machineClosesAt_of_memOnlyData_names`). Kept to compare the two paths on
one tree (par/r-2). -/
elab "#machine_no_ports_mem_olddata " d:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← noPortsMem f (oldData := true)
  match o with
  | Outcome.refused _ => throwError "{line f o}"
  | Outcome.failed _ => throwError "{line f o}"
  | _ => logInfo m!"{line f o}"

/-- `#machine_no_ports_mem_olddata_try f "EXPECTED"`: as
`#machine_no_ports_mem_try`, on the previous data path. -/
elab "#machine_no_ports_mem_olddata_try " d:ident ppSpace e:str : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← noPortsMem f (oldData := true)
  logInfo m!"{line f o}"
  unless o.tag == e.getString do
    throwError "NOPORTS MEM {f}: expected {e.getString}, found {o.tag}"

end Tools.ShippingNoPortsMemCommand
