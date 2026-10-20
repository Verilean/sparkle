import Tests.AllTests
import Tools.ShippingMachineCommand

/-! # A digest of the machine reader's output and of the endpoints' statements, to DIFF across a compiler change

WRITTEN, NOT BUILT (branch `fix/projchain-total`,
`docs/parallel/L-projchain-switch.md`). TARGET-ONLY: not in `Tests.AllTests`
(it imports it). A MEASUREMENT by compiled code; no theorem; it asserts
NOTHING and never throws. It uses only names that exist at the base commit
`80745d94`, so it elaborates unchanged on poc and on a candidate tree.

## What it is for

The "reflection-premise audit" of a change inside the reader (here: the
switch-over of `MachRawSurface.projChain`): the change must not alter what
the reader returns for any declaration, nor any endpoint's statement. Run
this file on BOTH trees and `diff` the `READERDIGEST` lines.

    lake build Tests.Compiler.ReaderDigestTest 2>&1 | grep '^READERDIGEST' | grep -v ' START ' | sort -u > digest.<tree>.txt
    diff digest.poc.txt digest.candidate.txt

(Each line is written to standard error and logged as a message; `sort -u`
keeps one copy. Through the cgroup runner as usual.)

## What is recorded

"Holders" are the declarations `f` with a constant `f.machineData` in the
environment (a `#machine_endpoint f`, or a gate-route child's data).

* `READERDIGEST SHAPE f: …` — for every holder, and for every definition
  under `Sparkle`, `Tests`, `IP`, `Examples`, `Tools` whose value uses
  `runCircuitH` and a pair-destructuring matcher (the raw surface, the only
  declarations that reach `projChain`), the reader is RUN AGAIN
  (`Tools.ShippingMachineCommand.readMachine`, the generator's own entry to
  `machineShape?`) and its result is digested: `Expr.hash` of the transition
  body, the binders, the layout (`Repr`), runs, loops, instances, fields. A
  declaration the reader refuses is logged with the refusal's text.
  `raw=T`: the declaration's value, or the entry constant the reader read,
  uses a pair-destructuring matcher (`prodMatcherArity?`).
* `READERDIGEST DATA f: …` — `Expr.hash` of the TYPE and of the VALUE of the
  generated constant `f.machineData` (read from the environment; reflected
  data is never evaluated by compiled code).
* `READERDIGEST STATEMENTS f: n=<count> hash=<h>` — one hash over the names
  and the TYPES of every constant below `f` (`f.machine_sound`,
  `f.machine_ships_wired`, …; a name whose last component starts with `_` or
  is a number is skipped). For a `raw=T` holder each is also listed:
  `READERDIGEST STATEMENT <name>: type=<h>`.
* `READERDIGEST CONST <name>: <type or absent>` — the local functions of
  `rawNode` and of `projChain` as constants (what a later proof about
  `rawNode` has to name). TWO of these lines are EXPECTED to differ across
  the switch: `projChain` (`opaque` before — a `partial def` — and `def`
  after) and `projChain.tail` (present before, absent after).
* `READERDIGEST TOTAL: …` — counts and one hash per kind.

## How to read a difference

`Expr.hash` equal is NOT a proof of equal terms (a hash can collide), and is
never to be reported as one; a differing hash IS a different term. So: a
diff that shows only the two `CONST` lines above is "no difference
measured"; any other differing line is a finding to look at before the
switch is taken.
The kernel-level evidence that statements did not move is elsewhere: every
endpoint is re-generated and kernel-checked when the suite is built on the
candidate tree, and the pinned statements (`DepthSwitchPinTest`,
`RanSplitStatementsTest`) are compared there.

PREDICTED (poc against the switch-over): identical lines except
`READERDIGEST CONST Sparkle.Compiler.MachRawSurface.projChain` (`opaque` on
poc, `def` on the candidate) and `…projChain.tail` (present on poc, absent
on the candidate). NOT predicted: the counts. -/
namespace Tests.Compiler.ReaderDigestTest
open Lean Meta

def bs (b : Bool) : String := if b then "T" else "F"

def emit (s : String) : MetaM Unit := do
  IO.eprintln s
  (← IO.getStderr).flush
  logInfo m!"{s}"

def mixAll (hs : List UInt64) : UInt64 := hs.foldl mixHash 7

def hashStr (s : String) : UInt64 := hash s

def nameHash (n : Name) : UInt64 := hash n

/-- The digest of one result of the reader. -/
structure ShapeDigest where
  body : UInt64
  nBinders : Nat
  binders : UInt64
  layout : UInt64
  slots : Nat
  lets : Nat
  runs : String
  loops : String
  nInsts : Nat
  insts : UInt64
  fields : UInt64

def shapeDigest (sh : Sparkle.Compiler.Elab.MachineShape) : ShapeDigest :=
  let kinds : String := toString (repr (sh.binders.map fun b => b.2))
  let instKinds : String := toString (repr (sh.insts.map fun i => i.2.2))
  let instArgs : String := toString (sh.insts.map fun i => i.2.1)
  { body := sh.body.hash
    nBinders := sh.binders.length
    binders := mixAll ((sh.binders.map fun b => nameHash b.1) ++ [hashStr kinds])
    layout := hashStr (toString (repr sh.layout))
    slots := sh.layout.slots.length
    lets := sh.layout.lets
    runs := toString sh.runs
    loops := toString sh.loops
    nInsts := sh.insts.length
    insts := mixAll ((sh.insts.map fun i => nameHash i.1) ++ [hashStr instArgs, hashStr instKinds])
    fields := hashStr (toString sh.instFields) }

def ShapeDigest.all (d : ShapeDigest) : UInt64 :=
  mixAll [d.body, d.binders, d.layout, hashStr d.runs, hashStr d.loops, d.insts, d.fields]

def ShapeDigest.line (d : ShapeDigest) : String :=
  s!"body={d.body} binders={d.nBinders}/{d.binders} layout={d.layout} slots={d.slots} lets={d.lets} runs={d.runs} loops={d.loops} insts={d.nInsts}/{d.insts} fields={d.fields} all={d.all}"

/-- The nearest proper prefix of a name that is a holder. -/
def holderOf (hs : NameSet) : Name → Option Name
  | .str p _ => if hs.contains p then some p else holderOf hs p
  | .num p _ => if hs.contains p then some p else holderOf hs p
  | .anonymous => none

/-- A name whose last component is generated bookkeeping (`_proof_1`, a
number): not a statement to pin. -/
def skipChild : Name → Bool
  | .str _ s => s.startsWith "_"
  | .num _ _ => true
  | .anonymous => true

def roots : List Name := [`Sparkle, `Tests, `IP, `Examples, `Tools]

def underRoots (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | some m => roots.contains m.getRoot
    | none => false
  | none => true

def sortNames (a : Array Name) : Array Name :=
  a.qsort fun x y => x.toString < y.toString

/-- The reader, run again on one declaration; never throws. The flag: the
gate route takes the declaration and it was read with `allowGate`. -/
def readAgain (f : Name) :
    MetaM (Except String (Tools.ShippingMachineCommand.Read × Bool)) := do
  let first : Except String Tools.ShippingMachineCommand.Read ←
    try
      let r ← Tools.ShippingMachineCommand.readMachine f
      pure (Except.ok r)
    catch ex =>
      let text ← ex.toMessageData.toString
      pure (Except.error (text.replace "\n" " | "))
  match first with
  | .ok r => return .ok (r, false)
  | .error text1 =>
    let second : Except String Tools.ShippingMachineCommand.Read ←
      try
        let r ← Tools.ShippingMachineCommand.readMachine f (allowGate := true)
        pure (Except.ok r)
      catch _ =>
        pure (Except.error text1)
    match second with
    | .ok r => return .ok (r, true)
    | .error text => return .error text

def usesPairMatcher (pm : Name → Option Nat) (e : Expr) : Bool :=
  e.getUsedConstants.any fun c => (pm c).isSome

def run : MetaM Unit := do
  let env ← getEnv
  let pm : Name → Option Nat := Sparkle.Compiler.MachRawSurface.prodMatcherArity? env
  emit "READERDIGEST START collect (holders of machineData; raw-surface definitions under the roots)"
  -- the holders
  let holderArr : Array Name := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
    match n with
    | .str p "machineData" => acc.push p
    | _ => acc
  let holders : NameSet := holderArr.foldl (fun s n => s.insert n) {}
  -- raw-surface definitions without data
  let rawArr : Array Name := env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    match ci with
    | .defnInfo d =>
      if holders.contains n || !underRoots env n then acc
      else
        let used := d.value.getUsedConstants
        if used.contains ``Sparkle.Core.runCircuitH && (used.any fun c => (pm c).isSome) then
          acc.push n
        else acc
    | _ => acc
  -- the constants below a holder
  let kids : Array (Name × Name × UInt64) :=
    env.constants.fold (init := (#[] : Array (Name × Name × UInt64))) fun acc n ci =>
      if skipChild n then acc
      else
        match holderOf holders n with
        | some h => acc.push (h, n, ci.type.hash)
        | none => acc
  emit s!"READERDIGEST COLLECT: holders={holderArr.size} raw definitions without data={rawArr.size} constants below a holder={kids.size}"
  -- the local functions, as constants
  for c in [``Sparkle.Compiler.MachRawSurface.projChain,
      ``Sparkle.Compiler.MachRawSurface.projChain ++ `tail,
      ``Sparkle.Compiler.MachRawSurface.rawNode,
      ``Sparkle.Compiler.MachRawSurface.rawNode ++ `peel,
      ``Sparkle.Compiler.MachRawSurface.rawNode ++ `build] do
    match env.find? c with
    | some ci =>
      let kind : String :=
        match ci with
        | .defnInfo _ => "def"
        | .opaqueInfo _ => "opaque"
        | .thmInfo _ => "theorem"
        | _ => "other"
      let ty ← ppExpr ci.type
      let flat : String := (toString ty).replace "\n" " "
      emit s!"READERDIGEST CONST {c}: {kind} : {flat}"
    | none => emit s!"READERDIGEST CONST {c}: absent"
  let mut nRead := 0
  let mut nRefused := 0
  let mut nRaw := 0
  let mut hShapes : UInt64 := 7
  let mut hData : UInt64 := 7
  let mut hStmts : UInt64 := 7
  let mut nStmts := 0
  for f in (sortNames (holderArr ++ rawArr)).toList do
    let isHolder : Bool := holders.contains f
    emit s!"READERDIGEST START {f}"
    let rawDirect : Bool :=
      match env.find? f with
      | some (.defnInfo d) => usesPairMatcher pm d.value
      | _ => false
    -- the reader, again
    let res ← readAgain f
    let mut raw : Bool := rawDirect
    match res with
    | .ok (r, gate) =>
      let rawEntry : Bool :=
        match r.entry.value? with
        | some v => usesPairMatcher pm v
        | none => false
      raw := rawDirect || rawEntry
      let d := shapeDigest r.shape
      nRead := nRead + 1
      hShapes := mixHash hShapes (mixHash (nameHash f) d.all)
      emit s!"READERDIGEST SHAPE {f}: holder={bs isHolder} raw={bs raw} gate route={bs gate} read=T {d.line}"
    | .error text =>
      nRefused := nRefused + 1
      hShapes := mixHash hShapes (mixHash (nameHash f) (hashStr text))
      emit s!"READERDIGEST SHAPE {f}: holder={bs isHolder} raw={bs raw} read=F refused: {text}"
    if raw then nRaw := nRaw + 1
    -- the generated data
    if isHolder then
      match env.find? (f ++ `machineData) with
      | some ci =>
        let tyH := ci.type.hash
        let valH : UInt64 :=
          match ci.value? with
          | some v => v.hash
          | none => 0
        hData := mixHash hData (mixAll [nameHash f, tyH, valH])
        emit s!"READERDIGEST DATA {f}: type={tyH} value={valH}"
      | none => emit s!"READERDIGEST DATA {f}: absent"
      -- the statements below it
      let mine : Array (Name × UInt64) :=
        (kids.filter fun k => k.1 == f).map fun k => (k.2.1, k.2.2)
      let mineSorted := mine.qsort fun x y => x.1.toString < y.1.toString
      let h : UInt64 := mineSorted.foldl (fun acc k => mixHash acc (mixHash (nameHash k.1) k.2)) 7
      hStmts := mixHash hStmts (mixHash (nameHash f) h)
      nStmts := nStmts + mineSorted.size
      emit s!"READERDIGEST STATEMENTS {f}: n={mineSorted.size} hash={h}"
      if raw then
        for k in mineSorted.toList do
          emit s!"READERDIGEST STATEMENT {k.1}: type={k.2}"
  emit s!"READERDIGEST TOTAL: declarations={holderArr.size + rawArr.size} holders={holderArr.size} read={nRead} refused={nRefused} raw={nRaw} statements={nStmts} shapes hash={hShapes} data hash={hData} statements hash={hStmts}"

/-- Log the digest of the current environment. Asserts nothing. -/
elab "#reader_digest" : command =>
  Lean.Elab.Command.liftTermElabM do
    run

end Tests.Compiler.ReaderDigestTest

#reader_digest
