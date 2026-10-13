import Lean.Elab.Command
import Tools.ShippingFinalGoalCommand
import Tools.ShippingMachineCommand
import Tools.ShippingNoPortsMemCommand
import Tools.ShippingLeafDesignCommand

/-! # `#design_coverage`: which declarations have a check-free design-level endpoint — a CENSUS of the environment (round par/b-34)

WRITTEN, NOT BUILT. A MEASUREMENT, not a proof: it reads the environment of
the file it is run in and logs. It adds nothing, asserts nothing, expects
nothing.

## What it scans

Every constant of the environment once (`env.constants.fold`). A constant
`f.s` (last component `s`) makes `f` a DECLARATION WITH AN ARTIFACT when

* `s = machineData` — `f` took the machine route and `#machine_endpoint`
  (`Tools/ShippingMachineCommand.lean`, the reflected data) ran on it;
* `s = gateValue` — `#gate_child f` ran (`Tools/ShippingGateChildCommand.lean`
  60): `f` is compiled by the certified gate as a child;
* `s` starts with `machine_design_` — a design-level theorem of `f` (whatever
  generator or hand test made it).

## COVERED

`f` is COVERED when at least one constant `f.machine_design_…` (not a
`…_gap`, `…_regen`, `…_expected` companion) passes the RE-CHECK, on its
stored statement:

1. every proposition BINDER is allowed by the goal's classifier
   `Tools.ShippingFinalGoalCommand.allowed` (the run, `MachineDefines`,
   `EntryDefines`, `ChildBnd`, conjunctions of them);
2. under the leading existentials, in `P ∧ (A₁ → … → C)` (or `A₁ → … → C`),
   every antecedent `Aᵢ` is allowed;
3. the statement mentions NO checker / closing constant: the parents' seven
   (`portsMatchB`, `kidsPass`, `designCheck`, `shipsHierCheck`, `outsCheck`,
   `kidsMaskedN`, `hierCheck` — the list every family's audit uses),
   `MachineCloses`, `MachineClosesAt`, `ChildRanIn`. (The further constants
   the memory route's audits ban — `kidsMixed`, `kidsMem`, `kidsMasked`, and
   the rest of `Tools.ShippingNoPortsMemCommand.forbiddenMem` — are REPORTED
   in the row when a passing endpoint mentions one; they do not fail it);
4. the statement mentions `Tools.ShippingDesignSV.DesignSV`.

No list of endpoint NAMES decides coverage: any `machine_design_…` constant
that passes counts, and one that does not is listed with what failed. (The
forms known at 7d8d56b1 are in `docs/parallel/B-coverage-census.md`.)

## OPEN, with a reason read at the Meta level

For a declaration that is not covered the reason is read from the SOURCE
declaration by the compiler's reader
(`Tools.ShippingMachineCommand.readMachine`, the function every scope scan
uses): its call entries (by name), whether an entry is a memory placeholder,
its register slots, its closing kind (`instFields = []`: one-output), and
the depth of its call tree. The reflected data `f.machineData` is NEVER
evaluated: neither by compiled code nor by reduction.

| class | meaning |
|---|---|
| `COVERED` | a check-free design-level endpoint passes the re-check |
| `OPEN gate-route` | `f.gateValue` exists and the machine reader does not read `f` (or there is no `f.machineData`): a gate child; no entry-level design endpoint was found (`#gate_design0`) |
| `OPEN memory` | call entries that are memory placeholders (alone or beside others) |
| `OPEN calls` | call entries, none a memory: with the callees, the closing kind and the depth |
| `OPEN register-leaf` | no call, a register: `#machine_leaf_design` was not run on it, or refused it |
| `OPEN slotless-leaf` | no call, no register: `#machine_comb_design0` was not run on it, or refused it (several outputs, …) |
| `OPEN reader` | the reader refuses the declaration now, or threw |
| `OPEN design-only` | a constant with a `machine_design_…` constant below it but neither marker (not expected) |

Since round par/b-35 a prefix `p` of a `p.machine_design_…` constant that is
NOT itself a constant of the environment (the namespace of a general
theorem, e.g. `Tools.ShippingNoPorts.machine_design_noPorts`) gets no row:
such prefixes are counted and listed in the SCAN line. A check-free design
endpoint of a gate-route declaration is `f.gate_design0`
(`Tools/ShippingGateDesignCommand.lean`): its last component does not start
with `machine_design_`, so it is recognised as a fourth form — see `isDesign`.

Each OPEN row also lists the `machine_design_…` constants of `f` that failed
the re-check, with the number of NOT ALLOWED premises and the checker
constants mentioned.

## Cost

One fold over all constants of the environment (their NUMBER is logged; a
string comparison on the last name component each); per `machine_design_…`
constant one traversal of its statement (no pretty-printing); per uncovered
machine-route declaration one run of the reader on it and on its callees, to
depth 6. Nothing is elaborated, nothing is added. A failure on one
declaration is caught and recorded in its row. -/
namespace Tools.ShippingDesignCoverage
open Lean Meta Elab Command

/-- The checker / closing constants a check-free endpoint must not mention:
the parents' seven checkers (the list every family's audit uses) and the
closing premises. -/
def checkerConsts : List Name :=
  (Tools.ShippingLeafDesignCommand.checkers ++
    [``Tools.ShippingMachineEntry.MachineCloses, ``Tools.ShippingChildInv.MachineClosesAt,
     ``Tools.ShippingChildInv.ChildRanIn]).eraseDups

/-- Further constants some families' audits ban (the memory route's list):
REPORTED when a passing endpoint mentions one, not a reason to fail it. -/
def extraConsts : List Name :=
  (Tools.ShippingNoPortsMemCommand.forbiddenMem.filter fun k => !checkerConsts.contains k).eraseDups

/-- The companion suffixes that are not endpoints of their own. -/
def isCompanion (s : String) : Bool :=
  s.endsWith "_gap" || s.endsWith "_regen" || s.endsWith "_expected"

/-- The last components of design-level constants: `machine_design_…`, and
the gate route's `gate_design0` (round par/b-35). -/
def isDesign (s : String) : Bool :=
  s.startsWith "machine_design_" || s == "gate_design0"

/-- What the fold collects. -/
structure Found where
  machine : NameSet := {}
  gate : NameSet := {}
  /-- (declaration, design-level constant, its last component) -/
  design : Array (Name × Name × String) := #[]
  scanned : Nat := 0

def collect (env : Environment) : Found :=
  env.constants.fold (fun (acc : Found) (n : Name) (_ : ConstantInfo) =>
    let acc := { acc with scanned := acc.scanned + 1 }
    match n with
    | .str p s =>
      if s == "machineData" then { acc with machine := acc.machine.insert p }
      else if s == "gateValue" then { acc with gate := acc.gate.insert p }
      else if isDesign s && !isCompanion s then
        { acc with design := acc.design.push (p, n, s) }
      else acc
    | _ => acc) {}

/-- The antecedents under the existentials of an endpoint's body: how many,
and how many are NOT ALLOWED. `∃ x…, P ∧ (A₁ → … → C)`, or `A₁ → … → C`. -/
partial def antecedents (ty : Lean.Expr) : MetaM (Nat × Nat) := do
  if ty.isAppOfArity ``Exists 2 then
    let α := ty.getArg! 0
    let p := ty.getArg! 1
    let nm : Name := if p.isLambda then p.bindingName! else `w
    withLocalDeclD nm α fun x => antecedents (mkApp p x).headBeta
  else
    let mut R : Lean.Expr := if ty.isAppOfArity ``And 2 then ty.getArg! 1 else ty
    let mut n : Nat := 0
    let mut bad : Nat := 0
    while (← Tools.ShippingFinalGoalCommand.isPropArrow R) do
      n := n + 1
      unless Tools.ShippingFinalGoalCommand.allowed R.bindingDomain! do bad := bad + 1
      R := R.bindingBody!
    return (n, bad)

/-- The re-check of one design-level constant. -/
structure Check where
  ok : Bool
  props : Nat
  antes : Nat
  bad : Nat
  checkers : List Name
  hasDesign : Bool
  extra : List Name := []
  err : Option String := none

def recheck (c : Name) : MetaM Check := do
  try
    let ci ← getConstInfo c
    let ty := ci.type
    let checkers := checkerConsts.filter fun k => (ty.find? (·.isConstOf k)).isSome
    let extra := extraConsts.filter fun k => (ty.find? (·.isConstOf k)).isSome
    let hasDesign := (ty.find? (·.isConstOf ``Tools.ShippingDesignSV.DesignSV)).isSome
    let (props, badB, antes, badA) ← forallTelescope ty fun xs body => do
      let mut props : Nat := 0
      let mut badB : Nat := 0
      for x in xs do
        let t ← instantiateMVars (← inferType x)
        if ← isProp t then
          props := props + 1
          unless Tools.ShippingFinalGoalCommand.allowed t do badB := badB + 1
      let (antes, badA) ← antecedents body
      pure (props, badB, antes, badA)
    let bad := badB + badA
    return { ok := bad == 0 && checkers.isEmpty && hasDesign, props, antes, bad, checkers,
             hasDesign, extra }
  catch ex =>
    let msg ← ex.toMessageData.toString
    return { ok := false, props := 0, antes := 0, bad := 0, checkers := [], hasDesign := false,
             err := some msg }

/-- The depth of the call tree of `f`, by the reader (0: no call entry; a
callee the reader does not read counts as a leaf). -/
partial def depthOf (f : Name) (fuel : Nat) : MetaM Nat := do
  if fuel == 0 then return 0
  let calls? : Option (List Name) ← try
      let r ← Tools.ShippingMachineCommand.readMachine f
      pure (some (r.shape.insts.map (·.1)).eraseDups)
    catch _ => pure none
  match calls? with
  | none => return 0
  | some [] => return 0
  | some cs =>
    let mut m : Nat := 0
    for c in cs do
      if (Sparkle.Compiler.MachMemory.memChild? c).isNone then
        let d ← depthOf c (fuel - 1)
        if d > m then m := d
    return m + 1

/-- The class and the reason of a declaration that is not covered. -/
def openReason (env : Environment) (f : Name) (isMachine isGate : Bool) :
    MetaM (String × String) := do
  if !isMachine then
    if isGate then
      return ("OPEN gate-route", "f.gateValue and no f.machineData: compiled by the certified gate as a child (#gate_child); no entry-level design endpoint in the environment")
    else
      return ("OPEN design-only", "a machine_design_… constant, but neither f.machineData nor f.gateValue")
  try
    let r ← Tools.ShippingMachineCommand.readMachine f
    let calls : List Name := r.shape.insts.map (·.1)
    let kids := calls.eraseDups
    let mems := kids.filter fun k => (Sparkle.Compiler.MachMemory.memChild? k).isSome
    let others := kids.filter fun k => (Sparkle.Compiler.MachMemory.memChild? k).isNone
    let slots := r.shape.layout.slots.length
    let outs := r.shape.layout.outs.map (·.name)
    let has (s : String) : Bool := env.contains (f ++ Name.mkSimple s)
    let arts : List String := ["machine_sound", "machine_ships", "machine_ships_wired",
      "machine_ships_comb", "machine_closes", "machine_closes_at", "closes_deep",
      "machine_linked", "machine_composed", "machine_ships_hier", "machine_ships_hierR"].filter has
    if !mems.isEmpty then
      return ("OPEN memory", s!"call entries {calls}: memory placeholders {mems}, other callees {others}; slots {slots}; instFields {r.shape.instFields}; present: {arts}")
    else if !kids.isEmpty then
      let depth ← depthOf f 6
      let closing : String :=
        if r.shape.instFields.isEmpty then "one-output closing (instFields = [])"
        else s!"general closing (instFields {r.shape.instFields})"
      let kinds := others.map fun k =>
        let km : String := if env.contains (k ++ `machineData) then "machine" else
          if env.contains (k ++ `gateValue) then "gate" else "no artifact"
        s!"{k} ({km})"
      return ("OPEN calls", s!"call entries {calls}; distinct callees {kinds}; {closing}; depth {depth}; slots {slots}; present: {arts}")
    else if slots > 0 then
      return ("OPEN register-leaf", s!"no call, {slots} register slot(s), outputs {outs}; present: {arts} (machine_ships_wired is what #machine_leaf_design starts from)")
    else
      return ("OPEN slotless-leaf", s!"no call, no register, outputs {outs}; present: {arts} (machine_ships_comb and the one output `out` are what #machine_comb_design0 asks)")
  catch ex =>
    let msg ← ex.toMessageData.toString
    let short : String := if msg.length ≤ 300 then msg else String.ofList (msg.toList.take 300) ++ " …"
    -- (round par/b-35) a gate child that the machine reader refuses is a
    -- gate-route declaration, not a reader failure
    if isGate then
      return ("OPEN gate-route", s!"f.gateValue exists (#gate_child) and the machine reader does not read it: compiled by the certified gate; its entry-level design endpoint is f.gate_design0 (#gate_design0), not in the environment. The reader says: {short}")
    return ("OPEN reader", s!"the machine reader does not read it now: {short}")

/-- A name's last component with its digits replaced (to count forms). -/
def formOf (s : String) : String :=
  String.ofList (s.toList.map fun c => if c.isDigit then 'N' else c)

/-- `#design_coverage`: see the file header. -/
elab "#design_coverage" : command => do
  IO.eprintln "DESIGN COVERAGE START"
  logInfo m!"DESIGN COVERAGE START"
  let t0 ← IO.monoMsNow
  let env ← getEnv
  let found := collect env
  let designDecls : NameSet := found.design.foldl (fun s x => s.insert x.1) {}
  let all : NameSet := designDecls.toList.foldl (fun s n => s.insert n)
    (found.gate.toList.foldl (fun s n => s.insert n) found.machine)
  -- (round par/b-35) only CONSTANTS of the environment are declarations: a
  -- prefix that is a namespace of general theorems (`Tools.ShippingNoPorts`
  -- before `machine_design_noPorts`, …) is counted apart and gets no row
  let notDecl := (all.toList.filter fun n => !env.contains n).toArray.qsort
    fun a b => a.toString < b.toString
  let decls := (all.toList.filter fun n => env.contains n).toArray.qsort
    fun a b => a.toString < b.toString
  logInfo m!"DESIGN COVERAGE SCAN: {found.scanned} constants scanned; declarations with f.machineData: {found.machine.size}; with f.gateValue: {found.gate.size}; machine_design_… constants (without _gap / _regen / _expected): {found.design.size}; declarations in the census: {decls.size}; prefixes of machine_design_… constants that are NOT constants of the environment (namespaces of general theorems; no row): {notDecl.size} {notDecl.toList}"
  let mut rows : Array String := #[]
  let mut classes : Array (String × Name) := #[]
  let mut forms : Array String := #[]
  let mut k : Nat := 0
  for f in decls do
    k := k + 1
    if k % 25 == 0 then IO.eprintln s!"DESIGN COVERAGE {k} of {decls.size}"
    let res : Except String (String × String × List String) ← try
        let r ← liftTermElabM do
          let mine := found.design.filter fun x => x.1 == f
          let mut passed : List String := []
          let mut failed : List String := []
          for (_, c, s) in mine do
            let ch ← recheck c
            if ch.ok then
              passed := passed ++ [s]
              unless ch.extra.isEmpty do
                failed := failed ++ [s!"{s} PASSES, but mentions {ch.extra} (banned by the memory route's audits only)"]
            else
              let why : String := match ch.err with
                | some e => s!"error {e}"
                | none => s!"{ch.bad} NOT ALLOWED of {ch.props} binders + {ch.antes} antecedents; checker constants {ch.checkers}; DesignSV {ch.hasDesign}"
              failed := failed ++ [s!"{s} ({why})"]
          if !passed.isEmpty then
            pure ("COVERED", s!"by {passed}" ++ (if failed.isEmpty then "" else s!"; notes on its design-level constants (not check-free, or passing with a reported mention): {failed}"), passed)
          else
            let (cls, reason) ← openReason env f (found.machine.contains f) (found.gate.contains f)
            pure (cls, reason ++ (if failed.isEmpty then "; no machine_design_… constant" else s!"; design-level constants, not check-free: {failed}"), [])
        pure (Except.ok r)
      catch ex =>
        let msg ← ex.toMessageData.toString
        pure (Except.error msg)
    match res with
    | Except.ok (cls, text, passed) =>
      rows := rows.push s!"COVERAGE ROW {f}: {cls} — {text}"
      classes := classes.push (cls, f)
      for s in passed do forms := forms.push (formOf s)
    | Except.error msg =>
      rows := rows.push s!"COVERAGE ROW {f}: ERROR — {msg}"
      classes := classes.push ("ERROR", f)
  for r in rows do logInfo m!"{r}"
  let classNames := (classes.map (·.1)).toList.eraseDups
  let totals := classNames.map fun c => s!"{c}: {(classes.filter fun x => x.1 == c).size}"
  let formNames := forms.toList.eraseDups
  let formTotals := formNames.map fun c => s!"{c}: {(forms.filter fun x => x == c).size}"
  let ms := (← IO.monoMsNow) - t0
  logInfo m!"DESIGN COVERAGE TOTALS of {decls.size} declarations: {totals}. Covering endpoints by form (digits as N; a declaration may have several): {formTotals}. {ms} ms. A MEASUREMENT of this file's environment: COVERED means that a machine_design_… constant of the declaration passed the re-check (0 NOT ALLOWED premises by the goal's classifier, no checker / closing constant, a DesignSV conclusion); it says nothing beyond that statement's own scope (one declaration, its depth, data conditions decided per declaration, DesignSV of the module list — not the SV string, not #sim). Declarations whose endpoints are generated only in target-only files are not in this environment unless the file imports them."

end Tools.ShippingDesignCoverage
