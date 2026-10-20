import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Tools.ShippingDesignCoverage
import Tools.ShippingGateDefines
import Tools.ShippingHierarchySoundness
import Tools.ShippingMixedEntrySoundness

/-! # `#gate_coverage p₁ … pₙ`: gate-route PARENTS — a SEPARATE tally (round par/gate-cov)

WRITTEN, NOT BUILT. A MEASUREMENT of the environment of the file it is run
in: it adds nothing, proves nothing, asserts nothing. `#design_coverage`
(`Tools/ShippingDesignCoverage.lean`) and `#outermost_coverage` are NOT
edited; the machine-route census (134 declarations / 133 covered) is NOT
touched and these rows are NOT part of it. The machine classifier
`Tools.ShippingFinalGoalCommand.allowed` is used unchanged; `GateDefines` is
NOT added to it.

Ruling (reviewer, 2026-10-15): gate-parent rows are a SEPARATE kind, with
separate columns for existence-only / all-run match / remaining conditions,
and target-only vs in-suite distinguished; never claim all-input coverage.
`GateDefines` is a separate gate-only reflection class with its own tally
(`docs/parallel/G-gatedefines-class.md`).

## Which theorems belong to a parent `P`

Every THEOREM of the environment one of whose LEADING binders (the syntactic
`∀` spine of its stored type) is a run

    RunsTo (synthesizeCombinational ``P) mctx mref cctx cref w (b, design) w'

with the name literal decoding (`Lean.Expr.name?`) to exactly `P` (both
compiler constants named `synthesizeCombinational` are accepted). No theorem
NAME is used to find or to classify.

## The three forms — read from the theorem's TYPE

* **observation**: the type mentions `evalAssignsH` and the constant `P`
  itself, directly or through a predicate constant (a definition whose type
  ends in `Prop`) up to two definitions deep — e.g. `ParentMixObservesC`,
  whose body evaluates the emitted module with `evalAssignsH` and compares
  `out` with `(parentMix aS bS).val t`. A predicate that mentions only the
  NAME literal ``P`` (e.g. `WrapPickObservesT`, against `pickF`) does not count.
* **existence**: a subterm `∃ e, DesignSV … e ∧ R` (`e` the last argument of
  `DesignSV`) with `R` mentioning the constant `P`.
* **all-run**: a subterm `∀ e, DesignSV … e → R` (`e` the last argument of
  `DesignSV`) with `R` mentioning the constant `P` — the every-closed-run
  clause of `ships_design_svN_all`'s form.

Columns: observation (every theorem with the observation), existence-only
(existence and NOT all-run), all-run.

## Premises

Every proposition binder, and every antecedent of an implication met while
descending the conclusion through `∃`, `∧` and `∀` (stopping at the
existence / all-run clauses), is classified:

| class | meaning |
|---|---|
| `run` | `RunsTo …` |
| `GATE` | `GateDefines …` — the separate gate-only reflection class (NOT ALLOWED by the machine classifier; if the classifier ever allows it the row says so in capitals) |
| `ALLOWED` | allowed by `Tools.ShippingFinalGoalCommand.allowed` (`ChildBnd`, `EntryDefines`, `MachineDefines`, conjunctions) |
| `INPUT` | the input-seeding antecedent (`∀ t st, t < T → ∃ bools bits, Admissible … ∧ …`): binds the source inputs, listed apart |
| `OTHER` | anything else, by its head constant (e.g. `DesignSideR`): a REMAINING condition |

The census's checker / closing constants
(`Tools.ShippingDesignCoverage.checkerConsts`) mentioned by the type are
listed too.

## Remaining conditions of a row

Taken from the STRONGEST form present (all-run, else existence-only, else
observation); among its theorems the one with the fewest `OTHER` + checker
mentions.

## Axioms, suite

`Lean.collectAxioms` of every form theorem: OK when only `propext`,
`Classical.choice`, `Quot.sound`; anything else (`Lean.ofReduceBool`,
`sorryAx`, a new axiom) is listed. In-suite: the theorem's module is in the
import closure of `Tests.AllTests`, computed from the SOURCE files under the
current directory (`import` lines of `Tests/AllTests.lean` and, recursively,
of every module whose file exists there); a module outside it is
target-only. When `Tests/AllTests.lean` is not found the column says
`UNKNOWN`. -/
namespace Tools.ShippingGateCoverage
open Lean Meta Elab Command

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The head of the synthesis entry (two compiler constants carry the name). -/
def isSynthHead (f : Lean.Expr) : Bool :=
  match f with
  | .const (.str _ "synthesizeCombinational") _ => true
  | _ => false

/-- `RunsTo (synthesizeCombinational ``P) …` ↦ `P`. -/
def runParent? (t : Lean.Expr) : Option Name :=
  if t.isAppOf ``Tools.ShippingEntrySoundness.RunsTo then
    t.getAppArgs.toList.findSome? fun a =>
      if isSynthHead a.getAppFn && a.getAppNumArgs ≥ 1 then (a.getArg! 0).name? else none
  else none

/-- The parent of the first run binder on the syntactic `∀` spine. -/
partial def spineParent? : Lean.Expr → Option Name
  | .forallE _ d b _ =>
    match runParent? d with
    | some p => some p
    | none => spineParent? b
  | _ => none

/-- The module a constant comes from (the main module for a local one). -/
def moduleOf (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some i => (env.allImportedModuleNames[i.toNat]?).getD Name.anonymous
  | none => env.mainModule

/-- (parent, theorem) for every theorem with a run binder of a listed parent. -/
def collect (env : Environment) (parents : List Name) : Array (Name × Name) :=
  env.constants.fold (fun (acc : Array (Name × Name)) (n : Name) (ci : ConstantInfo) =>
    match ci with
    | .thmInfo t =>
      match spineParent? t.type with
      | some p => if parents.contains p then acc.push (p, n) else acc
      | none => acc
    | _ => acc) #[]

def mentions (e : Lean.Expr) (c : Name) : Bool := (e.find? (·.isConstOf c)).isSome

/-- `DesignSV … #0`: the run argument is the variable just bound. -/
def isDesignSVOnBVar0 (d : Lean.Expr) : Bool :=
  d.isAppOf ``Tools.ShippingDesignSV.DesignSV && d.getAppNumArgs > 0 && d.appArg! == .bvar 0

/-- `∀ e, DesignSV … e → R` with `R` mentioning `P`. -/
def isAllRunNode (parent : Name) (e : Lean.Expr) : Bool :=
  match e with
  | .forallE _ _ (.forallE _ d b _) _ => isDesignSVOnBVar0 d && mentions b parent
  | _ => false

/-- `∃ e, DesignSV … e ∧ R` with `R` mentioning `P`. -/
def isExistNode (parent : Name) (e : Lean.Expr) : Bool :=
  if e.isAppOfArity ``Exists 2 then
    match e.getArg! 1 with
    | .lam _ _ b _ =>
      b.isAppOfArity ``And 2 && isDesignSVOnBVar0 (b.getArg! 0) && mentions (b.getArg! 1) parent
    | _ => false
  else false

def hasAllRun (parent : Name) (ty : Lean.Expr) : Bool := (ty.find? (isAllRunNode parent)).isSome
def hasExist (parent : Name) (ty : Lean.Expr) : Bool := (ty.find? (isExistNode parent)).isSome

/-- A type `… → Prop`. -/
def isPredType : Lean.Expr → Bool
  | .forallE _ _ b _ => isPredType b
  | .sort .zero => true
  | _ => false

def obsIn (parent : Name) (e : Lean.Expr) : Bool :=
  mentions e ``Tools.ShippingHierarchySoundness.evalAssignsH && mentions e parent

/-- A predicate constant used in `e` (up to `depth` definitions deep) whose
body carries the observation. -/
partial def obsConst? (env : Environment) (parent : Name) (e : Lean.Expr) (depth : Nat) :
    Option Name :=
  if depth == 0 then none else
  e.getUsedConstants.toList.findSome? fun k =>
    if k == parent then none else
    match env.find? k with
    | some (.defnInfo d) =>
      if isPredType d.type then
        if obsIn parent d.value then some k else obsConst? env parent d.value (depth - 1)
      else none
    | _ => none

def observation? (env : Environment) (parent : Name) (ty : Lean.Expr) : Option Name :=
  if obsIn parent ty then some `inlineObservation else obsConst? env parent ty 2

/-- The constant naming a premise: under its `∀`s, `∃`s and the left of `∧`s. -/
partial def keyOf (t : Lean.Expr) : MetaM String := do
  match t with
  | .forallE .. => forallTelescope t fun _ b => keyOf b
  | .mdata _ e => keyOf e
  | _ =>
    if t.isAppOfArity ``Exists 2 then
      match t.getArg! 1 with
      | .lam n d b _ => withLocalDeclD n d fun x => keyOf (b.instantiate1 x)
      | _ => pure "Exists"
    else if t.isAppOfArity ``And 2 then keyOf (t.getArg! 0)
    else pure (Tools.ShippingFinalGoalCommand.headName t)

/-- (class, label) of one premise; see the table of the file header. -/
def classify (t : Lean.Expr) : MetaM (String × String) := do
  if t.isAppOf ``Tools.ShippingEntrySoundness.RunsTo then return ("run", "RunsTo")
  if t.isAppOf ``Tools.ShippingGateDefines.GateDefines then
    if Tools.ShippingFinalGoalCommand.allowed t then
      return ("GATE", "GateDefines (ALLOWED BY THE MACHINE CLASSIFIER — A DEFECT TO REPORT)")
    return ("GATE", "GateDefines")
  if Tools.ShippingFinalGoalCommand.allowed t then
    return ("ALLOWED", Tools.ShippingFinalGoalCommand.headName t)
  let k ← keyOf t
  if k == "Admissible" then return ("INPUT", "Admissible")
  return ("OTHER", k)

/-- The antecedents met while descending a conclusion through `∃`, `∧`, `∀`
(stopping at the existence / all-run clauses), classified in place. -/
partial def antes (parent : Name) (e : Lean.Expr) (acc : Array (String × String)) :
    MetaM (Array (String × String)) := do
  if isExistNode parent e || isAllRunNode parent e then return acc
  match e with
  | .mdata _ e' => antes parent e' acc
  | .forallE n d b bi =>
    if ← isProp d then
      let c ← classify d
      withLocalDecl n bi d fun x => antes parent (b.instantiate1 x) (acc.push c)
    else
      withLocalDecl n bi d fun x => antes parent (b.instantiate1 x) acc
  | _ =>
    if e.isAppOfArity ``Exists 2 then
      match e.getArg! 1 with
      | .lam n d b _ => withLocalDeclD n d fun x => antes parent (b.instantiate1 x) acc
      | _ => pure acc
    else if e.isAppOfArity ``And 2 then
      let acc ← antes parent (e.getArg! 0) acc
      antes parent (e.getArg! 1) acc
    else pure acc

/-- What is read of one theorem. -/
structure Thm where
  name : Name
  module : Name
  obs : Option Name := none
  exist : Bool := false
  allRun : Bool := false
  binders : Array (String × String) := #[]
  antes : Array (String × String) := #[]
  checkers : List Name := []
  axioms : List Name := []
  err : Option String := none

def Thm.labels (t : Thm) (cls : String) : List String :=
  ((t.binders ++ t.antes).filter (·.1 == cls)).toList.map (·.2)
def Thm.flags (t : Thm) : Nat :=
  (t.labels "OTHER").length + t.checkers.length + (if t.err.isSome then 1000 else 0)
def Thm.axOk (t : Thm) : Bool := t.axioms.all standardAxioms.contains
def Thm.isForm (t : Thm) : Bool := t.err.isNone && (t.obs.isSome || t.exist || t.allRun)

def analyse (env : Environment) (parent c : Name) : MetaM Thm := do
  let base : Thm := { name := c, module := moduleOf env c }
  try
    let ci ← getConstInfo c
    let ty := ci.type
    let checkers := Tools.ShippingDesignCoverage.checkerConsts.filter (mentions ty)
    let (bs, ants) ← forallTelescope ty fun xs body => do
      let mut bs : Array (String × String) := #[]
      for x in xs do
        let t ← instantiateMVars (← inferType x)
        if ← isProp t then bs := bs.push (← classify t)
      let ants ← antes parent body #[]
      pure (bs, ants)
    let o := observation? env parent ty
    let ex := hasExist parent ty
    let ar := hasAllRun parent ty
    let t : Thm := { base with obs := o, exist := ex, allRun := ar, binders := bs, antes := ants, checkers := checkers }
    if t.isForm then
      let axs ← collectAxioms c
      return { t with axioms := axs.toList }
    return t
  catch ex =>
    let msg ← ex.toMessageData.toString
    return { base with err := some msg }

/-! ### The suite: import closure of `Tests.AllTests`, from the source files -/

def modPath (root : System.FilePath) (m : Name) : System.FilePath :=
  root / (String.intercalate "/" (m.components.map (·.toString)) ++ ".lean")

/-- A line after which no `import` can follow. -/
def stopLine (l : String) : Bool :=
  ["namespace ", "/-!", "open ", "section", "def ", "theorem ", "set_option", "noncomputable",
   "@[", "#"].any fun p => l.startsWith p

def importsOf (root : System.FilePath) (m : Name) : IO (Option (List Name)) := do
  let p := modPath root m
  unless (← p.pathExists) do return none
  let txt ← IO.FS.readFile p
  let mut out : List Name := []
  for l in txt.splitOn "\n" do
    if stopLine l then break
    if l.startsWith "import " || l.startsWith "public import " then
      let toks := (l.splitOn " ").takeWhile fun t => !t.startsWith "--"
      for tok in toks do
        if !tok.isEmpty && tok != "import" && tok != "public" && tok != "meta" && tok != "all" then
          out := out ++ [tok.toName]
  return some out

def suiteClosure (root : System.FilePath) : IO (Option NameSet) := do
  if (← importsOf root `Tests.AllTests).isNone then return none
  let mut seen : NameSet := ({} : NameSet).insert `Tests.AllTests
  let mut stack : Array Name := #[`Tests.AllTests]
  while stack.size > 0 do
    let m := stack.back!
    stack := stack.pop
    if let some imps ← importsOf root m then
      for i in imps do
        unless seen.contains i do
          seen := seen.insert i
          stack := stack.push i
  return some seen

def short (c : Name) : String :=
  match c with
  | .str _ s => s
  | _ => c.toString

def colOf (ts : Array Thm) : String :=
  if ts.isEmpty then "NONE" else toString (ts.toList.map fun t => short t.name)

/-- `#gate_coverage p₁ … pₙ`: see the file header. -/
elab "#gate_coverage" ids:(ppSpace ident)* : command => do
  logInfo m!"GATE COVERAGE START"
  let t0 ← IO.monoMsNow
  let parents ← ids.toList.mapM fun (id : TSyntax `ident) => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id.raw
  let env ← getEnv
  let root ← IO.currentDir
  let suite? ← suiteClosure root
  let suiteNote : String := match suite? with
    | none => s!"Tests/AllTests.lean NOT found under {root}: in-suite UNKNOWN"
    | some s => s!"import closure of Tests.AllTests read from the sources under {root}: {s.size} modules"
  let found := collect env parents
  let scan : String := s!"GATE COVERAGE SCAN: {parents.length} parent(s); {found.size} theorem(s) with a run binder RunsTo (synthesizeCombinational ``P) of a listed P; {suiteNote}"
  logInfo m!"{scan}"
  let suiteOf (t : Thm) : String := match suite? with
    | none => "UNKNOWN"
    | some s => if s.contains t.module then "in-suite" else "target-only"
  let mut nObs := 0
  let mut nEx := 0
  let mut nAll := 0
  let mut nNone : List Name := []
  let mut gateParents : List Name := []
  let mut badAx : List Name := []
  let mut nIn := 0
  let mut nTarget := 0
  let mut nMixed := 0
  let mut remaining : List String := []
  for p in parents do
    let cands := ((found.filter (·.1 == p)).map (·.2)).qsort fun a b => a.toString < b.toString
    let thms ← liftTermElabM <| cands.mapM fun c => analyse env p c
    let obsT := thms.filter (·.obs.isSome)
    let exT := thms.filter fun t => t.isForm && t.exist && !t.allRun
    let allT := thms.filter fun t => t.isForm && t.allRun
    let formT := thms.filter (·.isForm)
    let errT := thms.filter (·.err.isSome)
    let otherN := (thms.filter fun t => !t.isForm && t.err.isNone).size
    -- the per-theorem audit lines
    for t in formT do
      let forms : List String :=
        (if t.obs.isSome then [s!"observation (via {t.obs.getD .anonymous})"] else []) ++
        (if t.exist then ["existence"] else []) ++ (if t.allRun then ["all-run"] else [])
      let ax : String := if t.axOk then "standard axioms" else s!"NON-STANDARD AXIOMS {t.axioms}"
      let line : String := s!"GATE THM {short p} {t.name}: forms {forms}; binders {t.binders.toList}; antecedents in the conclusion {t.antes.toList}; checker / closing constants {t.checkers}; {ax}; module {t.module} ({suiteOf t})"
      logInfo m!"{line}"
    for t in errT do
      let msg : String := t.err.getD "error"
      let line : String := s!"GATE THM {short p} {t.name}: ERROR {msg}"
      logInfo m!"{line}"
    -- the row
    let (formName, strongest) : String × Array Thm :=
      if !allT.isEmpty then ("all-run", allT)
      else if !exT.isEmpty then ("existence-only", exT)
      else ("observation", obsT)
    let best? : Option Thm := strongest.foldl (fun (b : Option Thm) t =>
      match b with
      | none => some t
      | some b => if t.flags < b.flags then some t else some b) none
    let rem : String := match best? with
      | none => "no theorem of any form"
      | some b =>
        let g := b.labels "GATE"
        let o := b.labels "OTHER"
        let i := b.labels "INPUT"
        let a := b.labels "ALLOWED"
        let r := b.labels "run"
        s!"from {formName} theorem {short b.name}: GATE CLASS {g}; OTHER (remaining) {o}; INPUT {i}; ALLOWED {a}; run {r}; checker / closing constants {b.checkers}"
    match best? with
    | some b =>
      unless (b.labels "GATE").isEmpty do gateParents := gateParents ++ [p]
      remaining := remaining ++ b.labels "OTHER" ++ b.checkers.map toString
    | none => nNone := nNone ++ [p]
    let bad := formT.filter fun t => !t.axOk
    badAx := badAx ++ (bad.toList.map (·.name))
    let axCol : String :=
      if formT.isEmpty then "n/a"
      else if bad.isEmpty then s!"OK ({formT.size} theorem(s), standard axioms only)"
      else s!"NOT OK: {bad.toList.map fun t => (short t.name, t.axioms)}"
    let ins := formT.filter fun t => suiteOf t == "in-suite"
    let suiteCol : String :=
      if suite?.isNone then "UNKNOWN"
      else if formT.isEmpty then "n/a"
      else if ins.size == formT.size then "in-suite"
      else if ins.isEmpty then "target-only"
      else s!"mixed (in-suite: {ins.toList.map fun t => short t.name})"
    if suiteCol == "in-suite" then nIn := nIn + 1
    else if suiteCol == "target-only" then nTarget := nTarget + 1
    else if suiteCol.startsWith "mixed" then nMixed := nMixed + 1
    unless obsT.isEmpty do nObs := nObs + 1
    unless exT.isEmpty do nEx := nEx + 1
    unless allT.isEmpty do nAll := nAll + 1
    let row : String := s!"GATE ROW {p}: observation {colOf obsT} | existence-only {colOf exT} | all-run {colOf allT} | remaining ({rem}) | axioms {axCol} | {suiteCol} | theorems with this parent's run binder of none of the three forms: {otherN}; errors: {colOf errT}"
    logInfo m!"{row}"
  let ms := (← IO.monoMsNow) - t0
  let totals : String := s!"GATE COVERAGE TOTALS of {parents.length} gate-route parent(s): observation {nObs}; existence-only {nEx}; all-run {nAll}; no theorem of any form {nNone}; strongest form carries GateDefines (GATE CLASS) for {gateParents.length}; remaining OTHER conditions of the strongest forms {remaining.eraseDups}; non-standard axioms in {badAx}; in-suite {nIn}, target-only {nTarget}, mixed {nMixed}. {ms} ms. A SEPARATE TALLY of the kind 'gate-route parent': NOT part of #design_coverage (its machine-route population and counts are unchanged and counted apart) nor of #outermost_coverage. GateDefines is the separate gate-only reflection class (docs/parallel/G-gatedefines-class.md), counted here and NOT ALLOWED by the machine classifier. Every statement is conditional on its remaining premises and antecedents (GATE CLASS, OTHER) and is per declaration for the parents listed; all-run means every closed run of the emitted design from the theorem's own seeding and states, not every input of every design. This tally does NOT claim coverage of all inputs, nor of all gate-route declarations."
  logInfo m!"{totals}"

end Tools.ShippingGateCoverage
