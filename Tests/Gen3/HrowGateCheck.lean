import Tools.ShippingGen3HrowGateServed
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built: cached target build at 76c9d2ae (kjob lake build in the rt77 Pod; NOT a clean build, the coder runs it), exit 0, standard axioms. No `sorry`, no `axiom`, no `native_decide`.

/-! # G-HROW-GATE checks (scripts/gen3/HROW_GATE_DECISION.md, user decision G)

1. **Expected types** (`checkExpected`, shared helper `Tests.Gen3.ExpectedType`), binder by binder, against
   independent texts: `machineShape?_noMemRow` (L2), `servedShips0_run`, `postFacts_of_run`, `t1_of_stepPF_run`,
   `t1_of_step_rows_run`.
2. **Mutants** (`checkMutant`): a REJECTION BY SIGNATURE / defeq of the statement, NOT a semantic counterexample.
   L2 with the conclusion `= false`; `servedShips0_run` with the old `hrow` binder; `postFacts_of_run` without
   `hrows`; `t1_of_stepPF_run` without `hPF`.
3. **Binder set, fully qualified.** For every new theorem the binder NAMES are listed and the set of `Tools.*`
   constants in the binder types must lie in an explicit whitelist (`Laws`, `Pkgs`, `Pkg`, `DataRows`,
   `StepStmt`, `PostFactsStmt`, `ServedShips0Stmt`). `OneOutNoMemRow` (the `hrow` binder) is not on it. DECOYS: the
   old `servedShips0_proved` (binder `hrow`) and a local decoy theorem with an `hrow` binder MUST be flagged.
4. **Closure.** The transitive constants of each new theorem (type and value) do not contain the five theorems that
   take `hrow` (`servedShips0_proved`, `postFacts_proved`, `postFacts_of_hord`, `t1_of_stepPF_served`,
   `t1_of_step_rows`). Control: `t1_of_stepPF_served` reaches `servedShips0_proved` (detector fires).
5. **AXIOMS** standard only, **COUNTS** line. -/

namespace Tests.Gen3.HrowGateCheck
open Tests.Gen3.ExpectedType
open Tools.ShippingGen2
open Sparkle.Core.Domain

section Expected
open Lean hiding Module
open Meta
open Sparkle.Compiler.Elab
open Tools.ShippingGen2DataBridge (noMemRowS)

def ExpectedL2 : Prop :=
  ∀ {sym : Bool} {params : List (String × Nat)} {ci : ConstantInfo} {senv : StructEnv} {allow : Bool}
    {sp : MachineShape} (h : machineShape? sym params ci senv allow = some sp), noMemRowS sp = true

/-- MUTANT: conclusion negated. -/
def MutL2_false : Prop :=
  ∀ {sym : Bool} {params : List (String × Nat)} {ci : ConstantInfo} {senv : StructEnv} {allow : Bool}
    {sp : MachineShape} (h : machineShape? sym params ci senv allow = some sp), noMemRowS sp = false

def ExpectedServedRun : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop),
    ServedShips0Stmt L P Reach DataOk

/-- MUTANT: the old `hrow` binder back (= the old theorem's statement). -/
def MutServedRun_hrow : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true),
    ServedShips0Stmt L P Reach DataOk

def ExpectedPostFactsRun : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q),
    PostFactsStmt L P Reach DataOk

/-- MUTANT: `hrows` dropped. -/
def MutPostFactsRun_noRows : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop),
    PostFactsStmt L P Reach DataOk

def ExpectedT1PFRun : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hStep : StepStmt L P DataOk) (hPF : PostFactsStmt L P Reach DataOk),
    T1Stmt L P Reach DataOk

/-- MUTANT: `hPF` dropped. -/
def MutT1PFRun_noPF : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hStep : StepStmt L P DataOk),
    T1Stmt L P Reach DataOk

def ExpectedT1RowsRun : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hStep : StepStmt L P DataOk),
    T1Stmt L P Reach DataOk

end Expected

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``Tools.ShippingGen3HrowGate.machineShape?_noMemRow ``ExpectedL2
  checkExpected ``Tools.ShippingGen2.servedShips0_run ``ExpectedServedRun
  checkExpected ``Tools.ShippingGen2.postFacts_of_run ``ExpectedPostFactsRun
  checkExpected ``Tools.ShippingGen2.t1_of_stepPF_run ``ExpectedT1PFRun
  checkExpected ``Tools.ShippingGen2.t1_of_step_rows_run ``ExpectedT1RowsRun
  checkMutant ``Tools.ShippingGen3HrowGate.machineShape?_noMemRow ``MutL2_false
  checkMutant ``Tools.ShippingGen2.servedShips0_run ``MutServedRun_hrow
  checkMutant ``Tools.ShippingGen2.postFacts_of_run ``MutPostFactsRun_noRows
  checkMutant ``Tools.ShippingGen2.t1_of_stepPF_run ``MutT1PFRun_noPF

/-! ## Binder set and closure -/

/-- A decoy: a theorem with an `hrow` binder. -/
theorem decoyHrow {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true) : True := trivial

section Audit
open Lean Meta

/-- The binder names of a theorem's type, macro scopes erased. -/
def binderNames (n : Name) : MetaM (List Name) := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs _ => xs.toList.mapM fun x => do
    pure (← x.fvarId!.getDecl).userName.eraseMacroScopes

/-- The `Tools.*` constants occurring in the binder types, fully qualified. -/
def binderToolsConsts (n : Name) : MetaM (List Name) := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs _ => do
    let mut out : NameSet := {}
    for x in xs do
      let t ← inferType x
      for c in t.getUsedConstants do
        if (`Tools).isPrefixOf c then out := out.insert c
    pure out.toList

def whitelist : List Name :=
  [``Tools.ShippingGen2.Laws, ``Tools.ShippingGen2.Pkgs, ``Tools.ShippingGen2.Pkg, ``Tools.ShippingGen2.DataRows,
   ``Tools.ShippingGen2.StepStmt, ``Tools.ShippingGen2.PostFactsStmt]

def hrowConst : Name := ``Tools.ShippingGen2DataBridge.OneOutNoMemRow

/-- The `Tools.*` constants of the binders are all on the whitelist (and `OneOutNoMemRow` is not among them). -/
def binderClean (n : Name) : MetaM Bool := do
  let cs ← binderToolsConsts n
  pure (cs.all (whitelist.contains ·) && !cs.contains hrowConst)

def forbidden : List Name :=
  [``Tools.ShippingGen2.servedShips0_proved, ``Tools.ShippingGen2.postFacts_proved,
   ``Tools.ShippingGen2.postFacts_of_hord, ``Tools.ShippingGen2.t1_of_stepPF_served,
   ``Tools.ShippingGen2.t1_of_step_rows]

def body? : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

/-- Transitive constants of `root` (type and value); the first forbidden one reached, with the count visited. -/
def reach (root : Name) (cap : Nat := 3000000) : MetaM (Option Name × Nat) := do
  let env ← getEnv
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut queue : Array Name := #[root]
  let mut i := 0
  while i < queue.size do
    let c := queue[i]!
    i := i + 1
    if i > cap then throwError "HROWGATE AUDIT INCOMPLETE at {root}"
    let some ci := env.find? c | continue
    for u in ci.type.getUsedConstants ++ ((body? ci).map (·.getUsedConstants)).getD #[] do
      if forbidden.contains u && u != root then return (some u, i)
      unless seen.contains u do
        seen := seen.insert u
        queue := queue.push u
  return (none, i)

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let news : List (Name × List Name) :=
    [(``Tools.ShippingGen2.servedShips0_run, [`ι, `dom, `mref, `cref, `L, `P, `Reach, `DataOk]),
     (``Tools.ShippingGen2.postFacts_of_run, [`ι, `dom, `mref, `cref, `L, `P, `Reach, `DataOk, `hrows]),
     (``Tools.ShippingGen2.t1_of_stepPF_run, [`ι, `dom, `mref, `cref, `L, `P, `Reach, `DataOk, `hStep, `hPF]),
     (``Tools.ShippingGen2.t1_of_step_rows_run, [`ι, `dom, `mref, `cref, `L, `P, `Reach, `DataOk, `hrows, `hStep])]
  -- DECOYS (detector must fire): the old theorem and the local decoy have an `hrow` binder
  for d in [``Tools.ShippingGen2.servedShips0_proved, ``decoyHrow] do
    if (← binderClean d) then throwError "HROWGATE AUDIT FAILED: decoy {d} not flagged"
    unless (← binderNames d).contains `hrow do throwError "HROWGATE AUDIT FAILED: decoy {d} has no hrow binder name"
  let (ctl, _) ← reach ``Tools.ShippingGen2.t1_of_stepPF_served
  unless ctl == some ``Tools.ShippingGen2.servedShips0_proved do
    throwError "HROWGATE AUDIT FAILED: closure control did not reach servedShips0_proved: {ctl}"
  let mut nb := 0
  let mut nv := 0
  for (n, exp) in news do
    let bs ← binderNames n
    unless bs == exp do throwError "HROWGATE AUDIT FAILED {n}: binders {bs}, expected {exp}"
    if bs.contains `hrow then throwError "HROWGATE AUDIT FAILED {n}: hrow binder"
    unless (← binderClean n) do throwError "HROWGATE AUDIT FAILED {n}: a non-whitelisted Tools constant in the binders"
    let (hit, v) ← reach n
    if let some h := hit then throwError "HROWGATE AUDIT FAILED {n}: closure reaches {h}"
    nb := nb + bs.length
    nv := nv + v
    logInfo m!"HROWGATE BINDERS {n}: {bs}; closure clean (visited {v})"
  logInfo m!"HROWGATE COUNTS: theorems {news.length}, binders {nb}, decoys flagged 2, closure control hit 1, closure visited {nv}"

end Audit

/-! ## Axioms -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Tools.ShippingGen3HrowGate.noMemRowS_of_gate, ``Tools.ShippingGen3HrowGate.machineShape?_noMemRow_defn,
      ``Tools.ShippingGen3HrowGate.machineShape?_noMemRow, ``Tools.ShippingGen2.servedShips0_run,
      ``Tools.ShippingGen2.postFacts_of_run, ``Tools.ShippingGen2.t1_of_stepPF_run,
      ``Tools.ShippingGen2.t1_of_step_rows_run] do
    checkAxioms n

#print axioms Tools.ShippingGen3HrowGate.machineShape?_noMemRow
#print axioms Tools.ShippingGen2.servedShips0_run
#print axioms Tools.ShippingGen2.postFacts_of_run
#print axioms Tools.ShippingGen2.t1_of_step_rows_run

end Tests.Gen3.HrowGateCheck
