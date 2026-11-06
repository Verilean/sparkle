import Tools.ShippingFGCircuitApply
import Tools.ShippingFGCircuitSupply2
import Tools.ShippingFGCircuitCover
import Tools.ShippingFGCircuitBridge
set_option autoImplicit false
-- FG circuit pilot S1d check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §9.

/-! # FGCircuitPilotCheck3

1. SIGNATURES: the expected type of the new general theorems, written here independently, compared with the actual type by `isDefEq`; single-point MUTANTS must be rejected.
2. HYPS: the explicit hypotheses of the four `X_final` theorems are read from their types and compared with the expected list; the supplied ones (`hd`, `hc`, `hP`, `hl`, `hTop`) must NOT be among them;
   each root's final statement mentions only its own root name.
3. AXIOMS of every new name.
4. SNAPSHOT3: facts about THIS build's environment, evaluated on real values in `MetaM` (the reader's data for each root, `MachineDefinesAt`), kept apart from the theorems' statements about any run. -/
namespace Tests.Gen5.FGCircuitPilotCheck3
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitSupply Tools.ShippingFGCircuitSupply2 Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMachineEntry (MachineDefines MachineCloses)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingStRefCorrespondence (SetGet)
open Tools.ShippingMachineAuto (MachineData)
open Sparkle.Compiler.Elab Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge

abbrev Cref := ST.Ref IO.RealWorld Core.State
abbrev W := Void IO.RealWorld
def nC : Name := ``Sparkle.Tests.SignalLoopTest.counterLoop
def nS : Name := ``Sparkle.Tests.SignalLoopTest.shift4Loop

/-! ## 1. expected statements -/

def ExpNotStatic : Prop := ∀ {cref : Cref} {E : Environment}, SetGet cref → ∀ w : W, ¬ StaticEnv cref E
def MutNotStaticNoSetGet : Prop := ∀ {cref : Cref} {E : Environment}, ∀ w : W, ¬ StaticEnv cref E          -- without the cell premise
def MutNotStaticOtherEnv : Prop := ∀ {cref : Cref} {E E' : Environment}, SetGet cref → ∀ w : W, ¬ StaticEnv cref E ∨ E = E'

def ExpHdA6 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : Cref} {L : Laws mref cref} {mctx : Meta.Context}
    {cctx : Core.Context} {P : Pkgs ι dom} {X : Name} {p : Pkg ι dom} {d : MachineData},
    AdmCtx L.O.quiet mctx cctx →
    (∀ c, TgtRun P X c → ∀ q : Pkg ι dom, P c = some q →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx L.O.quiet mctx' cctx' → MachineDefines mctx' mref cctx' cref c q.d.shape) →
    P X = some p → p.d = d → MachineDefines mctx mref cctx cref X d.shape
def MutHdA6Name : Prop :=      -- the conclusion about another declaration than the one `P` is queried at
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : Cref} {L : Laws mref cref} {mctx : Meta.Context}
    {cctx : Core.Context} {P : Pkgs ι dom} {X Y : Name} {p : Pkg ι dom} {d : MachineData},
    AdmCtx L.O.quiet mctx cctx →
    (∀ c, TgtRun P X c → ∀ q : Pkg ι dom, P c = some q →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx L.O.quiet mctx' cctx' → MachineDefines mctx' mref cctx' cref c q.d.shape) →
    P X = some p → p.d = d → MachineDefines mctx mref cctx cref Y d.shape
def MutHdA6NoStart : Prop :=   -- no admissible start context
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : Cref} {L : Laws mref cref} {mctx : Meta.Context}
    {cctx : Core.Context} {P : Pkgs ι dom} {X : Name} {p : Pkg ι dom} {d : MachineData},
    (∀ c, TgtRun P X c → ∀ q : Pkg ι dom, P c = some q →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx L.O.quiet mctx' cctx' → MachineDefines mctx' mref cctx' cref c q.d.shape) →
    P X = some p → p.d = d → MachineDefines mctx mref cctx cref X d.shape

def ExpCover : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (lvl : Lean.Expr → Nat) (env : Environment) {X : Name} {d : MachineData},
    RootReader lvl env X d → Tools.ShippingGen5Sem.GenWF d = true → d.shape.insts = [] →
    ∃ p : Pkg ι dom, Tools.ShippingGenFGLedgerPremises.genGP (ι := ι) (dom := dom) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) env X = some p ∧
      p.decl = X ∧ p.d = d ∧ p.kD = Tools.ShippingGen5Sem.kDOf d
def MutCoverNoLeaf : Prop :=   -- without the leaf condition
  ∀ {ι : Type} {dom : ι → DomainConfig} (lvl : Lean.Expr → Nat) (env : Environment) {X : Name} {d : MachineData},
    RootReader lvl env X d → Tools.ShippingGen5Sem.GenWF d = true →
    ∃ p : Pkg ι dom, Tools.ShippingGenFGLedgerPremises.genGP (ι := ι) (dom := dom) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) env X = some p ∧
      p.decl = X ∧ p.d = d ∧ p.kD = Tools.ShippingGen5Sem.kDOf d
def MutCoverKD : Prop :=       -- wrong kD
  ∀ {ι : Type} {dom : ι → DomainConfig} (lvl : Lean.Expr → Nat) (env : Environment) {X : Name} {d : MachineData},
    RootReader lvl env X d → Tools.ShippingGen5Sem.GenWF d = true → d.shape.insts = [] →
    ∃ p : Pkg ι dom, Tools.ShippingGenFGLedgerPremises.genGP (ι := ι) (dom := dom) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) env X = some p ∧
      p.decl = X ∧ p.d = d ∧ p.kD = 0

def whitelist : List Name := [``ExpNotStatic, ``MutNotStaticNoSetGet, ``MutNotStaticOtherEnv, ``ExpHdA6, ``MutHdA6Name, ``MutHdA6NoStart, ``ExpCover, ``MutCoverNoLeaf, ``MutCoverKD]

def norm (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    if let .const c _ := e.getAppFn then
      if whitelist.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let same (thm exp : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    unless ci.levelParams.isEmpty do throwError "{thm}: level parameters"
    let a ← norm ci.type
    let e ← norm (mkConst exp)
    unless ← withReducible (isDefEq a e) do throwError "{thm}: type is NOT the expected statement {exp}"
  let differs (thm mu0 : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    let a ← norm ci.type
    let e ← norm (mkConst mu0)
    if ← withReducible (isDefEq a e) then throwError "{thm}: the MUTANT {mu0} was accepted"
  let S2 := `Tools.ShippingFGCircuitSupply2
  let C := `Tools.ShippingFGCircuitCover
  same (S2 ++ `not_staticEnv) ``ExpNotStatic
  same (S2 ++ `machineDefines_of_hA6) ``ExpHdA6
  same (C ++ `genGP_root_canon) ``ExpCover
  let mut nm : Nat := 0
  for (t, mu) in [(S2 ++ `not_staticEnv, ``MutNotStaticNoSetGet), (S2 ++ `not_staticEnv, ``MutNotStaticOtherEnv), (S2 ++ `machineDefines_of_hA6, ``MutHdA6Name),
      (S2 ++ `machineDefines_of_hA6, ``MutHdA6NoStart), (C ++ `genGP_root_canon, ``MutCoverNoLeaf), (C ++ `genGP_root_canon, ``MutCoverKD)] do
    differs t mu; nm := nm + 1
  logInfo m!"FGCIRCUIT3 SIGNATURES: not_staticEnv, machineDefines_of_hA6, genGP_root_canon equal their independently written expected types; {nm} mutants rejected"

/-! ## 2. the hypotheses that remain, by name (read from the theorem types) -/

def explicitBinders (thm : Name) : MetaM (List (String × Lean.Expr)) := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs _ => do
    let mut hs : List (String × Lean.Expr) := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isExplicit then hs := hs ++ [(d.userName.toString, d.type)]
    return hs

run_cmd liftTermElabM do
  let A := `Tools.ShippingFGCircuitApply
  let roots : List (Name × Name × List String) := [
    (`counterLoop, ``Sparkle.Tests.SignalLoopTest.counterLoop, ["L", "lvl", "hw", "hr", "hA6", "hRead", "hE", "hsrc", "htr"]),
    (`shift4Loop, ``Sparkle.Tests.SignalLoopTest.shift4Loop, ["L", "lvl", "hw", "hr", "hA6", "hRead", "hE", "hsrc", "htr"]),
    (`counterEnableLoop, ``Sparkle.Tests.SignalLoopTest.counterEnableLoop, ["L", "lvl", "hw", "hr", "hA6", "hRead", "hE", "hsrc", "htr"]),
    (`arbiterSignal, ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal, ["L", "lvl", "hw", "hr", "hA6", "hRead", "hE", "hB", "hsrc", "htr"])]
  let allRoots : List Name := roots.map (·.2.1)
  for (r, full, expected) in roots do
    let thm := A ++ (r.appendAfter "_final")
    let bs ← explicitBinders thm
    let names := bs.map (·.1)
    unless names == expected do throwError "{thm}: hypotheses are {names}, expected {expected}"
    for supplied in ["hd", "hc", "hcl", "hP", "hl", "hTop", "hpost"] do
      if names.contains supplied then throwError "{thm}: {supplied} is still a hypothesis"
    -- the statement (hypotheses and conclusion) mentions its own root and no other root
    let ci ← getConstInfo thm
    let consts := ci.type.getUsedConstants
    unless consts.contains full do throwError "{thm}: root {full} not mentioned"
    for o in allRoots do
      if o != full && consts.contains o then throwError "{thm}: mentions another root {o}"
    for need in [``Tools.ShippingGenFGLedgerPremises.genGP, ``Tools.ShippingFGCircuitCover.canonGD, ``Tools.ShippingFGCircuitBridge.PostRun] do
      unless consts.contains need do throwError "{thm}: {need} absent"
    logInfo m!"FGCIRCUIT3 HYPS {r}_final: {String.intercalate " " names}"
  logInfo "FGCIRCUIT3 HYPS: hd, hc, hP, hl.data/kD, hTop(core design), ∃raw supplied inside every X_final; hr is the antecedent `compile succeeded`"

/-! ## 3. axioms of every new name -/
run_cmd liftTermElabM do
  let S2 := `Tools.ShippingFGCircuitSupply2
  let C := `Tools.ShippingFGCircuitCover
  let B := `Tools.ShippingFGCircuitBridge
  let A := `Tools.ShippingFGCircuitApply
  let roots := [`counterLoop, `shift4Loop, `counterEnableLoop, `arbiterSignal]
  let names : List Name := [S2 ++ `not_staticEnv, S2 ++ `machineDefines_of_hA6, S2 ++ `machineDefines_of_witness, S2 ++ `run_reads_const, S2 ++ `rootInEnv_of_quote,
    S2 ++ `hE_of_run, C ++ `genSemI_kD, C ++ `genGP_root, C ++ `canon_row, C ++ `genGP_root_canon, B ++ `machineClosesAtA_of_closes, B ++ `leaf_topShips_of_run, B ++ `hTop_of_leaf] ++
    roots.map (fun r => A ++ (r.appendAfter "_final")) ++ roots.map (fun r => A ++ (r.appendAfter "_leafFacts")) ++ roots.map (fun r => A ++ (r.appendAfter "_wf")) ++
    roots.map (fun r => A ++ (r.appendAfter "_kD"))
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT3 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

/-! ## 4. SNAPSHOT3: real values in THIS build's environment -/

def invariants (d : MachineData) : List Nat :=
  [d.nIn, d.ss.length, d.outs.length, d.ls.length, d.shape.insts.length, d.shape.binders.length, if d.ok then 1 else 0,
   if Tools.ShippingGen5Sem.GenWF d then 1 else 0]

def litInvariants (d0 : Name) : TermElabM (List Nat) := do
  let c := mkIdent d0
  let terms : Array (TSyntax `term) := #[← `(($c : MachineData).nIn), ← `(($c : MachineData).ss.length), ← `(($c : MachineData).outs.length),
    ← `(($c : MachineData).ls.length), ← `(($c : MachineData).shape.insts.length), ← `(($c : MachineData).shape.binders.length),
    ← `(if ($c : MachineData).ok then 1 else 0), ← `(if Tools.ShippingGen5Sem.GenWF ($c : MachineData) then 1 else 0)]
  let mut out := []
  for t in terms do
    let e ← elabTerm t (some (mkConst ``Nat))
    let e ← instantiateMVars e
    let r ← withTransparency .all (whnf e)
    let n ← match r.nat? with
      | some n => pure n
      | none => match r.rawNatLit? with
        | some n => pure n
        | none => throwError "not a literal: {r}"
    out := out ++ [n]
  return out

run_cmd liftTermElabM do
  let env ← getEnv
  let roots : List (Name × Name) := [(``Sparkle.Tests.SignalLoopTest.counterLoop, ``Sparkle.Tests.SignalLoopTest.counterLoop.machineData),
    (``Sparkle.Tests.SignalLoopTest.shift4Loop, ``Sparkle.Tests.SignalLoopTest.shift4Loop.machineData),
    (``Sparkle.Tests.SignalLoopTest.counterEnableLoop, ``Sparkle.Tests.SignalLoopTest.counterEnableLoop.machineData),
    (``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal, ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData)]
  let mut nd : Nat := 0
  for (x, d0) in roots do
    -- RootReader (with a large fuel `lvl`): entry, machineShape?, dataOfAt on the real environment
    let some E := Tools.ShippingGen5Acc.entry₀ env x | throwError "{x}: no entry constant in this environment"
    let some s := machineShape? false [] E (structEnv env) | throwError "{x}: machineShape? none"
    let some d := Tools.ShippingGen5DataOf.dataOfAt (fun _ => 1000000) E (structEnv env) s | throwError "{x}: dataOfAt none"
    let lit ← litInvariants d0
    unless invariants d == lit do throwError "{x}: the reader's data {invariants d} differs from the endpoint literal {lit}"
    unless d.shape.insts.isEmpty do throwError "{x}: not a leaf"
    -- MachineDefinesAt on the real environment (the three facts of `hd`)
    let some ci := env.find? x | throwError "{x}: not in env"
    let ec := entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)
    unless (certifiedShape? false [] ec).isNone do throwError "{x}: certifiedShape? is not none"
    unless (mixedCertifiedShape? false [] ec (instancePredicate env)).isNone do throwError "{x}: mixedCertifiedShape? is not none"
    unless (machineShape? false [] ec (structEnv env)).isSome do throwError "{x}: machineShape? of the entry is none"
    nd := nd + 1
  logInfo m!"FGCIRCUIT3 SNAPSHOT3: in THIS build's environment, for {nd} roots: the entry constant exists, machineShape? and dataOfAt (fuel 1000000) return data with the SAME nIn / #state / #outs / #lets / #insts / #binders / ok / GenWF as the endpoint literal (an invariant comparison, NOT full equality of the data), the root is a leaf, and the three facts of MachineDefinesAt hold (certifiedShape? = none, mixedCertifiedShape? = none, machineShape? = some). These are values, evaluated, for one environment; they are not the kernel statements about an arbitrary run (RootReader / MachineDefinesAt stay named premises)"

end Tests.Gen5.FGCircuitPilotCheck3
