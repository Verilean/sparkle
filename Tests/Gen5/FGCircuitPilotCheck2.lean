import Tools.ShippingFGCircuitArtifact
import Tools.ShippingFGCircuitSupply
import Tools.ShippingFGCircuitEnvCD
import Tools.ShippingFGCircuitFunc
set_option autoImplicit false
-- FG circuit pilot S1c check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §8.

/-! # FGCircuitPilotCheck2

Same method as `FGCircuitPilotCheckAt`: the EXPECTED type of each new theorem is written here independently (literal names, shapes, environments) and compared with the
actual type by `isDefEq` in `MetaM`; single-point MUTANTS must be rejected. Then: the axioms of every new name, the list of named hypotheses that remain, and the
SNAPSHOT2 lines (facts about THIS build's environment, kept apart from the theorems' statements about any run's environment). -/
namespace Tests.Gen5.FGCircuitPilotCheck2
open Lean Meta Elab Command Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitSupply Sparkle.Tests.SignalLoopTest
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMachineEntry (MachineDefines MachineCloses)
open Tools.ShippingEntryReadsLinked (envAt)

abbrev Cref := ST.Ref IO.RealWorld Core.State
abbrev W := Void IO.RealWorld
abbrev MD := Tools.ShippingMachineAuto.MachineData
def emptyModule : Sparkle.IR.AST.Module := { name := "", inputs := [], outputs := [], wires := [], body := [] }

/-! ## 1. functionality: expected statements -/

def ExpCdFun : Prop :=
  ∀ {ρ : Tools.ShippingGen5ConstValueE.Val} {e : Lean.Expr} {α α' : Type} {v : α} {v' : α'},
    CD ρ e α v → CD ρ e α' v' → α = α' ∧ HEq v v'
def ExpTdFun : Prop :=
  ∀ {ρ : Tools.ShippingGen5ConstValueE.Val} {e : Lean.Expr} {T T' : Type}, TD ρ e T → TD ρ e T' → T = T'
def ExpCircCVFun : Prop :=
  ∀ env c (α β : Type) (v : α) (w : β), CircCV env c α v → CircCV env c β w → α = β ∧ HEq v w
-- mutants: the second derivation in ANOTHER valuation; the conclusion without the value; the TD statement with unrelated types' equality direction kept but another expression
def MutCdFunVal : Prop :=
  ∀ {ρ ρ' : Tools.ShippingGen5ConstValueE.Val} {e : Lean.Expr} {α α' : Type} {v : α} {v' : α'},
    CD ρ e α v → CD ρ' e α' v' → α = α' ∧ HEq v v'
def MutCdFunWeak : Prop :=
  ∀ {ρ : Tools.ShippingGen5ConstValueE.Val} {e : Lean.Expr} {α α' : Type} {v : α} {v' : α'}, CD ρ e α v → CD ρ e α' v' → α = α'
def MutCdFunExpr : Prop :=
  ∀ {ρ : Tools.ShippingGen5ConstValueE.Val} {e e' : Lean.Expr} {α α' : Type} {v : α} {v' : α'},
    CD ρ e α v → CD ρ e' α' v' → α = α' ∧ HEq v v'
def MutCircCVFunEnv : Prop :=
  ∀ env env' c (α β : Type) (v : α) (w : β), CircCV env c α v → CircCV env' c β w → α = β ∧ HEq v w

/-! ## 2. same-artifact statements -/

def eS : Cref → W → W → Environment := fun cref w _ => envAt cref w
def eE : Cref → W → W → Environment := fun cref _ w' => envAt cref w'
def selM : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module := fun m => m
def selX : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module := fun _ => emptyModule

def shC : SigShape := { args := [], res := .one (.bits 8) }
def shS : SigShape := { args := [.bits 8], res := .one (.bits 8) }
def shE : SigShape := { args := [.bool], res := .one (.bits 8) }
def shA : SigShape := { args := [.bool, .bool], res := .one (.bits 2) }
noncomputable def dC : MD := counterLoop.machineData
noncomputable def dS : MD := shift4Loop.machineData
noncomputable def dE : MD := counterEnableLoop.machineData
noncomputable def dA : MD := Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData
def nC : Name := ``Sparkle.Tests.SignalLoopTest.counterLoop
def nS : Name := ``Sparkle.Tests.SignalLoopTest.shift4Loop
def nE : Name := ``Sparkle.Tests.SignalLoopTest.counterEnableLoop
def nA : Name := ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal

/-- EH: env of `RootInEnv`; EA: env of the artifact's `SourceDenotesMono`; XP: name looked up in `P`; XD: name of `p.decl` and `TopShips`; dl/kD: the link; mm: the meaning the link observes;
sel: module of the printed artifact (for `TopShips`/`WiredConclusion`/`RootArtifactMono`) -/
def ExpArtMono (EH EA : Cref → W → W → Environment) (sel : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) (X XP XD : Name) (ty val : Lean.Expr)
    (sh : SigShape) (mm : MonoTy sh) (dd dl : MD) (kD : Nat) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : Cref} {w w' : W}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design} {d : DefinitionVal} {ι : Type} {P : Pkgs ι (fun _ => defaultDomain)}
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {p : Pkg ι (fun _ => defaultDomain)},
    RootInEnv (EH cref w w') X ty val d →
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational X) mctx mref cctx cref w (b, design) w' →
    MachineDefines mctx mref cctx cref X dd.shape →
    P XP = some p → p.decl = XD →
    EndpointLink dl kD (fun _ bools bits => monoObs sh mm bools bits) p →
    (∀ raw, Post (sel b) raw → ∃ n, TopShips p n XD (sel b) raw design) →
    ∃ mm' : MonoTy sh, RootArtifactMono (EA cref w w') P Post XD sh mm' (sel b) design p ∧
      WiredConclusion X dd (fun _ : Unit => defaultDomain) (fun _ bools bits => monoObs sh mm' bools bits) (sel b)

def ExpArtC : Prop := ExpArtMono eS eS selM nC nC nC counterLoopType counterLoopValue shC counterLoop dC dC 0
def ExpArtS : Prop := ExpArtMono eS eS selM nS nS nS shift4LoopType shift4LoopValue shS shift4Loop dS dS 1
def ExpArtE : Prop := ExpArtMono eS eS selM nE nE nE counterEnableLoopType counterEnableLoopValue shE counterEnableLoop dE dE 1
def MutArtHypEnv : Prop := ExpArtMono eE eS selM nC nC nC counterLoopType counterLoopValue shC counterLoop dC dC 0     -- RootInEnv at the END world
def MutArtEnv : Prop := ExpArtMono eS eE selM nC nC nC counterLoopType counterLoopValue shC counterLoop dC dC 0        -- artifact's source meaning at the END world
def MutArtPName : Prop := ExpArtMono eS eS selM nC nS nC counterLoopType counterLoopValue shC counterLoop dC dC 0      -- package of ANOTHER declaration
def MutArtDeclName : Prop := ExpArtMono eS eS selM nC nC nS counterLoopType counterLoopValue shC counterLoop dC dC 0   -- p.decl / TopShips of another declaration
def MutArtLinkData : Prop := ExpArtMono eS eS selM nC nC nC counterLoopType counterLoopValue shC counterLoop dC dS 0   -- link to another root's data
def MutArtKD : Prop := ExpArtMono eS eS selM nC nC nC counterLoopType counterLoopValue shC counterLoop dC dC 1         -- wrong input count in the link
def MutArtModule : Prop := ExpArtMono eS eS selX nC nC nC counterLoopType counterLoopValue shC counterLoop dC dC 0     -- artifact about another module
def MutArtRunName : Prop := ExpArtMono eS eS selM nS nC nC counterLoopType counterLoopValue shC counterLoop dC dC 0    -- run of another declaration

def ExpArtA : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : Cref} {w w' : W}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design} {d : DefinitionVal} {P : Pkgs DomainConfig (fun i => i)}
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {p : Pkg DomainConfig (fun i => i)},
    RootInEnv (envAt cref w) nA arbiterType arbiterValue d →
    BoundaryRowsInEnv (envAt cref w) →
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational nA) mctx mref cctx cref w (b, design) w' →
    MachineDefines mctx mref cctx cref nA dA.shape →
    P nA = some p → p.decl = nA →
    EndpointLink dA (shA.args.length + 1) (fun i bools bits => shA.obs (dom := fun i : DomainConfig => i)
      (fun D => @Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D) i bools bits) p →
    (∀ raw, Post b raw → ∃ n, TopShips p n nA b raw design) →
    ∃ mm : shA.Ty, RootArtifact (envAt cref w) P Post nA shA mm b design p ∧
      WiredConclusion nA dA (fun i : DomainConfig => i) (fun i bools bits => shA.obs (dom := fun i : DomainConfig => i) mm i bools bits) b
def MutArtABoundary : Prop :=      -- boundary rows at the END world
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : Cref} {w w' : W}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design} {d : DefinitionVal} {P : Pkgs DomainConfig (fun i => i)}
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {p : Pkg DomainConfig (fun i => i)},
    RootInEnv (envAt cref w) nA arbiterType arbiterValue d →
    BoundaryRowsInEnv (envAt cref w') →
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational nA) mctx mref cctx cref w (b, design) w' →
    MachineDefines mctx mref cctx cref nA dA.shape →
    P nA = some p → p.decl = nA →
    EndpointLink dA (shA.args.length + 1) (fun i bools bits => shA.obs (dom := fun i : DomainConfig => i)
      (fun D => @Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D) i bools bits) p →
    (∀ raw, Post b raw → ∃ n, TopShips p n nA b raw design) →
    ∃ mm : shA.Ty, RootArtifact (envAt cref w) P Post nA shA mm b design p ∧
      WiredConclusion nA dA (fun i : DomainConfig => i) (fun i bools bits => shA.obs (dom := fun i : DomainConfig => i) mm i bools bits) b

/-! ## 3. static-environment reductions -/

/-- EHs: environment used for `RootInEnv` (E, or the run's start env = the mutant that drops `StaticEnv`'s use); Xd: name of `MachineDefinesAt` -/
def ExpStatic (EH : Cref → Environment → W → Environment) (Xd : Name) (X : Name) (ty val : Lean.Expr) (sh : SigShape) (mm : MonoTy sh) (dd : MD) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : Cref} {w w' : W}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design} {d : DefinitionVal} {E : Environment},
    StaticEnv cref E →
    RootInEnv (EH cref E w) X ty val d →
    MachineDefinesAt E Xd dd.shape →
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore X [] false) mctx mref cctx cref w (m, design) w' →
    ∃ mm' : MonoTy sh, SourceDenotesMono (envAt cref w) X [] sh mm' ∧
      Tools.ShippingMachineAuto.MachineTrace X dd m (fun _ : Unit => defaultDomain) (fun _ bools bits => monoObs sh mm' bools bits)
def eEnv : Cref → Environment → W → Environment := fun _ E _ => E
def eStart : Cref → Environment → W → Environment := fun cref _ w => envAt cref w
def ExpStC : Prop := ExpStatic eEnv nC nC counterLoopType counterLoopValue shC counterLoop dC
def ExpStS : Prop := ExpStatic eEnv nS nS shift4LoopType shift4LoopValue shS shift4Loop dS
def ExpStE : Prop := ExpStatic eEnv nE nE counterEnableLoopType counterEnableLoopValue shE counterEnableLoop dE
def MutStHyp : Prop := ExpStatic eStart nC nC counterLoopType counterLoopValue shC counterLoop dC       -- RootInEnv at the start env, not the static E
def MutStName : Prop := ExpStatic eEnv nS nC counterLoopType counterLoopValue shC counterLoop dC        -- MachineDefinesAt of another declaration
def MutStData : Prop := ExpStatic eEnv nC nC counterLoopType counterLoopValue shC counterLoop dS        -- trace for another machine data

/-! ## the comparison (MetaM) -/

def whitelist : List Name := [``ExpCdFun, ``ExpTdFun, ``ExpCircCVFun, ``MutCdFunVal, ``MutCdFunWeak, ``MutCdFunExpr, ``MutCircCVFunEnv,
  ``ExpArtMono, ``ExpArtC, ``ExpArtS, ``ExpArtE, ``MutArtHypEnv, ``MutArtEnv, ``MutArtPName, ``MutArtDeclName, ``MutArtLinkData, ``MutArtKD,
  ``MutArtModule, ``MutArtRunName, ``ExpArtA, ``MutArtABoundary, ``ExpStatic, ``ExpStC, ``ExpStS, ``ExpStE, ``MutStHyp, ``MutStName, ``MutStData,
  ``eS, ``eE, ``selM, ``selX, ``emptyModule, ``eEnv, ``eStart, ``shC, ``shS, ``shE, ``shA, ``dC, ``dS, ``dE, ``dA, ``nC, ``nS, ``nE, ``nA,
  ``shCounter, ``shShift4, ``shEnable, ``shArbiter, ``ConstValueFunctional]

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
  let F := `Tools.ShippingFGCircuit
  let A := `Tools.ShippingFGCircuitArtifact
  let S := `Tools.ShippingFGCircuitSupply
  same (F ++ `cd_fun) ``ExpCdFun
  same (F ++ `td_fun) ``ExpTdFun
  same (F ++ `circCV_functional) ``ExpCircCVFun
  let mut nm : Nat := 0
  for (t, mu) in [(F ++ `cd_fun, ``MutCdFunVal), (F ++ `cd_fun, ``MutCdFunWeak), (F ++ `cd_fun, ``MutCdFunExpr), (F ++ `circCV_functional, ``MutCircCVFunEnv)] do
    differs t mu; nm := nm + 1
  for (t, e) in [(A ++ `counterLoop_artifact_at, ``ExpArtC), (A ++ `shift4Loop_artifact_at, ``ExpArtS),
      (A ++ `counterEnableLoop_artifact_at, ``ExpArtE), (A ++ `arbiterSignal_artifact_at, ``ExpArtA),
      (S ++ `counterLoop_root_static, ``ExpStC), (S ++ `shift4Loop_root_static, ``ExpStS), (S ++ `counterEnableLoop_root_static, ``ExpStE)] do
    same t e
  for mu in [``MutArtHypEnv, ``MutArtEnv, ``MutArtPName, ``MutArtDeclName, ``MutArtLinkData, ``MutArtKD, ``MutArtModule, ``MutArtRunName] do
    differs (A ++ `counterLoop_artifact_at) mu; nm := nm + 1
  differs (A ++ `arbiterSignal_artifact_at) ``MutArtABoundary; nm := nm + 1
  for mu in [``MutStHyp, ``MutStName, ``MutStData] do
    differs (S ++ `counterLoop_root_static) mu; nm := nm + 1
  -- the genGP specialisations: P is the generated table at the SAME environment (envAt cref w) as the root
  for r in [`counterLoop, `shift4Loop, `counterEnableLoop, `arbiterSignal] do
    let ci ← getConstInfo (A ++ (r.appendAfter "_artifact_genGP"))
    let t := ci.type
    unless (t.find? (·.isConstOf `Tools.ShippingGenFGLedgerPremises.genGP)).isSome do throwError "{r}: genGP absent from the artifact statement"
  logInfo m!"FGCIRCUIT2 SIGNATURES: functionality (cd_fun, td_fun, circCV_functional), 4 same-artifact statements and 3 static reductions equal their independently written expected types; {nm} mutants rejected; 4 genGP specialisations mention genGP"

/-! ## axioms of every new name -/
run_cmd liftTermElabM do
  let F := `Tools.ShippingFGCircuit
  let A := `Tools.ShippingFGCircuitArtifact
  let S := `Tools.ShippingFGCircuitSupply
  let E := `Tools.ShippingFGCircuitEnvCD
  let roots := [`counterLoop, `shift4Loop, `counterEnableLoop, `arbiterSignal]
  let names : List Name := [F ++ `td_fun, F ++ `cd_fun, F ++ `cd_eq, F ++ `circCV_functional, F ++ `sourceDenotes_unique, F ++ `sourceDenotesMono_unique,
    A ++ `genGP_decl, A ++ `fgCircuitConclusionMono_of_artifact, A ++ `observationsEqualMono_of_link, A ++ `observationsEqual_of_link,
    A ++ `counterLoop_shape, A ++ `shift4Loop_shape, A ++ `counterEnableLoop_shape, A ++ `arbiterSignal_shape,
    S ++ `machineDefines_of_static, S ++ `rootInEnv_of_static, S ++ `boundaryRows_of_static, S ++ `run_reads_root, S ++ `run_reads_root_static,
    E ++ `abbrevDenotes_of_boundary, E ++ `abbrevDenotes_unique, E ++ `abbrev_unfold_eq_row, E ++ `boundaryRows_iff_unfold] ++
    roots.map (fun r => A ++ (r.appendAfter "_artifact_at")) ++ roots.map (fun r => A ++ (r.appendAfter "_artifact_genGP")) ++
    roots.map (fun r => S ++ (r.appendAfter "_root_static"))
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT2 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

/-! ## the hypotheses that remain, by name (read from the theorem types) -/
run_cmd liftTermElabM do
  let A := `Tools.ShippingFGCircuitArtifact
  let S := `Tools.ShippingFGCircuitSupply
  let show1 (thm : Name) : MetaM String := do
    let ci ← getConstInfo thm
    forallTelescope ci.type fun xs _ => do
      let mut hs : List String := []
      for x in xs do
        let d ← x.fvarId!.getDecl
        if d.binderInfo.isExplicit then hs := hs ++ [d.userName.toString]
      return String.intercalate " " hs
  for r in [`counterLoop, `shift4Loop, `counterEnableLoop, `arbiterSignal] do
    logInfo m!"FGCIRCUIT2 HYPS {r}_artifact_at: {← show1 (A ++ (r.appendAfter "_artifact_at"))}"
  for r in [`counterLoop, `shift4Loop, `counterEnableLoop, `arbiterSignal] do
    logInfo m!"FGCIRCUIT2 HYPS {r}_root_static: {← show1 (S ++ (r.appendAfter "_root_static"))}"

/-! ## SNAPSHOT2: facts about THIS build's environment -/
run_cmd liftTermElabM do
  let env ← getEnv
  let roots : List (Name × Lean.Expr × Lean.Expr) := [(nC, counterLoopType, counterLoopValue), (nS, shift4LoopType, shift4LoopValue),
    (nE, counterEnableLoopType, counterEnableLoopValue), (nA, arbiterType, arbiterValue)]
  for (x, ty, v) in roots do
    let some (.defnInfo d) := env.find? x | throwError "{x}: not a definition here"
    unless d.levelParams.isEmpty && d.type == ty && d.value == v do throwError "{x}: RootInEnv fails in this build's environment"
  for (nm, k) in [(`stIdle, 0), (`stGrantA, 1), (`stGrantB, 2)] do
    let some (.defnInfo d) := env.find? (Tools.ShippingFGCircuit.privAbbrev nm) | throwError "{nm}: missing"
    unless d.levelParams.isEmpty && d.type == Tools.ShippingFGCircuitRoots.eBV 2 && d.value == Tools.ShippingFGCircuitRoots.eBVLit 2 k do
      throwError "{nm}: BoundaryRowsInEnv fails here"
  logInfo "FGCIRCUIT2 SNAPSHOT2: in THIS build's environment RootInEnv holds for the 4 roots and BoundaryRowsInEnv holds (two of the three env-level premises of *_root_static, hE and hB, are true here); StaticEnv (the Core state keeps this one environment at every world of a run) and MachineDefinesAt (hd) are NOT checked here; this says nothing about the environment of an arbitrary run"

end Tests.Gen5.FGCircuitPilotCheck2
