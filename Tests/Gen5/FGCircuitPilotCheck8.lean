import Tests.Gen5.FGCircuitPilotCheck7
import Tools.ShippingFGCircuitS1iChild
import IP.Bus.PCIeHFT
set_option autoImplicit false
-- FG circuit pilot S1i check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §14.

/-! # FGCircuitPilotCheck8

1. SIGNATURES: complete expected types written independently of the theorems for `envFrame_coreHead`, `root_find_of_headAt`, `machineDefinesLinked_of_headAt`, `counterLoop_final9`/`9C`, `startFacts_of_checked`, the structure constructors of `CheckedEnv`/`CheckedStart`/`HeadIO`,
   `X_final10` for the four roots, `boundaryRows_of_contains`, `topShips_transport`, the two checker soundness lemmas.  MUTANTS: a cut connection (no head fact, the head fact at another run's world, `ReadsAt`/`CheckedStart` at the end world), another env / root / Post / data,
   a premise dropped (cell, IO fact, `NoRawBelow`), the transport in the wrong direction.
2. HYPS: the explicit hypotheses of the final theorems, by name and type.  Not hypotheses: `hquiet`, `GetEnvFrame`, `EnvFrame (coreHead X)` over all worlds, `hdRun`, `MachineDefinesLinked`, `hsrc`, `DesignTransport`, `hw`.
3. AXIOMS of every new name.
4. SNAPSHOT8: values of ONE environment (the build's): gates, root quote, boundary rows, and the design a real compile produced for `synth_hftPcieOutByte`'s body (a non-leaf), with the `NoRawBelow` side conditions evaluated by the checker. -/
namespace Tests.Gen5.FGCircuitPilotCheck8
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitLinked Tools.ShippingFGCircuitFinal4 Tools.ShippingFGCircuitRoots4
open Tools.ShippingFGCircuitS1hFrame Tools.ShippingFGCircuitS1hGates Tools.ShippingFGCircuitS1hQuote
open Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv Tools.ShippingFGCircuitS1iRoots Tools.ShippingFGCircuitS1iChild
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt CoreSaved coreHead)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingStRefCorrespondence (ReadWorld)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingGen5Env (ReadsAt)
open Sparkle.Compiler.Elab Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises
open Tests.Gen5.FGCircuitPilotCheck5 (W GPd EnvStart EnvEnd explicitBinders binderInfos)
open Tests.Gen5.FGCircuitPilotCheck6 (ExpGates ExpQuoteAt ExpReaderAt)
open Tests.Gen5.FGCircuitPilotCheck7 (ExpGatesB Z0 ZS ZE)

/-! ## 1. expected statements, written independently -/

/-- `envFrame_coreHead` (the frame of the whole head, from `CellPrem` and the two IO facts). Knob: the root of the head. -/
def ExpFrameHead (hn : Name → Name) (needCell needIO : Bool) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} (X : Name),
    (if needCell then CellPrem Tools.ShippingChildFresh.MkRefd mref cref else True) →
    (if needIO then HeadIO mctx mref cctx cref else True) →
    ∀ (w : W) (s : CoreSaved) (w' : W), RunsTo (coreHead (hn X)) mctx mref cctx cref w s w' → envAt cref w' = envAt cref w
def FrameHeadTrue := ExpFrameHead (fun x => x) true true
def MutFrameRoot := ExpFrameHead (fun _ => ``shift4Loop) true true
def MutFrameNoCell := ExpFrameHead (fun x => x) false true
def MutFrameNoIO := ExpFrameHead (fun x => x) true false

/-- `root_find_of_headAt`. Knobs: the world the head fact is stated at; the world of the lookup. -/
def ExpRootFindAt (hw : W → W → W) (fw : W → W → W) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {X : Name} {w w' : W} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    (∀ (s : CoreSaved) (w1 : W), RunsTo (coreHead X) mctx mref cctx cref (hw w w') s w1 → envAt cref w1 = envAt cref (hw w w')) →
    RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (M, D) w' →
    ∃ ci : ConstantInfo, (envAt cref (fw w w')).find? X = some ci
def RootFindAtTrue := ExpRootFindAt (fun w _ => w) (fun w _ => w)
def MutRootFindHeadEnd := ExpRootFindAt (fun _ w' => w') (fun w _ => w)
def MutRootFindEnd := ExpRootFindAt (fun w _ => w) (fun _ w' => w')

/-- `machineDefinesLinked_of_headAt`. Knobs: world of the head fact, environment of the lookup, of the gates, the output world. -/
def ExpHeadAt (hw : W → W → W) (eF eG : ST.Ref IO.RealWorld Core.State → W → W → Environment) (wsel : W → W → W) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {X : Name} {shape : MachineShape} {ci₀ : ConstantInfo} {w w' : W} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    (∀ (s : CoreSaved) (w1 : W), RunsTo (coreHead X) mctx mref cctx cref (hw w w') s w1 → envAt cref w1 = envAt cref (hw w w')) →
    Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref →
    (eF cref w w').find? X = some ci₀ →
    certifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate (eG cref w w')) (userInliner (eG cref w w')) (structEnv (eG cref w w'))) = none →
    mixedCertifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate (eG cref w w')) (userInliner (eG cref w w')) (structEnv (eG cref w w'))) (instancePredicate (eG cref w w')) = none →
    machineShape? false [] (entryConst true false [] ci₀ (instancePredicate (eG cref w w')) (userInliner (eG cref w w')) (structEnv (eG cref w w'))) (structEnv (eG cref w w')) = some shape →
    Tests.Gen5.FGCircuitPilotCheck6.ExpMDLTrue mctx mref cctx cref X shape (wsel w w') M D w'
def HeadAtTrue := ExpHeadAt (fun w _ => w) EnvStart EnvStart (fun w _ => w)
def MutHeadAtEnd := ExpHeadAt (fun _ w' => w') EnvStart EnvStart (fun w _ => w)
def MutHeadAtFind := ExpHeadAt (fun w _ => w) EnvEnd EnvStart (fun w _ => w)
def MutHeadAtGates := ExpHeadAt (fun w _ => w) EnvStart EnvEnd (fun w _ => w)
def MutHeadAtWorld := ExpHeadAt (fun w _ => w) EnvStart EnvStart (fun _ w' => w')

/-- `counterLoop_final9`. Knobs: world of the head fact, world `ReadsAt` is asserted at, environments of gates / quote / reader / conclusion, head root, data, Post root. -/
def ExpF9 (hroot : Name) (hw rw : W → W → W) (eG eK eD eC : Environment → ST.Ref IO.RealWorld Core.State → W → W → Environment) (dd : MachineData) (postRoot : Name) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {ι : Type}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment) {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ (s : CoreSaved) (w1 : W), RunsTo (coreHead hroot) mctx mref cctx cref (hw w w') s w1 → envAt cref w1 = envAt cref (hw w w')) →
    ReadWorld cref →
    ReadsAt env₀ cref (rw w w') →
    ExpGatesB (eG env₀ cref w w') ``counterLoop = true →
    ExpQuoteAt (eK env₀ cref w w') ``counterLoop counterLoopType counterLoopValue →
    ExpReaderAt lvl (eD env₀ cref w w') ``counterLoop dd →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (eC env₀ cref w w') (GPd lvl (eC env₀ cref w w')) (PostRun mctx mref cctx cref w postRoot D') ``counterLoop shCounter mm b D' p
def F9True := ExpF9 ``counterLoop (fun w _ => w) (fun w _ => w) Z0 Z0 Z0 ZS counterLoop.machineData ``counterLoop
def M9HeadEnd := ExpF9 ``counterLoop (fun _ w' => w') (fun w _ => w) Z0 Z0 Z0 ZS counterLoop.machineData ``counterLoop
def M9ReadsEnd := ExpF9 ``counterLoop (fun w _ => w) (fun _ w' => w') Z0 Z0 Z0 ZS counterLoop.machineData ``counterLoop
def M9HeadRoot := ExpF9 ``shift4Loop (fun w _ => w) (fun w _ => w) Z0 Z0 Z0 ZS counterLoop.machineData ``counterLoop
def M9GatesStart := ExpF9 ``counterLoop (fun w _ => w) (fun w _ => w) ZS Z0 Z0 ZS counterLoop.machineData ``counterLoop
def M9QuoteEnd := ExpF9 ``counterLoop (fun w _ => w) (fun w _ => w) Z0 ZE Z0 ZS counterLoop.machineData ``counterLoop
def M9ReaderEnd := ExpF9 ``counterLoop (fun w _ => w) (fun w _ => w) Z0 Z0 ZE ZS counterLoop.machineData ``counterLoop
def M9ConclEnd := ExpF9 ``counterLoop (fun w _ => w) (fun w _ => w) Z0 Z0 Z0 ZE counterLoop.machineData ``counterLoop
def M9Data := ExpF9 ``counterLoop (fun w _ => w) (fun w _ => w) Z0 Z0 Z0 ZS shift4Loop.machineData ``counterLoop
def M9Post := ExpF9 ``counterLoop (fun w _ => w) (fun w _ => w) Z0 Z0 Z0 ZS counterLoop.machineData ``shift4Loop
/-- a cut connection: no head fact at all -/
def M9NoHead : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {ι : Type}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment) {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    ReadWorld cref →
    ReadsAt env₀ cref w →
    ExpGatesB env₀ ``counterLoop = true →
    ExpQuoteAt env₀ ``counterLoop counterLoopType counterLoopValue →
    ExpReaderAt lvl env₀ ``counterLoop counterLoop.machineData →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd lvl (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p

/-- `counterLoop_final9C`: the head fact from `CellPrem` and `HeadIO` -/
def ExpF9C (needCell needIO : Bool) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {ι : Type}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment) {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (if needCell then CellPrem Tools.ShippingChildFresh.MkRefd mref cref else True) →
    (if needIO then HeadIO mctx mref cctx cref else True) →
    ReadsAt env₀ cref w →
    ExpGatesB env₀ ``counterLoop = true →
    ExpQuoteAt env₀ ``counterLoop counterLoopType counterLoopValue →
    ExpReaderAt lvl env₀ ``counterLoop counterLoop.machineData →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd lvl (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p
def F9CTrue := ExpF9C true true
def M9CNoCell := ExpF9C false true
def M9CNoIO := ExpF9C true false

/-- the structures: the constructors take exactly the listed fields (written independently) -/
def ExpCheckedEnvMk (needRoot needGates needReader : Bool) : Prop :=
  ∀ {lvl : Lean.Expr → Nat} {env₀ : Environment} {X : Name} {ty val : Lean.Expr} {dd : MachineData},
    (if needRoot then (∃ d : DefinitionVal, env₀.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ d.type = ty ∧ d.value = val) else True) →
    (if needGates then ExpGatesB env₀ X = true else True) →
    (if needReader then ExpReaderAt lvl env₀ X dd else True) →
    CheckedEnv lvl env₀ X ty val dd
def CheckedEnvMkTrue := ExpCheckedEnvMk true true true
def MutCEnvNoRoot := ExpCheckedEnvMk false true true
def MutCEnvNoGates := ExpCheckedEnvMk true false true
def MutCEnvNoReader := ExpCheckedEnvMk true true false

def ExpCheckedStartMk (needLink : Bool) (lw : W → W) : Prop :=
  ∀ {lvl : Lean.Expr → Nat} {env₀ : Environment} {cref : ST.Ref IO.RealWorld Core.State} {w : W} {X : Name} {ty val : Lean.Expr} {dd : MachineData},
    CheckedEnv lvl env₀ X ty val dd → (if needLink then ReadsAt env₀ cref (lw w) else True) → CheckedStart lvl env₀ cref w X ty val dd
def CheckedStartMkTrue := ExpCheckedStartMk true id
def MutCStartNoLink := ExpCheckedStartMk false id

def ExpHeadIOMk (needEnv needLog : Bool) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State},
    (if needEnv then Tools.ShippingEnvSnapshot.EnvFrame (liftM (IO.getEnv "SPARKLE_PROFILE") : MetaM (Option String)) mctx mref cctx cref else True) →
    (if needLog then (∀ msg : String, Tools.ShippingEnvSnapshot.EnvFrame (liftM (profLogIO true msg : IO Unit) : MetaM Unit) mctx mref cctx cref) else True) →
    HeadIO mctx mref cctx cref
def HeadIOMkTrue := ExpHeadIOMk true true

/-- `startFacts_of_checked`. Knobs: the environment of the three conclusions. -/
def ExpStartFacts (eG eR : ST.Ref IO.RealWorld Core.State → W → Environment → Environment) : Prop :=
  ∀ {lvl : Lean.Expr → Nat} {env₀ : Environment} {cref : ST.Ref IO.RealWorld Core.State} {w : W} {X : Name} {ty val : Lean.Expr} {dd : MachineData},
    CheckedStart lvl env₀ cref w X ty val dd → (∃ ci : ConstantInfo, (envAt cref w).find? X = some ci) →
    ExpGates (eG cref w env₀) X ∧ (∃ d : DefinitionVal, RootInEnv (envAt cref w) X ty val d) ∧ RootReader lvl (eR cref w env₀) X dd
def StartFactsTrue := ExpStartFacts (fun c w _ => envAt c w) (fun c w _ => envAt c w)
def MutStartGatesEnv0 := ExpStartFacts (fun _ _ e => e) (fun c w _ => envAt c w)
def MutStartReaderEnv0 := ExpStartFacts (fun c w _ => envAt c w) (fun _ _ e => e)


def ExpF10_counterLoop (hhw rdw : W → W → W) (eC : Environment → ST.Ref IO.RealWorld Core.State → W → W → Environment) (dd : MachineData) (postRoot : Name) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ (s : CoreSaved) (w1 : W), RunsTo (coreHead ``counterLoop) mctx mref cctx cref (hhw w w') s w1 → envAt cref w1 = envAt cref (hhw w w')) →
    ReadWorld cref →
    CheckedStart lvl env₀ cref (rdw w w') ``counterLoop counterLoopType counterLoopValue dd →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (eC env₀ cref w w') (GPd (ι := ι) lvl (eC env₀ cref w w'))
        (PostRun mctx mref cctx cref w postRoot D') ``counterLoop shCounter mm b D' p

def ExpF10_shift4Loop (hhw rdw : W → W → W) (eC : Environment → ST.Ref IO.RealWorld Core.State → W → W → Environment) (dd : MachineData) (postRoot : Name) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``shift4Loop) mctx mref cctx cref w (b, D') w' →
    (∀ (s : CoreSaved) (w1 : W), RunsTo (coreHead ``shift4Loop) mctx mref cctx cref (hhw w w') s w1 → envAt cref w1 = envAt cref (hhw w w')) →
    ReadWorld cref →
    CheckedStart lvl env₀ cref (rdw w w') ``shift4Loop shift4LoopType shift4LoopValue dd →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy shShift4) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (eC env₀ cref w w') (GPd (ι := ι) lvl (eC env₀ cref w w'))
        (PostRun mctx mref cctx cref w postRoot D') ``shift4Loop shShift4 mm b D' p

def ExpF10_counterEnableLoop (hhw rdw : W → W → W) (eC : Environment → ST.Ref IO.RealWorld Core.State → W → W → Environment) (dd : MachineData) (postRoot : Name) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterEnableLoop) mctx mref cctx cref w (b, D') w' →
    (∀ (s : CoreSaved) (w1 : W), RunsTo (coreHead ``counterEnableLoop) mctx mref cctx cref (hhw w w') s w1 → envAt cref w1 = envAt cref (hhw w w')) →
    ReadWorld cref →
    CheckedStart lvl env₀ cref (rdw w w') ``counterEnableLoop counterEnableLoopType counterEnableLoopValue dd →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy shEnable) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (eC env₀ cref w w') (GPd (ι := ι) lvl (eC env₀ cref w w'))
        (PostRun mctx mref cctx cref w postRoot D') ``counterEnableLoop shEnable mm b D' p

def ExpF10_arbiterSignal (hhw rdw : W → W → W) (eC : Environment → ST.Ref IO.RealWorld Core.State → W → W → Environment) (dd : MachineData) (postRoot : Name) : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal) mctx mref cctx cref w (b, D') w' →
    (∀ (s : CoreSaved) (w1 : W), RunsTo (coreHead ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal) mctx mref cctx cref (hhw w w') s w1 → envAt cref w1 = envAt cref (hhw w w')) →
    ReadWorld cref →
    CheckedStart lvl env₀ cref (rdw w w') ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue dd →
    BoundaryRowsInEnv env₀ → ContainsAt env₀ cref w boundaryNames →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : shArbiter.Ty) (p : Pkg DomainConfig (fun i => i)),
      RootArtifact (eC env₀ cref w w') (genGP (ι := DomainConfig) (dom := fun i => i) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (eC env₀ cref w w'))
        (PostRun mctx mref cctx cref w postRoot D') ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal shArbiter mm b D' p

/-- `boundaryRows_of_contains` -/
def ExpBoundary (rev : Bool) : Prop :=
  ∀ {env₀ : Environment} {cref : ST.Ref IO.RealWorld Core.State} {w : W},
    BoundaryRowsInEnv (if rev then envAt cref w else env₀) → ContainsAt env₀ cref w boundaryNames → BoundaryRowsInEnv (if rev then env₀ else envAt cref w)
def BoundaryTrue := ExpBoundary false
def MutBoundaryRev := ExpBoundary true
def MutBoundaryNoContains : Prop :=
  ∀ {env₀ : Environment} {cref : ST.Ref IO.RealWorld Core.State} {w : W}, BoundaryRowsInEnv env₀ → BoundaryRowsInEnv (envAt cref w)

/-- `topShips_transport`. Knobs: which design the premises talk about, the direction. -/
def ExpTopShips (dir : Bool) (needOpt : Bool) (rnB : Bool) : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (X : Name) {b raw : Sparkle.IR.AST.Module} {D D' : Sparkle.IR.AST.Design},
    Tools.ShippingGen5DCEntryD.PostEntry b raw D D' →
    Tools.ShippingGen5DCEntryR.NoRawBelow D raw.name (n + 1) raw →
    (if needOpt then Tools.ShippingGen5DCEntryR.NoRawBelow D raw.name (n + 1) (Sparkle.IR.OptCheck.checkedOptimize b) else True) →
    (∀ mn iname conns, Sparkle.IR.AST.Stmt.inst mn iname conns ∈ b.body → mn ≠ (if rnB then b.name else raw.name)) →
    (if dir then TopShips p n X b raw D else TopShips p n X b raw D') →
    (if dir then TopShips p n X b raw D' else TopShips p n X b raw D)
def TopShipsTrue := ExpTopShips true true false
def MutTSRev := ExpTopShips false true false
def MutTSNoOpt := ExpTopShips true false false
def MutTSNameB := ExpTopShips true true true

def ExpNoRawSound : Prop :=
  ∀ (D : Sparkle.IR.AST.Design) (rn : String) (k : Nat) (mc : Sparkle.IR.AST.Module), noRawBelowB D rn k mc = true → Tools.ShippingGen5DCEntryR.NoRawBelow D rn k mc
def MutNoRawSoundConv : Prop :=
  ∀ (D : Sparkle.IR.AST.Design) (rn : String) (k : Nat) (mc : Sparkle.IR.AST.Module), Tools.ShippingGen5DCEntryR.NoRawBelow D rn k mc → noRawBelowB D rn k mc = true
def ExpInstsNeSound : Prop :=
  ∀ (rn : String) (body : List Sparkle.IR.AST.Stmt), instsNeB rn body = true → ∀ mn iname conns, Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → mn ≠ rn
def MutInstsNeSoundEq : Prop :=
  ∀ (rn : String) (body : List Sparkle.IR.AST.Stmt), instsNeB rn body = true → ∀ mn iname conns, Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → mn = rn

def whitelist : List Name := [``ExpFrameHead, ``FrameHeadTrue, ``MutFrameRoot, ``MutFrameNoCell, ``MutFrameNoIO, ``ExpRootFindAt, ``RootFindAtTrue, ``MutRootFindHeadEnd, ``MutRootFindEnd,
  ``ExpHeadAt, ``HeadAtTrue, ``MutHeadAtEnd, ``MutHeadAtFind, ``MutHeadAtGates, ``MutHeadAtWorld,
  ``ExpF9, ``F9True, ``M9HeadEnd, ``M9ReadsEnd, ``M9HeadRoot, ``M9GatesStart, ``M9QuoteEnd, ``M9ReaderEnd, ``M9ConclEnd, ``M9Data, ``M9Post, ``M9NoHead, ``ExpF9C, ``F9CTrue, ``M9CNoCell, ``M9CNoIO,
  ``ExpCheckedEnvMk, ``CheckedEnvMkTrue, ``MutCEnvNoRoot, ``MutCEnvNoGates, ``MutCEnvNoReader, ``ExpCheckedStartMk, ``CheckedStartMkTrue, ``MutCStartNoLink, ``ExpHeadIOMk, ``HeadIOMkTrue,
  ``ExpStartFacts, ``StartFactsTrue, ``MutStartGatesEnv0, ``MutStartReaderEnv0,
  ``ExpBoundary, ``BoundaryTrue, ``MutBoundaryRev, ``MutBoundaryNoContains, ``ExpTopShips, ``TopShipsTrue, ``MutTSRev, ``MutTSNoOpt, ``MutTSNameB,
  ``ExpNoRawSound, ``MutNoRawSoundConv, ``ExpInstsNeSound, ``MutInstsNeSoundEq,
  ``Z0, ``ZS, ``ZE, ``Tests.Gen5.FGCircuitPilotCheck5.GPd, ``Tests.Gen5.FGCircuitPilotCheck5.EnvStart, ``Tests.Gen5.FGCircuitPilotCheck5.EnvEnd,
  ``Tests.Gen5.FGCircuitPilotCheck7.ExpGatesB, ``Tests.Gen5.FGCircuitPilotCheck6.ExpMDLTrue, ``Tests.Gen5.FGCircuitPilotCheck6.ExpMDL, ``Tests.Gen5.FGCircuitPilotCheck6.ExpGates,
  ``Tests.Gen5.FGCircuitPilotCheck6.ExpQuoteAt, ``Tests.Gen5.FGCircuitPilotCheck6.ExpReaderAt,
  -- definitions under test
  ``HeadAt, ``MachineDefinesLinked, ``EntryGates, ``entryGatesB, ``Tools.ShippingGen5Acc.entry₀, ``QuoteAt, ``ReaderAt,
  ``Tools.ShippingEnvSnapshot.GetEnvFrame, ``Tools.ShippingEnvSnapshot.EnvFrame, ``Tools.ShippingFGCircuitBridge.DesignTransport]

def F10True_counterLoop := ExpF10_counterLoop (fun w _ => w) (fun w _ => w) ZS counterLoop.machineData ``counterLoop
def M10HeadEnd_counterLoop := ExpF10_counterLoop (fun _ w' => w') (fun w _ => w) ZS counterLoop.machineData ``counterLoop
def M10LinkEnd_counterLoop := ExpF10_counterLoop (fun w _ => w) (fun _ w' => w') ZS counterLoop.machineData ``counterLoop
def M10ConclEnd_counterLoop := ExpF10_counterLoop (fun w _ => w) (fun w _ => w) ZE counterLoop.machineData ``counterLoop
def M10Data_counterLoop := ExpF10_counterLoop (fun w _ => w) (fun w _ => w) ZS shift4Loop.machineData ``counterLoop
def M10Post_counterLoop := ExpF10_counterLoop (fun w _ => w) (fun w _ => w) ZS counterLoop.machineData ``shift4Loop
def F10True_shift4Loop := ExpF10_shift4Loop (fun w _ => w) (fun w _ => w) ZS shift4Loop.machineData ``shift4Loop
def M10HeadEnd_shift4Loop := ExpF10_shift4Loop (fun _ w' => w') (fun w _ => w) ZS shift4Loop.machineData ``shift4Loop
def M10LinkEnd_shift4Loop := ExpF10_shift4Loop (fun w _ => w) (fun _ w' => w') ZS shift4Loop.machineData ``shift4Loop
def M10ConclEnd_shift4Loop := ExpF10_shift4Loop (fun w _ => w) (fun w _ => w) ZE shift4Loop.machineData ``shift4Loop
def M10Data_shift4Loop := ExpF10_shift4Loop (fun w _ => w) (fun w _ => w) ZS counterLoop.machineData ``shift4Loop
def M10Post_shift4Loop := ExpF10_shift4Loop (fun w _ => w) (fun w _ => w) ZS shift4Loop.machineData ``counterLoop
def F10True_counterEnableLoop := ExpF10_counterEnableLoop (fun w _ => w) (fun w _ => w) ZS counterEnableLoop.machineData ``counterEnableLoop
def M10HeadEnd_counterEnableLoop := ExpF10_counterEnableLoop (fun _ w' => w') (fun w _ => w) ZS counterEnableLoop.machineData ``counterEnableLoop
def M10LinkEnd_counterEnableLoop := ExpF10_counterEnableLoop (fun w _ => w) (fun _ w' => w') ZS counterEnableLoop.machineData ``counterEnableLoop
def M10ConclEnd_counterEnableLoop := ExpF10_counterEnableLoop (fun w _ => w) (fun w _ => w) ZE counterEnableLoop.machineData ``counterEnableLoop
def M10Data_counterEnableLoop := ExpF10_counterEnableLoop (fun w _ => w) (fun w _ => w) ZS counterLoop.machineData ``counterEnableLoop
def M10Post_counterEnableLoop := ExpF10_counterEnableLoop (fun w _ => w) (fun w _ => w) ZS counterEnableLoop.machineData ``counterLoop
def F10True_arbiterSignal := ExpF10_arbiterSignal (fun w _ => w) (fun w _ => w) ZS Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
def M10HeadEnd_arbiterSignal := ExpF10_arbiterSignal (fun _ w' => w') (fun w _ => w) ZS Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
def M10LinkEnd_arbiterSignal := ExpF10_arbiterSignal (fun w _ => w) (fun _ w' => w') ZS Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
def M10ConclEnd_arbiterSignal := ExpF10_arbiterSignal (fun w _ => w) (fun w _ => w) ZE Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
def M10Data_arbiterSignal := ExpF10_arbiterSignal (fun w _ => w) (fun w _ => w) ZS counterLoop.machineData ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
def M10Post_arbiterSignal := ExpF10_arbiterSignal (fun w _ => w) (fun w _ => w) ZS Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData ``counterLoop

def whitelist2 : List Name := [``ExpF10_counterLoop, ``F10True_counterLoop, ``M10HeadEnd_counterLoop, ``M10LinkEnd_counterLoop, ``M10ConclEnd_counterLoop, ``M10Data_counterLoop, ``M10Post_counterLoop, ``ExpF10_shift4Loop, ``F10True_shift4Loop, ``M10HeadEnd_shift4Loop, ``M10LinkEnd_shift4Loop, ``M10ConclEnd_shift4Loop, ``M10Data_shift4Loop, ``M10Post_shift4Loop, ``ExpF10_counterEnableLoop, ``F10True_counterEnableLoop, ``M10HeadEnd_counterEnableLoop, ``M10LinkEnd_counterEnableLoop, ``M10ConclEnd_counterEnableLoop, ``M10Data_counterEnableLoop, ``M10Post_counterEnableLoop, ``ExpF10_arbiterSignal, ``F10True_arbiterSignal, ``M10HeadEnd_arbiterSignal, ``M10LinkEnd_arbiterSignal, ``M10ConclEnd_arbiterSignal, ``M10Data_arbiterSignal, ``M10Post_arbiterSignal]

def norm (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if whitelist.contains c || whitelist2.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)

set_option maxHeartbeats 16000000 in
run_cmd liftTermElabM do
  let same (thm exp : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    unless ci.levelParams.isEmpty do throwError "{thm}: level parameters"
    let a ← norm ci.type
    let e ← norm (mkConst exp)
    unless ← withDefault (isDefEq a e) do throwError "{thm}: type is NOT the expected statement {exp}"
    let ba ← binderInfos a
    let be ← binderInfos e
    unless ba == be do throwError "{thm}: binder kinds differ from {exp}: {repr ba} vs {repr be}"
  let differs (thm mu0 : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    let a ← norm ci.type
    let e ← norm (mkConst mu0)
    if ← withDefault (isDefEq a e) then throwError "{thm}: the MUTANT {mu0} was accepted"
  let H := `Tools.ShippingFGCircuitS1iHead
  let E := `Tools.ShippingFGCircuitS1iEnv
  let R := `Tools.ShippingFGCircuitS1iRoots
  let C := `Tools.ShippingFGCircuitS1iChild
  -- envFrame_coreHead: stated as the unfolded frame (EnvFrame is unfolded by `norm`)
  same (H ++ `envFrame_coreHead) ``FrameHeadTrue
  let mut nm : Nat := 0
  for mu in [``MutFrameRoot, ``MutFrameNoCell, ``MutFrameNoIO] do differs (H ++ `envFrame_coreHead) mu; nm := nm + 1
  same (H ++ `root_find_of_headAt) ``RootFindAtTrue
  for mu in [``MutRootFindHeadEnd, ``MutRootFindEnd] do differs (H ++ `root_find_of_headAt) mu; nm := nm + 1
  same (H ++ `machineDefinesLinked_of_headAt) ``HeadAtTrue
  for mu in [``MutHeadAtEnd, ``MutHeadAtFind, ``MutHeadAtGates, ``MutHeadAtWorld] do differs (H ++ `machineDefinesLinked_of_headAt) mu; nm := nm + 1
  same (H ++ `counterLoop_final9) ``F9True
  for mu in [``M9HeadEnd, ``M9ReadsEnd, ``M9HeadRoot, ``M9GatesStart, ``M9QuoteEnd, ``M9ReaderEnd, ``M9ConclEnd, ``M9Data, ``M9Post, ``M9NoHead] do differs (H ++ `counterLoop_final9) mu; nm := nm + 1
  same (H ++ `counterLoop_final9C) ``F9CTrue
  for mu in [``M9CNoCell, ``M9CNoIO] do differs (H ++ `counterLoop_final9C) mu; nm := nm + 1
  same (E ++ `CheckedEnv.mk) ``CheckedEnvMkTrue
  for mu in [``MutCEnvNoRoot, ``MutCEnvNoGates, ``MutCEnvNoReader] do differs (E ++ `CheckedEnv.mk) mu; nm := nm + 1
  same (E ++ `CheckedStart.mk) ``CheckedStartMkTrue
  differs (E ++ `CheckedStart.mk) ``MutCStartNoLink; nm := nm + 1
  same (H ++ `HeadIO.mk) ``HeadIOMkTrue
  same (E ++ `startFacts_of_checked) ``StartFactsTrue
  for mu in [``MutStartGatesEnv0, ``MutStartReaderEnv0] do differs (E ++ `startFacts_of_checked) mu; nm := nm + 1
  same (R ++ `boundaryRows_of_contains) ``BoundaryTrue
  for mu in [``MutBoundaryRev, ``MutBoundaryNoContains] do differs (R ++ `boundaryRows_of_contains) mu; nm := nm + 1
  same (C ++ `topShips_transport) ``TopShipsTrue
  for mu in [``MutTSRev, ``MutTSNoOpt, ``MutTSNameB] do differs (C ++ `topShips_transport) mu; nm := nm + 1
  same (C ++ `noRawBelowB_sound) ``ExpNoRawSound
  differs (C ++ `noRawBelowB_sound) ``MutNoRawSoundConv; nm := nm + 1
  same (C ++ `instsNeB_sound) ``ExpInstsNeSound
  differs (C ++ `instsNeB_sound) ``MutInstsNeSoundEq; nm := nm + 1
  for r in [`counterLoop, `shift4Loop, `counterEnableLoop, `arbiterSignal] do
    let rn := r.toString
    let t := R ++ Name.mkSimple (rn ++ "_final10")
    let tr := `Tests.Gen5.FGCircuitPilotCheck8 ++ Name.mkSimple ("F10True_" ++ rn)
    same t tr
    for mu in ["M10HeadEnd_", "M10LinkEnd_", "M10ConclEnd_", "M10Data_", "M10Post_"] do
      differs t (`Tests.Gen5.FGCircuitPilotCheck8 ++ Name.mkSimple (mu ++ rn)); nm := nm + 1
    -- another root's statement
    for r' in [`counterLoop, `shift4Loop, `counterEnableLoop, `arbiterSignal] do
      if r' != r then differs t (`Tests.Gen5.FGCircuitPilotCheck8 ++ Name.mkSimple ("F10True_" ++ r'.toString)); nm := nm + 1
  logInfo m!"FGCIRCUIT8 SIGNATURES: envFrame_coreHead, root_find_of_headAt, machineDefinesLinked_of_headAt, counterLoop_final9/9C, CheckedEnv.mk, CheckedStart.mk, HeadIO.mk, startFacts_of_checked, X_final10 (4 roots), boundaryRows_of_contains, topShips_transport, noRawBelowB_sound, instsNeB_sound: complete types match the independently written statements; {nm} mutants rejected (head fact for another root / at another run's world / at the end world, ReadsAt and CheckedStart at the end world, dropped head / cell / IO / read / NoRawBelow premises, another env / root / Post / data, another root's final theorem, transport reversed)"

/-! ## 2. the hypotheses that remain -/

run_cmd liftTermElabM do
  let H := `Tools.ShippingFGCircuitS1iHead
  let R := `Tools.ShippingFGCircuitS1iRoots
  let C := `Tools.ShippingFGCircuitS1iChild
  let check (thm : Name) (expected : List String) : MetaM Unit := do
    let bs ← explicitBinders thm
    let names := (bs.map (·.1)).filter fun n => !(n.splitOn "_@").length.succ.pred.beq 2 && !n.startsWith "a._@"
    unless names == expected do throwError "{thm}: hypotheses are {names}, expected {expected}"
    for gone in ["hquiet", "hg", "hw", "hA6", "hsrc", "htr", "hd", "hdRun", "hc", "hcl", "hP", "hl", "hTop", "hpost", "hsnap", "hgates", "hRead", "hE"] do
      if names.contains gone then throwError "{thm}: {gone} is a hypothesis"
    for (n, t) in bs do
      let cs := t.getUsedConstants
      if cs.contains ``sorryAx then throwError "{thm}: hypothesis {n} mentions sorryAx"
      if cs.contains ``Tools.ShippingChildInvA.RefLawsAOps.quiet then throwError "{thm}: hypothesis {n} quantifies over the quiet predicate (hquiet)"
      if cs.contains ``Tools.ShippingEnvSnapshot.GetEnvFrame then throwError "{thm}: hypothesis {n} is GetEnvFrame"
      if cs.contains ``Tools.ShippingEnvSnapshot.EnvFrame then throwError "{thm}: hypothesis {n} is an all-worlds EnvFrame"
      if cs.contains ``Tools.ShippingGen5FG.EntryWitness then throwError "{thm}: hypothesis {n} is EntryWitness"
      if cs.contains ``Tools.ShippingFGCircuitBridge.DesignTransport then throwError "{thm}: hypothesis {n} is DesignTransport"
      if cs.contains ``Tools.ShippingMachineEntry.MachineDefines then throwError "{thm}: hypothesis {n} is the global MachineDefines"
      if cs.contains ``MachineDefinesLinked then throwError "{thm}: hypothesis {n} is MachineDefinesLinked (derived)"
    for (n, t) in bs do
      let pp ← try pure (toString (← ppExpr t)) catch _ => pure s!"<unprintable; constants: {t.getUsedConstants.toList.map (·.toString)}>"
      logInfo m!"FGCIRCUIT8 REMAINING {thm.getString!} {n} : {pp}"
  check (H ++ `counterLoop_final9) ["L", "lvl", "env₀", "hstart", "hr", "hhead", "hcell", "hread", "hgatesB", "hquote", "hreader"]
  check (H ++ `counterLoop_final9C) ["L", "lvl", "env₀", "hstart", "hr", "hcell", "hio", "hread", "hgatesB", "hquote", "hreader"]
  check (R ++ `counterLoop_final10) ["L", "lvl", "env₀", "hstart", "hr", "hhead", "hcell", "hchk"]
  check (R ++ `shift4Loop_final10) ["L", "lvl", "env₀", "hstart", "hr", "hhead", "hcell", "hchk"]
  check (R ++ `counterEnableLoop_final10) ["L", "lvl", "env₀", "hstart", "hr", "hhead", "hcell", "hchk"]
  check (R ++ `arbiterSignal_final10) ["L", "lvl", "env₀", "hstart", "hr", "hhead", "hcell", "hchk", "hB0", "hcont"]
  check (C ++ `topShips_transport) ["p", "n", "X", "hpe", "hnoRaw", "hnoOpt", "hnoB"]
  logInfo "FGCIRCUIT8 HYPS: final10 = L lvl env₀ hstart hr hhead(HeadAt: the run's start world only) hcell(ReadWorld cref) hchk(CheckedStart: env₀ facts + ReadsAt env₀ cref w); arbiter + hB0 (BoundaryRowsInEnv env₀) + hcont (ContainsAt: converse inclusion on 3 names). final9C: hhead from hcell(CellPrem) + hio(HeadIO: 2 IO facts). NOT hypotheses: hquiet, GetEnvFrame, all-worlds EnvFrame(coreHead), hdRun, MachineDefinesLinked, hsrc, DesignTransport, hw, hgates/hRead/hE of the start environment"

/-! ## 3. axioms -/
run_cmd liftTermElabM do
  let H := `Tools.ShippingFGCircuitS1iHead
  let E := `Tools.ShippingFGCircuitS1iEnv
  let R := `Tools.ShippingFGCircuitS1iRoots
  let C := `Tools.ShippingFGCircuitS1iChild
  let names : List Name := [H ++ `envFrame_coreHead, H ++ `headAt_of_frame, H ++ `headAt_of_cellPrem, H ++ `readsAt_after_headAt, H ++ `root_find_of_headAt,
    H ++ `machineDefinesLinked_of_headAt, H ++ `machineDefinesLinked_of_reader_headAt, H ++ `counterLoop_final9, H ++ `counterLoop_final9C,
    E ++ `quoteAt_of_rootInEnv, E ++ `entry₀_of_rootInEnv, E ++ `entryGatesB_of_rootInEnv, E ++ `startFacts_of_checked, E ++ `find_eq_of_checked,
    R ++ `shift4Loop_final4D, R ++ `counterEnableLoop_final4D, R ++ `arbiterSignal_final4D, R ++ `boundaryRows_of_contains,
    R ++ `counterLoop_final10, R ++ `shift4Loop_final10, R ++ `counterEnableLoop_final10, R ++ `arbiterSignal_final10,
    C ++ `bodyInstOuts_congr, C ++ `topShips_transport, C ++ `designTransport_of_noRawBelow, C ++ `noRawBelowB_sound, C ++ `instsNeB_sound]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT8 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

/-! ## 4. SNAPSHOT8: ONE environment, and the design of a real compile of a non-leaf -/

/-- the non-leaf body of `synth_hftPcieOutByte` (that definition is `private` in a test file) -/
def hftOutProbe
    (rxByte : Signal defaultDomain (BitVec 8))
    (rxValid sopTlp : Signal defaultDomain Bool)
    (dataDword : Signal defaultDomain (BitVec 32))
    (cplId : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain (BitVec 8) :=
  (Sparkle.IP.Bus.PCIeHFT.hftPcieLoop rxByte rxValid sopTlp dataDword cplId).outByte

def rootB (env : Environment) (x : Name) (ty val : Lean.Expr) : Bool :=
  match env.find? x with
  | some (.defnInfo d) => d.levelParams.isEmpty && d.type == ty && d.value == val
  | _ => false

def boundaryB (env : Environment) : Bool :=
  [(`stIdle, 0), (`stGrantA, 1), (`stGrantB, 2)].all fun (nm, k) =>
    match env.find? (privAbbrev nm) with
    | some (.defnInfo d) => d.levelParams.isEmpty && d.type == eBV 2 && d.value == eBVLit 2 k
    | _ => false

def instNames (m : Sparkle.IR.AST.Module) : List String :=
  m.body.filterMap fun s => match s with | .inst mn _ _ => some mn | _ => none

run_cmd liftTermElabM do
  let env ← getEnv
  let roots : List (Name × Name × Lean.Expr × Lean.Expr) :=
    [(``Sparkle.Tests.SignalLoopTest.counterLoop, ``Sparkle.Tests.SignalLoopTest.counterLoop.machineData, counterLoopType, counterLoopValue),
     (``Sparkle.Tests.SignalLoopTest.shift4Loop, ``Sparkle.Tests.SignalLoopTest.shift4Loop.machineData, shift4LoopType, shift4LoopValue),
     (``Sparkle.Tests.SignalLoopTest.counterEnableLoop, ``Sparkle.Tests.SignalLoopTest.counterEnableLoop.machineData, counterEnableLoopType, counterEnableLoopValue),
     (``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal, ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData, arbiterType, arbiterValue)]
  for (x, l, ty, val) in roots do
    -- CheckedEnv.root (on types: a closed declaration) and CheckedEnv.gates (evaluation)
    unless rootB env x ty val do throwError "{x}: CheckedEnv.root does not hold on this environment"
    unless entryGatesB env x do throwError "{x}: entryGatesB is false"
    -- the gate checker equals the pair of isNone tests on the entry constant (entryGatesB_of_rootInEnv, evaluated)
    for (_, _, ty', val') in roots do
      if ty' != ty && rootB env x ty' val' then throwError "{x}: root mutant accepted"
    Tests.Gen5.FGCircuitPilotCheck6.snapshotRoot x l   -- ReaderAt content: machineShape?/dataOfAt = machineData, whole structure, with 10 one-field perturbations rejected
  unless boundaryB env do throwError "BoundaryRowsInEnv does not hold on this environment"
  -- negative control for the boundary checker: a wrong literal
  unless !([(`stIdle, 1)].all fun (nm, k) => match env.find? (privAbbrev nm) with
    | some (.defnInfo d) => d.value == eBVLit 2 k | _ => false) do throwError "boundary mutant accepted"
  logInfo "FGCIRCUIT8 SNAPSHOT8a: on this build's ONE environment: CheckedEnv.root (closed declaration with the pilot's type and value) holds for the four roots, entryGatesB is true, ReaderAt content equals machineData (whole structure; SNAPSHOT6), BoundaryRowsInEnv holds for the arbiter's three constants; mutants rejected. ContainsAt/ReadsAt compare TWO environments (env₀ and a start world's) and are not evaluated here"

run_cmd liftTermElabM do
  let env ← getEnv
  let x := ``hftOutProbe
  -- machine route with children
  let some ci := env.find? x | throwError "hftOutProbe missing"
  let E := entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)
  unless (certifiedShape? false [] E).isNone && (mixedCertifiedShape? false [] E (instancePredicate env)).isNone do throwError "hftOutProbe: not a machine-route root"
  let some sh := machineShape? false [] E (structEnv env) | throwError "hftOutProbe: machineShape? is none"
  unless sh.insts.length == 2 do throwError "hftOutProbe: insts {sh.insts.length}"
  unless entryGatesB env x do throwError "hftOutProbe: entryGatesB false"
  -- the leaf lemma does not apply: LeafFacts requires insts = []
  -- a real compile
  let (raw, D₀) ← synthesizeCombinationalCore x [] false
  let (b, D') ← synthesizeCombinational x
  let kids := instNames raw
  unless kids.length == 2 do throwError "raw has {kids.length} instances"
  -- PostEntry on this output (the first disjunct, identity merge): b = dropZeroWidth raw, D' = topMap … D₀ (D₀ does not contain the top module)
  unless b == Sparkle.IR.ZeroWidth.dropZeroWidthModule raw || b == Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) do throwError "b is neither disjunct of PostEntry"
  unless D'.modules == D₀.modules do throwError "D'.modules ≠ D₀.modules"
  -- the side conditions of topShips_transport, evaluated on this design for several depths n
  for n in [0, 1, 2, 3, 4, 5] do
    unless noRawBelowB D₀ raw.name (n + 1) raw do throwError "NoRawBelow raw fails at depth {n}"
    unless noRawBelowB D₀ raw.name (n + 1) (Sparkle.IR.OptCheck.checkedOptimize b) do throwError "NoRawBelow (checkedOptimize b) fails at depth {n}"
  unless instsNeB raw.name b.body do throwError "an instance of b names the top"
  -- negative controls: the checkers can reject (a child named as the top)
  for k in kids do
    if noRawBelowB D₀ k 2 raw then throwError "noRawBelowB accepted a design whose child is the 'top' {k}"
    if instsNeB k raw.body then throwError "instsNeB accepted"
  logInfo m!"FGCIRCUIT8 SNAPSHOT8b (non-leaf, hftPcie body = synth_hftPcieOutByte's): machine route (certified none, mixed none, machineShape? some, insts {sh.insts.length}, slots {sh.layout.slots.length}); real compile: raw instances {kids}, D₀ modules {D₀.modules.map (·.name)}, D' modules equal; NoRawBelow of raw and of checkedOptimize b hold for depths 1..6 and no instance of b names the top (checker true); controls (child as top) false. PostEntry: b = dropZeroWidth raw (first disjunct). This is ONE compile, not a kernel statement about every run"

-- a leaf for contrast: the leaf lemma's condition insts = []
run_cmd liftTermElabM do
  let env ← getEnv
  let some ci := env.find? ``counterLoop | throwError "missing"
  let E := entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)
  let some sh := machineShape? false [] E (structEnv env) | throwError "none"
  unless sh.insts.length == 0 do throwError "counterLoop has instances"
  logInfo "FGCIRCUIT8 SNAPSHOT8c: counterLoop (leaf) has insts = [] (LeafFacts' condition), hftOutProbe has 2"

end Tests.Gen5.FGCircuitPilotCheck8
