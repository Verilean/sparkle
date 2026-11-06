import Tests.Gen5.FGCircuitPilotCheck6
import Tools.ShippingFGCircuitS1hQuote
set_option autoImplicit false
-- FG circuit pilot S1h check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §13.

/-! # FGCircuitPilotCheck7

1. SIGNATURES: complete expected types written independently of the theorems (compared by `isDefEq` at default transparency after `norm` unfolds the whitelisted definitions; `isDefEq` itself may unfold further definitions, so the whitelist does not bound what is unfolded) for
   `getEnvFrame_of_readWorld`, `machineDefinesLinked_of_head`, `root_find_of_head`, `counterLoop_final6/7/8`, `entryGatesB_sound/complete`, `entryGatesB_of_readsAt`, `quoteAt_of_readsAt`, `readerAt_of_readsAt`.
   MUTANTS: a cut connection (the head frame of another root; `ReadsAt` at the end world; a premise dropped), another run's world, another env / root / Post / data, the transfer in the wrong direction.
2. HYPS: the explicit hypotheses of the final theorems, by name and type (no `hquiet`, no `GetEnvFrame`, no `hw`/`hsrc`/`hdRun`).
3. AXIOMS of every new name.
4. SNAPSHOT7: on this build's ONE environment, the compiled checker `entryGatesB` is `true` for the four roots (and `false` for a certified combinational control), `QuoteAt` holds on the four roots, `ReaderAt` is the SNAPSHOT6 check.
   These are values of ONE environment and not kernel statements about an arbitrary run's start environment. -/
namespace Tests.Gen5.FGCircuitPilotCheck7
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitLinked Tools.ShippingFGCircuitFinal4 Tools.ShippingFGCircuitRoots4
open Tools.ShippingFGCircuitS1hFrame Tools.ShippingFGCircuitS1hGates Tools.ShippingFGCircuitS1hQuote
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt CoreSaved coreHead)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingStRefCorrespondence (ReadWorld)
open Sparkle.Compiler.Elab Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises
open Tests.Gen5.FGCircuitPilotCheck5 (W GPd EnvStart EnvEnd dataExprOf shapeExprOf literalExpr perturbations ppAll binderInfos explicitBinders)
open Tests.Gen5.FGCircuitPilotCheck6 (ExpMDLTrue ExpGates ExpQuoteAt ExpReaderAt)

/-! ## 1. expected statements, written independently -/

def ExpGatesB (env : Environment) (X : Name) : Bool :=
  match (env.find? X).map fun ci => entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env) with
  | none => true
  | some E => (certifiedShape? false [] E).isNone && (mixedCertifiedShape? false [] E (instancePredicate env)).isNone

/-- `getEnvFrame_of_readWorld` (the frame of `getEnv`, written out) -/
def ExpGetEnvRW (conclEq : Environment → Environment → Prop) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State},
    ReadWorld cref → ∀ (w : W) (a : Environment) (w' : W),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w a w' → conclEq (envAt cref w') (envAt cref w)
abbrev GetEnvTrue := ExpGetEnvRW (fun a b => a = b)
def MutGetEnvConcl := ExpGetEnvRW (fun a _ => a = a)
def MutGetEnvNoCell : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State},
    ∀ (w : W) (a : Environment) (w' : W),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w a w' → envAt cref w' = envAt cref w

/-- `machineDefinesLinked_of_head`. Knobs: the root whose `coreHead` is framed, the environment of the lookup, of the gates. -/
def ExpHead (hn : Name → Name) (eF eG : ST.Ref IO.RealWorld Core.State → W → W → Environment) (wsel : W → W → W) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {X : Name} {shape : MachineShape} {ci₀ : ConstantInfo} {w w' : W} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    Tools.ShippingEnvSnapshot.EnvFrame (coreHead (hn X)) mctx mref cctx cref →
    Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref →
    (eF cref w w').find? X = some ci₀ →
    certifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate (eG cref w w')) (userInliner (eG cref w w')) (structEnv (eG cref w w'))) = none →
    mixedCertifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate (eG cref w w')) (userInliner (eG cref w w')) (structEnv (eG cref w w'))) (instancePredicate (eG cref w w')) = none →
    machineShape? false [] (entryConst true false [] ci₀ (instancePredicate (eG cref w w')) (userInliner (eG cref w w')) (structEnv (eG cref w w'))) (structEnv (eG cref w w')) = some shape →
    ExpMDLTrue mctx mref cctx cref X shape (wsel w w') M D w'
abbrev HeadTrue := ExpHead (fun x => x) EnvStart EnvStart (fun w _ => w)
def MutHeadRoot := ExpHead (fun _ => ``shift4Loop) EnvStart EnvStart (fun w _ => w)
def MutHeadFind := ExpHead (fun x => x) EnvEnd EnvStart (fun w _ => w)
def MutHeadGates := ExpHead (fun x => x) EnvStart EnvEnd (fun w _ => w)
def MutHeadWorld := ExpHead (fun x => x) EnvStart EnvStart (fun _ w' => w')

def ExpRootFindHead (hn : Name → Name) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {X : Name} {w w' : W} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    Tools.ShippingEnvSnapshot.EnvFrame (coreHead (hn X)) mctx mref cctx cref →
    RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (M, D) w' →
    ∃ ci : ConstantInfo, (envAt cref w).find? X = some ci
abbrev RootFindTrue := ExpRootFindHead (fun x => x)
def MutRootFindRoot := ExpRootFindHead (fun _ => ``shift4Loop)

/-- `counterLoop_final6`.  Knobs: the root of the head frame, the environments of gates / reader / root, of the conclusion, the data, the Post root. -/
def ExpF6 (hroot : Name) (eG eR eE eC : ST.Ref IO.RealWorld Core.State → W → W → Environment) (dd : MachineData) (postRoot : Name) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {ι : Type}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    Tools.ShippingEnvSnapshot.EnvFrame (coreHead hroot) mctx mref cctx cref →
    ReadWorld cref →
    ExpGates (eG cref w w') ``counterLoop →
    RootReader lvl (eR cref w w') ``counterLoop dd →
    RootInEnv (eE cref w w') ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (eC cref w w') (GPd lvl (eC cref w w')) (PostRun mctx mref cctx cref w postRoot D') ``counterLoop shCounter mm b D' p
abbrev F6True := ExpF6 ``counterLoop EnvStart EnvStart EnvStart EnvStart counterLoop.machineData ``counterLoop
def M6Head := ExpF6 ``shift4Loop EnvStart EnvStart EnvStart EnvStart counterLoop.machineData ``counterLoop
def M6G := ExpF6 ``counterLoop EnvEnd EnvStart EnvStart EnvStart counterLoop.machineData ``counterLoop
def M6R := ExpF6 ``counterLoop EnvStart EnvEnd EnvStart EnvStart counterLoop.machineData ``counterLoop
def M6E := ExpF6 ``counterLoop EnvStart EnvStart EnvEnd EnvStart counterLoop.machineData ``counterLoop
def M6C := ExpF6 ``counterLoop EnvStart EnvStart EnvStart EnvEnd counterLoop.machineData ``counterLoop
def M6Data := ExpF6 ``counterLoop EnvStart EnvStart EnvStart EnvStart shift4Loop.machineData ``counterLoop
def M6Post := ExpF6 ``counterLoop EnvStart EnvStart EnvStart EnvStart counterLoop.machineData ``shift4Loop
/-- a cut connection: no head frame -/
def M6NoHead : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {ι : Type}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    ReadWorld cref →
    ExpGates (envAt cref w) ``counterLoop →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd lvl (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p
/-- a cut connection: no cell premise (`ReadWorld cref`) -/
def M6NoCell : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {ι : Type}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    Tools.ShippingEnvSnapshot.EnvFrame (coreHead ``counterLoop) mctx mref cctx cref →
    ExpGates (envAt cref w) ``counterLoop →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd lvl (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p

/-- `counterLoop_final7` (gates by the checker; explicit binder order of that file) -/
def ExpF7 (hroot : Name) (eG eR eE eC : ST.Ref IO.RealWorld Core.State → W → W → Environment) (dd : MachineData) (postRoot : Name) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {mctx : Meta.Context} {cctx : Core.Context}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    Tools.ShippingEnvSnapshot.EnvFrame (coreHead hroot) mctx mref cctx cref →
    ReadWorld cref →
    ExpGatesB (eG cref w w') ``counterLoop = true →
    RootReader lvl (eR cref w w') ``counterLoop dd →
    RootInEnv (eE cref w w') ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (eC cref w w') (GPd lvl (eC cref w w')) (PostRun mctx mref cctx cref w postRoot D') ``counterLoop shCounter mm b D' p
abbrev F7True := ExpF7 ``counterLoop EnvStart EnvStart EnvStart EnvStart counterLoop.machineData ``counterLoop
def M7Head := ExpF7 ``shift4Loop EnvStart EnvStart EnvStart EnvStart counterLoop.machineData ``counterLoop
def M7G := ExpF7 ``counterLoop EnvEnd EnvStart EnvStart EnvStart counterLoop.machineData ``counterLoop
def M7Data := ExpF7 ``counterLoop EnvStart EnvStart EnvStart EnvStart shift4Loop.machineData ``counterLoop
def M7Post := ExpF7 ``counterLoop EnvStart EnvStart EnvStart EnvStart counterLoop.machineData ``shift4Loop

/-- `counterLoop_final8`: the evaluation facts are about `env₀`, tied to the START world by `ReadsAt env₀ cref w`.
Knobs: the world `ReadsAt` is asserted at, the environments of gates / quote / reader / conclusion, the head root, the data, the Post root. -/
def ExpF8 (hroot : Name) (rw : W → W → W) (eG eK eD eC : Environment → ST.Ref IO.RealWorld Core.State → W → W → Environment) (dd : MachineData) (postRoot : Name) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {mctx : Meta.Context} {cctx : Core.Context}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment) {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    Tools.ShippingEnvSnapshot.EnvFrame (coreHead hroot) mctx mref cctx cref →
    ReadWorld cref →
    Tools.ShippingGen5Env.ReadsAt env₀ cref (rw w w') →
    ExpGatesB (eG env₀ cref w w') ``counterLoop = true →
    ExpQuoteAt (eK env₀ cref w w') ``counterLoop counterLoopType counterLoopValue →
    ExpReaderAt lvl (eD env₀ cref w w') ``counterLoop dd →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (eC env₀ cref w w') (GPd lvl (eC env₀ cref w w')) (PostRun mctx mref cctx cref w postRoot D') ``counterLoop shCounter mm b D' p
abbrev Z0 : Environment → ST.Ref IO.RealWorld Core.State → W → W → Environment := fun e _ _ _ => e
abbrev ZS : Environment → ST.Ref IO.RealWorld Core.State → W → W → Environment := fun _ c w _ => envAt c w
abbrev ZE : Environment → ST.Ref IO.RealWorld Core.State → W → W → Environment := fun _ c _ w' => envAt c w'
abbrev F8True := ExpF8 ``counterLoop (fun w _ => w) Z0 Z0 Z0 ZS counterLoop.machineData ``counterLoop
-- the three evaluation facts in the START environment instead of `env₀` (these are the S1g premises; a different theorem), and other cut connections
def M8GatesStart := ExpF8 ``counterLoop (fun w _ => w) ZS Z0 Z0 ZS counterLoop.machineData ``counterLoop
def M8QuoteEnd := ExpF8 ``counterLoop (fun w _ => w) Z0 ZE Z0 ZS counterLoop.machineData ``counterLoop
def M8ReaderEnd := ExpF8 ``counterLoop (fun w _ => w) Z0 Z0 ZE ZS counterLoop.machineData ``counterLoop
def M8ConclEnv0 := ExpF8 ``counterLoop (fun w _ => w) Z0 Z0 Z0 Z0 counterLoop.machineData ``counterLoop
def M8ConclEnd := ExpF8 ``counterLoop (fun w _ => w) Z0 Z0 Z0 ZE counterLoop.machineData ``counterLoop
/-- another run's world: `ReadsAt` at the END world of the run -/
def M8ReadsEnd := ExpF8 ``counterLoop (fun _ w' => w') Z0 Z0 Z0 ZS counterLoop.machineData ``counterLoop
def M8Head := ExpF8 ``shift4Loop (fun w _ => w) Z0 Z0 Z0 ZS counterLoop.machineData ``counterLoop
def M8Data := ExpF8 ``counterLoop (fun w _ => w) Z0 Z0 Z0 ZS shift4Loop.machineData ``counterLoop
def M8Post := ExpF8 ``counterLoop (fun w _ => w) Z0 Z0 Z0 ZS counterLoop.machineData ``shift4Loop
def M8NoRead : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {mctx : Meta.Context} {cctx : Core.Context}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment) {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    Tools.ShippingEnvSnapshot.EnvFrame (coreHead ``counterLoop) mctx mref cctx cref →
    ReadWorld cref →
    ExpGatesB env₀ ``counterLoop = true →
    ExpQuoteAt env₀ ``counterLoop counterLoopType counterLoopValue →
    ExpReaderAt lvl env₀ ``counterLoop counterLoop.machineData →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd lvl (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p

/-- the checker is sound / complete for `EntryGates` -/
def ExpSound : Prop := ∀ {env : Environment} {X : Name}, ExpGatesB env X = true → ExpGates env X
def ExpComplete : Prop := ∀ {env : Environment} {X : Name}, ExpGates env X → ExpGatesB env X = true
def MutSoundFalse : Prop := ∀ {env : Environment} {X : Name}, ExpGatesB env X = false → ExpGates env X
def MutSoundOtherX : Prop := ∀ {env : Environment} {X Y : Name}, ExpGatesB env X = true → ExpGates env Y

/-- transfers along `ReadsAt env₀ cref w` -/
def ExpXferGates : Prop :=
  ∀ {cref : ST.Ref IO.RealWorld Core.State} {w : W} {env₀ : Environment} {X : Name},
    Tools.ShippingGen5Env.ReadsAt env₀ cref w → ExpGatesB env₀ X = true → ExpGatesB (envAt cref w) X = true
abbrev ExpXferGatesTrue := ExpXferGates
def MutXferGatesRev : Prop :=
  ∀ {cref : ST.Ref IO.RealWorld Core.State} {w : W} {env₀ : Environment} {X : Name},
    Tools.ShippingGen5Env.ReadsAt env₀ cref w → ExpGatesB (envAt cref w) X = true → ExpGatesB env₀ X = true
def ExpXferQuote : Prop :=
  ∀ {cref : ST.Ref IO.RealWorld Core.State} {w : W} {env₀ : Environment} {X : Name} {ty val : Lean.Expr},
    Tools.ShippingGen5Env.ReadsAt env₀ cref w → ExpQuoteAt env₀ X ty val → ExpQuoteAt (envAt cref w) X ty val
def MutXferQuoteRev : Prop :=
  ∀ {cref : ST.Ref IO.RealWorld Core.State} {w : W} {env₀ : Environment} {X : Name} {ty val : Lean.Expr},
    Tools.ShippingGen5Env.ReadsAt env₀ cref w → ExpQuoteAt (envAt cref w) X ty val → ExpQuoteAt env₀ X ty val
def ExpXferReader : Prop :=
  ∀ {cref : ST.Ref IO.RealWorld Core.State} {w : W} {env₀ : Environment} {X : Name} {lvl : Lean.Expr → Nat} {dd : MachineData},
    Tools.ShippingGen5Env.ReadsAt env₀ cref w → ExpReaderAt lvl env₀ X dd → ExpReaderAt lvl (envAt cref w) X dd
def MutXferReaderRev : Prop :=
  ∀ {cref : ST.Ref IO.RealWorld Core.State} {w : W} {env₀ : Environment} {X : Name} {lvl : Lean.Expr → Nat} {dd : MachineData},
    Tools.ShippingGen5Env.ReadsAt env₀ cref w → ExpReaderAt lvl (envAt cref w) X dd → ExpReaderAt lvl env₀ X dd

def whitelist : List Name := [``ExpGatesB, ``ExpGetEnvRW, ``GetEnvTrue, ``MutGetEnvConcl, ``MutGetEnvNoCell, ``ExpHead, ``HeadTrue, ``MutHeadRoot, ``MutHeadFind, ``MutHeadGates, ``MutHeadWorld,
  ``ExpRootFindHead, ``RootFindTrue, ``MutRootFindRoot, ``ExpF6, ``F6True, ``M6Head, ``M6G, ``M6R, ``M6E, ``M6C, ``M6Data, ``M6Post, ``M6NoHead, ``M6NoCell,
  ``ExpF7, ``F7True, ``M7Head, ``M7G, ``M7Data, ``M7Post, ``ExpF8, ``Z0, ``ZS, ``ZE, ``F8True, ``M8GatesStart, ``M8QuoteEnd, ``M8ReaderEnd, ``M8ConclEnv0, ``M8ConclEnd, ``M8ReadsEnd, ``M8Head, ``M8Data, ``M8Post, ``M8NoRead,
  ``ExpSound, ``ExpComplete, ``MutSoundFalse, ``MutSoundOtherX, ``ExpXferGates, ``ExpXferGatesTrue, ``MutXferGatesRev, ``ExpXferQuote, ``MutXferQuoteRev, ``ExpXferReader, ``MutXferReaderRev,
  ``Tests.Gen5.FGCircuitPilotCheck5.GPd, ``Tests.Gen5.FGCircuitPilotCheck5.EnvStart, ``Tests.Gen5.FGCircuitPilotCheck5.EnvEnd,
  ``Tests.Gen5.FGCircuitPilotCheck6.ExpMDLTrue, ``Tests.Gen5.FGCircuitPilotCheck6.ExpMDL, ``Tests.Gen5.FGCircuitPilotCheck6.ExpGates, ``Tests.Gen5.FGCircuitPilotCheck6.ExpQuoteAt, ``Tests.Gen5.FGCircuitPilotCheck6.ExpReaderAt,
  -- the definitions under test are unfolded too
  ``MachineDefinesLinked, ``EntryGates, ``entryGatesB, ``Tools.ShippingGen5Acc.entry₀, ``QuoteAt, ``ReaderAt,
  ``Tools.ShippingEnvSnapshot.GetEnvFrame, ``Tools.ShippingEnvSnapshot.EnvFrame]

def norm (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if whitelist.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    -- `if true then A else B` / `if false then A else B` of the `dir` knobs
    return .done e)

set_option maxHeartbeats 8000000 in
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
  let S := `Tools.ShippingFGCircuitS1hFrame
  let G := `Tools.ShippingFGCircuitS1hGates
  let Q := `Tools.ShippingFGCircuitS1hQuote
  same (S ++ `getEnvFrame_of_readWorld) ``GetEnvTrue
  same (S ++ `machineDefinesLinked_of_head) ``HeadTrue
  same (S ++ `root_find_of_head) ``RootFindTrue
  same (S ++ `counterLoop_final6) ``F6True
  same (G ++ `counterLoop_final7) ``F7True
  same (Q ++ `counterLoop_final8) ``F8True
  let mut nm : Nat := 0
  for mu in [``MutGetEnvConcl, ``MutGetEnvNoCell] do differs (S ++ `getEnvFrame_of_readWorld) mu; nm := nm + 1
  for mu in [``MutHeadRoot, ``MutHeadFind, ``MutHeadGates, ``MutHeadWorld] do differs (S ++ `machineDefinesLinked_of_head) mu; nm := nm + 1
  differs (S ++ `root_find_of_head) ``MutRootFindRoot; nm := nm + 1
  for mu in [``M6Head, ``M6G, ``M6R, ``M6E, ``M6C, ``M6Data, ``M6Post, ``M6NoHead, ``M6NoCell] do differs (S ++ `counterLoop_final6) mu; nm := nm + 1
  for mu in [``M7Head, ``M7G, ``M7Data, ``M7Post] do differs (G ++ `counterLoop_final7) mu; nm := nm + 1
  for mu in [``M8GatesStart, ``M8QuoteEnd, ``M8ReaderEnd, ``M8ConclEnv0, ``M8ConclEnd, ``M8ReadsEnd, ``M8Head, ``M8Data, ``M8Post, ``M8NoRead] do differs (Q ++ `counterLoop_final8) mu; nm := nm + 1
  same (G ++ `entryGatesB_sound) ``ExpSound
  same (G ++ `entryGatesB_complete) ``ExpComplete
  same (Q ++ `entryGatesB_of_readsAt) ``ExpXferGatesTrue
  same (Q ++ `quoteAt_of_readsAt) ``ExpXferQuote
  same (Q ++ `readerAt_of_readsAt) ``ExpXferReader
  for mu in [``MutSoundFalse, ``MutSoundOtherX, ``ExpComplete] do differs (G ++ `entryGatesB_sound) mu; nm := nm + 1
  differs (G ++ `entryGatesB_complete) ``ExpSound; nm := nm + 1
  differs (Q ++ `entryGatesB_of_readsAt) ``MutXferGatesRev; nm := nm + 1
  differs (Q ++ `quoteAt_of_readsAt) ``MutXferQuoteRev; nm := nm + 1
  differs (Q ++ `readerAt_of_readsAt) ``MutXferReaderRev; nm := nm + 1
  -- cross-version mutants: the final6 statement is not final7's / final8's
  for (t, mu) in [(S ++ `counterLoop_final6, ``F7True), (G ++ `counterLoop_final7, ``F6True), (Q ++ `counterLoop_final8, ``F7True)] do differs t mu; nm := nm + 1
  logInfo m!"FGCIRCUIT7 SIGNATURES: getEnvFrame_of_readWorld, machineDefinesLinked_of_head, root_find_of_head, counterLoop_final6/7/8, entryGatesB_sound/complete, entryGatesB_of_readsAt, quoteAt_of_readsAt, readerAt_of_readsAt: complete types match the independently written statements; {nm} mutants rejected (head frame of another root, ReadsAt at the end world, dropped head / cell / read premises, another env / root / Post / data, checker vs prop, S1g premises in place of env₀ premises)"

/-! ## 2. the hypotheses that remain -/

run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1hFrame
  let G := `Tools.ShippingFGCircuitS1hGates
  let Q := `Tools.ShippingFGCircuitS1hQuote
  let check (thm : Name) (expected : List String) : MetaM Unit := do
    let bs ← explicitBinders thm
    let names := bs.map (·.1)
    unless names == expected do throwError "{thm}: hypotheses are {names}, expected {expected}"
    for gone in ["hquiet", "hg", "hw", "hA6", "hsrc", "htr", "hd", "hdRun", "hc", "hcl", "hP", "hl", "hTop", "hpost", "hsnap"] do
      if names.contains gone then throwError "{thm}: {gone} is a hypothesis"
    for (n, t) in bs do
      let cs := t.getUsedConstants
      if cs.contains ``sorryAx then throwError "{thm}: hypothesis {n} mentions sorryAx"
      if cs.contains ``Tools.ShippingChildInvA.RefLawsAOps.quiet then throwError "{thm}: hypothesis {n} quantifies over the quiet predicate (hquiet)"
      if cs.contains ``Tools.ShippingEnvSnapshot.GetEnvFrame then throwError "{thm}: hypothesis {n} is GetEnvFrame"
      if cs.contains ``Tools.ShippingGen5FG.EntryWitness then throwError "{thm}: hypothesis {n} is EntryWitness"
      if cs.contains ``Tools.ShippingFGCircuitBridge.DesignTransport then throwError "{thm}: hypothesis {n} is DesignTransport"
      if cs.contains ``Tools.ShippingMachineEntry.MachineDefines then throwError "{thm}: hypothesis {n} is the global MachineDefines"
      if cs.contains ``MachineDefinesLinked then throwError "{thm}: hypothesis {n} is MachineDefinesLinked (derived)"
    let ci ← getConstInfo thm
    for o in [``Sparkle.Tests.SignalLoopTest.shift4Loop, ``Sparkle.Tests.SignalLoopTest.counterEnableLoop, ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal] do
      if ci.type.getUsedConstants.contains o then throwError "{thm}: mentions another root {o}"
    for (n, t) in bs do
      let pp ← try pure (toString (← ppExpr t)) catch _ => pure s!"<unprintable; constants: {t.getUsedConstants.toList.map (·.toString)}>"
      logInfo m!"FGCIRCUIT7 REMAINING {thm.getString!} {n} : {pp}"
  check (S ++ `counterLoop_final6) ["L", "lvl", "hstart", "hr", "hhead", "hcell", "hgates", "hRead", "hE"]
  check (G ++ `counterLoop_final7) ["L", "lvl", "hstart", "hr", "hhead", "hcell", "hgatesB", "hRead", "hE"]
  check (Q ++ `counterLoop_final8) ["L", "lvl", "env₀", "hstart", "hr", "hhead", "hcell", "hread", "hgatesB", "hquote", "hreader"]
  logInfo "FGCIRCUIT7 HYPS: final6 = L lvl hstart hr hhead hcell hgates hRead hE; final7 = gates by the checker; final8 = L lvl env₀ hstart hr hhead hcell hread hgatesB hquote hreader. NOT hypotheses: hquiet (quantifier over the quiet predicate), GetEnvFrame (derived from ReadWorld cref), hw / ReflectsAll, hA6, MachineDefines*, hsrc, hdRun, DesignTransport"

/-! ## 3. axioms -/
run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1hFrame
  let G := `Tools.ShippingFGCircuitS1hGates
  let Q := `Tools.ShippingFGCircuitS1hQuote
  let names : List Name := [S ++ `envFrame_of_envFrameEnd, S ++ `getEnvFrame_of_readWorld, S ++ `getEnvFrame_of_cellPrem, S ++ `hquiet_of_strength, S ++ `readsAt_after_head,
    S ++ `machineDefinesLinked_of_head, S ++ `root_find_of_head, S ++ `machineDefinesLinked_of_reader_head, S ++ `counterLoop_final6,
    G ++ `entryGatesB_sound, G ++ `entryGatesB_complete, G ++ `entryGatesB_iff, G ++ `not_entryGates_of_false, G ++ `counterLoop_final7,
    Q ++ `entry₀_of_readsAt, Q ++ `entryGatesB_of_readsAt, Q ++ `quoteAt_of_readsAt, Q ++ `readerAt_of_readsAt, Q ++ `counterLoop_final8]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT7 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

/-! ## 4. SNAPSHOT7: ONE environment -/

/-- a certified combinational control (not a root of the pilot) -/
def combControl (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := a + b

def quoteB (env : Environment) (x : Name) (ty val : Lean.Expr) : Bool :=
  match env.find? x with
  | none => true
  | some (.defnInfo d) => d.levelParams.isEmpty && d.type == ty && d.value == val
  | some _ => false

run_cmd liftTermElabM do
  let env ← getEnv
  let roots : List (Name × Name × Lean.Expr × Lean.Expr) :=
    [(``Sparkle.Tests.SignalLoopTest.counterLoop, ``Sparkle.Tests.SignalLoopTest.counterLoop.machineData, counterLoopType, counterLoopValue),
     (``Sparkle.Tests.SignalLoopTest.shift4Loop, ``Sparkle.Tests.SignalLoopTest.shift4Loop.machineData, shift4LoopType, shift4LoopValue),
     (``Sparkle.Tests.SignalLoopTest.counterEnableLoop, ``Sparkle.Tests.SignalLoopTest.counterEnableLoop.machineData, counterEnableLoopType, counterEnableLoopValue),
     (``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal, ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData, arbiterType, arbiterValue)]
  for (x, l, ty, val) in roots do
    unless entryGatesB env x do throwError "{x}: entryGatesB is false on this environment"
    unless quoteB env x ty val do throwError "{x}: the environment's constant is not the quoted definition"
    -- negative controls: another root's quote
    for (_, _, ty', val') in roots do
      if ty' != ty && quoteB env x ty' val' then throwError "{x}: quote mutant accepted"
    Tests.Gen5.FGCircuitPilotCheck6.snapshotRoot x l
  -- the checker can be false: a certified combinational control
  if entryGatesB env ``combControl then throwError "negative control: entryGatesB accepts a certified combinational definition"
  logInfo "FGCIRCUIT7 SNAPSHOT7: on this build's ONE environment, the compiled checker entryGatesB is TRUE for the four roots, quote (type/value) equals the pilot's constants, and the ReaderAt content (dataOfAt = machineData, whole structure) is SNAPSHOT6's; entryGatesB is FALSE for a certified combinational control (so the checker can reject). These are values of one environment: the kernel theorems take them as premises about env₀, tied to a run's start by ReadsAt env₀ cref w"

end Tests.Gen5.FGCircuitPilotCheck7
