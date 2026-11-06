import Tests.Gen5.FGCircuitPilotCheck5
import Tests.Gen5.FGCircuitPilotCheck4
import Tools.ShippingFGCircuitRoots4
set_option autoImplicit false
-- FG circuit pilot S1g check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §12.

/-! # FGCircuitPilotCheck6

1. SIGNATURES: COMPLETE expected types written independently of the theorems and compared by `isDefEq` after unfolding only the whitelisted definitions: `MachineDefinesLinked`, `machineDefinesLinked_of_env`, `root_find_of_run`, `rootEnv_of_lookup`,
   `X_final4` / `X_final5` (four roots), `X_hsrc` (four roots). MUTANTS: another environment in each premise slot, another design/Post root, another shape/data, a dropped premise (Start, hr, hquiet, GetEnvFrame, gates), an added old premise (global MachineDefines, hsrc, hdRun), a different world link.
2. HYPS / REMAINING: the explicit hypotheses of every final theorem by name and type, per root.
3. AXIOMS of every new name.
4. SNAPSHOT6: on this build's environment, for all four roots: `EntryGates`, `machineShape?`, `dataOfAt` and its WHOLE-STRUCTURE equality with the endpoint literal (negative controls: another root's data, single-field perturbations).
   This is the value of ONE environment: it is NOT a proof that all premises are satisfiable together (no example run / `Environment` / `Laws` is built). Separately, kernel-proved first cycles of each root's observation (a non-vacuous stream: observed 0/3). Those two kinds of evidence are different and are labelled separately. -/
namespace Tests.Gen5.FGCircuitPilotCheck6
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitLinked Tools.ShippingFGCircuitFinal4 Tools.ShippingFGCircuitRoots4
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt CoreSaved coreHead)
open Tools.ShippingMachineEntry (MachineCloses)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildCacheA (JQC)
open Tools.ShippingChildVCA (JQ)
open Sparkle.Compiler.Elab Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises
open Tests.Gen5.FGCircuitPilotCheck5 (W GPd EnvStart EnvEnd dataExprOf shapeExprOf literalExpr perturbations ppAll binderInfos explicitBinders)

/-! ## 1. expected statements, written independently -/

/-- `MachineDefinesLinked`. Knobs: where `getConstInfo` starts (`pickC w1 w2`), where the first `getEnv` starts (`pickE w2 w3`), the world the shape-reading `getEnv` starts at (`tie w3 w2`), the environment the shape is read from, the two `Bool`s of `entryConst`, the name. -/
def ExpMDL (pickC pickE tie : W → W → W) (shEnv : Environment → Environment → Environment) (b1 b2 : Bool) (gc : Name → Name)
    (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (X : Name) (shape : MachineShape) (w : W) (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w' : W) : Prop :=
  RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (M, D) w' →
  ∀ (s : CoreSaved) (w1 w2 w3 w4 : W) (env : Environment) (ci : ConstantInfo),
    RunsTo (coreHead X) mctx mref cctx cref w s w1 →
    RunsTo (Lean.getConstInfo (gc X)) mctx mref cctx cref (pickC w1 w2) ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref (pickE w2 w3) env w3 →
    RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire env e h t n) (Tools.ShippingChildInv.profLogIO s.profile) X [] false true
      (entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)) (instancePredicate env))
      mctx mref cctx cref w3 (M, D) w4 →
    certifiedShape? false [] (entryConst b1 b2 [] ci (instancePredicate env) (userInliner env) (structEnv env)) = none ∧
    mixedCertifiedShape? false [] (entryConst b1 b2 [] ci (instancePredicate env) (userInliner env) (structEnv env)) (instancePredicate env) = none ∧
    ∀ (env' : Environment) (w8 : W), RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref (tie w3 w2) env' w8 →
      machineShape? false [] (entryConst b1 b2 [] ci (instancePredicate env) (userInliner env) (structEnv env)) (structEnv (shEnv env env')) = some shape

abbrev ExpMDLTrue := @ExpMDL (fun w1 _ => w1) (fun w2 _ => w2) (fun w3 _ => w3) (fun _ e' => e') true false (fun x => x)
def MutMDLCWorld := @ExpMDL (fun _ w2 => w2) (fun w2 _ => w2) (fun w3 _ => w3) (fun _ e' => e') true false (fun x => x)
def MutMDLEWorld := @ExpMDL (fun w1 _ => w1) (fun _ w3 => w3) (fun w3 _ => w3) (fun _ e' => e') true false (fun x => x)
def MutMDLTie := @ExpMDL (fun w1 _ => w1) (fun w2 _ => w2) (fun _ w2 => w2) (fun _ e' => e') true false (fun x => x)
def MutMDLEnv := @ExpMDL (fun w1 _ => w1) (fun w2 _ => w2) (fun w3 _ => w3) (fun e _ => e) true false (fun x => x)
def MutMDLFlag1 := @ExpMDL (fun w1 _ => w1) (fun w2 _ => w2) (fun w3 _ => w3) (fun _ e' => e') false false (fun x => x)
def MutMDLFlag2 := @ExpMDL (fun w1 _ => w1) (fun w2 _ => w2) (fun w3 _ => w3) (fun _ e' => e') true true (fun x => x)
def MutMDLName := @ExpMDL (fun w1 _ => w1) (fun w2 _ => w2) (fun w3 _ => w3) (fun _ e' => e') true false (fun _ => ``shift4Loop)

/-- the refusal facts of the entry constant of one environment (`entry₀` written out) -/
def ExpGates (env : Environment) (X : Name) : Prop :=
  ∀ E : ConstantInfo, ((env.find? X).map fun ci => entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)) = some E →
    certifiedShape? false [] E = none ∧ mixedCertifiedShape? false [] E (instancePredicate env) = none
def ExpQuoteAt (env : Environment) (X : Name) (ty val : Lean.Expr) : Prop :=
  ∀ ci : ConstantInfo, env.find? X = some ci → ∃ d : DefinitionVal, ci = ConstantInfo.defnInfo d ∧ d.levelParams = [] ∧ d.type = ty ∧ d.value = val
def ExpReaderAt (lvl : Lean.Expr → Nat) (env : Environment) (X : Name) (dd : MachineData) : Prop :=
  ∀ E : ConstantInfo, ((env.find? X).map fun ci => entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)) = some E →
    machineShape? false [] E (structEnv env) = some dd.shape ∧ Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) dd.shape = some dd

/-- `machineDefinesLinked_of_env` -/
def ExpSupply : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) {X : Name} {shape : MachineShape} {e : Environment} {ci₀ : ConstantInfo} {w w' : W}
    {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    AdmCtx L.O.quiet mctx cctx → JQ L.O.quiet 0 w →
    (∀ u, L.O.quiet u → Tools.ShippingGen5Env.ReadsAt e cref u) →
    Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref →
    e.find? X = some ci₀ →
    certifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate e) (userInliner e) (structEnv e)) = none →
    mixedCertifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate e) (userInliner e) (structEnv e)) (instancePredicate e) = none →
    machineShape? false [] (entryConst true false [] ci₀ (instancePredicate e) (userInliner e) (structEnv e)) (structEnv e) = some shape →
    ExpMDLTrue mctx mref cctx cref X shape w M D w'

/-- `root_find_of_run` -/
def ExpRootFind : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) {mctx : Meta.Context} {cctx : Core.Context} {X : Name}
    {w w' : W} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    Start L mctx cctx w → (∀ u, L.O.quiet u → Tools.ShippingGen5Env.ReadsAt (envAt cref w) cref u) →
    RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (M, D) w' →
    ∃ ci : ConstantInfo, (envAt cref w).find? X = some ci

/-- `rootEnv_of_lookup` -/
def ExpLookup : Prop :=
  ∀ {lvl : Lean.Expr → Nat} {X : Name} {ty val : Lean.Expr} {dd : MachineData} {env : Environment},
    ExpQuoteAt env X ty val → ExpReaderAt lvl env X dd → (∃ ci : ConstantInfo, env.find? X = some ci) →
    (∃ d : DefinitionVal, RootInEnv env X ty val d) ∧ RootReader lvl env X dd

/-- `X_final4` for a root with a `MonoTy` shape. Knobs: the environment of each premise slot and of the conclusion, the data of `hRead`, the Post root. -/
def ExpF4 (X : Name) (ty val : Lean.Expr) (sh : SigShape) (dd : MachineData)
    (eQ eG eR eE eC : ST.Ref IO.RealWorld Core.State → W → W → Environment) (postRoot : Name) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational X) mctx mref cctx cref w (b, D') w' →
    (∀ u, L.O.quiet u → Tools.ShippingGen5Env.ReadsAt (eQ cref w w') cref u) →
    Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref →
    ExpGates (eG cref w w') X →
    RootReader lvl (eR cref w w') X dd →
    RootInEnv (eE cref w w') X ty val d →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy sh) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (eC cref w w') (GPd lvl (eC cref w w')) (PostRun mctx mref cctx cref w postRoot D') X sh mm b D' p

def ExpF5 (X : Name) (ty val : Lean.Expr) (sh : SigShape) (dd : MachineData)
    (eQ eG eK eD eC : ST.Ref IO.RealWorld Core.State → W → W → Environment) (postRoot : Name) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational X) mctx mref cctx cref w (b, D') w' →
    (∀ u, L.O.quiet u → Tools.ShippingGen5Env.ReadsAt (eQ cref w w') cref u) →
    Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref →
    ExpGates (eG cref w w') X →
    ExpQuoteAt (eK cref w w') X ty val →
    ExpReaderAt lvl (eD cref w w') X dd →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy sh) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (eC cref w w') (GPd lvl (eC cref w w')) (PostRun mctx mref cctx cref w postRoot D') X sh mm b D' p

abbrev S := EnvStart
abbrev E := EnvEnd
abbrev F4Counter := ExpF4 ``counterLoop counterLoopType counterLoopValue shCounter counterLoop.machineData S S S S S ``counterLoop
abbrev F4Shift := ExpF4 ``shift4Loop shift4LoopType shift4LoopValue shShift4 shift4Loop.machineData S S S S S ``shift4Loop
abbrev F4Enable := ExpF4 ``counterEnableLoop counterEnableLoopType counterEnableLoopValue shEnable counterEnableLoop.machineData S S S S S ``counterEnableLoop
abbrev F5Counter := ExpF5 ``counterLoop counterLoopType counterLoopValue shCounter counterLoop.machineData S S S S S ``counterLoop
abbrev F5Shift := ExpF5 ``shift4Loop shift4LoopType shift4LoopValue shShift4 shift4Loop.machineData S S S S S ``shift4Loop
abbrev F5Enable := ExpF5 ``counterEnableLoop counterEnableLoopType counterEnableLoopValue shEnable counterEnableLoop.machineData S S S S S ``counterEnableLoop
-- mutants of counterLoop_final4: each premise slot / the conclusion in another environment, another shape / data / design root
def M4Q := ExpF4 ``counterLoop counterLoopType counterLoopValue shCounter counterLoop.machineData E S S S S ``counterLoop
def M4G := ExpF4 ``counterLoop counterLoopType counterLoopValue shCounter counterLoop.machineData S E S S S ``counterLoop
def M4R := ExpF4 ``counterLoop counterLoopType counterLoopValue shCounter counterLoop.machineData S S E S S ``counterLoop
def M4E := ExpF4 ``counterLoop counterLoopType counterLoopValue shCounter counterLoop.machineData S S S E S ``counterLoop
def M4C := ExpF4 ``counterLoop counterLoopType counterLoopValue shCounter counterLoop.machineData S S S S E ``counterLoop
def M4Data := ExpF4 ``counterLoop counterLoopType counterLoopValue shCounter shift4Loop.machineData S S S S S ``counterLoop
def M4Post := ExpF4 ``counterLoop counterLoopType counterLoopValue shCounter counterLoop.machineData S S S S S ``shift4Loop
def M4Val := ExpF4 ``counterLoop counterLoopType shift4LoopValue shCounter counterLoop.machineData S S S S S ``counterLoop
-- mutants of counterLoop_final5
def M5Q := ExpF5 ``counterLoop counterLoopType counterLoopValue shCounter counterLoop.machineData E S S S S ``counterLoop
def M5G := ExpF5 ``counterLoop counterLoopType counterLoopValue shCounter counterLoop.machineData S E S S S ``counterLoop
def M5K := ExpF5 ``counterLoop counterLoopType counterLoopValue shCounter counterLoop.machineData S S E S S ``counterLoop
def M5D := ExpF5 ``counterLoop counterLoopType counterLoopValue shCounter counterLoop.machineData S S S E S ``counterLoop
def M5C := ExpF5 ``counterLoop counterLoopType counterLoopValue shCounter counterLoop.machineData S S S S E ``counterLoop
def M5Data := ExpF5 ``counterLoop counterLoopType counterLoopValue shCounter shift4Loop.machineData S S S S S ``counterLoop
-- dropped / added premises of counterLoop_final4
def M4NoStart : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ u, L.O.quiet u → Tools.ShippingGen5Env.ReadsAt (envAt cref w) cref u) →
    Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref →
    ExpGates (envAt cref w) ``counterLoop →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd lvl (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p
def M4NoRun : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    Start L mctx cctx w →
    (∀ u, L.O.quiet u → Tools.ShippingGen5Env.ReadsAt (envAt cref w) cref u) →
    Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref →
    ExpGates (envAt cref w) ``counterLoop →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd lvl (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p
def M4NoQuiet : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref →
    ExpGates (envAt cref w) ``counterLoop →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd lvl (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p
def M4NoFrame : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ u, L.O.quiet u → Tools.ShippingGen5Env.ReadsAt (envAt cref w) cref u) →
    ExpGates (envAt cref w) ``counterLoop →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd lvl (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p
def M4NoGates : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ u, L.O.quiet u → Tools.ShippingGen5Env.ReadsAt (envAt cref w) cref u) →
    Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd lvl (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p
def M4AddHdRun : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W), ExpMDLTrue mctx mref cctx cref ``counterLoop counterLoop.machineData.shape w raw D₀ w1) →
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ u, L.O.quiet u → Tools.ShippingGen5Env.ReadsAt (envAt cref w) cref u) →
    Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref →
    ExpGates (envAt cref w) ``counterLoop →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd lvl (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p
def M4AddGlobalDefines : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``counterLoop counterLoop.machineData.shape →
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ u, L.O.quiet u → Tools.ShippingGen5Env.ReadsAt (envAt cref w) cref u) →
    Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref →
    ExpGates (envAt cref w) ``counterLoop →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd lvl (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p
def M4AddHsrc : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    (∀ p : Pkg ι (fun _ => defaultDomain), GPd lvl (envAt cref w) ``counterLoop = some p →
      ∀ (i : ι) bools bits, p.src i bools bits = monoObs shCounter counterLoop bools bits) →
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ u, L.O.quiet u → Tools.ShippingGen5Env.ReadsAt (envAt cref w) cref u) →
    Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref →
    ExpGates (envAt cref w) ``counterLoop →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd lvl (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p
def M4NoExists : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ u, L.O.quiet u → Tools.ShippingGen5Env.ReadsAt (envAt cref w) cref u) →
    Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref →
    ExpGates (envAt cref w) ``counterLoop →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd lvl (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p
def M4Lvl : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ u, L.O.quiet u → Tools.ShippingGen5Env.ReadsAt (envAt cref w) cref u) →
    Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref →
    ExpGates (envAt cref w) ``counterLoop →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd (fun _ => 0) (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p

/-! ### arbiterSignal (domain-polymorphic, `RootArtifact`, `hB`) -/
abbrev ArbX : Name := ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
noncomputable abbrev GPa (lvl : Lean.Expr → Nat) (env : Environment) :=
  genGP (ι := DomainConfig) (dom := fun i => i) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) env
def ExpFArb4 (dd : MachineData) (eQ eG eR eE eB eC : ST.Ref IO.RealWorld Core.State → W → W → Environment) (postRoot : Name) : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ArbX) mctx mref cctx cref w (b, D') w' →
    (∀ u, L.O.quiet u → Tools.ShippingGen5Env.ReadsAt (eQ cref w w') cref u) →
    Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref →
    ExpGates (eG cref w w') ArbX →
    RootReader lvl (eR cref w w') ArbX dd →
    RootInEnv (eE cref w w') ArbX arbiterType arbiterValue d →
    BoundaryRowsInEnv (eB cref w w') →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : shArbiter.Ty) (p : Pkg DomainConfig (fun i => i)),
      RootArtifact (eC cref w w') (GPa lvl (eC cref w w')) (PostRun mctx mref cctx cref w postRoot D') ArbX shArbiter mm b D' p
def ExpFArb5 (dd : MachineData) (eQ eG eK eD eB eC : ST.Ref IO.RealWorld Core.State → W → W → Environment) (postRoot : Name) : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ArbX) mctx mref cctx cref w (b, D') w' →
    (∀ u, L.O.quiet u → Tools.ShippingGen5Env.ReadsAt (eQ cref w w') cref u) →
    Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref →
    ExpGates (eG cref w w') ArbX →
    BoundaryRowsInEnv (eB cref w w') →
    ExpQuoteAt (eK cref w w') ArbX arbiterType arbiterValue →
    ExpReaderAt lvl (eD cref w w') ArbX dd →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : shArbiter.Ty) (p : Pkg DomainConfig (fun i => i)),
      RootArtifact (eC cref w w') (GPa lvl (eC cref w w')) (PostRun mctx mref cctx cref w postRoot D') ArbX shArbiter mm b D' p
abbrev FArb4 := ExpFArb4 Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData S S S S S S ArbX
abbrev FArb5 := ExpFArb5 Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData S S S S S S ArbX
def MArbB := ExpFArb4 Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData S S S S E S ArbX
def MArbR := ExpFArb4 Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData S S E S S S ArbX
def MArbData := ExpFArb4 counterLoop.machineData S S S S S S ArbX
def MArbPost := ExpFArb4 Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData S S S S S S ``counterLoop
def MArb5B := ExpFArb5 Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData S S S S E S ArbX

/-! ### `hsrc` -/
def ExpHsrcMono (X : Name) (sh : SigShape) (decl : MonoTy sh) (dd : MachineData)
    (eL : (Lean.Expr → Nat) → (Lean.Expr → Nat)) : Prop :=
  ∀ {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment), RootReader lvl env X dd →
    ∃ p : Pkg ι (fun _ => defaultDomain), GPd (eL lvl) env X = some p ∧
      ∀ (i : ι) bools bits, p.src i bools bits = monoObs sh decl bools bits
abbrev HsrcShift := ExpHsrcMono ``shift4Loop shShift4 shift4Loop shift4Loop.machineData (fun l => l)
abbrev HsrcEnable := ExpHsrcMono ``counterEnableLoop shEnable counterEnableLoop counterEnableLoop.machineData (fun l => l)
def MHsrcEnableData := ExpHsrcMono ``counterEnableLoop shEnable counterEnableLoop shift4Loop.machineData (fun l => l)
def MHsrcShiftData := ExpHsrcMono ``shift4Loop shShift4 shift4Loop counterEnableLoop.machineData (fun l => l)
def MHsrcShiftLvl := ExpHsrcMono ``shift4Loop shShift4 shift4Loop shift4Loop.machineData (fun _ => fun _ => 0)
def MHsrcShiftRoot := ExpHsrcMono ``counterLoop shShift4 shift4Loop shift4Loop.machineData (fun l => l)
def ExpHsrcArb (dd : MachineData) : Prop :=
  ∀ (lvl : Lean.Expr → Nat) (env : Environment), RootReader lvl env ArbX dd →
    ∃ p : Pkg DomainConfig (fun i => i), GPa lvl env ArbX = some p ∧
      ∀ (i : DomainConfig) bools bits, p.src i bools bits = shArbiter.obs (dom := fun i : DomainConfig => i)
        (fun D => @Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D) i bools bits
abbrev HsrcArb := ExpHsrcArb Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData
def MHsrcArbData := ExpHsrcArb counterLoop.machineData

def whitelist : List Name := [``ExpMDL, ``ExpMDLTrue, ``MutMDLCWorld, ``MutMDLEWorld, ``MutMDLTie, ``MutMDLEnv, ``MutMDLFlag1, ``MutMDLFlag2, ``MutMDLName,
  ``ExpGates, ``ExpQuoteAt, ``ExpReaderAt, ``ExpSupply, ``ExpRootFind, ``ExpLookup, ``ExpF4, ``ExpF5, ``S, ``E,
  ``F4Counter, ``F4Shift, ``F4Enable, ``F5Counter, ``F5Shift, ``F5Enable,
  ``M4Q, ``M4G, ``M4R, ``M4E, ``M4C, ``M4Data, ``M4Post, ``M4Val, ``M5Q, ``M5G, ``M5K, ``M5D, ``M5C, ``M5Data,
  ``M4NoStart, ``M4NoRun, ``M4NoQuiet, ``M4NoFrame, ``M4NoGates, ``M4AddHdRun, ``M4AddGlobalDefines, ``M4AddHsrc, ``M4NoExists, ``M4Lvl,
  ``ExpFArb4, ``ExpFArb5, ``FArb4, ``FArb5, ``MArbB, ``MArbR, ``MArbData, ``MArbPost, ``MArb5B, ``ArbX, ``GPa,
  ``ExpHsrcMono, ``HsrcShift, ``HsrcEnable, ``MHsrcShiftData, ``MHsrcShiftLvl, ``MHsrcShiftRoot, ``MHsrcEnableData, ``ExpHsrcArb, ``HsrcArb, ``MHsrcArbData,
  ``Tests.Gen5.FGCircuitPilotCheck5.GPd, ``Tests.Gen5.FGCircuitPilotCheck5.EnvStart, ``Tests.Gen5.FGCircuitPilotCheck5.EnvEnd,
  -- the definitions under test are unfolded too, so the comparison is against the independently written statements
  ``MachineDefinesLinked, ``EntryGates, ``Tools.ShippingGen5Acc.entry₀, ``QuoteAt, ``ReaderAt]

def norm (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if whitelist.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let same (thm exp : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    unless ci.levelParams.isEmpty do throwError "{thm}: level parameters"
    let a ← norm ci.type
    let e ← norm (mkConst exp)
    unless ← withReducible (isDefEq a e) do throwError "{thm}: type is NOT the expected statement {exp}"
    let ba ← binderInfos a
    let be ← binderInfos e
    unless ba == be do throwError "{thm}: binder kinds differ from {exp}: {repr ba} vs {repr be}"
  let differs (thm mu0 : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    let a ← norm ci.type
    let e ← norm (mkConst mu0)
    if ← withReducible (isDefEq a e) then throwError "{thm}: the MUTANT {mu0} was accepted"
  -- the definition `MachineDefinesLinked` against its independent statement
  let ci ← getConstInfo ``MachineDefinesLinked
  let ce ← getConstInfo ``ExpMDLTrue
  let appl (c : Name) (t : Lean.Expr) : MetaM Lean.Expr := do
    let r ← forallTelescope t fun xs _ => do
      let b ← norm (mkAppN (mkConst c) xs)
      mkForallFVars xs b
    norm r
  let a ← appl ``MachineDefinesLinked ci.type
  let e ← appl ``ExpMDLTrue ce.type
  unless ← withReducible (isDefEq a e) do throwError "MachineDefinesLinked is NOT the independently written statement"
  let mut nm : Nat := 0
  for mu in [``MutMDLCWorld, ``MutMDLEWorld, ``MutMDLTie, ``MutMDLEnv, ``MutMDLFlag1, ``MutMDLFlag2, ``MutMDLName] do
    let cm ← getConstInfo mu
    let m ← appl mu cm.type
    if ← withReducible (isDefEq a m) then throwError "the MUTANT {mu} of MachineDefinesLinked was accepted"
    nm := nm + 1
  let L := `Tools.ShippingFGCircuitLinked
  let F := `Tools.ShippingFGCircuitFinal4
  let R := `Tools.ShippingFGCircuitRoots4
  same (L ++ `machineDefinesLinked_of_env) ``ExpSupply
  same (F ++ `root_find_of_run) ``ExpRootFind
  same (F ++ `rootEnv_of_lookup) ``ExpLookup
  same (F ++ `counterLoop_final4) ``F4Counter
  same (F ++ `counterLoop_final5) ``F5Counter
  same (R ++ `shift4Loop_final4) ``F4Shift
  same (R ++ `shift4Loop_final5) ``F5Shift
  same (R ++ `counterEnableLoop_final4) ``F4Enable
  same (R ++ `counterEnableLoop_final5) ``F5Enable
  same (R ++ `arbiterSignal_final4) ``FArb4
  same (R ++ `arbiterSignal_final5) ``FArb5
  same (R ++ `shift4Loop_hsrc) ``HsrcShift
  same (R ++ `counterEnableLoop_hsrc) ``HsrcEnable
  same (R ++ `arbiterSignal_hsrc) ``HsrcArb
  for mu in [``M4Q, ``M4G, ``M4R, ``M4E, ``M4C, ``M4Data, ``M4Post, ``M4Val, ``M4NoStart, ``M4NoRun, ``M4NoQuiet, ``M4NoFrame, ``M4NoGates, ``M4AddHdRun, ``M4AddGlobalDefines, ``M4AddHsrc, ``M4NoExists, ``M4Lvl] do
    differs (F ++ `counterLoop_final4) mu; nm := nm + 1
  for mu in [``M5Q, ``M5G, ``M5K, ``M5D, ``M5C, ``M5Data] do
    differs (F ++ `counterLoop_final5) mu; nm := nm + 1
  for mu in [``MArbB, ``MArbR, ``MArbData, ``MArbPost] do
    differs (R ++ `arbiterSignal_final4) mu; nm := nm + 1
  differs (R ++ `arbiterSignal_final5) ``MArb5B; nm := nm + 1
  for mu in [``MHsrcShiftData, ``MHsrcShiftLvl, ``MHsrcShiftRoot] do
    differs (R ++ `shift4Loop_hsrc) mu; nm := nm + 1
  differs (R ++ `counterEnableLoop_hsrc) ``MHsrcEnableData; nm := nm + 1
  differs (R ++ `arbiterSignal_hsrc) ``MHsrcArbData; nm := nm + 1
  -- cross-root mutants: one root's final theorem is not another root's statement
  differs (R ++ `shift4Loop_final4) ``F4Counter; differs (R ++ `counterEnableLoop_final4) ``F4Shift; differs (F ++ `counterLoop_final4) ``F4Enable
  nm := nm + 3
  logInfo m!"FGCIRCUIT6 SIGNATURES: MachineDefinesLinked, machineDefinesLinked_of_env, root_find_of_run, rootEnv_of_lookup, X_final4 / X_final5 for the four roots and X_hsrc for shift4Loop / counterEnableLoop / arbiterSignal equal their independently written COMPLETE types (hypotheses, conclusion, environments, designs, binder kinds); {nm} mutants rejected"

/-! ## 2. the hypotheses that remain, by name and by type, per root -/

run_cmd liftTermElabM do
  let F := `Tools.ShippingFGCircuitFinal4
  let R := `Tools.ShippingFGCircuitRoots4
  let others : List (Name × List Name) :=
    [(F ++ `counterLoop_final4, [``Sparkle.Tests.SignalLoopTest.shift4Loop, ``Sparkle.Tests.SignalLoopTest.counterEnableLoop, ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal]),
     (F ++ `counterLoop_final5, [``Sparkle.Tests.SignalLoopTest.shift4Loop, ``Sparkle.Tests.SignalLoopTest.counterEnableLoop, ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal]),
     (R ++ `shift4Loop_final4, [``Sparkle.Tests.SignalLoopTest.counterLoop, ``Sparkle.Tests.SignalLoopTest.counterEnableLoop, ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal]),
     (R ++ `shift4Loop_final5, [``Sparkle.Tests.SignalLoopTest.counterLoop, ``Sparkle.Tests.SignalLoopTest.counterEnableLoop, ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal]),
     (R ++ `counterEnableLoop_final4, [``Sparkle.Tests.SignalLoopTest.counterLoop, ``Sparkle.Tests.SignalLoopTest.shift4Loop, ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal]),
     (R ++ `counterEnableLoop_final5, [``Sparkle.Tests.SignalLoopTest.counterLoop, ``Sparkle.Tests.SignalLoopTest.shift4Loop, ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal]),
     (R ++ `arbiterSignal_final4, [``Sparkle.Tests.SignalLoopTest.counterLoop, ``Sparkle.Tests.SignalLoopTest.shift4Loop, ``Sparkle.Tests.SignalLoopTest.counterEnableLoop]),
     (R ++ `arbiterSignal_final5, [``Sparkle.Tests.SignalLoopTest.counterLoop, ``Sparkle.Tests.SignalLoopTest.shift4Loop, ``Sparkle.Tests.SignalLoopTest.counterEnableLoop])]
  let check (thm : Name) (expected : List String) (others : List Name) : MetaM Unit := do
    let bs ← explicitBinders thm
    let names := bs.map (·.1)
    unless names == expected do throwError "{thm}: hypotheses are {names}, expected {expected}"
    for supplied in ["hw", "hA6", "hsrc", "htr", "hd", "hdRun", "hc", "hcl", "hP", "hl", "hTop", "hpost", "hsnap"] do
      if names.contains supplied then throwError "{thm}: {supplied} is a hypothesis"
    for (n, t) in bs do
      if t.getUsedConstants.contains ``sorryAx then throwError "{thm}: hypothesis {n} mentions sorryAx"
      if t.getUsedConstants.contains ``Tools.ShippingGen5FG.EntryWitness then throwError "{thm}: hypothesis {n} is the EntryWitness (ReflectsAll)"
      if t.getUsedConstants.contains ``Tools.ShippingFGCircuitBridge.DesignTransport then throwError "{thm}: hypothesis {n} is DesignTransport"
      if t.getUsedConstants.contains ``Tools.ShippingMachineEntry.MachineDefines then throwError "{thm}: hypothesis {n} is the global MachineDefines"
      if t.getUsedConstants.contains ``Tools.ShippingFGCircuitRunLocal.MachineDefinesRun then throwError "{thm}: hypothesis {n} is MachineDefinesRun"
      if t.getUsedConstants.contains ``MachineDefinesLinked then throwError "{thm}: hypothesis {n} is MachineDefinesLinked (it is derived)"
    let ci ← getConstInfo thm
    for o in others do
      if ci.type.getUsedConstants.contains o then throwError "{thm}: mentions another root {o}"
    for (n, t) in bs do
      let pp ← try pure (toString (← ppExpr t)) catch _ => pure s!"<unprintable; constants: {t.getUsedConstants.toList.map (·.toString)}>"
      logInfo m!"FGCIRCUIT6 REMAINING {thm.getString!} {n} : {pp}"
  for (thm, os) in others do
    let isArb := (thm.getString!.startsWith "arbiter")
    let is5 := thm.getString!.endsWith "final5"
    let exp : List String :=
      if is5 then (if isArb then ["L", "lvl", "hstart", "hr", "hquiet", "hg", "hgates", "hB", "hquote", "hreader"] else ["L", "lvl", "hstart", "hr", "hquiet", "hg", "hgates", "hquote", "hreader"])
      else (if isArb then ["L", "lvl", "hstart", "hr", "hquiet", "hg", "hgates", "hRead", "hE", "hB"] else ["L", "lvl", "hstart", "hr", "hquiet", "hg", "hgates", "hRead", "hE"])
    check thm exp os
  logInfo "FGCIRCUIT6 HYPS: X_final4 = L lvl hstart hr hquiet hg hgates hRead hE (arbiter: + hB); X_final5 = L lvl hstart hr hquiet hg hgates [hB] hquote hreader. NOT hypotheses: hw / ReflectsAll, hA6, global MachineDefines, MachineDefinesRun / MachineDefinesLinked (derived), hsrc (derived, all four roots), DesignTransport (derived, all four roots are register leaves with insts = []). Laws L is an explicit argument: it remains an obligation (A.P-02 runtime laws)"

/-! ## 3. axioms of every new name -/
run_cmd liftTermElabM do
  let L := `Tools.ShippingFGCircuitLinked
  let L2 := `Tools.ShippingFGCircuitLinked2
  let F := `Tools.ShippingFGCircuitFinal4
  let R := `Tools.ShippingFGCircuitRoots4
  let names : List Name := [L ++ `machineDefinesLinked_of_env, L ++ `machine_run_of_coreC, L ++ `machineRunJQC_of_closesC, L ++ `synthesizeCombinationalCore_machine_soundC,
    L2 ++ `machine_trace_lets_of_streamBC, L2 ++ `machine_trace_lets_of_streamC, L2 ++ `machine_traceL_of_streamC, L2 ++ `machine_traceL_of_loopC, L2 ++ `machine_ships_wiredC,
    F ++ `leaf_topShips_of_runC, F ++ `leaf_instFree_of_runC, F ++ `hTop_of_leaf4, F ++ `counterLoop_artifact_atC, F ++ `counterLoop_final4D, F ++ `machineDefinesLinked_of_reader,
    F ++ `counterLoop_final4, F ++ `root_find_of_run, F ++ `rootEnv_of_lookup, F ++ `counterLoop_final5,
    R ++ `src_eq_of_states, R ++ `loop_states, R ++ `hst_of_loop, R ++ `hsrc_of_states, R ++ `shift4Loop_hsrc, R ++ `counterEnableLoop_hsrc, R ++ `arbiterSignal_hsrc,
    R ++ `machine_traceL_of_regsC, R ++ `shift4Loop_artifact_atC, R ++ `shift4Loop_final4, R ++ `shift4Loop_final5,
    R ++ `counterEnableLoop_artifact_atC, R ++ `counterEnableLoop_final4, R ++ `counterEnableLoop_final5,
    R ++ `arbiterSignal_artifact_atC, R ++ `arbiterSignal_final4, R ++ `arbiterSignal_final5]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT6 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

/-! ## 4. SNAPSHOT6: ONE environment, all four roots -/

def snapshotRoot (x lit : Name) : MetaM Unit := do
  let env ← getEnv
  let litE ← literalExpr lit
  let some E := Tools.ShippingGen5Acc.entry₀ env x | throwError "{x}: no entry constant in this environment"
  -- EntryGates (the two refusal facts) on this environment
  unless (certifiedShape? false [] E).isNone do throwError "{x}: certifiedShape? is not none"
  unless (mixedCertifiedShape? false [] E (instancePredicate env)).isNone do throwError "{x}: mixedCertifiedShape? is not none"
  let some s := machineShape? false [] E (structEnv env) | throwError "{x}: machineShape? none"
  let some d := Tools.ShippingGen5DataOf.dataOfAt (fun _ => 1000000) E (structEnv env) s | throwError "{x}: dataOfAt none"
  let dE ← dataExprOf d
  unless dE == litE do throwError "{x}: the reader's data (dataOfAt) differs from the endpoint literal machineData (whole structure)"
  unless (← shapeExprOf s) == (← shapeExprOf d.shape) do throwError "{x}: machineShape? and the data's shape differ"
  let mut np : Nat := 0
  for (nm, d') in perturbations d do
    if (← dataExprOf d') == litE then throwError "negative control: the perturbation of {nm} is not detected"
    np := np + 1
  logInfo m!"FGCIRCUIT6 SNAPSHOT6 {x}: EntryGates (certifiedShape? = none, mixedCertifiedShape? = none), machineShape? = some, dataOfAt (fuel 1000000) EQUAL to the endpoint literal machineData over its WHOLE structure; {np} single-field perturbations rejected; nIn={d.nIn} ss={d.ss.length} outs={d.outs.length} lets={d.ls.length} binders={d.shape.binders.map (·.1)}"

run_cmd liftTermElabM do
  let roots : List (Name × Name) :=
    [(``Sparkle.Tests.SignalLoopTest.counterLoop, ``Sparkle.Tests.SignalLoopTest.counterLoop.machineData),
     (``Sparkle.Tests.SignalLoopTest.shift4Loop, ``Sparkle.Tests.SignalLoopTest.shift4Loop.machineData),
     (``Sparkle.Tests.SignalLoopTest.counterEnableLoop, ``Sparkle.Tests.SignalLoopTest.counterEnableLoop.machineData),
     (``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal, ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData)]
  for (x, l) in roots do snapshotRoot x l
  -- negative control across roots: counterLoop's data is not shift4Loop's literal
  let env ← getEnv
  let some E := Tools.ShippingGen5Acc.entry₀ env ``Sparkle.Tests.SignalLoopTest.counterLoop | throwError "no counterLoop"
  let some s := machineShape? false [] E (structEnv env) | throwError "no shape"
  let some d := Tools.ShippingGen5DataOf.dataOfAt (fun _ => 1000000) E (structEnv env) s | throwError "no data"
  if (← dataExprOf d) == (← literalExpr ``Sparkle.Tests.SignalLoopTest.shift4Loop.machineData) then throwError "negative control: counterLoop's data equals shift4Loop's literal"
  logInfo "FGCIRCUIT6 SNAPSHOT6: four roots checked on ONE environment (this build's, fuel 1000000). These are values of one environment: they are NOT the kernel statements hquiet / hgates / hRead / hreader for an arbitrary run, and NOT a proof or an example that all premises (Laws L, Start, hr, hquiet, GetEnvFrame, hgates, hRead, hE) hold together"

/-! ## 5. observed streams (kernel proofs): non-vacuous observations -- a DIFFERENT kind of evidence from SNAPSHOT6 -/

theorem shift4_stream : (shift4Loop (Signal.pure 5#8)).val 3 = 0#8 ∧ (shift4Loop (Signal.pure 5#8)).val 4 = 5#8 := by
  constructor <;> decide

run_cmd logInfo "FGCIRCUIT6 STREAMS: the kernel proves (Tests.Gen5.FGCircuitPilotCheck4.counterLoop_first_cycles) counterLoop.val 0 = 0, counterLoop.val 3 = 3, and shift4Loop (pure 5) has val 3 = 0, val 4 = 5. These show that the observations the roots' hsrc statements equate p.src with are non-trivial streams (observed 0/3 style); they say nothing about whether the premises hold together"

end Tests.Gen5.FGCircuitPilotCheck6
