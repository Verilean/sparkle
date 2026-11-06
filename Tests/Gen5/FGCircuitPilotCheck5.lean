import Tools.ShippingFGCircuitFinal3
set_option autoImplicit false
-- FG circuit pilot S1f check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §11.

/-! # FGCircuitPilotCheck5

1. SIGNATURES: the COMPLETE expected types (hypotheses, conclusion, environments, designs, binder kinds), written here independently of the theorems, are compared with the actual types by `isDefEq`: `MachineDefinesRun`, `OnRunReads`/`RunSnap`/`RunQuote`/`RunReader`,
   `hTop_of_leaf3`, `counterLoop_artifact_atR`, `counterLoop_final3`, `counterLoop_final3L`, `rootEnv_of_run`. MUTANTS (another environment, another design/Post, another package table, another shape/data, a dropped or added premise, a different world tie) must be rejected.
2. HYPS: the hypotheses of the two final theorems, by name and by type, as the list of what remains.
3. AXIOMS of every new name.
4. SNAPSHOT5: the real value of `dataOfAt` on this build's environment is compared with the endpoint literal `counterLoop.machineData` over its WHOLE structure (shape: binders / body / layout / runs / insts / loops / instFields / instOrigins; nIn / dom / positions / sorts / lets / outs / nexts as terms),
   with negative controls (another root's data, and 8 single-field perturbations of the observed data), and the observed values are printed. -/
namespace Tests.Gen5.FGCircuitPilotCheck5
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitRunLocal Tools.ShippingFGCircuitFinal3
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingMachineEntry (MachineCloses)
open Tools.ShippingMachineAuto (MachineData)
open Sparkle.Compiler.Elab Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises

abbrev W := Void IO.RealWorld

/-! ## 1. expected statements, written independently -/

/-- `MachineDefinesRun`. Knobs: the world the second `getEnv` is read at (`tie w3 w5`), the environment the shape is read from (`shEnv envR envR'`), the two `Bool`s of `entryConst`, the name `getConstInfo` is asked for. -/
def ExpMDR (tie : W → W → W) (shEnv : Environment → Environment → Environment) (b1 b2 : Bool) (gc : Name → Name)
    (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (X : Name) (shape : MachineShape) (w : W) (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w' : W) : Prop :=
  RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (M, D) w' →
  ∀ (lp : String → IO Unit) (env : Environment) (ci : ConstantInfo) (w1 w2 w3 w4 w5 w6 : W),
    RunsTo (Lean.getConstInfo (gc X)) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 env w6 →
    RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire env e h t n) lp X [] false true
      (entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)) (instancePredicate env))
      mctx mref cctx cref w3 (M, D) w4 →
    certifiedShape? false [] (entryConst b1 b2 [] ci (instancePredicate env) (userInliner env) (structEnv env)) = none ∧
    mixedCertifiedShape? false [] (entryConst b1 b2 [] ci (instancePredicate env) (userInliner env) (structEnv env)) (instancePredicate env) = none ∧
    ∀ (env' : Environment) (w8 : W), RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref (tie w3 w5) env' w8 →
      machineShape? false [] (entryConst b1 b2 [] ci (instancePredicate env) (userInliner env) (structEnv env)) (structEnv (shEnv env env')) = some shape

abbrev ExpMDRTrue := @ExpMDR (fun w3 _ => w3) (fun _ e' => e') true false (fun x => x)
def MutMDRTie := @ExpMDR (fun _ w5 => w5) (fun _ e' => e') true false (fun x => x)
def MutMDREnv := @ExpMDR (fun w3 _ => w3) (fun e _ => e) true false (fun x => x)
def MutMDRFlag1 := @ExpMDR (fun w3 _ => w3) (fun _ e' => e') false false (fun x => x)
def MutMDRFlag2 := @ExpMDR (fun w3 _ => w3) (fun _ e' => e') true true (fun x => x)
def MutMDRName := @ExpMDR (fun w3 _ => w3) (fun _ e' => e') true false (fun _ => ``shift4Loop)

/-- the reads of the run; the property `Q` of `(envR, ci, w1, w3, w5)` -/
def ExpOn (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (X : Name) (w : W) (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w' : W) (Q : Environment → ConstantInfo → W → W → W → Prop) : Prop :=
  RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (M, D) w' →
  ∀ (lp : String → IO Unit) (env : Environment) (ci : ConstantInfo) (w1 w2 w3 w4 w5 w6 : W),
    RunsTo (Lean.getConstInfo X) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 env w6 →
    RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire env e h t n) lp X [] false true
      (entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)) (instancePredicate env))
      mctx mref cctx cref w3 (M, D) w4 → Q env ci w1 w3 w5

def ExpSnap (selW : W → W → W) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (X : Name) (w : W) (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w' : W) : Prop :=
  ExpOn mctx mref cctx cref X w M D w' fun _ _ w1 w3 w5 =>
    envAt cref w1 = envAt cref (selW w w') ∧ envAt cref w5 = envAt cref (selW w w') ∧ envAt cref w3 = envAt cref (selW w w')
def ExpQuote (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (X : Name) (ty val : Lean.Expr) (w : W) (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w' : W) : Prop :=
  ExpOn mctx mref cctx cref X w M D w' fun _ ci _ _ _ =>
    ∃ d : DefinitionVal, ci = ConstantInfo.defnInfo d ∧ d.levelParams = [] ∧ d.type = ty ∧ d.value = val
def ExpReader (envSel : W → W → W) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (lvl : Lean.Expr → Nat) (X : Name) (dd : MachineData) (w : W) (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w' : W) : Prop :=
  ExpOn mctx mref cctx cref X w M D w' fun env ci _ _ _ =>
    Tools.ShippingGen5DataOf.dataOfAt lvl (entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env))
      (structEnv (envAt cref (envSel w w'))) dd.shape = some dd

/-- a reusable piece: the package table of the generated packages -/
noncomputable abbrev GPd {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment) :=
  genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) env

/-- `counterLoop_final3`. Knobs: the environment of the package table / conclusion (`eC`), of `hRead` (`eR`), of `hE` (`eE`), the shape in `hdRun`, the data in `hRead`, the root of `PostRun`, whether `hr` is there. -/
def ExpFinal3 (eC eR eE : ST.Ref IO.RealWorld Core.State → W → W → Environment) (hdShape : MachineShape) (hrData : MachineData) (postRoot : Name) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W), ExpMDRTrue mctx mref cctx cref ``counterLoop hdShape w raw D₀ w1) →
    RootReader lvl (eR cref w w') ``counterLoop hrData →
    RootInEnv (eE cref w w') ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (eC cref w w') (GPd lvl (eC cref w w')) (PostRun mctx mref cctx cref w postRoot D') ``counterLoop shCounter mm b D' p

abbrev EnvStart : ST.Ref IO.RealWorld Core.State → W → W → Environment := fun c w _ => envAt c w
abbrev EnvEnd : ST.Ref IO.RealWorld Core.State → W → W → Environment := fun c _ w' => envAt c w'
abbrev ExpFinal3True := ExpFinal3 EnvStart EnvStart EnvStart counterLoop.machineData.shape counterLoop.machineData ``counterLoop
def MutF3EnvC := ExpFinal3 EnvEnd EnvStart EnvStart counterLoop.machineData.shape counterLoop.machineData ``counterLoop
def MutF3EnvR := ExpFinal3 EnvStart EnvEnd EnvStart counterLoop.machineData.shape counterLoop.machineData ``counterLoop
def MutF3EnvE := ExpFinal3 EnvStart EnvStart EnvEnd counterLoop.machineData.shape counterLoop.machineData ``counterLoop
def MutF3Shape := ExpFinal3 EnvStart EnvStart EnvStart shift4Loop.machineData.shape counterLoop.machineData ``counterLoop
def MutF3Data := ExpFinal3 EnvStart EnvStart EnvStart counterLoop.machineData.shape shift4Loop.machineData ``counterLoop
def MutF3Post := ExpFinal3 EnvStart EnvStart EnvStart counterLoop.machineData.shape counterLoop.machineData ``shift4Loop
/-- a premise dropped: no `Start` -/
def MutF3NoStart : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W), ExpMDRTrue mctx mref cctx cref ``counterLoop counterLoop.machineData.shape w raw D₀ w1) →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd lvl (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p
/-- a premise dropped: no `hr` -/
def MutF3NoRun : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    Start L mctx cctx w →
    (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W), ExpMDRTrue mctx mref cctx cref ``counterLoop counterLoop.machineData.shape w raw D₀ w1) →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd lvl (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p
/-- a premise added: the old `EntryWitness`/`ReflectsAll` -/
def MutF3AddWitness : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    EntryWitness ReflectsAll L ``counterLoop [] mctx cctx w w' b D' →
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W), ExpMDRTrue mctx mref cctx cref ``counterLoop counterLoop.machineData.shape w raw D₀ w1) →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd lvl (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p
/-- the conclusion weakened: no existence of the post-processing -/
def MutF3NoExists : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W), ExpMDRTrue mctx mref cctx cref ``counterLoop counterLoop.machineData.shape w raw D₀ w1) →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd lvl (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p
/-- the generated table replaced by another: the conclusion about the packages of `genGP` at the START environment is moved to the table of another `lvl` -/
def MutF3Lvl : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W), ExpMDRTrue mctx mref cctx cref ``counterLoop counterLoop.machineData.shape w raw D₀ w1) →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPd (fun _ => 0) (envAt cref w)) (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p

/-- `counterLoop_final3L` -/
def ExpFinal3L (eC : ST.Ref IO.RealWorld Core.State → W → W → Environment) (rdData : MachineData) (snapW : W → W → W) (postRoot : Name) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W), ExpMDRTrue mctx mref cctx cref ``counterLoop counterLoop.machineData.shape w raw D₀ w1) →
    (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W), ExpSnap snapW mctx mref cctx cref ``counterLoop w raw D₀ w1) →
    (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W), ExpQuote mctx mref cctx cref ``counterLoop counterLoopType counterLoopValue w raw D₀ w1) →
    (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W), ExpReader (fun w _ => w) mctx mref cctx cref lvl ``counterLoop rdData w raw D₀ w1) →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (eC cref w w') (GPd lvl (eC cref w w')) (PostRun mctx mref cctx cref w postRoot D') ``counterLoop shCounter mm b D' p
abbrev ExpFinal3LTrue := ExpFinal3L EnvStart counterLoop.machineData (fun w _ => w) ``counterLoop
def MutF3LEnv := ExpFinal3L EnvEnd counterLoop.machineData (fun w _ => w) ``counterLoop
def MutF3LData := ExpFinal3L EnvStart shift4Loop.machineData (fun w _ => w) ``counterLoop
def MutF3LSnap := ExpFinal3L EnvStart counterLoop.machineData (fun _ w' => w') ``counterLoop
def MutF3LPost := ExpFinal3L EnvStart counterLoop.machineData (fun w _ => w) ``shift4Loop

/-- `hTop_of_leaf3` -/
def ExpTop3 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom)
    {d : MachineData} {mctx : Meta.Context} {cctx : Core.Context} {w : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    p.d = d → p.kD = Tools.ShippingGen5Sem.kDOf d → LeafFacts d → Start L mctx cctx w →
    (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W), ExpMDRTrue mctx mref cctx cref p.decl p.d.shape w raw D₀ w1) →
    MachineCloses mctx mref cctx cref p.decl p.d.shape →
    ∀ raw, PostRun mctx mref cctx cref w p.decl D' b raw → ∃ n, HasConcretePackage p n p.decl b raw D'
def MutTop3NoLeaf : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom)
    {d : MachineData} {mctx : Meta.Context} {cctx : Core.Context} {w : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    p.d = d → p.kD = Tools.ShippingGen5Sem.kDOf d → Start L mctx cctx w →
    (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W), ExpMDRTrue mctx mref cctx cref p.decl p.d.shape w raw D₀ w1) →
    MachineCloses mctx mref cctx cref p.decl p.d.shape →
    ∀ raw, PostRun mctx mref cctx cref w p.decl D' b raw → ∃ n, HasConcretePackage p n p.decl b raw D'
def MutTop3NoCloses : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom)
    {d : MachineData} {mctx : Meta.Context} {cctx : Core.Context} {w : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    p.d = d → p.kD = Tools.ShippingGen5Sem.kDOf d → LeafFacts d → Start L mctx cctx w →
    (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W), ExpMDRTrue mctx mref cctx cref p.decl p.d.shape w raw D₀ w1) →
    ∀ raw, PostRun mctx mref cctx cref w p.decl D' b raw → ∃ n, HasConcretePackage p n p.decl b raw D'

/-- `rootEnv_of_run` -/
def ExpRootEnv : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {lvl : Lean.Expr → Nat} {X : Name} {ty val : Lean.Expr} {dd : MachineData} {w w' : W} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (M, D) w' →
    ExpMDRTrue mctx mref cctx cref X dd.shape w M D w' →
    ExpSnap (fun w _ => w) mctx mref cctx cref X w M D w' → ExpQuote mctx mref cctx cref X ty val w M D w' →
    ExpReader (fun w _ => w) mctx mref cctx cref lvl X dd w M D w' →
    (∃ d : DefinitionVal, RootInEnv (envAt cref w) X ty val d) ∧ RootReader lvl (envAt cref w) X dd

def whitelist : List Name := [``ExpMDR, ``ExpMDRTrue, ``MutMDRTie, ``MutMDREnv, ``MutMDRFlag1, ``MutMDRFlag2, ``MutMDRName, ``ExpOn, ``ExpSnap, ``ExpQuote, ``ExpReader, ``GPd,
  ``ExpFinal3, ``EnvStart, ``EnvEnd, ``ExpFinal3True, ``MutF3EnvC, ``MutF3EnvR, ``MutF3EnvE, ``MutF3Shape, ``MutF3Data, ``MutF3Post, ``MutF3NoStart, ``MutF3NoRun, ``MutF3AddWitness,
  ``MutF3NoExists, ``MutF3Lvl, ``ExpFinal3L, ``ExpFinal3LTrue, ``MutF3LEnv, ``MutF3LData, ``MutF3LSnap, ``MutF3LPost, ``ExpTop3, ``MutTop3NoLeaf, ``MutTop3NoCloses, ``ExpRootEnv,
  -- the definitions under test are unfolded too, so the comparison is against the independently written statements
  ``MachineDefinesRun, ``OnRunReads, ``RunSnap, ``RunQuote, ``RunReader]

def norm (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if whitelist.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)

def binderInfos (e : Lean.Expr) : MetaM (List BinderInfo) :=
  forallTelescope e fun xs _ => xs.toList.mapM fun x => do return (← x.fvarId!.getDecl).binderInfo

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let same (thm exp : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    unless ci.levelParams.isEmpty do throwError "{thm}: level parameters"
    let a ← norm ci.type
    let e ← norm (mkConst exp)
    unless ← withReducible (isDefEq a e) do throwError "{thm}: type is NOT the expected statement {exp}"
    -- the expected statement is closed and the binder kinds (explicit / implicit / inst-implicit) agree
    let ba ← binderInfos a
    let be ← binderInfos e
    unless ba == be do throwError "{thm}: binder kinds differ from {exp}: {repr ba} vs {repr be}"
  let differs (thm mu0 : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    let a ← norm ci.type
    let e ← norm (mkConst mu0)
    if ← withReducible (isDefEq a e) then throwError "{thm}: the MUTANT {mu0} was accepted"
  -- the definition `MachineDefinesRun` against its independent statement; mutants of the statement
  let mdr ← norm (mkConst ``MachineDefinesRun)
  let mdrE ← norm (mkConst ``ExpMDRTrue)
  -- the head binder lists (the knobs of `ExpMDR` are instantiated in `ExpMDRTrue`); compare the applied forms
  let ci ← getConstInfo ``MachineDefinesRun
  let ce ← getConstInfo ``ExpMDRTrue
  let a ← norm (← forallTelescope ci.type fun xs _ => do mkForallFVars xs (← norm (mkAppN (mkConst ``MachineDefinesRun) xs)))
  let e ← norm (← forallTelescope ce.type fun xs _ => do mkForallFVars xs (← norm (mkAppN (mkConst ``ExpMDRTrue) xs)))
  unless ← withReducible (isDefEq a e) do throwError "MachineDefinesRun is NOT the independently written statement"
  let mut nm : Nat := 0
  for mu in [``MutMDRTie, ``MutMDREnv, ``MutMDRFlag1, ``MutMDRFlag2, ``MutMDRName] do
    let cm ← getConstInfo mu
    let m ← norm (← forallTelescope cm.type fun xs _ => do mkForallFVars xs (← norm (mkAppN (mkConst mu) xs)))
    if ← withReducible (isDefEq a m) then throwError "the MUTANT {mu} of MachineDefinesRun was accepted"
    nm := nm + 1
  let _ := (mdr, mdrE)
  let A := `Tools.ShippingFGCircuitFinal3
  same (A ++ `counterLoop_final3) ``ExpFinal3True
  same (A ++ `counterLoop_final3L) ``ExpFinal3LTrue
  same (A ++ `hTop_of_leaf3) ``ExpTop3
  same (A ++ `rootEnv_of_run) ``ExpRootEnv
  for mu in [``MutF3EnvC, ``MutF3EnvR, ``MutF3EnvE, ``MutF3Shape, ``MutF3Data, ``MutF3Post, ``MutF3NoStart, ``MutF3NoRun, ``MutF3AddWitness, ``MutF3NoExists, ``MutF3Lvl] do
    differs (A ++ `counterLoop_final3) mu; nm := nm + 1
  for mu in [``MutF3LEnv, ``MutF3LData, ``MutF3LSnap, ``MutF3LPost] do
    differs (A ++ `counterLoop_final3L) mu; nm := nm + 1
  for mu in [``MutTop3NoLeaf, ``MutTop3NoCloses] do
    differs (A ++ `hTop_of_leaf3) mu; nm := nm + 1
  logInfo m!"FGCIRCUIT5 SIGNATURES: MachineDefinesRun, counterLoop_final3, counterLoop_final3L, hTop_of_leaf3, rootEnv_of_run equal their independently written COMPLETE types (hypotheses, conclusion, environments, designs, binder kinds); {nm} mutants rejected"

/-! ## 2. the hypotheses that remain, by name and by type -/

def explicitBinders (thm : Name) : MetaM (List (String × Lean.Expr)) := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs _ => do
    let mut hs : List (String × Lean.Expr) := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isExplicit then hs := hs ++ [(d.userName.toString, ← instantiateMVars d.type)]
    return hs

run_cmd liftTermElabM do
  let A := `Tools.ShippingFGCircuitFinal3
  let check (thm : Name) (expected : List String) : MetaM Unit := do
    let bs ← explicitBinders thm
    let names := bs.map (·.1)
    unless names == expected do throwError "{thm}: hypotheses are {names}, expected {expected}"
    for supplied in ["hw", "hA6", "hsrc", "htr", "hd", "hc", "hcl", "hP", "hl", "hTop", "hpost", "hE_run"] do
      if names.contains supplied then throwError "{thm}: {supplied} is a hypothesis"
    for (n, t) in bs do
      if t.getUsedConstants.contains ``sorryAx then throwError "{thm}: hypothesis {n} mentions sorryAx"
      if t.getUsedConstants.contains ``Tools.ShippingGen5FG.EntryWitness then throwError "{thm}: hypothesis {n} is the EntryWitness (ReflectsAll)"
      if t.getUsedConstants.contains ``Tools.ShippingFGCircuitBridge.DesignTransport then throwError "{thm}: hypothesis {n} is DesignTransport"
      if t.getUsedConstants.contains ``Tools.ShippingMachineEntry.MachineDefines then throwError "{thm}: hypothesis {n} is the global MachineDefines"
    let ci ← getConstInfo thm
    for o in [``Sparkle.Tests.SignalLoopTest.shift4Loop, ``Sparkle.Tests.SignalLoopTest.counterEnableLoop, ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal] do
      if ci.type.getUsedConstants.contains o then throwError "{thm}: mentions another root {o}"
    for (n, t) in bs do
      logInfo m!"FGCIRCUIT5 REMAINING {thm.getString!} {n} : {← ppExpr t}"
  check (A ++ `counterLoop_final3) ["L", "lvl", "hstart", "hr", "hdRun", "hRead", "hE"]
  check (A ++ `counterLoop_final3L) ["L", "lvl", "hstart", "hr", "hdRun", "hsnap", "hquote", "hreader"]
  logInfo "FGCIRCUIT5 HYPS: counterLoop_final3 = L lvl hstart hr hdRun hRead hE; counterLoop_final3L = L lvl hstart hr hdRun hsnap hquote hreader. Not hypotheses: hw / ReflectsAll, hA6, global MachineDefines, hsrc, DesignTransport. Laws L is an explicit argument: it remains an obligation (A.P-02 runtime laws)"

/-! ## 3. axioms of every new name -/
run_cmd liftTermElabM do
  let R := `Tools.ShippingFGCircuitRunLocal
  let R2 := `Tools.ShippingFGCircuitRunLocal2
  let A := `Tools.ShippingFGCircuitFinal3
  let names : List Name := [R ++ `machineDefinesRun_of_defines, R ++ `synthesizeFromConst_machine_invR, R ++ `machine_run_of_coreR, R ++ `machineRunJQC_of_closesR,
    R ++ `synthesizeFromConst_machineR, R ++ `synthesizeCombinationalCore_machine_soundR,
    R2 ++ `machine_trace_lets_of_streamBR, R2 ++ `machine_trace_lets_of_streamR, R2 ++ `machine_traceL_of_streamR, R2 ++ `machine_traceL_of_loopR, R2 ++ `machine_ships_wiredR,
    A ++ `leaf_topShips_of_runR, A ++ `leaf_instFree_of_runR, A ++ `hTop_of_leaf3, A ++ `counterLoop_artifact_atR, A ++ `counterLoop_final3, A ++ `rootEnv_of_run, A ++ `counterLoop_final3L]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT5 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

/-! ## 4. SNAPSHOT5: the whole structure of the observed data against the endpoint literal -/

open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote in
def mapMux : {ss : List SType} → Terms ss → Terms ss
  | _, .nil => .nil
  | _, .cons t r => .cons (.mux (.boolLit true) t t) (mapMux r)

open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineCommand in
def termsList : {ss : List SType} → Terms ss → List AnyTerm
  | _, .nil => []
  | _, .cons (s := s) t r => ⟨s, t⟩ :: termsList r

open Tools.ShippingMachineCommand in
/-- the shape as the Expr the endpoint command builds (`dataShapeE`), from the shape value -/
def shapeExprOf (s : MachineShape) : MetaM Lean.Expr := do
  let body ← match Tools.ShippingEntrySoundness.reflExpr s.body with
    | .ok b => pure b
    | .error msg => throwError msg
  let some layout := layoutE s.layout | throwError "an output type is not a bit vector"
  return dataShapeE s body layout

open Tools.ShippingMachineCommand in
/-- the data as the Expr the endpoint command builds (`dataE`/`dataPure`), from a `MachineData` value: EVERY field -/
def dataExprOf (d : MachineData) : MetaM Lean.Expr := do
  let dom ← match Tools.ShippingEntrySoundness.reflExpr d.dom with
    | .ok b => pure b
    | .error msg => throwError msg
  return mkAppN (mkConst ``MachineData.mk)
    #[← shapeExprOf d.shape, natL d.nIn, dom, natListE d.bposL, natListE d.vposL, natListE d.vwL,
      Tools.ShippingMachineCommand.listE stypeT (d.ss.map stypeE), Tools.ShippingMachineCommand.listE anyTermT (d.ls.map anyTermE), Tools.ShippingMachineCommand.listE anyTermT (d.outs.map anyTermE), termsE (termsList d.nexts)]

def literalExpr (c : Name) : MetaM Lean.Expr := do
  let ci ← getConstInfo c
  match ci.value? with
  | some v => instantiateMVars v
  | none => throwError "{c}: no value"

def perturbations (d : MachineData) : List (String × MachineData) :=
  [("nIn", { d with nIn := d.nIn + 1 }), ("dom", { d with dom := .bvar 0 }), ("bposL", { d with bposL := 7 :: d.bposL }),
   ("vposL", { d with vposL := 7 :: d.vposL }), ("vwL", { d with vwL := 9 :: d.vwL }),
   ("shape.body", { d with shape := { d.shape with body := .bvar 0 } }),
   ("shape.binders", { d with shape := { d.shape with binders := d.shape.binders ++ d.shape.binders } }),
   ("shape.loops", { d with shape := { d.shape with loops := (3, 4) :: d.shape.loops } }),
   ("outs (a term changed)", { d with outs := d.outs.map fun ⟨s, t⟩ => ⟨s, .mux (.boolLit true) t t⟩ }),
   ("nexts (a term changed)", { d with nexts := mapMux d.nexts })]

def ppAll (es : List Lean.Expr) : MetaM (List String) := es.mapM fun e => do return toString (← ppExpr e)

run_cmd liftTermElabM do
  let env ← getEnv
  let x := ``Sparkle.Tests.SignalLoopTest.counterLoop
  let lit ← literalExpr ``Sparkle.Tests.SignalLoopTest.counterLoop.machineData
  let other ← literalExpr ``Sparkle.Tests.SignalLoopTest.shift4Loop.machineData
  let some E := Tools.ShippingGen5Acc.entry₀ env x | throwError "{x}: no entry constant in this environment"
  let some s := machineShape? false [] E (structEnv env) | throwError "{x}: machineShape? none"
  let some d := Tools.ShippingGen5DataOf.dataOfAt (fun _ => 1000000) E (structEnv env) s | throwError "{x}: dataOfAt none"
  let dE ← dataExprOf d
  -- whole-structure comparison with the endpoint literal (an Expr built field by field from the observed value)
  unless dE == lit do throwError "{x}: the reader's data (dataOfAt) differs from the endpoint literal machineData (whole structure)"
  unless (← shapeExprOf s) == (← shapeExprOf d.shape) do throwError "{x}: machineShape? and the data's shape differ"
  -- negative controls: the comparison must reject
  if dE == other then throwError "negative control: counterLoop's data equals shift4Loop's"
  let mut np : Nat := 0
  for (nm, d') in perturbations d do
    if (← dataExprOf d') == lit then throwError "negative control: the perturbation of {nm} is not detected"
    np := np + 1
  -- the three facts of the run-local boundary, on the environment the run would read (envR = envR' = this environment)
  let some ci := env.find? x | throwError "{x}: not in env"
  let ec := entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)
  unless (certifiedShape? false [] ec).isNone do throwError "{x}: certifiedShape? is not none"
  unless (mixedCertifiedShape? false [] ec (instancePredicate env)).isNone do throwError "{x}: mixedCertifiedShape? is not none"
  let some s2 := machineShape? false [] ec (structEnv env) | throwError "{x}: machineShape? of the entry is none"
  unless (← shapeExprOf s2) == (← shapeExprOf s) do throwError "{x}: the entry's machineShape? differs from the shape the reader used"
  -- the observed values, exactly
  let outsS ← ppAll (d.outs.map Tools.ShippingMachineCommand.anyTermE)
  let nextsS ← ppAll (Tools.ShippingMachineCommand.termsE (termsList d.nexts) :: [])
  let bodyS ← ppAll [d.shape.body]
  logInfo m!"FGCIRCUIT5 SNAPSHOT5 observed (this build's environment, dataOfAt with fuel 1000000): nIn={d.nIn} ss={d.ss.length} sorts, bposL={d.bposL} vposL={d.vposL} vwL={d.vwL} binders={d.shape.binders.map (·.1)} layout={reprStr d.shape.layout} runs={d.shape.runs} insts={d.shape.insts.length} loops={d.shape.loops} instFields={d.shape.instFields} instOrigins={d.shape.instOrigins.length}"
  logInfo m!"FGCIRCUIT5 SNAPSHOT5 observed terms: outs={outsS} lets={d.ls.length} nexts={nextsS} body={bodyS}"
  logInfo m!"FGCIRCUIT5 SNAPSHOT5: counterLoop's reader data (dataOfAt) is EQUAL to the endpoint literal machineData over its WHOLE structure (the Expr the endpoint command builds, rebuilt field by field from the observed value: shape binders/body/layout/runs/insts/loops/instFields/instOrigins, nIn, dom, positions, sorts, lets, outs, nexts as terms); the comparison rejects shift4Loop's data and {np} single-field perturbations; certifiedShape? = none, mixedCertifiedShape? = none, and machineShape? equals the reader's shape on this environment. These are values of ONE environment (fuel 1000000), NOT the kernel statements RootReader / RunReader / MachineDefinesRun for an arbitrary run, and NOT a proof that the premises are satisfiable together"

end Tests.Gen5.FGCircuitPilotCheck5
