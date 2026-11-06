import Tools.ShippingFGCircuitRootsAt
import Tools.ShippingFGCircuitFunc
import Tools.ShippingGenFGLedgerPremisesG
set_option autoImplicit false
-- FG circuit pilot S1c, unit 2: the root statements and the generated package are about the SAME artifact.
-- No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # The root's source meaning, the run's module and the `genGP` package: one artifact

`Tools.ShippingFGCircuitRoots.X_ships_at` talks about the module `b` that a run of `synthesizeCombinational X` returns, with the source meaning `mm`
read from the environment `envAt cref w` of that run. The generated table `genGP lvl hs genData₀ (envAt cref w)` of
`Tools/ShippingGenFGLedgerPremisesG.lean` talks about a package `p` for `X` at the SAME environment, and `TopShips p n X b raw D` about the same `b`.

This file states, per root, that these are one artifact (`RootArtifactMono`: same environment, same source name, same parameters `[]`, same `b`/`D`,
the SAME `mm` in `SourceDenotes(Mono)` and in the observation correspondence with the package `p`). The link between the package and the endpoint
the root theorems use is the NAMED condition `EndpointLink`: the package's data, input count and observation are the endpoint's
(`X.machineData`, the shape's argument count, `monoObs sh mm`). `p.decl = X` is NOT part of the link: it is proved from `genP_decl`.

What is NOT proved (named, not hidden): (a) `EndpointLink` — `p.d` is `dataOfAt …` of the constant (`GenPDEdgesStmt`) while `X.machineData` is produced by
`readMachine`; their equality is the "`dataOfAt` ↔ `readMachine`" bridge that `Tools/ShippingGen5DataOf.lean` records as NOT in the tree; and `p.src` is the
generated `genSem` observation. (b) `TopShips p n X b raw D` for the printed `b` — a hypothesis `hTop` (it is the `TopShips` conjunct of the FG
conclusion; no theorem in this tree lifts `MachineShips`/`WiredConclusion` to `TopShips`, that is `StepStmt`). -/
namespace Tools.ShippingFGCircuitArtifact
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG Tools.ShippingGen2
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Sparkle.Tests.SignalLoopTest
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMachineEntry (MachineDefines MachineCloses)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingMachineAuto (MachineData)

/-- The package is the endpoint: its data, its number of declared inputs, its observation. (`p.decl = X` is not here: `genP_decl`.) -/
structure EndpointLink {ι : Type} {dom : ι → DomainConfig} (d : MachineData) (kD : Nat)
    (obs : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (p : Pkg ι dom) : Prop where
  data : p.d = d
  kD_eq : p.kD = kD
  src : ∀ i bools bits, p.src i bools bits = obs i bools bits

/-- One artifact, domain-fixed root: the package from `P` at the declaration, the source meaning `mm` (from the environment `env`), their
observation correspondence, and the concrete package for the printed `b` (`TopShips`) for every `raw` the post-relation accepts. -/
def RootArtifactMono {ι : Type} (env : Environment) (P : Pkgs ι (fun _ => defaultDomain))
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop) (X : Name) (sh : SigShape) (mm : MonoTy sh)
    (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (p : Pkg ι (fun _ => defaultDomain)) : Prop :=
  P X = some p ∧ SourceDenotesMono env X [] sh mm ∧ ObservationsEqualMono sh mm p ∧
    ∀ raw, Post b raw → ∃ n, HasConcretePackage p n X b raw D

/-- the domain-polymorphic root (the arbiter) -/
def RootArtifact {ι : Type} {dom : ι → DomainConfig} (env : Environment) (P : Pkgs ι dom)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop) (X : Name) (sh : SigShape) (mm : sh.Ty)
    (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (p : Pkg ι dom) : Prop :=
  P X = some p ∧ SourceDenotes env X [] sh mm ∧ ObservationsEqual sh mm p ∧
    ∀ raw, Post b raw → ∃ n, HasConcretePackage p n X b raw D

/-- the artifact statement gives the (mono) FG circuit conclusion form: `FGCircuitConclusion` with `SourceDenotesMono`/`ObservationsEqualMono` -/
def FGCircuitConclusionMono {ι : Type} (env : Environment) (P : Pkgs ι (fun _ => defaultDomain))
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop) (X : Name) (params : List (String × Nat))
    (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) : Prop :=
  (∃ raw, Post b raw) ∧
  ∀ raw, Post b raw → ∃ (sh : SigShape) (m : MonoTy sh) (p : Pkg ι (fun _ => defaultDomain)) (n : Nat),
    P X = some p ∧ SourceDenotesMono env X params sh m ∧ HasConcretePackage p n X b raw D ∧ ObservationsEqualMono sh m p

theorem fgCircuitConclusionMono_of_artifact {ι : Type} {env : Environment} {P : Pkgs ι (fun _ => defaultDomain)}
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {X : Name} {sh : SigShape} {mm : MonoTy sh}
    {b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {p : Pkg ι (fun _ => defaultDomain)}
    (hpost : ∃ raw, Post b raw) (h : RootArtifactMono env P Post X sh mm b D p) : FGCircuitConclusionMono env P Post X [] b D := by
  obtain ⟨hP, hS, hO, hT⟩ := h
  refine ⟨hpost, fun raw hraw => ?_⟩
  obtain ⟨n, hn⟩ := hT raw hraw
  exact ⟨sh, mm, p, n, hP, hS, hn, hO⟩

theorem observationsEqualMono_of_link {ι : Type} {sh : SigShape} {mm : MonoTy sh} {d : MachineData} {k : Nat} {p : Pkg ι (fun _ => defaultDomain)}
    (hsm : ShapeMatchesMono sh d k)
    (hl : EndpointLink d k (fun _ bools bits => monoObs sh mm bools bits) p) : ObservationsEqualMono sh mm p :=
  ⟨by rw [hl.data, hl.kD_eq]; exact hsm, fun i bools bits => (hl.src i bools bits).symm⟩

theorem observationsEqual_of_link {ι : Type} {dom : ι → DomainConfig} {sh : SigShape} {mm : sh.Ty} {d : MachineData} {k : Nat} {p : Pkg ι dom}
    (hsm : ShapeMatches sh d k)
    (hl : EndpointLink d k (fun i bools bits => sh.obs (dom := dom) mm i bools bits) p) : ObservationsEqual sh mm p :=
  ⟨by rw [hl.data, hl.kD_eq]; exact hsm, fun i bools bits => (hl.src i bools bits).symm⟩

/-- the generated table's package for `X` is a package of `X` (`genP_decl`, no hypothesis) -/
theorem genGP_decl {ι : Type} {dom : ι → DomainConfig} (lvl : Lean.Expr → Nat)
    (genData₀ : (env : Environment) → (E : ConstantInfo) →
      Option (Tools.ShippingGen5Sem.GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env)))
    (env : Environment) {X : Name} {p : Pkg ι dom}
    (hp : Tools.ShippingGenFGLedgerPremises.genGP lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) genData₀ env X = some p) : p.decl = X :=
  Tools.ShippingGen5Acc.genP_decl
    (Tools.ShippingGenFGLedgerPremises.genKit lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) env (genData₀ env))
    (Tools.ShippingGen5Acc.factsOf_genS_assembled'' (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (genData₀ env)) hp

/-! ## the endpoint data matches the root's shape (kernel `decide` on the generated `machineData`) -/
theorem counterLoop_shape : ShapeMatchesMono shCounter counterLoop.machineData 0 := by unfold ShapeMatchesMono; decide
theorem shift4Loop_shape : ShapeMatchesMono shShift4 shift4Loop.machineData 1 := by unfold ShapeMatchesMono; decide
theorem counterEnableLoop_shape : ShapeMatchesMono shEnable counterEnableLoop.machineData 1 := by unfold ShapeMatchesMono; decide
theorem arbiterSignal_shape :
    ShapeMatches shArbiter Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData (shArbiter.args.length + 1) := by decide

theorem counterLoop_artifact_at {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} {ι : Type} {P : Pkgs ι (fun _ => defaultDomain)} {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop}
    {p : Pkg ι (fun _ => defaultDomain)}
    (hE : RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, design) w')
    (hd : MachineDefines mctx mref cctx cref ``counterLoop counterLoop.machineData.shape)
    (hP : P ``counterLoop = some p) (hdecl : p.decl = ``counterLoop)
    (hl : EndpointLink counterLoop.machineData 0 (fun _ bools bits => monoObs shCounter counterLoop bools bits) p)
    (hTop : ∀ raw, Post b raw → ∃ n, TopShips p n ``counterLoop b raw design) :
    ∃ mm : MonoTy shCounter, RootArtifactMono (envAt cref w) P Post ``counterLoop shCounter mm b design p ∧
      WiredConclusion ``counterLoop counterLoop.machineData (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shCounter mm bools bits) b :=
  ⟨counterLoop, ⟨hP, counterLoop_denotes hE, observationsEqualMono_of_link counterLoop_shape hl,
      fun raw hraw => (hTop raw hraw).imp fun _ hn => ⟨hdecl, hn⟩⟩,
    counterLoop.machine_ships_wired hr hd (counterLoop.machine_closes mctx mref cctx cref)⟩

theorem shift4Loop_artifact_at {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} {ι : Type} {P : Pkgs ι (fun _ => defaultDomain)} {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop}
    {p : Pkg ι (fun _ => defaultDomain)}
    (hE : RootInEnv (envAt cref w) ``shift4Loop shift4LoopType shift4LoopValue d)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``shift4Loop) mctx mref cctx cref w (b, design) w')
    (hd : MachineDefines mctx mref cctx cref ``shift4Loop shift4Loop.machineData.shape)
    (hP : P ``shift4Loop = some p) (hdecl : p.decl = ``shift4Loop)
    (hl : EndpointLink shift4Loop.machineData 1 (fun _ bools bits => monoObs shShift4 shift4Loop bools bits) p)
    (hTop : ∀ raw, Post b raw → ∃ n, TopShips p n ``shift4Loop b raw design) :
    ∃ mm : MonoTy shShift4, RootArtifactMono (envAt cref w) P Post ``shift4Loop shShift4 mm b design p ∧
      WiredConclusion ``shift4Loop shift4Loop.machineData (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shShift4 mm bools bits) b :=
  ⟨shift4Loop, ⟨hP, shift4Loop_denotes hE, observationsEqualMono_of_link shift4Loop_shape hl,
      fun raw hraw => (hTop raw hraw).imp fun _ hn => ⟨hdecl, hn⟩⟩,
    shift4Loop.machine_ships_wired hr hd (shift4Loop.machine_closes mctx mref cctx cref)⟩

theorem counterEnableLoop_artifact_at {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} {ι : Type} {P : Pkgs ι (fun _ => defaultDomain)} {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop}
    {p : Pkg ι (fun _ => defaultDomain)}
    (hE : RootInEnv (envAt cref w) ``counterEnableLoop counterEnableLoopType counterEnableLoopValue d)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterEnableLoop) mctx mref cctx cref w (b, design) w')
    (hd : MachineDefines mctx mref cctx cref ``counterEnableLoop counterEnableLoop.machineData.shape)
    (hP : P ``counterEnableLoop = some p) (hdecl : p.decl = ``counterEnableLoop)
    (hl : EndpointLink counterEnableLoop.machineData 1 (fun _ bools bits => monoObs shEnable counterEnableLoop bools bits) p)
    (hTop : ∀ raw, Post b raw → ∃ n, TopShips p n ``counterEnableLoop b raw design) :
    ∃ mm : MonoTy shEnable, RootArtifactMono (envAt cref w) P Post ``counterEnableLoop shEnable mm b design p ∧
      WiredConclusion ``counterEnableLoop counterEnableLoop.machineData (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shEnable mm bools bits) b :=
  ⟨counterEnableLoop, ⟨hP, counterEnableLoop_denotes hE, observationsEqualMono_of_link counterEnableLoop_shape hl,
      fun raw hraw => (hTop raw hraw).imp fun _ hn => ⟨hdecl, hn⟩⟩,
    counterEnableLoop.machine_ships_wired hr hd (counterEnableLoop.machine_closes mctx mref cctx cref)⟩

theorem arbiterSignal_artifact_at {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} {P : Pkgs DomainConfig (fun i => i)}
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {p : Pkg DomainConfig (fun i => i)}
    (hE : RootInEnv (envAt cref w) ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue d)
    (hB : BoundaryRowsInEnv (envAt cref w))
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal) mctx mref cctx cref w
      (b, design) w')
    (hd : MachineDefines mctx mref cctx cref ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
      Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape)
    (hP : P ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal = some p) (hdecl : p.decl = ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal)
    (hl : EndpointLink Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData (shArbiter.args.length + 1)
      (fun i bools bits => shArbiter.obs (dom := fun i : DomainConfig => i)
        (fun D => @Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D) i bools bits) p)
    (hTop : ∀ raw, Post b raw → ∃ n, TopShips p n ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal b raw design) :
    ∃ mm : shArbiter.Ty, RootArtifact (envAt cref w) P Post ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal shArbiter mm b design p ∧
      WiredConclusion ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData
        (fun i : DomainConfig => i) (fun i bools bits => shArbiter.obs (dom := fun i : DomainConfig => i) mm i bools bits) b :=
  ⟨_, ⟨hP, arbiterSignal_denotes hE, observationsEqual_of_link arbiterSignal_shape hl,
      fun raw hraw => (hTop raw hraw).imp fun _ hn => ⟨hdecl, hn⟩⟩,
    Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_ships_wired hr hd
      (Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_closes mctx mref cctx cref)⟩

theorem counterLoop_artifact_genGP {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} {ι : Type} (lvl : Lean.Expr → Nat)
    (genData₀ : (env : Environment) → (E : ConstantInfo) →
      Option (Tools.ShippingGen5Sem.GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env)))
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {p : Pkg ι (fun _ => defaultDomain)}
    (hE : RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, design) w')
    (hd : MachineDefines mctx mref cctx cref ``counterLoop counterLoop.machineData.shape)
    (hP : Tools.ShippingGenFGLedgerPremises.genGP (ι := ι) (dom := fun _ => defaultDomain) lvl
      (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) genData₀ (envAt cref w) ``counterLoop = some p)
    (hl : EndpointLink counterLoop.machineData 0 (fun _ bools bits => monoObs shCounter counterLoop bools bits) p)
    (hTop : ∀ raw, Post b raw → ∃ n, TopShips p n ``counterLoop b raw design) :
    ∃ mm : MonoTy shCounter, RootArtifactMono (envAt cref w)
      (Tools.ShippingGenFGLedgerPremises.genGP (ι := ι) (dom := fun _ => defaultDomain) lvl
        (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) genData₀ (envAt cref w)) Post ``counterLoop shCounter mm b design p ∧
      WiredConclusion ``counterLoop counterLoop.machineData (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shCounter mm bools bits) b :=
  counterLoop_artifact_at hE hr hd hP (genGP_decl lvl genData₀ _ hP) hl hTop

theorem shift4Loop_artifact_genGP {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} {ι : Type} (lvl : Lean.Expr → Nat)
    (genData₀ : (env : Environment) → (E : ConstantInfo) →
      Option (Tools.ShippingGen5Sem.GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env)))
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {p : Pkg ι (fun _ => defaultDomain)}
    (hE : RootInEnv (envAt cref w) ``shift4Loop shift4LoopType shift4LoopValue d)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``shift4Loop) mctx mref cctx cref w (b, design) w')
    (hd : MachineDefines mctx mref cctx cref ``shift4Loop shift4Loop.machineData.shape)
    (hP : Tools.ShippingGenFGLedgerPremises.genGP (ι := ι) (dom := fun _ => defaultDomain) lvl
      (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) genData₀ (envAt cref w) ``shift4Loop = some p)
    (hl : EndpointLink shift4Loop.machineData 1 (fun _ bools bits => monoObs shShift4 shift4Loop bools bits) p)
    (hTop : ∀ raw, Post b raw → ∃ n, TopShips p n ``shift4Loop b raw design) :
    ∃ mm : MonoTy shShift4, RootArtifactMono (envAt cref w)
      (Tools.ShippingGenFGLedgerPremises.genGP (ι := ι) (dom := fun _ => defaultDomain) lvl
        (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) genData₀ (envAt cref w)) Post ``shift4Loop shShift4 mm b design p ∧
      WiredConclusion ``shift4Loop shift4Loop.machineData (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shShift4 mm bools bits) b :=
  shift4Loop_artifact_at hE hr hd hP (genGP_decl lvl genData₀ _ hP) hl hTop

theorem counterEnableLoop_artifact_genGP {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} {ι : Type} (lvl : Lean.Expr → Nat)
    (genData₀ : (env : Environment) → (E : ConstantInfo) →
      Option (Tools.ShippingGen5Sem.GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env)))
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {p : Pkg ι (fun _ => defaultDomain)}
    (hE : RootInEnv (envAt cref w) ``counterEnableLoop counterEnableLoopType counterEnableLoopValue d)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterEnableLoop) mctx mref cctx cref w (b, design) w')
    (hd : MachineDefines mctx mref cctx cref ``counterEnableLoop counterEnableLoop.machineData.shape)
    (hP : Tools.ShippingGenFGLedgerPremises.genGP (ι := ι) (dom := fun _ => defaultDomain) lvl
      (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) genData₀ (envAt cref w) ``counterEnableLoop = some p)
    (hl : EndpointLink counterEnableLoop.machineData 1 (fun _ bools bits => monoObs shEnable counterEnableLoop bools bits) p)
    (hTop : ∀ raw, Post b raw → ∃ n, TopShips p n ``counterEnableLoop b raw design) :
    ∃ mm : MonoTy shEnable, RootArtifactMono (envAt cref w)
      (Tools.ShippingGenFGLedgerPremises.genGP (ι := ι) (dom := fun _ => defaultDomain) lvl
        (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) genData₀ (envAt cref w)) Post ``counterEnableLoop shEnable mm b design p ∧
      WiredConclusion ``counterEnableLoop counterEnableLoop.machineData (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shEnable mm bools bits) b :=
  counterEnableLoop_artifact_at hE hr hd hP (genGP_decl lvl genData₀ _ hP) hl hTop

theorem arbiterSignal_artifact_genGP {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} (lvl : Lean.Expr → Nat)
    (genData₀ : (env : Environment) → (E : ConstantInfo) →
      Option (Tools.ShippingGen5Sem.GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env)))
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {p : Pkg DomainConfig (fun i => i)}
    (hE : RootInEnv (envAt cref w) ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue d)
    (hB : BoundaryRowsInEnv (envAt cref w))
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal) mctx mref cctx cref w
      (b, design) w')
    (hd : MachineDefines mctx mref cctx cref ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
      Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape)
    (hP : Tools.ShippingGenFGLedgerPremises.genGP (ι := DomainConfig) (dom := fun i => i) lvl
      (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) genData₀ (envAt cref w) ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal = some p)
    (hl : EndpointLink Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData (shArbiter.args.length + 1)
      (fun i bools bits => shArbiter.obs (dom := fun i : DomainConfig => i)
        (fun D => @Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D) i bools bits) p)
    (hTop : ∀ raw, Post b raw → ∃ n, TopShips p n ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal b raw design) :
    ∃ mm : shArbiter.Ty, RootArtifact (envAt cref w)
      (Tools.ShippingGenFGLedgerPremises.genGP (ι := DomainConfig) (dom := fun i => i) lvl
        (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) genData₀ (envAt cref w)) Post
      ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal shArbiter mm b design p ∧
      WiredConclusion ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData
        (fun i : DomainConfig => i) (fun i bools bits => shArbiter.obs (dom := fun i : DomainConfig => i) mm i bools bits) b :=
  arbiterSignal_artifact_at hE hB hr hd hP (genGP_decl lvl genData₀ _ hP) hl hTop

end Tools.ShippingFGCircuitArtifact

#print axioms Tools.ShippingFGCircuitArtifact.counterLoop_artifact_genGP
#print axioms Tools.ShippingFGCircuitArtifact.shift4Loop_artifact_genGP
#print axioms Tools.ShippingFGCircuitArtifact.counterEnableLoop_artifact_genGP
#print axioms Tools.ShippingFGCircuitArtifact.arbiterSignal_artifact_genGP
