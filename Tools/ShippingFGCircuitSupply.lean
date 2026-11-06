import Tools.ShippingFGCircuitRootsAt
set_option autoImplicit false
-- FG circuit pilot S1c, unit 3: what can be supplied of the run premises `hr`, `hE`, `hd`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # Supplying the run premises of the four roots

`hc` (MachineCloses) is already supplied (`X.machine_closes`). For the others:

* `hr` (the run succeeds, `RunsTo (synthesizeCombinational…) … w (m, design) w'`): NOT suppliable. `RunsTo` is the relational semantics of a `MetaM` computation; no theorem in this
  tree says that the run of the compiler on a given declaration EXISTS (`MachineCloses` is "if the machine synthesis runs it does not return `none`", not an existence
  statement). It stays a premise of every root; it is the "compile succeeds" side of `compileCircuit … = .ok artifact`. FG row: the entry `EntryWitness`/`A.P-04 run`.
* `hE` (`RootInEnv (envAt cref w)`), `hd` (`MachineDefines`): both are statements about ENVIRONMENTS that the run reads at (up to) three different worlds
  (`getConstInfo` at `w1`, `getEnv` at `w5`, `getEnv` at `w7`, each `envAt cref wᵢ`). This file proves what they REDUCE to:
  - `StaticEnv cref E`: the Core state carries one environment `E` at every world (the open `EnvSnapshot` of `Tools/ShippingEntryReadsLinked.lean`, made global);
  - env-level facts about the ONE value `E`: `RootInEnv E …`, `MachineDefinesAt E X shape`, `BoundaryRowsInEnv E`. They are statements about a closed `Environment` value, so they are
    CHECKABLE on the actual snapshot (`FGCircuitPilotCheck2`'s `SNAPSHOT2` lines run them in `MetaM`), but a kernel proof about the real compiler environment is not possible.
  What remains unsupplied: `StaticEnv` (a frame property of the Core state across the run) and the three env-level facts (FG rows: ENV/cache, reader production ↔ model,
  `C.EN-4`). They are not proved or assumed anywhere as TRUSTED; they are named premises of the `_static` theorems. -/
namespace Tools.ShippingFGCircuitSupply
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5DeclConnect
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Sparkle.Tests.SignalLoopTest
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry (MachineDefines MachineCloses)
open Tools.ShippingEntryReadsLinked (envAt)

/-- the Core state holds one environment at every world -/
def StaticEnv (cref : ST.Ref IO.RealWorld Core.State) (E : Environment) : Prop := ∀ w, envAt cref w = E

/-- `MachineDefines` as a statement about one environment `E` (what the three reads of the run agree on under `StaticEnv`). -/
def MachineDefinesAt (E : Environment) (declName : Name) (shape : MachineShape) : Prop :=
  ∀ ci : ConstantInfo, E.find? declName = some ci →
    certifiedShape? false [] (entryConst true false [] ci (instancePredicate E) (userInliner E) (structEnv E)) = none ∧
    mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate E) (userInliner E) (structEnv E)) (instancePredicate E) = none ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate E) (userInliner E) (structEnv E)) (structEnv E) = some shape

theorem machineDefines_of_static {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {E : Environment} {declName : Name} {shape : MachineShape}
    (hs : StaticEnv cref E) (h : MachineDefinesAt E declName shape) : MachineDefines mctx mref cctx cref declName shape := by
  intro w1 ci w2 w5 envR w6 w7 envR' w8 hget henv henv'
  have hci : E.find? declName = some ci := by
    have := Tools.ShippingEntryReadsLinked.getConstInfo_value hget
    rwa [hs] at this
  have h5 : envR = E := by rw [Tools.ShippingEntryReadsLinked.getEnv_value henv, hs]
  have h7 : envR' = E := by rw [Tools.ShippingEntryReadsLinked.getEnv_value henv', hs]
  subst h5 h7
  exact h ci hci

theorem rootInEnv_of_static {cref : ST.Ref IO.RealWorld Core.State} {E : Environment} {w : Void IO.RealWorld} {X : Name} {ty val : Lean.Expr}
    {d : DefinitionVal} (hs : StaticEnv cref E) (h : RootInEnv E X ty val d) : RootInEnv (envAt cref w) X ty val d := by
  rw [hs]; exact h

theorem boundaryRows_of_static {cref : ST.Ref IO.RealWorld Core.State} {E : Environment} {w : Void IO.RealWorld}
    (hs : StaticEnv cref E) (h : BoundaryRowsInEnv E) : BoundaryRowsInEnv (envAt cref w) := by
  rw [hs]; exact h

/-- the part of `hE` that the run DOES give: it read `X` from the environment at the world of its `getConstInfo` (no frame assumption, no quote) -/
theorem run_reads_root {X : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore X [] false) mctx mref cctx cref w (M, D) w') :
    ∃ (w1 : Void IO.RealWorld) (ci : ConstantInfo), (envAt cref w1).find? X = some ci := by
  obtain ⟨_, _, ci, w1, _, _, _, _, _, hget, _, _⟩ := synthesizeCombinationalCore_reads hr
  exact ⟨w1, ci, Tools.ShippingEntryReadsLinked.getConstInfo_value hget⟩

/-- under `StaticEnv` that is the start environment: the run's root is a constant of `E` -/
theorem run_reads_root_static {X : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    {E : Environment} (hs : StaticEnv cref E)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore X [] false) mctx mref cctx cref w (M, D) w') :
    ∃ ci : ConstantInfo, (envAt cref w).find? X = some ci := by
  obtain ⟨w1, ci, h⟩ := run_reads_root hr
  rw [hs] at h ⊢
  exact ⟨ci, h⟩

/-! ## the four roots with `hE`, `hd`, `hB` replaced by env-level facts about one environment `E` and `StaticEnv` -/

theorem counterLoop_root_static {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} {E : Environment} (hs : StaticEnv cref E)
    (hE : RootInEnv E ``counterLoop counterLoopType counterLoopValue d)
    (hd : MachineDefinesAt E ``counterLoop counterLoop.machineData.shape)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``counterLoop [] false) mctx mref cctx cref w (m, design) w') :
    ∃ (mm : MonoTy shCounter), SourceDenotesMono (envAt cref w) ``counterLoop [] shCounter mm ∧
      Tools.ShippingMachineAuto.MachineTrace ``counterLoop counterLoop.machineData m (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shCounter mm bools bits) :=
  counterLoop_root_at (rootInEnv_of_static hs hE) hr (machineDefines_of_static hs hd)

theorem shift4Loop_root_static {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} {E : Environment} (hs : StaticEnv cref E)
    (hE : RootInEnv E ``shift4Loop shift4LoopType shift4LoopValue d)
    (hd : MachineDefinesAt E ``shift4Loop shift4Loop.machineData.shape)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``shift4Loop [] false) mctx mref cctx cref w (m, design) w') :
    ∃ (mm : MonoTy shShift4), SourceDenotesMono (envAt cref w) ``shift4Loop [] shShift4 mm ∧
      Tools.ShippingMachineAuto.MachineTrace ``shift4Loop shift4Loop.machineData m (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shShift4 mm bools bits) :=
  shift4Loop_root_at (rootInEnv_of_static hs hE) hr (machineDefines_of_static hs hd)

theorem counterEnableLoop_root_static {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} {E : Environment} (hs : StaticEnv cref E)
    (hE : RootInEnv E ``counterEnableLoop counterEnableLoopType counterEnableLoopValue d)
    (hd : MachineDefinesAt E ``counterEnableLoop counterEnableLoop.machineData.shape)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``counterEnableLoop [] false) mctx mref cctx cref w (m, design) w') :
    ∃ (mm : MonoTy shEnable), SourceDenotesMono (envAt cref w) ``counterEnableLoop [] shEnable mm ∧
      Tools.ShippingMachineAuto.MachineTrace ``counterEnableLoop counterEnableLoop.machineData m (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shEnable mm bools bits) :=
  counterEnableLoop_root_at (rootInEnv_of_static hs hE) hr (machineDefines_of_static hs hd)

theorem arbiterSignal_root_static {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} {E : Environment} (hs : StaticEnv cref E)
    (hE : RootInEnv E ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue d)
    (hB : BoundaryRowsInEnv E)
    (hd : MachineDefinesAt E ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal [] false)
      mctx mref cctx cref w (m, design) w') :
    ∃ (mm : shArbiter.Ty), SourceDenotes (envAt cref w) ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal [] shArbiter mm ∧
      Tools.ShippingMachineAuto.MachineTrace ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
        Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData m (fun i : DomainConfig => i)
        (fun i bools bits => shArbiter.obs (dom := fun i : DomainConfig => i) mm i bools bits) :=
  arbiterSignal_root_at (rootInEnv_of_static hs hE) (boundaryRows_of_static hs hB) hr (machineDefines_of_static hs hd)

end Tools.ShippingFGCircuitSupply

#print axioms Tools.ShippingFGCircuitSupply.machineDefines_of_static
#print axioms Tools.ShippingFGCircuitSupply.run_reads_root
#print axioms Tools.ShippingFGCircuitSupply.counterLoop_root_static
#print axioms Tools.ShippingFGCircuitSupply.arbiterSignal_root_static
