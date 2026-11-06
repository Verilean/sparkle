import Tools.ShippingFGCircuitRoots
set_option autoImplicit false
-- FG circuit pilot S1b. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # Roots specialised to the run's start environment

`Tools.ShippingFGCircuitRoots.X_root` takes a free `env`, independent of the run. Here the published statements fix `env := envAt cref w`, the
environment of the START world `w` of the very run `hr : RunsTo (synthesizeCombinational…) … cref w … w'`, in the source-meaning claim AND in
`RootInEnv`. What is still NOT supplied (named premises of every theorem below, not hidden):

* `hE : RootInEnv (envAt cref w) X ty val d` — that the run's start environment holds `X` with the quoted type and value (no theorem gives this yet);
* `hr` — that the run succeeds (no theorem gives this yet);
* `hd : MachineDefines …`;
* for the arbiter, `hB : BoundaryRowsInEnv (envAt cref w)` — the three auxiliary `abbrev`s are the literals `bvAbbrevRow` assumes.

`hc : MachineCloses` is supplied here (`X.machine_closes`, generated from the data; it is a theorem for ALL contexts). -/
namespace Tools.ShippingFGCircuitRoots
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5DeclConnect
open Tools.ShippingFGCircuit Sparkle.Tests.SignalLoopTest
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMachineEntry (MachineDefines MachineCloses)
open Tools.ShippingEntryReadsLinked (envAt)

/-- the arbiter's three auxiliary declarations, as `bvAbbrevRow` assumes them, in the environment `env` (an explicit condition; `CD` itself does
not read the environment for these names). -/
def BoundaryRowsInEnv (env : Environment) : Prop :=
  ∀ (nm : Name) (k : Nat), (nm, k) ∈ [(`stIdle, 0), (`stGrantA, 1), (`stGrantB, 2)] →
    ∃ d : DefinitionVal, env.find? (privAbbrev nm) = some (.defnInfo d) ∧ d.levelParams = [] ∧ d.type = eBV 2 ∧ d.value = eBVLit 2 k

/-! ## denotation lemmas: `RootInEnv env` gives `SourceDenotes(Mono) env` with the meaning the Lean constant itself -/

theorem counterLoop_denotes {env : Environment} {d : DefinitionVal} (hE : RootInEnv env ``counterLoop counterLoopType counterLoopValue d) :
    SourceDenotesMono env ``counterLoop [] shCounter counterLoop := by
  obtain ⟨hf, hl, ht, hv⟩ := hE
  refine ⟨rfl, d, hf, hl, ?_, ?_⟩
  · show (if d.levelParams.isEmpty = true then monoGo [] d.type else none) = some shCounter
    rw [hl, ht]; simpa using shCounter_of_type
  · rw [hv]; exact counterLoop_cd

theorem shift4Loop_denotes {env : Environment} {d : DefinitionVal} (hE : RootInEnv env ``shift4Loop shift4LoopType shift4LoopValue d) :
    SourceDenotesMono env ``shift4Loop [] shShift4 shift4Loop := by
  obtain ⟨hf, hl, ht, hv⟩ := hE
  refine ⟨rfl, d, hf, hl, ?_, ?_⟩
  · show (if d.levelParams.isEmpty = true then monoGo [] d.type else none) = some shShift4
    rw [hl, ht]; simpa using shShift4_of_type
  · rw [hv]; exact shift4Loop_cd

theorem counterEnableLoop_denotes {env : Environment} {d : DefinitionVal}
    (hE : RootInEnv env ``counterEnableLoop counterEnableLoopType counterEnableLoopValue d) :
    SourceDenotesMono env ``counterEnableLoop [] shEnable counterEnableLoop := by
  obtain ⟨hf, hl, ht, hv⟩ := hE
  refine ⟨rfl, d, hf, hl, ?_, ?_⟩
  · show (if d.levelParams.isEmpty = true then monoGo [] d.type else none) = some shEnable
    rw [hl, ht]; simpa using shEnable_of_type
  · rw [hv]; exact counterEnableLoop_cd

theorem arbiterSignal_denotes {env : Environment} {d : DefinitionVal}
    (hE : RootInEnv env ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue d) :
    SourceDenotes env ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal [] shArbiter (fun D => @Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D) := by
  obtain ⟨hf, hl, ht, hv⟩ := hE
  refine ⟨rfl, .defnInfo d, hf, ?_, d, hf, hl, ?_⟩
  · show (if d.levelParams.isEmpty = true then sigShape? d.type else none) = some shArbiter
    rw [hl, ht]; simpa using shArbiter_of_type
  · rw [hv]; exact arbiterSignal_cd

/-! ## the four roots at the run's start environment (`hc` supplied by `X.machine_closes`) -/

theorem counterLoop_root_at {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} (hE : RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``counterLoop [] false) mctx mref cctx cref w (m, design) w')
    (hd : MachineDefines mctx mref cctx cref ``counterLoop counterLoop.machineData.shape) :
    ∃ (mm : MonoTy shCounter), SourceDenotesMono (envAt cref w) ``counterLoop [] shCounter mm ∧
      Tools.ShippingMachineAuto.MachineTrace ``counterLoop counterLoop.machineData m (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shCounter mm bools bits) :=
  ⟨counterLoop, counterLoop_denotes hE, counterLoop.machine_sound hr hd (counterLoop.machine_closes mctx mref cctx cref)⟩

theorem shift4Loop_root_at {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} (hE : RootInEnv (envAt cref w) ``shift4Loop shift4LoopType shift4LoopValue d)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``shift4Loop [] false) mctx mref cctx cref w (m, design) w')
    (hd : MachineDefines mctx mref cctx cref ``shift4Loop shift4Loop.machineData.shape) :
    ∃ (mm : MonoTy shShift4), SourceDenotesMono (envAt cref w) ``shift4Loop [] shShift4 mm ∧
      Tools.ShippingMachineAuto.MachineTrace ``shift4Loop shift4Loop.machineData m (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shShift4 mm bools bits) :=
  ⟨shift4Loop, shift4Loop_denotes hE, shift4Loop.machine_sound hr hd (shift4Loop.machine_closes mctx mref cctx cref)⟩

theorem counterEnableLoop_root_at {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} (hE : RootInEnv (envAt cref w) ``counterEnableLoop counterEnableLoopType counterEnableLoopValue d)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``counterEnableLoop [] false) mctx mref cctx cref w (m, design) w')
    (hd : MachineDefines mctx mref cctx cref ``counterEnableLoop counterEnableLoop.machineData.shape) :
    ∃ (mm : MonoTy shEnable), SourceDenotesMono (envAt cref w) ``counterEnableLoop [] shEnable mm ∧
      Tools.ShippingMachineAuto.MachineTrace ``counterEnableLoop counterEnableLoop.machineData m (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shEnable mm bools bits) :=
  ⟨counterEnableLoop, counterEnableLoop_denotes hE,
    counterEnableLoop.machine_sound hr hd (counterEnableLoop.machine_closes mctx mref cctx cref)⟩

theorem arbiterSignal_root_at {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal}
    (hE : RootInEnv (envAt cref w) ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue d)
    (hB : BoundaryRowsInEnv (envAt cref w))
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal [] false)
      mctx mref cctx cref w (m, design) w')
    (hd : MachineDefines mctx mref cctx cref ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
      Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape) :
    ∃ (mm : shArbiter.Ty), SourceDenotes (envAt cref w) ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal [] shArbiter mm ∧
      Tools.ShippingMachineAuto.MachineTrace ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
        Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData m (fun i : DomainConfig => i)
        (fun i bools bits => shArbiter.obs (dom := fun i : DomainConfig => i) mm i bools bits) :=
  ⟨_, arbiterSignal_denotes hE,
    Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_sound hr hd
      (Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_closes mctx mref cctx cref)⟩

/-! ## the printed module at the run's start environment

The conclusion still carries `seqCheck`, `simpleBody`, `declWidth` conditions INSIDE (`WiredConclusion`): it does not say the printed SV satisfies
the source meaning unconditionally. -/

theorem counterLoop_ships_at {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} (hE : RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, design) w')
    (hd : MachineDefines mctx mref cctx cref ``counterLoop counterLoop.machineData.shape) :
    ∃ (mm : MonoTy shCounter), SourceDenotesMono (envAt cref w) ``counterLoop [] shCounter mm ∧
      WiredConclusion ``counterLoop counterLoop.machineData (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shCounter mm bools bits) b :=
  ⟨counterLoop, counterLoop_denotes hE, counterLoop.machine_ships_wired hr hd (counterLoop.machine_closes mctx mref cctx cref)⟩

theorem shift4Loop_ships_at {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} (hE : RootInEnv (envAt cref w) ``shift4Loop shift4LoopType shift4LoopValue d)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``shift4Loop) mctx mref cctx cref w (b, design) w')
    (hd : MachineDefines mctx mref cctx cref ``shift4Loop shift4Loop.machineData.shape) :
    ∃ (mm : MonoTy shShift4), SourceDenotesMono (envAt cref w) ``shift4Loop [] shShift4 mm ∧
      WiredConclusion ``shift4Loop shift4Loop.machineData (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shShift4 mm bools bits) b :=
  ⟨shift4Loop, shift4Loop_denotes hE, shift4Loop.machine_ships_wired hr hd (shift4Loop.machine_closes mctx mref cctx cref)⟩

theorem counterEnableLoop_ships_at {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} (hE : RootInEnv (envAt cref w) ``counterEnableLoop counterEnableLoopType counterEnableLoopValue d)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterEnableLoop) mctx mref cctx cref w (b, design) w')
    (hd : MachineDefines mctx mref cctx cref ``counterEnableLoop counterEnableLoop.machineData.shape) :
    ∃ (mm : MonoTy shEnable), SourceDenotesMono (envAt cref w) ``counterEnableLoop [] shEnable mm ∧
      WiredConclusion ``counterEnableLoop counterEnableLoop.machineData (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shEnable mm bools bits) b :=
  ⟨counterEnableLoop, counterEnableLoop_denotes hE,
    counterEnableLoop.machine_ships_wired hr hd (counterEnableLoop.machine_closes mctx mref cctx cref)⟩

theorem arbiterSignal_ships_at {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal}
    (hE : RootInEnv (envAt cref w) ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue d)
    (hB : BoundaryRowsInEnv (envAt cref w))
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal) mctx mref cctx cref w
      (b, design) w')
    (hd : MachineDefines mctx mref cctx cref ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
      Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape) :
    ∃ (mm : shArbiter.Ty), SourceDenotes (envAt cref w) ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal [] shArbiter mm ∧
      WiredConclusion ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData
        (fun i : DomainConfig => i) (fun i bools bits => shArbiter.obs (dom := fun i : DomainConfig => i) mm i bools bits) b :=
  ⟨_, arbiterSignal_denotes hE,
    Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_ships_wired hr hd
      (Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_closes mctx mref cctx cref)⟩

end Tools.ShippingFGCircuitRoots
