import Tools.ShippingFGCircuitFinal4
import Tools.ShippingGen5EnvFrame3
set_option autoImplicit false
-- FG circuit pilot S1h, unit 1: `GetEnvFrame` from `ReadWorld cref` (the CellPrem component), and `hquiet` replaced by the run-local `EnvFrame (coreHead X)`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # S1h-1: connecting `hquiet` / `GetEnvFrame` to `CellPrem` (C.EN-4)

* `getEnvFrame_of_readWorld`: `GetEnvFrame` is NOT a separate premise: it follows from `ReadWorld cref` (a component of `CellPrem`; `envFrameEnd_getEnv` of `ShippingGen5EnvFrame`).
* `hquiet : ∀ u, L.O.quiet u → ReadsAt e cref u` quantifies over the opaque `L.O.quiet`; nothing in `CellPrem` mentions it (it would need `QuietStrength L L' e` for a constructed `L'`).
  What the proof actually uses is `ReadsAt e cref w1` at ONE world, the world after `coreHead`.  That follows from `ReadsAt e cref w` (free at the start world, `readsAt_self`) and `EnvFrame (coreHead X)`, a statement about one MetaM action.
  So `hquiet` is replaced by `hhead : EnvFrame (coreHead X)`.  `hhead` is not derived: `coreHead` runs `IO.getEnv`/optional file IO (the unserved class-D `ioEnv` row, `DRow`), and the `ST.Ref.get` of `sparkleSynthDepth`/`sparkleFvarValueMap`
  (served by `CellOK`); the IO part needs a law that IO actions do not change the `cref` cell. -/
namespace Tools.ShippingFGCircuitS1hFrame
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitSupply2 Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitApply Tools.ShippingFGCircuitTransport Tools.ShippingFGCircuitSrc Tools.ShippingFGCircuitFinal Tools.ShippingFGCircuitLinked Tools.ShippingFGCircuitFinal4
open Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt coreHead core_chain)
open Tools.ShippingStRefCorrespondence (ReadWorld)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- the `endW` form of an environment frame gives the `RunsTo` form -/
theorem envFrame_of_envFrameEnd {α : Type} {x : MetaM α}
    (hx : Tools.ShippingGen5EnvFrame.EnvFrameEnd x mctx mref cctx cref) :
    Tools.ShippingEnvSnapshot.EnvFrame x mctx mref cctx cref := by
  intro w a w' h
  rw [← Tools.ShippingChildInv.endW_of_runs h]
  exact hx w

/-- **`GetEnvFrame` from `ReadWorld cref`** (the `hc` component of `CellPrem`): the premise `GetEnvFrame` of S1g is not separate. -/
theorem getEnvFrame_of_readWorld (hc : ReadWorld cref) :
    Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref :=
  envFrame_of_envFrameEnd (Tools.ShippingGen5EnvFrame.envFrameEnd_getEnv hc)

/-- `GetEnvFrame` from a whole `CellPrem` -/
theorem getEnvFrame_of_cellPrem {Fresh : (σ : Type) → IO.Ref σ → Prop}
    (h : Tools.ShippingGen5EnvFrame3.CellPrem Fresh mref cref) :
    Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref :=
  getEnvFrame_of_readWorld h.2.2.2.2.2.2.2.2.1

/-- `hquiet` is the `→` direction of `QuietStrength L L' e` for the strengthened laws `L'` (so it is a premise about a constructed `L'`, not about `L`) -/
theorem hquiet_of_strength {L L' : Laws mref cref} {e : Environment}
    (hq : Tools.ShippingGen5EnvQ.QuietStrength L L' e) : ∀ u, L'.O.quiet u → Tools.ShippingGen5Env.ReadsAt e cref u :=
  fun u hu => ((hq u).1 hu).2

/-- the world after `coreHead` carries `ReadsAt (envAt cref w)`, from `EnvFrame (coreHead X)` alone (no `hquiet`) -/
theorem readsAt_after_head {X : Name} (hhead : Tools.ShippingEnvSnapshot.EnvFrame (coreHead X) mctx mref cctx cref)
    {w w1 : Void IO.RealWorld} {s : Tools.ShippingEntryReadsLinked.CoreSaved}
    (hh : RunsTo (coreHead X) mctx mref cctx cref w s w1) :
    Tools.ShippingGen5Env.ReadsAt (envAt cref w) cref w1 :=
  Tools.ShippingGen5Env.ReadsAt.of_frame hhead hh (Tools.ShippingGen5Env.readsAt_self cref w)

/-- `machineDefinesLinked_of_env` with `hquiet` replaced by `hhead` (the start environment is the world's own) -/
theorem machineDefinesLinked_of_head {X : Name} {shape : MachineShape} {ci₀ : ConstantInfo}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hhead : Tools.ShippingEnvSnapshot.EnvFrame (coreHead X) mctx mref cctx cref)
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    (hc : (envAt cref w).find? X = some ci₀)
    (hg1 : certifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate (envAt cref w)) (userInliner (envAt cref w)) (structEnv (envAt cref w))) = none)
    (hg2 : mixedCertifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate (envAt cref w)) (userInliner (envAt cref w)) (structEnv (envAt cref w))) (instancePredicate (envAt cref w)) = none)
    (hsh : machineShape? false [] (entryConst true false [] ci₀ (instancePredicate (envAt cref w)) (userInliner (envAt cref w)) (structEnv (envAt cref w))) (structEnv (envAt cref w)) = some shape) :
    MachineDefinesLinked mctx mref cctx cref X shape w M D w' := by
  intro _ s w1 w2 w3 w4 envR ci h0 h1 h2 _
  have r1 := readsAt_after_head hhead h0
  have r2 : Tools.ShippingGen5Env.ReadsAt (envAt cref w) cref w2 :=
    Tools.ShippingGen5Env.ReadsAt.of_frame (Tools.ShippingEnvSnapshot.envFrame_getConstInfo X hg) h1 r1
  have r3 : Tools.ShippingGen5Env.ReadsAt (envAt cref w) cref w3 := Tools.ShippingGen5Env.ReadsAt.of_frame hg h2 r2
  have hci : ci = ci₀ := Option.some.inj ((Tools.ShippingGen5Env.ci_of_readsAt h1 r1).symm.trans hc)
  obtain ⟨-, hi, hu, hs⟩ := Tools.ShippingGen5Env.envR_of_readsAt h2 r2
  subst hci
  rw [hi, hu, hs]
  refine ⟨hg1, hg2, ?_⟩
  intro envR' w8 h3
  obtain ⟨-, -, -, hs'⟩ := Tools.ShippingGen5Env.envR_of_readsAt h3 r3
  rw [hs']
  exact hsh

/-- the root of the run is a constant of the start environment, from `hhead` -/
theorem root_find_of_head {X : Name} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hhead : Tools.ShippingEnvSnapshot.EnvFrame (coreHead X) mctx mref cctx cref)
    (hc : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (M, D) w') :
    ∃ ci : ConstantInfo, (envAt cref w).find? X = some ci := by
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hget, -, -, -⟩ := core_chain hc
  exact ⟨ci, Tools.ShippingGen5Env.ci_of_readsAt hget (readsAt_after_head hhead hh)⟩

/-- `machineDefinesLinked_of_reader` with `hhead` for `hquiet` -/
theorem machineDefinesLinked_of_reader_head {lvl : Lean.Expr → Nat} {X : Name} {ty val : Lean.Expr}
    {dd : Tools.ShippingMachineAuto.MachineData} {d : DefinitionVal}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hhead : Tools.ShippingEnvSnapshot.EnvFrame (coreHead X) mctx mref cctx cref)
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    (hE : RootInEnv (envAt cref w) X ty val d) (hRead : RootReader lvl (envAt cref w) X dd)
    (hgates : EntryGates (envAt cref w) X) :
    MachineDefinesLinked mctx mref cctx cref X dd.shape w M D w' := by
  obtain ⟨hf, -, -, -⟩ := hE
  obtain ⟨E, hent, hsh, -⟩ := hRead
  have hgE := hgates E hent
  unfold Tools.ShippingGen5Acc.entry₀ at hent
  rw [hf] at hent
  simp only [Option.map_some, Option.some.injEq] at hent
  subst hent
  exact machineDefinesLinked_of_head hhead hg hf hgE.1 hgE.2 hsh

/-- **`counterLoop_final6`**: `counterLoop_final4` with `hquiet` and `GetEnvFrame` replaced by `hhead : EnvFrame (coreHead ``counterLoop)` and `hcell : ReadWorld cref` (a `CellPrem` component).  Laws `L`/`hstart` are still arguments of the endpoint theorem. -/
theorem counterLoop_final6 {ι : Type} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    {d : DefinitionVal}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w')
    (hhead : Tools.ShippingEnvSnapshot.EnvFrame (coreHead ``counterLoop) mctx mref cctx cref)
    (hcell : ReadWorld cref)
    (hgates : EntryGates (envAt cref w) ``counterLoop)
    (hRead : RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData)
    (hE : RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d) :
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p :=
  counterLoop_final4D L lvl hstart hr
    (fun _ _ _ => machineDefinesLinked_of_reader_head (lvl := lvl) hhead (getEnvFrame_of_readWorld hcell) hE hRead hgates) hRead hE

end Tools.ShippingFGCircuitS1hFrame

#print axioms Tools.ShippingFGCircuitS1hFrame.getEnvFrame_of_cellPrem
#print axioms Tools.ShippingFGCircuitS1hFrame.machineDefinesLinked_of_head
#print axioms Tools.ShippingFGCircuitS1hFrame.root_find_of_head
#print axioms Tools.ShippingFGCircuitS1hFrame.counterLoop_final6
