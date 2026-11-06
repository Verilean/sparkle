import Tools.ShippingFGCircuitS1qEndpoint
import Tools.ShippingFGCircuitS1nRoots
set_option autoImplicit false
-- FG circuit pilot S1q, unit 3: `HeadAtOff` for the profile-free head from `CellPrem` ALONE, and the four leaf roots' finals on it.  No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.

/-! # S1q-3: the profile-free head and the final theorems `X_final12`

`coreHeadOff X` has no `IO.getEnv` and no log action (compiler: `synthesizeCombinationalCoreOff`, docs §21).  Its `EnvFrame` follows from `CellPrem` by the same `ef_step` decomposition as S1i, WITHOUT `HeadIO` and WITHOUT `GetEnvProfileAt`:
`envFrame_coreHeadOff`, `headAtOff_of_cellPrem`.
`X_final10Off` / `X_final12` are the S1i `X_final10` and S1l/S1n `X_final11` on `synthesizeCombinationalOff` (premise diff in docs §21.4):
* `hr` is a run of `synthesizeCombinationalOff`; the conclusion's post is `PostRunOff`.
* `hhead : HeadAt` (or `GetEnvProfileAt`, or `HeadIO`) is gone; `hcell : ReadWorld cref` becomes `hcell : CellPrem MkRefd mref cref` (its `ReadWorld cref` component is the one `X_final11` took).
Everything else (`Laws`, `Start`, `lvl`, `env₀`, `hlvl`, `RootExtern`, `RootEnvFacts`, `ReadsAt`, the arbiter's `BoundaryRowsInEnv`/`ContainsAt`) is unchanged and stays a named hypothesis.
NOT proved here: that the run of `synthesizeEntry` takes its `else` branch (the process environment has no `SPARKLE_PROFILE`); that is a statement about the command-level setting, outside the entry. -/
namespace Tools.ShippingFGCircuitS1qHead
open Lean Tools.ShippingEntryReadsLinked Tools.ShippingEnvSnapshot Sparkle.Compiler.Elab
open Tools.ShippingGen5EnvFrame3 (CellPrem CellOK)
open Tools.ShippingChildInv (SideRef)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingStRefCorrespondence (ReadWorld)
open Tools.ShippingFGCircuitS1iHead
open Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qEndpoint
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 1000000 in
/-- **`hhead` for the profile-free head from `CellPrem` alone** (no `HeadIO`, no `GetEnvProfileAt`) -/
theorem envFrame_coreHeadOff (X : Name) (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref) :
    EnvFrame (coreHeadOff X) mctx mref cctx cref := by
  obtain ⟨hC, hS, hD, hSide, -, hm, -, -, hc, -⟩ := hcell
  unfold coreHeadOff
  repeat' ((try dsimp -zeta only); ef_step)

/-- the run-local form on the profile-free head: any `coreHeadOff` run from the start world `w` keeps the Core environment -/
def HeadAtOff (X : Name) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) : Prop :=
  ∀ (s : CoreSaved) (w1 : Void IO.RealWorld), RunsTo (coreHeadOff X) mctx mref cctx cref w s w1 → envAt cref w1 = envAt cref w

theorem headAtOff_of_frame {X : Name} {w : Void IO.RealWorld} (h : EnvFrame (coreHeadOff X) mctx mref cctx cref) :
    HeadAtOff X mctx mref cctx cref w := fun s w1 hh => h w s w1 hh

/-- **`HeadAtOff` from `CellPrem` alone** -/
theorem headAtOff_of_cellPrem {w : Void IO.RealWorld} (X : Name) (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref) :
    HeadAtOff X mctx mref cctx cref w :=
  headAtOff_of_frame (envFrame_coreHeadOff X hcell)

theorem readsAt_after_headAtOff {X : Name} {w w1 : Void IO.RealWorld} {s : CoreSaved}
    (hhead : HeadAtOff X mctx mref cctx cref w) (hh : RunsTo (coreHeadOff X) mctx mref cctx cref w s w1) :
    Tools.ShippingGen5Env.ReadsAt (envAt cref w) cref w1 :=
  Tools.ShippingGen5Env.ReadsAt.of_envEq (hhead s w1 hh) (Tools.ShippingGen5Env.readsAt_self cref w)

/-- the root is a constant of the start environment, from `HeadAtOff` -/
theorem root_find_of_headAtOff {X : Name} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hhead : HeadAtOff X mctx mref cctx cref w)
    (hc : RunsTo (synthesizeCombinationalCoreOff X) mctx mref cctx cref w (M, D) w') :
    ∃ ci : ConstantInfo, (envAt cref w).find? X = some ci := by
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hget, -, -, -⟩ := core_chainOff hc
  exact ⟨ci, Tools.ShippingGen5Env.ci_of_readsAt hget (readsAt_after_headAtOff hhead hh)⟩

/-- `machineDefinesLinked_of_head` with `HeadAt` -/
theorem machineDefinesLinked_of_headAtOff {X : Name} {shape : MachineShape} {ci₀ : ConstantInfo}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hhead : HeadAtOff X mctx mref cctx cref w)
    (hg : GetEnvFrame mctx mref cctx cref)
    (hc : (envAt cref w).find? X = some ci₀)
    (hg1 : certifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate (envAt cref w)) (userInliner (envAt cref w)) (structEnv (envAt cref w))) = none)
    (hg2 : mixedCertifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate (envAt cref w)) (userInliner (envAt cref w)) (structEnv (envAt cref w))) (instancePredicate (envAt cref w)) = none)
    (hsh : machineShape? false [] (entryConst true false [] ci₀ (instancePredicate (envAt cref w)) (userInliner (envAt cref w)) (structEnv (envAt cref w))) (structEnv (envAt cref w)) = some shape) :
    MachineDefinesLinkedOff mctx mref cctx cref X shape w M D w' := by
  intro _ s w1 w2 w3 w4 envR ci h0 h1 h2 _
  have r1 := readsAt_after_headAtOff hhead h0
  have r2 : Tools.ShippingGen5Env.ReadsAt (envAt cref w) cref w2 :=
    Tools.ShippingGen5Env.ReadsAt.of_frame (envFrame_getConstInfo X hg) h1 r1
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


section Finals
open Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitSupply2 Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitApply Tools.ShippingFGCircuitTransport Tools.ShippingFGCircuitSrc Tools.ShippingFGCircuitFinal Tools.ShippingFGCircuitFinal4
open Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitRoots4
open Tools.ShippingFGCircuitS1hGates Tools.ShippingFGCircuitS1hQuote Tools.ShippingFGCircuitS1iEnv Tools.ShippingFGCircuitS1iRoots
open Tools.ShippingFGCircuitS1lReader Tools.ShippingFGCircuitS1nRoots
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingMachineAuto (MachineData)

/-- `machineDefinesLinked_of_reader_head` with `HeadAt` -/
theorem machineDefinesLinked_of_reader_headAtOff {lvl : Lean.Expr → Nat} {X : Name} {ty val : Lean.Expr}
    {dd : Tools.ShippingMachineAuto.MachineData} {d : DefinitionVal}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hhead : HeadAtOff X mctx mref cctx cref w) (hg : GetEnvFrame mctx mref cctx cref)
    (hE : RootInEnv (envAt cref w) X ty val d) (hRead : RootReader lvl (envAt cref w) X dd)
    (hgates : EntryGates (envAt cref w) X) :
    MachineDefinesLinkedOff mctx mref cctx cref X dd.shape w M D w' := by
  obtain ⟨hf, -, -, -⟩ := hE
  obtain ⟨E, hent, hsh, -⟩ := hRead
  have hgE := hgates E hent
  unfold Tools.ShippingGen5Acc.entry₀ at hent
  rw [hf] at hent
  simp only [Option.map_some, Option.some.injEq] at hent
  subst hent
  exact machineDefinesLinked_of_headAtOff hhead hg hf hgE.1 hgE.2 hsh


/-- **`counterLoop_final10Off`**: `counterLoop_final9` with the checked-environment premises bundled (`CheckedStart`) -/
theorem counterLoop_final10Off {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalOff ``counterLoop) mctx mref cctx cref w (b, D') w')
    (hhead : HeadAtOff ``counterLoop mctx mref cctx cref w) (hcell : ReadWorld cref)
    (hchk : CheckedStart lvl env₀ cref w ``counterLoop counterLoopType counterLoopValue counterLoop.machineData) :
    (∃ raw, PostRunOff mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRunOff mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p := by
  obtain ⟨raw, D₀, w1, hc, -⟩ := postEntryOff hr
  obtain ⟨hgates, ⟨d, hE⟩, hRead⟩ := startFacts_of_checked hchk (root_find_of_headAtOff hhead hc)
  exact counterLoop_final4DOff L lvl hstart hr
    (fun _ _ _ => machineDefinesLinked_of_reader_headAtOff hhead (Tools.ShippingFGCircuitS1hFrame.getEnvFrame_of_readWorld hcell) hE hRead hgates) hRead hE

theorem shift4Loop_final10Off {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalOff ``shift4Loop) mctx mref cctx cref w (b, D') w')
    (hhead : HeadAtOff ``shift4Loop mctx mref cctx cref w) (hcell : ReadWorld cref)
    (hchk : CheckedStart lvl env₀ cref w ``shift4Loop shift4LoopType shift4LoopValue shift4Loop.machineData) :
    (∃ raw, PostRunOff mctx mref cctx cref w ``shift4Loop D' b raw) ∧
    ∃ (mm : MonoTy shShift4) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRunOff mctx mref cctx cref w ``shift4Loop D') ``shift4Loop shShift4 mm b D' p := by
  obtain ⟨raw, D₀, w1, hc, -⟩ := postEntryOff hr
  obtain ⟨hgates, ⟨d, hE⟩, hRead⟩ := startFacts_of_checked hchk (root_find_of_headAtOff hhead hc)
  exact shift4Loop_final4DOff L lvl hstart hr
    (fun _ _ _ => machineDefinesLinked_of_reader_headAtOff hhead (Tools.ShippingFGCircuitS1hFrame.getEnvFrame_of_readWorld hcell) hE hRead hgates) hRead hE

theorem counterEnableLoop_final10Off {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalOff ``counterEnableLoop) mctx mref cctx cref w (b, D') w')
    (hhead : HeadAtOff ``counterEnableLoop mctx mref cctx cref w) (hcell : ReadWorld cref)
    (hchk : CheckedStart lvl env₀ cref w ``counterEnableLoop counterEnableLoopType counterEnableLoopValue counterEnableLoop.machineData) :
    (∃ raw, PostRunOff mctx mref cctx cref w ``counterEnableLoop D' b raw) ∧
    ∃ (mm : MonoTy shEnable) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRunOff mctx mref cctx cref w ``counterEnableLoop D') ``counterEnableLoop shEnable mm b D' p := by
  obtain ⟨raw, D₀, w1, hc, -⟩ := postEntryOff hr
  obtain ⟨hgates, ⟨d, hE⟩, hRead⟩ := startFacts_of_checked hchk (root_find_of_headAtOff hhead hc)
  exact counterEnableLoop_final4DOff L lvl hstart hr
    (fun _ _ _ => machineDefinesLinked_of_reader_headAtOff hhead (Tools.ShippingFGCircuitS1hFrame.getEnvFrame_of_readWorld hcell) hE hRead hgates) hRead hE

theorem arbiterSignal_final10Off {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalOff ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal) mctx mref cctx cref w (b, D') w')
    (hhead : HeadAtOff ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal mctx mref cctx cref w) (hcell : ReadWorld cref)
    (hchk : CheckedStart lvl env₀ cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData)
    (hB0 : BoundaryRowsInEnv env₀) (hcont : ContainsAt env₀ cref w boundaryNames) :
    (∃ raw, PostRunOff mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D' b raw) ∧
    ∃ (mm : shArbiter.Ty) (p : Pkg DomainConfig (fun i => i)),
      RootArtifact (envAt cref w)
        (genGP (ι := DomainConfig) (dom := fun i => i) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRunOff mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D') ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal shArbiter mm b D' p := by
  obtain ⟨raw, D₀, w1, hc, -⟩ := postEntryOff hr
  obtain ⟨hgates, ⟨d, hE⟩, hRead⟩ := startFacts_of_checked hchk (root_find_of_headAtOff hhead hc)
  exact arbiterSignal_final4DOff L lvl hstart hr
    (fun _ _ _ => machineDefinesLinked_of_reader_headAtOff hhead (Tools.ShippingFGCircuitS1hFrame.getEnvFrame_of_readWorld hcell) hE hRead hgates) hRead hE (boundaryRows_of_contains hB0 hcont)


/-- **`counterLoop_final12`**: `counterLoop_final10` with `hchk : CheckedStart` replaced by the finite facts and the link `ReadsAt env₀ cref w` -/
theorem counterLoop_final12 {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalOff ``counterLoop) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hlvl : lvl counterLoop.machineData.shape.body = 1000000) (hx : CounterLoopExtern) (hf : CounterLoopEnvFacts env₀)
    (hlink : ReadsAt env₀ cref w) :
    (∃ raw, PostRunOff mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRunOff mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p :=
  counterLoop_final10Off L lvl env₀ hstart hr (headAtOff_of_cellPrem _ hcell) hcell.2.2.2.2.2.2.2.2.1
    ⟨counterLoop_checkedEnv_of_finite lvl env₀ hlvl hx hf, hlink⟩

/-- **`shift4Loop_final12`**: `shift4Loop_final10` with `hchk : CheckedStart` replaced by the finite facts and the link `ReadsAt env₀ cref w` -/
theorem shift4Loop_final12 {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalOff ``shift4Loop) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hlvl : lvl shift4Loop.machineData.shape.body = 1000000) (hx : Shift4LoopExtern) (hf : Shift4LoopEnvFacts env₀)
    (hlink : ReadsAt env₀ cref w) :
    (∃ raw, PostRunOff mctx mref cctx cref w ``shift4Loop D' b raw) ∧
    ∃ (mm : MonoTy shShift4) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRunOff mctx mref cctx cref w ``shift4Loop D') ``shift4Loop shShift4 mm b D' p :=
  shift4Loop_final10Off L lvl env₀ hstart hr (headAtOff_of_cellPrem _ hcell) hcell.2.2.2.2.2.2.2.2.1 ⟨shift4Loop_checkedEnv_of_finite lvl env₀ hlvl hx hf, hlink⟩

/-! ## counterEnableLoop -/

/-- **`counterEnableLoop_final12`** -/
theorem counterEnableLoop_final12 {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalOff ``counterEnableLoop) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hlvl : lvl counterEnableLoop.machineData.shape.body = 1000000) (hx : CounterEnableLoopExtern) (hf : CounterEnableLoopEnvFacts env₀)
    (hlink : ReadsAt env₀ cref w) :
    (∃ raw, PostRunOff mctx mref cctx cref w ``counterEnableLoop D' b raw) ∧
    ∃ (mm : MonoTy shEnable) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRunOff mctx mref cctx cref w ``counterEnableLoop D') ``counterEnableLoop shEnable mm b D' p :=
  counterEnableLoop_final10Off L lvl env₀ hstart hr (headAtOff_of_cellPrem _ hcell) hcell.2.2.2.2.2.2.2.2.1 ⟨counterEnableLoop_checkedEnv_of_finite lvl env₀ hlvl hx hf, hlink⟩

/-! ## arbiterSignal (the inliner changes the value: the entry constant is the inlined declaration) -/

/-- **`arbiterSignal_final12`** (keeps `hB0`/`hcont`: the boundary rows are an existence statement `ReadsAt` does not carry) -/
theorem arbiterSignal_final12 {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalOff ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hlvl : lvl Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape.body = 1000000)
    (hx : ArbiterSignalExtern) (hf : ArbiterSignalEnvFacts env₀)
    (hlink : ReadsAt env₀ cref w)
    (hB0 : BoundaryRowsInEnv env₀) (hcont : ContainsAt env₀ cref w boundaryNames) :
    (∃ raw, PostRunOff mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D' b raw) ∧
    ∃ (mm : shArbiter.Ty) (p : Pkg DomainConfig (fun i => i)),
      RootArtifact (envAt cref w)
        (genGP (ι := DomainConfig) (dom := fun i => i) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRunOff mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D') ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal shArbiter mm b D' p :=
  arbiterSignal_final10Off L lvl env₀ hstart hr (headAtOff_of_cellPrem _ hcell) hcell.2.2.2.2.2.2.2.2.1 ⟨arbiterSignal_checkedEnv_of_finite lvl env₀ hlvl hx hf, hlink⟩ hB0 hcont


end Finals

end Tools.ShippingFGCircuitS1qHead
#print axioms Tools.ShippingFGCircuitS1qHead.envFrame_coreHeadOff
#print axioms Tools.ShippingFGCircuitS1qHead.headAtOff_of_cellPrem
#print axioms Tools.ShippingFGCircuitS1qHead.root_find_of_headAtOff
#print axioms Tools.ShippingFGCircuitS1qHead.machineDefinesLinked_of_headAtOff
#print axioms Tools.ShippingFGCircuitS1qHead.counterLoop_final10Off
#print axioms Tools.ShippingFGCircuitS1qHead.shift4Loop_final10Off
#print axioms Tools.ShippingFGCircuitS1qHead.counterEnableLoop_final10Off
#print axioms Tools.ShippingFGCircuitS1qHead.arbiterSignal_final10Off
#print axioms Tools.ShippingFGCircuitS1qHead.counterLoop_final12
#print axioms Tools.ShippingFGCircuitS1qHead.shift4Loop_final12
#print axioms Tools.ShippingFGCircuitS1qHead.counterEnableLoop_final12
#print axioms Tools.ShippingFGCircuitS1qHead.arbiterSignal_final12
