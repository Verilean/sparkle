import Tools.ShippingFGCircuitS1iEnv
import Tools.ShippingFGCircuitRoots4
set_option autoImplicit false
-- FG circuit pilot S1i, unit 3: the S1h final6-8 shape (run-local `HeadAt`, `CheckedStart`) for all four roots. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # S1i-3: lifting to shift4Loop, counterEnableLoop, arbiterSignal

`X_final4D` is `X_final4` (S1g, `Roots4.lean`) with the machine boundary `hdRun : ∀ raw D₀ w1, MachineDefinesLinked …` as a hypothesis (the proof is the S1g proof minus the two lines that built `hdRun` from `hquiet`/`GetEnvFrame`).
`X_final10` supplies it from the run-local `HeadAt` (S1i-1), `ReadWorld cref` (a `CellPrem` component) and the single premise `CheckedStart` (S1i-2): the same shape as `counterLoop_final9`/`counterLoop_final10`.
For the arbiter the boundary rows `hB : BoundaryRowsInEnv (envAt cref w)` are an **existence** statement about the start environment's lookups of three auxiliary constants; `ReadsAt` is one-way (start ⊆ `env₀`), so it cannot transfer them.
The extra named premise `ContainsAt env₀ cref w names` (the converse inclusion, for exactly those three names: DG-ENV C0 for the boundary constants) together with `BoundaryRowsInEnv env₀` (a statement about one environment, checked in `MetaM`) gives `hB`. -/
namespace Tools.ShippingFGCircuitS1iRoots
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitSupply2 Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitApply Tools.ShippingFGCircuitTransport Tools.ShippingFGCircuitSrc Tools.ShippingFGCircuitFinal Tools.ShippingFGCircuitLinked Tools.ShippingFGCircuitFinal4
open Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitRoots4
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMachineEntry (MachineCloses)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5Sem (kDOf)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingStRefCorrespondence (ReadWorld)
open Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingFGCircuitLinked2

theorem shift4Loop_final4D {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    {d : DefinitionVal}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``shift4Loop) mctx mref cctx cref w (b, D') w')
    (hdRun : ∀ raw D₀ w1, MachineDefinesLinked mctx mref cctx cref ``shift4Loop shift4Loop.machineData.shape w raw D₀ w1)
    (hRead : RootReader lvl (envAt cref w) ``shift4Loop shift4Loop.machineData)
    (hE : RootInEnv (envAt cref w) ``shift4Loop shift4LoopType shift4LoopValue d) :
    (∃ raw, PostRun mctx mref cctx cref w ``shift4Loop D' b raw) ∧
    ∃ (mm : MonoTy shShift4) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``shift4Loop D') ``shift4Loop shShift4 mm b D' p := by
  obtain ⟨p, hP, hdecl, hpd, hkp⟩ := genGP_root_canon (ι := ι) (dom := fun _ => defaultDomain) lvl (envAt cref w) hRead
    shift4Loop_wf (by have := shift4Loop_leafFacts.2.2.2.2.1; exact this)
  obtain ⟨p', hP', hsrc'⟩ := shift4Loop_hsrc (ι := ι) lvl (envAt cref w) hRead
  have hpp : p' = p := Option.some.inj (hP'.symm.trans hP)
  subst hpp
  have hl : EndpointLink shift4Loop.machineData 1 (fun _ bools bits => monoObs shShift4 shift4Loop bools bits) p' :=
    ⟨hpd, by rw [hkp]; exact shift4Loop_kD, hsrc'⟩
  have hcl : MachineCloses mctx mref cctx cref ``shift4Loop shift4Loop.machineData.shape := shift4Loop.machine_closes mctx mref cctx cref
  have hTop := hTop_of_leaf4 (b := b) (D' := D') L p' hpd hkp shift4Loop_leafFacts hstart
    (by rw [hdecl, hpd]; exact hdRun) (by rw [hdecl, hpd]; exact hcl)
  rw [hdecl] at hTop
  have hpost : ∃ raw, PostRun mctx mref cctx cref w ``shift4Loop D' b raw := by
    obtain ⟨raw, D₀, w1, hc, hpe⟩ := Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry hr
    exact ⟨raw, D₀, w1, hc, hpe⟩
  obtain ⟨mm, hart, -⟩ := shift4Loop_artifact_atC (Post := PostRun mctx mref cctx cref w ``shift4Loop D') (P := genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
    hE hr hdRun hP hdecl hl (fun raw hraw => (hTop raw hraw).imp fun _ hn => hn.2)
  exact ⟨hpost, mm, p', hart⟩

theorem counterEnableLoop_final4D {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    {d : DefinitionVal}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterEnableLoop) mctx mref cctx cref w (b, D') w')
    (hdRun : ∀ raw D₀ w1, MachineDefinesLinked mctx mref cctx cref ``counterEnableLoop counterEnableLoop.machineData.shape w raw D₀ w1)
    (hRead : RootReader lvl (envAt cref w) ``counterEnableLoop counterEnableLoop.machineData)
    (hE : RootInEnv (envAt cref w) ``counterEnableLoop counterEnableLoopType counterEnableLoopValue d) :
    (∃ raw, PostRun mctx mref cctx cref w ``counterEnableLoop D' b raw) ∧
    ∃ (mm : MonoTy shEnable) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``counterEnableLoop D') ``counterEnableLoop shEnable mm b D' p := by
  obtain ⟨p, hP, hdecl, hpd, hkp⟩ := genGP_root_canon (ι := ι) (dom := fun _ => defaultDomain) lvl (envAt cref w) hRead
    counterEnableLoop_wf (by have := counterEnableLoop_leafFacts.2.2.2.2.1; exact this)
  obtain ⟨p', hP', hsrc'⟩ := counterEnableLoop_hsrc (ι := ι) lvl (envAt cref w) hRead
  have hpp : p' = p := Option.some.inj (hP'.symm.trans hP)
  subst hpp
  have hl : EndpointLink counterEnableLoop.machineData 1 (fun _ bools bits => monoObs shEnable counterEnableLoop bools bits) p' :=
    ⟨hpd, by rw [hkp]; exact counterEnableLoop_kD, hsrc'⟩
  have hcl : MachineCloses mctx mref cctx cref ``counterEnableLoop counterEnableLoop.machineData.shape := counterEnableLoop.machine_closes mctx mref cctx cref
  have hTop := hTop_of_leaf4 (b := b) (D' := D') L p' hpd hkp counterEnableLoop_leafFacts hstart
    (by rw [hdecl, hpd]; exact hdRun) (by rw [hdecl, hpd]; exact hcl)
  rw [hdecl] at hTop
  have hpost : ∃ raw, PostRun mctx mref cctx cref w ``counterEnableLoop D' b raw := by
    obtain ⟨raw, D₀, w1, hc, hpe⟩ := Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry hr
    exact ⟨raw, D₀, w1, hc, hpe⟩
  obtain ⟨mm, hart, -⟩ := counterEnableLoop_artifact_atC (Post := PostRun mctx mref cctx cref w ``counterEnableLoop D') (P := genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
    hE hr hdRun hP hdecl hl (fun raw hraw => (hTop raw hraw).imp fun _ hn => hn.2)
  exact ⟨hpost, mm, p', hart⟩

theorem arbiterSignal_final4D {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    {d : DefinitionVal}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal) mctx mref cctx cref w (b, D') w')
    (hdRun : ∀ raw D₀ w1, MachineDefinesLinked mctx mref cctx cref ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape w raw D₀ w1)
    (hRead : RootReader lvl (envAt cref w) ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData)
    (hE : RootInEnv (envAt cref w) ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue d)
    (hB : BoundaryRowsInEnv (envAt cref w)) :
    (∃ raw, PostRun mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D' b raw) ∧
    ∃ (mm : shArbiter.Ty) (p : Pkg DomainConfig (fun i => i)),
      RootArtifact (envAt cref w)
        (genGP (ι := DomainConfig) (dom := fun i => i) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D') ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal shArbiter mm b D' p := by
  obtain ⟨p, hP, hdecl, hpd, hkp⟩ := genGP_root_canon (ι := DomainConfig) (dom := fun i => i) lvl (envAt cref w) hRead
    arbiterSignal_wf (by have := arbiterSignal_leafFacts.2.2.2.2.1; exact this)
  obtain ⟨p', hP', hsrc'⟩ := arbiterSignal_hsrc lvl (envAt cref w) hRead
  have hpp : p' = p := Option.some.inj (hP'.symm.trans hP)
  subst hpp
  have hl : EndpointLink Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData (shArbiter.args.length + 1)
      (fun i bools bits => shArbiter.obs (dom := fun i : DomainConfig => i) (fun D => @Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D) i bools bits) p' :=
    ⟨hpd, by rw [hkp]; exact arbiterSignal_kD, hsrc'⟩
  have hcl : MachineCloses mctx mref cctx cref ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape :=
    Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_closes mctx mref cctx cref
  have hTop := hTop_of_leaf4 (b := b) (D' := D') L p' hpd hkp arbiterSignal_leafFacts hstart
    (by rw [hdecl, hpd]; exact hdRun) (by rw [hdecl, hpd]; exact hcl)
  rw [hdecl] at hTop
  have hpost : ∃ raw, PostRun mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D' b raw := by
    obtain ⟨raw, D₀, w1, hc, hpe⟩ := Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry hr
    exact ⟨raw, D₀, w1, hc, hpe⟩
  obtain ⟨mm, hart, -⟩ := arbiterSignal_artifact_atC (Post := PostRun mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D')
    (P := genGP (ι := DomainConfig) (dom := fun i => i) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
    hE hB hr hdRun hP hdecl hl (fun raw hraw => (hTop raw hraw).imp fun _ hn => hn.2)
  exact ⟨hpost, mm, p', hart⟩

/-- the three auxiliary constants whose lookups `BoundaryRowsInEnv` states -/
def boundaryNames : List Name := [privAbbrev `stIdle, privAbbrev `stGrantA, privAbbrev `stGrantB]

/-- the converse inclusion of `ReadsAt` for the given names: what `env₀` finds, the start environment finds (the same constant) -/
def ContainsAt (env₀ : Environment) (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (ns : List Name) : Prop :=
  ∀ n ∈ ns, ∀ ci : ConstantInfo, env₀.find? n = some ci → (envAt cref w).find? n = some ci

theorem boundaryRows_of_contains {env₀ : Environment} {cref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    (hB : BoundaryRowsInEnv env₀) (hc : ContainsAt env₀ cref w boundaryNames) : BoundaryRowsInEnv (envAt cref w) := by
  intro nm k hk
  obtain ⟨d, hf, hl, ht, hv⟩ := hB nm k hk
  refine ⟨d, hc _ ?_ _ hf, hl, ht, hv⟩
  simp only [boundaryNames, List.mem_cons, List.not_mem_nil, or_false]
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hk
  rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

/-- **`counterLoop_final10`**: `counterLoop_final9` with the checked-environment premises bundled (`CheckedStart`) -/
theorem counterLoop_final10 {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w')
    (hhead : HeadAt ``counterLoop mctx mref cctx cref w) (hcell : ReadWorld cref)
    (hchk : CheckedStart lvl env₀ cref w ``counterLoop counterLoopType counterLoopValue counterLoop.machineData) :
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p := by
  obtain ⟨raw, D₀, w1, hc, -⟩ := Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry hr
  obtain ⟨hgates, ⟨d, hE⟩, hRead⟩ := startFacts_of_checked hchk (root_find_of_headAt hhead hc)
  exact counterLoop_final4D L lvl hstart hr
    (fun _ _ _ => machineDefinesLinked_of_reader_headAt hhead (Tools.ShippingFGCircuitS1hFrame.getEnvFrame_of_readWorld hcell) hE hRead hgates) hRead hE

theorem shift4Loop_final10 {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``shift4Loop) mctx mref cctx cref w (b, D') w')
    (hhead : HeadAt ``shift4Loop mctx mref cctx cref w) (hcell : ReadWorld cref)
    (hchk : CheckedStart lvl env₀ cref w ``shift4Loop shift4LoopType shift4LoopValue shift4Loop.machineData) :
    (∃ raw, PostRun mctx mref cctx cref w ``shift4Loop D' b raw) ∧
    ∃ (mm : MonoTy shShift4) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``shift4Loop D') ``shift4Loop shShift4 mm b D' p := by
  obtain ⟨raw, D₀, w1, hc, -⟩ := Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry hr
  obtain ⟨hgates, ⟨d, hE⟩, hRead⟩ := startFacts_of_checked hchk (root_find_of_headAt hhead hc)
  exact shift4Loop_final4D L lvl hstart hr
    (fun _ _ _ => machineDefinesLinked_of_reader_headAt hhead (Tools.ShippingFGCircuitS1hFrame.getEnvFrame_of_readWorld hcell) hE hRead hgates) hRead hE

theorem counterEnableLoop_final10 {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterEnableLoop) mctx mref cctx cref w (b, D') w')
    (hhead : HeadAt ``counterEnableLoop mctx mref cctx cref w) (hcell : ReadWorld cref)
    (hchk : CheckedStart lvl env₀ cref w ``counterEnableLoop counterEnableLoopType counterEnableLoopValue counterEnableLoop.machineData) :
    (∃ raw, PostRun mctx mref cctx cref w ``counterEnableLoop D' b raw) ∧
    ∃ (mm : MonoTy shEnable) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``counterEnableLoop D') ``counterEnableLoop shEnable mm b D' p := by
  obtain ⟨raw, D₀, w1, hc, -⟩ := Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry hr
  obtain ⟨hgates, ⟨d, hE⟩, hRead⟩ := startFacts_of_checked hchk (root_find_of_headAt hhead hc)
  exact counterEnableLoop_final4D L lvl hstart hr
    (fun _ _ _ => machineDefinesLinked_of_reader_headAt hhead (Tools.ShippingFGCircuitS1hFrame.getEnvFrame_of_readWorld hcell) hE hRead hgates) hRead hE

theorem arbiterSignal_final10 {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal) mctx mref cctx cref w (b, D') w')
    (hhead : HeadAt ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal mctx mref cctx cref w) (hcell : ReadWorld cref)
    (hchk : CheckedStart lvl env₀ cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData)
    (hB0 : BoundaryRowsInEnv env₀) (hcont : ContainsAt env₀ cref w boundaryNames) :
    (∃ raw, PostRun mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D' b raw) ∧
    ∃ (mm : shArbiter.Ty) (p : Pkg DomainConfig (fun i => i)),
      RootArtifact (envAt cref w)
        (genGP (ι := DomainConfig) (dom := fun i => i) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D') ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal shArbiter mm b D' p := by
  obtain ⟨raw, D₀, w1, hc, -⟩ := Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry hr
  obtain ⟨hgates, ⟨d, hE⟩, hRead⟩ := startFacts_of_checked hchk (root_find_of_headAt hhead hc)
  exact arbiterSignal_final4D L lvl hstart hr
    (fun _ _ _ => machineDefinesLinked_of_reader_headAt hhead (Tools.ShippingFGCircuitS1hFrame.getEnvFrame_of_readWorld hcell) hE hRead hgates) hRead hE (boundaryRows_of_contains hB0 hcont)

end Tools.ShippingFGCircuitS1iRoots

#print axioms Tools.ShippingFGCircuitS1iRoots.boundaryRows_of_contains
#print axioms Tools.ShippingFGCircuitS1iRoots.counterLoop_final10
#print axioms Tools.ShippingFGCircuitS1iRoots.shift4Loop_final10
#print axioms Tools.ShippingFGCircuitS1iRoots.counterEnableLoop_final10
#print axioms Tools.ShippingFGCircuitS1iRoots.arbiterSignal_final10
