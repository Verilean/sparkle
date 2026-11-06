import Tools.ShippingFGCircuitBridge
set_option autoImplicit false
-- FG circuit pilot S1d, unit 5: the roots with every premise that the tree supplies supplied. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # Applications: what is left after S1d

For each root the theorem `X_final` has as hypotheses ONLY:
* the compile succeeded: `hw : EntryWitness …` and `hr : RunsTo (synthesizeCombinational X) … (b, D') w'` (the "if compile succeeded" antecedent; it is the premise of the theorem, not something to prove for every input);
* `hA6` = the row `h_A_P06` of `FGLedgerPremisesStmtG` at the table `genGP … (canonGD lvl) (envAt cref w)`;
* `hRead : RootReader` (reader ↔ model agreement of the root: environment/reader fact, FG rows DG-DATAOF / DG-COVER / DG-ENV; checked in `MetaM` by `FGCircuitPilotCheck3`);
* `hE : RootInEnv (envAt cref w) …` (content of the environment entry; reduces to `QuoteFact` + the run-local `EnvSnapshot`, `Supply2.hE_of_run`; C.EN-4 / ENV cache) and, for the arbiter, `hB`;
* `hsrc` (the package's `src` is the declaration's observation: D.D-3 for this root, not proved);
* `htr : DesignTransport` (core design → printed design, `DCEntryT` lemmas not lifted).

Supplied inside the proof: `hd` (from `hA6`), `hc` (`X.machine_closes`), `hP` (`genGP` returns a package: `Cover`), `p.decl`, `p.d`, `p.kD` (`Cover`), the decidable leaf facts, `TopShips` at the core design (`Bridge`),
`∃ raw, Post` (from `hr`), the shape match and `SourceDenotes` (`RootsAt`, `Artifact`). `Post` is instantiated to `PostRun` (the post-processing relation tied to THIS core run), the table to `genGP … (canonGD lvl)`. -/
namespace Tools.ShippingFGCircuitApply
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitSupply2 Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMachineEntry (MachineDefines MachineCloses)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingChildInvA (AdmCtx)

theorem counterLoop_leafFacts : LeafFacts counterLoop.machineData := by unfold LeafFacts; decide
theorem counterLoop_kD : Tools.ShippingGen5Sem.kDOf counterLoop.machineData = 0 := by decide
theorem counterLoop_wf : Tools.ShippingGen5Sem.GenWF counterLoop.machineData = true := by decide

theorem counterLoop_final {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    {d : DefinitionVal}
    (hw : EntryWitness ReflectsAll L ``counterLoop [] mctx cctx w w' b D')
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w')
    (hA6 : ∀ c, TgtRun (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        ``counterLoop c → ∀ q : Pkg ι (fun _ => defaultDomain),
      genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w) c = some q →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx L.O.quiet mctx' cctx' → MachineDefines mctx' mref cctx' cref c q.d.shape)
    (hRead : RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData)
    (hE : RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d)
    (hsrc : ∀ p : Pkg ι (fun _ => defaultDomain),
      genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w) ``counterLoop = some p →
      ∀ (i : ι) bools bits, p.src i bools bits = monoObs shCounter counterLoop bools bits)
    (htr : ∀ (p : Pkg ι (fun _ => defaultDomain)) raw D₀, DesignTransport p ``counterLoop b raw D₀ D') :
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p := by
  obtain ⟨p, hP, hdecl, hpd, hkp⟩ := genGP_root_canon (ι := ι) (dom := fun _ => defaultDomain) lvl (envAt cref w) hRead
    counterLoop_wf (by have := counterLoop_leafFacts.2.2.2.2.1; exact this)
  have hl : EndpointLink counterLoop.machineData 0 (fun _ bools bits => monoObs shCounter counterLoop bools bits) p :=
    ⟨hpd, by rw [hkp]; exact counterLoop_kD, hsrc p hP⟩
  have hd : MachineDefines mctx mref cctx cref ``counterLoop counterLoop.machineData.shape :=
    machineDefines_of_witness hw hA6 hP hl
  have hcl : MachineCloses mctx mref cctx cref ``counterLoop counterLoop.machineData.shape := counterLoop.machine_closes mctx mref cctx cref
  have hTop := hTop_of_leaf L p hpd hkp counterLoop_leafFacts hw.1 (by rw [hdecl, hpd]; exact hd) (by rw [hdecl, hpd]; exact hcl)
    (fun raw D₀ => by rw [hdecl]; exact htr p raw D₀)
  rw [hdecl] at hTop
  have hpost : ∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw := by
    obtain ⟨raw, D₀, w1, hc, hpe⟩ := Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry hr
    exact ⟨raw, D₀, w1, hc, hpe⟩
  obtain ⟨mm, hart, -⟩ := counterLoop_artifact_at (Post := PostRun mctx mref cctx cref w ``counterLoop D') (P := genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
    hE hr hd hP hdecl hl (fun raw hraw => (hTop raw hraw).imp fun _ hn => hn.2)
  exact ⟨hpost, mm, p, hart⟩

theorem shift4Loop_leafFacts : LeafFacts shift4Loop.machineData := by unfold LeafFacts; decide
theorem shift4Loop_kD : Tools.ShippingGen5Sem.kDOf shift4Loop.machineData = 1 := by decide
theorem shift4Loop_wf : Tools.ShippingGen5Sem.GenWF shift4Loop.machineData = true := by decide

theorem shift4Loop_final {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    {d : DefinitionVal}
    (hw : EntryWitness ReflectsAll L ``shift4Loop [] mctx cctx w w' b D')
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``shift4Loop) mctx mref cctx cref w (b, D') w')
    (hA6 : ∀ c, TgtRun (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        ``shift4Loop c → ∀ q : Pkg ι (fun _ => defaultDomain),
      genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w) c = some q →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx L.O.quiet mctx' cctx' → MachineDefines mctx' mref cctx' cref c q.d.shape)
    (hRead : RootReader lvl (envAt cref w) ``shift4Loop shift4Loop.machineData)
    (hE : RootInEnv (envAt cref w) ``shift4Loop shift4LoopType shift4LoopValue d)
    (hsrc : ∀ p : Pkg ι (fun _ => defaultDomain),
      genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w) ``shift4Loop = some p →
      ∀ (i : ι) bools bits, p.src i bools bits = monoObs shShift4 shift4Loop bools bits)
    (htr : ∀ (p : Pkg ι (fun _ => defaultDomain)) raw D₀, DesignTransport p ``shift4Loop b raw D₀ D') :
    (∃ raw, PostRun mctx mref cctx cref w ``shift4Loop D' b raw) ∧
    ∃ (mm : MonoTy shShift4) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``shift4Loop D') ``shift4Loop shShift4 mm b D' p := by
  obtain ⟨p, hP, hdecl, hpd, hkp⟩ := genGP_root_canon (ι := ι) (dom := fun _ => defaultDomain) lvl (envAt cref w) hRead
    shift4Loop_wf (by have := shift4Loop_leafFacts.2.2.2.2.1; exact this)
  have hl : EndpointLink shift4Loop.machineData 1 (fun _ bools bits => monoObs shShift4 shift4Loop bools bits) p :=
    ⟨hpd, by rw [hkp]; exact shift4Loop_kD, hsrc p hP⟩
  have hd : MachineDefines mctx mref cctx cref ``shift4Loop shift4Loop.machineData.shape :=
    machineDefines_of_witness hw hA6 hP hl
  have hcl : MachineCloses mctx mref cctx cref ``shift4Loop shift4Loop.machineData.shape := shift4Loop.machine_closes mctx mref cctx cref
  have hTop := hTop_of_leaf L p hpd hkp shift4Loop_leafFacts hw.1 (by rw [hdecl, hpd]; exact hd) (by rw [hdecl, hpd]; exact hcl)
    (fun raw D₀ => by rw [hdecl]; exact htr p raw D₀)
  rw [hdecl] at hTop
  have hpost : ∃ raw, PostRun mctx mref cctx cref w ``shift4Loop D' b raw := by
    obtain ⟨raw, D₀, w1, hc, hpe⟩ := Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry hr
    exact ⟨raw, D₀, w1, hc, hpe⟩
  obtain ⟨mm, hart, -⟩ := shift4Loop_artifact_at (Post := PostRun mctx mref cctx cref w ``shift4Loop D') (P := genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
    hE hr hd hP hdecl hl (fun raw hraw => (hTop raw hraw).imp fun _ hn => hn.2)
  exact ⟨hpost, mm, p, hart⟩

theorem counterEnableLoop_leafFacts : LeafFacts counterEnableLoop.machineData := by unfold LeafFacts; decide
theorem counterEnableLoop_kD : Tools.ShippingGen5Sem.kDOf counterEnableLoop.machineData = 1 := by decide
theorem counterEnableLoop_wf : Tools.ShippingGen5Sem.GenWF counterEnableLoop.machineData = true := by decide

theorem counterEnableLoop_final {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    {d : DefinitionVal}
    (hw : EntryWitness ReflectsAll L ``counterEnableLoop [] mctx cctx w w' b D')
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterEnableLoop) mctx mref cctx cref w (b, D') w')
    (hA6 : ∀ c, TgtRun (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        ``counterEnableLoop c → ∀ q : Pkg ι (fun _ => defaultDomain),
      genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w) c = some q →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx L.O.quiet mctx' cctx' → MachineDefines mctx' mref cctx' cref c q.d.shape)
    (hRead : RootReader lvl (envAt cref w) ``counterEnableLoop counterEnableLoop.machineData)
    (hE : RootInEnv (envAt cref w) ``counterEnableLoop counterEnableLoopType counterEnableLoopValue d)
    (hsrc : ∀ p : Pkg ι (fun _ => defaultDomain),
      genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w) ``counterEnableLoop = some p →
      ∀ (i : ι) bools bits, p.src i bools bits = monoObs shEnable counterEnableLoop bools bits)
    (htr : ∀ (p : Pkg ι (fun _ => defaultDomain)) raw D₀, DesignTransport p ``counterEnableLoop b raw D₀ D') :
    (∃ raw, PostRun mctx mref cctx cref w ``counterEnableLoop D' b raw) ∧
    ∃ (mm : MonoTy shEnable) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``counterEnableLoop D') ``counterEnableLoop shEnable mm b D' p := by
  obtain ⟨p, hP, hdecl, hpd, hkp⟩ := genGP_root_canon (ι := ι) (dom := fun _ => defaultDomain) lvl (envAt cref w) hRead
    counterEnableLoop_wf (by have := counterEnableLoop_leafFacts.2.2.2.2.1; exact this)
  have hl : EndpointLink counterEnableLoop.machineData 1 (fun _ bools bits => monoObs shEnable counterEnableLoop bools bits) p :=
    ⟨hpd, by rw [hkp]; exact counterEnableLoop_kD, hsrc p hP⟩
  have hd : MachineDefines mctx mref cctx cref ``counterEnableLoop counterEnableLoop.machineData.shape :=
    machineDefines_of_witness hw hA6 hP hl
  have hcl : MachineCloses mctx mref cctx cref ``counterEnableLoop counterEnableLoop.machineData.shape := counterEnableLoop.machine_closes mctx mref cctx cref
  have hTop := hTop_of_leaf L p hpd hkp counterEnableLoop_leafFacts hw.1 (by rw [hdecl, hpd]; exact hd) (by rw [hdecl, hpd]; exact hcl)
    (fun raw D₀ => by rw [hdecl]; exact htr p raw D₀)
  rw [hdecl] at hTop
  have hpost : ∃ raw, PostRun mctx mref cctx cref w ``counterEnableLoop D' b raw := by
    obtain ⟨raw, D₀, w1, hc, hpe⟩ := Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry hr
    exact ⟨raw, D₀, w1, hc, hpe⟩
  obtain ⟨mm, hart, -⟩ := counterEnableLoop_artifact_at (Post := PostRun mctx mref cctx cref w ``counterEnableLoop D') (P := genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
    hE hr hd hP hdecl hl (fun raw hraw => (hTop raw hraw).imp fun _ hn => hn.2)
  exact ⟨hpost, mm, p, hart⟩

theorem arbiterSignal_leafFacts : LeafFacts Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData := by unfold LeafFacts; decide
theorem arbiterSignal_kD : Tools.ShippingGen5Sem.kDOf Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData = shArbiter.args.length + 1 := by decide
theorem arbiterSignal_wf : Tools.ShippingGen5Sem.GenWF Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData = true := by decide

theorem arbiterSignal_final {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    {d : DefinitionVal}
    (hw : EntryWitness ReflectsAll L ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal [] mctx cctx w w' b D')
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal) mctx mref cctx cref w (b, D') w')
    (hA6 : ∀ c, TgtRun (genGP (ι := DomainConfig) (dom := fun i => i) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal c → ∀ q : Pkg DomainConfig (fun i => i),
      genGP (ι := DomainConfig) (dom := fun i => i) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w) c = some q →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx L.O.quiet mctx' cctx' → MachineDefines mctx' mref cctx' cref c q.d.shape)
    (hRead : RootReader lvl (envAt cref w) ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData)
    (hE : RootInEnv (envAt cref w) ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue d)
    (hB : BoundaryRowsInEnv (envAt cref w))
    (hsrc : ∀ p : Pkg DomainConfig (fun i => i),
      genGP (ι := DomainConfig) (dom := fun i => i) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w)
        ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal = some p →
      ∀ (i : DomainConfig) bools bits, p.src i bools bits = shArbiter.obs (dom := fun i : DomainConfig => i)
        (fun D => @Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D) i bools bits)
    (htr : ∀ (p : Pkg DomainConfig (fun i => i)) raw D₀, DesignTransport p ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal b raw D₀ D') :
    (∃ raw, PostRun mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D' b raw) ∧
    ∃ (mm : shArbiter.Ty) (p : Pkg DomainConfig (fun i => i)),
      RootArtifact (envAt cref w)
        (genGP (ι := DomainConfig) (dom := fun i => i) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D') ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal shArbiter mm b D' p := by
  obtain ⟨p, hP, hdecl, hpd, hkp⟩ := genGP_root_canon (ι := DomainConfig) (dom := fun i => i) lvl (envAt cref w) hRead
    arbiterSignal_wf (by have := arbiterSignal_leafFacts.2.2.2.2.1; exact this)
  have hl : EndpointLink Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData (shArbiter.args.length + 1)
      (fun i bools bits => shArbiter.obs (dom := fun i : DomainConfig => i) (fun D => @Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D) i bools bits) p :=
    ⟨hpd, by rw [hkp]; exact arbiterSignal_kD, hsrc p hP⟩
  have hd : MachineDefines mctx mref cctx cref ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape :=
    machineDefines_of_witness hw hA6 hP hl
  have hcl : MachineCloses mctx mref cctx cref ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape :=
    Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_closes mctx mref cctx cref
  have hTop := hTop_of_leaf L p hpd hkp arbiterSignal_leafFacts hw.1 (by rw [hdecl, hpd]; exact hd) (by rw [hdecl, hpd]; exact hcl)
    (fun raw D₀ => by rw [hdecl]; exact htr p raw D₀)
  rw [hdecl] at hTop
  have hpost : ∃ raw, PostRun mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D' b raw := by
    obtain ⟨raw, D₀, w1, hc, hpe⟩ := Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry hr
    exact ⟨raw, D₀, w1, hc, hpe⟩
  obtain ⟨mm, hart, -⟩ := arbiterSignal_artifact_at (Post := PostRun mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D')
    (P := genGP (ι := DomainConfig) (dom := fun i => i) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
    hE hB hr hd hP hdecl hl (fun raw hraw => (hTop raw hraw).imp fun _ hn => hn.2)
  exact ⟨hpost, mm, p, hart⟩

end Tools.ShippingFGCircuitApply

#print axioms Tools.ShippingFGCircuitApply.counterLoop_final
#print axioms Tools.ShippingFGCircuitApply.shift4Loop_final
#print axioms Tools.ShippingFGCircuitApply.counterEnableLoop_final
#print axioms Tools.ShippingFGCircuitApply.arbiterSignal_final
