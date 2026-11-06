import Tools.ShippingFGCircuitFinal3
import Tools.ShippingFGCircuitLinked2
set_option autoImplicit false
-- FG circuit pilot S1g, unit 3: `counterLoop_final4D`: Start + hr only, and the run-local boundary `MachineDefinesLinked` consumed all the way. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # `counterLoop_final4D` and `counterLoop_final4` (S1g)

`counterLoop_final4D` is `counterLoop_final3` (S1f) with the boundary `hdRun : MachineDefinesRun` (free read worlds) replaced by `hdLinked : MachineDefinesLinked` (the worlds of the run's own chain `coreHead → getConstInfo → getEnv → synthesizeFromConst`). The consumers are
the `…C` copies (`Tools/ShippingFGCircuitLinked.lean`, `Tools/ShippingFGCircuitLinked2.lean`).

`counterLoop_final4` SUPPLIES that boundary (`machineDefinesLinked_of_reader`): from `hquiet` (every quiet world reads the start environment: DG-ENV's quiet strengthening, C.EN-4 / ENV), `GetEnvFrame` (the primitive frame law of `getEnv`, C.EN-4 / CellPrem),
`hE`, `hRead` (as in S1e/S1f) and `hgates : EntryGates (envAt cref w) X` (the two refusal facts `certifiedShape? = none`, `mixedCertifiedShape? = none` of the entry constant of ONE environment, the start environment; the third fact `machineShape? = some shape` is `RootReader`'s own conjunct).
No `hdRun`, no `hA6`, no `hw`, no `ReflectsAll`, no `∀`-world statement remains. -/
namespace Tools.ShippingFGCircuitFinal4
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitSupply2 Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitApply Tools.ShippingFGCircuitTransport Tools.ShippingFGCircuitSrc Tools.ShippingFGCircuitFinal Tools.ShippingFGCircuitLinked
open Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMachineEntry (MachineCloses)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5Sem (kDOf)
open Tools.ShippingHierStateG (instFree)
open Sparkle.IR.OptCheck

/-- `leaf_topShips_of_run` from the run-local boundary (same proof, `machineRunJQC_of_closesC`) -/
theorem leaf_topShips_of_runC {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom) {d : Tools.ShippingMachineAuto.MachineData}
    {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D₀ : Sparkle.IR.AST.Design}
    (hdp : p.d = d) (hkp : p.kD = kDOf d) (hleaf : LeafFacts d)
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D₀) w1)
    (hd : MachineDefinesLinked mctx mref cctx cref p.decl p.d.shape w raw D₀ w1)
    (hcl : MachineCloses mctx mref cctx cref p.decl p.d.shape)
    (hpost : Tools.ShippingGen5DCEntry.PostT1 b raw) (n : Nat) : TopShips p n p.decl b raw D₀ := by
  obtain ⟨hok, hco, hSS, houtTy, hnoI, hsl⟩ := hleaf
  subst hdp
  have hran := machineRunJQC_of_closesC L.O hstart.1 hr hd
    (machineClosesAtA_of_closes L.O hcl) hstart.2.1 (Or.inl rfl)
  have hL := (Pkg.trace L.O L.T hstart.1 p hran).toLB
  have htake := leaf_take p.d p.kD hok (by rw [hkp]; exact hco) hnoI
  exact leaf_topShips_of_LB p hL hnoI hsl hok hSS houtTy htake hpost n

/-- `leaf_instFree_of_run` from the run-local boundary -/
theorem leaf_instFree_of_runC {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom) {d : Tools.ShippingMachineAuto.MachineData}
    {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D₀ : Sparkle.IR.AST.Design}
    (hdp : p.d = d) (hleaf : LeafFacts d)
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D₀) w1)
    (hd : MachineDefinesLinked mctx mref cctx cref p.decl p.d.shape w raw D₀ w1)
    (hcl : MachineCloses mctx mref cctx cref p.decl p.d.shape)
    (hpost : Tools.ShippingGen5DCEntry.PostT1 b raw) :
    instFree raw.body ∧ instFree b.body ∧ instFree (checkedOptimize b).body := by
  obtain ⟨hok, hco, hSS, houtTy, hnoI, hsl⟩ := hleaf
  subst hdp
  have hran := machineRunJQC_of_closesC L.O hstart.1 hr hd
    (machineClosesAtA_of_closes L.O hcl) hstart.2.1 (Or.inl rfl)
  have hL := (Pkg.trace L.O L.T hstart.1 p hran).toLB
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, _, wired, tr⟩ := id hL
  obtain ⟨_, hbok, _⟩ := leaf_b_facts wired rlen hnoI hsl hSS houtTy hpost
  obtain ⟨_, _, _, _, _, _, _, houts, _, _, hclean, _⟩ := wired
  obtain ⟨⟨hb, hw, hi, ho⟩, hrstIn, hregs, hevery, _, _, _, _, hokR⟩ := hclean hnoI houtTy
  refine ⟨Tools.ShippingMachineDepthRun.instFree_of_seqOk hokR, Tools.ShippingMachineDepthRun.instFree_of_seqOk hbok,
    Tools.ShippingMachineDepthRun.instFree_of_seqOk (Tools.ShippingChecksDerived.checkedOptimize_seqOk_all hbok)⟩

/-- `hTop` for the printed design of a register leaf from the run-local boundary of the core run(s) from `w` -/
theorem hTop_of_leaf4 {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom) {d : Tools.ShippingMachineAuto.MachineData}
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hdp : p.d = d) (hkp : p.kD = kDOf d) (hleaf : LeafFacts d)
    (hstart : Start L mctx cctx w)
    (hd : ∀ raw D₀ w1, MachineDefinesLinked mctx mref cctx cref p.decl p.d.shape w raw D₀ w1)
    (hcl : MachineCloses mctx mref cctx cref p.decl p.d.shape) :
    ∀ raw, PostRun mctx mref cctx cref w p.decl D' b raw → ∃ n, HasConcretePackage p n p.decl b raw D' := by
  intro raw ⟨D₀, w1, hr, hpe⟩
  have hpost := Tools.ShippingGen5DCEntryD.postEntry_postT1 hpe
  obtain ⟨h1, h2, h3⟩ := leaf_instFree_of_runC L p hdp hleaf hstart hr (hd raw D₀ w1) hcl hpost
  exact ⟨0, rfl, topShips_design_irrel p 0 p.decl D₀ D' h1 h2 h3
    (leaf_topShips_of_runC L p hdp hkp hleaf hstart hr (hd raw D₀ w1) hcl hpost 0)⟩

/-- `counterLoop_artifact_at` with the run-local boundary: the wired endpoint is `machine_ships_wiredC` -/
theorem counterLoop_artifact_atC {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} {ι : Type} {P : Pkgs ι (fun _ => defaultDomain)} {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop}
    {p : Pkg ι (fun _ => defaultDomain)}
    (hE : RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, design) w')
    (hd : ∀ raw D₀ w1, MachineDefinesLinked mctx mref cctx cref ``counterLoop counterLoop.machineData.shape w raw D₀ w1)
    (hP : P ``counterLoop = some p) (hdecl : p.decl = ``counterLoop)
    (hl : EndpointLink counterLoop.machineData 0 (fun _ bools bits => monoObs shCounter counterLoop bools bits) p)
    (hTop : ∀ raw, Post b raw → ∃ n, TopShips p n ``counterLoop b raw design) :
    ∃ mm : MonoTy shCounter, RootArtifactMono (envAt cref w) P Post ``counterLoop shCounter mm b design p ∧
      WiredConclusion ``counterLoop counterLoop.machineData (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shCounter mm bools bits) b :=
  ⟨counterLoop, ⟨hP, counterLoop_denotes hE, observationsEqualMono_of_link counterLoop_shape hl,
      fun raw hraw => (hTop raw hraw).imp fun _ hn => ⟨hdecl, hn⟩⟩,
    Tools.ShippingFGCircuitLinked2.machine_ships_wiredC counterLoop.machineData
      (Tools.ShippingFGCircuitLinked2.machine_traceL_of_loopC counterLoop.machineData (fun i => defaultDomain) counterLoop.machineSigma
        counterLoop.machineInits counterLoop.machineBody counterLoop.machineRes counterLoop.machineResult
        counterLoop.machineSource counterLoop.machine_ok counterLoop.machine_body counterLoop.machine_inits
        counterLoop.machine_reset counterLoop.machine_writes counterLoop.machine_result counterLoop.machine_source)
      (of_decide_eq_true (Eq.refl true)) (of_decide_eq_true (Eq.refl true))
      (of_decide_eq_true (Eq.refl true)) (of_decide_eq_true (Eq.refl true))
      hr hd (counterLoop.machine_closes mctx mref cctx cref)⟩

/-- **`counterLoop_final4D`.** Premises: `Laws L`, `hstart : Start L mctx cctx w` (A.P-02), `hr` (the compile succeeded), `hdRun` (the run-local machine boundary),
`hRead : RootReader` and `hE : RootInEnv` (unchanged from S1e). No `hw`, no `ReflectsAll`, no `hA6`. -/
theorem counterLoop_final4D {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    {d : DefinitionVal}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w')
    (hdRun : ∀ raw D₀ w1, MachineDefinesLinked mctx mref cctx cref ``counterLoop counterLoop.machineData.shape w raw D₀ w1)
    (hRead : RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData)
    (hE : RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d) :
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p := by
  obtain ⟨p, hP, hdecl, hpd, hkp⟩ := genGP_root_canon (ι := ι) (dom := fun _ => defaultDomain) lvl (envAt cref w) hRead
    counterLoop_wf (by have := counterLoop_leafFacts.2.2.2.2.1; exact this)
  obtain ⟨p', hP', hsrc'⟩ := counterLoop_hsrc (ι := ι) lvl (envAt cref w) hRead
  have hpp : p' = p := Option.some.inj (hP'.symm.trans hP)
  subst hpp
  have hl : EndpointLink counterLoop.machineData 0 (fun _ bools bits => monoObs shCounter counterLoop bools bits) p' :=
    ⟨hpd, by rw [hkp]; exact counterLoop_kD, hsrc'⟩
  have hcl : MachineCloses mctx mref cctx cref ``counterLoop counterLoop.machineData.shape := counterLoop.machine_closes mctx mref cctx cref
  have hTop := hTop_of_leaf4 (b := b) (D' := D') L p' hpd hkp counterLoop_leafFacts hstart
    (by rw [hdecl, hpd]; exact hdRun) (by rw [hdecl, hpd]; exact hcl)
  rw [hdecl] at hTop
  have hpost : ∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw := by
    obtain ⟨raw, D₀, w1, hc, hpe⟩ := Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry hr
    exact ⟨raw, D₀, w1, hc, hpe⟩
  obtain ⟨mm, hart, -⟩ := counterLoop_artifact_atC (Post := PostRun mctx mref cctx cref w ``counterLoop D') (P := genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
    hE hr hdRun hP hdecl hl (fun raw hraw => (hTop raw hraw).imp fun _ hn => hn.2)
  exact ⟨hpost, mm, p', hart⟩

/-- the two refusal facts of the entry constant of ONE environment (the third machine-boundary fact, `machineShape?`, is `RootReader`'s conjunct) -/
def EntryGates (env : Environment) (X : Name) : Prop :=
  ∀ E : ConstantInfo, Tools.ShippingGen5Acc.entry₀ env X = some E →
    certifiedShape? false [] E = none ∧ mixedCertifiedShape? false [] E (instancePredicate env) = none

/-- `MachineDefinesLinked` from the start-environment facts: `hE`, `hRead`, `EntryGates`, `hquiet`, `GetEnvFrame` -/
theorem machineDefinesLinked_of_reader {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) {mctx : Meta.Context} {cctx : Core.Context} {lvl : Lean.Expr → Nat} {X : Name} {ty val : Lean.Expr}
    {dd : Tools.ShippingMachineAuto.MachineData} {d : DefinitionVal} {e : Environment}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hquiet : ∀ u, L.O.quiet u → Tools.ShippingGen5Env.ReadsAt e cref u)
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    (hE : RootInEnv e X ty val d) (hRead : RootReader lvl e X dd) (hgates : EntryGates e X) :
    MachineDefinesLinked mctx mref cctx cref X dd.shape w M D w' := by
  obtain ⟨hf, -, -, -⟩ := hE
  obtain ⟨E, hent, hsh, -⟩ := hRead
  have hgE := hgates E hent
  unfold Tools.ShippingGen5Acc.entry₀ at hent
  rw [hf] at hent
  simp only [Option.map_some, Option.some.injEq] at hent
  subst hent
  exact machineDefinesLinked_of_env L hstart.1 hstart.2.1 hquiet hg hf hgE.1 hgE.2 hsh

/-- **`counterLoop_final4`.** Premises: `Laws L`, `hstart` (A.P-02), `hr` (A.P-04), `hquiet` + `GetEnvFrame` (C.EN-4 / ENV), `hgates` (`EntryGates` of the start environment), `hRead` (DG-DATAOF/COVER/ENV), `hE` (`QuoteFact`, C.EN-4 / ENV cache).
`hdRun` / `hA6` are gone: the machine boundary is derived on the run's linked chain. -/
theorem counterLoop_final4 {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    {d : DefinitionVal}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w')
    (hquiet : ∀ u, L.O.quiet u → Tools.ShippingGen5Env.ReadsAt (envAt cref w) cref u)
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    (hgates : EntryGates (envAt cref w) ``counterLoop)
    (hRead : RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData)
    (hE : RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d) :
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p :=
  counterLoop_final4D L lvl hstart hr
    (fun _ _ _ => machineDefinesLinked_of_reader (lvl := lvl) L hstart hquiet hg hE hRead hgates) hRead hE

end Tools.ShippingFGCircuitFinal4

#print axioms Tools.ShippingFGCircuitFinal4.hTop_of_leaf4
#print axioms Tools.ShippingFGCircuitFinal4.counterLoop_final4D
#print axioms Tools.ShippingFGCircuitFinal4.machineDefinesLinked_of_reader
#print axioms Tools.ShippingFGCircuitFinal4.counterLoop_final4
