import Tools.ShippingFGCircuitFinal
import Tools.ShippingFGCircuitRunLocal2
set_option autoImplicit false
-- FG circuit pilot S1f, unit 3: `counterLoop_final3`: Start + hr only, and the run-local boundary `MachineDefinesRun` consumed all the way. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # `counterLoop_final3`

Changes against `counterLoop_final2` (S1e):

1. `hw : EntryWitness ReflectsAll L …` is gone. The proof only used its `Start` part (`hw.1`) and `hr`; `hw` also carried `ReflectsAll L declName parameters`, which was never supplied and never used. The premises are now `hstart : Start L mctx cctx w`
   and `hr`. `Laws L` stays an explicit argument: it is an obligation that remains (the uniform runtime laws, A.P-02); `Start` is the admissible-context / depth-0 start of the OUTERMOST call.
2. `hA6` (h_A_P06, `∀`-world `MachineDefines`) is gone. The boundary is `hdRun : ∀ raw D₀ w1, MachineDefinesRun … w raw D₀ w1` (`Tools/ShippingFGCircuitRunLocal.lean`): the three machine-boundary facts, asked only of the `ci` / `envR` / `envR'` that the core run
   from the start world `w` reads. It is consumed by `machineRunJQC_of_closesR` (the package trace; leaf `TopShips`; `DesignTransport`) and by `machine_ships_wiredR` (the endpoint, `Tools/ShippingFGCircuitRunLocal2.lean`).
   It is NOT supplied: it is the run-local form of the h_A_P06 row.
3. `hRead` and `hE` are unchanged in this theorem (docs §11.3 says what was tried). -/
namespace Tools.ShippingFGCircuitFinal3
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitSupply2 Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitApply Tools.ShippingFGCircuitTransport Tools.ShippingFGCircuitSrc Tools.ShippingFGCircuitFinal Tools.ShippingFGCircuitRunLocal
open Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMachineEntry (MachineCloses)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5Sem (kDOf)
open Tools.ShippingHierStateG (instFree)
open Sparkle.IR.OptCheck

/-- `leaf_topShips_of_run` from the run-local boundary (same proof, `machineRunJQC_of_closesR`) -/
theorem leaf_topShips_of_runR {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom) {d : Tools.ShippingMachineAuto.MachineData}
    {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D₀ : Sparkle.IR.AST.Design}
    (hdp : p.d = d) (hkp : p.kD = kDOf d) (hleaf : LeafFacts d)
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D₀) w1)
    (hd : MachineDefinesRun mctx mref cctx cref p.decl p.d.shape w raw D₀ w1)
    (hcl : MachineCloses mctx mref cctx cref p.decl p.d.shape)
    (hpost : Tools.ShippingGen5DCEntry.PostT1 b raw) (n : Nat) : TopShips p n p.decl b raw D₀ := by
  obtain ⟨hok, hco, hSS, houtTy, hnoI, hsl⟩ := hleaf
  subst hdp
  have hran := machineRunJQC_of_closesR L.O hstart.1 hr hd
    (machineClosesAtA_of_closes L.O hcl) hstart.2.1 (Or.inl rfl)
  have hL := (Pkg.trace L.O L.T hstart.1 p hran).toLB
  have htake := leaf_take p.d p.kD hok (by rw [hkp]; exact hco) hnoI
  exact leaf_topShips_of_LB p hL hnoI hsl hok hSS houtTy htake hpost n

/-- `leaf_instFree_of_run` from the run-local boundary -/
theorem leaf_instFree_of_runR {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom) {d : Tools.ShippingMachineAuto.MachineData}
    {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D₀ : Sparkle.IR.AST.Design}
    (hdp : p.d = d) (hleaf : LeafFacts d)
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D₀) w1)
    (hd : MachineDefinesRun mctx mref cctx cref p.decl p.d.shape w raw D₀ w1)
    (hcl : MachineCloses mctx mref cctx cref p.decl p.d.shape)
    (hpost : Tools.ShippingGen5DCEntry.PostT1 b raw) :
    instFree raw.body ∧ instFree b.body ∧ instFree (checkedOptimize b).body := by
  obtain ⟨hok, hco, hSS, houtTy, hnoI, hsl⟩ := hleaf
  subst hdp
  have hran := machineRunJQC_of_closesR L.O hstart.1 hr hd
    (machineClosesAtA_of_closes L.O hcl) hstart.2.1 (Or.inl rfl)
  have hL := (Pkg.trace L.O L.T hstart.1 p hran).toLB
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, _, wired, tr⟩ := id hL
  obtain ⟨_, hbok, _⟩ := leaf_b_facts wired rlen hnoI hsl hSS houtTy hpost
  obtain ⟨_, _, _, _, _, _, _, houts, _, _, hclean, _⟩ := wired
  obtain ⟨⟨hb, hw, hi, ho⟩, hrstIn, hregs, hevery, _, _, _, _, hokR⟩ := hclean hnoI houtTy
  refine ⟨Tools.ShippingMachineDepthRun.instFree_of_seqOk hokR, Tools.ShippingMachineDepthRun.instFree_of_seqOk hbok,
    Tools.ShippingMachineDepthRun.instFree_of_seqOk (Tools.ShippingChecksDerived.checkedOptimize_seqOk_all hbok)⟩

/-- `hTop` for the printed design of a register leaf from the run-local boundary of the core run(s) from `w` -/
theorem hTop_of_leaf3 {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom) {d : Tools.ShippingMachineAuto.MachineData}
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hdp : p.d = d) (hkp : p.kD = kDOf d) (hleaf : LeafFacts d)
    (hstart : Start L mctx cctx w)
    (hd : ∀ raw D₀ w1, MachineDefinesRun mctx mref cctx cref p.decl p.d.shape w raw D₀ w1)
    (hcl : MachineCloses mctx mref cctx cref p.decl p.d.shape) :
    ∀ raw, PostRun mctx mref cctx cref w p.decl D' b raw → ∃ n, HasConcretePackage p n p.decl b raw D' := by
  intro raw ⟨D₀, w1, hr, hpe⟩
  have hpost := Tools.ShippingGen5DCEntryD.postEntry_postT1 hpe
  obtain ⟨h1, h2, h3⟩ := leaf_instFree_of_runR L p hdp hleaf hstart hr (hd raw D₀ w1) hcl hpost
  exact ⟨0, rfl, topShips_design_irrel p 0 p.decl D₀ D' h1 h2 h3
    (leaf_topShips_of_runR L p hdp hkp hleaf hstart hr (hd raw D₀ w1) hcl hpost 0)⟩

/-- `counterLoop_artifact_at` with the run-local boundary: the wired endpoint is `machine_ships_wiredR` -/
theorem counterLoop_artifact_atR {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} {ι : Type} {P : Pkgs ι (fun _ => defaultDomain)} {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop}
    {p : Pkg ι (fun _ => defaultDomain)}
    (hE : RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, design) w')
    (hd : ∀ raw D₀ w1, MachineDefinesRun mctx mref cctx cref ``counterLoop counterLoop.machineData.shape w raw D₀ w1)
    (hP : P ``counterLoop = some p) (hdecl : p.decl = ``counterLoop)
    (hl : EndpointLink counterLoop.machineData 0 (fun _ bools bits => monoObs shCounter counterLoop bools bits) p)
    (hTop : ∀ raw, Post b raw → ∃ n, TopShips p n ``counterLoop b raw design) :
    ∃ mm : MonoTy shCounter, RootArtifactMono (envAt cref w) P Post ``counterLoop shCounter mm b design p ∧
      WiredConclusion ``counterLoop counterLoop.machineData (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shCounter mm bools bits) b :=
  ⟨counterLoop, ⟨hP, counterLoop_denotes hE, observationsEqualMono_of_link counterLoop_shape hl,
      fun raw hraw => (hTop raw hraw).imp fun _ hn => ⟨hdecl, hn⟩⟩,
    Tools.ShippingFGCircuitRunLocal2.machine_ships_wiredR counterLoop.machineData
      (Tools.ShippingFGCircuitRunLocal2.machine_traceL_of_loopR counterLoop.machineData (fun i => defaultDomain) counterLoop.machineSigma
        counterLoop.machineInits counterLoop.machineBody counterLoop.machineRes counterLoop.machineResult
        counterLoop.machineSource counterLoop.machine_ok counterLoop.machine_body counterLoop.machine_inits
        counterLoop.machine_reset counterLoop.machine_writes counterLoop.machine_result counterLoop.machine_source)
      (of_decide_eq_true (Eq.refl true)) (of_decide_eq_true (Eq.refl true))
      (of_decide_eq_true (Eq.refl true)) (of_decide_eq_true (Eq.refl true))
      hr hd (counterLoop.machine_closes mctx mref cctx cref)⟩

/-- **`counterLoop_final3`.** Premises: `Laws L`, `hstart : Start L mctx cctx w` (A.P-02), `hr` (the compile succeeded), `hdRun` (the run-local machine boundary),
`hRead : RootReader` and `hE : RootInEnv` (unchanged from S1e). No `hw`, no `ReflectsAll`, no `hA6`. -/
theorem counterLoop_final3 {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    {d : DefinitionVal}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w')
    (hdRun : ∀ raw D₀ w1, MachineDefinesRun mctx mref cctx cref ``counterLoop counterLoop.machineData.shape w raw D₀ w1)
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
  have hTop := hTop_of_leaf3 (b := b) (D' := D') L p' hpd hkp counterLoop_leafFacts hstart
    (by rw [hdecl, hpd]; exact hdRun) (by rw [hdecl, hpd]; exact hcl)
  rw [hdecl] at hTop
  have hpost : ∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw := by
    obtain ⟨raw, D₀, w1, hc, hpe⟩ := Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry hr
    exact ⟨raw, D₀, w1, hc, hpe⟩
  obtain ⟨mm, hart, -⟩ := counterLoop_artifact_atR (Post := PostRun mctx mref cctx cref w ``counterLoop D') (P := genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
    hE hr hdRun hP hdecl hl (fun raw hraw => (hTop raw hraw).imp fun _ hn => hn.2)
  exact ⟨hpost, mm, p', hart⟩

end Tools.ShippingFGCircuitFinal3

#print axioms Tools.ShippingFGCircuitFinal3.hTop_of_leaf3
#print axioms Tools.ShippingFGCircuitFinal3.counterLoop_final3
