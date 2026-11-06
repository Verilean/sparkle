import Tools.ShippingFGCircuitSrc
import Tools.ShippingFGCircuitTransport
set_option autoImplicit false
-- FG circuit pilot S1e, unit 3: the final theorem of ONE root (`counterLoop`) with `hsrc` and `DesignTransport` supplied. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # `counterLoop_final2`: one root, connected to the generated package

`Tools/ShippingFGCircuitApply.lean` `counterLoop_final` had the premises `hw hr hA6 hRead hE hsrc htr`. Here `hsrc` is `Tools/ShippingFGCircuitSrc.lean` `counterLoop_hsrc` (from `RootReader`, the package's `src` is the declaration's `Signal.loop`
observation) and `htr` is `Tools/ShippingFGCircuitTransport.lean` `designTransport_of_leaf` (from the core run; the printed design is irrelevant for an instance-free leaf). The premises that remain are exactly:

* `hw : EntryWitness …`, `hr : RunsTo (synthesizeCombinational counterLoop) …` — the compile succeeded (the antecedent);
* `hA6` — the row `h_A_P06` of `FGLedgerPremisesStmtG` at the generated table (its `∀`-world form is under reviewer review);
* `hRead : RootReader` — `dataOfAt`/`machineShape?` agree with the literal `counterLoop.machineData` in the environment (DG-DATAOF / DG-COVER / DG-ENV);
* `hE : RootInEnv …` — the environment's entry for `counterLoop` is the quoted one (`QuoteFact` + `EnvSnapshot`; C.EN-4 / ENV cache). -/
namespace Tools.ShippingFGCircuitFinal
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitSupply2 Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitApply Tools.ShippingFGCircuitTransport Tools.ShippingFGCircuitSrc
open Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMachineEntry (MachineDefines MachineCloses)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingChildInvA (AdmCtx)

/-- `hTop` for the printed design of a register leaf, from the core run alone (no transport premise) -/
theorem hTop_of_leaf2 {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom) {d : Tools.ShippingMachineAuto.MachineData}
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hdp : p.d = d) (hkp : p.kD = Tools.ShippingGen5Sem.kDOf d) (hleaf : LeafFacts d)
    (hstart : Start L mctx cctx w)
    (hd : MachineDefines mctx mref cctx cref p.decl p.d.shape)
    (hcl : MachineCloses mctx mref cctx cref p.decl p.d.shape) :
    ∀ raw, PostRun mctx mref cctx cref w p.decl D' b raw → ∃ n, HasConcretePackage p n p.decl b raw D' := by
  intro raw ⟨D₀, w1, hr, hpe⟩
  have hpost := Tools.ShippingGen5DCEntryD.postEntry_postT1 hpe
  exact ⟨0, rfl, designTransport_of_leaf L p hdp hleaf hstart hr hd hcl hpost 0
    (leaf_topShips_of_run L p hdp hkp hleaf hstart hr hd hcl hpost 0)⟩

theorem counterLoop_final2 {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
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
  have hd : MachineDefines mctx mref cctx cref ``counterLoop counterLoop.machineData.shape :=
    machineDefines_of_witness hw hA6 hP hl
  have hcl : MachineCloses mctx mref cctx cref ``counterLoop counterLoop.machineData.shape := counterLoop.machine_closes mctx mref cctx cref
  have hTop := hTop_of_leaf2 (b := b) (D' := D') L p' hpd hkp counterLoop_leafFacts hw.1 (by rw [hdecl, hpd]; exact hd) (by rw [hdecl, hpd]; exact hcl)
  rw [hdecl] at hTop
  have hpost : ∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw := by
    obtain ⟨raw, D₀, w1, hc, hpe⟩ := Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry hr
    exact ⟨raw, D₀, w1, hc, hpe⟩
  obtain ⟨mm, hart, -⟩ := counterLoop_artifact_at (Post := PostRun mctx mref cctx cref w ``counterLoop D') (P := genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
    hE hr hd hP hdecl hl (fun raw hraw => (hTop raw hraw).imp fun _ hn => hn.2)
  exact ⟨hpost, mm, p', hart⟩

end Tools.ShippingFGCircuitFinal

#print axioms Tools.ShippingFGCircuitFinal.hTop_of_leaf2
#print axioms Tools.ShippingFGCircuitFinal.counterLoop_final2
