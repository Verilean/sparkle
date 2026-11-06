import Tools.ShippingFGCircuitS1kStmt
import Tools.ShippingFGCircuitCover
set_option autoImplicit false
-- FG circuit pilot S1k, unit 3: kernel facts about the three machine data literals and the package table for the non-leaf root. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.
namespace Tools.ShippingFGCircuitS1kPkg
open Lean Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen5DeclConnect Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kRoot
open Tools.ShippingGen5Sem (kDOf GenWF)
open Tools.ShippingGen5Acc Tools.ShippingGen5DataOf Tools.ShippingGenFGLedgerPremises Tools.ShippingGen5SM1 Tools.ShippingFGCircuitCover
open Tools.ShippingMachineAuto (MachineData)
open Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5FG Tools.ShippingGen5Sem
open Tools.ShippingMachineDenote Tools.ShippingMachineSource

theorem root_wf : GenWF synth_hftPcieOutByte.machineData = true := by decide +kernel
theorem http_wf : GenWF Sparkle.IP.Net.HTTP.httpGetByte.machineData = true := by decide +kernel
theorem tlp_wf : GenWF Sparkle.IP.Bus.PCIe.tlpCplByte.machineData = true := by decide +kernel
theorem http_leaf : Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape.insts = [] := by decide +kernel
theorem tlp_leaf : Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.shape.insts = [] := by decide +kernel
theorem root_insts : synth_hftPcieOutByte.machineData.shape.insts.map (·.1) = [hftHttp, hftTlp] := by decide +kernel
theorem root_kD : kDOf synth_hftPcieOutByte.machineData = 5 := by decide +kernel
theorem root_shape : ShapeMatchesMono shHft synth_hftPcieOutByte.machineData 5 := by unfold ShapeMatchesMono; decide +kernel

section
variable {ι : Type} {dom : ι → DomainConfig}

/-- a leaf row of the table makes `genS` succeed at that name (the single-name case of `genGP_root`) -/
theorem genS_leaf_isSome (lvl : Lean.Expr → Nat) {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound (dataOfAt lvl) initsOf)
    (genData₀ : (env : Environment) → (E : ConstantInfo) → Option (GenData (dataOfAt lvl) E (structEnv env)))
    (env : Environment) {c : Name} {E : ConstantInfo} {g : GenData (dataOfAt lvl) E (structEnv env)}
    (hE : entry₀ env c = some E) (hg : genData₀ env E = some g) (hleaf : g.d.shape.insts = []) :
    Acc (CallRel (genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env))) c ∧
    (genS (genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env)) c).isSome := by
  let K := genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env)
  have hgK : K.genData₀ E = some g := hg
  have hd0 : dataOf₀ K c = some g.d := dataOf₀_of_genData₀ K hE hgK
  have hacc : Acc (CallRel K) c := by
    refine Acc.intro c fun y hy => ?_
    obtain ⟨d, hd, k, hk, -, -⟩ := hy
    rw [hd0] at hd
    have hd' : d = g.d := (Option.some.inj hd).symm
    subst hd'
    rw [hleaf] at hk
    exact absurd hk (by simp)
  refine ⟨hacc, ?_⟩
  have hunf := genS_unfold K hacc hE hgK
  have hall : ∀ k ∈ K.ordCallees (K.dOf g), (genS K ((K.dOf g).shape.insts[k]).1).isSome := by
    intro k _
    have hlen : (K.dOf g).shape.insts.length = 0 := by
      show g.d.shape.insts.length = 0
      rw [hleaf]; rfl
    have := k.2
    omega
  rw [if_pos hall] at hunf
  rw [hunf]; rfl

/-- **`genGP` covers a root whose callees are leaf rows of the table**: the package's declaration, data and `kD` as for a leaf (`genGP_root`). -/
theorem genGP_root_kids (lvl : Lean.Expr → Nat) {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound (dataOfAt lvl) initsOf)
    (genData₀ : (env : Environment) → (E : ConstantInfo) → Option (GenData (dataOfAt lvl) E (structEnv env)))
    (env : Environment) {X : Name} {E : ConstantInfo} {g : GenData (dataOfAt lvl) E (structEnv env)}
    (hE : entry₀ env X = some E) (hg : genData₀ env E = some g)
    (hkids : ∀ c ∈ g.d.shape.insts.map (·.1), ∃ (Ec : ConstantInfo) (gc : GenData (dataOfAt lvl) Ec (structEnv env)),
      entry₀ env c = some Ec ∧ genData₀ env Ec = some gc ∧ gc.d.shape.insts = []) :
    ∃ p : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl hs genData₀ env X = some p ∧ p.decl = X ∧ p.d = g.d ∧ p.kD = kDOf g.d := by
  let K := genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env)
  have hgK : K.genData₀ E = some g := hg
  have hd0 : dataOf₀ K X = some g.d := dataOf₀_of_genData₀ K hE hgK
  have hleafK : ∀ k : Fin g.d.shape.insts.length,
      Acc (CallRel K) (g.d.shape.insts[k]).1 ∧ (genS K (g.d.shape.insts[k]).1).isSome := by
    intro k
    obtain ⟨Ec, gc, hEc, hgc, hl⟩ := hkids _ (List.mem_map.2 ⟨g.d.shape.insts[k], List.getElem_mem k.2, rfl⟩)
    exact genS_leaf_isSome (ι := ι) (dom := dom) lvl hs genData₀ env hEc hgc hl
  have hacc : Acc (CallRel K) X := by
    refine Acc.intro X fun y hy => ?_
    obtain ⟨d, hd, k, hk, -, hy⟩ := hy
    rw [hd0] at hd
    have hd' : d = g.d := (Option.some.inj hd).symm
    subst hd'
    subst hy
    exact (hleafK ⟨k, hk⟩).1
  have hunf := genS_unfold K hacc hE hgK
  have hall : ∀ k ∈ K.ordCallees (K.dOf g), (genS K ((K.dOf g).shape.insts[k]).1).isSome := by
    intro k _
    exact (hleafK k).2
  rw [if_pos hall] at hunf
  have hF := factsOf_genS_assembled'' (ι := ι) (dom := dom) hs (genData₀ env)
  have hP := genP_eq_some K hF hunf
  have hpp : genGP (ι := ι) (dom := dom) lvl hs genData₀ env X = some _ := hP
  refine ⟨_, hpp, ?_, ?_, ?_⟩
  · exact genP_decl K hF hP
  · obtain ⟨d', hd', hpd⟩ := genP_d_edges K hF hP
    rw [hd0] at hd'
    rw [hpd, ← Option.some.inj hd']
  · obtain ⟨s, hs', hps⟩ := genP_some_inv K hF hP
    rw [hunf] at hs'
    have hs'' : s = K.genSem (genS K) X g := (Option.some.inj hs').symm
    rw [← kD_toSem, hps, hs'']
    exact genSemI_kD _ _ _

end

theorem hftRootType_shape : monoGo [] hftRootType = some shHft := by decide

open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitS1iChild

/-- **`synth_hftPcieOutByte_final`**: the non-leaf root's final theorem, from the four named obligations (`HftObCD`, `HftObSrc`, `HftObTopCore`, `HftObNoRaw`) and the children's readers. Proved here: `genGP` covers the root
(its two callees are leaf rows), the package's `decl`/`data`/`kD`, the shape correspondence, `SourceDenotesMono` from `RootInEnv` and `HftObCD`, `TopShips` on the printed design from `HftObTopCore` + `HftObNoRaw` by `topShips_transport`. -/
theorem synth_hftPcieOutByte_final : HftFinalStmt := by
  intro ι mref cref L lvl env₀ mctx cctx w w' b D' hstart hr hhead hcell hchk hRdH hRdT hCD hSrc hTop hNoRaw
  obtain ⟨raw, D₀, w1, hc, hpe⟩ := Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry hr
  obtain ⟨hgates, ⟨d, hE⟩, hRead⟩ := startFacts_of_checked hchk (root_find_of_headAt hhead hc)
  have hdRun : ∀ raw D₀ w1, Tools.ShippingFGCircuitLinked.MachineDefinesLinked mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1 :=
    fun _ _ _ => machineDefinesLinked_of_reader_headAt hhead (Tools.ShippingFGCircuitS1hFrame.getEnvFrame_of_readWorld hcell) hE hRead hgates
  obtain ⟨E, hEnt, hsh, hdat⟩ := hRead
  obtain ⟨g, hg, hgd⟩ := canon_row (lvl := lvl) (env := envAt cref w) root_wf hsh hdat
  obtain ⟨Eh, hEh, hshh, hdath⟩ := hRdH
  obtain ⟨gh, hgh, hghd⟩ := canon_row (lvl := lvl) (env := envAt cref w) http_wf hshh hdath
  obtain ⟨Et, hEt, hsht, hdatt⟩ := hRdT
  obtain ⟨gt, hgt, hgtd⟩ := canon_row (lvl := lvl) (env := envAt cref w) tlp_wf hsht hdatt
  have hkids : ∀ c ∈ g.d.shape.insts.map (·.1), ∃ (Ec : ConstantInfo) (gc : GenData (dataOfAt lvl) Ec (structEnv (envAt cref w))),
      entry₀ (envAt cref w) c = some Ec ∧ canonGD lvl (envAt cref w) Ec = some gc ∧ gc.d.shape.insts = [] := by
    intro c hc
    rw [hgd, root_insts] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨Eh, gh, hEh, hgh, by rw [hghd]; exact http_leaf⟩
    · exact ⟨Et, gt, hEt, hgt, by rw [hgtd]; exact tlp_leaf⟩
  obtain ⟨p, hP, hdecl, hpd, hkp⟩ := genGP_root_kids (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w) hEnt hg hkids
  rw [hgd] at hpd
  have hkD : p.kD = 5 := by rw [hkp, hgd]; exact root_kD
  have hl : EndpointLink synth_hftPcieOutByte.machineData 5 (fun _ bools bits => monoObs shHft synth_hftPcieOutByte bools bits) p :=
    ⟨hpd, hkD, hSrc p hP⟩
  have hpost : ∃ raw, PostRun mctx mref cctx cref w hftRoot D' b raw := ⟨raw, D₀, w1, hc, hpe⟩
  refine ⟨hpost, synth_hftPcieOutByte, p, hP, ?_, observationsEqualMono_of_link root_shape hl, ?_⟩
  · obtain ⟨hf, hlv, ht, hv⟩ := hE
    refine ⟨rfl, d, hf, hlv, ?_, ?_⟩
    · show (if d.levelParams.isEmpty = true then monoGo [] d.type else none) = some shHft
      rw [hlv, ht]; simpa using hftRootType_shape
    · rw [hv]; exact hCD
  · intro raw' ⟨D₀', w1', hr', hpe'⟩
    obtain ⟨n, hn⟩ := hTop p hP hdRun raw' D₀' w1' hr' hpe'
    obtain ⟨h1, h2, h3⟩ := hNoRaw raw' D₀' w1' hr' hpe'
    exact ⟨n, hdecl, topShips_transport p n hftRoot hpe' (h1 n) (h2 n) h3 hn⟩

end Tools.ShippingFGCircuitS1kPkg

#print axioms Tools.ShippingFGCircuitS1kPkg.genGP_root_kids
#print axioms Tools.ShippingFGCircuitS1kPkg.synth_hftPcieOutByte_final
