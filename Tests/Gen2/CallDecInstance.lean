import Tools.ShippingGen2CallDec
import Tools.ShippingGen2Data
import Tests.Compiler.QuadCallsTest
set_option autoImplicit false

/-! # G-CALLDEC probe step 2: a real `CallDec` (scripts/gen2/CALLDEC_PROBE_FREEZE.md §3)

The generated parent `topshare2` (callees `wrapQ`, `wrapP`, 3 declared inputs each) of
Tests/Compiler/QuadCallsTest.lean. Suppliers, all existing: `b_gen`, `b_wrapQ_gen`, `b_wrapP_gen` (the generated
`machine_*` facts), `b_topshare2_hFP` (`CallFactF`, extracted from the generated `machine_composedNR2`), `b_quadAll`
(the decided data facts). The callees' packages are restricted to the parent's index by `genFacts_restrict`. -/
set_option maxHeartbeats 4000000

namespace Tests.Gen2.CallDecInstance
open Tools.ShippingGen2
open Tools.ShippingQuadCalls Tools.ShippingQuadComposed Tools.ShippingQuadLeafGeneric
open Tests.Compiler.QuadCallsTest Tests.Compiler.SharedLeafGenTest
open Sparkle.Core.Domain

abbrev U := fun _ : Unit => defaultDomain

noncomputable def tm2Pkg : SrcPkg Unit U :=
  { decl := ``topshare2, d := topshare2.machineData, kD := 3, ρ := _, inh := inferInstance,
    inits := topshare2.machineInits, body := topshare2.machineBody, obsR := topshare2.machineResult,
    ext := topshare2.machineExt, extB := topshare2.machineExtB, src := topshare2.machineSource, gen := b_gen }

noncomputable def wQPkg : SrcPkg Unit U :=
  { decl := ``wrapQ, d := wrapQ.machineData, kD := 3, ρ := _, inh := inferInstance,
    inits := wrapQ.machineInits, body := fun _ => wrapQ.machineBody defaultDomain,
    obsR := fun _ => wrapQ.machineResult defaultDomain, ext := fun _ => wrapQ.machineExt defaultDomain,
    extB := fun _ => wrapQ.machineExtB defaultDomain, src := fun _ => wrapQ.machineSource defaultDomain,
    gen := genFacts_restrict wrapQ.machineData defaultDomain b_wrapQ_gen }

noncomputable def wPPkg : SrcPkg Unit U :=
  { decl := ``wrapP, d := wrapP.machineData, kD := 3, ρ := _, inh := inferInstance,
    inits := wrapP.machineInits, body := fun _ => wrapP.machineBody defaultDomain,
    obsR := fun _ => wrapP.machineResult defaultDomain, ext := fun _ => wrapP.machineExt defaultDomain,
    extB := fun _ => wrapP.machineExtB defaultDomain, src := fun _ => wrapP.machineSource defaultDomain,
    gen := genFacts_restrict wrapP.machineData defaultDomain b_wrapP_gen }

/-- The package assignment of the probe. -/
noncomputable def P2 : Pkgs Unit U :=
  fun c => if c = ``wrapQ then some wQPkg else if c = ``wrapP then some wPPkg else none

theorem hne : (``wrapQ : Lean.Name) ≠ ``wrapP := by decide

theorem P2_outs : pkgOutsC P2 = quadOutsOf ``wrapQ ``wrapP wrapQ.machineData wrapP.machineData := by
  funext c
  unfold pkgOutsC P2 quadOutsOf
  by_cases h1 : c = ``wrapQ
  · subst h1; simp [wQPkg]
  · by_cases h2 : c = ``wrapP
    · subst h2; simp [hne.symm, wPPkg]
    · simp [h1, h2]

theorem P2_bs : pkgBsC P2 = quadBsF ``wrapQ ``wrapP wrapQ.machineData wrapP.machineData 3 3 := by
  funext c
  unfold pkgBsC P2 quadBsF
  by_cases h1 : c = ``wrapQ
  · subst h1; simp [wQPkg]
  · by_cases h2 : c = ``wrapP
    · subst h2; simp [hne.symm, wPPkg]
    · simp [h1, h2]

theorem P2_S : (fun i => pkgS P2 i) =
    quadSrcF ``wrapQ ``wrapP wrapQ.machineData wrapP.machineData 3 3 wrapQ.machineSource wrapP.machineSource := by
  funext i c
  unfold pkgS P2 quadSrcF
  by_cases h1 : c = ``wrapQ
  · subst h1; simp [wQPkg, SrcPkg.S]
  · by_cases h2 : c = ``wrapP
    · subst h2; simp [hne.symm, wPPkg, SrcPkg.S]
    · simp [h1, h2]

/-- `CallFactF` of the package, from the existing generated-fact theorem. -/
theorem tm2_hF : CallFactF tm2Pkg.d tm2Pkg.kD tm2Pkg.lsrc tm2Pkg.extS tm2Pkg.extBS (pkgOutsC P2)
    (fun i => pkgS P2 i) := by
  rw [P2_outs, P2_S]
  exact b_topshare2_hFP

/-- **A real `CallDec`**: every call of `topshare2` (all ordinary) has its callee's package and `CallDec`. -/
theorem tm2_callDec : ∀ (k : Nat) (hk : k < tm2Pkg.d.shape.insts.length),
    ∃ q, P2 (tm2Pkg.d.shape.insts[k]).1 = some q ∧ CallDec tm2Pkg q k := by
  intro k hk
  have Q := b_quadAll
  have hwid : ∀ (d : Tools.ShippingMachineAuto.MachineData) (n : Nat), Tools.ShippingCallsChildPorts.argWidths d n =
      ((d.bsIn.take n).filter fun b => b.2 != .domain).map fun b => (Sparkle.Compiler.Elab.kindTy b.2).bitWidth := by
    intro d n
    unfold Tools.ShippingCallsChildPorts.argWidths
    rw [List.map_map]; rfl
  have hw : ∀ (k : Nat) (hk : k < tm2Pkg.d.shape.insts.length),
      quadWidthsOf ``wrapQ ``wrapP wrapQ.machineData wrapP.machineData 3 3 (quadCalleeAt tm2Pkg.d k) =
      ((pkgBsC P2 (tm2Pkg.d.shape.insts[k]).1).filter fun b => b.2 != .domain).map
        fun b => (Sparkle.Compiler.Elab.kindTy b.2).bitWidth := by
    intro k hk
    rw [P2_bs, quadCalleeAt_eq _ k hk]
    rcases quad_insts_mem Q.hP k hk with hn | hn
    · rw [hn]; unfold quadWidthsOf quadBsF; rw [if_pos rfl, if_pos rfl]; exact hwid _ 3
    · rw [hn]; unfold quadWidthsOf quadBsF
      rw [if_neg (Ne.symm Q.hP.c12), if_neg (Ne.symm Q.hP.c12), if_pos rfl, if_pos rfl]; exact hwid _ 3
  have hlen : ∀ (k : Nat) (hk : k < tm2Pkg.d.shape.insts.length), (tm2Pkg.d.shape.insts[k]).2.1.length =
      ((pkgBsC P2 (tm2Pkg.d.shape.insts[k]).1).filter fun b => b.2 != .domain).length := by
    intro k hk
    rw [P2_bs]
    have hnk := Q.hP.argsN k hk
    rcases quad_callee_at Q.hP k hk with ⟨hn, hk2⟩ | ⟨hn, hk2⟩
    · rw [hn]; unfold quadBsF; rw [if_pos rfl]
      simp only [quadNk, hk2, if_true] at hnk
      rw [← hnk, Q.hC₁.hNIn]
    · rw [hn]; unfold quadBsF; rw [if_neg (Ne.symm Q.hP.c12), if_pos rfl]
      simp only [quadNk, hk2, if_false] at hnk
      rw [← hnk, Q.hC₂.hNIn]
  have hnone : (tm2Pkg.d.shape.instOrigins.getD k .ord).child? = none := by
    have hlt : k < tm2Pkg.d.shape.instTagged.length := by
      rw [Tools.ShippingInstTagged.instTagged_length]; exact hk
    have h := Q.hP.child _ (List.getElem_mem hlt)
    rw [Tools.ShippingInstTagged.instTagged_getElem_snd] at h
    simpa [Tools.ShippingInstTagged.originAt] using h
  rcases quad_insts_mem Q.hP k hk with hn | hn
  · refine ⟨wQPkg, by show P2 _ = _; rw [hn]; simp [P2], ?_⟩
    exact callDec_of_callFactF P2 tm2Pkg wQPkg k hk (by show P2 _ = _; rw [hn]; simp [P2]) hnone tm2_hF
      Q.hP.ok Q.hP.callsOk Q.hP.slots _ Q.hPX.callArgs hw hlen
  · refine ⟨wPPkg, by show P2 _ = _; rw [hn]; simp [P2, hne.symm], ?_⟩
    exact callDec_of_callFactF P2 tm2Pkg wPPkg k hk (by show P2 _ = _; rw [hn]; simp [P2, hne.symm]) hnone tm2_hF
      Q.hP.ok Q.hP.callsOk Q.hP.slots _ Q.hPX.callArgs hw hlen

/-- `DataOk` of the three packages (non-vacuity on this instance). -/
theorem tm2_dataOk : DataOk tm2Pkg ∧ DataOk wQPkg ∧ DataOk wPPkg := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold DataOk DataOkB; first | decide | decide +kernel)

#print axioms Tools.ShippingGen2.callDec_of_callFactF
#print axioms Tools.ShippingGen2.callFactF_of_hPointAt_pkg
#print axioms Tools.ShippingGen2.genFacts_restrict
#print axioms tm2_callDec
#print axioms tm2_dataOk

end Tests.Gen2.CallDecInstance
