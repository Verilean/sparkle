import Tools.ShippingFGCircuitS2jTop
import Tools.ShippingGen5T2Range
import Tools.ShippingGen5T2Tie
set_option autoImplicit false
-- FG circuit pilot S2l: `hdec : HftCallDec lvl env` for the non-leaf root `synth_hftPcieOutByte` from the three readers. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §38.

namespace Tools.ShippingFGCircuitS2lDec
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitCover
open Tools.ShippingGenFGLedgerPremises Tools.ShippingGen5Sem
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kPkg Tools.ShippingFGCircuitS1uSrc
open Tools.ShippingFGCircuitS2jKid Tools.ShippingFGCircuitS2jTop
open Tools.ShippingMachineEntry (kindTy)
open Sparkle.IP.Net.HTTP Sparkle.IP.Bus.PCIe

/-! ## 1. one ordinary call to a one-output callee: `CallDec` from `GenExtAtCall` + static data (no run) -/

section Call
variable {ι : Type} {dom : ι → DomainConfig}

/-- **`CallDec` of an ordinary call to a one-output callee** (`callDec_of_callTie` ← `CallTie` ← `GenExtAtCall` + `CallOutRange` + T2-FIELD): `GenExtAtCall` is the table's (`hsem`); T2-FIELD is the callee's single layout output (`callField_one`); `CallOutRange` is `callOutRange_of_widths` (the callee's `o.ty.bitWidth = o.width` and the binder width); the rest is the static data checks. -/
theorem callDec_of_oneOutCall (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hP : P (p.d.shape.insts[k]'hk).1 = some q) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hsem : GenExtAtCall p q k hk) (h1 : p.d.shape.instFields = [])
    (hco : p.d.callsOk p.kD = true) (hsl : p.d.ss.length = p.d.shape.layout.slots.length)
    (hargs : callArgsOkAt p.d p.kD k q.portWidths = true) (hlen : (p.d.shape.insts[k]'hk).2.1.length = q.ports.length)
    (hone : ∃ o, q.d.shape.layout.outs = [o])
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hW : ∀ o, q.d.shape.layout.outs = [o] →
      (p.d.shape.binders[p.kD + k]?).map (fun bn => (kindTy bn.2).bitWidth) = some o.ty.bitWidth) :
    CallDec p q k := by
  obtain ⟨o, ho⟩ := hone
  have hF : ∀ i : ι, ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o :=
    fun _ => ⟨0, o, by rw [ho]; rfl, (callField_one (p := p) (q := q) (k := k) (o := o) h1).mpr ho⟩
  have hR : CallOutWidthAt p q k := by
    intro k' o' _ hcf
    exact hW o' ((callField_one (p := p) (q := q) (k := k) (o := o') h1).mp hcf)
  exact callDec_of_callTie P p q k hk hP hnone (callTie_of_dgen p q k hk hF hsem (callOutRange_of_widths p q k hk houtTy hR))
    hco hsl hargs hlen

end Call

/-! ## 2. the root's and the children's static data (kernel) -/

def dataPW (d : Tools.ShippingMachineAuto.MachineData) (kD : Nat) : List Nat :=
  ((d.bsIn.take kD).filter fun (b : Lean.Name × MixedGateBinder) => b.2 != .domain).map fun b => (kindTy b.2).bitWidth

theorem hft_callsOk : synth_hftPcieOutByte.machineData.callsOk 5 = true := by decide +kernel
theorem hft_slotsLen : synth_hftPcieOutByte.machineData.ss.length = synth_hftPcieOutByte.machineData.shape.layout.slots.length := by decide +kernel
theorem hft_args0 : callArgsOkAt synth_hftPcieOutByte.machineData 5 0 (dataPW httpGetByte.machineData (kDOf httpGetByte.machineData)) = true := by decide +kernel
theorem hft_args1 : callArgsOkAt synth_hftPcieOutByte.machineData 5 1 (dataPW tlpCplByte.machineData (kDOf tlpCplByte.machineData)) = true := by decide +kernel
theorem hft_len0 : ∀ h : 0 < synth_hftPcieOutByte.machineData.shape.insts.length,
    (synth_hftPcieOutByte.machineData.shape.insts[0]'h).2.1.length = (((httpGetByte.machineData.bsIn.take (kDOf httpGetByte.machineData)).filter fun (b : Lean.Name × MixedGateBinder) => b.2 != .domain).length) := by decide +kernel
theorem hft_len1 : ∀ h : 1 < synth_hftPcieOutByte.machineData.shape.insts.length,
    (synth_hftPcieOutByte.machineData.shape.insts[1]'h).2.1.length = (((tlpCplByte.machineData.bsIn.take (kDOf tlpCplByte.machineData)).filter fun (b : Lean.Name × MixedGateBinder) => b.2 != .domain).length) := by decide +kernel
theorem hft_len0' (d : Tools.ShippingMachineAuto.MachineData) (hd : d = synth_hftPcieOutByte.machineData) : ∀ h : 0 < d.shape.insts.length,
    (d.shape.insts[0]'h).2.1.length = (((httpGetByte.machineData.bsIn.take (kDOf httpGetByte.machineData)).filter fun (b : Lean.Name × MixedGateBinder) => b.2 != .domain).length) := by
  subst hd; exact hft_len0
theorem hft_len1' (d : Tools.ShippingMachineAuto.MachineData) (hd : d = synth_hftPcieOutByte.machineData) : ∀ h : 1 < d.shape.insts.length,
    (d.shape.insts[1]'h).2.1.length = (((tlpCplByte.machineData.bsIn.take (kDOf tlpCplByte.machineData)).filter fun (b : Lean.Name × MixedGateBinder) => b.2 != .domain).length) := by
  subst hd; exact hft_len1
theorem http_outsLen : httpGetByte.machineData.shape.layout.outs.length = 1 := by decide +kernel
theorem tlp_outsLen : tlpCplByte.machineData.shape.layout.outs.length = 1 := by decide +kernel
theorem http_outTy : ∀ o ∈ httpGetByte.machineData.shape.layout.outs, o.ty.bitWidth = o.width := by decide +kernel
theorem tlp_outTy : ∀ o ∈ tlpCplByte.machineData.shape.layout.outs, o.ty.bitWidth = o.width := by decide +kernel

/-! ## 3. `hdec` from the three readers -/

section Main
variable {ι : Type}

/-- **`hdec` from the readers** (FG D.D-4 `G-CALLDEC` / T2-TIE for the root `synth_hftPcieOutByte`). The premises are the three `RootReader`s at the table's environment (the root and the two children); no run, no world, no `Start`, no `ShipsRes`. -/
theorem hftCallDec_of_readers (lvl : Lean.Expr → Nat) (env : Environment)
    (hreadR : RootReader lvl env hftRoot synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl env hftHttp httpGetByte.machineData)
    (hreadT : RootReader lvl env hftTlp tlpCplByte.machineData) :
    HftCallDec (ι := ι) lvl env := by
  intro p hP k hk
  obtain ⟨E, hEnt, hsh, hdat⟩ := hreadR
  obtain ⟨g, hgr, hgd⟩ := canon_row (lvl := lvl) (env := env) root_wf hsh hdat
  obtain ⟨Eh, hEh, hshh, hdath⟩ := id hreadH
  obtain ⟨gh, hgh, hghd⟩ := canon_row (lvl := lvl) (env := env) http_wf hshh hdath
  obtain ⟨Et, hEt, hsht, hdatt⟩ := id hreadT
  obtain ⟨gt, hgt, hgtd⟩ := canon_row (lvl := lvl) (env := env) tlp_wf hsht hdatt
  have hkids : ∀ c ∈ g.d.shape.insts.map (·.1), ∃ (Ec : ConstantInfo) (gc : Tools.ShippingGen5Sem.GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) Ec (structEnv env)),
      Tools.ShippingGen5Acc.entry₀ env c = some Ec ∧ canonGD lvl env Ec = some gc ∧ gc.d.shape.insts = [] := by
    intro c hc
    rw [hgd, root_insts] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨Eh, gh, hEh, hgh, by rw [hghd]; exact http_leaf⟩
    · exact ⟨Et, gt, hEt, hgt, by rw [hgtd]; exact tlp_leaf⟩
  obtain ⟨p', hP', hdecl, hpd, hkp⟩ := genGP_root_kids (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) env hEnt hgr hkids
  obtain rfl : p' = p := Option.some.inj (hP'.symm.trans hP)
  rw [hgd] at hpd
  have hkD : p'.kD = 5 := by rw [hkp, hgd]; exact root_kD
  obtain ⟨cpH, hPH, hdeclH, hdH, hkH⟩ := kid_pkg (ι := ι) lvl env hreadH http_wf http_leaf http_ss
  obtain ⟨cpT, hPT, hdeclT, hdT, hkT⟩ := kid_pkg (ι := ι) lvl env hreadT tlp_wf tlp_leaf tlp_ss
  have hmapP : p'.d.shape.insts.map (·.1) = [hftHttp, hftTlp] := by rw [hpd]; exact root_insts
  have hlen : p'.d.shape.insts.length = 2 := by have := congrArg List.length hmapP; simpa using this
  have h1 := congrArg (fun l => l[k]?) hmapP
  simp only [List.getElem?_map, List.getElem?_eq_getElem hk] at h1
  have hord : ∀ k, k < p'.d.shape.insts.length → (p'.d.shape.instOrigins.getD k .ord).child? = none := fun k hk => by
    rw [hpd]; exact hft_ord k (by rw [← hpd]; exact hk)
  have hi1 : p'.d.shape.instFields = [] := by rw [hpd]; exact hft_instFields
  have hco : p'.d.callsOk p'.kD = true := by rw [hpd, hkD]; exact hft_callsOk
  have hsl : p'.d.ss.length = p'.d.shape.layout.slots.length := by rw [hpd]; exact hft_slotsLen
  have hk2 : k < 2 := hlen ▸ hk
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · have hn : (p'.d.shape.insts[0]).1 = hftHttp := Option.some.inj (by simpa using h1)
    have hq : GPt (ι := ι) lvl env (p'.d.shape.insts[0]).1 = some (Pkg.comb cpH) := by rw [hn]; exact hPH
    refine ⟨Pkg.comb cpH, hq, callDec_of_oneOutCall (GPt (ι := ι) lvl env) p' (Pkg.comb cpH) 0 hk hq (hord 0 hk)
      (hDT1_of_genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) env hftRoot p' hP 0 hk (hord 0 hk) _ hq)
      hi1 hco hsl ?_ ?_ ?_ ?_ ?_⟩
    · have hpw : (Pkg.comb cpH).portWidths = dataPW httpGetByte.machineData (kDOf httpGetByte.machineData) := by
        simp only [Pkg.portWidths, Pkg.ports, Pkg.d, Pkg.kD, dataPW, hdH, hkH]
      rw [hpw, hpd, hkD]; exact hft_args0
    · have := hft_len0' p'.d hpd hk
      have hpl : (Pkg.comb cpH).ports.length = (((httpGetByte.machineData.bsIn.take (kDOf httpGetByte.machineData)).filter fun (b : Lean.Name × MixedGateBinder) => b.2 != .domain).length) := by
        simp only [Pkg.ports, Pkg.d, Pkg.kD, hdH, hkH]
      rw [hpl]; exact this
    · exact List.length_eq_one_iff.mp (by simpa only [Pkg.d, hdH] using http_outsLen)
    · intro o ho; exact http_outTy o (by have h : o ∈ cpH.d.shape.layout.outs := ho; rw [hdH] at h; exact h)
    · intro o ho
      rw [hpd, hkD]
      exact hft_width0 o (by have : cpH.d.shape.layout.outs = [o] := ho; rw [hdH] at this; rw [this]; exact List.mem_singleton_self o)
  · have hn : (p'.d.shape.insts[1]).1 = hftTlp := Option.some.inj (by simpa using h1)
    have hq : GPt (ι := ι) lvl env (p'.d.shape.insts[1]).1 = some (Pkg.comb cpT) := by rw [hn]; exact hPT
    refine ⟨Pkg.comb cpT, hq, callDec_of_oneOutCall (GPt (ι := ι) lvl env) p' (Pkg.comb cpT) 1 hk hq (hord 1 hk)
      (hDT1_of_genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) env hftRoot p' hP 1 hk (hord 1 hk) _ hq)
      hi1 hco hsl ?_ ?_ ?_ ?_ ?_⟩
    · have hpw : (Pkg.comb cpT).portWidths = dataPW tlpCplByte.machineData (kDOf tlpCplByte.machineData) := by
        simp only [Pkg.portWidths, Pkg.ports, Pkg.d, Pkg.kD, dataPW, hdT, hkT]
      rw [hpw, hpd, hkD]; exact hft_args1
    · have := hft_len1' p'.d hpd hk
      have hpl : (Pkg.comb cpT).ports.length = (((tlpCplByte.machineData.bsIn.take (kDOf tlpCplByte.machineData)).filter fun (b : Lean.Name × MixedGateBinder) => b.2 != .domain).length) := by
        simp only [Pkg.ports, Pkg.d, Pkg.kD, hdT, hkT]
      rw [hpl]; exact this
    · exact List.length_eq_one_iff.mp (by simpa only [Pkg.d, hdT] using tlp_outsLen)
    · intro o ho; exact tlp_outTy o (by have h : o ∈ cpT.d.shape.layout.outs := ho; rw [hdT] at h; exact h)
    · intro o ho
      rw [hpd, hkD]
      exact hft_width1 o (by have : cpT.d.shape.layout.outs = [o] := ho; rw [hdT] at this; rw [this]; exact List.mem_singleton_self o)

end Main

end Tools.ShippingFGCircuitS2lDec

#print axioms Tools.ShippingFGCircuitS2lDec.callDec_of_oneOutCall
#print axioms Tools.ShippingFGCircuitS2lDec.hftCallDec_of_readers
