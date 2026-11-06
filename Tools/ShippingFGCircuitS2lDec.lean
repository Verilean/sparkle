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
theorem http_outsLen : httpGetByte.machineData.shape.layout.outs.length = 1 := by decide +kernel
theorem tlp_outsLen : tlpCplByte.machineData.shape.layout.outs.length = 1 := by decide +kernel
theorem http_outTy : ∀ o ∈ httpGetByte.machineData.shape.layout.outs, o.ty.bitWidth = o.width := by decide +kernel
theorem tlp_outTy : ∀ o ∈ tlpCplByte.machineData.shape.layout.outs, o.ty.bitWidth = o.width := by decide +kernel

end Tools.ShippingFGCircuitS2lDec
