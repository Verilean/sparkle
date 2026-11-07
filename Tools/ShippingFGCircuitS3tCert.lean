import Tools.ShippingFGCircuitS3tSat
set_option autoImplicit false
-- FG circuit pilot S3t, step 1 (the structural part of `CheckRoot` on the closed artifact): the certificate `cert0` (UNTRUSTED hints: the indices of the two `inst` statements in the returned top module, the 17 register names in slot order; read off `pilotB0`), and `structuralOk rootS pilotB0 pilotD0 cert0 = true` by the KERNEL; negative controls (a missing child, a swapped child, a wrong width, a wrong output, a register reset value changed, no `rst`, a rejected certificate).  `CheckRoot` itself is false for every input (its body validator is not written, `bodyOk`), so `certifiedReturn` refuses today.  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §69.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3tCert
open Sparkle.IR.AST Tools.ShippingFGCircuitS3tSpec Tools.ShippingFGCircuitS3rArtifact

/-- the certificate of the pilot artifact (untrusted generator output) -/
def cert0 : Cert := { callAt := [173, 238], regs := ["_gen_cnt", "_gen_cnt_1", "_gen_fmtR_1", "_gen_reqR_1", "_gen_tagR_1", "_gen_addrR_1", "_gen_doneR_1", "_gen_r0_2", "_gen_r1_2", "_gen_r2_2", "_gen_r3_2", "_gen_cplCnt_2", "_gen_reqIdLatch_2", "_gen_tagLatch_2", "_gen_lowAddrLatch_2", "_gen_dataLatch_2", "_gen_wPulseR_2"] }

theorem struct_ok : structuralOk rootS pilotB0 pilotD0 cert0 = true := by decide +kernel

/-- `CheckRoot` is false today: its body validator `bodyOk` is not written -/
theorem check_root_refuses : CheckRoot rootS pilotB0 pilotD0 cert0 = false := by decide +kernel

/-! ### negative controls (the structural part is FALSE on each altered input) -/

/-- a design without the second child -/
def noKid1 (D : Design) : Design := { D with modules := D.modules.take 1 }
/-- a design without the first child -/
def noKid0 (D : Design) : Design := { D with modules := D.modules.drop 1 }
/-- the children's names exchanged (each module under the other's name) -/
def swapNames (D : Design) : Design :=
  { D with modules := match D.modules with
      | [a, b] => [{ a with name := b.name }, { b with name := a.name }]
      | ms => ms }
/-- the second child's first input port one bit narrower -/
def narrowKid1 (D : Design) : Design :=
  { D with modules := D.modules.map fun m => if m.name == "Sparkle_IP_Bus_PCIe_tlpCplByte" then
      { m with inputs := m.inputs.map fun p => if p.name == "_gen_cplId" then { p with ty := .bitVector 15 } else p } else m }
/-- the top module's output port one bit narrower -/
def narrowOut (b : Module) : Module := { b with outputs := b.outputs.map fun p => { p with ty := .bitVector 7 } }
/-- every register's reset value changed to 1 -/
def flipInit (b : Module) : Module :=
  { b with body := b.body.map fun st => match st with
      | .register o c r i _ => .register o c r i 1
      | s => s }
/-- the top module without its `rst` input -/
def noRst (b : Module) : Module := { b with inputs := b.inputs.filter fun p => p.name != "rst" }

theorem neg_no_kid1 : structuralOk rootS pilotB0 (noKid1 pilotD0) cert0 = false := by decide +kernel
theorem neg_no_kid0 : structuralOk rootS pilotB0 (noKid0 pilotD0) cert0 = false := by decide +kernel
theorem neg_swap_names : structuralOk rootS pilotB0 (swapNames pilotD0) cert0 = false := by decide +kernel
theorem neg_narrow_kid1 : structuralOk rootS pilotB0 (narrowKid1 pilotD0) cert0 = false := by decide +kernel
theorem neg_narrow_out : structuralOk rootS (narrowOut pilotB0) pilotD0 cert0 = false := by decide +kernel
theorem neg_flip_init : structuralOk rootS (flipInit pilotB0) pilotD0 cert0 = false := by decide +kernel
theorem neg_no_rst : structuralOk rootS (noRst pilotB0) pilotD0 cert0 = false := by decide +kernel
/-- certificates that name the wrong statements or registers -/
theorem neg_cert_swapped : structuralOk rootS pilotB0 pilotD0 { cert0 with callAt := [238, 173] } = false := by decide +kernel
theorem neg_cert_same : structuralOk rootS pilotB0 pilotD0 { cert0 with callAt := [173, 173] } = false := by decide +kernel
theorem neg_cert_regs : structuralOk rootS pilotB0 pilotD0 { cert0 with regs := cert0.regs.reverse } = false := by decide +kernel
/-- the data checks reject a data with a wrong child width or a wrong number of children -/
theorem neg_data_width : structuralOk { rootS with kidInW := [[7], [16, 16, 8, 8, 32, 5]] } pilotB0 pilotD0 cert0 = false := by decide +kernel
theorem neg_data_kids : structuralOk { rootS with kidMod := ["Sparkle_IP_Net_HTTP_httpGetByte"] } pilotB0 pilotD0 cert0 = false := by decide +kernel

/-! ### the simultaneous-satisfaction example at the artifact's own registers -/

/-- the artifact's 17 registers (the cert's names) are distinct and lie in the claimed names' register range -/
theorem cert0_regs : cert0.regs.Nodup ∧ (∀ r ∈ cert0.regs, r ∈ rootS.portNames.drop
    (rootS.portNames.length - rootS.d.shape.layout.lets - rootS.d.shape.layout.slots.length)) := by
  decide +kernel

/-- **the four seed premises of `RootShowsAt` hold together** at the artifact's registers, for every per-cycle input values: `(a)` the input ports `_gen_rxByte … _gen_cplId` carry the values, `(b)` the registers read the state, `(c)` `rst` is 0, `(d)` register `k` starts at slot `k`'s init -/
theorem example_premises (val : Nat → Nat → Nat) :
    ∃ (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) (st0 : String → Nat),
      (∀ (t : Nat) (st : String → Nat) (q : Nat) (nm : String), q < rootS.kD → rootS.portNames[q]? = some nm →
        seed t st nm = val t q) ∧
      (∀ (t : Nat) (st : String → Nat) (r : String), r ∈ cert0.regs → seed t st r = st r) ∧
      (∀ (t : Nat) (st : String → Nat), seed t st "rst" = 0) ∧
      (∀ (k : Nat) (r : String) (f : Sparkle.IR.Machine.SlotField), cert0.regs[k]? = some r →
        rootS.d.shape.layout.slots[k]? = some f → st0 r = f.init) :=
  Tools.ShippingFGCircuitS3tSat.rootS_premises cert0.regs cert0_regs.1 cert0_regs.2 val

end Tools.ShippingFGCircuitS3tCert
