import Tools.ShippingGen2SlotlessLeaf
import Tests.Compiler.ShippingMachineLinkedTest
set_option autoImplicit false

/-! # M2-step S2 on `Pkg.comb`: the CONDITIONAL instance of `slotlessLeaf_ships` on `pickByteH`
(scripts/gen2/PKG_COMB_FREEZE.md §5)

`pickByteH` (Tests/Compiler/ShippingMachineLinkedTest.lean:21): a slotless, call-free machine-route declaration (a
plain `let` expression) with lets. Its package is `.comb` over the comb endpoint's generated facts (`combProof`:
`machineSource`, `machine_ok/body/inits/next/result`; `machine_result` is the kernel-checked tie of the Lean source's
observations to the IR). The data/case premises are decided here; the compiler-run premises (the run, `hpost`,
`MachineDefines`, `MachineTaken`, `AdmCtx`, `JQC`) stay hypotheses — package/data satisfiability, NOT evidence that a
run exists. (Earlier failed diagnostics: g2st-s2i-bf7d963e (no `.gen` package for pickByteH), g2st-s2i-bb31bb0b (a
register-free `circuit do` is refused).) -/
set_option maxHeartbeats 4000000

namespace Tests.Gen2.SlotlessLeafInstance
open Tools.ShippingGen2
open Sparkle.Tests.Compiler.ShippingMachineLinkedTest
open Sparkle.Core.Domain

abbrev U := fun _ : Unit => defaultDomain

noncomputable def pbhC : CombPkg Unit U :=
  { decl := ``pickByteH, d := pickByteH.machineData, kD := pickByteH.machineData.bsIn.length,
    inits := pickByteH.machineInits, src := pickByteH.machineSource,
    facts := ⟨pickByteH.machine_ok, pickByteH.machine_body, pickByteH.machine_inits, pickByteH.machine_next,
      pickByteH.machine_result⟩ }

noncomputable abbrev pbhPkg : Pkg Unit U := .comb pbhC

/-- `lsrc` is not vacuous: `pickByteH` has lets. -/
theorem pbh_ls_ne : pickByteH.machineData.ls ≠ [] := by decide

theorem pbh_dataOk : LeafDataOk pbhPkg := by
  unfold LeafDataOk LeafDataOkB; first | decide | decide +kernel

theorem pbh_extInS : ExtInS pbhPkg := ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

theorem pbh_noI : pbhPkg.d.shape.insts = [] := by decide

theorem pbh_slots0 : pbhPkg.d.shape.layout.slots = [] := by decide

/-- **The conditional instance** on a real slotless declaration. -/
theorem pbh_ships {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design)
    (hA : Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx cctx)
    (hjqc : Tools.ShippingChildCacheA.JQC L.O (Tools.ShippingChildBndCore.dv w) w)
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore pbhPkg.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref pbhPkg.decl pbhPkg.d.shape)
    (ran : MachineTaken L mctx cctx (Tools.ShippingChildBndCore.dv w + 1) pbhPkg.decl pbhPkg.d.shape raw D)
    (n : Nat) :
    TopShips pbhPkg n pbhPkg.decl b raw D ∧ ChildShips pbhPkg n b D :=
  slotlessLeaf_ships L pbhPkg mctx cctx w w1 raw b D pbh_dataOk pbh_extInS pbh_noI pbh_slots0
    hA hjqc hcore hpost entry ran n

#print axioms pbh_ls_ne
#print axioms pbh_dataOk
#print axioms pbh_ships

end Tests.Gen2.SlotlessLeafInstance
