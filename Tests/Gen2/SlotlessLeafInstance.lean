import Tools.ShippingGen2SlotlessLeaf
import Tests.Compiler.ShippingMachineLinkedTest
set_option autoImplicit false

/-! # M2-step S2: the CONDITIONAL instance of `slotlessLeaf_ships` on `pickByteH`

`pickByteH` (Tests/Compiler/ShippingMachineLinkedTest.lean:21): a slotless (no register), call-free machine-route
module with `let`s and one output. The package and every data / case premise of `SlotlessLeafStmt` are SUPPLIED
here; without calls the extension is the inputs themselves (`ext := bits`, `extB := bools`), so `ExtInS` is `rfl`.
The compiler-run premises stay hypotheses: package/data satisfiability, NOT evidence that a run exists. -/
set_option maxHeartbeats 4000000

namespace Tests.Gen2.SlotlessLeafInstance
open Tools.ShippingGen2
open Sparkle.Tests.Compiler.ShippingMachineLinkedTest
open Sparkle.Core.Domain

abbrev U := fun _ : Unit => defaultDomain

noncomputable instance pbh_inh : Inhabited (Sparkle.Core.HList (Tools.ShippingMachineDenote.tys pickByteH.machineData.ss)) :=
  ⟨pickByteH.machineInits⟩

theorem pbh_gen : Tools.ShippingQuadComposed.GenFacts pickByteH.machineData U
    pickByteH.machineInits pickByteH.machineBody pickByteH.machineResult
    (fun _ _ bits _ => bits) (fun _ bools _ _ => bools) pickByteH.machineSource :=
  ⟨pickByteH.machine_ok, pickByteH.machine_body, pickByteH.machine_inits, pickByteH.machine_writes,
   pickByteH.machine_result, pickByteH.machine_source, fun _ _ _ _ _ _ _ => ⟨fun _ _ => rfl, fun _ => rfl⟩⟩

noncomputable def pbhSrc : SrcPkg Unit U :=
  { decl := ``pickByteH, d := pickByteH.machineData, kD := pickByteH.machineData.bsIn.length, ρ := _,
    inh := inferInstance, inits := pickByteH.machineInits, body := pickByteH.machineBody,
    obsR := pickByteH.machineResult, ext := fun _ _ bits _ => bits, extB := fun _ bools _ _ => bools,
    src := pickByteH.machineSource, gen := pbh_gen }

noncomputable abbrev pbhPkg : Pkg Unit U := .gen pbhSrc

theorem pbh_dataOk : LeafDataOk pbhPkg := by
  unfold LeafDataOk LeafDataOkB; first | decide | decide +kernel

theorem pbh_extInS : ExtInS pbhPkg := ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

theorem pbh_noI : pbhPkg.d.shape.insts = [] := by decide

theorem pbh_slots0 : pbhPkg.d.shape.layout.slots = [] := by decide

/-- **The conditional instance**: every compiler run of `pickByteH` meeting the run premises ships at every height
(top and as a combinational child). -/
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

#print axioms pbh_dataOk
#print axioms pbh_ships

end Tests.Gen2.SlotlessLeafInstance
