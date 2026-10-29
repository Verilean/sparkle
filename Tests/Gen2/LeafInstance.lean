import Tools.ShippingGen2Leaf
import Tests.Compiler.SharedLeafGenTest
set_option autoImplicit false

/-! # M2-a2: the CONDITIONAL instance of `leaf_ships` on `leaf16` (LEAF_FREEZE.md rev2 §5)

`leaf16` (Tests/Compiler/SharedLeafGenTest.lean:35): one 16-bit register, one bits input, outputs `s`/`odd`, no
calls. The package and every data / case premise of `LeafStmt'` are SUPPLIED here from the generated facts; without
calls the extension is the inputs themselves (`ext := bits`, `extB := bools`), so `ExtInS` is `rfl`. The
compiler-run premises stay hypotheses: this is package/data satisfiability, NOT evidence that an actual successful
compiler run exists. -/
set_option maxHeartbeats 4000000

namespace Tests.Gen2.LeafInstance
open Tools.ShippingGen2
open Tests.Compiler.SharedLeafGenTest
open Sparkle.Core.Domain

abbrev U := fun _ : Unit => defaultDomain

/-- The state type is inhabited by the reset values (the generator registers no instance for a callless leaf). -/
noncomputable instance leaf16_inh : Inhabited (Sparkle.Core.HList (Tools.ShippingMachineDenote.tys leaf16.machineData.ss)) :=
  ⟨leaf16.machineInits⟩

/-- `leaf16`'s `GenFacts` at `(DomainConfig, id)` with the identity extension, from its generated `machine_*`
theorems. -/
theorem leaf16_gen : Tools.ShippingQuadComposed.GenFacts leaf16.machineData (fun i : DomainConfig => i)
    leaf16.machineInits leaf16.machineBody leaf16.machineResult
    (fun _ _ bits _ => bits) (fun _ bools _ _ => bools) leaf16.machineSource :=
  ⟨leaf16.machine_ok, leaf16.machine_body, leaf16.machine_inits, leaf16.machine_writes, leaf16.machine_result,
   leaf16.machine_source, fun _ _ _ _ _ _ _ => ⟨fun _ _ => rfl, fun _ => rfl⟩⟩

/-- `leaf16`'s package at `Unit`. -/
noncomputable def leaf16Src : SrcPkg Unit U :=
  { decl := ``leaf16, d := leaf16.machineData, kD := leaf16.machineData.bsIn.length, ρ := _,
    inh := inferInstance, inits := leaf16.machineInits, body := fun _ => leaf16.machineBody defaultDomain,
    obsR := fun _ => leaf16.machineResult defaultDomain, ext := fun _ _ bits _ => bits,
    extB := fun _ bools _ _ => bools, src := fun _ => leaf16.machineSource defaultDomain,
    gen := genFacts_restrict leaf16.machineData defaultDomain leaf16_gen }

noncomputable abbrev leaf16Pkg : Pkg Unit U := .gen leaf16Src

theorem leaf16_dataOk : LeafDataOk leaf16Pkg := by
  unfold LeafDataOk LeafDataOkB; first | decide | decide +kernel

theorem leaf16_extInS : ExtInS leaf16Pkg :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

theorem leaf16_noI : leaf16Pkg.d.shape.insts = [] := by decide

theorem leaf16_slotsNe : leaf16Pkg.d.shape.layout.slots ≠ [] := by decide

/-- **The conditional instance**: for every compiler run of `leaf16` meeting the run premises, both conclusions at
every height. -/
theorem leaf16_ships {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design)
    (hA : Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx cctx)
    (hjqc : Tools.ShippingChildCacheA.JQC L.O (Tools.ShippingChildBndCore.dv w) w)
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore leaf16Pkg.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref leaf16Pkg.decl leaf16Pkg.d.shape)
    (ran : MachineTaken L mctx cctx (Tools.ShippingChildBndCore.dv w + 1) leaf16Pkg.decl leaf16Pkg.d.shape raw D)
    (n : Nat) :
    TopShips leaf16Pkg n leaf16Pkg.decl b raw D ∧ ChildShips leaf16Pkg n b D :=
  leaf_ships L leaf16Pkg mctx cctx w w1 raw b D leaf16_dataOk leaf16_extInS leaf16_noI leaf16_slotsNe
    hA hjqc hcore hpost entry ran n

#print axioms Tools.ShippingGen2.leaf_ships
#print axioms Tools.ShippingGen2.leaf_topShips_of_LB
#print axioms Tools.ShippingGen2.leaf_childShips_of_LB
#print axioms Tools.ShippingGen2.traceL_of_LB
#print axioms Tools.ShippingGen2LeafSeq.seqStream_of_L
#print axioms Tools.ShippingGen2LeafSeq.seqChildRun_of_L
#print axioms leaf16_ships

end Tests.Gen2.LeafInstance
