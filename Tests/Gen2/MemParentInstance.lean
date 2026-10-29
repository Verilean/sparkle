import Tools.ShippingGen2MemShips
import Tests.Compiler.Srm4RunTest
set_option autoImplicit false

/-! # M2-a: the CONDITIONAL instance of `memParent_ships` on `leafM` (MEMPARENT_FREEZE.md rev1 §4.7)

`leafM` (Tests/Compiler/SharedLeafMemKidTest.lean, circuit-do, one memory entry, slots ≠ []). The package and every
data / case premise of `MemParentStmt'` are SUPPLIED here from the existing generated facts. The compiler-run premises
(the run, `MachineDefines`, `MachineTaken`, `AdmCtx`, `JQC`) stay hypotheses: this is package/data satisfiability, NOT
evidence that an actual successful compiler run exists. The real-IP instance is `sparkle-gen2-loop-pkg`. -/
set_option maxHeartbeats 4000000

namespace Tests.Gen2.MemParentInstance
open Tools.ShippingGen2
open Tests.Compiler.SharedLeafMemKidIfaceTest Tests.Compiler.SharedLeafMemKidTest
open Sparkle.Core.Domain

abbrev U := fun _ : Unit => defaultDomain

/-- `leafM`'s package at `Unit`, its `GenFacts` restricted from `(DomainConfig, id)`. -/
noncomputable def lmPkg : SrcPkg Unit U :=
  { decl := ``leafM, d := leafM.machineData, kD := 4, ρ := _, inh := inferInstance,
    inits := leafM.machineInits, body := fun _ => leafM.machineBody defaultDomain,
    obsR := fun _ => leafM.machineResult defaultDomain, ext := fun _ => leafM.machineExt defaultDomain,
    extB := fun _ => leafM.machineExtB defaultDomain, src := fun _ => leafM.machineSource defaultDomain,
    gen := genFacts_restrict leafM.machineData defaultDomain leafM_gen }

theorem lm_dataOk : MemParentDataOk lmPkg := by
  unfold MemParentDataOk MemParentDataOkB; first | decide | decide +kernel

theorem lm_extInS : ExtInS lmPkg :=
  ⟨fun _ bools bits j hj => leafM_hextB defaultDomain bools bits j hj,
   fun _ bools bits j n' hj => leafM_hext defaultDomain bools bits j n' hj⟩

theorem lm_memDec : ∀ (k : Nat) (hk : k < lmPkg.d.shape.insts.length), MemDec lmPkg k (lmPkg.d.shape.insts[k]).1 := by
  intro k hk _ bools bits
  exact leafM_memcalls defaultDomain bools bits k _ (by rw [List.getElem?_map, List.getElem?_eq_getElem (show k < leafM.machineData.shape.insts.length from hk)]; rfl)

theorem lm_memOrigin : MemOrigin lmPkg := memOrigin_of_memDec lmPkg lm_memDec

/-- **The conditional instance**: for every compiler run of `leafM` meeting the run premises, both conclusions. -/
theorem lm_ships {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design)
    (hA : Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx cctx)
    (hjqc : Tools.ShippingChildCacheA.JQC L.O (Tools.ShippingChildBndCore.dv w) w)
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore lmPkg.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref lmPkg.decl lmPkg.d.shape)
    (ran : MachineTaken L mctx cctx (Tools.ShippingChildBndCore.dv w + 1) lmPkg.decl lmPkg.d.shape raw D) (n : Nat) :
    TopShips lmPkg (n + 1) lmPkg.decl b raw D ∧ ChildShips lmPkg (n + 1) b D :=
  memParent_ships L lmPkg mctx cctx w w1 raw b D lm_dataOk lm_extInS lm_memOrigin leafM_insts_ne leafM_fne
    leafM_slotsNe hA hjqc hcore hpost entry ran lm_memDec n

#print axioms Tools.ShippingGen2.memParent_ships
#print axioms Tools.ShippingGen2.memParent_topShips
#print axioms Tools.ShippingGen2.memParent_childShips
#print axioms Tools.ShippingGen2.memKSn_boundedIn
#print axioms Tools.ShippingGen2.resetNk_memInvN
#print axioms Tools.ShippingGen2.core_kidsMem_ranAM
#print axioms Tools.ShippingGen2.hkidW_of_memOrigin
#print axioms Tools.ShippingGen2.memOrigin_of_memDec
#print axioms Tools.ShippingGen2.pkg_memComposedNW
#print axioms Tools.ShippingGen2C6.seqChildRunN_of_composedNW_run
#print axioms lm_ships

end Tests.Gen2.MemParentInstance
