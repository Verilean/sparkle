import Tools.ShippingSrm17Ran
import Tools.ShippingSrm12Corr
set_option autoImplicit false
-- UNBUILT (unit SRM17): see REPORT-SRM17.md for run names / exits.
-- SCOPE: the RECURSION over `RealChildA` for the three structural facts `ModP` (Tools/ShippingSrm17Body.lean), in the style of SRM12's `ran_designCorr`/`memCallee_childCorr`/`childCorr_noInst`.
-- `ChildP O c`: the served module and every module of the served design of every `RealChildA` of `c` satisfy `ModP`.  PROVED generically: `ran_designP` (a machine run with calls: its module, post-processed module and every module of its
-- design, from the callees' `ChildP`), `memCallee_childP` (a callee over `MemCalleeData`), `leaf_childP` (a plain leaf: from the interface and `leaf_modPA`), `memModule_modP` (a built memory module).
-- PREMISES of those theorems (named in the statements): `hsl : slots ≠ []` (`ran_modP`), `hord` (the ordinary kids' `ChildIfaceP`, as for `memCallee_childCorr`), `hkids` (the callees' own `ChildP`), the machine entry.
-- `RealChildA` is a history of past synthesis results, not semantic correctness in the current environment.  No `sorry`, no `axiom`, no `native_decide`, no heartbeat option.
namespace Tools.ShippingSrm17Corr
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingChildVCA Tools.ShippingChildRunA Tools.ShippingChildBndCore Tools.ShippingChildRunAKids
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineClosesData Tools.ShippingMachineCloses Tools.ShippingMachineAuto
open Tools.ShippingMemCloses Tools.ShippingCallsMemA
open Tools.ShippingSrm3Iface Tools.ShippingSrm3Callee
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingInstTagged (originAt)
open Sparkle.Compiler.MachMemory (memModule)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingSrm17Body Tools.ShippingSrm17Ran

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- the three facts for the served module and every module of the served design of every `RealChildA` of the declaration `c` -/
def ChildP (O : RefLawsAOps MkRefd mref cref) (c : Name) : Prop :=
  ∀ y : Res, RealChildA O c y → ∀ m ∈ y.1 :: y.2.modules, ModP m

/-- **A built memory module satisfies `ModP`**: its body is one memory statement and one assignment (no instance, no register). -/
theorem memModule_modP (cb : Bool) (aw dw : Nat) : ModP (memModule cb aw dw).1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro mn i c mn' c' h1 _
    simp [memModule] at h1
  · intro r c rs inp init c' rs' inp' init' h1 _
    simp [memModule] at h1
  · intro nm aw' dw' c wa wd we ra rd cr ew er hm c' rs' inp' init' hr
    simp [memModule] at hr

/-- **GENERIC step** (the analogue of `ran_designCorr`): for a machine run `ran` with calls, its module `M`, its post-processed form `b` and every module of its design `D` satisfy `ModP`.  Premises: `hsl`, `hkids` (the ordinary
kids' `ChildP`). -/
theorem ran_designP (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    (hkids : ∀ (k : Nat) (hk : k < d.shape.insts.length), (originAt d.shape k).child? = none →
      ChildP O (d.shape.insts[k]).1) :
    ModP M ∧ ModP b ∧ ∀ g ∈ D.modules, ModP g := by
  obtain ⟨hM, hb⟩ := ran_modP O d ok hbody hC hslots hdomB hins hsl hfne outTy hpost ran
  obtain ⟨-, -, -, -, hmods, -⟩ := core_kids_facts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran
  refine ⟨hM, hb, ?_⟩
  intro g' hg'
  obtain ⟨k, hk, y, hKT, hor, -⟩ := hmods g' hg'
  rcases hKT with hmem | ⟨hnone, hre⟩
  · obtain ⟨cb, aw, dw, rfl⟩ := Tools.ShippingInstTagged.child?_eq_memModule hmem
    rcases hor with h | h
    · rw [h]; exact memModule_modP cb aw dw
    · have : g' = (memModule cb aw dw).1 := by
        simpa [Tools.ShippingSrm12Corr.memModule_design_modules] using h
      rw [this]; exact memModule_modP cb aw dw
  · have := hkids k hk hnone y hre
    rcases hor with h | h
    · exact this g' (by rw [h]; exact List.mem_cons_self)
    · exact this g' (List.mem_cons_of_mem _ h)

/-- **`ChildP` of a callee over `MemCalleeData`** (the analogue of `memCallee_childCorr`; same premises `hord`, entry, plus `hsl` and `hkids`). -/
theorem memCallee_childP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {d : MachineData} {C : Name} {n : Nat} {nameK : Nat → String} {nk : Nat → Nat}
    {outsK namesK : Nat → List String} {names : List String}
    (hC : MemCalleeData d C n nameK nk outsK namesK names)
    (hord : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res), (originAt d.shape k).child? = none →
      RealChildA O (d.shape.insts[k]).1 y → ChildIfaceP (nameK k) (nk k) (outsK k) (namesK k) y.1 y.2)
    (entry : MachineDefines mctx mref cctx cref C d.shape)
    (hsl : d.shape.layout.slots ≠ [])
    (hkids : ∀ (k : Nat) (hk : k < d.shape.insts.length), (originAt d.shape k).child? = none →
      ChildP O (d.shape.insts[k]).1) :
    ChildP O C := by
  intro y hy
  obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ :=
    Tools.ShippingSrm4Core5.deepChild_ranAM O T d hC.ok hC.body (nDecl := n) hC.callsOk hC.slots hC.domB hC.insts_ne hC.fne hC.outTy
      (Tools.ShippingSrm4Kid.memCallee_hsep O hC hord) entry (fun m c hA => memCallee_closesA O T hA hC (hord m c hA)) hy
  obtain ⟨-, hb, hD⟩ := ran_designP O d hC.ok hC.body (nDecl := n) hC.callsOk hC.slots hC.domB hC.insts_ne hsl hC.fne hC.outTy hpost ran hkids
  intro m hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact hb
  · exact hD m (by rw [← hdes]; exact hm)

/-- **`ChildP` of a plain leaf** (a machine without calls, `LeafData`): the served design is empty (`ChildIfaceG.design`) and the served module is `leaf_modPA`'s. -/
theorem leaf_childP (O : RefLawsAOps MkRefd mref cref) {dG : MachineData} {G : Name}
    (hG : Tools.ShippingQuadLeafGeneric.LeafData dG)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape) :
    ChildP O G := by
  intro y hy m hm
  have hI := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O dG hG.ok hG.body hG.insts hG.outTy hR0 hcl hy
  have hmod : ModP y.1 := by
    cases hy with
    | run mctx' cctx' w w' adm cache synth quiet hr =>
      exact leaf_modPA O adm dG hG.ok hG.body hG.insts hG.outTy ⟨quiet, synth, rfl⟩ (Or.inr (fun c r h => cache c r h)) hr
        (Tools.ShippingReflectCtx.MachineDefines.ctx hR0) (hcl mctx' cctx')
  rcases List.mem_cons.mp hm with rfl | hm
  · exact hmod
  · rw [hI.design] at hm
    cases hm

end Tools.ShippingSrm17Corr
