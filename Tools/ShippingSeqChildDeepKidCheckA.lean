import Tools.ShippingSeqChildDeepFactsA
import Tools.ShippingGenKid
import Tools.ShippingChildMapCongr
-- BUILT (unit SR3p): p1 exit 0; #print axioms: propext, Classical.choice, Quot.sound for both.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.  Witness `O : RefLawsAOps MkRefd mref cref`, `T : RefLawsATele O.quiet mref cref` (ADDED boundary).

/-! # Unit SR3p, step 2 and 3: `kids_designCheck_in` on the new boundary, and `KidFacts.check` for a non-leaf child

* `kids_designCheck_inA` (PROVED): the port of `Tools.ShippingGenKid.kids_designCheck_in` to `MachineRanA O`: `designCheck (childMap ms) n b`
  of the UNOPTIMISED `b` (post-processing of the run's module) against ANY module list `ms` that resolves the modules of the run's
  design to themselves.  Built from `core_runFacts_ranA`, `core_linkedWF_ranA`, `core_closed_typedIn_ranA`, `core_portsMatch_raw_ranA`
  (+ `core_clk_ranA`), `core_kids_facts_ranA`, `core_kids_self_ranA`, and `ChildMapCongr` (`linkedWF_congr`, `noSelfRead_congr`,
  `portsMatchB_congr`) to move from `childMap D.modules` to `childMap ms`.  PREMISES (caller's, per grandchild): `hkidP`, `hkidW`,
  `hkidT`, `hargs`, `hkidIn`, `hkidClk`, and `hkidC` (the grandchild's own `check`, in the form `KidFacts.check`).
* `deepChild_kidCheckA` (PROVED): for `RealChildA O c y` of a machine WITH calls, the `KidFacts.check` field at depth `n + 1`:
  `kidCheck (childMap ms) (n+1) y.1` (the UNOPTIMISED `y.1`, via `kidCheck_succ` and `kids_designCheck_inA`) and
  `kidCheck (childMap ms) (n+1) g` for every module `g` of the served design (via `core_kids_self_ranA` and the grandchild's `hkidC`).
  The unoptimised check is NOT inferred from `designCheck (checkedOptimize y.1)`.

`RealChildA` is a history of past synthesis results, not freshness, not runtime fit. -/

namespace Tools.ShippingSeqChildDeepKidCheckA
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG
open Sparkle.IR.RefineCheck (mergeChecked hierGate)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildBndCore
open Tools.ShippingParentRanA Tools.ShippingParentTailsA Tools.ShippingKidsSelfA
open Tools.ShippingChildMapCongr (AgreeOn)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **`kids_designCheck_in` on the new boundary** (see the header). -/
theorem kids_designCheck_inA (O : RefLawsAOps MkRefd mref cref)
    {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ p ∈ y'.1.outputs, (∀ q ∈ inPortsOf y'.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ p ∈ y'.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    (hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → Tools.ShippingLeafTyped.PortsIn y'.1)
    {kidIns : Nat → List Nat} (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)
    (hkidIn : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ (j : Nat) (q : Port), (inPortsOf y'.1)[j]? = some q →
        ∃ wd, (kidIns k)[j]? = some wd ∧ Tools.ShippingDesignSV.weS y'.1 q.name = wd)
    (hkidClk : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → isSeqChild y'.1 = true →
      Tools.ShippingDesignSV.weS y'.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y'.1 "rst" = 1)
    (n : Nat)
    (hkidC : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → ∀ ms : List Sparkle.IR.AST.Module,
      moduleByName ms y'.1.name = some y'.1 →
      (∀ g ∈ y'.2.modules, moduleByName ms g.name = some g) →
      Tools.ShippingChecksDesign.kidCheck (childMap ms) n y'.1 = true ∧
        ∀ g ∈ y'.2.modules, Tools.ShippingChecksDesign.kidCheck (childMap ms) n g = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (ms : List Sparkle.IR.AST.Module)
    (hms : ∀ g ∈ D.modules, moduleByName ms g.name = some g) :
    Tools.ShippingDesignSV.designCheck (childMap ms) n b = true := by
  have hF : Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
    Tools.ShippingParentRunFactsA.core_runFacts_ranA O d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem
      hkidP hkidW hpost ran
  have hwf := core_linkedWF_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran
  have hT := core_closed_typedIn_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran hon hoty
  have hports : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) b = true :=
    Tools.ShippingParentDesignFA.core_portsMatch_raw_ranA O d ok hbody hC hslots hdomB hins hfne outTy hnomem
      hkidW hkidT hargs hkidIn hkidClk hpost ran hon hoty
      (Tools.ShippingParentDesignFA.core_clk_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hsl hpost ran)
  obtain ⟨-, hbody', -, hresM, -, -⟩ :=
    core_kids_facts_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran
  have hselfD := core_kids_self_ranA O d ok hbody hC hslots hdomB hins hnomem ran
  have hres : ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, moduleByName D.modules mn = some mc ∧ moduleByName ms mn = some mc := by
    intro mn iname conns hm
    rw [hbody'] at hm
    obtain ⟨mc, hmc⟩ := hresM mn iname conns hm
    obtain ⟨hmem, hname⟩ := Tools.ShippingHierPremisesBase.moduleByName_mem hmc
    refine ⟨mc, hmc, ?_⟩
    rw [← hname]
    exact hms mc hmem
  have hag : AgreeOn (childMap ms) (childMap D.modules) b.body := by
    intro mn iname conns hm
    obtain ⟨mc, h1, h2⟩ := hres mn iname conns hm
    simp only [Tools.ShippingMachineLinked.childMap, h1, h2]
  have hCm : ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, mc ∈ D.modules ∧
        childMap ms mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) := by
    intro mn iname conns hm
    obtain ⟨mc, h1, h2⟩ := hres mn iname conns hm
    exact ⟨mc, (Tools.ShippingHierPremisesBase.moduleByName_mem h1).1,
      congrArg (fun o : Option Sparkle.IR.AST.Module =>
        o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) h2⟩
  have hlinked : Tools.ShippingHierOpen.linkedWF (childMap ms) b.body = true := by
    rw [Tools.ShippingChildMapCongr.linkedWF_congr b.body hag]
    exact hwf
  have hself : Tools.ShippingHierPremisesBase.noSelfRead (childMap ms) b.body = true := by
    rw [Tools.ShippingChildMapCongr.noSelfRead_congr hag]
    exact hF.self
  have hportsM : Tools.ShippingDesignSV.portsMatchB (childMap ms) b = true := by
    rw [Tools.ShippingChildMapCongr.portsMatchB_congr hag]
    exact hports
  have hkids : Tools.ShippingDesignSV.kidsPass (childMap ms)
      (Tools.ShippingChecksDesign.kidCheck (childMap ms) n) b.body = true := by
    unfold Tools.ShippingDesignSV.kidsPass
    rw [List.all_eq_true]
    intro st hst
    cases st with
    | inst mn iname conns =>
      obtain ⟨mc, hmem, hc⟩ := hCm mn iname conns hst
      obtain ⟨k, hk, y, hre, hor, hs1, hs2⟩ := hselfD mc hmem
      have hy1 : moduleByName ms y.1.name = some y.1 :=
        hms y.1 (Tools.ShippingHierPremisesBase.moduleByName_mem hs1).1
      have hy2 : ∀ g ∈ y.2.modules, moduleByName ms g.name = some g := fun g hg =>
        hms g (Tools.ShippingHierPremisesBase.moduleByName_mem (hs2 g hg)).1
      have hchk := hkidC k hk y hre ms hy1 hy2
      simp only [hc]
      rcases hor with heq | hin
      · rw [heq]
        exact hchk.1
      · exact hchk.2 mc hin
    | _ => rfl
  rw [Tools.ShippingChecksDesign.designCheck_eq]
  exact Tools.ShippingChecksDepth.and_true_intro
    (Tools.ShippingChecksDesign.textCheckI_of
      (List.all_eq_true.mpr hT.kinds) hT.seqCheck.1 hT.seqCheck.2 hlinked hF.ndB hself hportsM
      (fun mn iname conns hm => by
        obtain ⟨mc, -, hc⟩ := hCm mn iname conns hm
        simp [hc]))
    hkids

set_option maxHeartbeats 4000000 in
/-- **`KidFacts.check` at depth `n + 1` for a non-leaf child** (see the header): the UNOPTIMISED `y.1`, and every module of the
served design, against every module list resolving the served design to itself. -/
theorem deepChild_kidCheckA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ p ∈ y'.1.outputs, (∀ q ∈ inPortsOf y'.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ p ∈ y'.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    (hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → Tools.ShippingLeafTyped.PortsIn y'.1)
    {kidIns : Nat → List Nat} (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)
    (hkidIn : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ (j : Nat) (q : Port), (inPortsOf y'.1)[j]? = some q →
        ∃ wd, (kidIns k)[j]? = some wd ∧ Tools.ShippingDesignSV.weS y'.1 q.name = wd)
    (hkidClk : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → isSeqChild y'.1 = true →
      Tools.ShippingDesignSV.weS y'.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y'.1 "rst" = 1)
    (n : Nat)
    (hkidC : ∀ (m : Nat) (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → ∀ ms : List Sparkle.IR.AST.Module,
      moduleByName ms y'.1.name = some y'.1 →
      (∀ g ∈ y'.2.modules, moduleByName ms g.name = some g) →
      Tools.ShippingChecksDesign.kidCheck (childMap ms) m y'.1 = true ∧
        ∀ g ∈ y'.2.modules, Tools.ShippingChecksDesign.kidCheck (childMap ms) m g = true)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    {y : Res} (h : RealChildA O c y) (ms : List Sparkle.IR.AST.Module)
    (_hy1 : moduleByName ms y.1.name = some y.1)
    (hy2 : ∀ g ∈ y.2.modules, moduleByName ms g.name = some g) :
    Tools.ShippingChecksDesign.kidCheck (childMap ms) (n + 1) y.1 = true ∧
      ∀ g ∈ y.2.modules, Tools.ShippingChecksDesign.kidCheck (childMap ms) (n + 1) g = true := by
  obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ :=
    Tools.ShippingSeqChildDeepFactsA.deepChild_ranA O T d ok hbody hC hslots hdomB hins outTy hnomem hsep entry closes h
  have hmsD : ∀ g ∈ D.modules, moduleByName ms g.name = some g := fun g hg =>
    hy2 g (by rw [hdes]; exact hg)
  refine ⟨?_, ?_⟩
  · exact (Tools.ShippingGenKid.kidCheck_succ (childMap ms) n y.1).trans
      (kids_designCheck_inA O d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem hkidP hkidW hkidT hargs hkidIn
        hkidClk n (fun k hk y' hre => hkidC n k hk y' hre) hpost ran hon hoty ms hmsD)
  · intro g hg
    rw [hdes] at hg
    obtain ⟨k, hk, y', hre, hor, hs1, hs2⟩ := core_kids_self_ranA O d ok hbody hC hslots hdomB hins hnomem ran g hg
    have hz1 : moduleByName ms y'.1.name = some y'.1 :=
      hmsD y'.1 (Tools.ShippingHierPremisesBase.moduleByName_mem hs1).1
    have hz2 : ∀ g2 ∈ y'.2.modules, moduleByName ms g2.name = some g2 := fun g2 hg2 =>
      hmsD g2 (Tools.ShippingHierPremisesBase.moduleByName_mem (hs2 g2 hg2)).1
    have hchk := hkidC (n + 1) k hk y' hre ms hz1 hz2
    rcases hor with heq | hin
    · rw [heq]
      exact hchk.1
    · exact hchk.2 g hin

end Tools.ShippingSeqChildDeepKidCheckA

#print axioms Tools.ShippingSeqChildDeepKidCheckA.kids_designCheck_inA
#print axioms Tools.ShippingSeqChildDeepKidCheckA.deepChild_kidCheckA
