import Tools.ShippingSeqChildDeepKidCheckA
import Tools.ShippingSrm4Parent
import Tools.ShippingSrm5Height
import Tools.ShippingSrm5Ident
-- UNBUILT (unit SRM5)
-- SCOPE (binding): the HEIGHT-INDEXED transfer of `kids_designCheck_inA` (`Tools/ShippingSeqChildDeepKidCheckA.lean`) and of the parent's `designCheck` block (`kidsNC_designCheck_of_kidsPass`, `Tools/ShippingSrm4Parent.lean`).
-- * `kids_textCheck_inA`: the text-check half of `kids_designCheck_inA`, a SCRIPTED copy (the `hkids` block and the `n`/`hkidC` hypotheses deleted, conclusion `textCheckI`); nothing else changed.
-- * `kidsH_body_ranA`: every instance statement of the run's module passes `instOkH` at the rank table `rk`: the statement's target is IDENTIFIED BY NAME with the kid's own module `y.1` (`Tools/ShippingSrm5Ident.lean`), which is checked at ITS rank
--   (`hkidH`, the per-kid HEIGHT fact: the kid's own module only, NOT its served design); the rank bound `hrank` is a NAMED PREMISE (the existence of a rank table is not derived).
-- * `kids_hcheck_inA`: `kids_designCheck_inA` with the uniform `kidCheck` replaced by `hcheck`; `kidsNC_hcheck`: the parent block, `hkids` DISCHARGED by `hrank`/`hkidH`.
-- PREMISES kept (named): `hrb` (the module's own rank is `h + 1`), `hrank` (every kid's rank is ≤ h), `hkidH` (each kid's height check at fuel `f`), `ms`-resolution `hms`, and the old ones of the originals.  `RealChildA` is a history of past
-- synthesis results, not freshness or runtime fit.  Nothing here says a rank table exists for a given design.
-- No `sorry`, no `axiom`, no `native_decide`, no heartbeat option.

namespace Tools.ShippingSrm5Transfer
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG
open Sparkle.IR.RefineCheck (mergeChecked hierGate)
open Sparkle.IR.OptCheck (checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildBndCore
open Tools.ShippingParentRanA Tools.ShippingParentTailsA Tools.ShippingKidsSelfA
open Tools.ShippingChildMapCongr (AgreeOn)
open Tools.ShippingSrm5Height

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The text-check half of `kids_designCheck_inA`** (scripted copy: the children's check and its depth deleted). -/
theorem kids_textCheck_inA (O : RefLawsAOps MkRefd mref cref)
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
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (ms : List Sparkle.IR.AST.Module)
    (hms : ∀ g ∈ D.modules, moduleByName ms g.name = some g) :
    Tools.ShippingDesignSV.textCheckI (childMap ms) b = true := by
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
  exact Tools.ShippingChecksDesign.textCheckI_of
    (List.all_eq_true.mpr hT.kinds) hT.seqCheck.1 hT.seqCheck.2 hlinked hF.ndB hself hportsM
    (fun mn iname conns hm => by
      obtain ⟨mc, -, hc⟩ := hCm mn iname conns hm
      simp [hc])


/-- **Every instance statement of the run's module passes the height check of one statement** (`instOkH`): its target is identified BY NAME with the kid's own module `y.1`
(`inst_target_ord_ranA`), that module resolves in `ms`, has a rank `r ≤ h` (`hrank`), and is checked at ITS rank (`hkidH`).  `hmsD`: `ms` resolves every module `D` resolves as itself. -/
theorem kidsH_body_ranA (O : RefLawsAOps MkRefd mref cref)
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    (rk : String → Option Nat) (h f : Nat)
    (hrank : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → ∃ r, rk y'.1.name = some r ∧ r ≤ h)
    (hkidH : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → ∀ ms : List Sparkle.IR.AST.Module,
      moduleByName ms y'.1.name = some y'.1 →
      (∀ g ∈ y'.2.modules, moduleByName ms g.name = some g) →
      hcheck (childMap ms) rk f y'.1 = true)
    (ms : List Sparkle.IR.AST.Module)
    (hmsD : ∀ g : Sparkle.IR.AST.Module, moduleByName D.modules g.name = some g → moduleByName ms g.name = some g) :
    b.body.all (instOkH (childMap ms) rk (hcheck (childMap ms) rk f) h) = true := by
  obtain ⟨-, hbody', -, -, -, -⟩ :=
    core_kids_facts_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran
  rw [List.all_eq_true]
  intro st hst
  cases st with
  | inst mn iname conns =>
    obtain ⟨k, hk, y, hre, hmn, hres, hres2⟩ :=
      Tools.ShippingSrm5Ident.inst_target_ord_ranA O d ok hbody hC hslots hdomB hnomem ran mn iname conns
        (hbody' ▸ hst)
    subst hmn
    have hy1 : moduleByName ms y.1.name = some y.1 := hmsD y.1 hres
    have hy2 : ∀ g ∈ y.2.modules, moduleByName ms g.name = some g := fun g hg => hmsD g (hres2 g hg)
    obtain ⟨r, hr1, hr2⟩ := hrank k hk y hre
    have hCm : childMap ms y.1.name = some (y.1, Sparkle.IR.RegDedup.declWidth y.1) := by
      simp only [Tools.ShippingMachineLinked.childMap, hy1, Option.map_some]
    exact instOkH_inst.mpr ⟨y.1, _, r, hCm, hr1, hr2, rfl, hkidH k hk y hre ms hy1 hy2⟩
  | _ => rfl

/-- **`kids_designCheck_inA`, height-indexed**: the check of the UNOPTIMISED `b` at its rank `h + 1`, against any `ms` resolving the run's design.
The text half is `kids_textCheck_inA`; the children's half is `kidsH_body_ranA`.  PREMISES beyond the text half's: `hrb`, `hrank`, `hkidH`. -/
theorem kids_hcheck_inA (O : RefLawsAOps MkRefd mref cref)
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
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (ms : List Sparkle.IR.AST.Module)
    (hms : ∀ g ∈ D.modules, moduleByName ms g.name = some g)
    (rk : String → Option Nat) (h f : Nat) (hrb : rk b.name = some (h + 1))
    (hrank : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → ∃ r, rk y'.1.name = some r ∧ r ≤ h)
    (hkidH : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → ∀ ms : List Sparkle.IR.AST.Module,
      moduleByName ms y'.1.name = some y'.1 →
      (∀ g ∈ y'.2.modules, moduleByName ms g.name = some g) →
      hcheck (childMap ms) rk f y'.1 = true) :
    hcheck (childMap ms) rk (f + 1) b = true := by
  rw [hcheck_succ hrb f]
  exact Tools.ShippingChecksDepth.and_true_intro
    (kids_textCheck_inA O d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem hkidP hkidW hkidT hargs hkidIn
      hkidClk hpost ran hon hoty ms hms)
    (kidsH_body_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran rk h f hrank hkidH ms
      (fun g hg => hms g (Tools.ShippingHierPremisesBase.moduleByName_mem hg).1))

end Tools.ShippingSrm5Transfer

#print axioms Tools.ShippingSrm5Transfer.kids_textCheck_inA
#print axioms Tools.ShippingSrm5Transfer.kidsH_body_ranA
#print axioms Tools.ShippingSrm5Transfer.kids_hcheck_inA
