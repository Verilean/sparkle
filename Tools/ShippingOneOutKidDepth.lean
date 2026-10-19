import Tools.ShippingOneOutKid
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

/-! # `OneOutKid` at every depth (G1, unit U3, round par/a-15)

`Tools.ShippingOneOutKid.OneOutKid.facts` gives `KidFacts … 1` for a callee
with a register and one-output calls of its own (`midH → rcH`). A callee
under the GENERAL closing whose callee is such a machine (`mid2 → midH`,
below `topD2`) needs `KidFacts` of `midH` at TWO depths
(`Tools.ShippingGenKid.GenKid.kidsLo` / `kidsHi`: 1 and 2). This file gives
`OneOutKid.factsN : KidFacts … (n + 1)` for every `n`.

Only the `check` field depends on the depth: `designCheck (childMap ms) n`
of the served module. The grandchildren of a `OneOutKid` are asked in the
LEAF form (`kidK : ∀ C n, kidCheck C n y.1 = true`), so the proof of
`core_designCheck_in₁` goes through with `n` for `0`
(`core_designCheck_inN₁`: that proof, copied; if it changes, this copy does
not follow). The other fields are `OneOutKid.facts`'s.

No new fact about the compiler is proved here.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingOneOutKidDepth
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingChildMapCongr (AgreeOn)
open Tools.ShippingCallsChildPorts (CallsPorts argWidths)
open Tools.ShippingOneOutKid (OneOutKid)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at EVERY depth `n` of the UNOPTIMISED full-entry module
of a machine with a register and one-output calls, against ANY module list
that resolves the modules of the run's design to themselves.**
`Tools.ShippingOneOutKid.core_designCheck_in₁` is this statement at
`n = 0`; the proof is the same (the children's check is asked in the leaf
form `hkidK`, which holds at every child map and depth). -/
theorem core_designCheck_inN₁ {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hsl : d.shape.layout.slots ≠ [])
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (hkidK : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
        ∀ g ∈ y.2.modules,
          ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
            Tools.ShippingChecksDesign.kidCheck C n g = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hports : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) b = true)
    (n : Nat) (ms : List Sparkle.IR.AST.Module)
    (hms : ∀ g ∈ D.modules, moduleByName ms g.name = some g) :
    Tools.ShippingDesignSV.designCheck (childMap ms) n b = true := by
  have hF := Tools.ShippingOneOutFacts.core_runFactsH d ok hbody hC hslots hdomB hins hf outTy
    hnomem hB hcore hpost entry closes hsl
  have hwf := Tools.ShippingLinkedFresh.core_linkedWF d ok hbody hC hslots hdomB hins outTy
    hnomem hB hcore hpost entry closes
  have hT := Tools.ShippingClosedTyped.core_closed_typedIn d ok hbody hC hslots hdomB hins outTy
    hnomem hB hcore hpost entry closes hon hoty
  obtain ⟨-, hbody', -, hresM, hrealD, -⟩ :=
    Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes
  -- an instance of `b` resolves, in both module lists, to the same module
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
      obtain ⟨k, hk, y, hre, hor, -⟩ := hrealD mc hmem
      simp only [hc]
      rcases hor with heq | hin
      · rw [heq]
        exact (hkidK k hk y hre).1 _ n
      · exact (hkidK k hk y hre).2 mc hin _ n
    | _ => rfl
  rw [Tools.ShippingChecksDesign.designCheck_eq]
  exact Tools.ShippingChecksDepth.and_true_intro
    (Tools.ShippingChecksDesign.textCheckI_of
      (List.all_eq_true.mpr hT.kinds) hT.seqCheck.1 hT.seqCheck.2 hlinked hF.ndB hself hportsM
      (fun mn iname conns hm => by
        obtain ⟨mc, -, hc⟩ := hCm mn iname conns hm
        simp [hc]))
    hkids

variable {c : Name} {dk : MachineData} {nDecl : Nat} {namesK : Nat → List String}

set_option maxHeartbeats 4000000 in
/-- **The check of the served module at depth `n`**, against every module
list that resolves the modules of the served design to themselves, and the
leaf form for the modules of the served design (`OneOutKid.check` with `n`
for `0`). -/
theorem checkN (K : OneOutKid mref cref c dk nDecl namesK) {y : Res}
    (hy : RealChild mref cref c y) (n : Nat) (ms : List Sparkle.IR.AST.Module)
    (hms : ∀ g ∈ y.2.modules, moduleByName ms g.name = some g) :
    Tools.ShippingDesignSV.designCheck (childMap ms) n y.1 = true ∧
      ∀ g ∈ y.2.modules,
        ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (m : Nat),
          Tools.ShippingChecksDesign.kidCheck C m g = true := by
  obtain ⟨mctx', cctx', w, w1, M, D, hB, hcore, hpost, hdes⟩ := K.core hy
  have entry := K.entry mctx' cctx'
  have closes : MachineClosesAt mctx' mref cctx' cref c dk.shape := K.closes mctx' cctx'
  refine ⟨?_, (K.check hy ms hms).2⟩
  exact core_designCheck_inN₁ dk K.ok K.body K.calls K.ss K.dom K.insts K.oneOut K.outTy
    K.nomem K.slots K.outName K.outScalar K.kidK hB hcore hpost entry closes
    (K.portsRaw mctx' cctx' w w1 M y.1 D hB hcore hpost) n ms
    (fun g hg => hms g (by rw [hdes]; exact hg))

/-- **`KidFacts` of a callee with a register and one-output calls of its
own, at every depth `n + 1`.** -/
theorem factsN (K : OneOutKid mref cref c dk nDecl namesK) (n : Nat) :
    Tools.ShippingKidFacts.KidFacts mref cref c dk.shape.layout.outs (argWidths dk nDecl)
      (n + 1) :=
  { outsIn := K.facts.outsIn
    outTys := K.facts.outTys
    kidA := K.facts.kidA
    kidR := K.facts.kidR
    masked := K.facts.masked
    portsIn := K.facts.portsIn
    inW := K.facts.inW
    clk := K.facts.clk
    check := fun y hy ms _ h2 => by
      obtain ⟨h0, hg⟩ := checkN K hy n ms h2
      exact ⟨(Tools.ShippingOneOutKid.kidCheck_succ (childMap ms) n y.1).trans h0,
        fun g hgm => hg g hgm _ (n + 1)⟩ }

end Tools.ShippingOneOutKidDepth
