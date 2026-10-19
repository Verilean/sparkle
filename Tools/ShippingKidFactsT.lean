import Tools.ShippingKidFacts
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md).

/-! # The no-ports chain's interface of ONE callee, with the check of the callee's OWN module only (round par/c-4)

WRITTEN, NOT BUILT.

`Tools.ShippingKidFacts.KidFacts … c … n` asks, in its field `check`,
`kidCheck C n` of the callee's module AND of every module of its design, at
the SAME depth index `n`. For a callee whose design contains a memory module
(`memCounterH`: a register machine with one memory read) that field is FALSE
at every `n ≥ 1`: `kidCheck C (m + 1) g = designCheck C m g` asks `textCheckI
C g`, whose first conjunct `g.body.all seqStmtOkI` rejects a memory
statement (`Tools/ShippingDesignSV.lean` 103–124,
`Tools/ShippingHierSVSoundness.lean` 30–34); a memory module passes
`leafCheck` only, i.e. at depth index 0 below its own parent. `KidFactsM`
(`Tools/ShippingMemKidFacts.lean` 423–449) has the same field.

The uniform second conjunct is consumed in ONE place of the parent's chain,
`Tools.ShippingKidsSelf.core_kidsPass_deep`, for the case "an instance of
the parent resolves to a module of some child's DESIGN" — which does not
occur under the general closing when the names are separated: every
instance resolves to a real child's OWN module
(`Tools.ShippingPortsMatchRaw.core_callConns`, the fact
`core_kidsMaskedN_top` already uses), whose name is the callee's printed
name, and that is not a name below a child.

* `KidFactsT`: `KidFacts` with `check` about the callee's own module only.
  `KidFacts.toT`.
* `core_kidsPass_top`: the children's check from the own-module checks, the
  children's names (`hname`) and the separation (`hsep`).
* `kidsT_runFacts`, `kidsT_outsCheck`, `kidsT_maskedN`, `kidsT_designCheck`:
  the four parent-side theorems of `Tools/ShippingKidFacts.lean` over
  `KidFactsT` (their proofs, copied from the built file's lines 104–251; only
  `kidsT_designCheck` changes: `core_kidsPass_top` with the names).

SCOPE, as the built theorems: a parent WITH a register under the general
closing, NO memory entry of its own (`hnomem`) — its children may have
memories below them. -/
namespace Tools.ShippingKidFactsT
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
open Tools.ShippingKidFacts (KidFacts)

/-- **What a parent's check-free depth chain takes of one callee `c`, the
check asked of the callee's own module only.** -/
structure KidFactsT (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) (c : Name) (outs : List OutField)
    (ins : List Nat) (n : Nat) : Prop where
  outsIn : ∀ (y : Res), RealChild mref cref c y →
    ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
      p.name ≠ "rst"
  outTys : ∀ (y : Res), RealChild mref cref c y →
    Tools.ShippingChildIfaceTy.ChildOutTys outs y.1
  kidA : ∀ (y : Res), RealChild mref cref c y →
    Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
      ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true
  kidR : ∀ (y : Res), RealChild mref cref c y →
    ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
      ∃ g2 ∈ y.2.modules, g2.name = mn
  masked : ∀ (y : Res), RealChild mref cref c y →
    Tools.ShippingMachineShipsDepth.outsMaskedN y.1 = true
  portsIn : ∀ (y : Res), RealChild mref cref c y → Tools.ShippingLeafTyped.PortsIn y.1
  inW : ∀ (y : Res), RealChild mref cref c y →
    ∀ (j : Nat) (q : Port), (inPortsOf y.1)[j]? = some q →
      ∃ wd, ins[j]? = some wd ∧ Tools.ShippingDesignSV.weS y.1 q.name = wd
  clk : ∀ (y : Res), RealChild mref cref c y → isSeqChild y.1 = true →
    Tools.ShippingDesignSV.weS y.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y.1 "rst" = 1
  check : ∀ (y : Res), RealChild mref cref c y →
    ∀ ms : List Sparkle.IR.AST.Module,
      moduleByName ms y.1.name = some y.1 →
      (∀ g ∈ y.2.modules, moduleByName ms g.name = some g) →
      Tools.ShippingChecksDesign.kidCheck (childMap ms) n y.1 = true

theorem _root_.Tools.ShippingKidFacts.KidFacts.toT {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} {c : Name} {outs : List OutField} {ins : List Nat}
    {n : Nat} (h : KidFacts mref cref c outs ins n) : KidFactsT mref cref c outs ins n :=
  { outsIn := h.outsIn
    outTys := h.outTys
    kidA := h.kidA
    kidR := h.kidR
    masked := h.masked
    portsIn := h.portsIn
    inW := h.inW
    clk := h.clk
    check := fun y hy ms h1 h2 => (h.check y hy ms h1 h2).1 }

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **The children's check of the shipped module, at depth `n`, from the
check of each real child's OWN module only** (`core_kidsPass_deep` without
the check of the modules of the child's design): every instance of the
general closing's module resolves to a real child's own module
(`core_callConns`), and that module is not a module of another child's
design when no child's printed name is a name below a child (`hsep`). -/
theorem core_kidsPass_top {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (n : Nat)
    (hkidK : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ ms : List Sparkle.IR.AST.Module,
        moduleByName ms y.1.name = some y.1 →
        (∀ g ∈ y.2.modules, moduleByName ms g.name = some g) →
        Tools.ShippingChecksDesign.kidCheck (childMap ms) n y.1 = true)
    (namesK : Nat → List String)
    (hname : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      y.1.name = Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1 ∧
        ∀ g ∈ y.2.modules, g.name ∈ namesK k)
    (hsep : ∀ (k : Nat) (_ : k < d.shape.insts.length) (k' : Nat)
      (_ : k' < d.shape.insts.length),
      Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1 ∉ namesK k')
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingDesignSV.kidsPass (childMap D.modules)
      (Tools.ShippingChecksDesign.kidCheck (childMap D.modules) n)
      (checkedOptimize b).body = true := by
  obtain ⟨-, hbody', -, hresM, -, -⟩ :=
    Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes
  have hselfD := Tools.ShippingKidsSelf.core_kids_self d ok hbody hC hslots hdomB hins hnomem hB hcore entry closes
  have hgate : Sparkle.IR.RefineCheck.hierGate b = true :=
    Tools.ShippingChecksWidths.core_hierGate d ok hbody hC hslots hdomB hins hfne outTy hnomem
      hB hcore hpost entry closes
  have hconn := Tools.ShippingPortsMatchRaw.core_callConns d ok hbody hC hslots hdomB hins hfne
    outTy hnomem hB hcore hpost entry closes
  unfold Tools.ShippingDesignSV.kidsPass
  rw [List.all_eq_true]
  intro st hst
  cases st with
  | inst mn iname conns =>
    have hm : Stmt.inst mn iname conns ∈ b.body :=
      (Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate hgate mn iname conns).mp hst
    obtain ⟨mc2, hmc2, ⟨k2, hk2, y2, hre2, e2⟩, -⟩ := hconn mn iname conns hm
    rw [hbody'] at hm
    obtain ⟨mc, hmc⟩ := hresM mn iname conns hm
    have hmem : mc ∈ D.modules := (Tools.ShippingHierPremisesBase.moduleByName_mem hmc).1
    obtain ⟨k, hk, y, hre, hor, hs1, hs2⟩ := hselfD mc hmem
    have hCm : childMap D.modules mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) :=
      congrArg (fun o : Option Sparkle.IR.AST.Module =>
        o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hmc
    simp only [hCm]
    rcases hor with heq | hin
    · rw [heq]
      exact hkidK k hk y hre D.modules hs1 hs2
    · -- the instance's module is a real child's OWN module: not below a child
      exfalso
      have e : mc2 = mc := Option.some.inj (hmc2.symm.trans hmc)
      have h1 : mc.name = Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k2]).1 := by
        rw [← e, e2]
        exact (hname k2 hk2 y2 hre2).1
      have h2 : mc.name ∈ namesK k := (hname k hk y hre).2 mc hin
      rw [h1] at h2
      exact hsep k2 hk2 k hk h2
  | _ => rfl

/-- **The run's facts of the full entry's module**, from `KidFactsT` of every
call entry's callee (`core_runFacts`). -/
theorem kidsT_runFacts {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsT mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  Tools.ShippingChecksRunFacts.core_runFacts d ok hbody hC hslots hdomB hins hsl hfne outTy
    hnomem
    (fun k hk y hy => (hkid k hk).outsIn y hy)
    (Tools.ShippingCallWidths.hkidW_of_data hcw (fun k hk y hy => (hkid k hk).outTys y hy))
    hB hcore hpost entry closes

/-- **The output check at depth `n`, under the statement-kind gate**, from
`KidFactsT` (`core_outsCheck_all_gate`). -/
theorem kidsT_outsCheck {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsT mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true :=
  Tools.ShippingChecksCoreGate.core_outsCheck_all_gate d ok hbody hC hslots hdomB hins outTy
    hnomem
    (fun k hk y hy => (hkid k hk).kidA y hy)
    (fun k hk y hy => (hkid k hk).kidR y hy)
    hB hcore hpost entry closes hg n

/-- **The children's masked outputs**, from `KidFactsT`
(`core_kidsMaskedN_top`). -/
theorem kidsT_maskedN {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsT mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingKidsSelf.core_kidsMaskedN_top d ok hbody hC hslots hdomB hins hfne outTy hnomem
    (fun k hk y hy => (hkid k hk).masked y hy)
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
/-- **`designCheck` of the shipped module at depth `n` with NO check
premise**, from `KidFactsT`: the connection widths by `core_portsMatch_raw`
(with the parent's `clk` / `rst` by `core_clk`) through the optimizer
(`portsMatchB_shipped`), the children's check by `core_kidsPass_top` (the
own-module checks, the children's names and their separation). -/
theorem kidsT_designCheck {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsT mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)
    (namesK : Nat → List String)
    (hname : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      y.1.name = Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1 ∧
        ∀ g ∈ y.2.modules, g.name ∈ namesK k)
    (hsep : ∀ (k : Nat) (_ : k < d.shape.insts.length) (k' : Nat)
      (_ : k' < d.shape.insts.length),
      Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1 ∉ namesK k')
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) n (checkedOptimize b) = true := by
  have hkidW := Tools.ShippingCallWidths.hkidW_of_data hcw
    (fun k hk y hy => (hkid k hk).outTys y hy)
  have hraw : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) b = true :=
    Tools.ShippingPortsMatchRaw.core_portsMatch_raw d ok hbody hC hslots hdomB hins hfne outTy
      hnomem hkidW
      (fun k hk y hy => (hkid k hk).portsIn y hy)
      (kidIns := kidIns) hargs
      (fun k hk y hy j q hq => (hkid k hk).inW y hy j q hq)
      (fun k hk y hy hs => (hkid k hk).clk y hy hs)
      hB hcore hpost entry closes hon hoty
      (Tools.ShippingCoreClk.core_clk d ok hbody hC hslots hdomB hins outTy hnomem hsl hB hcore
        hpost entry closes)
  have hports : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) (checkedOptimize b) =
      true :=
    Tools.ShippingPortsMatchShipped.portsMatchB_shipped
      (Tools.ShippingChecksWidths.core_hierGate d ok hbody hC hslots hdomB hins hfne outTy
        hnomem hB hcore hpost entry closes)
      hraw
  have hkids := core_kidsPass_top d ok hbody hC hslots hdomB hins hfne
    outTy hnomem n
    (fun k hk y hy ms h1 h2 => (hkid k hk).check y hy ms h1 h2)
    namesK hname hsep
    hB hcore hpost entry closes
  exact Tools.ShippingTextShipped.core_designCheck_run d ok hbody hC hslots hdomB hins hsl hfne
    outTy hnomem
    (fun k hk y hy => (hkid k hk).outsIn y hy)
    hkidW hB hcore hpost entry closes hon hoty n hports hkids

end Tools.ShippingKidFactsT
