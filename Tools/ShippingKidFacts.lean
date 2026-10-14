import Tools.ShippingKidsSelf
import Tools.ShippingCallWidths
import Tools.ShippingChecksCoreGate
import Tools.ShippingChecksRunFacts
import Tools.ShippingTextShipped
import Tools.ShippingPortsMatchShipped
import Tools.ShippingCoreClk
import Tools.ShippingLeafTyped
import Tools.ShippingMachineRanBase

/-! # What the no-ports chain takes of ONE callee, without "leaf" (G1, unit U2, round par/a-13)

The depth chain `#machine_no_ports` (`Tools/ShippingNoPortsCommand.lean`)
discharges the four run hypotheses of the head
`Tools.ShippingNoPorts.machine_design_noPorts` with general theorems whose
per-child hypotheses it fills by `leaf_real_*` lemmas — each asks
`dk.shape.insts = []` (`LeafKid.leaf`). This file states those per-child
hypotheses as ONE interface over the real children of a callee, with no
field about the callee's shape, and proves the four run hypotheses from it:

* `KidFacts mref cref c outs ins n`: for EVERY `y` with
  `RealChild mref cref c y` —
  - `outsIn`  (`hkidP` of `core_runFacts`, `core_designCheck_run`);
  - `outTys`  (`ChildOutTys outs y.1`, for `hkidW_of_data`);
  - `kidA`, `kidR` (`core_outsCheck_all_gate`);
  - `masked`  (`outsMaskedN y.1` — of the child's OWN module only:
    `core_kidsMaskedN_top`);
  - `portsIn`, `inW`, `clk` (`hkidT`, `hkidIn`, `hkidClk` of
    `core_portsMatch_raw`; `ins` is the callee's argument widths, the data
    the parent's `callArgsOk` is decided against);
  - `check`: the children's check at depth `n` in the form that is TRUE of
    a child with instances — against any module list that resolves the
    child's module and the modules of its design to themselves
    (`core_kidsPass_deep`). The leaf form `∀ C n, kidCheck C n y.1 = true`
    is false for a module with instances.
* `kids_runFacts`, `kids_outsCheck`, `kids_maskedN`, `kids_designCheck`:
  `RunFacts`, `outsCheck … n`, `kidsMaskedN`, `designCheck … n` of the
  parent's core run, from `KidFacts` of every call entry's callee and the
  parent's data conditions (`callWidthsOk`, `callArgsOk`, the output names
  and types). `kids_designCheck` has NO check premise: `portsMatchB` by
  `core_portsMatch_raw` + `core_clk` + `portsMatchB_shipped`, the
  children's check by `core_kidsPass_deep`.

SCOPE: a parent WITH a register (`hsl`) tied by the GENERAL closing
(`hfne`), no memory callee. Which callees have `KidFacts` is a separate
question: `Tools/ShippingOneOutKid.lean` gives it at `n = 1` for a callee
with a register and one-output calls of its own; a LEAF register machine
has it at every `n` by the `leaf_real_*` lemmas (not restated here).

No new fact about the compiler is proved in this file: the four theorems
are applications of BUILT general theorems and of
`Tools/ShippingKidsSelf.lean`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingKidFacts
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

/-- **What a parent's check-free depth chain takes of one callee `c`**: facts
of every real child of `c`. `outs`: the callee's layout outputs; `ins`: the
widths of its argument ports; `n`: the parent's depth. -/
structure KidFacts (mref : ST.Ref IO.RealWorld Meta.State)
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
      Tools.ShippingChecksDesign.kidCheck (childMap ms) n y.1 = true ∧
        ∀ g ∈ y.2.modules, Tools.ShippingChecksDesign.kidCheck (childMap ms) n g = true

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `kids_runFacts` over `MachineRan`:
the proof of the built theorem, MOVED here (split in place, branch
`fix/ran-threading-split`) with the run, the reflection, the closing and the boundary
replaced by `ran` and every callee of the chain by its `_ran` form. It takes of the run only
that the machine synthesis this core run performed returned the result from an invariant
world; the theorem below, its statement unchanged, is the instance at the all-worlds closing
(`Tools.ShippingMachineRan.machineRan_of_closes`). -/
theorem kids_runFacts_ran {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  Tools.ShippingChecksRunFacts.core_runFacts_ran d ok hbody hC hslots hdomB hins hsl hfne outTy
    hnomem
    (fun k hk y hy => (hkid k hk).outsIn y hy)
    (Tools.ShippingCallWidths.hkidW_of_data hcw (fun k hk y hy => (hkid k hk).outTys y hy))
    hpost ran

/-- **The run's facts of the full entry's module**, from `KidFacts` of every
call entry's callee (`core_runFacts`). -/
theorem kids_runFacts {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  kids_runFacts_ran d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem kidOuts kidIns n hkid hcw
    hpost (Tools.ShippingMachineRan.machineRan_of_closes hcore entry hB closes)

/-- `kids_outsCheck` over `MachineRan`:
the proof of the built theorem, MOVED here (split in place, branch
`fix/ran-threading-split`) with the run, the reflection, the closing and the boundary
replaced by `ran` and every callee of the chain by its `_ran` form. It takes of the run only
that the machine synthesis this core run performed returned the result from an invariant
world; the theorem below, its statement unchanged, is the instance at the all-worlds closing
(`Tools.ShippingMachineRan.machineRan_of_closes`). -/
theorem kids_outsCheck_ran {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true :=
  Tools.ShippingChecksCoreGate.core_outsCheck_all_gate_ran d ok hbody hC hslots hdomB hins outTy
    hnomem
    (fun k hk y hy => (hkid k hk).kidA y hy)
    (fun k hk y hy => (hkid k hk).kidR y hy)
    hpost ran hg n

/-- **The output check at depth `n`, under the statement-kind gate**, from
`KidFacts` (`core_outsCheck_all_gate`). -/
theorem kids_outsCheck {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true :=
  kids_outsCheck_ran d ok hbody hC hslots hdomB hins outTy hnomem kidOuts kidIns n hkid hpost
    (Tools.ShippingMachineRan.machineRan_of_closes hcore entry hB closes) hg

/-- `kids_maskedN` over `MachineRan`:
the proof of the built theorem, MOVED here (split in place, branch
`fix/ran-threading-split`) with the run, the reflection, the closing and the boundary
replaced by `ran` and every callee of the chain by its `_ran` form. It takes of the run only
that the machine synthesis this core run performed returned the result from an invariant
world; the theorem below, its statement unchanged, is the instance at the all-worlds closing
(`Tools.ShippingMachineRan.machineRan_of_closes`). -/
theorem kids_maskedN_ran {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingKidsSelf.core_kidsMaskedN_top_ran d ok hbody hC hslots hdomB hins hfne outTy hnomem
    (fun k hk y hy => (hkid k hk).masked y hy)
    hpost ran

/-- **The children's masked outputs**, from `KidFacts`
(`core_kidsMaskedN_top`). -/
theorem kids_maskedN {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  kids_maskedN_ran d ok hbody hC hslots hdomB hins hfne outTy hnomem kidOuts kidIns n hkid hpost
    (Tools.ShippingMachineRan.machineRan_of_closes hcore entry hB closes)

set_option maxHeartbeats 4000000 in
/-- `kids_designCheck` over `MachineRan`:
the proof of the built theorem, MOVED here (split in place, branch
`fix/ran-threading-split`) with the run, the reflection, the closing and the boundary
replaced by `ran` and every callee of the chain by its `_ran` form. It takes of the run only
that the machine synthesis this core run performed returned the result from an invariant
world; the theorem below, its statement unchanged, is the instance at the all-worlds closing
(`Tools.ShippingMachineRan.machineRan_of_closes`). -/
theorem kids_designCheck_ran {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) n (checkedOptimize b) = true := by
  have hkidW := Tools.ShippingCallWidths.hkidW_of_data hcw
    (fun k hk y hy => (hkid k hk).outTys y hy)
  have hraw : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) b = true :=
    Tools.ShippingPortsMatchRaw.core_portsMatch_raw_ran d ok hbody hC hslots hdomB hins hfne outTy
      hnomem hkidW
      (fun k hk y hy => (hkid k hk).portsIn y hy)
      (kidIns := kidIns) hargs
      (fun k hk y hy j q hq => (hkid k hk).inW y hy j q hq)
      (fun k hk y hy hs => (hkid k hk).clk y hy hs)
      hpost ran hon hoty
      (Tools.ShippingCoreClk.core_clk_ran d ok hbody hC hslots hdomB hins outTy hnomem hsl hpost ran)
  have hports : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) (checkedOptimize b) =
      true :=
    Tools.ShippingPortsMatchShipped.portsMatchB_shipped
      (Tools.ShippingChecksWidths.core_hierGate_ran d ok hbody hC hslots hdomB hins hfne outTy
        hnomem hpost ran)
      hraw
  have hkids := Tools.ShippingKidsSelf.core_kidsPass_deep_ran d ok hbody hC hslots hdomB hins hfne
    outTy hnomem n
    (fun k hk y hy ms h1 h2 => (hkid k hk).check y hy ms h1 h2)
    hpost ran
  exact Tools.ShippingTextShipped.core_designCheck_run_ran d ok hbody hC hslots hdomB hins hsl hfne
    outTy hnomem
    (fun k hk y hy => (hkid k hk).outsIn y hy)
    hkidW hpost ran hon hoty n hports hkids

set_option maxHeartbeats 4000000 in
/-- **`designCheck` of the shipped module at depth `n` with NO check
premise**, from `KidFacts`: the connection widths by `core_portsMatch_raw`
(with the parent's `clk` / `rst` by `core_clk`) through the optimizer
(`portsMatchB_shipped`), the children's check by `core_kidsPass_deep`. -/
theorem kids_designCheck {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) n (checkedOptimize b) = true :=
  kids_designCheck_ran d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem kidOuts kidIns n hkid
    hcw hargs hpost (Tools.ShippingMachineRan.machineRan_of_closes hcore entry hB closes) hon hoty

end Tools.ShippingKidFacts
