import Tools.ShippingPortsMatchRaw
import Tools.ShippingCallWidths
import Tools.ShippingLeafPorts
import Tools.ShippingCoreClk

/-! # `portsMatchB` of the RAW full-entry module, for a parent of LEAF register machines (G1, port matching)

`Tools.ShippingPortsMatchRaw.core_portsMatch_raw` with its three underived
hypotheses (`hkidIn`, `hkidClk`, `hclkB`) and its two output-side hypotheses
(`hkidW`, `hkidT`) DERIVED, for a parent with slots whose calls are all of
machines without calls and with slots (the scope of `parent` and `chained`
of `Tests/Compiler/ShippingMachineSeqTest.lean`: child `cnt`).

* `LeafKid mctx mref cctx cref c dk`: the premises about ONE child
  declaration `c` with data `dk` — its data conditions (decidable), its
  reflection (`MachineDefines`) and its closing (`MachineCloses`, every
  context). No field is about a module.
* `core_portsMatch_raw_leaf`:
  `portsMatchB (childMap D.modules) b = true` for the full entry's module
  `b` before the optimizer, from the parent's core run, its reflection and
  closing, `ChildBnd`, `LeafKid` of every call entry's callee, and data
  conditions:
  - `callWidthsOk d nDecl (fun k => (kid k).shape.layout.outs)` — the
    result side (`Tools/ShippingCallWidths.lean`);
  - `callArgsOk d nDecl (fun k => declWidths (kid k))` — the argument side:
    `kidIns k` IS `declWidths (kid k)`, the widths of the port types of the
    child's declared non-domain binders
    (`Tools/ShippingPortWidthsPure.lean`);
  - `d.shape.layout.slots ≠ []` (the parent has a clock of its own).

Where each former hypothesis comes from:

    hkidW   hkidW_of_data hcw (leaf_real_outTys …)        Tools/ShippingCallWidths.lean
    hkidT   leaf_real_portsIn                              Tools/ShippingLeafTyped.lean
    hkidIn  leaf_real_inWidths                             Tools/ShippingLeafPorts.lean
    hkidClk leaf_real_clk                                  Tools/ShippingLeafPorts.lean
    hclkB   core_clk                                       Tools/ShippingCoreClk.lean

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingPortsMatchRawLeaf
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

/-- **The premises about one leaf child declaration** `c` with data `dk`: a
machine without calls, with slots; its data conditions, its reflection and
its closing. -/
structure LeafKid (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (c : Name)
    (dk : MachineData) : Prop where
  ok : dk.ok = true
  body : dk.shape.body = quote dk.dom
    (fun j => inputExpr dk.shape.binders.length (dk.bpos j))
    (fun j => inputExpr dk.shape.binders.length (dk.vpos j)) dk.packed
  calls : dk.callsOk dk.nIn = true
  dom : ∀ b ∈ dk.shape.binders.drop dk.nIn, b.2 ≠ .domain
  leaf : dk.shape.insts = []
  slots : dk.shape.layout.slots ≠ []
  ss : dk.ss.length = dk.shape.layout.slots.length
  outTy : ∀ o ∈ dk.shape.layout.outs, o.ty.bitWidth = o.width
  outName : ∀ o ∈ dk.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name
  outScalar : ∀ o ∈ dk.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true
  entry : MachineDefines mctx mref cctx cref c dk.shape
  closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
    MachineCloses mctx' mref cctx' cref c dk.shape

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **`portsMatchB` of the RAW full-entry module of a parent of leaf
register machines**: from the runs, the reflections, the closings and data
conditions only. -/
theorem core_portsMatch_raw_leaf {c : Name} (d : MachineData) (ok : d.ok = true)
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
    -- the parent has slots (its own clock and reset)
    (hsl : d.shape.layout.slots ≠ [])
    -- every call entry's callee is a leaf register machine
    (kid : Nat → MachineData)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      LeafKid mctx mref cctx cref (d.shape.insts[k]).1 (kid k))
    -- the two width conditions on the declarations' data
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl
      (fun k => (kid k).shape.layout.outs) = true)
    (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl
      (fun k => Tools.ShippingPortWidthsPure.declWidths (kid k)) = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    Tools.ShippingDesignSV.portsMatchB (childMap D.modules) b = true := by
  -- OUTPUT side: the children's output ports are their layouts' fields
  have hkidO : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingChildIfaceTy.ChildOutTys (kid k).shape.layout.outs y.1 := by
    intro k hk y hy
    have K := hkid k hk
    exact Tools.ShippingChildIfaceTy.leaf_real_outTys (kid k) K.ok K.body K.leaf K.slots K.ss
      K.outTy K.entry K.closes hy
  have hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth :=
    Tools.ShippingCallWidths.hkidW_of_data hcw hkidO
  have hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y → Tools.ShippingLeafTyped.PortsIn y.1 := by
    intro k hk y hy
    have K := hkid k hk
    exact Tools.ShippingLeafTyped.leaf_real_portsIn (nDecl := (kid k).nIn) (kid k) K.ok K.body
      K.calls K.dom K.leaf K.ss K.outTy K.entry K.closes K.outName K.outScalar hy
  -- INPUT side: the children's argument ports, their clock and reset
  have hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingLeafPorts.LeafPorts (d.shape.insts[k]).1 (kid k) y.1 := by
    intro k hk y hy
    have K := hkid k hk
    exact Tools.ShippingLeafPorts.leaf_real_ports (nDecl := (kid k).nIn) (kid k) K.ok K.body
      K.calls K.dom K.leaf K.ss K.outTy K.entry K.closes hy
  have hkidIn : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ (j : Nat) (q : Port), (inPortsOf y.1)[j]? = some q →
        ∃ wd, (Tools.ShippingPortWidthsPure.declWidths (kid k))[j]? = some wd ∧
          Tools.ShippingDesignSV.weS y.1 q.name = wd :=
    fun k hk y hy _ _ hq => (hkidP k hk y hy).inWidths hq
  have hkidClk : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y → isSeqChild y.1 = true →
      Tools.ShippingDesignSV.weS y.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y.1 "rst" = 1 :=
    fun k hk y hy hs => (hkidP k hk y hy).clk hs
  -- the parent's clock and reset
  have hclkB : Tools.ShippingDesignSV.weS b "clk" = 1 ∧ Tools.ShippingDesignSV.weS b "rst" = 1 :=
    Tools.ShippingCoreClk.core_clk d ok hbody hC hslots hdomB hins outTy hnomem hsl hB hcore
      hpost entry closes
  exact Tools.ShippingPortsMatchRaw.core_portsMatch_raw d ok hbody hC hslots hdomB hins hfne
    outTy hnomem hkidW hkidT
    (kidIns := fun k => Tools.ShippingPortWidthsPure.declWidths (kid k)) hargs hkidIn hkidClk
    hB hcore hpost entry closes hon hoty hclkB

end Tools.ShippingPortsMatchRawLeaf
