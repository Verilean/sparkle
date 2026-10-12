import Tools.ShippingKidFacts
import Tools.ShippingPortsMatchRawLeaf
import Tools.ShippingChecksMaskedLeaf
import Tools.ShippingChecksRun2
import Tools.ShippingChecksCore
import Tools.ShippingChildIfaceTy
import Tools.ShippingSeqChildIface
import Tools.ShippingLeafTyped
import Tools.ShippingLeafPorts

/-! # `LeafKid → KidFacts`: a leaf register machine as a callee of the `kids_*` chain (G1, round par/a-14)

`Tools/ShippingKidFacts.lean` proves the four run hypotheses of the head
`machine_design_noPorts` from `KidFacts` of every call entry's callee;
`Tools/ShippingOneOutKid.lean` gives `KidFacts … 1` for a callee with a
register and one-output calls of its own. This file gives it, at EVERY
depth `n`, for a LEAF register machine (`LeafKid`: no calls, a register),
so that a parent with both kinds of callees (`mixD1`: `midH` and `cnt`) goes
through the same four theorems.

Each field is a BUILT `leaf_real_*` lemma (the ones `#machine_no_ports`
fills the per-child hypotheses with):

    outsIn   seqChild_of_real … .outsIn                  Tools/ShippingSeqChildIface.lean
    outTys   leaf_real_outTys                            Tools/ShippingChildIfaceTy.lean
    kidA     leaf_real_kidA                              Tools/ShippingChecksRun2.lean
    kidR     leaf_real_kidR                              Tools/ShippingChecksCore.lean
    masked   (leaf_real_kidM …).1                        Tools/ShippingChecksMaskedLeaf.lean
    portsIn  leaf_real_portsIn                           Tools/ShippingLeafTyped.lean
    inW      (leaf_real_ports …).inWidths                Tools/ShippingLeafPorts.lean
    clk      (leaf_real_ports …).clk                     Tools/ShippingLeafPorts.lean
    check    leaf_real_kidK_reg (the leaf form, at every child map and depth)

`ins` is `declWidths dk` (the data `callArgsOk` is decided against for a
leaf callee, as in `core_portsMatch_raw_leaf`).

No new fact about the compiler is proved here.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingLeafKidFacts
open Lean Meta
open Tools.ShippingPortsMatchRawLeaf (LeafKid)
open Tools.ShippingKidFacts (KidFacts)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
  {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}

/-- **`KidFacts` of a leaf register machine, at every depth.** -/
theorem leafKid_facts (K : LeafKid mctx mref cctx cref c dk) (n : Nat) :
    KidFacts mref cref c dk.shape.layout.outs
      (Tools.ShippingPortWidthsPure.declWidths dk) n :=
  { outsIn := fun _ hy =>
      (Tools.ShippingSeqChildIface.seqChild_of_real dk K.ok K.body K.leaf K.outTy K.entry
        K.closes hy).outsIn
    outTys := fun _ hy =>
      Tools.ShippingChildIfaceTy.leaf_real_outTys dk K.ok K.body K.leaf K.slots K.ss K.outTy
        K.entry K.closes hy
    kidA := fun _ hy =>
      Tools.ShippingChecksRun2.leaf_real_kidA dk K.ok K.body K.leaf K.slots K.ss K.outTy
        K.entry K.closes hy
    kidR := fun _ hy =>
      Tools.ShippingChecksCore.leaf_real_kidR dk K.ok K.body K.leaf K.outTy K.entry K.closes hy
    masked := fun _ hy =>
      (Tools.ShippingChecksMaskedLeaf.leaf_real_kidM (nDecl := dk.nIn) dk K.ok K.body K.calls
        K.dom K.leaf K.slots K.ss K.outTy K.entry K.closes hy).1
    portsIn := fun _ hy =>
      Tools.ShippingLeafTyped.leaf_real_portsIn (nDecl := dk.nIn) dk K.ok K.body K.calls K.dom
        K.leaf K.ss K.outTy K.entry K.closes K.outName K.outScalar hy
    inW := fun _ hy _ _ hq =>
      (Tools.ShippingLeafPorts.leaf_real_ports (nDecl := dk.nIn) dk K.ok K.body K.calls K.dom
        K.leaf K.ss K.outTy K.entry K.closes hy).inWidths hq
    clk := fun _ hy hs =>
      (Tools.ShippingLeafPorts.leaf_real_ports (nDecl := dk.nIn) dk K.ok K.body K.calls K.dom
        K.leaf K.ss K.outTy K.entry K.closes hy).clk hs
    check := fun _ hy ms _ _ =>
      have h := Tools.ShippingLeafTyped.leaf_real_kidK_reg (nDecl := dk.nIn) dk K.ok K.body
        K.calls K.dom K.leaf K.slots K.ss K.outTy K.entry K.closes K.outName K.outScalar hy
      ⟨h.1 (Tools.ShippingMachineLinked.childMap ms) n,
        fun g hg => h.2 g hg (Tools.ShippingMachineLinked.childMap ms) n⟩ }

end Tools.ShippingLeafKidFacts
