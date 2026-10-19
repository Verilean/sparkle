import Tools.ShippingChecksWidths
import Tools.ShippingGuardsSound
import Tools.ShippingMachineRanBase
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

/-! # The run's facts of a machine with calls, bundled (isolated branch `fix/opt-fallback`)

`core_runFacts`: for a core run on a machine with calls closed by
`closeInstsG` and with a register — the hypotheses of `core_shipsHier_rest3`
WITHOUT its three check premises (`hierBinds`, the two post-pass facts) —
the full entry's module satisfies `Tools.ShippingGuardsSound.RunFacts`:
the statement-kind gate (`core_hierGate`), linked well-formedness
(`core_linkedWF`), distinct instance names, the self-read test and the
reset port (`core_raw_facts`), the extraction of the instance-driven wires
(`core_outsExtracted`) and their declared widths (`core_instOutWidthsOk`).

It is the `facts` argument of `machine_ships_hierC_free`, and with
`checkedOptimize_facts` it gives, of the SHIPPED module, linked
well-formedness, distinct instance names and the full entry's inputs
(`core_shipped_facts`) — what `shipped_sv`
(`Tools/ShippingHierShipsSV.lean` 89–93) takes from `hierCheck`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingChecksRunFacts
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

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `core_runFacts` over `MachineRan`:
the proof of the built theorem, MOVED here (split in place, branch
`fix/ran-threading-split`) with the run, the reflection, the closing and the boundary
replaced by `ran` and every callee of the chain by its `_ran` form. It takes of the run only
that the machine synthesis this core run performed returned the result from an invariant
world; the theorem below, its statement unchanged, is the instance at the all-worlds closing
(`Tools.ShippingMachineRan.machineRan_of_closes`). -/
theorem core_runFacts_ran {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b := by
  obtain ⟨hrst, hndB, hself⟩ :=
    Tools.ShippingChecksRaw.core_raw_facts_ran d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem
      hpost ran
  exact
    { gate := Tools.ShippingChecksWidths.core_hierGate_ran d ok hbody hC hslots hdomB hins hfne outTy
        hnomem hpost ran
      wfB := Tools.ShippingLinkedFresh.core_linkedWF_ran d ok hbody hC hslots hdomB hins outTy hnomem
        hpost ran
      ndB := hndB
      self := hself
      outs := Tools.ShippingChecksOuts.core_outsExtracted_ran d ok hbody hC hslots hdomB hins hfne
        outTy hnomem hkidP hpost ran
      rst := hrst
      wid := Tools.ShippingChecksWidths.core_instOutWidthsOk_ran d ok hbody hC hslots hdomB hins hfne
        outTy hnomem hkidP hkidW hpost ran }

/-- **The run's facts of the full entry's module**, from the core run of a
machine with calls closed by `closeInstsG` and with a register. -/
theorem core_runFacts {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  core_runFacts_ran d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem hkidP hkidW hpost
    (Tools.ShippingMachineRan.machineRan_of_closes hcore entry hB closes)

/-- **The shipped module of a machine with calls** is linked-well-formed,
has distinct instance names and the full entry's inputs — with NO check
premise (conjuncts 1, 2, 4 of `shipsHierCheck` are no longer asked). -/
theorem core_shipped_facts {C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {b : Sparkle.IR.AST.Module} (h : Tools.ShippingGuardsSound.RunFacts C b) :
    Tools.ShippingHierOpen.linkedWF C (checkedOptimize b).body = true ∧
      (Tools.ShippingHierState.instNames (checkedOptimize b).body).Nodup ∧
      (checkedOptimize b).inputs = b.inputs :=
  Tools.ShippingGuardsSound.checkedOptimize_facts h.gate h.wfB h.ndB h.outs

end Tools.ShippingChecksRunFacts
