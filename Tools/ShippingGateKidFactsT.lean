import Tools.ShippingMemKidFacts
import Tools.ShippingGatePorts
import Tools.ShippingChecksGate
import Tools.ShippingGateKid
-- WRITTEN, NOT BUILT (round par/o-gchk).

/-! # The check-free chain's facts of a GATE child, by ORIGIN (round par/o-gchk)

The origin-based chain `Tools.ShippingMemKid.kidsM_*T` takes, per call entry,
`KidFactsT mref cref (originAt d.shape k) (insts[k]).1 outs ins n`. For a
leaf register child it is given by `leafKid_facts` + `kidFactsT_of`, for a
memory origin by `memKidT_facts`. For a GATE child (a combinational
`@[hardware_module]` the unified mixed gate compiles; no `machine_sound`) it
is NOT provable: its field `flat : FlatOk y.1` asks (`noMem` and) every output
assigned by a SELF-MASKED expression (`outMasked`: a constant or a slice),
while the gate route drives its one output by `assign "out" (.ref w)`
(`Sparkle.Compiler.Elab.emitLeaves`), which no post-processing turns into a
slice (`mergeDuplicates` rewrites references to references) — and the gate
module is not the built memory module. READ off the compiler; not
machine-checked here.

`flat` is used by ONE consumer only, `kidsM_mixedT` (`kidsMixed`, the `Bd` of
the depth-0 route). The three other consumers read the remaining fields. So:

* `KidFactsTC`: `KidFactsT` WITHOUT `flat` (same field names, same types);
* `KidFactsT.toC`: every `KidFactsT` gives it (a memory origin: from
  `memKidT_facts`);
* `gateKidT_factsC`: a gate child — an entry whose origin builds no child,
  its callee `c` with the reflection `EntryDefines c value` and the gate's
  reading of `value` (what `#gate_child` / `gateDefs` leave: `old`, `peel`,
  `wf`, binder positions) — has it at EVERY depth, outputs
  `gateOuts srt.width` (`[out : BitVec w]`), argument widths `gateIns bs`;
  from `gate_real_ports` (`GateChildPorts`), `childFull_of_real`
  (`gate_kidA` / `gate_kidR`), `gate_real_kidK` and `gate_full_outputs`
  (result width ≠ 1);
* `kidsC_runFactsT`, `kidsC_outsCheckT`, `kidsC_designCheckT`: the three
  consumers, their proofs copied verbatim from `kidsM_runFactsT`,
  `kidsM_outsCheckT`, `kidsM_designCheckT` over `KidFactsTC`;
* `exists_bnd_merge`: pure — an antecedent `B ∧ E` under `∃ a b, P a b ∧ …`
  becomes `B` given `E`.

No new fact about the compiler; nothing added to `RefLaws` or a trusted list. -/
namespace Tools.ShippingMemKid
open Lean Meta
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
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
open Sparkle.Compiler.MachMemory (memModule memChild?)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`KidFactsT` without `flat`**: what `kidsM_runFactsT`, `kidsM_outsCheckT`
and `kidsM_designCheckT` read of one callee (by ORIGIN). -/
structure KidFactsTC (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) (o : InstOrigin) (c : Name) (outs : List OutField)
    (ins : List Nat) (n : Nat) : Prop where
  outsIn : ∀ (y : Res), Tools.ShippingInstTagged.KidT mref cref o c y →
    ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
      p.name ≠ "rst"
  outTys : ∀ (y : Res), Tools.ShippingInstTagged.KidT mref cref o c y →
    Tools.ShippingChildIfaceTy.ChildOutTys outs y.1
  kidA : ∀ (y : Res), Tools.ShippingInstTagged.KidT mref cref o c y →
    Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
      ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true
  kidR : ∀ (y : Res), Tools.ShippingInstTagged.KidT mref cref o c y →
    ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
      ∃ g2 ∈ y.2.modules, g2.name = mn
  portsIn : ∀ (y : Res), Tools.ShippingInstTagged.KidT mref cref o c y → Tools.ShippingLeafTyped.PortsIn y.1
  inW : ∀ (y : Res), Tools.ShippingInstTagged.KidT mref cref o c y →
    ∀ (j : Nat) (q : Port), (inPortsOf y.1)[j]? = some q →
      ∃ wd, ins[j]? = some wd ∧ Tools.ShippingDesignSV.weS y.1 q.name = wd
  clk : ∀ (y : Res), Tools.ShippingInstTagged.KidT mref cref o c y → isSeqChild y.1 = true →
    Tools.ShippingDesignSV.weS y.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y.1 "rst" = 1
  check : ∀ (y : Res), Tools.ShippingInstTagged.KidT mref cref o c y →
    ∀ ms : List Sparkle.IR.AST.Module,
      moduleByName ms y.1.name = some y.1 →
      (∀ g ∈ y.2.modules, moduleByName ms g.name = some g) →
      Tools.ShippingChecksDesign.kidCheck (childMap ms) n y.1 = true ∧
        ∀ g ∈ y.2.modules, Tools.ShippingChecksDesign.kidCheck (childMap ms) n g = true

/-- Every `KidFactsT` forgets to `KidFactsTC`. -/
theorem KidFactsT.toC {o : InstOrigin} {c : Name} {outs : List OutField} {ins : List Nat} {n : Nat}
    (h : KidFactsT mref cref o c outs ins n) : KidFactsTC mref cref o c outs ins n :=
  { outsIn := h.outsIn
    outTys := h.outTys
    kidA := h.kidA
    kidR := h.kidR
    portsIn := h.portsIn
    inW := h.inW
    clk := h.clk
    check := h.check }

/-! ## A gate child -/

/-- The output fields of a gate child of result width `w`: `[out : BitVec w]`. -/
def gateOuts (w : Nat) : List OutField :=
  [{ name := "out", lo := 0, width := w, ty := .bitVector w }]

/-- The argument widths of a gate child with binders `bs` (its non-domain
binders' types' widths, in order). -/
def gateIns (bs : List (Name × MixedGateBinder)) : List Nat :=
  (bs.filter fun x => x.2 != .domain).map fun x => (kindTy x.2).bitWidth

set_option maxHeartbeats 1000000 in
/-- **A GATE child's facts by origin, at every depth** (no `flat`): an entry
whose origin builds no child (`ho`), its callee `c` a declaration the unified
mixed gate reads to `value` (`entry`, `old`, `peel`, `he`, `hb`, `hv`), of
result width `≠ 1` (`hw1`). -/
theorem gateKidT_factsC {o : InstOrigin} {c : Name}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (ho : o.child? = none)
    (entry : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (hw1 : srt.width ≠ 1) (n : Nat) :
    KidFactsTC mref cref o c (gateOuts srt.width) (gateIns bs) n := by
  have hP : ∀ (y : Res), Tools.ShippingInstTagged.KidT mref cref o c y →
      Tools.ShippingGatePorts.GateChildPorts c bs srt.width y.1 := fun y hy =>
    Tools.ShippingGatePorts.gate_real_ports entry old peel he hb hv
      (Tools.ShippingInstTagged.KidT.real hy ho)
  have hF : ∀ (y : Res), Tools.ShippingInstTagged.KidT mref cref o c y →
      ChildFull c bs y.1 y.2 := fun y hy =>
    Tools.ShippingCallsGate.childFull_of_real entry old peel he hb hv
      (Tools.ShippingInstTagged.KidT.real hy ho)
  refine ⟨?outsIn, ?outTys, ?kidA, ?kidR, ?portsIn, ?inW, ?clk, ?check⟩
  case outsIn =>
    intro y hy p hp
    have hpn : p.name = "out" := ((hP y hy).outWidth p hp).1
    refine ⟨fun q hq hqe => ?_, ?_, ?_⟩
    · rw [(hP y hy).inPortsOf_eq] at hq
      have h1 : Sparkle.IR.NameHints.Allocated q.name := (hP y hy).inAlloc q hq
      rw [hqe, hpn] at h1
      exact Tools.ShippingRegisterSoundness.not_allocated_out h1
    · rw [hpn]; decide
    · rw [hpn]; decide
  case outTys =>
    intro y hy
    obtain ⟨mctx', cctx', w, w', -, hr⟩ := (Tools.ShippingInstTagged.KidT.real hy ho).inv
    refine ⟨?_⟩
    rw [Tools.ShippingGateKid.gate_full_outputs hr
      (Tools.ShippingReflectCtx.EntryDefines.ctx entry) old peel he hb hv hw1]
    rfl
  case kidA =>
    intro y hy
    exact Tools.ShippingChecksGate.gate_kidA (hF y hy)
  case kidR =>
    intro y hy
    exact Tools.ShippingChecksGate.gate_kidR (hF y hy)
  case portsIn =>
    intro y hy
    exact (hP y hy).portsIn
  case inW =>
    intro y hy j q hq
    rw [(hP y hy).inPortsOf_eq] at hq
    obtain ⟨wd, h1, h2, -⟩ := (hP y hy).inWidths hq
    exact ⟨wd, h1, h2⟩
  case clk =>
    intro y hy hs
    have h0 : isSeqChild y.1 = false := (hP y hy).notSeq
    rw [h0] at hs
    exact absurd hs (by decide)
  case check =>
    intro y hy ms _ _
    have hK := Tools.ShippingCombKidText.gate_real_kidK entry old peel he hb hv
      (Tools.ShippingInstTagged.KidT.real hy ho)
    exact ⟨hK.1 _ n, fun g hg => hK.2 g hg _ n⟩

/-! ## The three consumers over `KidFactsTC` (proofs copied from the `kidsM_*T` ones) -/

/-- **The run's facts of the full entry's module** (`kidsM_runFactsT` over
`KidFactsTC`). -/
theorem kidsC_runFactsT {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsTC mref cref (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  core_runFactsMT d ok hbody hC hslots hdomB hins hsl hfne outTy
    (fun k hk y hy => (hkid k hk).outsIn y hy)
    (hkidW_of_dataMT hcw (fun k hk y hy => (hkid k hk).outTys y hy))
    hB hcore hpost entry closes

/-- **The output check at depth `n`, under the statement-kind gate**
(`kidsM_outsCheckT` over `KidFactsTC`). -/
theorem kidsC_outsCheckT {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsTC mref cref (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true :=
  core_outsCheck_all_gateMT d ok hbody hC hslots hdomB hins outTy hfne
    (fun k hk y hy => (hkid k hk).kidA y hy)
    (fun k hk y hy => (hkid k hk).kidR y hy)
    hB hcore hpost entry closes hg n

set_option maxHeartbeats 4000000 in
/-- **`designCheck` of the shipped module at depth `n` with NO check
premise** (`kidsM_designCheckT` over `KidFactsTC`, its proof verbatim). -/
theorem kidsC_designCheckT {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsTC mref cref (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
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
    Tools.ShippingDesignSV.designCheck (childMap D.modules) n (checkedOptimize b) = true := by
  have hkidW := hkidW_of_dataMT hcw (fun k hk y hy => (hkid k hk).outTys y hy)
  have hraw : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) b = true :=
    core_portsMatch_rawMT d ok hbody hC hslots hdomB hins hfne outTy hkidW
      (fun k hk y hy => (hkid k hk).portsIn y hy)
      (kidIns := kidIns) hargs
      (fun k hk y hy j q hq => (hkid k hk).inW y hy j q hq)
      (fun k hk y hy hs => (hkid k hk).clk y hy hs)
      hB hcore hpost entry closes hon hoty
      (core_clkM d ok hbody hC hslots hdomB hins outTy hfne hsl hB hcore hpost entry closes)
  have hports : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) (checkedOptimize b) =
      true :=
    Tools.ShippingPortsMatchShipped.portsMatchB_shipped
      (core_hierGateMT d ok hbody hC hslots hdomB hins hfne outTy hB hcore hpost entry closes)
      hraw
  have hkids := core_kidsPass_deepMT d ok hbody hC hslots hdomB hins hfne outTy n
    (fun k hk y hy ms h1 h2 => (hkid k hk).check y hy ms h1 h2)
    hB hcore hpost entry closes
  exact core_designCheck_runMT d ok hbody hC hslots hdomB hins hsl hfne outTy
    (fun k hk y hy => (hkid k hk).outsIn y hy)
    hkidW hB hcore hpost entry closes hon hoty n hports hkids

/-! ## Merging a boundary conjunct that is given -/

/-- **An antecedent `B ∧ E` under the existentials becomes `B`, given `E`.** -/
theorem exists_bnd_merge {α β : Type} {P : α → β → Prop} {B E : Prop} {R : α → β → Prop}
    (hE : E) (h : ∃ a b, P a b ∧ (B ∧ E → R a b)) : ∃ a b, P a b ∧ (B → R a b) := by
  obtain ⟨a, b, hp, hr⟩ := h
  exact ⟨a, b, hp, fun hb => hr ⟨hb, hE⟩⟩

end Tools.ShippingMemKid
