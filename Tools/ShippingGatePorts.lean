import Tools.ShippingCombKidText
import Tools.ShippingTypedWidthOk
import Tools.ShippingInstWidthsParts
import Tools.ShippingOutsExtractedParts
import Tools.ShippingTransitionPortTys
import Tools.ShippingWidthTables
import Tools.ShippingCloseMachineFacts

/-! # The COMMON port facts of a gate child, and their two views (G1, round par/a-7; P2, P3, P4, T3 and the child side of T4 of docs/parallel/A-oneout.md)

A parent's two residual checks read a gate child's module in two width
tables: `hierTyped` in the IR's (`declWidth child`, the wire table) and
`portsMatchB` in the emitter's (`weS child`, wires then inputs then outputs
by sanitized name). Both are derived here from ONE structure of facts about
the child's full-entry module, `GateChildPorts c bs w m`.

## What existed, and what it determined

* `ChildFull c bs b design` (`Tools/ShippingGateChildComb.lean`, produced by
  `gate_child_fullFacts` / `childFull_of_real`): the input port TYPES
  (`tys`: `kindTy` of the non-domain binders, in order), the module's name,
  `ChildComb` (assignments only, closed reads, `∃ ty, outputs = [out : ty]`,
  `out` driven, input names distinct and allocated). It says NOTHING about
  the output port's type or width, nor that an input port is a wire.
* `transition_closed` (`Tools/ShippingTransitionClosed.lean`):
  `(∃ ow, PrintBaseAt ow m) ∧ TypedPostReady m` of the RAW gate module. The
  width `ow` is existentially hidden. `PrintBaseAt ow m` has
  `output : ∃ ty, m.outputs = [out : ty]`, `outputs` (the type printable),
  `outputWidth : p.ty.bitWidth = ow`, `inputWires`, `wireNames`,
  `outputTyped` (the driver of `out` typed at `ow`).
* `transition_facts` (`Tools/ShippingMachineEntry.lean` 301, the statement
  `transition_closed` is proved from) DOES name the width:
  `RawValueAt srt.width bs m …`, whose last conjunct is
  `PositiveBinders bs → PrintBaseAt srt.width m`. So `ow = srt.width`
  (`SType.width`: `1` for `.bool`, `w` for `.bits w`) was already a BUILT
  statement; only `transition_closed`'s conclusion dropped it.

## What is added

* `gate_child_base` — the ONE exporting variant: the prelude of
  `gate_child_comb` / `gate_child_fullFacts` / `gate_child_forwardCheck`
  (run → entry → harness run) followed by `transition_facts` instead of
  `transition_closed`: the raw module `M` of the run with
  `PrintBaseAt srt.width M` and `TypedPostReady M`. It strengthens the
  conclusion those three theorems extract from the same prelude (their
  `∃ ow`). No translator run is opened here; the prelude is nine existing
  lemma applications.
* `post_facts` — pure: the cleanup and the checked merge keep the ports, the
  order, the typing and the output's typing (`dropZeroWidth_typed`,
  `mergeChecked_ports`, `mergeDuplicates_order` / `_typed` / `_output`).
* `GateChildPorts c bs w m`, `gate_child_ports`, `gate_real_ports`.
* The emitter's view: `GateChildPorts.portsIn` (P3), `.weS_out` (P4),
  `.weS_in`, `.inWidths` (P2).
* The IR's view: `.declWidth_in`, `.outWidth` (`gate_real_outWidth`, P4),
  `.inWidths` (same statement, both tables), `.childTyped_ok` (T3).
* `.notSeq`, `.inPortsOf_eq`: no clock or reset input.

Both views of an input port come from the same two facts — the port IS a
wire of the module, the only one of its name (`inWire`, `wireUnique`), of a
scalar type (`inPrintable`) — through `declWidth_of_unique` and
`declWidth_eq_weS`. Both views of the output come from `out` (the one port
`out`, printable, of width `w`).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingGatePorts
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Semantics
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface
open Tools.ShippingUnifiedExecutionSoundness
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingTypedExprSoundness (TypedExpr)
open Tools.ShippingTypedPostSoundness (TypedStmts OutputTypedAt TypedPostReady)
open Sparkle.IR.RefineCheck (mergeChecked)

/-! ## The exporting variant of the gate prelude -/

set_option maxHeartbeats 1000000 in
/-- **A gate child's raw module, with the output width NAMED**: over every
run of the full entry, from the declaration's reflection, the full entry's
module `b` is the cleanup (or its checked merge) of a module `M` with
`PrintBaseAt srt.width M` and `TypedPostReady M`. The width is the width of
the quoted term's sort. -/
theorem gate_child_base {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ M : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      PrintBaseAt srt.width M ∧ TypedPostReady M := by
  obtain ⟨M, D, w1, hcore, hpost⟩ := Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  obtain ⟨logProf, envR, ci, w1', w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hcore
  obtain ⟨d, hd, definition⟩ := entry w1' ci w2 w5 envR w6 get henv
  rw [hd] at run
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have shape := term_gate (d := d) (by rw [definition]; exact peel) he hb hv
  have core := Tools.ShippingGateChild.synthesizeFromConst_mixed_run oldGate (shape _) run.mreturns
  obtain ⟨ids, cache, returned, st, nd, len, hrun, hm, _, nameLegal⟩ :=
    synthesizeMixedCertified_returns core
  have positive := Tools.ShippingMixedPrintSoundness.mixedShape_positive (shape (fun _ => false))
  have facts := transition_facts nd len hrun hm nameLegal he hb hv rfl
  have zero : SourceInputs declName bs ids cache (fun _ => false) (fun _ n => 0#n)
      (fun _ => 0) := Tools.ShippingMachineEntry.admissible_zero _ _
  obtain ⟨_, _, _, ready, _, _, _, _, base⟩ := facts.1 _ _ _ (fun _ _ => 0) zero
  exact ⟨M, hpost, base positive, ready⟩

/-! ## Pure: through the cleanup and the checked merge -/

/-- A printable type has a nonzero width. -/
theorem printable_ne_zero {ty : Sparkle.IR.Type.HWType}
    (h : Tools.ShippingModulePrintSoundness.PrintableType ty) : ty.bitWidth ≠ 0 := by
  cases h with
  | bit =>
    first
      | exact Nat.succ_ne_zero 0
      | decide
      | simp [Sparkle.IR.Type.HWType.bitWidth]
  | bits n hn =>
    first
      | exact Nat.ne_of_gt hn
      | (simp [Sparkle.IR.Type.HWType.bitWidth]; omega)

/-- A printable type is one bit or a bit vector. -/
theorem printable_scalar {ty : Sparkle.IR.Type.HWType}
    (h : Tools.ShippingModulePrintSoundness.PrintableType ty) :
    ty = .bit ∨ ∃ n, ty = .bitVector n := by
  cases h with
  | bit => exact Or.inl rfl
  | bits n hn => exact Or.inr ⟨n, rfl⟩

/-- **The cleanup and the checked merge of a gate module keep its ports, its
order, its typing and its output's typing.** -/
theorem post_facts {ow : Nat} {M b : Sparkle.IR.AST.Module}
    (pb : PrintBaseAt ow M) (ready : TypedPostReady M)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) :
    b.inputs = M.inputs ∧ b.outputs = M.outputs ∧
      b.wires = (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).wires ∧
      Tools.ShippingSettledSoundness.Acyclic b.body ∧
      TypedStmts (Tools.ShippingEntrySoundness.weOf b) b.body ∧
      OutputTypedAt ow (Tools.ShippingEntrySoundness.weOf b) b.body := by
  obtain ⟨dzb, dzw, dzi, dzo, dzt⟩ := Tools.ShippingTypedPostSoundness.dropZeroWidth_typed ready
  have hZa : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body.all
      Sparkle.IR.RegDedup.isAssign = true := by
    rw [dzb]
    exact acyclic_isAssign pb.order
  have hZo : Tools.ShippingSettledSoundness.Acyclic
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body := by
    rw [dzb]
    exact pb.order
  have hZout : OutputTypedAt ow
      (Tools.ShippingEntrySoundness.weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body := by
    rw [dzb, dzw]
    exact pb.outputTyped
  have hz : Tools.ShippingEntrySoundness.weOf
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) "out" = 0 := by
    rw [dzw]
    exact ready.outWidthZero
  rcases hpost with h | h
  · rw [h]
    exact ⟨dzi, dzo, rfl, hZo, dzt, hZout⟩
  · have hmd := Tools.ShippingCombKidText.mergeChecked_assign hZa
    have hp := Sparkle.IR.RefineCheck.mergeChecked_ports
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)
    rw [h]
    refine ⟨hp.1.trans dzi, hp.2.1.trans dzo, hp.2.2, ?_, ?_, ?_⟩
    · rw [hmd]
      exact Tools.ShippingPostSoundness.mergeDuplicates_order hZo
    · rw [hmd]
      exact Tools.ShippingTypedPostSoundness.mergeDuplicates_typed hz dzt
    · rw [hmd]
      exact Tools.ShippingTypedPostSoundness.mergeDuplicates_output hz dzt hZout

/-! ## The common facts -/

/-- **What a parent's width checks need of a gate child's full-entry
module** `m` (declaration `c`, binders `bs`, result width `w`): its name;
the input ports are the declared non-domain binders' ports, of their types,
each a wire of the module and the only wire of its name; every wire name is
an allocated name; the one output port is `out`, of a printable type of
width `w`; the body is an ordered list of typed assignments whose driver of
`out` is typed at `w`. -/
structure GateChildPorts (c : Name) (bs : List (Name × MixedGateBinder)) (w : Nat)
    (m : Sparkle.IR.AST.Module) : Prop where
  name : m.name = (Sparkle.IR.ModuleName.ofDecl c)
  inTys : m.inputs.map (·.ty) = (bs.filter fun x => x.2 != .domain).map fun x => kindTy x.2
  inPrintable : ∀ p ∈ m.inputs, Tools.ShippingModulePrintSoundness.PrintableType p.ty
  inWire : ∀ p ∈ m.inputs, p ∈ m.wires
  inNodup : (m.inputs.map (·.name)).Nodup
  wireAlloc : ∀ p ∈ m.wires, Sparkle.IR.NameHints.Allocated p.name
  wireUnique : ∀ p ∈ m.wires, ∀ r ∈ m.wires, r.name = p.name → r = p
  out : ∃ ty, m.outputs = [{ name := "out", ty := ty }] ∧
    Tools.ShippingModulePrintSoundness.PrintableType ty ∧ ty.bitWidth = w
  order : Tools.ShippingSettledSoundness.Acyclic m.body
  typed : TypedStmts (Tools.ShippingEntrySoundness.weOf m) m.body
  outTyped : OutputTypedAt w (Tools.ShippingEntrySoundness.weOf m) m.body
  outDriven : "out" ∈ Sparkle.IR.Reorder.writesOf m.body

set_option maxHeartbeats 1000000 in
/-- **The common port facts of a gate child's full-entry module**, over
every run of the full entry, from the declaration's reflection: derived
from `gate_child_base` (the widths) and the existing `gate_child_fullFacts`
(the input types, the name, the driven output). -/
theorem gate_child_ports {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    GateChildPorts declName bs srt.width b := by
  obtain ⟨M, hpost, pb, ready⟩ := gate_child_base hr entry old peel he hb hv
  have hfull := gate_child_fullFacts hr entry old peel he hb hv
  obtain ⟨hin, hout, hwires, hord, hty, hoty⟩ := post_facts pb ready hpost
  obtain ⟨ty, hty0⟩ := pb.output
  have hmemO : ({ name := "out", ty := ty } : Port) ∈ M.outputs := by
    rw [hty0]
    exact List.mem_singleton.mpr rfl
  have hsub : ∀ p ∈ b.wires, p ∈ M.wires := by
    intro p hp
    rw [hwires] at hp
    exact Tools.ShippingInstWidthsParts.dropZW_wires_sub M p hp
  have hinM : ∀ p ∈ b.inputs, p ∈ M.inputs := by
    intro p hp
    rw [hin] at hp
    exact hp
  exact
    { name := hfull.name
      inTys := hfull.tys
      inPrintable := fun p hp => pb.inputs p (hinM p hp)
      inWire := fun p hp => by
        rw [hwires]
        exact Tools.ShippingOutsExtractedParts.dropZW_wires (pb.inputWires p (hinM p hp))
          (printable_ne_zero (pb.inputs p (hinM p hp)))
      inNodup := hfull.comb.inputNames
      wireAlloc := fun p hp => pb.wireNames p (hsub p hp)
      wireUnique := fun p hp r hr' hn =>
        Tools.ShippingTransitionPortTys.port_of_name ready.wiresNodup (hsub r hr') (hsub p hp) hn
      out := ⟨ty, hout.trans hty0, pb.outputs _ hmemO, pb.outputWidth _ hmemO⟩
      order := hord
      typed := hty
      outTyped := hoty
      outDriven := hfull.comb.outDriven }

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The common port facts of a REAL gate child** (`gate_real_ports`): no
hypothesis but the child's reflection and what `#gate_child` leaves. -/
theorem gate_real_ports {c : Name} {y : Res}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (entry : EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (h : RealChild mref cref c y) : GateChildPorts c bs srt.width y.1 := by
  obtain ⟨mctx', cctx', w, w', -, hr⟩ := h.inv
  exact gate_child_ports hr (Tools.ShippingReflectCtx.EntryDefines.ctx entry) old peel he hb hv

/-! ## The views -/

section Views
variable {c : Name} {bs : List (Name × MixedGateBinder)} {w : Nat} {m : Sparkle.IR.AST.Module}

/-- The wire names are sanitize-stable. -/
theorem GateChildPorts.wn (h : GateChildPorts c bs w m) :
    ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name :=
  fun p hp => (Tools.ShippingPortWidthsPure.wire_ne_clk (Or.inl (h.wireAlloc p hp))).1

/-- No wire is named `out`. -/
theorem GateChildPorts.noOutWire (h : GateChildPorts c bs w m) :
    ∀ p ∈ m.wires, p.name ≠ "out" :=
  fun p hp e => Tools.ShippingRegisterSoundness.not_allocated_out (e ▸ h.wireAlloc p hp)

/-- The input names are allocated names. -/
theorem GateChildPorts.inAlloc (h : GateChildPorts c bs w m) :
    ∀ p ∈ m.inputs, Sparkle.IR.NameHints.Allocated p.name :=
  fun p hp => h.wireAlloc p (h.inWire p hp)

/-- No clock or reset input. -/
theorem GateChildPorts.notSeq (h : GateChildPorts c bs w m) : isSeqChild m = false :=
  Tools.ShippingPortWidthsPure.seq_of_alloc_inputs h.inAlloc

/-- Every input is an argument port. -/
theorem GateChildPorts.inPortsOf_eq (h : GateChildPorts c bs w m) : inPortsOf m = m.inputs := by
  unfold Tools.ShippingInstStmtG.inPortsOf
  refine List.filter_eq_self.mpr (fun p hp => ?_)
  obtain ⟨-, h1, h2⟩ := Tools.ShippingPortWidthsPure.wire_ne_clk (Or.inl (h.inAlloc p hp))
  show (p.name != "clk" && p.name != "rst") = true
  exact (Bool.and_eq_true _ _).mpr ⟨bne_iff_ne.mpr h1, bne_iff_ne.mpr h2⟩

/-- **The output port: named `out`, of the declared result width** (P4). -/
theorem GateChildPorts.outWidth (h : GateChildPorts c bs w m) :
    ∀ p ∈ m.outputs, p.name = "out" ∧ p.ty.bitWidth = w := by
  obtain ⟨ty, ho, -, hw⟩ := h.out
  intro p hp
  rw [ho] at hp
  rw [List.mem_singleton.mp hp]
  exact ⟨rfl, hw⟩

/-- **The emitter resolves the module's output port** (P3): `PortsIn`. -/
theorem GateChildPorts.portsIn (h : GateChildPorts c bs w m) :
    Tools.ShippingLeafTyped.PortsIn m := by
  obtain ⟨ty, ho, hpr, hw⟩ := h.out
  have hso : Sparkle.Backend.Verilog.sanitizeName "out" = "out" := by
    simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq]
  refine { wn := h.wn, ow := ?_, oi := ?_, ostable := ?_, ond := ?_, oty := ?_ }
  · intro q hq p hp
    rw [ho] at hq
    rw [List.mem_singleton.mp hq]
    exact h.noOutWire p hp
  · intro q hq p hp
    rw [ho] at hq
    rw [List.mem_singleton.mp hq, h.wn p (h.inWire p hp)]
    exact h.noOutWire p (h.inWire p hp)
  · intro q hq
    rw [ho] at hq
    rw [List.mem_singleton.mp hq]
    exact hso
  · rw [ho]
    first
      | exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
      | simp
  · intro q hq
    rw [ho] at hq
    rw [List.mem_singleton.mp hq]
    exact printable_scalar hpr

/-- **An input port's width in the IR's table** is its type's. -/
theorem GateChildPorts.declWidth_in (h : GateChildPorts c bs w m) {q : Port}
    (hq : q ∈ m.inputs) : Sparkle.IR.RegDedup.declWidth m q.name = q.ty.bitWidth :=
  Tools.ShippingInstWidthsParts.declWidth_of_unique (nm := q.name) (ty := q.ty)
    (h.inWire q hq) (fun r hr hn => h.wireUnique q (h.inWire q hq) r hr hn)
    (printable_scalar (h.inPrintable q hq))

/-- **An input port's width in the emitter's table** is its type's. -/
theorem GateChildPorts.weS_in (h : GateChildPorts c bs w m) {q : Port}
    (hq : q ∈ m.inputs) : Tools.ShippingDesignSV.weS m q.name = q.ty.bitWidth := by
  have h1 : Tools.ShippingDesignSV.weS m q.name = Sparkle.IR.RegDedup.declWidth m q.name :=
    (Tools.ShippingWidthTables.declWidth_eq_weS h.wn
      (List.mem_map.mpr ⟨q, h.inWire q hq, rfl⟩)).symm
  exact h1.trans (h.declWidth_in hq)

/-- **The output port's width in the emitter's table** (P4). -/
theorem GateChildPorts.weS_out (h : GateChildPorts c bs w m) :
    Tools.ShippingDesignSV.weS m "out" = w := by
  obtain ⟨ty, ho, -, hw⟩ := h.out
  have hq : ({ name := "out", ty := ty } : Port) ∈ m.outputs := by
    rw [ho]
    exact List.mem_singleton.mpr rfl
  have h1 : Tools.ShippingDesignSV.weS m "out" = ty.bitWidth := h.portsIn.weS_output hq
  exact h1.trans hw

/-- **The input ports' widths, by position, in BOTH tables** (P2 and the
child side of T4): the `j`-th input port has, in the emitter's table and in
the IR's, the width of the type of the `j`-th non-domain binder. -/
theorem GateChildPorts.inWidths (h : GateChildPorts c bs w m) {j : Nat} {q : Port}
    (hq : m.inputs[j]? = some q) :
    ∃ wd, ((bs.filter fun x => x.2 != .domain).map fun x => (kindTy x.2).bitWidth)[j]? =
        some wd ∧
      Tools.ShippingDesignSV.weS m q.name = wd ∧
      Sparkle.IR.RegDedup.declWidth m q.name = wd := by
  have hqm : q ∈ m.inputs := List.mem_of_getElem? hq
  have h1 : (m.inputs.map (·.ty))[j]? = some q.ty :=
    Tools.ShippingPortWidthsPure.getElem?_map_some (fun p : Port => p.ty) hq
  rw [h.inTys] at h1
  rw [List.getElem?_map] at h1
  cases hb : (bs.filter fun x => x.2 != .domain)[j]? with
  | none =>
    rw [hb] at h1
    cases h1
  | some bn =>
    rw [hb] at h1
    have hqt : kindTy bn.2 = q.ty := by
      simpa only [Option.map_some, Option.some.injEq] using h1
    refine ⟨q.ty.bitWidth, ?_, h.weS_in hqm, h.declWidth_in hqm⟩
    rw [List.getElem?_map, hb]
    show some ((kindTy bn.2).bitWidth) = some q.ty.bitWidth
    rw [hqt]

/-- `out` is `0` in the wire table. -/
theorem GateChildPorts.weOf_out (h : GateChildPorts c bs w m) :
    Tools.ShippingEntrySoundness.weOf m "out" = 0 :=
  Tools.ShippingTypedWidthOk.weOf_not_wire h.noOutWire

/-- **A gate child is a width-typed child** (T3): every assignment is
`assignTyped` in the module's own declared widths off `out`
(`assignTyped_of_typed`), and `out` is assigned exactly once (the order has
distinct targets, `out` is driven) by an expression of the port's width. -/
theorem GateChildPorts.childTyped_ok (h : GateChildPorts c bs w m) :
    Tools.ShippingHierTyped.childTyped (Sparkle.IR.RegDedup.declWidth m) m = true := by
  obtain ⟨ty, ho, hpr, hw⟩ := h.out
  have hW : Sparkle.IR.RegDedup.declWidth m = Tools.ShippingEntrySoundness.weOf m := rfl
  rw [hW]
  unfold Tools.ShippingHierTyped.childTyped
  refine (Bool.and_eq_true _ _).mpr ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    intro st hst
    obtain ⟨l, e, n, hse, ht, hl⟩ := h.typed st hst
    rw [hse]
    show Tools.ShippingHierTyped.assignTyped (Tools.ShippingEntrySoundness.weOf m)
      (m.outputs.map (·.name)) l e = true
    refine Tools.ShippingTypedWidthOk.assignTyped_of_typed ht ?_ ?_
    · intro x hx
      obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hx
      rw [ho] at hq
      have hq' := List.mem_singleton.mp hq
      have hqn' : q.name = x := hqn
      have hx' : x = "out" := by
        rw [← hqn', hq']
      rw [hx']
      exact h.weOf_out
    · rcases hl with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (List.mem_map.mpr ⟨{ name := "out", ty := ty },
          by rw [ho]; exact List.mem_singleton.mpr rfl, h1.symm⟩)
  · rw [ho, List.all_eq_true]
    intro p hp
    rw [List.mem_singleton.mp hp]
    obtain ⟨st, hst, hws⟩ := List.mem_flatMap.mp h.outDriven
    obtain ⟨l, e, n, hse, ht, hl⟩ := h.typed st hst
    rw [hse] at hws hst
    have hlo : l = "out" := (List.mem_singleton.mp hws).symm
    rw [hlo] at hst
    have hte := h.outTyped e hst
    have hle : widthOf (Tools.ShippingEntrySoundness.weOf m) e ≤ ty.bitWidth := by
      rw [hte.width, hw]
      exact Nat.le_refl w
    have hc : List.count "out" (Sparkle.IR.Reorder.writesOf m.body) = 1 := by
      rw [(Tools.ShippingCloseMachineFacts.Acyclic.nodup h.order).count, if_pos h.outDriven]
    refine (Bool.and_eq_true _ _).mpr ⟨beq_iff_eq.mpr hc, ?_⟩
    refine List.any_eq_true.mpr ⟨Stmt.assign "out" e, hst, ?_⟩
    show (("out" : String) == "out" &&
      decide (widthOf (Tools.ShippingEntrySoundness.weOf m) e ≤ ty.bitWidth)) = true
    exact (Bool.and_eq_true _ _).mpr ⟨beq_self_eq_true _, decide_eq_true hle⟩

end Views

/-- **The output width of a real gate child** (`gate_real_outWidth`, P4):
every output port of its module has the width of the quoted term's sort. -/
theorem gate_real_outWidth {c : Name} {y : Res}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (entry : EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (h : RealChild mref cref c y) :
    ∀ p ∈ y.1.outputs, p.ty.bitWidth = srt.width :=
  fun p hp => ((gate_real_ports entry old peel he hb hv h).outWidth p hp).2

end Tools.ShippingGatePorts
