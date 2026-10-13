import Tools.ShippingPortsMatchRawLeaf
import Tools.ShippingCallWidthsStrict

/-! # Port matching for a parent of LEAF machines with or without a register; the one-output width fact (G1, round par/a-5)

## 1. `LeafKid.slots` is not needed

`Tools.ShippingPortsMatchRawLeaf.LeafKid` asks `slots : dk.shape.layout.slots ≠ []`
of each callee. In `core_portsMatch_raw_leaf` that field has ONE use:
`leaf_real_outTys` (`Tools/ShippingChildIfaceTy.lean`), whose own proof
(`leaf_run_outputs`) uses `hsl` only to show that the raw module has a
register (`hnA`) — a fact the rest of that proof never reads (it was
copied from `leaf_run_outsAssigned`). The output ports come from
`closeMachine_outputs`, `MachineWired`'s cleanup clause and
`mergeChecked_ports`, none of which mentions slots.

* `leaf_run_outputs_any`, `leaf_real_outTys_any`: the same statements
  without `hsl` (the proof is `leaf_run_outputs`' with the unused block
  deleted, by a script).
* `LeafKidAny`: `LeafKid` without `slots`; `leafKid_toAny`.
* `core_portsMatch_raw_leaf_any`: `core_portsMatch_raw_leaf` over
  `LeafKidAny` (statement and proof copied by a script; the other three
  per-child facts — `leaf_real_portsIn`, `leaf_real_ports` — never asked
  for slots; `LeafPorts.clk` is conditional on `isSeqChild`, false for a
  slotless leaf by `LeafPorts.seq_iff`).

What stays: the PARENT's `hsl` (`core_clk`) and `hfne` (`core_callConns`,
the group closing). `core_portsMatch_raw` takes `hclkB` unconditionally and
uses it only at a sequential child's `clk` / `rst` connections
(`Tools/ShippingPortsMatchRaw.lean` 506–511): for a parent all of whose
children are combinational the parent's clock is not connected and `hsl`
would not be needed, but that needs `hclkB` weakened INSIDE
`core_portsMatch_raw` (an existing file; not done here).

## 2. The one-output closing: the width fact

`callWidthsOk` reads `instFields.getD k ""`; with `instFields = []`
(the one-output closing `closeInsts`) that is `""` and the condition is
vacuous. `Tools.ShippingCallWidthsStrict.callWidthsStrict` reads
`instFields[k]?`: with no entry, EVERY output of the child is compared.

* `hkidW_one`: under `instFields = []` and `callWidthsStrict`, every
  output port of a real child of call `k` has the width of the type of the
  call's binder. (A recombination of `hkidW_strict`.)

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingPortsMatchRawLeafAny
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
open Tools.ShippingPortsMatchRawLeaf (LeafKid)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 2000000 in
/-- **A leaf machine's returned module has the layout's output ports, with
their types**, over every run of the full entry — WITH OR WITHOUT a register
(`leaf_run_outputs` without `hsl`). -/
theorem leaf_run_outputs_any {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closesM : MachineCloses mctx mref cctx cref c d.shape) :
    b.outputs = d.shape.layout.outs.map (fun o => ({ name := o.name, ty := o.ty } : Port)) := by
  obtain ⟨M, D, w1, hcore, hpost, hdesM⟩ := synthesizeCombinational_parts hr
  have closes : MachineClosesAt mctx mref cctx cref c d.shape := machineClosesAt_of_closes closesM
  obtain ⟨_, bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
    machine_run_of_core hcore entry (ChildBnd.of_invW mctx cctx hw)
  have hne := closes bb _ _ _ hw9 hd9 hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ := synthesizeMachineCertified_runs hw9 hrun9
  rcases hmt with ⟨-, hMeq, hDeq⟩ | ⟨hne', -⟩
  rotate_left
  · exact absurd hno hne'
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, _, _, _, _, _, _, _, _⟩ := ok
  have hposv : PositiveBinders d.shape.binders := by
    intro name n hmem
    have := List.all_eq_true.mp positive _ hmem
    simpa using this
  have hb' : ∀ j, j < d.kb → ∃ name, d.shape.binders[d.bpos j]? = some (name, .bool) := by
    intro j hj
    have := hb j hj
    cases h : d.shape.binders[d.bpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have hv' : ∀ j, j < d.kv → ∃ name, d.shape.binders[d.vpos j]? = some (name, .bits (d.vw j)) := by
    intro j hj
    have := hv j hj
    cases h : d.shape.binders[d.vpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  obtain ⟨ids', cache', returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    synthesizeMixedCertified_returns run
  -- the transition ends in `assign out = w`, and so does the `let`-closed one
  obtain ⟨wP, hpw⟩ := Tools.ShippingChecksPacked.transition_packed nd len hrun hm d.packed hwf
    hb' hv' hbody
  obtain ⟨wP', hpw'⟩ := Option.isSome_iff_exists.mp
    (Tools.ShippingChecksPacked.closeLets_packed hcl hpw)
  have hrawA : Tools.ShippingDesignSVBack.outsAssigned M = true := by
    rw [hMeq]
    exact Tools.ShippingChecksDerived3.closeMachine_outsAssigned hpw'
  -- the raw module's wiring: the core entry's theorem at this run
  have layW : Tools.ShippingMachineClose.Zip₂
      (fun (f : SlotField) (b : Name × MixedGateBinder) =>
        f.width = machWidth b.2 ∧ b.2 ≠ .domain ∧ f.init < 2 ^ f.width)
      d.shape.layout.slots d.slotBs :=
    zip_of_all (by
      intro a b h
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h) layB
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeCombinationalCore_machine_sound hcore entry closesM d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, rlen, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hclean, -⟩ := wired
  obtain ⟨⟨hzb, -, -, hzo⟩, -, hregs, -, -, -, -, -, -⟩ := hclean hno outTy
  have hMout : M.outputs = d.shape.layout.outs.map
      (fun o => ({ name := o.name, ty := o.ty } : Port)) := by
    rw [hMeq]
    exact Tools.ShippingChecksCore.closeMachine_outputs hpw'
  rcases hpost with h | h
  · rw [h, hzo]
    exact hMout
  · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)).2.1, hzo]
    exact hMout

/-- **A real leaf child's output ports, with their types** — with or
without a register. -/
theorem leaf_real_outTys_any {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChild mref cref c y) :
    Tools.ShippingChildIfaceTy.ChildOutTys d.shape.layout.outs y.1 := by
  obtain ⟨mctx', cctx', w, w', hw, hr⟩ := h.inv
  exact ⟨leaf_run_outputs_any d ok hbody hno hSS outTy hw hr
    (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx')⟩

/-- **The premises about one leaf child declaration** `c` with data `dk`: a
machine without calls, WITH OR WITHOUT slots (`LeafKid` without `slots`). -/
structure LeafKidAny (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (c : Name)
    (dk : MachineData) : Prop where
  ok : dk.ok = true
  body : dk.shape.body = quote dk.dom
    (fun j => inputExpr dk.shape.binders.length (dk.bpos j))
    (fun j => inputExpr dk.shape.binders.length (dk.vpos j)) dk.packed
  calls : dk.callsOk dk.nIn = true
  dom : ∀ b ∈ dk.shape.binders.drop dk.nIn, b.2 ≠ .domain
  leaf : dk.shape.insts = []
  ss : dk.ss.length = dk.shape.layout.slots.length
  outTy : ∀ o ∈ dk.shape.layout.outs, o.ty.bitWidth = o.width
  outName : ∀ o ∈ dk.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name
  outScalar : ∀ o ∈ dk.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true
  entry : MachineDefines mctx mref cctx cref c dk.shape
  closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
    MachineCloses mctx' mref cctx' cref c dk.shape

/-- A leaf register machine is a leaf machine. -/
theorem leafKid_toAny {c : Name} {dk : MachineData}
    (h : LeafKid mctx mref cctx cref c dk) : LeafKidAny mctx mref cctx cref c dk :=
  { ok := h.ok, body := h.body, calls := h.calls, dom := h.dom, leaf := h.leaf, ss := h.ss,
    outTy := h.outTy, outName := h.outName, outScalar := h.outScalar, entry := h.entry,
    closes := h.closes }

set_option maxHeartbeats 4000000 in
/-- **`portsMatchB` of the RAW full-entry module of a parent (with a
register, calls closed by `closeInstsG`) of LEAF machines, with or without
registers**: `core_portsMatch_raw_leaf` with `LeafKid.slots` dropped. -/
theorem core_portsMatch_raw_leaf_any {c : Name} (d : MachineData) (ok : d.ok = true)
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
    -- every call entry's callee is a leaf machine (a register or not)
    (kid : Nat → MachineData)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      LeafKidAny mctx mref cctx cref (d.shape.insts[k]).1 (kid k))
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
    exact leaf_real_outTys_any (kid k) K.ok K.body K.leaf K.ss K.outTy K.entry K.closes hy
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


/-! ## The one-output closing -/

/-- **`hkidW` for the one-output closing**: with no field list, the strict
width condition compares every output port of a call's child with the
call's binder. -/
theorem hkidW_one {d : MachineData} {nDecl : Nat} {kidOuts : Nat → List OutField}
    (hf : d.shape.instFields = [])
    (hcw : Tools.ShippingCallWidthsStrict.callWidthsStrict d nDecl kidOuts = true)
    (hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingChildIfaceTy.ChildOutTys (kidOuts k) y.1) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs,
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth := by
  intro k hk y hy p hp
  refine Tools.ShippingCallWidthsStrict.hkidW_strict hcw hkidT k hk y hy p hp ?_
  intro f hf'
  rw [hf] at hf'
  simp at hf'

end Tools.ShippingPortsMatchRawLeafAny
