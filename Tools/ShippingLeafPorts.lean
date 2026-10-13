import Tools.ShippingLeafTyped
import Tools.ShippingPortWidthsPure

/-! # The INPUT ports of a leaf machine's module, in the emitter's width map (G1, port matching)

`Tools.ShippingPortsMatchRaw.core_portsMatch_raw` left two hypotheses about
a child's module: `hkidIn` (the emitted width of its `j`-th argument port)
and `hkidClk` (`clk`, `rst` one bit). For a child that is a machine WITHOUT
calls — its module is what its own full entry returned (`RealChild`): the
zero-width cleanup of `closeMachine lay t'`, or the checked merge of that —
both are derived here from the child's run.

* `LeafPorts c d b`: what the run gives about the ports of the returned
  module `b` (no statement of `b`'s body is mentioned):
  - `wal`: every wire is an allocated name or the `next…` name of one;
  - `pos`: the binders' vector widths are positive (from `d.ok`);
  - `args`: the non-clock inputs are the ports of the declared binders
    (`MachineWired`'s leaf clause; `machPorts` over the binders before the
    slots and `let`s);
  - `argW`: each non-clock input's name has, in the WIRE table, its type's
    width (`MachineWired`'s cleanup clause for a machine without calls);
  - `ins`: the inputs are allocated names, followed by `clk`, `rst` exactly
    when there are slots (`closeMachine`).
* `leaf_run_ports`: `LeafPorts c d b` over every run of the full entry of a
  machine without calls. The proof is `Tools.ShippingLeafTyped.leaf_run_typedIn`'s
  prelude (copied), keeping other clauses of `MachineWired`; the cleanup and
  the checked merge keep inputs and wires (`dropZW_inputs`,
  `mergeChecked_ports`), the cleanup keeps the wire table.
* `leaf_real_ports`: the same from a `RealChild` witness.
* `LeafPorts.inWidths` (= `hkidIn`): the `j`-th argument port `q` has
  `(declWidths d)[j]? = some wd ∧ weS b q.name = wd`.
* `LeafPorts.clk` (= `hkidClk`): `isSeqChild b = true →
  weS b "clk" = 1 ∧ weS b "rst" = 1`. `isSeqChild b` — an input named `clk`
  or `rst` — holds of a leaf machine's module exactly when it has slots
  (`LeafPorts.seq_iff`): the other inputs are allocated names.
* `leaf_real_inWidths`, `leaf_real_clk`: the two from a `RealChild`.

Is an argument port a WIRE of the module? Yes: a transition input is a wire
(`closedTransition_of_run`), the closing keeps the wires, the cleanup drops
zero-width wires only, the merge keeps the wires. The proof does not use
that chain: `argW` gives the port's name a POSITIVE width in the wire table
(positive binders), and a name of positive wire-table width is a wire on
which the two tables agree (`pos_wire`). `clk` / `rst` are not wires; the
emitter's map reads wires first, then inputs: no wire sanitizes to `clk` /
`rst`, and no earlier input does.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingLeafPorts
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingPortWidthsPure

/-- What a leaf machine's run gives about the ports of its module. -/
structure LeafPorts (c : Name) (d : MachineData) (b : Sparkle.IR.AST.Module) : Prop where
  /-- the wires: allocated names and `next…` names -/
  wal : ∀ p ∈ b.wires, Sparkle.IR.NameHints.Allocated p.name ∨
    ∃ y, Sparkle.IR.NameHints.Allocated y ∧ p.name = nextName y
  /-- positive vector binders -/
  pos : PositiveBinders d.shape.binders
  /-- the non-clock inputs are the declared binders' ports -/
  args : ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)),
    ids.length = d.shape.binders.length ∧
    inPortsOf b = machPorts c ids cache (d.shape.binders.take (declN d))
  /-- a non-clock input's name has its type's width in the wire table -/
  argW : ∀ p ∈ inPortsOf b,
    (p.ty = Sparkle.IR.Type.HWType.bit → Tools.ShippingEntrySoundness.weOf b p.name = 1) ∧
    ∀ k, p.ty = Sparkle.IR.Type.HWType.bitVector k →
      Tools.ShippingEntrySoundness.weOf b p.name = k
  /-- the inputs: allocated names, then the clock and the reset with slots -/
  ins : ∃ A : List Port, (∀ p ∈ A, Sparkle.IR.NameHints.Allocated p.name) ∧
    (d.shape.layout.slots.isEmpty = true → b.inputs = A) ∧
    (d.shape.layout.slots.isEmpty = false → b.inputs = A ++
      [({ name := "clk", ty := .bit } : Port), ({ name := "rst", ty := .bit } : Port)])

/-! ## Consequences (no run) -/

/-- **`hkidIn` for a leaf child**: the emitted width of the `j`-th argument
port is the `j`-th declared width. -/
theorem LeafPorts.inWidths {c : Name} {d : MachineData} {b : Sparkle.IR.AST.Module}
    (h : LeafPorts c d b) {j : Nat} {q : Port} (hq : (inPortsOf b)[j]? = some q) :
    ∃ wd, (declWidths d)[j]? = some wd ∧ Tools.ShippingDesignSV.weS b q.name = wd := by
  obtain ⟨ids, cache, hlen, hP⟩ := h.args
  have hle : (d.shape.binders.take (declN d)).length ≤ ids.length := by
    rw [List.length_take]
    omega
  have hty : (inPortsOf b).map (fun p => p.ty) =
      ((d.shape.binders.take (declN d)).filter nonDom).map (fun bn => kindTy bn.2) := by
    rw [hP]
    exact machPorts_tys c ids cache _ hle
  have hwn : ∀ p ∈ b.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name :=
    fun p hp => (wire_ne_clk (h.wal p hp)).1
  exact inPort_weS hwn hty
    (fun bn hbn => kindTy_pos h.pos (List.mem_of_mem_take hbn)) h.argW hq

/-- A leaf machine's module has a clock or reset input exactly when the
machine has slots. -/
theorem LeafPorts.seq_iff {c : Name} {d : MachineData} {b : Sparkle.IR.AST.Module}
    (h : LeafPorts c d b) :
    isSeqChild b = true ↔ d.shape.layout.slots.isEmpty = false := by
  obtain ⟨A, hA, h0, h1⟩ := h.ins
  constructor
  · intro hs
    cases hsl : d.shape.layout.slots.isEmpty with
    | false => rfl
    | true =>
      have hin : ∀ p ∈ b.inputs, Sparkle.IR.NameHints.Allocated p.name := by
        intro p hp
        rw [h0 hsl] at hp
        exact hA p hp
      exact absurd ((seq_of_alloc_inputs hin).symm.trans hs) Bool.false_ne_true
  · intro hsl
    have hi := h1 hsl
    have hmem : ({ name := "clk", ty := .bit } : Port) ∈ b.inputs := by
      rw [hi]
      exact List.mem_append_right _ (List.Mem.head _)
    have hb : (({ name := "clk", ty := .bit } : Port).name == "clk" ||
        ({ name := "clk", ty := .bit } : Port).name == "rst") = true := by
      first
        | (rw [Bool.or_eq_true]; exact Or.inl (beq_self_eq_true _))
        | simp
    show (b.inputs.any fun p => p.name == "clk" || p.name == "rst") = true
    exact List.any_eq_true.mpr ⟨({ name := "clk", ty := .bit } : Port), hmem, hb⟩

/-- **`hkidClk` for a leaf child**: `clk` and `rst` are one bit in the
emitter's width map of a module with a clock or reset input. -/
theorem LeafPorts.clk {c : Name} {d : MachineData} {b : Sparkle.IR.AST.Module}
    (h : LeafPorts c d b) (hs : isSeqChild b = true) :
    Tools.ShippingDesignSV.weS b "clk" = 1 ∧ Tools.ShippingDesignSV.weS b "rst" = 1 := by
  have hsl := h.seq_iff.mp hs
  obtain ⟨A, hA, -, h1⟩ := h.ins
  exact weS_clk_rst (A := A) (X := []) h.wal hA (h1 hsl)

/-! ## From a run -/

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **The ports of a leaf machine's returned module**, over every run of the
full entry. -/
theorem leaf_run_ports {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closesM : MachineCloses mctx mref cctx cref c d.shape) :
    LeafPorts c d b := by
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
  obtain ⟨Bc, coreW, hbodyc, typedc, namedc, namesc, inWc, inNdc, wNdc, slotsc, hcoreW⟩ :=
    Tools.ShippingClosedTransitionTyped.closedTransition_of_run d ok hbody hC hSS hdomB run hcl
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
  -- the leaf clause (position 9) and the cleanup clause for a machine
  -- without calls (position 11) of `MachineWired`
  obtain ⟨-, -, -, -, -, -, -, -, hleafIn, -, hclean, -⟩ := wired
  -- in the cleanup clause: the wire table is kept (1.2), an input other than
  -- the clock and the reset has its type's width in the wire table (8)
  obtain ⟨⟨-, hzw, -, -⟩, -, -, -, -, -, -, hinWd, -⟩ := hclean hno outTy
  obtain ⟨-, -, hwCM, -, -, -, -, -⟩ :=
    Tools.ShippingCloseMachineTyped.closeMachine_typed (lay := d.shape.layout) hbodyc typedc
      namedc namesc inWc inNdc wNdc slotsc
      (fun f hf => by rw [hcoreW]; exact hfit f hf)
      (fun o ho => by rw [hcoreW]; exact houtfit o ho) outsOk outTy
  have hM' : M = closeMachine d.shape.layout t' := hMeq
  -- the returned module's inputs, wires and wire table are the raw module's
  have hbi : b.inputs = M.inputs := by
    rcases hpost with h | h
    · rw [h]
      exact Tools.ShippingOutsExtractedParts.dropZW_inputs M
    · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).1]
      exact Tools.ShippingOutsExtractedParts.dropZW_inputs M
  have hbw : b.wires = (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).wires := by
    rcases hpost with h | h
    · rw [h]
    · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).2.2]
  have hweb : Tools.ShippingEntrySoundness.weOf b = Tools.ShippingEntrySoundness.weOf M :=
    (Tools.ShippingRegisterSoundness.weOf_congr_wires hbw).trans hzw
  have hwsub : ∀ p ∈ b.wires, p ∈ (closeMachine d.shape.layout t').wires := by
    intro p hp
    rw [hbw] at hp
    have h1 := Tools.ShippingClosedTyped.dropZW_wires_sub hp
    rw [hM'] at h1
    exact h1
  have hbIn : inPortsOf b = inPortsOf M := by
    unfold Tools.ShippingInstStmtG.inPortsOf
    rw [hbi]
  -- the closed machine's inputs
  obtain ⟨hcm0, hcm1⟩ :=
    closeMachine_inputs (t := t') (lay := d.shape.layout) hbodyc
  have hAal : ∀ p ∈ t'.inputs.take (t'.inputs.length - d.shape.layout.slots.length),
      Sparkle.IR.NameHints.Allocated p.name :=
    fun p hp => namesc p (inWc p (List.mem_of_mem_take hp))
  refine { wal := ?_, pos := hposv, args := ?_, argW := ?_, ins := ?_ }
  · intro p hp
    exact hwCM p (hwsub p hp)
  · have h9 := hleafIn hno
    exact ⟨ids, cache, hlenIds, hbIn.trans h9⟩
  · intro p hp
    have hp' : p ∈ M.inputs.filter (fun p => p.name != "clk" && p.name != "rst") := by
      rw [hbIn] at hp
      exact hp
    obtain ⟨hp1, hp2⟩ := List.mem_filter.mp hp'
    have hp3 : (p.name != "clk" && p.name != "rst") = true := hp2
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hp3
    have h := hinWd p hp1 hp3.1 hp3.2
    rw [hweb]
    constructor
    · intro hty
      rw [hty] at h
      exact h
    · intro k hty
      rw [hty] at h
      exact h
  · refine ⟨t'.inputs.take (t'.inputs.length - d.shape.layout.slots.length), hAal, ?_, ?_⟩
    · intro hs
      rw [hbi, hM']
      exact hcm0 hs
    · intro hs
      rw [hbi, hM']
      exact hcm1 hs

/-- The same from a `RealChild` witness. -/
theorem leaf_real_ports {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChild mref cref c y) : LeafPorts c d y.1 := by
  obtain ⟨mctx', cctx', w, w', hw, hr⟩ := h.inv
  exact leaf_run_ports d ok hbody hC hdomB hno hSS outTy hw hr
    (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx')

/-- **`hkidIn` of `core_portsMatch_raw` for a real leaf child.** -/
theorem leaf_real_inWidths {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChild mref cref c y) :
    ∀ (j : Nat) (q : Port), (inPortsOf y.1)[j]? = some q →
      ∃ wd, (declWidths d)[j]? = some wd ∧ Tools.ShippingDesignSV.weS y.1 q.name = wd :=
  fun _ _ hq =>
    (leaf_real_ports d ok hbody hC hdomB hno hSS outTy entry closes h).inWidths hq

/-- **`hkidClk` of `core_portsMatch_raw` for a real leaf child.** -/
theorem leaf_real_clk {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChild mref cref c y) :
    isSeqChild y.1 = true →
      Tools.ShippingDesignSV.weS y.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y.1 "rst" = 1 :=
  fun hs => (leaf_real_ports d ok hbody hC hdomB hno hSS outTy entry closes h).clk hs

end Tools.ShippingLeafPorts
