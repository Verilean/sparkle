import Tools.ShippingOneOutConns
import Tools.ShippingChecksMaskedLeaf
import Tools.ShippingMachineDepthChild
import Tools.ShippingPortWidthsPure
import Tools.ShippingChildIfaceTy
import Tools.ShippingChildMapCongr

/-! # The ports of the module of a machine WITH one-output calls, from its core run (G1, unit U2, round par/a-13)

What `Tools.ShippingLeafPorts.leaf_run_ports`, `Tools.ShippingChildIfaceTy.leaf_run_outputs`
and `Tools.ShippingChecksMaskedLeaf.leaf_run_masked` give for a machine
WITHOUT calls (each asks `shape.insts = []` and reads `MachineWired`'s
clauses that are conditional on it), for a machine with a register whose
calls are tied by the ONE-OUTPUT closing (`instFields = []`), as ONE
predicate over the full entry's module `b`:

* `CallsPorts c d kD b`
  - `outs`: the output ports are the layout's fields, with their types
    (`MachineWired`'s output clause, unconditional);
  - `masked`: every output port is assigned once by a self-masked expression
    within its width (`closedBody_masked_of_run` on the closed machine; the
    closing adds instance statements, which write nothing, and permutes:
    `outMaskedB_perm_insts`);
  - `args`: the non-clock inputs are the ports of the declaration's own
    binders `d.bsIn.take kD` (`Tools.ShippingMachineDepthChild.calls_ports`;
    for a machine with calls `declN d` would count the call binders too, so
    the list is NOT `Tools.ShippingPortWidthsPure.declWidths d`);
  - `argW`: a non-clock input of positive type width has that width in the
    wire table. NOT a clause of `MachineWired` for a machine with calls (its
    clause is under `insts = []`); derived here: the closing keeps a subset
    of the closed machine's inputs (`closeInsts_inputs`), those before the
    clock are transition inputs (`closeMachine_inputs`), a transition input
    is a transition wire (`closedTransition_of_run`), of distinct names
    (`weOf_of_port`), and the closed machine keeps the transition's positive
    widths (`closeMachine_typed`'s frame);
  - `pos`: the binders' vector widths are positive (`d.ok`).
* `core_calls_ports₁`: `CallsPorts c d kD b` from the core run.
* `argWidths d kD`: the widths of the port types of the declaration's own
  non-domain binders — the DATA a parent's `callArgsOk` is decided against.
* `CallsPorts.inWidths` (= `hkidIn` of `core_portsMatch_raw`): the `j`-th
  argument port has `(argWidths d kD)[j]? = some wd ∧ weS b q.name = wd`.
* `core_conn_wires₁`: every reference connection of an instance of `b` is a
  wire of `b` (`core_callConns₁`); `core_outsMaskedN₁`:
  `outsMaskedN b = true` (with `TypedIn b`: no wire has an output port's
  name).

SCOPE: a machine WITH a register (`hsl`), with calls, `instFields = []`,
no memory callee; the argument split `kD` with the data conditions of
`Tools.ShippingKidsChildIface.kidsChild_iface`. Not the general closing
(`closeInstsG` adds `withClockFor`'s inputs: not read here).

The run prelude of `core_calls_ports₁` is
`Tools.ShippingClosedTyped.core_closed_typedIn`'s, copied; if that changes,
this copy does not follow.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingCallsChildPorts
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
open Tools.ShippingPortWidthsPure

/-- **The widths of the argument ports of a machine with calls**, as data:
the port types of its own non-domain binders (`d.bsIn.take kD`). -/
def argWidths (d : MachineData) (kD : Nat) : List Nat :=
  (((d.bsIn.take kD).filter nonDom).map fun bn => kindTy bn.2).map
    fun ty : Sparkle.IR.Type.HWType => ty.bitWidth

/-- What the core run of a machine with one-output calls gives about the
ports of its full-entry module. -/
structure CallsPorts (c : Name) (d : MachineData) (kD : Nat) (b : Sparkle.IR.AST.Module) :
    Prop where
  /-- the output ports are the layout's fields, with their types -/
  outs : b.outputs = d.shape.layout.outs.map (fun o => ({ name := o.name, ty := o.ty } : Port))
  /-- every output port is assigned once, self-masked, within its width -/
  masked : ∀ p ∈ b.outputs,
    Sparkle.IR.RefineCheck.outMaskedB (Sparkle.IR.RegDedup.declWidth b) b.body p = true
  /-- the non-clock inputs are the declaration's own binders' ports -/
  args : ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)),
    ids.length = d.shape.binders.length ∧
    inPortsOf b = machPorts c ids cache (d.bsIn.take kD)
  /-- a non-clock input of positive width has its type's width in the wire table -/
  argW : ∀ p ∈ inPortsOf b,
    (p.ty = Sparkle.IR.Type.HWType.bit → Tools.ShippingEntrySoundness.weOf b p.name = 1) ∧
    ∀ k, 0 < k → p.ty = Sparkle.IR.Type.HWType.bitVector k →
      Tools.ShippingEntrySoundness.weOf b p.name = k
  /-- positive vector binders -/
  pos : PositiveBinders d.shape.binders

/-- **`hkidIn` for a child with one-output calls**: the emitted width of the
`j`-th argument port is the `j`-th of `argWidths`. -/
theorem CallsPorts.inWidths {c : Name} {d : MachineData} {kD : Nat}
    {b : Sparkle.IR.AST.Module} (h : CallsPorts c d kD b)
    (hwn : ∀ p ∈ b.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    {j : Nat} {q : Port} (hq : (inPortsOf b)[j]? = some q) :
    ∃ wd, (argWidths d kD)[j]? = some wd ∧ Tools.ShippingDesignSV.weS b q.name = wd := by
  obtain ⟨ids, cache, hlen, hP⟩ := h.args
  have hBl : d.bsIn.length ≤ d.shape.binders.length := by
    simp only [MachineData.bsIn, List.length_take]
    omega
  have hle : (d.bsIn.take kD).length ≤ ids.length := by
    rw [List.length_take, hlen]
    omega
  have hty : (inPortsOf b).map (fun p => p.ty) =
      ((d.bsIn.take kD).filter nonDom).map (fun bn => kindTy bn.2) := by
    rw [hP]
    exact machPorts_tys c ids cache _ hle
  have hmemB : ∀ bn ∈ d.bsIn.take kD, bn ∈ d.shape.binders := by
    intro bn hbn
    have h1 : bn ∈ d.shape.binders.take d.nIn := List.mem_of_mem_take hbn
    exact List.mem_of_mem_take h1
  have hpos : ∀ bn ∈ d.bsIn.take kD, 0 < (kindTy bn.2).bitWidth :=
    fun bn hbn => kindTy_pos h.pos (hmemB bn hbn)
  -- every argument port has a positive type width
  have hpp : ∀ p ∈ inPortsOf b, 0 < p.ty.bitWidth := by
    intro p hp
    have h1 : p.ty ∈ (inPortsOf b).map (fun p => p.ty) := List.mem_map.mpr ⟨p, hp, rfl⟩
    rw [hty] at h1
    obtain ⟨bn, hbn, e⟩ := List.mem_map.mp h1
    rw [← e]
    exact hpos bn (List.mem_filter.mp hbn).1
  unfold argWidths
  refine inPort_weS hwn hty hpos (fun p hp => ?_) hq
  obtain ⟨hbit, hvec⟩ := h.argW p hp
  refine ⟨hbit, fun k hk => hvec k ?_ hk⟩
  have h0 := hpp p hp
  rw [hk] at h0
  exact h0

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **The ports of the full entry's module of a machine with a register and
one-output calls**, from its core run. -/
theorem core_calls_ports₁ {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hsl : d.shape.layout.slots ≠ [])
    -- the argument split (the data conditions of `kidsChild_iface`)
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    CallsPorts c d kD b := by
  -- the body, the output ports, the inputs and the wires of the full
  -- entry's module are the raw module's
  have hkf := Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy
    hnomem hB hcore hpost entry closes
  have hbb : b.body = M.body := hkf.2.1
  have hbo : b.outputs = M.outputs := hkf.2.2.1
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
  -- the run
  obtain ⟨_, bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
    machine_run_of_core hcore entry hB
  have hne := closes bb _ _ _ hw9 hd9 hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ := synthesizeMachineCertified_runs hw9 hrun9
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, hreal⟩
  · exact absurd hno hins
  -- the one-output closing
  have hI : closeInsts (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
      (t.inputs.map (·.name)) (d.shape.insts.map (·.2.1)) children
      (closeMachine d.shape.layout t', d₀) = some (M, D) := by
    rcases hcc with ⟨-, hI⟩ | ⟨hfe, -, -⟩
    · exact hI
    · exact absurd hf hfe
  obtain ⟨hMw, -, -, L, hLinst, hperm, -, -, -, -, -, -, -⟩ := hcc.some
  -- the masked outputs of the closed machine
  have hMask := Tools.ShippingClosedMasked.closedBody_masked_of_run d ok hbody hC hslots hdomB
    run hcl
  -- the data conditions
  have ok' := ok
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok'
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, _, _, _, _, _, _, _, _⟩ := ok'
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
  have layW : Tools.ShippingMachineClose.Zip₂
      (fun (f : SlotField) (b : Name × MixedGateBinder) =>
        f.width = machWidth b.2 ∧ b.2 ≠ .domain ∧ f.init < 2 ^ f.width)
      d.shape.layout.slots d.slotBs :=
    zip_of_all (by
      intro a b h
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h) layB
  -- the raw module's wiring: its outputs, its argument ports, its cleanup
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeMachineCertified_sound hrun9.mreturns d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, -, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, -, -, -, hargP, -⟩ :=
    Tools.ShippingMachineDepthChild.calls_ports wired hlenIds hsl (fun o ho => (outsOk o ho).2)
      kD hkD hIlen hSL hSlen hLlen hNIn
  obtain ⟨-, -, -, -, -, -, -, houtsM, -, -, -, -, -, -, -, hcleanAny, -, -⟩ := wired
  obtain ⟨-, hzw, -, -⟩ := hcleanAny outTy
  -- the `let`-closed transition and the closed machine
  obtain ⟨Bc, coreW, hbodyc, typedc, namedc, namesc, inWc, inNdc, wNdc, slotsc, hcoreW⟩ :=
    Tools.ShippingClosedTransitionTyped.closedTransition_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨hfrCM, -, -, -, -, -, -, -⟩ :=
    Tools.ShippingCloseMachineTyped.closeMachine_typed (lay := d.shape.layout) hbodyc typedc
      namedc namesc inWc inNdc wNdc slotsc
      (fun f hf => by rw [hcoreW]; exact hfit f hf)
      (fun o ho => by rw [hcoreW]; exact houtfit o ho) outsOk outTy
  -- the wire table of the full entry's module is the closed machine's
  have hweb : Tools.ShippingEntrySoundness.weOf b =
      Tools.ShippingEntrySoundness.weOf (closeMachine d.shape.layout t') :=
    ((Tools.ShippingRegisterSoundness.weOf_congr_wires hbw).trans hzw).trans
      (Tools.ShippingRegisterSoundness.weOf_congr_wires hMw)
  have hbouts : b.outputs = d.shape.layout.outs.map
      (fun o => ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port)) := hbo.trans houtsM
  -- the closing keeps a subset of the closed machine's inputs
  obtain ⟨outWs, -, hMin⟩ := Tools.ShippingMachineInst.closeInsts_inputs hI
  obtain ⟨hcm0, hcm1⟩ :=
    closeMachine_inputs (t := t') (lay := d.shape.layout) hbodyc
  have hinP : inPortsOf b = machPorts c ids cache (d.bsIn.take kD) := by
    unfold inPortsOf
    rw [hbi]
    exact hargP
  refine { outs := hbouts, masked := ?_, args := ⟨ids, cache, hlenIds, hinP⟩, argW := ?_,
           pos := hposv }
  · -- the masked outputs
    intro p hp
    rw [hbouts] at hp
    obtain ⟨o, ho, e⟩ := List.mem_map.mp hp
    rw [← e, hbb]
    exact Tools.ShippingChildMapCongr.outMaskedB_perm_insts hLinst hperm
      (hMask _ o ho (outTy o ho))
  · -- an argument port's width in the wire table
    intro p hp
    have hp' : p ∈ M.inputs.filter (fun p => p.name != "clk" && p.name != "rst") := by
      unfold inPortsOf at hp
      rw [hbi] at hp
      exact hp
    obtain ⟨hp1, hp2⟩ := List.mem_filter.mp hp'
    have hp3 : (p.name != "clk" && p.name != "rst") = true := hp2
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hp3
    rw [hMin] at hp1
    have hpc : p ∈ (closeMachine d.shape.layout t').inputs := (List.mem_filter.mp hp1).1
    have hpt : p ∈ t'.inputs := by
      cases hs : d.shape.layout.slots.isEmpty with
      | true =>
        rw [hcm0 hs] at hpc
        exact List.mem_of_mem_take hpc
      | false =>
        rw [hcm1 hs] at hpc
        rcases List.mem_append.mp hpc with h | h
        · exact List.mem_of_mem_take h
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
          rcases h with rfl | rfl
          · exact absurd rfl hp3.1
          · exact absurd rfl hp3.2
    have hw0 := weOf_of_port wNdc (inWc p hpt)
    constructor
    · intro hty
      rw [hty] at hw0
      have hw1 : Tools.ShippingEntrySoundness.weOf t' p.name = 1 := hw0
      have hpos1 : 0 < Tools.ShippingEntrySoundness.weOf t' p.name := by
        rw [hw1]
        exact Nat.one_pos
      rw [hweb, hfrCM _ hpos1]
      exact hw1
    · intro k hk hty
      rw [hty] at hw0
      have hw1 : Tools.ShippingEntrySoundness.weOf t' p.name = k := hw0
      have hposk : 0 < Tools.ShippingEntrySoundness.weOf t' p.name := by
        rw [hw1]
        exact hk
      rw [hweb, hfrCM _ hposk]
      exact hw1

set_option maxHeartbeats 4000000 in
/-- **Every reference connection of an instance of the full entry's module
of a one-output parent is a wire of the module.** -/
theorem core_conn_wires₁ {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∀ cn ∈ conns, ∀ x, cn.2 = Sparkle.IR.AST.Expr.ref x → x ∈ b.wires.map (·.name) := by
  have hconn := Tools.ShippingOneOutConns.core_callConns₁ d ok hbody hC hslots hdomB hins hf
    outTy hnomem hB hcore hpost entry closes
  intro mn iname conns hst cn hcm x hc2
  obtain ⟨k, hk, y, outW, argWs, outP, hre, hfind, houts, hns, hall, hmemO,
    ⟨hxo, -⟩, hargsC⟩ := hconn mn iname conns hst
  have hcm' : (cn.1, Sparkle.IR.AST.Expr.ref x) ∈ conns := by
    rw [← hc2]
    exact hcm
  by_cases hpo : cn.1 = outP.name
  · rcases hall _ hcm' with e | ⟨q, -, aw, -, e, hqo⟩
    · have h2' : Sparkle.IR.AST.Expr.ref x = Sparkle.IR.AST.Expr.ref outW :=
        congrArg Prod.snd e
      have hx : x = outW := by
        cases h2'
        rfl
      rw [hx]
      exact hxo
    · exact absurd ((congrArg Prod.fst e).symm.trans hpo) hqo
  · obtain ⟨j, q, a, bn, -, -, -, -, hxw, -⟩ := hargsC cn.1 x hcm' hpo
    exact hxw

/-- **`outsMaskedN` of the full entry's module of a machine with one-output
calls**, from its ports' facts, its typing and its connections. -/
theorem outsMaskedN_of_calls {c : Name} {d : MachineData} {kD : Nat}
    {b : Sparkle.IR.AST.Module} (hP : CallsPorts c d kD b)
    (hT : Tools.ShippingTextTyped.TypedIn b)
    (hW : ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∀ cn ∈ conns, ∀ x, cn.2 = Sparkle.IR.AST.Expr.ref x → x ∈ b.wires.map (·.name)) :
    Tools.ShippingMachineShipsDepth.outsMaskedN b = true := by
  refine Tools.ShippingChildMapCongr.outsMaskedN_of_typed hT.kinds
    (fun p hp => (Tools.ShippingChecksMaskedLeaf.outMasked_eq _ _ p).trans (hP.masked p hp))
    (fun p hp mn iname conns hst cn hcn e => ?_)
  have hx := hW mn iname conns hst cn hcn p.name e
  obtain ⟨pw, hpw, hn⟩ := List.mem_map.mp hx
  exact hT.ow p hp pw hpw hn

end Tools.ShippingCallsChildPorts
