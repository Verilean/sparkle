import Tools.ShippingCallsChildPorts
import Tools.ShippingPortsMatchRaw
import Tools.ShippingMachineInstG

/-! # The ports of the module of a machine whose calls are tied by the GENERAL closing (G1, unit U3, round par/a-15)

`Tools.ShippingCallsChildPorts.core_calls_ports₁` gives
`CallsPorts c d kD b` — the output ports, the masked outputs, the argument
ports and their widths in the wire table — for a machine with a register
whose calls are tied by the ONE-OUTPUT closing (`instFields = []`,
`closeInsts`). This file gives the SAME predicate for the general closing
(`instFields ≠ []`, `closeInstsG`): `mid` (callee `cnt`), `mid2` (callee
`midH`), as children.

What differs, and only this: `closeInstsG` closes
`withClockFor children (closeMachine …)`, whose inputs are the closed
machine's or those with `clk` and `rst` appended
(`Tools.ShippingMachineInstG.withClockFor_inputs`); a non-clock input of the
result is therefore still an input of the closed machine. Everything else of
`core_calls_ports₁`'s proof does not read the closing (`MachineWired`,
`calls_ports`, `CloseCalls.some`).

* `core_calls_portsG`: `CallsPorts c d kD b` from the core run.
* `core_conn_refsG`: every reference connection of an instance of `b` is
  `clk`, `rst`, or a wire of `b` (`core_callConns`).
* `outsMaskedN_of_callsG`: `outsMaskedN b = true` from `CallsPorts`,
  `TypedIn b`, the connections, and "no output port is named `clk` or
  `rst`" (for a child: the second and third conjuncts of `KidFacts.outsIn`).

SCOPE: a machine WITH a register (`hsl`), with calls, `instFields ≠ []`, no
memory callee; the argument split `kD` with the data conditions of
`Tools.ShippingKidsChildIface.kidsChild_iface`.

The proof of `core_calls_portsG` is `core_calls_ports₁`'s, copied, with the
closing-specific lines replaced; if that changes, this copy does not follow.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingCallsPortsG
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
open Tools.ShippingCallsChildPorts (CallsPorts argWidths)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **The ports of the full entry's module of a machine with a register
whose calls are tied by the GENERAL closing**, from its core run. -/
theorem core_calls_portsG {c : Name} (d : MachineData) (ok : d.ok = true)
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
  -- the general closing
  have hG : closeInstsG (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
      (t.inputs.map (·.name)) (d.shape.insts.map (·.2.1)) d.shape.instFields children
      (closeMachine d.shape.layout t', d₀) = some (M, D) := by
    rcases hcc with ⟨hfe, -⟩ | ⟨-, hG, -⟩
    · exact absurd hfe hfne
    · exact hG
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
  -- the closing keeps a subset of the inputs of the closed machine with the
  -- clock and the reset `withClockFor` may append
  obtain ⟨outWs, -, hMin⟩ := Tools.ShippingMachineInstG.closeInstsG_inputs hG
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
    have hpw : p ∈ (withClockFor children (closeMachine d.shape.layout t')).inputs :=
      (List.mem_filter.mp hp1).1
    have hpc : p ∈ (closeMachine d.shape.layout t').inputs := by
      rcases Tools.ShippingMachineInstG.withClockFor_inputs children
        (closeMachine d.shape.layout t') with e | ⟨e, -⟩
      · rw [e] at hpw
        exact hpw
      · rw [e] at hpw
        rcases List.mem_append.mp hpw with h | h
        · exact h
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
          rcases h with h | h
          · exact absurd (congrArg Sparkle.IR.AST.Port.name h) hp3.1
          · exact absurd (congrArg Sparkle.IR.AST.Port.name h) hp3.2
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
of a parent tied by the general closing is the clock, the reset, or a wire
of the module** (`core_callConns`). -/
theorem core_conn_refsG {c : Name} (d : MachineData) (ok : d.ok = true)
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
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∀ cn ∈ conns, ∀ x, cn.2 = Sparkle.IR.AST.Expr.ref x →
        x = "clk" ∨ x = "rst" ∨ x ∈ b.wires.map (·.name) := by
  have hconn := Tools.ShippingPortsMatchRaw.core_callConns d ok hbody hC hslots hdomB hins hfne
    outTy hnomem hB hcore hpost entry closes
  intro mn iname conns hst cn hcm x hc2
  obtain ⟨mc, -, -, hall⟩ := hconn mn iname conns hst
  have hcm' : (cn.1, Sparkle.IR.AST.Expr.ref x) ∈ conns := by
    rw [← hc2]
    exact hcm
  rcases hall cn.1 x hcm' with ⟨-, h⟩ | ⟨hxw, -⟩
  · rcases h with ⟨-, e⟩ | ⟨-, e⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr hxw)

/-- **`outsMaskedN` of the full entry's module of a machine tied by the
general closing**, from its ports' facts, its typing, its connections and
its output ports not being named `clk` or `rst`. -/
theorem outsMaskedN_of_callsG {c : Name} {d : MachineData} {kD : Nat}
    {b : Sparkle.IR.AST.Module} (hP : CallsPorts c d kD b)
    (hT : Tools.ShippingTextTyped.TypedIn b)
    (hO : ∀ p ∈ b.outputs, p.name ≠ "clk" ∧ p.name ≠ "rst")
    (hW : ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∀ cn ∈ conns, ∀ x, cn.2 = Sparkle.IR.AST.Expr.ref x →
        x = "clk" ∨ x = "rst" ∨ x ∈ b.wires.map (·.name)) :
    Tools.ShippingMachineShipsDepth.outsMaskedN b = true := by
  refine Tools.ShippingChildMapCongr.outsMaskedN_of_typed hT.kinds
    (fun p hp => (Tools.ShippingChecksMaskedLeaf.outMasked_eq _ _ p).trans (hP.masked p hp))
    (fun p hp mn iname conns hst cn hcn e => ?_)
  rcases hW mn iname conns hst cn hcn p.name e with h | h | hx
  · exact (hO p hp).1 h
  · exact (hO p hp).2 h
  · obtain ⟨pw, hpw, hn⟩ := List.mem_map.mp hx
    exact hT.ow p hp pw hpw hn

end Tools.ShippingCallsPortsG
