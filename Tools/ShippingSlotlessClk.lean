import Tools.ShippingCoreClk
import Tools.ShippingChecksRaw
import Tools.ShippingMachineInstG
import Tools.ShippingCallsAssemblyG
import Tools.ShippingTransitionPortTys
import Tools.ShippingLeafPorts
import Tools.ShippingPortsMatchRawLeaf
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md).

/-! # `clk` and `rst` of a parent WITHOUT a register, from a sequential child's closing (G1, unit U5a, round par/a-20)

`Tools.ShippingCoreClk.core_clk` and `Tools.ShippingChecksRaw.core_raw_facts`
derive the clock and the reset of the full entry's module of a machine with
calls from the parent's OWN register (`hsl : d.shape.layout.slots ≠ []`):
`MachineWired`'s input clause is

    (ports.take K ++ (if slots.isEmpty then [] else [clk, rst]) ++ extra).filter …

with `extra = [] ∨ (extra = [clk, rst] ∧ slots = [])`, and the clause does
not say which disjunct holds. For a parent without a register the two ports
come from `withClockFor children (closeMachine …)`
(`Sparkle/IR/MachineInstG.lean:73`), which `closeInstsG` closes: they are
appended when some child's module has a `clk` or `rst` input
(`isSeqChild`).

This file gives the SECOND derivation of the same two facts:

* `SeqKid mref cref d`: some call entry of `d` whose every real child is
  sequential (`isSeqChild y.1 = true`). For a leaf register machine callee it
  follows from `LeafKid` (`seqKid_of_leafAt`: `LeafPorts.seq_iff`).
* `core_seqKid_inputs`: `"clk"` and `"rst"` are inputs of the core run's
  module, from `SeqKid` — by `closeInstsG_inputs`, `withClockFor_clk`, and
  the call ports being transition inputs, hence allocated names
  (`transitionPortTys_of_run`), hence neither `clk` nor `rst`. No condition
  on the slots.
* `core_slotless_seq`: for `slots = []` and `SeqKid` — the three conjuncts
  of `core_raw_facts` and the conclusion of `core_clk`. The wiring's `extra`
  is `[clk, rst]`: with `extra = []` every input would be an allocated name,
  and `"rst"` is an input.
* `core_raw_factsS`, `core_clkS`: the statements of `core_raw_facts` /
  `core_clk` with `hsl` replaced by

      d.shape.layout.slots ≠ [] ∨ SeqKid mref cref d

  The first disjunct IS the built theorem (the proof case-splits on
  `slots = []` and applies `core_raw_facts` / `core_clk` when there is a
  slot); nothing about a parent with a register is proved anew.

The prelude of `core_slotless_seq` is `core_clk`'s (copied, as every file of
this chain copies it), keeping two more components of `MachineWired`.

NOT covered: a parent without a register whose children are ALL
combinational (no `rst` input at all: `A-oneout.md` §13.6), memory children
(`hnomem`), the one-output closing (`hfne`).

WRITTEN, NOT BUILT. -/
namespace Tools.ShippingSlotlessClk
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

/-- **Some call entry's children are sequential**: there is a call entry `k`
of `d` such that the module of every real child of its callee has a `clk` or
`rst` input. -/
abbrev SeqKid (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)
    (d : MachineData) : Prop :=
  ∃ (k : Nat) (hk : k < d.shape.insts.length), ∀ y : Res,
    RealChild mref cref (d.shape.insts[k]).1 y → isSeqChild y.1 = true

/-! ## Pure: the input list with the clock and the reset as `extra` -/

/-- The input list of a machine with calls and NO slot whose clock and reset
are the wiring's `extra` (`MachineWired`'s input clause), with the two
exposed. -/
theorem inputs_tail_shape {P E X I : List Port} {f : Port → Bool}
    (hI : I = (P ++ E ++ X).filter f) (hE : E = [])
    (hX : X = [({ name := "clk", ty := .bit } : Port), ({ name := "rst", ty := .bit } : Port)])
    (hc : f ({ name := "clk", ty := .bit } : Port) = true)
    (hr : f ({ name := "rst", ty := .bit } : Port) = true) :
    I = P.filter f ++ (({ name := "clk", ty := .bit } : Port) ::
      ({ name := "rst", ty := .bit } : Port) :: []) := by
  have e1 : ([({ name := "clk", ty := .bit } : Port),
      ({ name := "rst", ty := .bit } : Port)]).filter f =
      [({ name := "clk", ty := .bit } : Port), ({ name := "rst", ty := .bit } : Port)] := by
    rw [List.filter_cons_of_pos (p := f) (a := ({ name := "clk", ty := .bit } : Port))
        (l := [({ name := "rst", ty := .bit } : Port)]) hc,
      List.filter_cons_of_pos (p := f) (a := ({ name := "rst", ty := .bit } : Port))
        (l := []) hr] <;> rfl
  subst hE
  subst hX
  rw [hI, List.append_nil, List.filter_append, e1]

/-- `weS_clk_rst` over the filtered input list of a machine with calls and no
slot, its clock and reset the wiring's `extra`
(`Tools.ShippingPortWidthsPure.weS_clk_rst_filtered` is the same over the
slots' `[clk, rst]`). -/
theorem weS_clk_rst_tail {m : Sparkle.IR.AST.Module} {P0 E X : List Port} {K : Nat}
    {f : Port → Bool}
    (hI : m.inputs = (P0.take K ++ E ++ X).filter f) (hE : E = [])
    (hX : X = [({ name := "clk", ty := .bit } : Port), ({ name := "rst", ty := .bit } : Port)])
    (hc : f ({ name := "clk", ty := .bit } : Port) = true)
    (hr : f ({ name := "rst", ty := .bit } : Port) = true)
    (hw : ∀ p ∈ m.wires, Sparkle.IR.NameHints.Allocated p.name ∨
      ∃ y, Sparkle.IR.NameHints.Allocated y ∧ p.name = nextName y)
    (hP : ∀ p ∈ P0, Sparkle.IR.NameHints.Allocated p.name) :
    Tools.ShippingDesignSV.weS m "clk" = 1 ∧ Tools.ShippingDesignSV.weS m "rst" = 1 :=
  Tools.ShippingPortWidthsPure.weS_clk_rst (A := (P0.take K).filter f) (X := []) hw
    (fun p hp => hP p (List.mem_of_mem_take (List.mem_filter.mp hp).1))
    (inputs_tail_shape hI hE hX hc hr)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## `SeqKid` of a parent of a leaf register machine -/

/-- **A call entry whose callee is a leaf register machine is a sequential
child**: every real child of a machine without calls and with slots has the
clock and the reset among its inputs (`LeafPorts.seq_iff`). -/
theorem seqKid_of_leafAt {d : MachineData} (k : Nat) (hk : k < d.shape.insts.length)
    {dk : MachineData} (K : LeafKid mctx mref cctx cref (d.shape.insts[k]).1 dk) :
    SeqKid mref cref d := by
  have hne : dk.shape.layout.slots.isEmpty = false := by
    cases hs : dk.shape.layout.slots with
    | nil => exact absurd hs K.slots
    | cons _ _ => rfl
  exact Exists.intro k (Exists.intro hk (fun y hy =>
    (Tools.ShippingLeafPorts.leaf_real_ports (nDecl := dk.nIn) dk K.ok K.body K.calls K.dom
      K.leaf K.ss K.outTy K.entry K.closes hy).seq_iff.mpr hne))

/-! ## The clock and the reset are inputs, from the closing -/

set_option maxHeartbeats 4000000 in
/-- **`clk` and `rst` are inputs of the core run's module of a machine one of
whose call entries is a sequential child** (general closing): `closeInstsG`
closes `withClockFor children (closeMachine …)`, which has the two ports
when a child is sequential; the closing removes the call ports only, and
those are transition inputs — allocated names. No condition on the slots. -/
theorem core_seqKid_inputs {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hseq : SeqKid mref cref d)
    {w w1 : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    "clk" ∈ M.inputs.map (·.name) ∧ "rst" ∈ M.inputs.map (·.name) := by
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
  -- the sequential child among the run's children
  obtain ⟨k, hk, hsk⟩ := hseq
  obtain ⟨hlenC, hall⟩ := hreal
  obtain ⟨y, hy, hor⟩ := hall k hk
  have hyR : RealChild mref cref (d.shape.insts[k]).1 y := by
    rcases hor with hmem | hre
    · rw [Tools.ShippingChildInv.nomem_tag hnomem hk] at hmem
      cases hmem
    · exact hre
  have hys : isSeqChild y.1 = true := hsk y hyR
  have hyc : y ∈ children := List.mem_of_getElem? hy
  obtain ⟨⟨pc, hpc, hpcn⟩, ⟨pr, hpr, hprn⟩⟩ :=
    withClockFor_clk (children := children) (m := closeMachine d.shape.layout t') hyc hys
  -- the closing keeps the clocked module's inputs but the call ports
  obtain ⟨outWs, hmap, hMin⟩ := Tools.ShippingMachineInstG.closeInstsG_inputs hG
  -- the call ports are transition inputs: wires, allocated names
  obtain ⟨-, hwalloc, hinW, -⟩ :=
    Tools.ShippingTransitionPortTys.transitionPortTys_of_run d ok hbody hC hslots hdomB run
  have hOW : ∀ x ∈ outWs, x ∈ t.inputs.map (·.name) := by
    intro x hx
    obtain ⟨hlen, hget⟩ := Tools.ShippingMachineInst.mapM_some _ _ _ hmap
    obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
    have hi' : i < (List.range (d.shape.insts.map (·.2.1)).length).length := by
      rw [← hlen]; exact hi
    obtain ⟨z, hz, hzr⟩ := hget i hi'
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hzr
    have hzx : z = x := hzr.symm.trans hxi
    rw [hzx] at hz
    simp only [List.getElem_range] at hz
    exact List.mem_of_getElem? hz
  have hnotin : ∀ x : String, ¬ Sparkle.IR.NameHints.Allocated x → outWs.contains x = false := by
    intro x hx
    refine Bool.eq_false_iff.mpr (fun hc => ?_)
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp (hOW x (List.contains_iff_mem.mp hc))
    exact hx (Eq.mp (congrArg Sparkle.IR.NameHints.Allocated hpn) (hwalloc p (hinW p hp)))
  have key : ∀ (nm : String), ¬ Sparkle.IR.NameHints.Allocated nm →
      ∀ p ∈ (withClockFor children (closeMachine d.shape.layout t')).inputs, p.name = nm →
      nm ∈ M.inputs.map (·.name) := by
    intro nm hnm p hp hpn
    have hkeep : (!outWs.contains p.name) = true := by
      rw [hpn]
      exact congrArg (fun v : Bool => !v) (hnotin nm hnm)
    rw [hMin]
    exact List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, hkeep⟩, hpn⟩
  exact ⟨key "clk" Tools.ShippingMachineCleanup.not_allocated_clk pc hpc hpcn,
    key "rst" Tools.ShippingRegisterSoundness.not_allocated_rst pr hpr hprn⟩

/-! ## A parent without a register: the facts of `core_raw_facts` and `core_clk` -/

set_option maxHeartbeats 4000000 in
/-- **The reset input, the distinct instance names, the self-read test and
the one-bit clock and reset of the full entry's module of a machine WITHOUT
a register one of whose call entries is a sequential child.** -/
theorem core_slotless_seq {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hsl0 : d.shape.layout.slots = [])
    (hseq : SeqKid mref cref d)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    "rst" ∈ b.inputs.map (·.name) ∧
    (Tools.ShippingHierState.instNames b.body).Nodup ∧
    Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules) b.body = true ∧
    Tools.ShippingDesignSV.weS b "clk" = 1 ∧ Tools.ShippingDesignSV.weS b "rst" = 1 := by
  -- the clock and the reset are inputs of the raw module (the closing)
  have hckM := core_seqKid_inputs d ok hbody hC hslots hdomB hins hfne hnomem hseq hB hcore
    entry closes
  have hrstM : "rst" ∈ M.inputs.map (·.name) := hckM.2
  have hbody' : b.body = M.body :=
    (Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes).2.1
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
  obtain ⟨hMw, -, -, L, hLinst, hperm, -, -, -, -, -, -, -⟩ := hcc.some
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
  -- the raw module's wiring: the allocated port names (2), the instances
  -- (14), its inputs (17)
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeMachineCertified_sound hrun9.mreturns d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, -, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, hnamesA, -, -, -, -, -, -, -, -, -, -, -, hG14, -, -, hinM, -⟩ := wired
  obtain ⟨hndM, hsfM⟩ := hG14 hfne
  obtain ⟨outWs, extra, houtW, -, hex, hMin⟩ := hinM
  -- the `let`-closed transition and the closed machine: the wires' names
  obtain ⟨Bc, coreW, hbodyc, typedc, namedc, namesc, inWc, inNdc, wNdc, slotsc, hcoreW⟩ :=
    Tools.ShippingClosedTransitionTyped.closedTransition_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨-, -, hwCM, -, -, -, -, -⟩ :=
    Tools.ShippingCloseMachineTyped.closeMachine_typed (lay := d.shape.layout) hbodyc typedc
      namedc namesc inWc inNdc wNdc slotsc
      (fun f hf => by rw [hcoreW]; exact hfit f hf)
      (fun o ho => by rw [hcoreW]; exact houtfit o ho) outsOk outTy
  have hwsub : ∀ p ∈ b.wires, p ∈ (closeMachine d.shape.layout t').wires := by
    intro p hp
    rw [hbw] at hp
    have := Tools.ShippingClosedTyped.dropZW_wires_sub hp
    rw [hMw] at this
    exact this
  -- the calls' ports are allocated names: the filter keeps `clk` and `rst`
  have hnotin : ∀ x : String, ¬ Sparkle.IR.NameHints.Allocated x → outWs.contains x = false := by
    intro x hx
    refine Bool.eq_false_iff.mpr (fun hc => ?_)
    obtain ⟨k, -, hk⟩ := houtW x (List.contains_iff_mem.mp hc)
    exact hx (hnamesA x (List.mem_of_getElem? hk))
  have hc : (!outWs.contains "clk") = true :=
    congrArg (fun v : Bool => !v) (hnotin "clk" Tools.ShippingMachineCleanup.not_allocated_clk)
  have hr : (!outWs.contains "rst") = true :=
    congrArg (fun v : Bool => !v) (hnotin "rst" Tools.ShippingRegisterSoundness.not_allocated_rst)
  have hs : d.shape.layout.slots.isEmpty = true := by
    rw [hsl0]
    rfl
  have hPal : ∀ p ∈ machPorts c ids cache d.shape.binders,
      Sparkle.IR.NameHints.Allocated p.name :=
    fun p hp => hnamesA p.name (List.mem_map.mpr ⟨p, hp, rfl⟩)
  -- the wiring's `extra` is the clock and the reset: with `extra = []` every
  -- input is an allocated name, and `rst` is an input
  have hx : extra = [({ name := "clk", ty := .bit } : Port), { name := "rst", ty := .bit }] := by
    rcases hex with h | ⟨h, -⟩
    · exfalso
      obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hrstM
      rw [hMin, h] at hp
      have hp1 := (List.mem_filter.mp hp).1
      rcases List.mem_append.mp hp1 with h1 | h1
      · rcases List.mem_append.mp h1 with h2 | h2
        · exact Tools.ShippingRegisterSoundness.not_allocated_rst
            (Eq.mp (congrArg Sparkle.IR.NameHints.Allocated hpn)
              (hPal p (List.mem_of_mem_take h2)))
        · first
            | (rw [if_pos hs] at h2; cases h2)
            | (simp [hs] at h2)
      · cases h1
    · exact h
  have hbIn := hbi.trans hMin
  have hrstB : "rst" ∈ b.inputs.map (·.name) := by
    rw [hbi]
    exact hrstM
  refine ⟨hrstB, ?_, ?_, ?_⟩
  · rw [hbody', ← Tools.ShippingChecksRaw.instNameOf_eq]
    exact hndM
  · rw [hbody']
    exact Tools.ShippingChecksRaw.noSelfRead_of_feed hsfM
  · exact weS_clk_rst_tail hbIn (if_pos hs) hx hc hr
      (fun p hp => hwCM p (hwsub p hp)) hPal

/-! ## The generalisations: a register, OR a sequential child -/

/-- **`core_raw_facts` for a parent with a register OR a sequential child**:
the reset input, the distinct instance names and the self-read test of the
full entry's module. With a register it is the built
`Tools.ShippingChecksRaw.core_raw_facts`. -/
theorem core_raw_factsS {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hck : d.shape.layout.slots ≠ [] ∨ SeqKid mref cref d)
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    "rst" ∈ b.inputs.map (·.name) ∧
    (Tools.ShippingHierState.instNames b.body).Nodup ∧
    Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules) b.body = true := by
  by_cases hsl : d.shape.layout.slots = []
  · have h := core_slotless_seq d ok hbody hC hslots hdomB hins hfne outTy hnomem hsl
      (Or.resolve_left hck (fun hn => hn hsl)) hB hcore hpost entry closes
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  · exact Tools.ShippingChecksRaw.core_raw_facts d ok hbody hC hslots hdomB hins hsl hfne outTy
      hnomem hB hcore hpost entry closes

/-- **`core_clk` for a parent with a register OR a sequential child**: the
clock and the reset of the full entry's module are one bit in the emitter's
width map. With a register it is the built `Tools.ShippingCoreClk.core_clk`
(which does not ask `hfne`). -/
theorem core_clkS {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hck : d.shape.layout.slots ≠ [] ∨ SeqKid mref cref d)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingDesignSV.weS b "clk" = 1 ∧ Tools.ShippingDesignSV.weS b "rst" = 1 := by
  by_cases hsl : d.shape.layout.slots = []
  · exact (core_slotless_seq d ok hbody hC hslots hdomB hins hfne outTy hnomem hsl
      (Or.resolve_left hck (fun hn => hn hsl)) hB hcore hpost entry closes).2.2.2
  · exact Tools.ShippingCoreClk.core_clk d ok hbody hC hslots hdomB hins outTy hnomem hsl hB
      hcore hpost entry closes

end Tools.ShippingSlotlessClk
