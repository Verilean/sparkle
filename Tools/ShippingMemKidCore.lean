import Tools.ShippingChecksCore
import Tools.ShippingChecksRaw
import Tools.ShippingLinkedFresh
import Tools.ShippingChecksOuts
import Tools.ShippingChecksWidths
import Tools.ShippingChecksRunFacts
import Tools.ShippingChecksCoreGate

/-! # The run's facts of a machine whose calls include MEMORY children (G1, unit U4, round par/b-13)

Every `core_*` theorem of the check-free chain asks

    hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none

READ (file:line in `docs/parallel/B-memkids.md`): the hypothesis is consumed
at ONE kind of place only — where a child of the run's child list is taken
by its witness `memChild? c = some y ∨ RealChild mref cref c y`
(`Tools.ShippingChildInv.ChildrenReal`) and the left case is refuted. Nothing
else in those proofs reads what a child IS: the per-child facts are
hypotheses, quantified over `RealChild`.

This file is the SAME chain with the child predicate

    Kid mref cref c y :=
      memChild? c = some y ∨ (memChild? c = none ∧ RealChild mref cref c y)

in place of `RealChild mref cref c y`, and with `hfne : d.shape.instFields ≠ []`
in place of `hnomem` (the GENERAL closing is the one that builds a memory's
child, and its run states `MemChildren`: a memory entry's child IS the built
module — `Tools.ShippingMachineEntry.CloseCalls`, second disjunct). `kid_of`
turns a child's witness into `Kid`.

Statements and proofs are COPIED BY A SCRIPT from the file each part below
names (the originals are not changed and these copies do not follow them).
The script's changes, all of them:

* the theorem's name gets the suffix `M`;
* the binder `hnomem` is removed (a theorem that already had `hfne`) or
  replaced, in place, by `hfne` (one that had not);
* `RealChild mref cref` becomes `Kid mref cref` (statements and proofs);
* a call of a copied theorem calls the copy, its `hnomem` argument dropped
  or replaced by `hfne` accordingly;
* at each place where the left case of a witness was refuted
  (`rcases hor with hmem | hre`, `rw [hnomem …] at hmem`, `cases hmem`) the
  three lines are `have hre := kid_of … hMC … hor`, and `hMC : MemChildren
  d.shape children` is taken from the closing's own statement right after
  the run is opened.

What is NOT proved here: the per-child facts of a memory child (they are
hypotheses over `Kid`; `Tools/ShippingMemKidFacts.lean` proves them of the
built memory module), the closing (`MachineClosesAt` stays a hypothesis).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingMemKid
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

/-- **A call entry's child as the general closing takes it**: the built
memory module for a memory placeholder name, a real child of the declaration
otherwise. -/
def Kid (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)
    (c : Name) (y : Res) : Prop :=
  Sparkle.Compiler.MachMemory.memChild? c = some y ∨
    (Sparkle.Compiler.MachMemory.memChild? c = none ∧ RealChild mref cref c y)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **A child of the general closing's run is a kid**: its witness
(`ChildrenReal`) and the closing's own statement that a memory entry's child
is the built module (`MemChildren`). -/
theorem kid_of {shape : MachineShape} {children : List Res} {k : Nat}
    (hk : k < shape.insts.length) (hMC : MemChildren shape children) {y : Res}
    (hy : children[k]? = some y)
    (hor : Sparkle.Compiler.MachMemory.memChild? (shape.insts[k]).1 = some y ∨
      RealChild mref cref (shape.insts[k]).1 y) :
    Kid mref cref (shape.insts[k]).1 y := by
  rcases hor with h | h
  · exact Or.inl h
  · cases hm : Sparkle.Compiler.MachMemory.memChild? (shape.insts[k]).1 with
    | none => exact Or.inr ⟨hm, h⟩
    | some md =>
      have hn : (shape.insts.map (·.1))[k]? = some (shape.insts[k]).1 := by simp [hk]
      have h1 : children[k]? = some md := hMC k _ hn md hm
      rw [hy] at h1
      have e : y = md := Option.some.inj h1
      rw [e]
      exact Or.inl hm

/-- A kid of a declaration that is not a memory placeholder is a real child. -/
theorem Kid.real {c : Name} {y : Res} (h : Kid mref cref c y)
    (hc : Sparkle.Compiler.MachMemory.memChild? c = none) : RealChild mref cref c y := by
  rcases h with h | ⟨-, h⟩
  · rw [hc] at h
    cases h
  · exact h

/-- A kid of a memory placeholder is the built module. -/
theorem Kid.mem {c : Name} {y md : Res} (h : Kid mref cref c y)
    (hc : Sparkle.Compiler.MachMemory.memChild? c = some md) : y = md := by
  rcases h with h | ⟨hn, -⟩
  · rw [hc] at h
    exact (Option.some.inj h).symm
  · rw [hc] at hn
    cases hn

/-! ## From `Tools/ShippingChecksCore.lean` -/

section
open Tools.ShippingChecksCore

set_option maxHeartbeats 4000000 in
/-- **A core run on a machine with calls: the module, its instances in the
design, and the design's modules.** -/
theorem core_kids_factsM {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hfne : d.shape.instFields ≠ [])
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    M.name = c.toString ∧ b.body = M.body ∧ b.outputs = M.outputs ∧
    (∀ mn i conns, Stmt.inst mn i conns ∈ M.body → ∃ mc, moduleByName D.modules mn = some mc) ∧
    (∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Kid mref cref (d.shape.insts[k]).1 y ∧ (g = y.1 ∨ g ∈ y.2.modules) ∧
      ∀ g2 ∈ y.1 :: y.2.modules, ∃ g' ∈ D.modules, g'.name = g2.name) ∧
    Tools.ShippingDesignSVBack.outsAssigned b = true := by
  obtain ⟨bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
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
  have hMC : MemChildren d.shape children := by
    rcases hcc with ⟨hf0, -⟩ | ⟨-, -, h⟩
    · exact absurd hf0 hfne
    · exact h
  obtain ⟨-, -, hMname, L, hLinst, hperm, -, -, -, -, -, hDeq, -⟩ := hcc.some
  obtain ⟨hseq0, hname0, hd0⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  -- the raw module's wiring
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
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeMachineCertified_sound hrun9.mreturns d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, -, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, -, -, -, hcall1, hinst1, -, houtsM, -, -, -, hGinst, hGcall, -, -, hcleanAny, -⟩ :=
    wired
  obtain ⟨hzb, -, hzi, hzo⟩ := hcleanAny outTy
  -- an instance statement of the module names a module of its design
  have hinstD : ∀ mn i conns, Stmt.inst mn i conns ∈ M.body →
      ∃ mc, moduleByName D.modules mn = some mc ∧ mc ∈ D.modules ∧ mc.name = mn := by
    intro mn i conns hm
    by_cases hf : d.shape.instFields = []
    · obtain ⟨k, args, mc, -, hfind, -⟩ := hinst1 hf mn i conns hm
      have hfind' := hfind
      unfold moduleByName at hfind'
      exact ⟨mc, hfind, List.mem_of_find?_eq_some hfind', by simpa using List.find?_some hfind'⟩
    · obtain ⟨args, outs, mc, hcs, hfind, -⟩ := hGinst hf _ hm rfl
      obtain ⟨_, _, _, -, -, -, -, -, -, -, -, -, -, -, he⟩ := hcs
      cases he
      exact ⟨mc, hfind, List.mem_of_find?_eq_some hfind, rfl⟩
  have hhas : Tools.ShippingMachineShipsHier.hasInst M := by
    have hk0 : 0 < d.shape.insts.length := List.length_pos_iff.mpr hins
    by_cases hf : d.shape.instFields = []
    · obtain ⟨args, mc, st, -, hst, -, hcs⟩ := hcall1 hf 0 hk0
      obtain ⟨_, _, _, iname, -, -, -, -, -, -, -, -, -, he⟩ := hcs
      exact ⟨mc.name, iname, _, he ▸ hst⟩
    · obtain ⟨st, hst, args, outs, mc, hcs, -⟩ := hGcall hf 0 hk0
      obtain ⟨_, _, iname, -, -, -, -, -, -, -, -, -, -, -, he⟩ := hcs
      exact ⟨mc.name, iname, _, he ▸ hst⟩
  have hbeq : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M := by
    rcases hpost with h | h
    · exact h
    · rw [h]
      refine Tools.ShippingMachineDepthRun.mergeChecked_of_hasInst ?_
      obtain ⟨mn, i, conns, hm⟩ := hhas
      exact ⟨mn, i, conns, by rw [hzb]; exact hm⟩
  have hbody' : b.body = M.body := by rw [hbeq, hzb]
  have hbout : b.outputs = M.outputs := by rw [hbeq, hzo]
  -- the children, by their witnesses
  obtain ⟨hlenC, hall⟩ := hreal
  -- the design: the join of the children
  obtain ⟨hdNd, hdVis⟩ := designWith_modules (children := children) hd0
  have hnames := Tools.ShippingChecksDepth.visited_name (children := children) hd0
  -- the closed machine assigns its outputs, and so does the module
  obtain ⟨ids', cache', returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    synthesizeMixedCertified_returns run
  obtain ⟨wP, hpw⟩ := Tools.ShippingChecksPacked.transition_packed nd len hrun hm d.packed hwf
    hb' hv' hbody
  obtain ⟨wP', hpw'⟩ := Option.isSome_iff_exists.mp
    (Tools.ShippingChecksPacked.closeLets_packed hcl hpw)
  have hMA : Tools.ShippingDesignSVBack.outsAssigned M = true := by
    refine Tools.ShippingChecksDerived2.outsAssigned_of_assigned fun p hp => ?_
    have hp2 : p ∈ (closeMachine d.shape.layout t').outputs := by
      rw [closeMachine_outputs hpw']
      rw [houtsM] at hp
      exact hp
    obtain ⟨r, hr⟩ := Tools.ShippingChecksDerived3.closeMachine_outs_assigned hpw' p hp2
    exact ⟨r, hperm.subset (List.mem_append_left _ hr)⟩
  refine ⟨hMname.trans hname0, hbody', hbout,
    fun mn i conns hm => (hinstD mn i conns hm).imp fun _ h => h.1, ?_,
    Tools.ShippingChecksDerived3.outsAssigned_congr hbody' hbout hMA⟩
  intro g hg
  rw [hDeq] at hg
  obtain ⟨y, hy, hor⟩ := mem_visited.mp (hdVis g hg)
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hy
  have hk' : k < d.shape.insts.length := by
    rw [← hlenC]
    exact (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨y', hy', hor'⟩ := hall k hk'
  rw [hk] at hy'
  cases hy'
  have hre := kid_of hk' hMC hk hor'
  · refine ⟨k, hk', y, hre, hor, fun g2 hg2 => ?_⟩
    rw [hDeq]
    refine hnames g2 (mem_visited.mpr ⟨y, hy, ?_⟩)
    rcases List.mem_cons.mp hg2 with h | h
    · exact Or.inl h
    · exact Or.inr h

end

/-! ## From `Tools/ShippingChecksRaw.lean` -/

section
open Tools.ShippingChecksRaw

set_option maxHeartbeats 4000000 in
/-- **The reset input, the distinct instance names and the self-read test of
the full entry's module**, from the core run of a machine with calls closed
by `closeInstsG` and with a register. -/
theorem core_raw_factsM {c : Name} (d : MachineData) (ok : d.ok = true)
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
  obtain ⟨bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
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
  obtain ⟨-, -, hMname, L, hLinst, hperm, -, -, -, -, -, hDeq, -⟩ := hcc.some
  obtain ⟨hseq0, hname0, hd0⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  -- the raw module's wiring
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
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeMachineCertified_sound hrun9.mreturns d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, -, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, hAlloc, -, -, -, -, -, -, -, -, -, -, -, hG14, -, hcleanAny, hInputs, -⟩ := wired
  obtain ⟨-, -, hzi, -⟩ := hcleanAny outTy
  obtain ⟨hndM, hsfM⟩ := hG14 hfne
  obtain ⟨outWs, extra, houtWs, -, -, hMin⟩ := hInputs
  have hbody' : b.body = M.body :=
    (core_kids_factsM d ok hbody hC hslots hdomB hins outTy hfne hB
      hcore hpost entry closes).2.1
  have hbin : b.inputs = M.inputs := by
    rcases hpost with h | h
    · rw [h]
      exact hzi
    · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).1]
      exact hzi
  have hne : d.shape.layout.slots.isEmpty = false := by
    cases hs : d.shape.layout.slots with
    | nil => exact absurd hs hsl
    | cons _ _ => rfl
  have hnotW : "rst" ∉ outWs := by
    intro hm
    obtain ⟨k, -, hk⟩ := houtWs _ hm
    exact rst_not_allocated (hAlloc _ (List.mem_of_getElem? hk))
  have hrstM : "rst" ∈ M.inputs.map (·.name) := by
    rw [hMin]
    refine List.mem_map.mpr ⟨{ name := "rst", ty := .bit }, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · refine List.mem_append_left _ (List.mem_append_right _ ?_)
      rw [hne]
      simp
    · simpa using hnotW
  refine ⟨by rw [hbin]; exact hrstM, ?_, ?_⟩
  · rw [hbody', ← instNameOf_eq]
    exact hndM
  · rw [hbody']
    exact noSelfRead_of_feed hsfM

end

/-! ## From `Tools/ShippingLinkedFresh.lean` -/

section
open Tools.ShippingLinkedFresh
open Tools.ShippingHierOpen (linkedWF bodyInstOuts stmtInstOuts linkedWrites instOutWires)

set_option maxHeartbeats 4000000 in
/-- **The full entry's body is linked-well-formed over the core run's
design**, for a machine with calls. -/
theorem core_linkedWFM {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hfne : d.shape.instFields ≠ [])
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingHierOpen.linkedWF (childMap D.modules) b.body = true := by
  obtain ⟨bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
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
  obtain ⟨-, -, hMname, L, hLinst, hperm, -, -, -, -, -, hDeq, -⟩ := hcc.some
  obtain ⟨hseq0, hname0, hd0⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  -- the raw module's wiring
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
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeMachineCertified_sound hrun9.mreturns d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, -, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, -, -, -, -, -, hlink, -⟩ := wired
  have hbody' : b.body = M.body :=
    (core_kids_factsM d ok hbody hC hslots hdomB hins outTy hfne hB
      hcore hpost entry closes).2.1
  rw [hbody', ← Tools.ShippingMachineLinked.linkedOk_eq]
  exact hlink

/-- **No assignment of the full entry's module targets an instance-driven
wire** — the assignment half of `outsExtracted`'s "not driven". -/
theorem core_instOuts_not_assignedM {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hfne : d.shape.instFields ≠ [])
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ∀ x, x ∈ bodyInstOuts (childMap D.modules) b.body →
      x ∉ Sparkle.IR.Reorder.writesOf b.body :=
  instOuts_not_written b.body
    (core_linkedWFM d ok hbody hC hslots hdomB hins outTy hfne hB hcore hpost entry closes)

end

/-! ## From `Tools/ShippingChecksOuts.lean` -/

section
open Tools.ShippingChecksOuts

set_option maxHeartbeats 4000000 in
/-- **Every instance-driven wire of the full entry's module is an extracted
input of the optimizer check**, from the core run of a machine with calls
closed by `closeInstsG`, each real child's output ports apart from its
argument ports, `clk` and `rst`. -/
theorem core_outsExtractedM {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Kid mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingHierPremisesBase.outsExtracted (childMap D.modules) b = true := by
  -- the full entry's body is the raw module's; no assignment targets an instance output
  have hbody' : b.body = M.body :=
    (core_kids_factsM d ok hbody hC hslots hdomB hins outTy hfne hB
      hcore hpost entry closes).2.1
  have hasg := core_instOuts_not_assignedM d ok hbody hC hslots hdomB
    hins outTy hfne hB hcore hpost entry closes
  -- the cleanup and the checked merge keep the inputs and the non-zero wires
  have hbin : b.inputs = M.inputs := by
    rcases hpost with h | h
    · rw [h]
      exact Tools.ShippingOutsExtractedParts.dropZW_inputs M
    · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).1]
      exact Tools.ShippingOutsExtractedParts.dropZW_inputs M
  have hbw : ∀ p ∈ M.wires, p.ty.bitWidth ≠ 0 → p ∈ b.wires := by
    intro p hp hz
    rcases hpost with h | h
    · rw [h]
      exact Tools.ShippingOutsExtractedParts.dropZW_wires hp hz
    · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).2.2]
      exact Tools.ShippingOutsExtractedParts.dropZW_wires hp hz
  -- the run
  obtain ⟨bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
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
  have hMC : MemChildren d.shape children := by
    rcases hcc with ⟨hf0, -⟩ | ⟨-, -, h⟩
    · exact absurd hf0 hfne
    · exact h
  obtain ⟨hMw, -, -, L, hLinst, hperm, -, -, -, -, -, -, -⟩ := hcc.some
  rcases hcc with ⟨hf0, -⟩ | ⟨-, hG, -⟩
  · exact absurd hf0 hfne
  obtain ⟨hseq0, -, -⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨PI, ls, hin, hPI, hlsL, hndI, hinW, hregs⟩ :=
    Tools.ShippingClosedPorts.closedPorts_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨hlenC, hallC⟩ := hreal
  have hlenT : t.inputs.length = PI.length + ls.length := by
    rw [hin, List.length_append]
  -- an instance-driven wire is a call port of the transition
  have hident : ∀ x, x ∈ Tools.ShippingHierOpen.bodyInstOuts (childMap D.modules) M.body →
      ∃ k, k < d.shape.insts.length ∧
        (t.inputs.map (·.name))[machNIn d.shape + k]? = some x := by
    intro x hx
    obtain ⟨st, hst, hxs⟩ := Tools.ShippingOutsExtractedParts.mem_bodyInstOuts M.body x hx
    cases st with
    | inst mn iname conns =>
      rcases Tools.ShippingMachineInstG.closeInstsG_insts hG _ hst rfl with
        h0 | ⟨args, outs, child, mc, hcs, hfind, hne0, hall⟩
      · exact Tools.ShippingChecksDerived.ff_absurd (List.all_eq_true.mp hseq0 _ h0)
      · -- an entry of the group, its child
        obtain ⟨e0, he0⟩ : ∃ e0, e0 ∈ outs := by
          cases outs with
          | nil => exact absurd rfl hne0
          | cons a rest => exact ⟨a, List.Mem.head _⟩
        obtain ⟨hargs0, hch0, -⟩ := hall e0 he0
        have hk0 : e0.1 < d.shape.insts.length := by
          have := (List.getElem?_eq_some_iff.mp hargs0).1
          simpa using this
        obtain ⟨y, hy, hor⟩ := hallC e0.1 hk0
        rw [hy] at hch0
        have hyn : y.1.name = child.1.name := by
          simpa only [Option.map_some, Option.some.injEq] using hch0
        have hre := kid_of hk0 hMC hy hor
        · -- the instance's module is the child's
          have hyfind :=
            ((Tools.ShippingMachineInstG.closeInstsG_names hG).2.2.2 y
              (List.mem_of_getElem? hy)).1
          rw [hyn, hfind] at hyfind
          have hmcy : mc = y.1 := Option.some.inj hyfind
          have hap : ∀ p ∈ mc.outputs, (∀ q ∈ inPortsOf mc, q.name ≠ p.name) ∧
              p.name ≠ "clk" ∧ p.name ≠ "rst" := by
            rw [hmcy]
            exact hkidP e0.1 hk0 y hre
          have hmn : mn = mc.name := Tools.ShippingOutsExtractedParts.callStmtG_name hcs
          have hfind' : moduleByName D.modules mn = some mc := by
            rw [hmn, (Tools.ShippingHierPremisesBase.moduleByName_mem hfind).2]
            exact hfind
          obtain ⟨p, hp, hpc⟩ := Tools.ShippingOutsExtractedParts.stmtInstOuts_inst hfind' hxs
          obtain ⟨hpin, hclk, hrst⟩ := hap p hp
          obtain ⟨e, he, hget⟩ :=
            Tools.ShippingOutsExtractedParts.callStmtG_outWire hcs hpin hclk hrst hpc
          obtain ⟨hargsE, -⟩ := hall e he
          have hke : e.1 < d.shape.insts.length := by
            have := (List.getElem?_eq_some_iff.mp hargsE).1
            simpa using this
          exact ⟨e.1, hke, hget⟩
    | _ =>
      have hx' : x ∈ ([] : List String) := hxs
      cases hx'
  refine Tools.ShippingOutsExtractedParts.outsExtracted_of_parts ?_ ?_ ?_
  · -- (a) a declared wire
    intro x hx
    rw [hbody'] at hx
    obtain ⟨k, hk, hget⟩ := hident x hx
    rw [List.getElem?_map] at hget
    cases hq : t.inputs[machNIn d.shape + k]? with
    | none =>
      rw [hq] at hget
      cases hget
    | some q =>
      rw [hq] at hget
      simp only [Option.map_some, Option.some.injEq] at hget
      obtain ⟨hqw, hqz⟩ := hinW q (List.mem_of_getElem? hq)
      exact ⟨q, hbw q (by rw [hMw]; exact hqw) hqz, hget⟩
  · -- (c) not driven
    intro x hx hdr
    rcases Tools.ShippingOutsExtractedParts.mem_drivesOf hdr with hwr | ⟨c', rs, inp, init, hreg⟩
    · exact hasg x hx hwr
    · rw [hbody'] at hx hreg
      obtain ⟨k, hk, hget⟩ := hident x hx
      have hreg' : Stmt.register x c' rs inp init ∈ (closeMachine d.shape.layout t').body := by
        rcases List.mem_append.mp (hperm.symm.subset hreg) with h0 | h0
        · exact h0
        · exact Tools.ShippingChecksDerived.ff_absurd (List.all_eq_true.mp hLinst _ h0)
      obtain ⟨i, p, hi, hpi, hpn⟩ := hregs x c' rs inp init hreg'
      have hgi : (t.inputs.map (·.name))[i]? = some x := by
        rw [List.getElem?_map, hpi]
        exact congrArg some hpn
      have heq : machNIn d.shape + k = i :=
        Tools.ShippingOutsExtractedParts.getElem?_nodup_inj hndI hget hgi
      omega
  · -- (d) not an input
    intro x hx hxin
    rw [hbody'] at hx
    obtain ⟨k, hk, hget⟩ := hident x hx
    obtain ⟨outWsI, hmapI, hMin⟩ := Tools.ShippingMachineInstG.closeInstsG_inputs hG
    rw [hbin, hMin] at hxin
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hxin
    have hpf : (!outWsI.contains p.name) = true := (List.mem_filter.mp hp).2
    rw [hpn] at hpf
    have hnot : x ∉ outWsI := by simpa [List.contains_eq_mem] using hpf
    obtain ⟨-, hgetI⟩ := Tools.ShippingMachineInst.mapM_some _ _ _ hmapI
    obtain ⟨y, hy, hyi⟩ := hgetI k (by simpa using hk)
    simp only [List.getElem_range] at hy
    have hy' : (t.inputs.map (·.name))[machNIn d.shape + k]? = some y := hy
    have hyx : y = x := (Option.some.inj (hget.symm.trans hy')).symm
    rw [hyx] at hyi
    exact hnot (List.mem_of_getElem? hyi)

end

/-! ## From `Tools/ShippingChecksWidths.lean` -/

section
open Tools.ShippingChecksWidths

set_option maxHeartbeats 4000000 in
/-- **The output connections of the full entry's instances**: each is the
connection of a call entry `k` — the instance's module a real child's, the
port the entry's field — and its wire is declared at the width of the type
of the call's binder. -/
theorem core_callPortsM {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Kid mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, moduleByName D.modules mn = some mc ∧
        ∀ p ∈ mc.outputs, ∀ x, (p.name, Sparkle.IR.AST.Expr.ref x) ∈ conns →
          ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
            Kid mref cref (d.shape.insts[k]).1 y ∧ mc = y.1 ∧
            p.name = d.shape.instFields.getD k "" ∧
            ∃ bn, d.shape.binders[nDecl + k]? = some bn ∧
              Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth := by
  have hbody' : b.body = M.body :=
    (core_kids_factsM d ok hbody hC hslots hdomB hins outTy hfne hB
      hcore hpost entry closes).2.1
  -- the cleanup and the checked merge keep the non-zero wires and add none
  have hbw : ∀ p ∈ M.wires, p.ty.bitWidth ≠ 0 → p ∈ b.wires := by
    intro p hp hz
    rcases hpost with h | h
    · rw [h]
      exact Tools.ShippingOutsExtractedParts.dropZW_wires hp hz
    · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).2.2]
      exact Tools.ShippingOutsExtractedParts.dropZW_wires hp hz
  have hbsub : ∀ p ∈ b.wires, p ∈ M.wires := by
    intro p hp
    rcases hpost with h | h
    · rw [h] at hp
      exact Tools.ShippingInstWidthsParts.dropZW_wires_sub M p hp
    · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).2.2] at hp
      exact Tools.ShippingInstWidthsParts.dropZW_wires_sub M p hp
  -- the run
  obtain ⟨bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
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
  have hMC : MemChildren d.shape children := by
    rcases hcc with ⟨hf0, -⟩ | ⟨-, -, h⟩
    · exact absurd hf0 hfne
    · exact h
  obtain ⟨hMw, -, -, L, hLinst, hperm, -, -, -, -, -, -, -⟩ := hcc.some
  rcases hcc with ⟨hf0, -⟩ | ⟨-, hG, -⟩
  · exact absurd hf0 hfne
  obtain ⟨hseq0, -, -⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨PI, ls, hin, hPI, hlsL, hndI, hinW, hregs⟩ :=
    Tools.ShippingClosedPorts.closedPorts_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨hwnd, hwal, hinWt, P1, P2, hsp, hP2d, hP2len, hP2ty⟩ :=
    Tools.ShippingTransitionPortTys.transitionPortTys_of_run d ok hbody hC hslots hdomB run
  have hls : P2 = ls := (List.append_inj' (hsp.symm.trans hin) (by omega)).2
  obtain ⟨hlenC, hallC⟩ := hreal
  intro mn iname conns hst
  rw [hbody'] at hst
  rcases Tools.ShippingMachineInstG.closeInstsG_insts hG _ hst rfl with
    h0 | ⟨args, outs, child, mc, hcs, hfind, hne0, hall⟩
  · exact Tools.ShippingChecksDerived.ff_absurd (List.all_eq_true.mp hseq0 _ h0)
  -- every entry of the group is a call of a real child whose module is `mc`
  have hrealE : ∀ e ∈ outs, ∃ (hk : e.1 < d.shape.insts.length) (y : Res),
      Kid mref cref (d.shape.insts[e.1]).1 y ∧ mc = y.1 := by
    intro e he
    obtain ⟨hargs0, hch0, -⟩ := hall e he
    have hk0 : e.1 < d.shape.insts.length := by
      have := (List.getElem?_eq_some_iff.mp hargs0).1
      simpa using this
    obtain ⟨y, hy, hor⟩ := hallC e.1 hk0
    rw [hy] at hch0
    have hyn : y.1.name = child.1.name := by
      simpa only [Option.map_some, Option.some.injEq] using hch0
    have hre := kid_of hk0 hMC hy hor
    · have hyfind :=
        ((Tools.ShippingMachineInstG.closeInstsG_names hG).2.2.2 y
          (List.mem_of_getElem? hy)).1
      rw [hyn, hfind] at hyfind
      exact ⟨hk0, y, hre, Option.some.inj hyfind⟩
  obtain ⟨e0, he0⟩ : ∃ e0, e0 ∈ outs := by
    cases outs with
    | nil => exact absurd rfl hne0
    | cons a rest => exact ⟨a, List.Mem.head _⟩
  obtain ⟨hk0, y0, hre0, hmcy0⟩ := hrealE e0 he0
  have hap : ∀ p ∈ mc.outputs, (∀ q ∈ inPortsOf mc, q.name ≠ p.name) ∧
      p.name ≠ "clk" ∧ p.name ≠ "rst" := by
    rw [hmcy0]
    exact hkidP e0.1 hk0 y0 hre0
  have hmn : mn = mc.name := Tools.ShippingOutsExtractedParts.callStmtG_name hcs
  have hfind' : moduleByName D.modules mn = some mc := by
    rw [hmn, (Tools.ShippingHierPremisesBase.moduleByName_mem hfind).2]
    exact hfind
  refine ⟨mc, hfind', ?_⟩
  intro p hp x hpc
  obtain ⟨hpin, hclk, hrst⟩ := hap p hp
  obtain ⟨e, he, hget, hef⟩ :=
    Tools.ShippingInstWidthsParts.callStmtG_outWireF hcs hpin hclk hrst hpc
  obtain ⟨hke, y, hre, hmcy⟩ := hrealE e he
  obtain ⟨-, -, hfld⟩ := hall e he
  -- the call port: a transition input, of its binder's type
  rw [List.getElem?_map] at hget
  cases hq : t.inputs[machNIn d.shape + e.1]? with
  | none =>
    rw [hq] at hget
    cases hget
  | some q =>
    rw [hq] at hget
    simp only [Option.map_some, Option.some.injEq] at hget
    have hqm : q ∈ t.inputs := List.mem_of_getElem? hq
    obtain ⟨hqw, hqz⟩ := hinW q hqm
    have hql : ls[e.1]? = some q := by
      have h1 : (PI ++ ls)[PI.length + e.1]? = some q := by
        rw [← hin, hPI]
        exact hq
      rw [List.getElem?_append_right (Nat.le_add_right _ _)] at h1
      have h2 : PI.length + e.1 - PI.length = e.1 := by omega
      rw [h2] at h1
      exact h1
    have hlt : e.1 < (d.shape.binders.drop nDecl).length := by
      rw [← hP2d, hls]
      exact (List.getElem?_eq_some_iff.mp hql).1
    have hbn : (d.shape.binders.drop nDecl)[e.1]? = some (d.shape.binders.drop nDecl)[e.1] :=
      List.getElem?_eq_getElem hlt
    have hty : q.ty = kindTy ((d.shape.binders.drop nDecl)[e.1]).2 :=
      hP2ty e.1 q _ (by rw [hls]; exact hql) hbn
    have hbn' : d.shape.binders[nDecl + e.1]? = some (d.shape.binders.drop nDecl)[e.1] := by
      rw [← List.getElem?_drop]
      exact hbn
    -- its declared width in `b`: `q` is the only wire of its name
    have huniq : ∀ r ∈ b.wires, r.name = q.name → r = q := by
      intro r hr hrn
      have hrM : r ∈ M.wires := hbsub r hr
      rw [hMw] at hrM
      rcases Tools.ShippingTransitionPortTys.closeMachine_wires_sup _ _ r hrM with h1 | ⟨z, h1⟩
      · rw [Tools.ShippingTransitionPortTys.closeLets_wires hcl] at h1
        exact Tools.ShippingTransitionPortTys.port_of_name hwnd h1 (hinWt q hqm) hrn
      · have hal : Sparkle.IR.NameHints.Allocated (nextName z) := by
          rw [← h1, hrn]
          exact hwal q (hinWt q hqm)
        exact absurd hal (Tools.ShippingMachineClose.nextName_not_allocated z)
    have hdw : Sparkle.IR.RegDedup.declWidth b q.name = q.ty.bitWidth :=
      Tools.ShippingInstWidthsParts.declWidth_of_unique (nm := q.name) (ty := q.ty)
        (hbw q (by rw [hMw]; exact hqw) hqz) huniq
        (by rw [hty]; exact Tools.ShippingTransitionPortTys.kindTy_shape _)
    exact ⟨e.1, hke, y, hre, hmcy, by rw [← hef, hfld], _, hbn',
      by rw [← hget, hdw, hty]⟩

set_option maxHeartbeats 4000000 in
/-- **Every instance-output wire of the full entry's module is declared at
its child port's width**, from the core run and, per real child, the width
agreement `hkidW` between the call's binder and the child's field port. -/
theorem core_instOutWidthsOkM {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Kid mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Kid mref cref (d.shape.insts[k]).1 y →
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
    Tools.ShippingHierOpen.instOutWidthsOk (childMap D.modules)
      (Sparkle.IR.RegDedup.declWidth b) b.body = true := by
  have hcp := core_callPortsM d ok hbody hC hslots hdomB hins hfne outTy hkidP hB hcore
    hpost entry closes
  refine Tools.ShippingInstWidthsParts.instOutWidthsOk_of b.body ?_
  intro mn iname conns hst
  obtain ⟨mc, hfind, hports⟩ := hcp mn iname conns hst
  refine ⟨mc, Sparkle.IR.RegDedup.declWidth mc,
    congrArg (Option.map fun c => (c, Sparkle.IR.RegDedup.declWidth c)) hfind, ?_⟩
  intro p hp x hl
  obtain ⟨l₁, l₂, e, -⟩ := List.lookup_eq_some_iff.mp hl
  have hpc : (p.name, Sparkle.IR.AST.Expr.ref x) ∈ conns := by
    rw [e]
    exact List.mem_append_right _ (List.Mem.head _)
  obtain ⟨k, hk, y, hre, hmcy, hpn, bn, hbn, hdw⟩ := hports p hp x hpc
  have hw := hkidW k hk y hre p (by rw [← hmcy]; exact hp) hpn
  rw [hbn] at hw
  have hwe : (kindTy bn.2).bitWidth = p.ty.bitWidth := by
    simpa only [Option.map_some, Option.some.injEq] using hw
  rw [hdw, hwe]

set_option maxHeartbeats 4000000 in
/-- **The statement-kind gate of the hierarchical check**: the full entry's
module has an instance statement, and every statement is an instance, an
assignment or a register. -/
theorem core_hierGateM {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Sparkle.IR.RefineCheck.hierGate b = true := by
  have hbody' : b.body = M.body :=
    (core_kids_factsM d ok hbody hC hslots hdomB hins outTy hfne hB
      hcore hpost entry closes).2.1
  obtain ⟨bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
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
  obtain ⟨-, -, -, L, hLinst, hperm, -, -, -, -, -, -, -⟩ := hcc.some
  rcases hcc with ⟨hf0, -⟩ | ⟨-, hG, -⟩
  · exact absurd hf0 hfne
  obtain ⟨hseq0, -, -⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  refine Tools.ShippingInstWidthsParts.hierGate_of ?_ ?_
  · -- the instance statement of the first call
    have hk0 : 0 < (d.shape.insts.map (·.2.1)).length := by
      rw [List.length_map]
      exact List.length_pos_iff.mpr hins
    obtain ⟨st, hst, args, outs, child, mc, hcs, -⟩ :=
      Tools.ShippingMachineInstG.closeInstsG_calls hG 0 hk0
    obtain ⟨_, _, iname, -, -, -, -, -, -, -, -, -, -, -, he⟩ := hcs
    rw [hbody']
    exact ⟨mc.name, iname, _, he ▸ hst⟩
  · intro st hst
    rw [hbody'] at hst
    rcases List.mem_append.mp (hperm.symm.subset hst) with h0 | h0
    · exact Or.inr (List.all_eq_true.mp hseq0 _ h0)
    · exact Or.inl (List.all_eq_true.mp hLinst _ h0)

end

/-! ## From `Tools/ShippingChecksRunFacts.lean` -/

section
open Tools.ShippingChecksRunFacts

/-- **The run's facts of the full entry's module**, from the core run of a
machine with calls closed by `closeInstsG` and with a register. -/
theorem core_runFactsM {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Kid mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Kid mref cref (d.shape.insts[k]).1 y →
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
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b := by
  obtain ⟨hrst, hndB, hself⟩ :=
    core_raw_factsM d ok hbody hC hslots hdomB hins hsl hfne outTy
      hB hcore hpost entry closes
  exact
    { gate := core_hierGateM d ok hbody hC hslots hdomB hins hfne outTy
        hB hcore hpost entry closes
      wfB := core_linkedWFM d ok hbody hC hslots hdomB hins outTy hfne
        hB hcore hpost entry closes
      ndB := hndB
      self := hself
      outs := core_outsExtractedM d ok hbody hC hslots hdomB hins hfne
        outTy hkidP hB hcore hpost entry closes
      rst := hrst
      wid := core_instOutWidthsOkM d ok hbody hC hslots hdomB hins hfne
        outTy hkidP hkidW hB hcore hpost entry closes }

end

/-! ## From `Tools/ShippingChecksCoreGate.lean` -/

section
open Tools.ShippingChecksCoreGate

set_option maxHeartbeats 4000000 in
/-- **`outsCheck` of the printed module of a machine with calls, on the core
run's design, at every depth, under the statement-kind gate** (no
`hierBinds`). -/
theorem core_outsCheck_all_gateM {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hfne : d.shape.instFields ≠ [])
    (hkidA : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Kid mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
        ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true)
    (hkidR : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Kid mref cref (d.shape.insts[k]).1 y →
      ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
        ∃ g2 ∈ y.2.modules, g2.name = mn)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true) (n : Nat) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true := by
  obtain ⟨-, hbody', -, hresM, hrealD, -⟩ :=
    core_kids_factsM d ok hbody hC hslots hdomB hins outTy hfne hB
      hcore hpost entry closes
  refine Tools.ShippingChecksDepthGate.outsCheck_opt_all_gate hg ?_ ?_ ?_ n
  · intro mn iname conns hm
    rw [hbody'] at hm
    exact hresM mn iname conns hm
  · intro g hg
    obtain ⟨k, hk, y, hre, hor, -⟩ := hrealD g hg
    rcases hor with heq | hin
    · rw [heq]
      exact (hkidA k hk y hre).1
    · exact (hkidA k hk y hre).2 g hin
  · intro g hg mn iname conns hm
    obtain ⟨k, hk, y, hre, hor, hnm⟩ := hrealD g hg
    have hg' : g ∈ y.1 :: y.2.modules := by
      rcases hor with heq | hin
      · rw [heq]
        exact List.Mem.head _
      · exact List.Mem.tail _ hin
    obtain ⟨g2, hg2, hn2⟩ := hkidR k hk y hre g hg' mn iname conns hm
    obtain ⟨g', hg'D, hn'⟩ := hnm g2 (List.Mem.tail _ hg2)
    exact Tools.ShippingChecksDepth.resolves_by_name ⟨g', hg'D, hn'.trans hn2⟩

end

end Tools.ShippingMemKid
