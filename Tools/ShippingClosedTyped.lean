import Tools.ShippingChecksCore
import Tools.ShippingChecksDerived
import Tools.ShippingOutsExtractedParts
import Tools.ShippingClosedTransitionTyped
import Tools.ShippingCloseMachineTyped
import Tools.ShippingTextTyped
import Tools.ShippingNamesNext
import Tools.ShippingNamesClk
import Tools.ShippingMachineRanBase
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

/-! # The full entry's module of a machine with calls is typed: the text conjuncts of the RAW module (G1)

For a core run on a machine with calls (the hypotheses of `core_kids_facts`:
no `hsl`, no `hfne`, no per-child premise) and two DATA conditions on the
layout's output ports — their names sanitize-stable, their types one bit or
bit vectors — the full entry's module `b`:

* `core_closed_typedIn : TypedIn b` (`Tools/ShippingTextTyped.lean`): every
  assignment and register input typed in `b`'s own wire table, the wire
  names sanitize-stable, the output ports resolved by the emitter's map;
* `core_closed_typed`: the four hypotheses `hwn`, `hread`, `hA`, `hR` of
  `Tools.ShippingSeqCheckTyped.core_text_same`, verbatim, with the name
  condition as `(outs.map name).all cleanB = true`;
* `core_text_raw`: conjuncts 2 and 3 of `textCheckI` for `b` ITSELF —
  `seqCheck (wofOf b) (weS b) b.body = true` and the width tables — no
  `checkedOptimize` in the statement. This holds of every such run and is
  what a fallback guard on the optimizer's candidate would fall back to.

## The chain

    t   (transition)            TypedPostReady, PrintBaseAt   transition_typed_of_run
    t'  (closeLets)             TypedStmts, slots, core width closedTransition_of_run
    closeMachine lay t'         typed in its wire table       closeMachine_typed
    M   (closeInstsG / closeInsts)  same wires and outputs, the same assignments and
                                registers plus instance statements (`CloseCalls.some`),
                                inputs: allocated names, clk, rst (`MachineWired`)
    dropZeroWidthModule M       same body, wire table, inputs, outputs (`MachineWired`,
                                its cleanup clause); wires a sublist
    b                           = that, or its checked merge: `core_kids_facts` (the
                                merge of a module with an instance is the identity),
                                `mergeChecked_ports`

## The two data conditions, and why they are needed

* `hon : ∀ o ∈ outs, sanitizeName o.name = o.name`. `outNameOk` does not
  give it (`docs/parallel/G1-designCheck-text.md`). `seqCheck` tests
  `sanitizeName l == l` of every assignment target; the output ports are
  targets.
* `hoty : ∀ o ∈ outs, scalarTy o.ty = true`. `seqCheck` tests
  `wof l == some (we l)`; the emitter's map is `none` on a port of an array
  or symbolic-width type. `outTy` (`o.ty.bitWidth = o.width`) does not
  exclude those.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingClosedTyped
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

/-- The zero-width cleanup's wires are the module's, or those of non-zero
width. -/
theorem dropZW_wires_cases (m : Sparkle.IR.AST.Module) :
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).wires = m.wires ∨
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).wires =
        m.wires.filter (fun p => p.ty.bitWidth != 0) := by
  unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A wire of the cleaned module is a wire of the module. -/
theorem dropZW_wires_sub {m : Sparkle.IR.AST.Module} {p : Sparkle.IR.AST.Port}
    (hp : p ∈ (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).wires) : p ∈ m.wires := by
  rcases dropZW_wires_cases m with h | h
  · rw [h] at hp
    exact hp
  · rw [h] at hp
    exact (List.mem_filter.mp hp).1

set_option maxHeartbeats 4000000 in
/-- `core_closed_typedIn` over `MachineRan`: the TAIL of the built proof, moved (round par/g-1).
What it takes of the run is that the machine synthesis this core run performed
returned `(M, D)` from an invariant world; `core_closed_typedIn` below is its instance at the
all-worlds closing (`Tools.ShippingMachineRan.machineRan_of_closes`). -/
theorem core_closed_typedIn_ran {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D)
    -- the two data conditions on the output ports
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    Tools.ShippingTextTyped.TypedIn b := by
  -- the body and the output ports of the full entry's module are the raw module's
  have hkf := Tools.ShippingChecksCore.core_kids_facts_ran d ok hbody hC hslots hdomB hins outTy
    hnomem hpost ran
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
  have ran0 := ran
  obtain ⟨_, bb, w9, w10, hrun9, hw9, -⟩ := ran0
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
  -- the raw module's wiring: its outputs, its inputs, its cleanup
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeMachineCertified_sound hrun9.mreturns d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, -, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, hnamesA, -, -, -, -, -, houtsM, -, -, -, -, -, -, -, hcleanAny, hinM, -⟩ := wired
  obtain ⟨-, hzw, -, -⟩ := hcleanAny outTy
  obtain ⟨outWs, extra, -, -, hextra, hMin⟩ := hinM
  have hMinputs : ∀ p ∈ M.inputs,
      Sparkle.IR.NameHints.Allocated p.name ∨ p.name = "clk" ∨ p.name = "rst" := by
    intro p hp
    rw [hMin] at hp
    have hp' := (List.mem_filter.mp hp).1
    rcases List.mem_append.mp hp' with h | h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inl (hnamesA p.name (List.mem_map.mpr ⟨p, List.mem_of_mem_take h, rfl⟩))
      · split at h
        · cases h
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
          rcases h with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
    · rcases hextra with he | ⟨he, -⟩
      · rw [he] at h
        cases h
      · rw [he] at h
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
        rcases h with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
  -- the `let`-closed transition and the closed machine
  obtain ⟨Bc, coreW, hbodyc, typedc, namedc, namesc, inWc, inNdc, wNdc, slotsc, hcoreW⟩ :=
    Tools.ShippingClosedTransitionTyped.closedTransition_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨-, -, hwCM, -, hoCM, hkCM, haCM, hrCM⟩ :=
    Tools.ShippingCloseMachineTyped.closeMachine_typed (lay := d.shape.layout) hbodyc typedc
      namedc namesc inWc inNdc wNdc slotsc
      (fun f hf => by rw [hcoreW]; exact hfit f hf)
      (fun o ho => by rw [hcoreW]; exact houtfit o ho) outsOk outTy
  -- the wire table of the full entry's module is the closed machine's
  have hweb : Tools.ShippingEntrySoundness.weOf b =
      Tools.ShippingEntrySoundness.weOf (closeMachine d.shape.layout t') :=
    ((Tools.ShippingRegisterSoundness.weOf_congr_wires hbw).trans hzw).trans
      (Tools.ShippingRegisterSoundness.weOf_congr_wires hMw)
  have hwsub : ∀ p ∈ b.wires, p ∈ (closeMachine d.shape.layout t').wires := by
    intro p hp
    rw [hbw] at hp
    have := dropZW_wires_sub hp
    rw [hMw] at this
    exact this
  have hbouts : b.outputs = d.shape.layout.outs.map
      (fun o => ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port)) := hbo.trans houtsM
  -- its assignments and registers are the closed machine's
  have hsub : ∀ st ∈ b.body, st ∈ (closeMachine d.shape.layout t').body ∨
      Sparkle.IR.Machine.isInst st = true := by
    intro st hst
    rw [hbb] at hst
    rcases List.mem_append.mp (hperm.symm.subset hst) with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (List.all_eq_true.mp hLinst _ h0)
  -- an output port: its name is none of the closed module's own names
  have outFacts : ∀ q ∈ b.outputs, ∃ o ∈ d.shape.layout.outs,
      q = ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port) := by
    intro q hq
    rw [hbouts] at hq
    obtain ⟨o, ho, he⟩ := List.mem_map.mp hq
    exact ⟨o, ho, he.symm⟩
  refine
    { wn := ?_, ow := ?_, oi := ?_, ostable := ?_, ond := ?_, oty := ?_, kinds := ?_, asg := ?_,
      reg := ?_ }
  · -- the wire names are sanitize-stable
    intro p hp
    rcases hwCM p (hwsub p hp) with ha | ⟨y, hy, hpn⟩
    · exact Tools.ShippingNamesStable.sanitizeName_of_allocated ha
    · rw [hpn]
      exact Tools.ShippingNamesNext.sanitizeName_nextName hy
  · -- no wire has an output port's name
    intro q hq p hp heq
    obtain ⟨o, ho, hqo⟩ := outFacts q hq
    have hpo : p.name = o.name := heq.trans (congrArg Sparkle.IR.AST.Port.name hqo)
    obtain ⟨hna, -, hnn⟩ := Tools.ShippingMachineClose.outNameOk_facts (outsOk o ho).2
    rcases hwCM p (hwsub p hp) with ha | ⟨y, hy, hpn⟩
    · rw [hpo] at ha
      exact hna ha
    · exact hnn y (hpo.symm.trans hpn)
  · -- no input's sanitized name is an output port's name
    intro q hq p hp heq
    obtain ⟨o, ho, hqo⟩ := outFacts q hq
    have hqn : q.name = o.name := congrArg Sparkle.IR.AST.Port.name hqo
    rw [hqn] at heq
    have hok := (outsOk o ho).2
    simp only [outNameOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
    obtain ⟨hna, -, -⟩ := Tools.ShippingMachineClose.outNameOk_facts (outsOk o ho).2
    rw [hbi] at hp
    rcases hMinputs p hp with ha | hc | hr
    · rw [Tools.ShippingNamesStable.sanitizeName_of_allocated ha] at heq
      rw [heq] at ha
      exact hna ha
    · rw [hc, Tools.ShippingNamesClk.sanitizeName_clk] at heq
      exact hok.2 heq.symm
    · rw [hr, Tools.ShippingNamesClk.sanitizeName_rst] at heq
      exact hok.1.2 heq.symm
  · -- the output port names are sanitize-stable
    intro q hq
    obtain ⟨o, ho, hqo⟩ := outFacts q hq
    rw [hqo]
    exact hon o ho
  · -- distinct output names
    rw [hbouts, List.map_map]
    exact outsNodup
  · -- scalar output ports
    intro q hq
    obtain ⟨o, ho, hqo⟩ := outFacts q hq
    rw [hqo]
    exact Tools.ShippingTextTyped.scalarTy_spec (hoty o ho)
  · -- the statement kinds
    intro st hst
    rcases hsub st hst with h0 | h0
    · rcases hkCM st h0 with ⟨l, r, he⟩ | ⟨o, c', rk, i, iv, he⟩
      · subst he
        rfl
      · subst he
        rfl
    · cases st with
      | inst mn iname conns => rfl
      | _ => exact Tools.ShippingChecksDerived.ff_absurd h0
  · -- the assignments
    intro l r hm
    rcases hsub _ hm with h0 | h0
    · obtain ⟨n, ht, hl⟩ := haCM l r h0
      refine ⟨n, ?_, ?_⟩
      · rw [hweb]
        exact ht
      · rcases hl with hl | ⟨q, hq, h1, h2⟩
        · left
          rw [hweb]
          exact hl
        · right
          have e : b.outputs = (closeMachine d.shape.layout t').outputs :=
            hbouts.trans hoCM.symm
          refine ⟨q, ?_, h1, h2⟩
          rw [e]
          exact hq
    · exact Tools.ShippingChecksDerived.ff_absurd h0
  · -- the registers
    intro o c' rk i iv hm
    rcases hsub _ hm with h0 | h0
    · have ht := hrCM o c' rk i iv h0
      rw [hweb]
      exact ht
    · exact Tools.ShippingChecksDerived.ff_absurd h0

set_option maxHeartbeats 4000000 in
/-- **The full entry's module of a machine with calls is typed in its own
wire table**, with its output ports resolved by the emitter's width map. -/
theorem core_closed_typedIn {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    -- the two data conditions on the output ports
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    Tools.ShippingTextTyped.TypedIn b :=
  core_closed_typedIn_ran d ok hbody hC hslots hdomB hins outTy hnomem hpost
    (Tools.ShippingMachineRan.machineRan_of_closes hcore entry hB closes) hon hoty

set_option maxHeartbeats 4000000 in
/-- **The four hypotheses of `core_text_same`, on the full entry's module,
from the core run** (`hwn`, `hread`, `hA`, `hR`, verbatim). -/
theorem core_closed_typed {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hclean : (d.shape.layout.outs.map (·.name)).all Tools.ShippingNamesStable.cleanB = true)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    (∀ p ∈ b.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) ∧
    (∀ x ∈ Tools.ShippingSeqSVSoundness.seqNames b.body, x ∈ b.wires.map (·.name)) ∧
    (∀ l r, Stmt.assign l r ∈ b.body →
      Tools.ShippingSeqCheckTyped.Decl (Tools.ShippingDesignSV.wofOf b) l ∧
        Tools.ShippingTypedExprSoundness.TypedExpr (Tools.ShippingDesignSV.weS b) r
          (Tools.ShippingDesignSV.weS b l) ∧
        ∀ x ∈ Sparkle.IR.Reorder.refsOf r,
          Tools.ShippingSeqCheckTyped.Decl (Tools.ShippingDesignSV.wofOf b) x) ∧
    (∀ o c rk i iv, Stmt.register o c rk i iv ∈ b.body →
      (∃ k, Tools.ShippingDesignSV.wofOf b o = some k) ∧
        Tools.ShippingTypedExprSoundness.TypedExpr (Tools.ShippingDesignSV.weS b) i
          (Tools.ShippingDesignSV.weS b o) ∧
        ∀ x ∈ Sparkle.IR.Reorder.refsOf i,
          Tools.ShippingSeqCheckTyped.Decl (Tools.ShippingDesignSV.wofOf b) x) := by
  have h := core_closed_typedIn d ok hbody hC hslots hdomB hins outTy hnomem hB hcore hpost
    entry closes
    (fun o ho => Tools.ShippingNamesStable.sanitizeName_of_cleanB
      (List.all_eq_true.mp hclean o.name (List.mem_map.mpr ⟨o, ho, rfl⟩)))
    hoty
  obtain ⟨hread, hA, hR⟩ := h.text
  exact ⟨h.wn, hread, hA, hR⟩

set_option maxHeartbeats 4000000 in
/-- **Conjuncts 2 and 3 of `textCheckI` of the RAW full-entry module**, from
the core run: the emitted-text check and the width tables, with no optimizer
in the statement. -/
theorem core_text_raw {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf b)
        (Tools.ShippingDesignSV.weS b) b.body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames b.body).all
        (fun x => Sparkle.IR.RegDedup.declWidth b x == Tools.ShippingDesignSV.weS b x) = true :=
  (core_closed_typedIn d ok hbody hC hslots hdomB hins outTy hnomem hB hcore hpost entry closes
    hon hoty).seqCheck

end Tools.ShippingClosedTyped
