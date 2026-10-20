import Tools.ShippingWireNamesRun
-- BUILT by the integrator: l51 exit 0 (528 jobs) (round par/init, base 87874a82 + merge of poc 853b1608). Writing-time guesses g1-g4 below accepted.
-- Writing-time guesses: (g1) the run destructuring is copied from `wireNames_runMT`
-- (`machine_run_of_core`, `closes`, `subst hres'`, `synthesizeMachineCertified_runs`); in the
-- branch without calls `hm : M = closeMachine …` is used by `rw` (not `subst`, M is a variable
-- of the statement and of `hmem`); (g2) `simp [Sparkle.IR.Machine.closeMachine, hpw]` computes
-- the closed body/wires from `packedWire? t'.body = some coreW` (as `closeMachine_typed` does);
-- (g3) `injection he with h1 h2 h3 h4 h5` on two `Stmt.register` gives the five field
-- equalities; (g4) `Tools.ShippingMachineClose.Zip₂.get slotsc k p f hp hf : SlotOk …`
-- unfolds to `weOf t' p.name = f.width ∧ 0 < f.width` by `.1`/`.2`.

/-! # Every register of the core module is a slot's, at the slot's width (round par/init, L5)

`slotRegs_runMT`: from the core run of a machine-route declaration (the premises of
`closedTransition_of_run` plus the run's `ChildBnd`, `MachineDefines`, `MachineClosesAt`), every
register statement of the core module `M` is the register of some slot `f`: its reset value is
`f.init` and its declared width `weOf M r` is `f.width`. With or without calls.

`MachineWired` states the width only without calls (`shape.insts = [] → …`); this lemma does
not mention `ids`, `cache`, `regs`, so it applies to the registers of ANY `MachineWired` of the
same `M` (whose unconditional conjunct gives each slot's register statement). The proof reads
the run: the module is `closeMachine lay t'` (no calls) or a closing of it (`CloseCalls.some`:
same wires, body a permutation of `closeMachine`'s body ++ instance statements); the registers of
`closeMachine` are `registers lay.resetKind ps lay.slots` (the transition's body is assignments,
`nextAssigns`/`outAssigns` are assignments); `SlotOk` of the transition gives the width, kept
by `closeMachine` (`weOf_wires_append`). No new fact about the compiler, no producer change;
nothing added to `RefLaws` or a trusted list. -/
namespace Tools.ShippingSlotRegsRun
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
open Tools.ShippingMemKid
open Tools.ShippingClosedTyped

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The registers of a closed machine are the slots', at the transition's widths. -/
theorem closeMachine_regs {t : Sparkle.IR.AST.Module} {lay : Layout} {B : List Stmt} {w : String}
    (hbody : t.body = B ++ [.assign "out" (.ref w)])
    (typed : Tools.ShippingTypedPostSoundness.TypedStmts (weOf t) t.body)
    (slots : Tools.ShippingMachineClose.Zip₂ (Tools.ShippingMachineClose.SlotOk (weOf t))
      (t.inputs.drop (t.inputs.length - lay.slots.length)) lay.slots)
    {r c : String} {rs : String × Sparkle.IR.Type.ResetKind} {inp : Sparkle.IR.AST.Expr}
    {init : Int} (hmem : Stmt.register r c rs inp init ∈ (closeMachine lay t).body) :
    ∃ f ∈ lay.slots, init = Int.ofNat f.init ∧ weOf (closeMachine lay t) r = f.width := by
  have hpw : packedWire? t.body = some w := by simp [packedWire?, hbody]
  have hCb : (closeMachine lay t).body = t.body.dropLast ++
      nextAssigns w (t.inputs.drop (t.inputs.length - lay.slots.length)) lay.slots ++
      registers lay.resetKind (t.inputs.drop (t.inputs.length - lay.slots.length)) lay.slots ++
      outAssigns w lay.outs := by
    simp [closeMachine, hpw]
  have hCw : (closeMachine lay t).wires = t.wires ++
      (t.inputs.drop (t.inputs.length - lay.slots.length)).map
        (fun p => ({ name := nextName p.name, ty := p.ty } : Port)) := by
    simp [closeMachine, hpw]
  rw [hCb] at hmem
  simp only [List.mem_append] at hmem
  rcases hmem with ((hB | hN) | hR) | hO
  · have := List.all_eq_true.mp typed.isAssign _ (List.dropLast_subset _ hB)
    simp [Sparkle.IR.RegDedup.isAssign] at this
  · obtain ⟨l, rr, he⟩ := Tools.ShippingMachineClose.nextAssigns_assigns w _ lay.slots _ hN
    cases he
  · obtain ⟨k, p, f, hp, hf, he⟩ :=
      Tools.ShippingMachineCleanup.registers_mem _ _ lay.slots _ hR
    injection he with h1 h2 h3 h4 h5
    subst h1 h5
    have hsl := Tools.ShippingMachineClose.Zip₂.get slots k p f hp hf
    have hpos : 0 < weOf t p.name := by rw [hsl.1]; exact hsl.2
    refine ⟨f, List.mem_of_getElem? hf, rfl, ?_⟩
    rw [Tools.ShippingMachineClose.weOf_wires_append (m := t) hCw hpos]
    exact hsl.1
  · simp only [outAssigns, List.mem_map] at hO
    obtain ⟨o, _, he⟩ := hO
    cases he

set_option maxHeartbeats 4000000 in
/-- **L5: every register statement of the core module is a slot's register, at the slot's
reset value and width**, from the core run (with or without calls). -/
theorem slotRegs_runMT {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    {w w1 : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ∀ (r c' : String) (rs : String × Sparkle.IR.Type.ResetKind) (inp : Sparkle.IR.AST.Expr)
      (init : Int), Stmt.register r c' rs inp init ∈ M.body →
      ∃ f ∈ d.shape.layout.slots, init = Int.ofNat f.init ∧ weOf M r = f.width := by
  intro r c' rs inp init hmem
  -- the run (copied from `wireNames_runMT`)
  obtain ⟨_, bb, rr, w9, w10, hrun9, hw9, hd9, hres⟩ :=
    machine_run_of_core hcore entry hB
  have hne := closes bb _ _ _ hw9 hd9 hrun9
  cases rr with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ := synthesizeMachineCertified_runs hw9 hrun9
  obtain ⟨Bc, coreW, hbodyc, typedc, -, -, -, -, -, slotsc, -⟩ :=
    Tools.ShippingClosedTransitionTyped.closedTransition_of_run d ok hbody hC hslots hdomB run hcl
  rcases hmt with ⟨-, hm, -⟩ | ⟨-, children, hcc, -⟩
  · -- without calls: the module is the closed machine
    rw [hm] at hmem ⊢
    exact closeMachine_regs hbodyc typedc slotsc hmem
  · -- with calls: the closing keeps the wires and adds instance statements only
    obtain ⟨hMw, -, -, L, hLinst, hperm, -⟩ := hcc.some
    have hmemC : Stmt.register r c' rs inp init ∈ (closeMachine d.shape.layout t').body := by
      rcases List.mem_append.mp (hperm.mem_iff.mpr hmem) with h | h
      · exact h
      · have := List.all_eq_true.mp hLinst _ h
        simp [Sparkle.IR.Machine.isInst] at this
    obtain ⟨f, hf, hinit, hwd⟩ := closeMachine_regs hbodyc typedc slotsc hmemC
    refine ⟨f, hf, hinit, ?_⟩
    rw [Tools.ShippingMachineEntry.weOf_congr_wires hMw]
    exact hwd

end Tools.ShippingSlotRegsRun
