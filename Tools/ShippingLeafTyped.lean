import Tools.ShippingChecksMaskedLeaf
import Tools.ShippingClosedTyped
import Tools.ShippingChecksDesign
import Tools.ShippingPrintGuard
import Tools.ShippingDesignSVLeaf

/-! # A LEAF machine's module is typed, and passes the children's check (G1, round optfb-7)

`kidsPass C (kidCheck C n) o.body` asks, of each instance's child module,
`leafCheck` (depth 0) or `designCheck C k` (deeper). For a child that is a
machine WITHOUT calls — its module is what its own full entry returned
(`RealChild`): the zero-width cleanup of `closeMachine lay t'`, or the
CHECKED MERGE of that — this file gives:

## Pure

* instance-free bodies (`body.all seqStmtOk`): `linkedWF_seq`,
  `instNames_seq`, `noSelfRead_seq`, `portsMatchB_seq`, `kidsPass_seq`;
* `leafNames_sub`: the names `leafCheck` compares are among `seqNames`;
* `kidCheck_leaf_of_text`: `kidCheck C n m = true` at EVERY depth and for
  EVERY child map, for an instance-free `m` whose emitted-text check and
  width tables hold (conjuncts 2, 3 of `textCheckI`);
* `PortsIn m`: the port / wire half of `TypedIn m` (it does not mention the
  body); `PortsIn.of_ports` (it transfers along equal ports and wires);
  `PortsIn.wof_output` (`moduleWof m q.name = some q.ty.bitWidth` for an
  output port `q`).

## From a run

* `leaf_run_typedIn`: over a run of the full entry of a machine without
  calls, the returned module `b` is `m0` or `mergeChecked m0` with
  `TypedIn m0` and `m0.body.all seqStmtOk`; and `PortsIn b`,
  `b.body.all seqStmtOk` hold of `b` ITSELF (the merge keeps ports and
  wires: `mergeChecked_ports`, `mergeChecked_seqOk`). The chain is
  `core_closed_typedIn`'s with `M = closeMachine lay t'` (no closing of
  calls): `closedTransition_of_run`, `closeMachine_typed`, the cleanup
  clause of `MachineWired`.
* `leaf_real_typedIn`: the same from a `RealChild` witness.
* `leaf_real_kidK`: `∀ C n, kidCheck C n y.1 = true` (and the same of the
  child's own design, which is empty) — under ONE hypothesis that is not
  derived, `hmergePrint`.

## What is NOT derived: the text of a MERGED leaf

`mergeChecked m0` is `m0` or `mergeDuplicates m0`, the latter kept when
`refineCheck m0 r && masksKept m0 r` (`Sparkle/IR/RefineCheck.lean` 257–264).
For a body with a register `mergeDuplicates m0 = mergeDuplicatesRaw m0`
(`Sparkle/IR/RegDedup.lean` 305–311): the body `mergeDuplicatesParts`
computes — an `Id.run do` program over hash maps (partition refinement,
then a rewrite of the statements). No theorem describes its statements;
`masksKept` is about the output assignments' masks; `refineCheck` is a
check on values (that it has no name, declaredness or operand-width
conjunct is recorded in `docs/parallel/G1-designCheck-text.md`, section D —
NOT re-read this round). So neither `TypedIn (mergeChecked m0)` nor
`seqCheck … (mergeChecked m0).body` follows from `TypedIn m0`.

The hypothesis of `leaf_real_kidK` is exactly that gap, in the form a print
guard would prove:

    hmergePrint : ∀ m0, y.1 = mergeChecked m0 →
      y.1 = m0 ∨ Sparkle.IR.PrintGuard.printOk y.1 = true

With the guard `… && masksKept m r && Sparkle.IR.PrintGuard.printOk r` in
`mergeChecked`'s last branch (the pattern of `keepGuarded`), `mergeChecked
m0 = m0 ∨ printOk (mergeChecked m0) = true` holds for every `m0` whose body
is not assignments only (the analogue of `deinline_print`), which is
`hmergePrint`.

IMPLEMENTED since (round par/a-1) for bodies that are not assignments only:
`mergeChecked`'s last branch asks `printOk` of the merge
(`Sparkle.IR.RefineCheck.mergeChecked_print`), `leaf_run_typedIn` also
returns "with a slot, `m0`'s body is not assignments only", and
`leaf_real_kidK_reg` is `leaf_real_kidK` for a leaf child WITH A REGISTER
without `hmergePrint`. For a slotless leaf (an assignment-only body) the
merge is `mergeDuplicates`' own validated one, not guarded: there
`hmergePrint` stays a hypothesis (`leaf_real_kidK`).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingLeafTyped
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
open Tools.ShippingChecksDerived (ff_absurd)
open Tools.ShippingChecksDepth (and_true_intro)

/-! ## Instance-free bodies -/

/-- A predicate true on assignments and registers is true on an
assignments-and-registers body. -/
theorem seq_all {body : List Stmt} (hs : body.all seqStmtOk = true) (f : Stmt → Bool)
    (hf : ∀ st, seqStmtOk st = true → f st = true) : body.all f = true :=
  List.all_eq_true.mpr fun st hst => hf st (List.all_eq_true.mp hs st hst)

theorem bodyInstOuts_seq (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) :
    ∀ (body : List Stmt), body.all seqStmtOk = true →
      Tools.ShippingHierOpen.bodyInstOuts C body = []
  | [], _ => rfl
  | st :: rest, h => by
    have h' := h
    rw [List.all_cons, Bool.and_eq_true] at h'
    have ih := bodyInstOuts_seq C rest h'.2
    have hst : Tools.ShippingHierOpen.stmtInstOuts C st = [] := by
      cases st <;> first | rfl | exact ff_absurd h'.1
    have e : Tools.ShippingHierOpen.stmtInstOuts C st ++
        Tools.ShippingHierOpen.bodyInstOuts C rest = [] ++ [] := by
      rw [hst, ih]
    exact e

/-- An assignments-and-registers body is linked-well-formed, whatever the
children. -/
theorem linkedWF_seq (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) :
    ∀ (body : List Stmt), body.all seqStmtOk = true →
      Tools.ShippingHierOpen.linkedWF C body = true
  | [], _ => rfl
  | st :: rest, h => by
    have h' := h
    rw [List.all_cons, Bool.and_eq_true] at h'
    have ih := linkedWF_seq C rest h'.2
    have hb := bodyInstOuts_seq C rest h'.2
    cases st with
    | assign l r =>
      first
        | simp [Tools.ShippingHierOpen.linkedWF, hb, ih]
        | (simp only [Tools.ShippingHierOpen.linkedWF, hb, ih]
           simp [List.contains, List.elem])
    | register o c rk i iv =>
      first
        | exact ih
        | (simp only [Tools.ShippingHierOpen.linkedWF]; exact ih)
    | _ => exact ff_absurd h'.1

theorem instNames_seq : ∀ (body : List Stmt), body.all seqStmtOk = true →
    Tools.ShippingHierState.instNames body = []
  | [], _ => rfl
  | st :: rest, h => by
    have h' := h
    rw [List.all_cons, Bool.and_eq_true] at h'
    have ih := instNames_seq rest h'.2
    cases st with
    | assign l r =>
      first
        | exact ih
        | (simp only [Tools.ShippingHierState.instNames]; exact ih)
    | register o c rk i iv =>
      first
        | exact ih
        | (simp only [Tools.ShippingHierState.instNames]; exact ih)
    | _ => exact ff_absurd h'.1

theorem noSelfRead_seq (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
    {body : List Stmt} (hs : body.all seqStmtOk = true) :
    Tools.ShippingHierPremisesBase.noSelfRead C body = true := by
  unfold Tools.ShippingHierPremisesBase.noSelfRead
  refine seq_all hs _ (fun st hst => ?_)
  cases st <;> first | rfl | exact ff_absurd hst

theorem portsMatchB_seq (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
    {m : Sparkle.IR.AST.Module} (hs : m.body.all seqStmtOk = true) :
    Tools.ShippingDesignSV.portsMatchB C m = true := by
  unfold Tools.ShippingDesignSV.portsMatchB
  refine seq_all hs _ (fun st hst => ?_)
  cases st <;> first | rfl | exact ff_absurd hst

theorem kidsPass_seq (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
    (g : Sparkle.IR.AST.Module → Bool) {body : List Stmt} (hs : body.all seqStmtOk = true) :
    Tools.ShippingDesignSV.kidsPass C g body = true := by
  unfold Tools.ShippingDesignSV.kidsPass
  refine seq_all hs _ (fun st hst => ?_)
  cases st <;> first | rfl | exact ff_absurd hst

/-- The names whose width an operand's evaluation consults are among its
references. -/
theorem wRefs_sub (e : Sparkle.IR.AST.Expr) :
    ∀ x ∈ Tools.ShippingDesignSV.wRefs e, x ∈ Sparkle.IR.Reorder.refsOf e := by
  intro x hx
  cases e with
  | ref n =>
    have hx' : x ∈ ([] : List String) := hx
    cases hx'
  | _ => exact hx

/-- On an assignments-and-registers body, the names `leafCheck` compares
are among the names `textCheckI` compares. -/
theorem leafNames_sub : ∀ (body : List Stmt), body.all seqStmtOk = true → ∀ (x : String),
    x ∈ Tools.ShippingDesignSV.leafNames body → x ∈ Tools.ShippingSeqSVSoundness.seqNames body
  | [], _, _, h => h
  | st :: rest, hs, x, h => by
    have hs' := hs
    rw [List.all_cons, Bool.and_eq_true] at hs'
    cases st with
    | assign l r =>
      have h' : x ∈ Tools.ShippingDesignSV.wRefs r ++ Tools.ShippingDesignSV.leafNames rest := h
      show x ∈ Sparkle.IR.Reorder.refsOf r ++ Tools.ShippingSeqSVSoundness.seqNames rest
      rcases List.mem_append.mp h' with h1 | h1
      · exact List.mem_append.mpr (Or.inl (wRefs_sub r x h1))
      · exact List.mem_append.mpr (Or.inr (leafNames_sub rest hs'.2 x h1))
    | register o c rk i iv =>
      have h' : x ∈ o :: (Tools.ShippingDesignSV.wRefs i ++
          Tools.ShippingDesignSV.leafNames rest) := h
      show x ∈ o :: (Sparkle.IR.Reorder.refsOf i ++ Tools.ShippingSeqSVSoundness.seqNames rest)
      rcases List.mem_cons.mp h' with h1 | h1
      · exact List.mem_cons.mpr (Or.inl h1)
      · rcases List.mem_append.mp h1 with h2 | h2
        · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl (wRefs_sub i x h2))))
        · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr
            (Or.inr (leafNames_sub rest hs'.2 x h2))))
    | _ => exact ff_absurd hs'.1

/-! ## The children's check of an instance-free module, from its text check -/

variable {m : Sparkle.IR.AST.Module}

/-- `leafCheck` of an assignments-and-registers module from conjuncts 2 and
3 of `textCheckI`. -/
theorem leafCheck_of_text (hs : m.body.all seqStmtOk = true)
    (h2 : Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf m)
      (Tools.ShippingDesignSV.weS m) m.body = true)
    (h3 : (Tools.ShippingSeqSVSoundness.seqNames m.body).all
      (fun x => Sparkle.IR.RegDedup.declWidth m x == Tools.ShippingDesignSV.weS m x) = true) :
    Tools.ShippingDesignSV.leafCheck m = true := by
  have hA : m.body.all Tools.ShippingDesignSV.seqStmtOkA = true :=
    seq_all hs _ (fun st hst => by cases st <;> first | rfl | exact ff_absurd hst)
  have hM : m.body.all Tools.ShippingMemSVSoundness.memOpsRefs = true :=
    seq_all hs _ (fun st hst => by cases st <;> first | rfl | exact ff_absurd hst)
  have hW : (Tools.ShippingDesignSV.leafNames m.body).all
      (fun x => Sparkle.IR.RegDedup.declWidth m x == Tools.ShippingDesignSV.weS m x) = true :=
    List.all_eq_true.mpr fun x hx =>
      List.all_eq_true.mp h3 x (leafNames_sub m.body hs x hx)
  have hS : Tools.ShippingDesignSV.hasSyncMem m.body = false := by
    cases hS : Tools.ShippingDesignSV.hasSyncMem m.body with
    | false => rfl
    | true =>
      unfold Tools.ShippingDesignSV.hasSyncMem at hS
      obtain ⟨st, hst, hp⟩ := List.any_eq_true.mp hS
      have hk := List.all_eq_true.mp hs st hst
      cases st <;> first | exact ff_absurd hk | exact ff_absurd hp
  unfold Tools.ShippingDesignSV.leafCheck
  refine and_true_intro (and_true_intro (and_true_intro hA hM) hW) ?_
  rw [hS]
  first
    | exact h2
    | simpa using h2

/-- `textCheckI` of an assignments-and-registers module, whatever the child
map, from conjuncts 2 and 3. -/
theorem textCheckI_leaf_of_text
    (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
    (hs : m.body.all seqStmtOk = true)
    (h2 : Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf m)
      (Tools.ShippingDesignSV.weS m) m.body = true)
    (h3 : (Tools.ShippingSeqSVSoundness.seqNames m.body).all
      (fun x => Sparkle.IR.RegDedup.declWidth m x == Tools.ShippingDesignSV.weS m x) = true) :
    Tools.ShippingDesignSV.textCheckI C m = true :=
  Tools.ShippingChecksDesign.textCheckI_of
    (seq_all hs _ (fun st hst => by cases st <;> first | rfl | exact ff_absurd hst))
    h2 h3 (linkedWF_seq C m.body hs)
    (by rw [instNames_seq m.body hs]; exact List.nodup_nil)
    (noSelfRead_seq C hs) (portsMatchB_seq C hs)
    (fun mn iname conns hm => ff_absurd (List.all_eq_true.mp hs _ hm))

/-- **What `designCheck` asks of a child, for an instance-free module**: at
every depth and for every child map. -/
theorem kidCheck_leaf_of_text
    (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat)
    (hs : m.body.all seqStmtOk = true)
    (h2 : Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf m)
      (Tools.ShippingDesignSV.weS m) m.body = true)
    (h3 : (Tools.ShippingSeqSVSoundness.seqNames m.body).all
      (fun x => Sparkle.IR.RegDedup.declWidth m x == Tools.ShippingDesignSV.weS m x) = true) :
    Tools.ShippingChecksDesign.kidCheck C n m = true := by
  cases n with
  | zero =>
    show Tools.ShippingDesignSV.leafCheck m = true
    exact leafCheck_of_text hs h2 h3
  | succ k =>
    show Tools.ShippingDesignSV.designCheck C k m = true
    rw [Tools.ShippingChecksDesign.designCheck_eq]
    exact and_true_intro (textCheckI_leaf_of_text C hs h2 h3) (kidsPass_seq C _ hs)

/-! ## The port / wire half of `TypedIn` -/

/-- The facts of `Tools.ShippingTextTyped.TypedIn` that do not mention the
body: sanitize-stable wire names, and output ports the emitter's width map
resolves to themselves. -/
structure PortsIn (m : Sparkle.IR.AST.Module) : Prop where
  wn : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name
  ow : ∀ q ∈ m.outputs, ∀ p ∈ m.wires, p.name ≠ q.name
  oi : ∀ q ∈ m.outputs, ∀ p ∈ m.inputs, Sparkle.Backend.Verilog.sanitizeName p.name ≠ q.name
  ostable : ∀ q ∈ m.outputs, Sparkle.Backend.Verilog.sanitizeName q.name = q.name
  ond : (m.outputs.map (·.name)).Nodup
  oty : ∀ q ∈ m.outputs, q.ty = .bit ∨ ∃ n, q.ty = .bitVector n

theorem PortsIn.of_typedIn (h : Tools.ShippingTextTyped.TypedIn m) : PortsIn m :=
  { wn := h.wn, ow := h.ow, oi := h.oi, ostable := h.ostable, ond := h.ond, oty := h.oty }

/-- It transfers to a module with the same ports and wires. -/
theorem PortsIn.of_ports {m' : Sparkle.IR.AST.Module} (h : PortsIn m)
    (hi : m'.inputs = m.inputs) (ho : m'.outputs = m.outputs) (hw : m'.wires = m.wires) :
    PortsIn m' := by
  refine { wn := ?_, ow := ?_, oi := ?_, ostable := ?_, ond := ?_, oty := ?_ }
  · intro p hp
    rw [hw] at hp
    exact h.wn p hp
  · intro q hq p hp
    rw [ho] at hq
    rw [hw] at hp
    exact h.ow q hq p hp
  · intro q hq p hp
    rw [ho] at hq
    rw [hi] at hp
    exact h.oi q hq p hp
  · intro q hq
    rw [ho] at hq
    exact h.ostable q hq
  · rw [ho]
    exact h.ond
  · intro q hq
    rw [ho] at hq
    exact h.oty q hq

/-- **An output port's entry in the emitter's width map is its type's
width.** -/
theorem PortsIn.wof_output (h : PortsIn m) {q : Port} (hq : q ∈ m.outputs) :
    Tools.SVParser.RoundtripProof.moduleWof m q.name = some q.ty.bitWidth :=
  Tools.ShippingTextTyped.moduleWof_output (m := m) (q := q)
    (fun p hp => by
      rw [h.wn p hp]
      exact h.ow q hq p hp)
    (h.oi q hq) h.ostable h.ond hq (h.oty q hq)

theorem PortsIn.weS_output (h : PortsIn m) {q : Port} (hq : q ∈ m.outputs) :
    Tools.ShippingDesignSV.weS m q.name = q.ty.bitWidth := by
  show (Tools.SVParser.RoundtripProof.moduleWof m q.name).getD 0 = q.ty.bitWidth
  exact congrArg (fun o : Option Nat => o.getD 0) (h.wof_output hq)

/-! ## From a run -/

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **A leaf machine's returned module is a typed module or its checked
merge**, over every run of the full entry; its ports and statement kinds are
the typed module's either way. -/
theorem leaf_run_typedIn {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (closesM : MachineCloses mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    ∃ m0 : Sparkle.IR.AST.Module, (b = m0 ∨ b = mergeChecked m0) ∧
      Tools.ShippingTextTyped.TypedIn m0 ∧ m0.body.all seqStmtOk = true ∧
      PortsIn b ∧ b.body.all seqStmtOk = true ∧
      (d.shape.layout.slots ≠ [] → m0.body.all Sparkle.IR.RegDedup.isAssign = false) := by
  obtain ⟨M, D, w1, hcore, hpost, hdesM⟩ := synthesizeCombinational_parts hr
  have closes : MachineClosesAt mctx mref cctx cref c d.shape := machineClosesAt_of_closes closesM
  obtain ⟨bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
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
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hclean, -⟩ := wired
  obtain ⟨⟨hzb, hzw, -, hzo⟩, -, hregs, -, -, -, -, -, hseq⟩ := hclean hno outTy
  -- with a slot, the core module has a register: the cleaned body is not
  -- assignments only (the steps of `leaf_run_masked`, copied)
  have hnAZ : d.shape.layout.slots ≠ [] →
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body.all Sparkle.IR.RegDedup.isAssign =
        false := by
    intro hsl
    obtain ⟨f0, hf0⟩ : ∃ f, d.shape.layout.slots[0]? = some f := by
      cases hs : d.shape.layout.slots with
      | nil => exact absurd hs hsl
      | cons f _ => exact ⟨f, rfl⟩
    obtain ⟨r0n, hr0n⟩ : ∃ r, regs[0]? = some r := by
      cases hrs : regs with
      | nil =>
        have hreg0 : regs.length = 0 := by simp [hrs]
        have hsb : d.slotBs.length = d.ss.length := by
          simp only [MachineData.slotBs, List.length_take, List.length_drop]
          omega
        have : d.shape.layout.slots.length = 0 := by omega
        rw [List.length_eq_zero_iff] at this; exact absurd this hsl
      | cons r _ => exact ⟨r, rfl⟩
    obtain ⟨_, _, rk0, inp0, hm0⟩ := hregs 0 r0n f0 hr0n hf0
    have hnA : M.body.all Sparkle.IR.RegDedup.isAssign = false := by
      apply List.all_eq_false.mpr
      exact ⟨_, hm0, by simp [Sparkle.IR.RegDedup.isAssign]⟩
    rw [hzb]
    exact hnA
  obtain ⟨-, -, hwCM, hiCM, hoCM, hkCM, haCM, hrCM⟩ :=
    Tools.ShippingCloseMachineTyped.closeMachine_typed (lay := d.shape.layout) hbodyc typedc
      namedc namesc inWc inNdc wNdc slotsc
      (fun f hf => by rw [hcoreW]; exact hfit f hf)
      (fun o ho => by rw [hcoreW]; exact houtfit o ho) outsOk outTy
  have hM' : M = closeMachine d.shape.layout t' := hMeq
  -- the cleaned module against the closed machine
  have hZb : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body =
      (closeMachine d.shape.layout t').body := by
    rw [hzb, hM']
  have hZi : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).inputs =
      (closeMachine d.shape.layout t').inputs := by
    rw [Tools.ShippingOutsExtractedParts.dropZW_inputs M, hM']
  have hZo : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).outputs = d.shape.layout.outs.map
      (fun o => ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port)) := by
    rw [hzo, hM']
    exact hoCM
  have hweZ : Tools.ShippingEntrySoundness.weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) =
      Tools.ShippingEntrySoundness.weOf (closeMachine d.shape.layout t') :=
    hzw.trans (congrArg Tools.ShippingEntrySoundness.weOf hM')
  have hwsub : ∀ p ∈ (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).wires,
      p ∈ (closeMachine d.shape.layout t').wires := by
    intro p hp
    have h1 := Tools.ShippingClosedTyped.dropZW_wires_sub hp
    rw [hM'] at h1
    exact h1
  have outFacts : ∀ q ∈ (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).outputs,
      ∃ o ∈ d.shape.layout.outs,
        q = ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port) := by
    intro q hq
    rw [hZo] at hq
    obtain ⟨o, ho, he⟩ := List.mem_map.mp hq
    exact ⟨o, ho, he.symm⟩
  have hseqZ : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body.all seqStmtOk = true := by
    rw [hzb]
    exact hseq
  have hT : Tools.ShippingTextTyped.TypedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) := by
    refine
      { wn := ?_, ow := ?_, oi := ?_, ostable := ?_, ond := ?_, oty := ?_, kinds := ?_,
        asg := ?_, reg := ?_ }
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
      rw [hZi] at hp
      rcases hiCM p hp with ha | hc | hr
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
      rw [hZo, List.map_map]
      exact outsNodup
    · -- scalar output ports
      intro q hq
      obtain ⟨o, ho, hqo⟩ := outFacts q hq
      rw [hqo]
      exact Tools.ShippingTextTyped.scalarTy_spec (hoty o ho)
    · -- the statement kinds
      intro st hst
      rw [hZb] at hst
      rcases hkCM st hst with ⟨l, r, he⟩ | ⟨o, c', rk, i, iv, he⟩
      · subst he
        rfl
      · subst he
        rfl
    · -- the assignments
      intro l r hm
      rw [hZb] at hm
      obtain ⟨n, ht, hl⟩ := haCM l r hm
      refine ⟨n, ?_, ?_⟩
      · rw [hweZ]
        exact ht
      · rcases hl with hl | ⟨q, hq, h1, h2⟩
        · left
          rw [hweZ]
          exact hl
        · right
          have e : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).outputs =
              (closeMachine d.shape.layout t').outputs := hZo.trans hoCM.symm
          refine ⟨q, ?_, h1, h2⟩
          rw [e]
          exact hq
    · -- the registers
      intro o c' rk i iv hm
      rw [hZb] at hm
      have ht := hrCM o c' rk i iv hm
      rw [hweZ]
      exact ht
  have hPZ : PortsIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) := PortsIn.of_typedIn hT
  refine ⟨Sparkle.IR.ZeroWidth.dropZeroWidthModule M, hpost, hT, hseqZ, ?_, ?_, hnAZ⟩
  · rcases hpost with h | h
    · rw [h]
      exact hPZ
    · rw [h]
      exact hPZ.of_ports
        (Sparkle.IR.RefineCheck.mergeChecked_ports _).1
        (Sparkle.IR.RefineCheck.mergeChecked_ports _).2.1
        (Sparkle.IR.RefineCheck.mergeChecked_ports _).2.2
  · rcases hpost with h | h
    · rw [h]
      exact hseqZ
    · rw [h]
      exact mergeChecked_seqOk hseqZ

/-- The same from a `RealChild` witness. -/
theorem leaf_real_typedIn {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    {y : Res} (h : RealChild mref cref c y) :
    ∃ m0 : Sparkle.IR.AST.Module, (y.1 = m0 ∨ y.1 = mergeChecked m0) ∧
      Tools.ShippingTextTyped.TypedIn m0 ∧ m0.body.all seqStmtOk = true ∧
      PortsIn y.1 ∧ y.1.body.all seqStmtOk = true ∧
      (d.shape.layout.slots ≠ [] → m0.body.all Sparkle.IR.RegDedup.isAssign = false) := by
  obtain ⟨mctx', cctx', w, w', hw, hr⟩ := h.inv
  exact leaf_run_typedIn d ok hbody hC hdomB hno hSS outTy hw hr
    (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx') hon hoty

/-- **A real leaf child's ports are resolved by the emitter's width map**
(no hypothesis on the merge: it keeps ports and wires). -/
theorem leaf_real_portsIn {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    {y : Res} (h : RealChild mref cref c y) : PortsIn y.1 := by
  obtain ⟨m0, -, -, -, hp, -, -⟩ :=
    leaf_real_typedIn d ok hbody hC hdomB hno hSS outTy entry closes hon hoty h
  exact hp

/-- **The children's check of a real leaf child**, at every depth and for
every child map — and of its own design's modules (there are none). The one
hypothesis not derived is `hmergePrint`: where the child's module is a
merge that changed it, the merged module passes the print guard. -/
theorem leaf_real_kidK {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    {y : Res} (h : RealChild mref cref c y)
    (hmergePrint : ∀ m0 : Sparkle.IR.AST.Module, y.1 = mergeChecked m0 →
      y.1 = m0 ∨ Sparkle.IR.PrintGuard.printOk y.1 = true) :
    (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
        Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
      ∀ g ∈ y.2.modules,
        ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n g = true := by
  obtain ⟨m0, hpost, hT, hs0, -, hs, -⟩ :=
    leaf_real_typedIn d ok hbody hC hdomB hno hSS outTy entry closes hon hoty h
  have hI := seqChild_of_real d ok hbody hno outTy entry closes h
  have htext : Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf y.1)
        (Tools.ShippingDesignSV.weS y.1) y.1.body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames y.1.body).all
        (fun x => Sparkle.IR.RegDedup.declWidth y.1 x == Tools.ShippingDesignSV.weS y.1 x) =
          true := by
    rcases hpost with e | e
    · rw [e]
      exact hT.seqCheck
    · rcases hmergePrint m0 e with e' | hp
      · rw [e']
        exact hT.seqCheck
      · exact Tools.ShippingPrintGuard.printOk_sound hp
  refine ⟨fun C n => kidCheck_leaf_of_text C n hs htext.1 htext.2, ?_⟩
  intro g hg
  rw [hI.design] at hg
  cases hg

/-- The identity-merge case of `leaf_real_kidK`: no print-guard hypothesis. -/
theorem leaf_real_kidK_id {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    {y : Res} (h : RealChild mref cref c y)
    (hmergeId : ∀ m0 : Sparkle.IR.AST.Module, y.1 = mergeChecked m0 → y.1 = m0) :
    (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
        Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
      ∀ g ∈ y.2.modules,
        ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n g = true :=
  leaf_real_kidK d ok hbody hC hdomB hno hSS outTy entry closes hon hoty h
    (fun m0 e => Or.inl (hmergeId m0 e))

/-- **The children's check of a real leaf child WITH A REGISTER**, at every
depth and for every child map — no hypothesis on the merge: the cleaned
module has a register, so its checked merge is the module itself or passes
the print guard (`Sparkle.IR.RefineCheck.mergeChecked_print`). -/
theorem leaf_real_kidK_reg {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    {y : Res} (h : RealChild mref cref c y) :
    (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
        Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
      ∀ g ∈ y.2.modules,
        ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n g = true := by
  obtain ⟨m0, hpost, hT, hs0, -, hs, hna⟩ :=
    leaf_real_typedIn d ok hbody hC hdomB hno hSS outTy entry closes hon hoty h
  have hI := seqChild_of_real d ok hbody hno outTy entry closes h
  have htext : Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf y.1)
        (Tools.ShippingDesignSV.weS y.1) y.1.body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames y.1.body).all
        (fun x => Sparkle.IR.RegDedup.declWidth y.1 x == Tools.ShippingDesignSV.weS y.1 x) =
          true := by
    rcases hpost with e | e
    · rw [e]
      exact hT.seqCheck
    · rcases Sparkle.IR.RefineCheck.mergeChecked_print (hna hsl) with e' | hp
      · have e2 : y.1 = m0 := e.trans e'
        rw [e2]
        exact hT.seqCheck
      · have hp' : Sparkle.IR.PrintGuard.printOk y.1 = true := by
          rw [e]
          exact hp
        exact Tools.ShippingPrintGuard.printOk_sound hp'
  refine ⟨fun C n => kidCheck_leaf_of_text C n hs htext.1 htext.2, ?_⟩
  intro g hg
  rw [hI.design] at hg
  cases hg

end Tools.ShippingLeafTyped
