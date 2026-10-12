import Tools.ShippingCombKidText
import Tools.ShippingLeafPorts
import Tools.ShippingPortsMatchRawLeafAny
import Tools.ShippingTypedWidthOk
import Tools.ShippingMergeClosed
import Tools.ShippingChecksGate
import Tools.ShippingMachineChildRun

/-! # The child-side facts of the one-output closing for a SLOTLESS LEAF MACHINE child with the one output `out` (G1, round par/a-10)

`Tools.ShippingOneOutConns.core_hierTyped₁` / `core_portsMatch_raw₁`,
`Tools.ShippingOneOutFacts.core_designCheckH` and
`Tools.ShippingChecksCoreGate.core_outsCheck_all_gate` ask, of each real
child `y` of a call entry: `hkidW`, `hkidT`, `hkidIn`, `hkidTy`, `hkidInD`,
`hkidK`, `hkidA`, `hkidR`. For a GATE child all of them come from
`GateChildPorts` / `ChildFull`. This file gives them for a child compiled by
the MACHINE route that has no register, no call, at least one hardware
`let` and the one output `out` (`pickByteH`).

## What existed (built) and what is new here

| hypothesis | for a slotless leaf machine child | source |
|---|---|---|
| `hkidW` | `SlotlessLeaf.outTys` + `hkidW_one` + the data condition `callWidthsStrict` | existing: `leaf_real_outTys_any`, `hkidW_one` |
| `hkidT` (`PortsIn y.1`) | `SlotlessLeaf.portsIn` | existing: `leaf_real_portsIn` |
| `hkidIn` (emitter widths) and `hkidInD` (IR widths) | `SlotlessLeaf.inWidths`: ONE statement, both tables | NEW: `inPort_both`, `leafPorts_inWidths2`, `leafPorts_inPortsOf_eq` — from the same `LeafPorts` facts (`args`, `argW`, `wal`, `pos`, `ins`) the built `LeafPorts.inWidths` uses |
| `hkidTy` (`childTyped (declWidth y.1) y.1`) | `SlotlessLeaf.childTyped` | NEW: `typedIn_childTyped_out`, `childTyped_post_out`, and the run theorem `leaf_run_typedIn_out` |
| `hkidK` | `SlotlessLeaf.kidK` | existing: `leaf_real_kidK_out` |
| `hkidA`, `hkidR` | `SlotlessLeaf.kidA`, `.kidR` | NEW (pure, from `ChildComb`): `comb_kidA`, `comb_kidR`; the `ChildComb` from the existing `machineChild_of_real` |

## Why `hkidTy` needed a run theorem

`leaf_real_typedIn` gives `y.1 = m0 ∨ y.1 = mergeChecked m0` with
`TypedIn m0`. `childTyped` of `mergeChecked m0` needs the merged module
typed, which `typedIn_mergeDuplicates_out` gives only for an
ASSIGNMENT-ONLY `m0`; and it needs `out` assigned exactly once. Neither
"`m0` is assignment-only" nor "`out` is written once" is in
`leaf_real_typedIn`'s conclusion (it has the opposite fact, for a machine
WITH slots), and the two existential witnesses of two separate theorems
about one run cannot be identified afterwards. So
`leaf_run_typedIn_out` is `leaf_run_typedIn`'s proof (copied by a script,
lines 374–573 of `Tools/ShippingLeafTyped.lean`, unchanged) with two
hypotheses added — no slot, the one output `out` — and the conclusion

    ∃ m0, (b = m0 ∨ b = mergeChecked m0) ∧ TypedIn m0 ∧
      m0.body.all isAssign = true ∧ count "out" (writesOf m0.body) = 1

(the two new conjuncts from `closeMachine_slotless_body`: without slots the
closed machine's body is the transition's assignments followed by the output
assignments; the transition's targets are allocated names, `out` is not).
Through the validated merge the writes are kept
(`mergeDuplicates_closed`, with `readsClosedB_of_all`: any body is
read-closed over the list of all the names it reads).

## Scope

ONE child kind: a machine without calls, WITHOUT slots, with at least one
`let`, with the one output `out`. Per-declaration data conditions are the
fields of `SlotlessLeaf` (decided by the kernel per child; conditions, not
reductions); `MachineDefines` of the child and its own closing
(`c.machine_closes`) stay inputs. Not covered: a leaf WITH slots (the
one-output closing refuses a child with a clock anyway), a child with
calls, several outputs.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingLeafOneOut
open Sparkle.IR.AST Sparkle.IR.Machine

/-! ## Pure: the closed machine without slots -/

/-- **Without slots the closed machine's body is the transition's
statements before the packed assignment, then the output assignments.** -/
theorem closeMachine_slotless_body {t : Sparkle.IR.AST.Module} {lay : Layout} {B : List Stmt}
    {w : String} (hbody : t.body = B ++ [.assign "out" (.ref w)]) (hsl : lay.slots = []) :
    (closeMachine lay t).body = B ++ outAssigns w lay.outs := by
  have hpw : packedWire? t.body = some w := by simp [packedWire?, hbody]
  have hdrop : t.body.dropLast = B := by simp [hbody]
  have hb : (closeMachine lay t).body =
      B ++ (nextAssigns w (t.inputs.drop (t.inputs.length - lay.slots.length)) lay.slots ++
        (registers lay.resetKind (t.inputs.drop (t.inputs.length - lay.slots.length)) lay.slots ++
          outAssigns w lay.outs)) := by
    first
      | simp [closeMachine, hpw, hdrop]
      | (unfold closeMachine
         simp only [hpw, hdrop, List.append_assoc])
  rw [hb, hsl, Tools.ShippingMachineChildComb.nextAssigns_nil,
    Tools.ShippingMachineChildComb.registers_nil, List.nil_append, List.nil_append]

/-- A name not in a list is counted zero times. -/
theorem count_zero {l : List String} {a : String} (h : a ∉ l) : List.count a l = 0 := by
  first
    | exact List.count_eq_zero_of_not_mem h
    | exact List.count_eq_zero.mpr h

/-- A name counted once is in the list. -/
theorem mem_of_count_one {l : List String} {a : String} (h : List.count a l = 1) : a ∈ l := by
  apply Classical.byContradiction
  intro hn
  have h0 : List.count a l = 0 := count_zero hn
  rw [h0] at h
  exact absurd h (by decide)

/-- **`out` is written exactly once** by assignments to allocated names
followed by the output assignments of a layout whose one output is `out`. -/
theorem count_out_slotless {B : List Stmt} {w : String} {outs : List OutField}
    (hBa : B.all Sparkle.IR.RegDedup.isAssign = true)
    (hBn : ∀ l r, Stmt.assign l r ∈ B → Sparkle.IR.NameHints.Allocated l)
    (hone : outs.map (·.name) = ["out"]) :
    List.count "out" (Sparkle.IR.Reorder.writesOf (B ++ outAssigns w outs)) = 1 := by
  have h0 : "out" ∉ Sparkle.IR.Reorder.writesOf B := by
    intro hm
    obtain ⟨r, hr⟩ := Tools.ShippingChecksGate.assign_of_writes hBa hm
    exact Tools.ShippingRegisterSoundness.not_allocated_out (hBn "out" r hr)
  have hc0 : List.count "out" (Sparkle.IR.Reorder.writesOf B) = 0 := count_zero h0
  have hw : Sparkle.IR.Reorder.writesOf (outAssigns w outs) = ["out"] := by
    cases outs with
    | nil => simp at hone
    | cons o rest =>
      cases rest with
      | nil =>
        have ho : o.name = "out" := by simpa using hone
        have h1 : Sparkle.IR.Reorder.writesOf (outAssigns w [o]) = [o.name] := by
          first
            | rfl
            | simp [outAssigns, Sparkle.IR.Reorder.writesOf, Sparkle.IR.Reorder.stmtWrites]
        exact h1.trans (congrArg (fun s : String => [s]) ho)
      | cons o2 rest2 => simp at hone
  have hc1 : List.count "out" (["out"] : List String) = 1 := by
    first
      | rfl
      | decide
      | simp
  have hc2 : List.count "out" (Sparkle.IR.Reorder.writesOf (outAssigns w outs)) = 1 :=
    (congrArg (List.count "out") hw).trans hc1
  have hap : List.count "out" (Sparkle.IR.Reorder.writesOf (B ++ outAssigns w outs)) =
      List.count "out" (Sparkle.IR.Reorder.writesOf B) +
        List.count "out" (Sparkle.IR.Reorder.writesOf (outAssigns w outs)) := by
    rw [Tools.ShippingTopoChecks.writesOf_append, List.count_append]
  omega

/-- **Any body is read-closed over a list holding every name it reads.** -/
theorem readsClosedB_of_all : ∀ (body : List Stmt) (S : List String),
    (∀ st ∈ body, ∀ n ∈ Sparkle.IR.Reorder.stmtReads st, n ∈ S) → readsClosedB S body = true
  | [], _, _ => rfl
  | st :: rest, S, h => by
    have h1 : (Sparkle.IR.Reorder.stmtReads st).all (fun n => S.contains n) = true := by
      rw [List.all_eq_true]
      intro n hn
      exact List.contains_iff_mem.mpr (h st (List.mem_cons_self ..) n hn)
    have h2 : readsClosedB (S ++ Sparkle.IR.Reorder.stmtWrites st) rest = true :=
      readsClosedB_of_all rest _ (fun st' hst' n hn =>
        List.mem_append_left _ (h st' (List.mem_cons_of_mem _ hst') n hn))
    show ((Sparkle.IR.Reorder.stmtReads st).all (fun n => S.contains n) &&
      readsClosedB (S ++ Sparkle.IR.Reorder.stmtWrites st) rest) = true
    exact (Bool.and_eq_true _ _).mpr ⟨h1, h2⟩

/-- The validated merge of an assignment-only body is assignment-only (the
step of `Tools.ShippingSeqChildIface.mergeChecked_seqOk`, as a lemma). -/
theorem mergeDuplicates_assign {r : Sparkle.IR.AST.Module}
    (hall : r.body.all Sparkle.IR.RegDedup.isAssign = true) :
    (Sparkle.IR.RegDedup.mergeDuplicates r).body.all Sparkle.IR.RegDedup.isAssign = true := by
  unfold Sparkle.IR.RegDedup.mergeDuplicates
  simp only [hall, if_true]
  split
  · rename_i hv
    exact Tools.ShippingMachineShipsHier.validateMerge_go_assign _ _ _ hv hall
  · exact hall

/-! ## Pure: `childTyped` of a typed assignment-only module with the one output `out` -/

/-- **A module typed in its own wire table, assignment-only, with the one
output `out` written exactly once, is a width-typed child**
(`childTyped (declWidth m) m`): every assignment is `assignTyped` off the
output (`assignTyped_of_typed`), and the one assignment of `out` is typed at
the port's width (a typing at the wire-table width of `out`, which is `0`,
is impossible: `TypedExpr.positive`). The machine-leaf twin of
`Tools.ShippingGatePorts.GateChildPorts.childTyped_ok`. -/
theorem typedIn_childTyped_out {m : Sparkle.IR.AST.Module}
    (h : Tools.ShippingTextTyped.TypedIn m) {ty : Sparkle.IR.Type.HWType}
    (hout : m.outputs = [({ name := "out", ty := ty } : Port)])
    (hall : m.body.all Sparkle.IR.RegDedup.isAssign = true)
    (hcnt : List.count "out" (Sparkle.IR.Reorder.writesOf m.body) = 1) :
    Tools.ShippingHierTyped.childTyped (Sparkle.IR.RegDedup.declWidth m) m = true := by
  have hW : Sparkle.IR.RegDedup.declWidth m = Tools.ShippingEntrySoundness.weOf m := rfl
  rw [hW]
  have hq : ({ name := "out", ty := ty } : Port) ∈ m.outputs := by
    rw [hout]
    exact List.Mem.head _
  have hz : Tools.ShippingEntrySoundness.weOf m "out" = 0 :=
    Tools.ShippingTypedWidthOk.weOf_not_wire (fun p hp e => h.ow _ hq p hp e)
  have hmem : "out" ∈ Sparkle.IR.Reorder.writesOf m.body := mem_of_count_one hcnt
  unfold Tools.ShippingHierTyped.childTyped
  refine (Bool.and_eq_true _ _).mpr ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    intro st hst
    cases st with
    | assign l r =>
      show Tools.ShippingHierTyped.assignTyped (Tools.ShippingEntrySoundness.weOf m)
        (m.outputs.map (·.name)) l r = true
      obtain ⟨n, ht, hl⟩ := h.asg l r hst
      refine Tools.ShippingTypedWidthOk.assignTyped_of_typed ht ?_ ?_
      · intro x hx
        obtain ⟨q, hq', hqn⟩ := List.mem_map.mp hx
        have hqn' : q.name = x := hqn
        exact Tools.ShippingTypedWidthOk.weOf_not_wire
          (fun p hp e => h.ow q hq' p hp (e.trans hqn'.symm))
      · rcases hl with h1 | ⟨q, hq', hqn, -⟩
        · exact Or.inl h1
        · exact Or.inr (List.mem_map.mpr ⟨q, hq', hqn⟩)
    | register => rfl
    | inst => rfl
    | memory =>
      exact Tools.ShippingTypedWidthOk.ff_absurd' (List.all_eq_true.mp hall _ hst)
  · rw [hout, List.all_eq_true]
    intro p hp
    rw [List.mem_singleton.mp hp]
    obtain ⟨e, hst⟩ := Tools.ShippingChecksGate.assign_of_writes hall hmem
    obtain ⟨n, ht, hl⟩ := h.asg "out" e hst
    have hte : Tools.ShippingTypedExprSoundness.TypedExpr (Tools.ShippingEntrySoundness.weOf m) e
        ty.bitWidth := by
      rcases hl with hl | ⟨q, hq', -, hqw⟩
      · have hn : n = 0 := hl.symm.trans hz
        have hp' := ht.positive
        rw [hn] at hp'
        exact absurd hp' (Nat.lt_irrefl 0)
      · rw [hout] at hq'
        have e' : q = ({ name := "out", ty := ty } : Port) := List.mem_singleton.mp hq'
        rw [e'] at hqw
        have hn : n = ty.bitWidth := hqw.symm
        rw [hn] at ht
        exact ht
    have hle : Sparkle.IR.Semantics.widthOf (Tools.ShippingEntrySoundness.weOf m) e ≤
        ty.bitWidth := by
      rw [hte.width]
      exact Nat.le_refl _
    refine (Bool.and_eq_true _ _).mpr ⟨beq_iff_eq.mpr hcnt, ?_⟩
    refine List.any_eq_true.mpr ⟨Stmt.assign "out" e, hst, ?_⟩
    show (("out" : String) == "out" &&
      decide (Sparkle.IR.Semantics.widthOf (Tools.ShippingEntrySoundness.weOf m) e ≤
        ty.bitWidth)) = true
    exact (Bool.and_eq_true _ _).mpr ⟨beq_self_eq_true _, decide_eq_true hle⟩

/-- **`childTyped` of the full entry's module**: the typed module itself, or
its checked merge — which, the typed module being assignment-only, is
`mergeDuplicates`' validated merge: typed (`typedIn_mergeDuplicates_out`),
assignment-only, with the same writes (`mergeDuplicates_closed`). -/
theorem childTyped_post_out {m0 b : Sparkle.IR.AST.Module}
    (hpost : b = m0 ∨ b = Sparkle.IR.RefineCheck.mergeChecked m0)
    (hT : Tools.ShippingTextTyped.TypedIn m0) {ty : Sparkle.IR.Type.HWType}
    (hout : m0.outputs = [({ name := "out", ty := ty } : Port)])
    (hall : m0.body.all Sparkle.IR.RegDedup.isAssign = true)
    (hcnt : List.count "out" (Sparkle.IR.Reorder.writesOf m0.body) = 1) :
    Tools.ShippingHierTyped.childTyped (Sparkle.IR.RegDedup.declWidth b) b = true := by
  rcases hpost with e | e
  · rw [e]
    exact typedIn_childTyped_out hT hout hall hcnt
  · rw [e, Tools.ShippingCombKidText.mergeChecked_assign hall]
    have hc : readsClosedB (m0.body.flatMap Sparkle.IR.Reorder.stmtReads) m0.body = true :=
      readsClosedB_of_all m0.body _ (fun st hst n hn => List.mem_flatMap.mpr ⟨st, hst, hn⟩)
    have hw : Sparkle.IR.Reorder.writesOf (Sparkle.IR.RegDedup.mergeDuplicates m0).body =
        Sparkle.IR.Reorder.writesOf m0.body :=
      (Tools.ShippingMergeClosed.mergeDuplicates_closed hall hc).2
    refine typedIn_childTyped_out
      (Tools.ShippingCombKidText.typedIn_mergeDuplicates_out hT hout hall)
      ((Sparkle.IR.RegDedup.mergeDuplicates_ports m0).2.1.trans hout)
      (mergeDuplicates_assign hall) ?_
    rw [hw]
    exact hcnt

/-! ## Pure: `hkidA`, `hkidR` from `ChildComb` -/

/-- **`hkidA` for a combinational child** (`gate_kidA` without the gate's
binders): an assignment-only module driving `out`, with an empty design. -/
theorem comb_kidA {b : Sparkle.IR.AST.Module} {design : Design}
    (h : Tools.ShippingGateChildComb.ChildComb b) (hd : design.modules = []) :
    Tools.ShippingDesignSVBack.outsAssigned b = true ∧
      ∀ g ∈ design.modules, Tools.ShippingDesignSVBack.outsAssigned g = true := by
  refine ⟨Tools.ShippingChecksDerived2.outsAssigned_of_assigned fun p hp => ?_, ?_⟩
  · obtain ⟨ty, hout⟩ := h.output
    rw [hout] at hp
    have e : p = { name := "out", ty := ty } := List.mem_singleton.mp hp
    rw [e]
    exact Tools.ShippingChecksGate.assign_of_writes h.assigns h.outDriven
  · intro g hg
    rw [hd] at hg
    cases hg

/-- **`hkidR` for a combinational child**: no instance statement. -/
theorem comb_kidR {b : Sparkle.IR.AST.Module} {design : Design}
    (h : Tools.ShippingGateChildComb.ChildComb b) (hd : design.modules = []) :
    ∀ g ∈ b :: design.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
      ∃ g2 ∈ design.modules, g2.name = mn := by
  intro g hg mn i conns hm
  rw [hd] at hg
  have hgb : g = b := List.mem_singleton.mp hg
  rw [hgb] at hm
  exact Tools.ShippingChecksDerived.ff_absurd (List.all_eq_true.mp h.assigns _ hm)

/-! ## Pure: an argument port's width in BOTH tables -/

/-- **`inPort_weS` with the IR's table beside the emitter's**: at position
`j` of the non-clock inputs, the port has, in the emitter's map AND in the
IR's declared widths, the width of the type of the `j`-th non-domain binder.
Same hypotheses as `Tools.ShippingPortWidthsPure.inPort_weS`; the IR's view
is the intermediate fact of that proof (the wire-table width is the type's),
`declWidth m` being the wire table. -/
theorem inPort_both {m : Sparkle.IR.AST.Module}
    {bs : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    (hwn : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (hty : (Tools.ShippingInstStmtG.inPortsOf m).map (fun p => p.ty) =
      (bs.filter Tools.ShippingPortWidthsPure.nonDom).map
        (fun b => Tools.ShippingMachineEntry.kindTy b.2))
    (hpos : ∀ bn ∈ bs, 0 < (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth)
    (hW : ∀ p ∈ Tools.ShippingInstStmtG.inPortsOf m,
      (p.ty = Sparkle.IR.Type.HWType.bit → Tools.ShippingEntrySoundness.weOf m p.name = 1) ∧
      ∀ k, p.ty = Sparkle.IR.Type.HWType.bitVector k →
        Tools.ShippingEntrySoundness.weOf m p.name = k)
    {j : Nat} {q : Port} (hq : (Tools.ShippingInstStmtG.inPortsOf m)[j]? = some q) :
    ∃ wd, ((((bs.filter Tools.ShippingPortWidthsPure.nonDom).map
        (fun b => Tools.ShippingMachineEntry.kindTy b.2)).map
        (fun ty : Sparkle.IR.Type.HWType => ty.bitWidth))[j]? = some wd) ∧
      Tools.ShippingDesignSV.weS m q.name = wd ∧
      Sparkle.IR.RegDedup.declWidth m q.name = wd := by
  have hqm : q ∈ Tools.ShippingInstStmtG.inPortsOf m := List.mem_of_getElem? hq
  have h1 : ((Tools.ShippingInstStmtG.inPortsOf m).map (fun p => p.ty))[j]? = some q.ty :=
    Tools.ShippingPortWidthsPure.getElem?_map_some (fun p : Port => p.ty) hq
  rw [hty] at h1
  have h2 := h1
  rw [List.getElem?_map] at h2
  cases hb : (bs.filter Tools.ShippingPortWidthsPure.nonDom)[j]? with
  | none =>
    rw [hb] at h2
    cases h2
  | some bn =>
    rw [hb] at h2
    have hqt : Tools.ShippingMachineEntry.kindTy bn.2 = q.ty := by
      simpa only [Option.map_some, Option.some.injEq] using h2
    have hbm : bn ∈ bs := (List.mem_filter.mp (List.mem_of_getElem? hb)).1
    have hp0 : 0 < (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth := hpos bn hbm
    obtain ⟨hbit, hvec⟩ := hW q hqm
    have hwq : Tools.ShippingEntrySoundness.weOf m q.name = q.ty.bitWidth := by
      rcases Tools.ShippingTransitionPortTys.kindTy_shape bn.2 with hk | ⟨n, hk⟩
      · have hq1 : q.ty = Sparkle.IR.Type.HWType.bit := hqt.symm.trans hk
        exact (hbit hq1).trans (congrArg Sparkle.IR.Type.HWType.bitWidth hq1).symm
      · have hq1 : q.ty = Sparkle.IR.Type.HWType.bitVector n := hqt.symm.trans hk
        exact (hvec n hq1).trans (congrArg Sparkle.IR.Type.HWType.bitWidth hq1).symm
    have hpq : 0 < Tools.ShippingEntrySoundness.weOf m q.name := by
      rw [hwq, ← hqt]
      exact hp0
    obtain ⟨-, hws, -⟩ := Tools.ShippingTextTyped.pos_wire hwn hpq
    have hWd : Sparkle.IR.RegDedup.declWidth m = Tools.ShippingEntrySoundness.weOf m := rfl
    exact ⟨q.ty.bitWidth,
      Tools.ShippingPortWidthsPure.getElem?_map_some
        (fun ty : Sparkle.IR.Type.HWType => ty.bitWidth) h1,
      hws.trans hwq, (congrFun hWd q.name).trans hwq⟩

/-- **A leaf machine's argument port, in both tables** (`LeafPorts.inWidths`
with the IR's view): the common child-port facts are `LeafPorts`' `args`,
`argW`, `wal`, `pos`. -/
theorem leafPorts_inWidths2 {c : Lean.Name} {d : Tools.ShippingMachineAuto.MachineData}
    {b : Sparkle.IR.AST.Module} (h : Tools.ShippingLeafPorts.LeafPorts c d b) {j : Nat} {q : Port}
    (hq : (Tools.ShippingInstStmtG.inPortsOf b)[j]? = some q) :
    ∃ wd, (Tools.ShippingPortWidthsPure.declWidths d)[j]? = some wd ∧
      Tools.ShippingDesignSV.weS b q.name = wd ∧
      Sparkle.IR.RegDedup.declWidth b q.name = wd := by
  obtain ⟨ids, cache, hlen, hP⟩ := h.args
  have hle : (d.shape.binders.take (Tools.ShippingPortWidthsPure.declN d)).length ≤
      ids.length := by
    rw [List.length_take]
    omega
  have hty : (Tools.ShippingInstStmtG.inPortsOf b).map (fun p => p.ty) =
      ((d.shape.binders.take (Tools.ShippingPortWidthsPure.declN d)).filter
        Tools.ShippingPortWidthsPure.nonDom).map
        (fun bn => Tools.ShippingMachineEntry.kindTy bn.2) := by
    rw [hP]
    exact Tools.ShippingPortWidthsPure.machPorts_tys c ids cache _ hle
  have hwn : ∀ p ∈ b.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name :=
    fun p hp => (Tools.ShippingPortWidthsPure.wire_ne_clk (h.wal p hp)).1
  exact inPort_both hwn hty
    (fun bn hbn => Tools.ShippingPortWidthsPure.kindTy_pos h.pos (List.mem_of_mem_take hbn))
    h.argW hq

/-- **A slotless leaf machine's inputs are its argument ports** (no clock,
no reset): `LeafPorts.ins`. -/
theorem leafPorts_inPortsOf_eq {c : Lean.Name} {d : Tools.ShippingMachineAuto.MachineData}
    {b : Sparkle.IR.AST.Module} (h : Tools.ShippingLeafPorts.LeafPorts c d b)
    (hsl : d.shape.layout.slots = []) : Tools.ShippingInstStmtG.inPortsOf b = b.inputs := by
  obtain ⟨A, hA, h0, -⟩ := h.ins
  have hemp : d.shape.layout.slots.isEmpty = true :=
    (congrArg List.isEmpty hsl).trans rfl
  have hin : ∀ p ∈ b.inputs, Sparkle.IR.NameHints.Allocated p.name := by
    intro p hp
    rw [h0 hemp] at hp
    exact hA p hp
  unfold Tools.ShippingInstStmtG.inPortsOf
  refine List.filter_eq_self.mpr (fun p hp => ?_)
  obtain ⟨-, h1, h2⟩ := Tools.ShippingPortWidthsPure.wire_ne_clk (Or.inl (hin p hp))
  show (p.name != "clk" && p.name != "rst") = true
  exact (Bool.and_eq_true _ _).mpr ⟨bne_iff_ne.mpr h1, bne_iff_ne.mpr h2⟩

end Tools.ShippingLeafOneOut

/-! ## From a run: the typed module of a slotless leaf with the one output `out`

Declared in the namespace of `Tools/ShippingLeafTyped.lean`, with that
file's `open`s, so that the copied proof text resolves every name as it does
there. -/
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

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **A slotless leaf machine with the one output `out`: the returned module
is a typed, ASSIGNMENT-ONLY module writing `out` exactly once, or its checked
merge**, over every run of the full entry. `leaf_run_typedIn`'s proof
(copied unchanged up to the construction of `hT`) with the hypotheses `hsl`,
`hone` and the two new conjuncts. -/
theorem leaf_run_typedIn_out {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hsl : d.shape.layout.slots = [])
    (hone : d.shape.layout.outs.map (·.name) = ["out"])
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closesM : MachineCloses mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    ∃ m0 : Sparkle.IR.AST.Module, (b = m0 ∨ b = mergeChecked m0) ∧
      Tools.ShippingTextTyped.TypedIn m0 ∧
      m0.body.all Sparkle.IR.RegDedup.isAssign = true ∧
      List.count "out" (Sparkle.IR.Reorder.writesOf m0.body) = 1 := by
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
  -- NEW (par/a-10): without slots the cleaned body is the transition's
  -- assignments and the output assignments; `out` is written once
  have hCMb : (closeMachine d.shape.layout t').body =
      Bc ++ outAssigns coreW d.shape.layout.outs :=
    Tools.ShippingLeafOneOut.closeMachine_slotless_body hbodyc hsl
  have hBa : Bc.all Sparkle.IR.RegDedup.isAssign = true := by
    rw [List.all_eq_true]
    intro st hst
    have hst' : st ∈ t'.body := by
      rw [hbodyc]
      exact List.mem_append_left _ hst
    obtain ⟨l, e, n, he, -, -⟩ := typedc st hst'
    subst he
    rfl
  have hAZ : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body.all
      Sparkle.IR.RegDedup.isAssign = true := by
    rw [hZb, hCMb, List.all_eq_true]
    intro st hst
    rcases List.mem_append.mp hst with h1 | h1
    · exact List.all_eq_true.mp hBa st h1
    · simp only [outAssigns, List.mem_map] at h1
      obtain ⟨o', -, rfl⟩ := h1
      rfl
  have hcntZ : List.count "out"
      (Sparkle.IR.Reorder.writesOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body) = 1 := by
    rw [hZb, hCMb]
    exact Tools.ShippingLeafOneOut.count_out_slotless hBa namedc hone
  exact ⟨Sparkle.IR.ZeroWidth.dropZeroWidthModule M, hpost, hT, hAZ, hcntZ⟩

/-- The same from a `RealChild` witness. -/
theorem leaf_real_typedIn_out {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hsl : d.shape.layout.slots = [])
    (hone : d.shape.layout.outs.map (·.name) = ["out"])
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    {y : Res} (h : RealChild mref cref c y) :
    ∃ m0 : Sparkle.IR.AST.Module, (y.1 = m0 ∨ y.1 = mergeChecked m0) ∧
      Tools.ShippingTextTyped.TypedIn m0 ∧
      m0.body.all Sparkle.IR.RegDedup.isAssign = true ∧
      List.count "out" (Sparkle.IR.Reorder.writesOf m0.body) = 1 := by
  obtain ⟨mctx', cctx', w, w', hw, hr⟩ := h.inv
  exact leaf_run_typedIn_out d ok hbody hC hdomB hno hSS outTy hsl hone hw hr
    (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx') hon hoty

end Tools.ShippingLeafTyped

/-! ## The child-side facts, from ONE bundle of per-declaration conditions -/
namespace Tools.ShippingLeafOneOut
open Lean Meta
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineAuto Tools.ShippingMachineEntry Tools.ShippingMachineCloses
open Tools.ShippingChildInv

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The premises about one SLOTLESS LEAF MACHINE child declaration** `c`
with data `dk` and the one output `out`: `LeafKidAny` (the endpoint's `ok`
and body, `callsOk` and the late-domain condition at `dk.nIn`, no call, the
slot count, the output width / name / scalar conditions, the child's
reflection and its own closing in every context) and four more DATA
conditions: `gateCallsOk` at `dk.nIn`, at least one `let`, no slot, the one
output `out`. Every field but `any.entry` and `any.closes` is decided per
declaration. -/
structure SlotlessLeaf (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (c : Name)
    (dk : MachineData) : Prop where
  any : Tools.ShippingPortsMatchRawLeafAny.LeafKidAny mctx mref cctx cref c dk
  gate : dk.gateCallsOk dk.nIn = true
  lets : dk.shape.layout.lets ≠ 0
  slots : dk.shape.layout.slots = []
  one : ∃ o, dk.shape.layout.outs = [o] ∧ o.name = "out"

section Facts
variable {c : Name} {dk : MachineData}

/-- The output names are `["out"]`. -/
theorem SlotlessLeaf.outNames (K : SlotlessLeaf mctx mref cctx cref c dk) :
    dk.shape.layout.outs.map (·.name) = ["out"] := by
  obtain ⟨o, ho, hn⟩ := K.one
  rw [ho]
  show [o.name] = ["out"]
  rw [hn]

/-- The module is combinational (`ChildComb`) and the child's design is
empty (`machineChild_of_real`). -/
theorem SlotlessLeaf.comb (K : SlotlessLeaf mctx mref cctx cref c dk) {y : Res}
    (hy : RealChild mref cref c y) :
    Tools.ShippingGateChildComb.ChildComb y.1 ∧ y.2.modules = [] := by
  have h := Tools.ShippingMachineChildRun.machineChild_of_real (nDecl := dk.nIn) dk K.any.ok
    K.any.body K.gate K.lets K.any.leaf K.slots K.one K.any.outTy K.any.entry K.any.closes hy
  have h' : Tools.ShippingGateChildComb.ChildComb y.1 ∧
      y.1.inputs.length = _ ∧ y.1.name = c.toString ∧ y.2.modules = [] := h
  exact ⟨h'.1, h'.2.2.2⟩

/-- **`hkidA`.** -/
theorem SlotlessLeaf.kidA (K : SlotlessLeaf mctx mref cctx cref c dk) {y : Res}
    (hy : RealChild mref cref c y) :
    Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
      ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true :=
  comb_kidA (K.comb hy).1 (K.comb hy).2

/-- **`hkidR`.** -/
theorem SlotlessLeaf.kidR (K : SlotlessLeaf mctx mref cctx cref c dk) {y : Res}
    (hy : RealChild mref cref c y) :
    ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
      ∃ g2 ∈ y.2.modules, g2.name = mn :=
  comb_kidR (K.comb hy).1 (K.comb hy).2

/-- The output ports are the layout's (what `hkidW_one` asks). -/
theorem SlotlessLeaf.outTys (K : SlotlessLeaf mctx mref cctx cref c dk) {y : Res}
    (hy : RealChild mref cref c y) :
    Tools.ShippingChildIfaceTy.ChildOutTys dk.shape.layout.outs y.1 :=
  Tools.ShippingPortsMatchRawLeafAny.leaf_real_outTys_any dk K.any.ok K.any.body K.any.leaf
    K.any.ss K.any.outTy K.any.entry K.any.closes hy

/-- **`hkidT`**: the emitter's width map resolves the output port. -/
theorem SlotlessLeaf.portsIn (K : SlotlessLeaf mctx mref cctx cref c dk) {y : Res}
    (hy : RealChild mref cref c y) : Tools.ShippingLeafTyped.PortsIn y.1 :=
  Tools.ShippingLeafTyped.leaf_real_portsIn (nDecl := dk.nIn) dk K.any.ok K.any.body
    K.any.calls K.any.dom K.any.leaf K.any.ss K.any.outTy K.any.entry K.any.closes
    K.any.outName K.any.outScalar hy

/-- The common port facts (`LeafPorts`). -/
theorem SlotlessLeaf.ports (K : SlotlessLeaf mctx mref cctx cref c dk) {y : Res}
    (hy : RealChild mref cref c y) : Tools.ShippingLeafPorts.LeafPorts c dk y.1 :=
  Tools.ShippingLeafPorts.leaf_real_ports (nDecl := dk.nIn) dk K.any.ok K.any.body
    K.any.calls K.any.dom K.any.leaf K.any.ss K.any.outTy K.any.entry K.any.closes hy

/-- **`hkidIn` and `hkidInD` in one statement**: the `j`-th INPUT port has,
in the emitter's table and in the IR's, the `j`-th declared width. -/
theorem SlotlessLeaf.inWidths (K : SlotlessLeaf mctx mref cctx cref c dk) {y : Res}
    (hy : RealChild mref cref c y) {j : Nat} {q : Port} (hq : y.1.inputs[j]? = some q) :
    ∃ wd, (Tools.ShippingPortWidthsPure.declWidths dk)[j]? = some wd ∧
      Tools.ShippingDesignSV.weS y.1 q.name = wd ∧
      Sparkle.IR.RegDedup.declWidth y.1 q.name = wd := by
  have hP := K.ports hy
  have hq' : (Tools.ShippingInstStmtG.inPortsOf y.1)[j]? = some q := by
    rw [leafPorts_inPortsOf_eq hP K.slots]
    exact hq
  exact leafPorts_inWidths2 hP hq'

/-- **`hkidTy`**: the module is a width-typed child in its own declared
widths. -/
theorem SlotlessLeaf.childTyped (K : SlotlessLeaf mctx mref cctx cref c dk) {y : Res}
    (hy : RealChild mref cref c y) :
    Tools.ShippingHierTyped.childTyped (Sparkle.IR.RegDedup.declWidth y.1) y.1 = true := by
  obtain ⟨m0, hpost, hT, hall, hcnt⟩ :=
    Tools.ShippingLeafTyped.leaf_real_typedIn_out (nDecl := dk.nIn) dk K.any.ok K.any.body
      K.any.calls K.any.dom K.any.leaf K.any.ss K.any.outTy K.slots K.outNames K.any.entry
      K.any.closes K.any.outName K.any.outScalar hy
  have hI := Tools.ShippingSeqChildIface.seqChild_of_real dk K.any.ok K.any.body K.any.leaf
    K.any.outTy K.any.entry K.any.closes hy
  have hyo : y.1.outputs.map (·.name) = ["out"] := hI.outs.trans K.outNames
  have hm0o : m0.outputs.map (·.name) = ["out"] := by
    rcases hpost with e | e
    · rw [← e]
      exact hyo
    · rw [← (Sparkle.IR.RefineCheck.mergeChecked_ports m0).2.1, ← e]
      exact hyo
  obtain ⟨ty, hout⟩ := Tools.ShippingCombKidText.single_out hm0o
  exact childTyped_post_out hpost hT hout hall hcnt

/-- **`hkidK`**: the children's text check, at every depth. -/
theorem SlotlessLeaf.kidK (K : SlotlessLeaf mctx mref cctx cref c dk) {y : Res}
    (hy : RealChild mref cref c y) :
    (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
        Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
      ∀ g ∈ y.2.modules,
        ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n g = true :=
  Tools.ShippingCombKidText.leaf_real_kidK_out (nDecl := dk.nIn) dk K.any.ok K.any.body
    K.any.calls K.any.dom K.any.leaf K.any.ss K.any.outTy K.outNames K.any.entry K.any.closes
    K.any.outName K.any.outScalar hy

end Facts

end Tools.ShippingLeafOneOut
