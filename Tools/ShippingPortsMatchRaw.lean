import Tools.ShippingChecksWidths
import Tools.ShippingClosedTyped
import Tools.ShippingTextShipped
import Tools.ShippingLeafTyped
import Tools.ShippingMachineRanBase

/-! # `portsMatchB` of the RAW full-entry module (conjunct 7 of `textCheckI`) (G1, round optfb-7)

`PortsMatch C b` asks, of every connection `(port, .ref x)` of an instance
of `child`, `weS b x = weS child port`. For the full entry's module `b` of
a machine with calls (before the optimizer):

## Pure

* `callStmtG_conn`: a reference connection of a call group's instance
  (`CallStmtG`) is an ARGUMENT connection (the `j`-th argument port of the
  child to the transition port of the `let` `args[j]`), the CLOCK or the
  RESET (`clk ↦ clk`, `rst ↦ rst`, for a child with one of them), or an
  OUTPUT connection (the field of an entry of the group, an output port of
  the child, to the entry's transition port).
* `callArgsOk d nDecl kidIns : Bool` — the missing argument-width agreement
  as a run-free DATA condition per parent / children: for every entry `k`
  and argument position `j`, the width of the type of the parent's binder of
  the `let` `args[j]` is `(kidIns k)[j]`, the emitted width of the child's
  `j`-th argument port. `callArgs_width`: what it gives at a position.
  (The model is `Tools.ShippingCallWidths.callWidthsOk`, the result side.)
  NOTHING in the compiler compares these two widths (`instStmtG` compares
  the NUMBER of argument ports with the number of argument wires only).

## From the run

* `core_callConns`: every instance statement of `b` resolves to the module
  of a real child, and each of its reference connections `(pn, .ref x)` is
  the clock / reset, or `x` is a declared WIRE of `b` whose declared width
  is the width of the type of a binder of the parent: the call's result
  binder `binders[nDecl + k]` (output connection, `pn` the field of entry
  `k`), or the `let` binder
  `binders[nDecl + (|insts| + (|slots| + a))]` (argument connection of the
  `j`-th argument port, `a = args[j]`). Its proof is `core_callPorts`'s
  (`Tools/ShippingChecksWidths.lean`, copied by a script up to the
  resolution of the instance) with the width argument made generic in the
  transition port's position (`key`).
* `core_portsMatch_raw`: `portsMatchB (childMap D.modules) b = true`.
  Derived inside: the parent side of every connection (`core_callConns`;
  `weS b x = declWidth b x` on wires by `TypedIn b`), the child side of the
  OUTPUT connections (`PortsIn` of the child: `hkidT`, for a leaf
  `Tools.ShippingLeafTyped.leaf_real_portsIn`; the width agreement `hkidW`,
  from `callWidthsOk`). Hypotheses that are NOT derived this round, each a
  statement about ONE module's emitted width map (none mentions a
  connection):

      hargs   : callArgsOk d nDecl kidIns = true            -- data, decidable
      hkidIn  : per real child y of entry k, the j-th argument port q of y.1:
                  ∃ wd, (kidIns k)[j]? = some wd ∧ weS y.1 q.name = wd
      hkidClk : per real child with a clock or reset input:
                  weS y.1 "clk" = 1 ∧ weS y.1 "rst" = 1
      hclkB   : weS b "clk" = 1 ∧ weS b "rst" = 1

  What `hkidIn` needs for a leaf child (not written): its argument ports
  are the ports of its declared non-domain binders, of their types
  (`MachineWired`'s clause `m.inputs.filter … = machPorts …` and
  `inputPorts_typesD`), each is also a wire of that type (`weOf m p.name =`
  the port type's width: the leaf clause of `MachineWired`), and a wire of
  positive width has its wire-table width as emitted width (`pos_wire`).
  What `hkidClk` / `hclkB` need: `closeMachine` adds
  `clk`, `rst : .bit` to the inputs of a machine with slots, no wire is
  named `clk` / `rst` (wires are allocated names or `nextName`s:
  `not_allocated_clk`, `nextName_ne_clk`), no earlier input has that
  sanitized name; for the parent `MachineWired`'s input clause.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingPortsMatchRaw
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

/-- **A reference connection of a call group's instance**: an argument
connection, the clock or the reset, or an output connection. -/
theorem callStmtG_conn {nIn kI n : Nat} {names : List String} {args : List Nat}
    {outs : List (Nat × String)} {mc : Sparkle.IR.AST.Module} {mn iname : String}
    {conns : List (String × Sparkle.IR.AST.Expr)}
    (h : Tools.ShippingMachineInstG.CallStmtG nIn kI n names args outs mc
      (Stmt.inst mn iname conns))
    {pn x : String} (hm : (pn, Sparkle.IR.AST.Expr.ref x) ∈ conns) :
    (∃ (j : Nat) (q : Port) (a : Nat), (inPortsOf mc)[j]? = some q ∧ q.name = pn ∧
        args[j]? = some a ∧ names[nIn + kI + n + a]? = some x) ∨
    (isSeqChild mc = true ∧ ((pn = "clk" ∧ x = "clk") ∨ (pn = "rst" ∧ x = "rst"))) ∨
    (∃ e ∈ outs, names[nIn + e.1]? = some x ∧ e.2 = pn ∧ ∃ p ∈ mc.outputs, p.name = pn) := by
  obtain ⟨outWs, argWs, iname', hout, hargs, -, -, hfo, -, -, -, -, -, -, he⟩ := h
  injection he with h1 h2 h3
  rw [h3] at hm
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · -- an argument connection: position `j` of the argument ports
      left
      obtain ⟨⟨q, aw⟩, hq, heq⟩ := List.mem_map.mp hm
      have hqn : q.name = pn := congrArg Prod.fst heq
      have h2' : Sparkle.IR.AST.Expr.ref aw = Sparkle.IR.AST.Expr.ref x := congrArg Prod.snd heq
      have haw : aw = x := by
        cases h2'
        rfl
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hq
      obtain ⟨hj1, hj2⟩ := List.getElem?_zip_eq_some.mp hj
      have hj2' : argWs[j]? = some aw := hj2
      obtain ⟨hlen, hget⟩ := Tools.ShippingMachineInst.mapM_some _ _ _ hargs
      have hjl : j < args.length := by
        rw [← hlen]
        exact (List.getElem?_eq_some_iff.mp hj2').1
      obtain ⟨z, hz, hzj⟩ := hget j hjl
      rw [hj2'] at hzj
      have hzw : z = aw := (Option.some.inj hzj).symm
      have hz' : names[nIn + kI + n + args[j]]? = some x := by
        rw [← haw, ← hzw]
        exact hz
      exact ⟨j, q, args[j], hj1, hqn, List.getElem?_eq_getElem hjl, hz'⟩
    · -- the clock and the reset
      right
      left
      by_cases hs : (mc.inputs.any fun p => p.name == "clk" || p.name == "rst") = true
      · rw [if_pos hs] at hm
        refine ⟨hs, ?_⟩
        rcases List.mem_cons.mp hm with h0 | h0
        · left
          have e1 : pn = "clk" := congrArg Prod.fst h0
          have e2 : Sparkle.IR.AST.Expr.ref x = Sparkle.IR.AST.Expr.ref "clk" :=
            congrArg Prod.snd h0
          have e3 : x = "clk" := by
            cases e2
            rfl
          exact ⟨e1, e3⟩
        · rcases List.mem_cons.mp h0 with h0 | h0
          · right
            have e1 : pn = "rst" := congrArg Prod.fst h0
            have e2 : Sparkle.IR.AST.Expr.ref x = Sparkle.IR.AST.Expr.ref "rst" :=
              congrArg Prod.snd h0
            have e3 : x = "rst" := by
              cases e2
              rfl
            exact ⟨e1, e3⟩
          · cases h0
      · rw [if_neg hs] at hm
        cases hm
  · -- an output connection: position `j` of the group
    right
    right
    obtain ⟨⟨f, w'⟩, hfw, heq⟩ := List.mem_map.mp hm
    have hfp : f = pn := congrArg Prod.fst heq
    have h2' : Sparkle.IR.AST.Expr.ref w' = Sparkle.IR.AST.Expr.ref x := congrArg Prod.snd heq
    have hw' : w' = x := by
      cases h2'
      rfl
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hfw
    obtain ⟨hj1, hj2⟩ := List.getElem?_zip_eq_some.mp hj
    have hj1' : (outs.map (·.2))[j]? = some f := hj1
    have hj2' : outWs[j]? = some w' := hj2
    rw [List.getElem?_map] at hj1'
    cases he : outs[j]? with
    | none =>
      rw [he] at hj1'
      cases hj1'
    | some e =>
      rw [he] at hj1'
      have hef : e.2 = f := by
        simpa only [Option.map_some, Option.some.injEq] using hj1'
      have hjl : j < outs.length := (List.getElem?_eq_some_iff.mp he).1
      have hej : outs[j] = e := by
        rw [List.getElem?_eq_getElem hjl] at he
        exact Option.some.inj he
      obtain ⟨-, hget⟩ := Tools.ShippingMachineInst.mapM_some _ _ _ hout
      obtain ⟨z, hz, hzj⟩ := hget j hjl
      rw [hej] at hz
      rw [hj2'] at hzj
      have hzw : z = w' := (Option.some.inj hzj).symm
      have hz' : names[nIn + e.1]? = some z := by
        obtain ⟨k, f'⟩ := e
        exact hz
      have hem : e ∈ outs := List.mem_of_getElem? he
      have hfa : mc.outputs.any (fun p => p.name == e.2) = true :=
        List.all_eq_true.mp hfo e.2 (List.mem_map.mpr ⟨e, hem, rfl⟩)
      obtain ⟨p, hp, hpe⟩ := List.any_eq_true.mp hfa
      exact ⟨e, hem, by rw [hz', hzw, hw'], hef.trans hfp, p, hp,
        (beq_iff_eq.mp hpe).trans (hef.trans hfp)⟩

/-- **The calls' argument widths agree with the children's argument ports**
(run-free): for every entry `k` and argument position `j`, the width of the
type of the parent's binder of the `let` `args[j]` is `(kidIns k)[j]`. -/
def callArgsOk (d : MachineData) (nDecl : Nat) (kidIns : Nat → List Nat) : Bool :=
  (List.range d.shape.insts.length).all fun k =>
    (List.range (kidIns k).length).all fun j =>
      decide ((((d.shape.insts[k]?).bind fun c => c.2.1[j]?).bind fun a =>
        (d.shape.binders[nDecl + (d.shape.insts.length +
          (d.shape.layout.slots.length + a))]?).map fun bn => (kindTy bn.2).bitWidth) =
        (kidIns k)[j]?)

/-- What `callArgsOk` gives at an entry and an argument position. -/
theorem callArgs_width {d : MachineData} {nDecl : Nat} {kidIns : Nat → List Nat}
    (h : callArgsOk d nDecl kidIns = true)
    {k : Nat} (hk : k < d.shape.insts.length) {j a : Nat}
    (ha : ((d.shape.insts[k]).2.1)[j]? = some a)
    {bn : Name × MixedGateBinder}
    (hbn : d.shape.binders[nDecl + (d.shape.insts.length +
      (d.shape.layout.slots.length + a))]? = some bn)
    {wd : Nat} (hwd : (kidIns k)[j]? = some wd) : (kindTy bn.2).bitWidth = wd := by
  unfold callArgsOk at h
  have h1 : ((List.range (kidIns k).length).all fun j =>
      decide ((((d.shape.insts[k]?).bind fun c => c.2.1[j]?).bind fun a =>
        (d.shape.binders[nDecl + (d.shape.insts.length +
          (d.shape.layout.slots.length + a))]?).map fun bn => (kindTy bn.2).bitWidth) =
        (kidIns k)[j]?)) = true :=
    List.all_eq_true.mp h k (List.mem_range.mpr hk)
  have hj : j < (kidIns k).length := (List.getElem?_eq_some_iff.mp hwd).1
  have h2 : (((d.shape.insts[k]?).bind fun c => c.2.1[j]?).bind fun a =>
        (d.shape.binders[nDecl + (d.shape.insts.length +
          (d.shape.layout.slots.length + a))]?).map fun bn => (kindTy bn.2).bitWidth) =
        (kidIns k)[j]? :=
    of_decide_eq_true (List.all_eq_true.mp h1 j (List.mem_range.mpr hj))
  rw [List.getElem?_eq_getElem hk] at h2
  have h3 : (((d.shape.insts[k]).2.1)[j]?).bind (fun a =>
        (d.shape.binders[nDecl + (d.shape.insts.length +
          (d.shape.layout.slots.length + a))]?).map fun bn => (kindTy bn.2).bitWidth) =
        (kidIns k)[j]? := h2
  rw [ha] at h3
  have h4 : (d.shape.binders[nDecl + (d.shape.insts.length +
        (d.shape.layout.slots.length + a))]?).map (fun bn => (kindTy bn.2).bitWidth) =
      (kidIns k)[j]? := h3
  rw [hbn, hwd] at h4
  have h5 : some ((kindTy bn.2).bitWidth) = some wd := h4
  exact Option.some.inj h5

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- `core_callConns` over `MachineRan`: the TAIL of the built proof, moved (round par/g-1).
What it takes of the run is that the machine synthesis this core run performed
returned `(M, D)` from an invariant world; `core_callConns` below is its instance at the
all-worlds closing (`Tools.ShippingMachineRan.machineRan_of_closes`). -/
theorem core_callConns_ran {c : Name} (d : MachineData) (ok : d.ok = true)
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
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, moduleByName D.modules mn = some mc ∧
        (∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
          RealChild mref cref (d.shape.insts[k]).1 y ∧ mc = y.1) ∧
        ∀ pn x, (pn, Sparkle.IR.AST.Expr.ref x) ∈ conns →
          (isSeqChild mc = true ∧ ((pn = "clk" ∧ x = "clk") ∨ (pn = "rst" ∧ x = "rst"))) ∨
          (x ∈ b.wires.map (·.name) ∧
            ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
              RealChild mref cref (d.shape.insts[k]).1 y ∧ mc = y.1 ∧
              ((pn = d.shape.instFields.getD k "" ∧ (∃ p ∈ mc.outputs, p.name = pn) ∧
                  ∃ bn, d.shape.binders[nDecl + k]? = some bn ∧
                    Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth) ∨
                (∃ (j : Nat) (q : Port) (a : Nat) (bn : Name × MixedGateBinder),
                  (inPortsOf mc)[j]? = some q ∧ q.name = pn ∧
                  ((d.shape.insts[k]).2.1)[j]? = some a ∧
                  d.shape.binders[nDecl + (d.shape.insts.length +
                    (d.shape.layout.slots.length + a))]? = some bn ∧
                  Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth))) := by
  have hbody' : b.body = M.body :=
    (Tools.ShippingChecksCore.core_kids_facts_ran d ok hbody hC hslots hdomB hins outTy hnomem hpost ran).2.1
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
  have ran0 := ran
  obtain ⟨bb, w9, w10, hrun9, hw9, -⟩ := ran0
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ := synthesizeMachineCertified_runs hw9 hrun9
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, hreal⟩
  · exact absurd hno hins
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
      RealChild mref cref (d.shape.insts[e.1]).1 y ∧ mc = y.1 := by
    intro e he
    obtain ⟨hargs0, hch0, -⟩ := hall e he
    have hk0 : e.1 < d.shape.insts.length := by
      have := (List.getElem?_eq_some_iff.mp hargs0).1
      simpa using this
    obtain ⟨y, hy, hor⟩ := hallC e.1 hk0
    rw [hy] at hch0
    have hyn : y.1.name = child.1.name := by
      simpa only [Option.map_some, Option.some.injEq] using hch0
    rcases hor with hmem | hre
    · rw [hnomem _ (List.getElem_mem hk0)] at hmem
      cases hmem
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
  have hmn : mn = mc.name := Tools.ShippingOutsExtractedParts.callStmtG_name hcs
  have hfind' : moduleByName D.modules mn = some mc := by
    rw [hmn, (Tools.ShippingHierPremisesBase.moduleByName_mem hfind).2]
    exact hfind
  -- a transition port after the declaration's: a wire of `b`, declared at
  -- the width of its binder's type
  have key : ∀ (i : Nat) (x : String),
      (t.inputs.map (·.name))[machNIn d.shape + i]? = some x →
      x ∈ b.wires.map (·.name) ∧ ∃ bn, d.shape.binders[nDecl + i]? = some bn ∧
        Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth := by
    intro i x hget
    rw [List.getElem?_map] at hget
    cases hq : t.inputs[machNIn d.shape + i]? with
    | none =>
      rw [hq] at hget
      cases hget
    | some q =>
      rw [hq] at hget
      simp only [Option.map_some, Option.some.injEq] at hget
      have hqm : q ∈ t.inputs := List.mem_of_getElem? hq
      obtain ⟨hqw, hqz⟩ := hinW q hqm
      have hql : ls[i]? = some q := by
        have h1 : (PI ++ ls)[PI.length + i]? = some q := by
          rw [← hin, hPI]
          exact hq
        rw [List.getElem?_append_right (Nat.le_add_right _ _)] at h1
        have h2 : PI.length + i - PI.length = i := by omega
        rw [h2] at h1
        exact h1
      have hlt : i < (d.shape.binders.drop nDecl).length := by
        rw [← hP2d, hls]
        exact (List.getElem?_eq_some_iff.mp hql).1
      have hbn : (d.shape.binders.drop nDecl)[i]? = some (d.shape.binders.drop nDecl)[i] :=
        List.getElem?_eq_getElem hlt
      have hty : q.ty = kindTy ((d.shape.binders.drop nDecl)[i]).2 :=
        hP2ty i q _ (by rw [hls]; exact hql) hbn
      have hbn' : d.shape.binders[nDecl + i]? = some (d.shape.binders.drop nDecl)[i] := by
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
      have hqb : q ∈ b.wires := hbw q (by rw [hMw]; exact hqw) hqz
      have hdw : Sparkle.IR.RegDedup.declWidth b q.name = q.ty.bitWidth :=
        Tools.ShippingInstWidthsParts.declWidth_of_unique (nm := q.name) (ty := q.ty)
          hqb huniq
          (by rw [hty]; exact Tools.ShippingTransitionPortTys.kindTy_shape _)
      exact ⟨List.mem_map.mpr ⟨q, hqb, hget⟩, _, hbn', by rw [← hget, hdw, hty]⟩
  refine ⟨mc, hfind', ⟨e0.1, hk0, y0, hre0, hmcy0⟩, ?_⟩
  intro pn x hpc
  rcases callStmtG_conn hcs hpc with ⟨j, q, a, hq, hqn, haj, hnm⟩ | hclk | ⟨e, he, hget, hef, p, hp, hpn⟩
  · -- an argument connection: the `let`'s transition port
    have eidx : machNIn d.shape + d.shape.insts.length + d.shape.layout.slots.length + a =
        machNIn d.shape + (d.shape.insts.length + (d.shape.layout.slots.length + a)) := by
      omega
    have hnm' : (t.inputs.map (·.name))[machNIn d.shape +
        (d.shape.insts.length + (d.shape.layout.slots.length + a))]? = some x := by
      rw [← eidx]
      exact hnm
    obtain ⟨hxw, bn, hbn, hdw⟩ := key _ x hnm'
    have h9 : (d.shape.insts.map (·.2.1))[e0.1]? =
        Option.map (·.2.1) (some (d.shape.insts[e0.1])) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hk0]
    have h10 : some args = some ((d.shape.insts[e0.1]).2.1) :=
      (hall e0 he0).1.symm.trans h9
    have hA : args = (d.shape.insts[e0.1]).2.1 := Option.some.inj h10
    rw [hA] at haj
    exact Or.inr ⟨hxw, e0.1, hk0, y0, hre0, hmcy0,
      Or.inr ⟨j, q, a, bn, hq, hqn, haj, hbn, hdw⟩⟩
  · exact Or.inl hclk
  · -- an output connection: the entry's transition port
    obtain ⟨hke, y, hre, hmcy⟩ := hrealE e he
    obtain ⟨-, -, hfld⟩ := hall e he
    obtain ⟨hxw, bn, hbn, hdw⟩ := key e.1 x hget
    exact Or.inr ⟨hxw, e.1, hke, y, hre, hmcy,
      Or.inl ⟨by rw [← hef, hfld], ⟨p, hp, hpn⟩, bn, hbn, hdw⟩⟩

set_option maxHeartbeats 4000000 in
/-- **Every reference connection of an instance of the full entry's
module**: the clock or the reset, or a declared wire of `b` at the width of
the type of a binder of the parent — the call's result binder (output
connection) or the argument's `let` binder (argument connection). -/
theorem core_callConns {c : Name} (d : MachineData) (ok : d.ok = true)
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
      ∃ mc, moduleByName D.modules mn = some mc ∧
        (∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
          RealChild mref cref (d.shape.insts[k]).1 y ∧ mc = y.1) ∧
        ∀ pn x, (pn, Sparkle.IR.AST.Expr.ref x) ∈ conns →
          (isSeqChild mc = true ∧ ((pn = "clk" ∧ x = "clk") ∨ (pn = "rst" ∧ x = "rst"))) ∨
          (x ∈ b.wires.map (·.name) ∧
            ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
              RealChild mref cref (d.shape.insts[k]).1 y ∧ mc = y.1 ∧
              ((pn = d.shape.instFields.getD k "" ∧ (∃ p ∈ mc.outputs, p.name = pn) ∧
                  ∃ bn, d.shape.binders[nDecl + k]? = some bn ∧
                    Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth) ∨
                (∃ (j : Nat) (q : Port) (a : Nat) (bn : Name × MixedGateBinder),
                  (inPortsOf mc)[j]? = some q ∧ q.name = pn ∧
                  ((d.shape.insts[k]).2.1)[j]? = some a ∧
                  d.shape.binders[nDecl + (d.shape.insts.length +
                    (d.shape.layout.slots.length + a))]? = some bn ∧
                  Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth))) :=
  core_callConns_ran d ok hbody hC hslots hdomB hins hfne outTy hnomem hpost
    (Tools.ShippingMachineRan.machineRan_of_closes hcore entry hB closes)

set_option maxHeartbeats 4000000 in
/-- **`portsMatchB` of the RAW full-entry module**, from the core run. -/
theorem core_portsMatch_raw {c : Name} (d : MachineData) (ok : d.ok = true)
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
    -- OUTPUT side: the result binder's width is the child's field port's
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    -- OUTPUT side: the child's output ports are resolved by its emitted width map
    (hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y → Tools.ShippingLeafTyped.PortsIn y.1)
    -- INPUT side: the data condition, and (NOT derived) the child's argument
    -- ports' emitted widths
    {kidIns : Nat → List Nat} (hargs : callArgsOk d nDecl kidIns = true)
    (hkidIn : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ (j : Nat) (q : Port), (inPortsOf y.1)[j]? = some q →
        ∃ wd, (kidIns k)[j]? = some wd ∧ Tools.ShippingDesignSV.weS y.1 q.name = wd)
    -- CLOCK / RESET (NOT derived): one bit in a sequential child ...
    (hkidClk : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y → isSeqChild y.1 = true →
      Tools.ShippingDesignSV.weS y.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y.1 "rst" = 1)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    -- ... and in the parent (NOT derived)
    (hclkB : Tools.ShippingDesignSV.weS b "clk" = 1 ∧ Tools.ShippingDesignSV.weS b "rst" = 1) :
    Tools.ShippingDesignSV.portsMatchB (childMap D.modules) b = true := by
  have hT : Tools.ShippingTextTyped.TypedIn b :=
    Tools.ShippingClosedTyped.core_closed_typedIn d ok hbody hC hslots hdomB hins outTy hnomem
      hB hcore hpost entry closes hon hoty
  have hconn := core_callConns d ok hbody hC hslots hdomB hins hfne outTy hnomem hB hcore hpost
    entry closes
  refine Tools.ShippingTextShipped.portsMatchB_of ?_ ?_
  · intro mn iname conns child cwe hst hc cn hcm x hc2
    obtain ⟨mc, hmc, ⟨k0, hk0, y0, hre0, hmcy0⟩, hall⟩ := hconn mn iname conns hst
    have hCm : childMap D.modules mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) :=
      congrArg (fun o : Option Sparkle.IR.AST.Module =>
        o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hmc
    rw [hCm] at hc
    have hch : child = mc := (congrArg Prod.fst (Option.some.inj hc)).symm
    rw [hch]
    have hcm' : (cn.1, Sparkle.IR.AST.Expr.ref x) ∈ conns := by
      rw [← hc2]
      exact hcm
    rcases hall cn.1 x hcm' with ⟨hseq, hcr⟩ | ⟨hxw, k, hk, y, hre, hmcy, hside⟩
    · -- the clock and the reset
      have hseq' : isSeqChild y0.1 = true := by
        rw [← hmcy0]
        exact hseq
      obtain ⟨hk1, hk2⟩ := hkidClk k0 hk0 y0 hre0 hseq'
      rcases hcr with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2, hmcy0, hk1]
        exact hclkB.1
      · rw [e1, e2, hmcy0, hk2]
        exact hclkB.2
    · have h1 : Tools.ShippingDesignSV.weS b x = Sparkle.IR.RegDedup.declWidth b x :=
        (Tools.ShippingWidthTables.declWidth_eq_weS hT.wn hxw).symm
      rcases hside with ⟨hpn, ⟨p, hp, hpe⟩, bn, hbn, hdw⟩ | ⟨j, q, a, bn, hq, hqn, haj, hbn, hdw⟩
      · -- an output connection
        have hP := hkidT k hk y hre
        have hp' : p ∈ y.1.outputs := by
          rw [← hmcy]
          exact hp
        have h3 := hkidW k hk y hre p hp' (hpe.trans hpn)
        rw [hbn] at h3
        have h4 : some ((kindTy bn.2).bitWidth) = some p.ty.bitWidth := h3
        have h5 := Option.some.inj h4
        rw [h1, hdw, h5, hmcy, ← hpe]
        exact (hP.weS_output hp').symm
      · -- an argument connection
        have hq' : (inPortsOf y.1)[j]? = some q := by
          rw [← hmcy]
          exact hq
        obtain ⟨wd, hwd, hws⟩ := hkidIn k hk y hre j q hq'
        have h5 := callArgs_width hargs hk haj hbn hwd
        rw [h1, hdw, h5, hmcy, ← hqn]
        exact hws.symm
  · intro mn iname conns hst
    obtain ⟨mc, hmc, -, -⟩ := hconn mn iname conns hst
    have hCm : childMap D.modules mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) :=
      congrArg (fun o : Option Sparkle.IR.AST.Module =>
        o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hmc
    simp [hCm]

end Tools.ShippingPortsMatchRaw
