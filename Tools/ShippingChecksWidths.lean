import Tools.ShippingChecksOuts
import Tools.ShippingTransitionPortTys
import Tools.ShippingInstWidthsParts

/-! # Conjunct 8, `instOutWidthsOk`, and the gate half of conjunct 1 (G1)

For a core run on a machine WITH calls closed by `closeInstsG` — the
hypotheses of `core_outsExtracted` (with its per-child `hkidP`) — on the
full entry's module `b`:

* `core_callPorts`: every instance statement of `b` resolves in the design
  to a module `mc`, and every connection `(p.name, ref x)` of an output
  port `p` of `mc` is the output connection of a call entry `k`: `mc` is
  the module of a real child of `insts[k]`, `p` is the field
  `instFields[k]`, and the DECLARED width of `x` in `b` is the width of the
  type the transition gave the binder of that call's result,
  `(kindTy (binders[nDecl + k]).2).bitWidth`.
* `core_instOutWidthsOk`: `instOutWidthsOk (childMap D.modules)
  (declWidth b) b.body = true`, under ONE more per-child premise, `hkidW`.
* `core_shipsHier_rest3`: `shipsHierCheck` from the run and conjuncts 1, 2,
  4 (`hierBinds`, the two post-pass facts).
* `core_hierGate`: `hierGate b = true` (the statement-kind half of
  `hierBinds`); `core_shipsHier_rest3F`: `core_shipsHier_rest3` with
  `hierBinds b` replaced by `refineCheck flat flat` on the extracted
  interface.

## The premise `hkidW`: a width agreement NOTHING checks

    ∀ k (hk : k < |insts|) y, RealChild mref cref insts[k].1 y →
      ∀ p ∈ y.1.outputs, p.name = instFields.getD k "" →
        (binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) = some p.ty.bitWidth

The parent's wire for a call result is declared at the type of the BINDER
the reader made for it (`machInstance` / `machInstanceS`,
`Sparkle/Compiler/Elab.lean`: the kind of the call's result type at the
call site, `machOuts?` of the instantiated result type). The child's output
port has the type of the child's OWN layout field (`ChildOutTys`). Read
from the sources:

* `closeInstsG` / `instStmtG` (`Sparkle/IR/MachineInstG.lean`) compare
  NAMES only (the field is an output port of the child, the call port is a
  declared wire of the parent); no width is compared;
* `MachineData.ok` and `callsOk` are checks on the PARENT's data alone; the
  child's layout is not in it;
* `instOutWidthsOk` itself occurs nowhere under `Sparkle/`: it is evaluated
  by no compiler pass. It is a conjunct of the endpoint premise
  `shipsHierCheck` only.

So the agreement is a relation between two declarations' data, decidable
for a given pair once the child's ports are its layout's
(`leaf_real_outTys`; done for `parent` / `cnt` in the test by `decide`),
and it holds in practice because both sides come from the same structure
type. Were it to fail (a reader giving the call binder another width than
the child's field — e.g. a result type whose width the call site and the
child's own declaration normalise differently), the parent would declare
`wire [A-1:0] w` and connect it to a `B`-bit port: SystemVerilog truncates
or zero-extends silently, while the linked meaning seeds `w` with the
child's value. No compile-time check would refuse it; the ONLY guard is
that the endpoint's premise `shipsHierCheck` (this conjunct) is then false,
so no theorem is claimed for that module — the module is still emitted.

## Conjunct 1: what `core_hierGate` leaves, and why it is not a fallback

`hierBinds b = hierGate b && refineCheck flat flat`. The gate is derived
(`core_hierGate`). `refineCheck flat flat` is NOT, and nothing existing
proves a `refineCheck _ _ = true`: the instance-free route
(`machine_ships_wired`) never shows that its check binds — it uses that a
FAILED check returns the module unchanged (`mergeChecked_nonAssign`,
`checkedOptimize_seqOk`: "a checked refinement, or the module itself").
`checkedOptimize` (`Sparkle/IR/RefineCheck.lean`) has no such fallback for
an instance-bearing module: when `hierBinds m` is false it returns the
optimizer's output `o` UNCHECKED (`else o`). So on this route `hierBinds b`
is a real premise: without it the shipped module is not validated at all.
`refineCheck flat flat` asks that every assignment of the body normalises
(`rNormBody`: the operators of the normal forms, equal mux branch widths,
two-part concatenations, in-range constants, wire widths equal to their
definitions'), i.e. a property of what the translator emits for THIS body;
no theorem states it for the translator's output.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingChecksWidths
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

set_option maxHeartbeats 4000000 in
/-- **The output connections of the full entry's instances**: each is the
connection of a call entry `k` — the instance's module a real child's, the
port the entry's field — and its wire is declared at the width of the type
of the call's binder. -/
theorem core_callPorts {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
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
            RealChild mref cref (d.shape.insts[k]).1 y ∧ mc = y.1 ∧
            p.name = d.shape.instFields.getD k "" ∧
            ∃ bn, d.shape.binders[nDecl + k]? = some bn ∧
              Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth := by
  have hbody' : b.body = M.body :=
    (Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB
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
theorem core_instOutWidthsOk {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
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
  have hcp := core_callPorts d ok hbody hC hslots hdomB hins hfne outTy hnomem hkidP hB hcore
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

/-- **`shipsHierCheck` from the run and the three conjuncts not derived**:
the optimizer gate and the two post-pass facts. (`core_shipsHier_rest4`
without `hwid`; the per-child width agreement `hkidW` instead.) -/
theorem core_shipsHier_rest3 {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    -- 1: the optimizer gate
    (hb : hierBinds b = true)
    -- 2, 4: the post-pass facts
    (hwfO : Tools.ShippingHierOpen.linkedWF (childMap D.modules) (checkedOptimize b).body = true)
    (hndO : (Tools.ShippingHierState.instNames (checkedOptimize b).body).Nodup) :
    Tools.ShippingHierPremisesBase.shipsHierCheck (childMap D.modules) b = true :=
  Tools.ShippingChecksOuts.core_shipsHier_rest4 d ok hbody hC hslots hdomB hins hsl hfne outTy
    hnomem hkidP hB hcore hpost entry closes hb hwfO hndO
    (core_instOutWidthsOk d ok hbody hC hslots hdomB hins hfne outTy hnomem hkidP hkidW hB hcore
      hpost entry closes)

set_option maxHeartbeats 4000000 in
/-- **The statement-kind gate of the hierarchical check**: the full entry's
module has an instance statement, and every statement is an instance, an
assignment or a register. -/
theorem core_hierGate {c : Name} (d : MachineData) (ok : d.ok = true)
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
    Sparkle.IR.RefineCheck.hierGate b = true := by
  have hbody' : b.body = M.body :=
    (Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB
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

/-- **`shipsHierCheck` with the gate half of conjunct 1 derived**: what is
left of `hierBinds b` is `refineCheck flat flat` on the extracted interface
`flat = openFlat b (openIns b) (openOuts b)`. -/
theorem core_shipsHier_rest3F {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    -- 1, what is left: the extracted interface is in the normal forms
    (hflat : Sparkle.IR.RefineCheck.refineCheck
      (Sparkle.IR.HierCheck.openFlat b (Sparkle.IR.HierCheck.openIns b)
        (Sparkle.IR.HierCheck.openOuts b))
      (Sparkle.IR.HierCheck.openFlat b (Sparkle.IR.HierCheck.openIns b)
        (Sparkle.IR.HierCheck.openOuts b)) = true)
    -- 2, 4: the post-pass facts
    (hwfO : Tools.ShippingHierOpen.linkedWF (childMap D.modules) (checkedOptimize b).body = true)
    (hndO : (Tools.ShippingHierState.instNames (checkedOptimize b).body).Nodup) :
    Tools.ShippingHierPremisesBase.shipsHierCheck (childMap D.modules) b = true :=
  core_shipsHier_rest3 d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem hkidP hkidW hB hcore
    hpost entry closes
    (Tools.ShippingInstWidthsParts.hierBinds_of
      (core_hierGate d ok hbody hC hslots hdomB hins hfne outTy hnomem hB hcore hpost entry closes)
      hflat)
    hwfO hndO

end Tools.ShippingChecksWidths
