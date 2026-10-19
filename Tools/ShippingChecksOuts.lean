import Tools.ShippingChecksExtract
import Tools.ShippingLinkedFresh
import Tools.ShippingClosedPorts
import Tools.ShippingOutsExtractedParts
import Tools.ShippingMachineRanBase
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md).

/-! # Conjunct 6 of `shipsHierCheck`, `outsExtracted`, from the core run (G1)

For a core run on a machine WITH calls closed by `closeInstsG`
(`instFields ≠ []`) — the hypotheses of `core_raw_facts` without `hsl`, and
ONE fact per real child (`hkidP`, below) — on the full entry's module `b`:

    outsExtracted (childMap D.modules) b = true        (`core_outsExtracted`)

and `core_shipsHier_rest4`: `shipsHierCheck` from the run and the FOUR
conjuncts still underived (1 `hierBinds`, 2 and 4 the post-pass facts,
8 `instOutWidthsOk`).

## How

An instance-driven wire `x` of `b` is, by `closeInstsG_insts` (the closing
itself, not `MachineWired`), connected in a call group's instance statement
(`CallStmtG`) to an output port `p` of the module `mc` the instance's name
resolves to; `mc` is the module `y.1` a real child entry returned for an
entry of the group (`closeInstsG_names`: every child module is found by its
name as itself). With the child's ports apart (`hkidP`), the connection is
an OUTPUT connection, so `x = (t.inputs.map name)[machNIn + k]` for an entry
`k < |insts|` (`callStmtG_outWire`) — `hident`. Then:

* (a) declared: the transition's input at that position is a wire of the
  transition, hence of the closed machine, hence of the raw module
  (`CloseCalls.some`: the wires are the closed machine's); its width is not
  zero (the transition's inputs are printable), so the zero-width cleanup
  keeps it (`dropZW_wires`), and the checked merge keeps the wires
  (`mergeChecked_ports`). (`closedPorts_of_run`.)
* (b) connected: `bodyInstOuts_connRefs`.
* (c) not driven: no assignment targets it (`core_instOuts_not_assigned`);
  a register statement of the raw module is one of the closed machine's
  (the closing adds instance statements only: `CloseCalls.some`), whose
  output is a slot port — an input of the transition at a position
  `≥ |inputs| - lets - slots = machNIn + |insts|` — and the transition's
  input names are distinct (`closedPorts_of_run`).
* (d) not an input: the closing removes the call ports from the inputs
  (`closeInstsG_inputs`), the cleanup and the merge keep the inputs.

## The child premise `hkidP`, and why one is needed

    ∀ k (hk : k < |insts|) y, RealChild mref cref insts[k].1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧
        p.name ≠ "clk" ∧ p.name ≠ "rst"

It is `ChildIfaceG.outsIn` / `ChildIfaceD.outsIn` verbatim — the fact the
closing generators already take of every child (`seqChild_of_real` for a
child without calls, `kidsChild_of_real` for one with calls). It is NOT
derivable from the parent's run: `closeInstsG` checks the FIELDS the parent
reads (`CallStmtG`: they are no argument port, not `clk`, not `rst`), not
the child's other output ports; were an unread output port of the child
named as one of its argument ports (or `rst`), `instOutWires` would list the
argument's `let` wire (or `rst`) as instance-driven and `outsExtracted`
would be FALSE (`rst` is an input of `b`). So conjunct 6 does depend on the
child's interface.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingChecksOuts
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
/-- `core_outsExtracted` over `MachineRan`: the TAIL of the built proof, moved (round par/g-1).
What it takes of the run is that the machine synthesis this core run performed
returned `(M, D)` from an invariant world; `core_outsExtracted` below is its instance at the
all-worlds closing (`Tools.ShippingMachineRan.machineRan_of_closes`). -/
theorem core_outsExtracted_ran {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    Tools.ShippingHierPremisesBase.outsExtracted (childMap D.modules) b = true := by
  -- the full entry's body is the raw module's; no assignment targets an instance output
  have hbody' : b.body = M.body :=
    (Tools.ShippingChecksCore.core_kids_facts_ran d ok hbody hC hslots hdomB hins outTy hnomem hpost ran).2.1
  have hasg := Tools.ShippingLinkedFresh.core_instOuts_not_assigned_ran d ok hbody hC hslots hdomB
    hins outTy hnomem hpost ran
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
  have ran0 := ran
  obtain ⟨_, bb, w9, w10, hrun9, hw9, -⟩ := ran0
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ := synthesizeMachineCertified_runs hw9 hrun9
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, hreal⟩
  · exact absurd hno hins
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
        rcases hor with hmem | hre
        · rw [Tools.ShippingChildInv.nomem_tag hnomem hk0] at hmem
          cases hmem
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

set_option maxHeartbeats 4000000 in
/-- **Every instance-driven wire of the full entry's module is an extracted
input of the optimizer check**, from the core run of a machine with calls
closed by `closeInstsG`, each real child's output ports apart from its
argument ports, `clk` and `rst`. -/
theorem core_outsExtracted {c : Name} (d : MachineData) (ok : d.ok = true)
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
    Tools.ShippingHierPremisesBase.outsExtracted (childMap D.modules) b = true :=
  core_outsExtracted_ran d ok hbody hC hslots hdomB hins hfne outTy hnomem hkidP hpost
    (Tools.ShippingMachineRan.machineRan_of_closes hcore entry hB closes)

/-- **`shipsHierCheck` from the run and the four conjuncts not derived**: the
optimizer gate, the two post-pass facts and the instance-output widths.
(`core_shipsHier_rest` without `houts`; the per-child fact `hkidP` instead.) -/
theorem core_shipsHier_rest4 {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
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
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    -- 1: the optimizer gate
    (hb : hierBinds b = true)
    -- 2, 4: the post-pass facts
    (hwfO : Tools.ShippingHierOpen.linkedWF (childMap D.modules) (checkedOptimize b).body = true)
    (hndO : (Tools.ShippingHierState.instNames (checkedOptimize b).body).Nodup)
    -- 8: run fact not derived yet
    (hwid : Tools.ShippingHierOpen.instOutWidthsOk (childMap D.modules)
      (Sparkle.IR.RegDedup.declWidth b) b.body = true) :
    Tools.ShippingHierPremisesBase.shipsHierCheck (childMap D.modules) b = true := by
  obtain ⟨hrst, hndB, hself⟩ :=
    Tools.ShippingChecksRaw.core_raw_facts d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem
      hB hcore hpost entry closes
  have houts := core_outsExtracted d ok hbody hC hslots hdomB hins hfne outTy hnomem hkidP hB
    hcore hpost entry closes
  exact Tools.ShippingChecksShipsHier.shipsHierCheck_of hb hwfO hndB hndO hself houts hrst hwid

end Tools.ShippingChecksOuts
