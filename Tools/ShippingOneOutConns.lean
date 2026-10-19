import Tools.ShippingPortsMatchRaw
import Tools.ShippingOneOutFacts
import Tools.ShippingTypedWidthOk
import Tools.ShippingChildServe
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

/-! # The connections of a ONE-OUTPUT parent, and its two residual checks from child-side facts (G1, round par/a-7; P1 and T2–T5 of docs/parallel/A-oneout.md)

For a machine with calls closed by the one-output closing `closeInsts`
(`instFields = []`):

* `callStmt_conn` (pure): a reference connection of a call's instance
  statement (`CallStmt`) is an ARGUMENT connection — the `j`-th argument port
  of the child to the transition port of the `let` `args[j]` — or THE output
  connection, the child's one output port to the call's transition port.
  (`callStmtG_conn`'s proof on `CallStmt`'s connection list; there is no
  clock / reset case: the list has none.)
* `inPortsOf_of_notSeq` (pure): a child with no clock and no reset input has
  all its inputs as argument ports.
* `core_callConns₁` (from the core run): every instance statement of the full
  entry's module `b` is call `k`'s, of a REAL child `y` found by name in
  `D.modules` as `y.1`; `y.1` has one output port `outP` and no clock /
  reset input; the connection list is as `callStmt_parts` describes it; the
  output wire is a declared wire of `b` whose declared width is the width of
  the type of the call's result binder `binders[nDecl + k]`; and each other
  reference connection `(pn, .ref x)` is the `j`-th input port of `y.1` read
  from a declared wire `x` of `b` whose declared width is the width of the
  type of the `let` binder of `args[j]`. Its proof is `core_callConns`'s
  (`Tools/ShippingPortsMatchRaw.lean`, the wire/width argument `key` copied)
  on `closeInsts`'s result (`core_closeInsts`, `closeInsts_insts`,
  `closeInsts_names`).
* `core_portsMatch_raw₁` (P1): `portsMatchB (childMap D.modules) b = true`.
* `core_hierTyped₁` (T2–T5): `hierTyped (childMap D.modules) b = true`.

## What the two theorems still ask — the PARENT side

Both take the parent's data conditions of the unit (`callsOk`, the slot
count, no late domain binder, `insts ≠ []`, `instFields = []`, the output
widths, no memory callee, clean output names, scalar output types) and the
run boundary (`ChildBnd`, the core run, `MachineDefines`, `MachineClosesAt`).
Neither asks `slots ≠ []`: these two checks do not depend on the parent
having a register. From them the PARENT-side facts are derived inside:
`TypedIn b` (`core_closed_typedIn`) and `core_callConns₁`. One parent-side
DATA condition stays a hypothesis, decidable per declaration:

    hargs : callArgsOk d nDecl kidIns = true

(the width of the type of the `let` binder of each call argument is the
child's argument width `(kidIns k)[j]`). NOTHING in the compiler compares
these two widths (as noted at `callArgsOk`); it is a condition on the
SOURCE declaration's reflected data, not a run fact.

## What they ask — the CHILD side (each about ONE real child's module)

    hkidW   : ∀ p ∈ y.1.outputs, (binders[nDecl + k]?).map (width of its type) = some p.ty.bitWidth
    hkidT   : PortsIn y.1                                   (portsMatchB only)
    hkidIn  : y.1.inputs[j]? = some q → ∃ wd, (kidIns k)[j]? = some wd ∧ weS y.1 q.name = wd
                                                            (portsMatchB only)
    hkidInD : y.1.inputs[j]? = some q → ∃ wd, (kidIns k)[j]? = some wd ∧ declWidth y.1 q.name = wd
                                                            (hierTyped only)
    hkidTy  : childTyped (declWidth y.1) y.1 = true         (hierTyped only)

For a GATE child every one of them follows from
`Tools.ShippingGatePorts.GateChildPorts` (`outWidth`, `portsIn`, `inWidths`
— one statement for both tables — and `childTyped_ok`), with `kidIns k` the
widths of the child's declared non-domain binders; `hkidW` then is a data
condition on the parent's result binder against the child's sort width.
For a machine-route child (worker B's `entryStrict_declared`) they are not
derived here.

UNVERIFIED at the time of writing: this file was not built. It imports
`Tools.ShippingOneOutFacts`, itself queued for its first build. -/
namespace Tools.ShippingOneOutConns
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
open Tools.ShippingPortsMatchRaw (callArgsOk callArgs_width)

/-! ## Pure -/

/-- **A reference connection of a one-output call's instance**: an argument
connection, or the output connection. -/
theorem callStmt_conn {nIn kI n k : Nat} {names : List String} {args : List Nat}
    {mc : Sparkle.IR.AST.Module} {mn iname : String}
    {conns : List (String × Sparkle.IR.AST.Expr)}
    (h : Tools.ShippingMachineInst.CallStmt nIn kI n names k args mc
      (Stmt.inst mn iname conns))
    {pn x : String} (hm : (pn, Sparkle.IR.AST.Expr.ref x) ∈ conns) :
    (∃ (j : Nat) (q : Port) (a : Nat), (inPortsOf mc)[j]? = some q ∧ q.name = pn ∧
        args[j]? = some a ∧ names[nIn + kI + n + a]? = some x) ∨
    (∃ outP : Port, mc.outputs = [outP] ∧ outP.name = pn ∧ names[nIn + k]? = some x) := by
  obtain ⟨outW, argWs, outP, iname', hout, hargs, houts, -, -, -, -, -, -, he⟩ := h
  injection he with h1 h2 h3
  rw [h3] at hm
  rcases List.mem_append.mp hm with hm | hm
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
  · -- the output connection
    right
    have h0 := List.mem_singleton.mp hm
    have e1 : pn = outP.name := congrArg Prod.fst h0
    have e2 : Sparkle.IR.AST.Expr.ref x = Sparkle.IR.AST.Expr.ref outW := congrArg Prod.snd h0
    have e3 : x = outW := by
      cases e2
      rfl
    exact ⟨outP, houts, e1.symm, by rw [e3]; exact hout⟩

/-- A child with no clock and no reset input: every input is an argument
port. -/
theorem inPortsOf_of_notSeq {mc : Sparkle.IR.AST.Module}
    (h : (mc.inputs.any fun p => p.name == "clk" || p.name == "rst") = false) :
    inPortsOf mc = mc.inputs := by
  unfold Tools.ShippingInstStmtG.inPortsOf
  refine List.filter_eq_self.mpr (fun p hp => ?_)
  have hor : (p.name == "clk" || p.name == "rst") = false := by
    cases hc : (p.name == "clk" || p.name == "rst") with
    | false => rfl
    | true =>
      have hany : (mc.inputs.any fun p => p.name == "clk" || p.name == "rst") = true :=
        List.any_eq_true.mpr ⟨p, hp, hc⟩
      rw [h] at hany
      cases hany
  have h1 : (p.name == "clk") = false := by
    cases hc : (p.name == "clk") with
    | false => rfl
    | true =>
      rw [hc] at hor
      first
        | cases hor
        | simp at hor
  have h2 : (p.name == "rst") = false := by
    cases hc : (p.name == "rst") with
    | false => rfl
    | true =>
      rw [h1, hc] at hor
      first
        | cases hor
        | simp at hor
  show (p.name != "clk" && p.name != "rst") = true
  simp [bne, h1, h2]

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## From the run -/

set_option maxHeartbeats 4000000 in
/-- **Every instance statement of the full entry's module of a one-output
parent**: the real child, the shape of the connection list, and the declared
widths of the parent's wires it connects, as the widths of the types of the
parent's binders. -/
theorem core_callConns₁ {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res) (outW : String)
        (argWs : List String) (outP : Port),
        RealChild mref cref (d.shape.insts[k]).1 y ∧
        moduleByName D.modules mn = some y.1 ∧
        y.1.outputs = [outP] ∧
        isSeqChild y.1 = false ∧
        (∀ cn ∈ conns, cn = (outP.name, Sparkle.IR.AST.Expr.ref outW) ∨
          ∃ q ∈ y.1.inputs, ∃ aw ∈ argWs,
            cn = (q.name, Sparkle.IR.AST.Expr.ref aw) ∧ q.name ≠ outP.name) ∧
        (outP.name, Sparkle.IR.AST.Expr.ref outW) ∈ conns ∧
        (outW ∈ b.wires.map (·.name) ∧ ∃ bn, d.shape.binders[nDecl + k]? = some bn ∧
          Sparkle.IR.RegDedup.declWidth b outW = (kindTy bn.2).bitWidth) ∧
        ∀ pn x, (pn, Sparkle.IR.AST.Expr.ref x) ∈ conns → pn ≠ outP.name →
          ∃ (j : Nat) (q : Port) (a : Nat) (bn : Name × MixedGateBinder),
            y.1.inputs[j]? = some q ∧ q.name = pn ∧
            ((d.shape.insts[k]).2.1)[j]? = some a ∧
            d.shape.binders[nDecl + (d.shape.insts.length +
              (d.shape.layout.slots.length + a))]? = some bn ∧
            x ∈ b.wires.map (·.name) ∧
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
  -- the run: the one-output closing
  obtain ⟨_, logProf, t, t', d₀, children, run, hcl, hI, hreal⟩ :=
    Tools.ShippingOneOutFacts.core_closeInsts d hins hf hB hcore entry closes
  obtain ⟨hMw, -⟩ := Tools.ShippingMachineInst.closeInsts_some hI
  obtain ⟨hseq0, -, -⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨PI, ls, hin, hPI, hlsL, hndI, hinW, hregs⟩ :=
    Tools.ShippingClosedPorts.closedPorts_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨hwnd, hwal, hinWt, P1, P2, hsp, hP2d, hP2len, hP2ty⟩ :=
    Tools.ShippingTransitionPortTys.transitionPortTys_of_run d ok hbody hC hslots hdomB run
  have hls : P2 = ls := (List.append_inj' (hsp.symm.trans hin) (by omega)).2
  obtain ⟨hlenC, hallC⟩ := hreal
  -- a transition port after the declaration's: a wire of `b`, declared at
  -- the width of its binder's type (`core_callConns`' `key`)
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
  intro mn iname conns hst
  rw [hbody'] at hst
  rcases Tools.ShippingMachineInst.closeInsts_insts hI _ hst rfl with
    h0 | ⟨k, args, child, mc, hargs0, hch0, hmc, hcs⟩
  · exact Tools.ShippingChecksDerived.ff_absurd (List.all_eq_true.mp hseq0 _ h0)
  have hk0 : k < d.shape.insts.length := by
    have := (List.getElem?_eq_some_iff.mp hargs0).1
    simpa using this
  -- the call's child is real, and the module found by its name is its module
  obtain ⟨y, hy, hor⟩ := hallC k hk0
  have hyc : y = child := Option.some.inj (hy.symm.trans hch0)
  have hnm1 := (Tools.ShippingChildServe.closeInsts_names hI).2 child (List.mem_of_getElem? hch0)
  have hmcc : mc = child.1 := Option.some.inj (hmc.symm.trans hnm1)
  have hmcy : mc = y.1 := by
    rw [hyc]
    exact hmcc
  have hre : RealChild mref cref (d.shape.insts[k]).1 y := by
    rcases hor with hmem | hre
    · rw [Tools.ShippingChildInv.nomem_tag hnomem hk0] at hmem
      cases hmem
    · exact hre
  have h9 : (d.shape.insts.map (·.2.1))[k]? =
      Option.map (·.2.1) (some (d.shape.insts[k])) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hk0]
  have h10 : some args = some ((d.shape.insts[k]).2.1) := hargs0.symm.trans h9
  have hA : args = (d.shape.insts[k]).2.1 := Option.some.inj h10
  obtain ⟨outW, argWs, outP, hmn, hout, houts, hclk, hne, hrst, hall, hmemO⟩ :=
    Tools.ShippingOneOutClose.callStmt_parts hcs
  have hfind' : moduleByName D.modules mn = some mc := by
    rw [hmn, Tools.ShippingMachineInst.moduleByName_name hmc]
    exact hmc
  have hni : inPortsOf mc = mc.inputs := inPortsOf_of_notSeq hclk
  refine ⟨k, hk0, y, outW, argWs, outP, hre, ?_, ?_, ?_, ?_, hmemO, key k outW hout, ?_⟩
  · rw [← hmcy]
    exact hfind'
  · rw [← hmcy]
    exact houts
  · rw [← hmcy]
    exact hclk
  · rw [← hmcy]
    exact hall
  · intro pn x hpc hpn
    rcases callStmt_conn hcs hpc with ⟨j, q, a, hq, hqn, haj, hnm⟩ | ⟨outP', houts', e1, -⟩
    · have eidx : machNIn d.shape + d.shape.insts.length + d.shape.layout.slots.length + a =
          machNIn d.shape + (d.shape.insts.length + (d.shape.layout.slots.length + a)) := by
        omega
      have hnm' : (t.inputs.map (·.name))[machNIn d.shape +
          (d.shape.insts.length + (d.shape.layout.slots.length + a))]? = some x := by
        rw [← eidx]
        exact hnm
      obtain ⟨hxw, bn, hbn, hdw⟩ := key _ x hnm'
      rw [hA] at haj
      have hq' : y.1.inputs[j]? = some q := by
        rw [← hmcy, ← hni]
        exact hq
      exact ⟨j, q, a, bn, hq', hqn, haj, hbn, hxw, hdw⟩
    · exfalso
      rw [houts] at houts'
      have he : outP = outP' := (List.cons.inj houts').1
      exact hpn (by rw [he]; exact e1.symm)

set_option maxHeartbeats 4000000 in
/-- **`portsMatchB` of the RAW full-entry module of a one-output parent**
(P1), from the core run and the child-side facts `hkidW`, `hkidT`, `hkidIn`
and the data condition `hargs`. No clock / reset hypothesis: a one-output
call has no such connection. -/
theorem core_portsMatch_raw₁ {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    -- OUTPUT side: the result binder's width is the child's output port's
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs,
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    -- OUTPUT side: the child's output port is resolved by its emitted width map
    (hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y → Tools.ShippingLeafTyped.PortsIn y.1)
    -- INPUT side: the data condition, and the child's input ports' emitted widths
    {kidIns : Nat → List Nat} (hargs : callArgsOk d nDecl kidIns = true)
    (hkidIn : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ (j : Nat) (q : Port), y.1.inputs[j]? = some q →
        ∃ wd, (kidIns k)[j]? = some wd ∧ Tools.ShippingDesignSV.weS y.1 q.name = wd)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    Tools.ShippingDesignSV.portsMatchB (childMap D.modules) b = true := by
  have hT : Tools.ShippingTextTyped.TypedIn b :=
    Tools.ShippingClosedTyped.core_closed_typedIn d ok hbody hC hslots hdomB hins outTy hnomem
      hB hcore hpost entry closes hon hoty
  have hconn := core_callConns₁ d ok hbody hC hslots hdomB hins hf outTy hnomem hB hcore hpost
    entry closes
  refine Tools.ShippingTextShipped.portsMatchB_of ?_ ?_
  · intro mn iname conns child cwe hst hc cn hcm x hc2
    obtain ⟨k, hk, y, outW, argWs, outP, hre, hfind, houts, hns, hall, hmemO,
      ⟨hxo, bno, hbno, hdwo⟩, hargsC⟩ := hconn mn iname conns hst
    have hCm : childMap D.modules mn = some (y.1, Sparkle.IR.RegDedup.declWidth y.1) :=
      congrArg (fun o : Option Sparkle.IR.AST.Module =>
        o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hfind
    rw [hCm] at hc
    have hch : child = y.1 := (congrArg Prod.fst (Option.some.inj hc)).symm
    rw [hch]
    have hcm' : (cn.1, Sparkle.IR.AST.Expr.ref x) ∈ conns := by
      rw [← hc2]
      exact hcm
    by_cases hpo : cn.1 = outP.name
    · -- the output connection
      rcases hall _ hcm' with e | ⟨q, -, aw, -, e, hqo⟩
      · have h2' : Sparkle.IR.AST.Expr.ref x = Sparkle.IR.AST.Expr.ref outW :=
          congrArg Prod.snd e
        have hx : x = outW := by
          cases h2'
          rfl
        have h1 : Tools.ShippingDesignSV.weS b outW = Sparkle.IR.RegDedup.declWidth b outW :=
          (Tools.ShippingWidthTables.declWidth_eq_weS hT.wn hxo).symm
        have hp' : outP ∈ y.1.outputs := by
          rw [houts]
          exact List.mem_singleton.mpr rfl
        have h3 := hkidW k hk y hre outP hp'
        rw [hbno] at h3
        have h4 : some ((kindTy bno.2).bitWidth) = some outP.ty.bitWidth := h3
        have h5 := Option.some.inj h4
        rw [hx, hpo, h1, hdwo, h5]
        exact ((hkidT k hk y hre).weS_output hp').symm
      · exact absurd ((congrArg Prod.fst e).symm.trans hpo) hqo
    · -- an argument connection
      obtain ⟨j, q, a, bn, hq, hqn, haj, hbn, hxw, hdw⟩ := hargsC cn.1 x hcm' hpo
      obtain ⟨wd, hwd, hws⟩ := hkidIn k hk y hre j q hq
      have h5 := callArgs_width hargs hk haj hbn hwd
      have h1 : Tools.ShippingDesignSV.weS b x = Sparkle.IR.RegDedup.declWidth b x :=
        (Tools.ShippingWidthTables.declWidth_eq_weS hT.wn hxw).symm
      rw [h1, hdw, h5, ← hqn]
      exact hws.symm
  · intro mn iname conns hst
    obtain ⟨k, hk, y, outW, argWs, outP, hre, hfind, -⟩ := hconn mn iname conns hst
    have hCm : childMap D.modules mn = some (y.1, Sparkle.IR.RegDedup.declWidth y.1) :=
      congrArg (fun o : Option Sparkle.IR.AST.Module =>
        o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hfind
    simp [hCm]

set_option maxHeartbeats 4000000 in
/-- **`hierTyped` of the full-entry module of a one-output parent** (T2–T5),
from the core run and the child-side facts `hkidW`, `hkidInD`, `hkidTy` and
the data condition `hargs`: the assignments are typed in the module's own
wire table (`typedIn_assignTyped`); each instance's child is a typed child
and its connections are typed (`connsTyped_call`: equal widths on both sides
of every connection); no memory; no extracted input is an output port. -/
theorem core_hierTyped₁ {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    -- OUTPUT side: the result binder's width is the child's output port's
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs,
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    -- the child is a width-typed child in its own declared widths
    (hkidTy : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingHierTyped.childTyped (Sparkle.IR.RegDedup.declWidth y.1) y.1 = true)
    -- INPUT side: the data condition, and the child's input ports' declared widths
    {kidIns : Nat → List Nat} (hargs : callArgsOk d nDecl kidIns = true)
    (hkidInD : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ (j : Nat) (q : Port), y.1.inputs[j]? = some q →
        ∃ wd, (kidIns k)[j]? = some wd ∧ Sparkle.IR.RegDedup.declWidth y.1 q.name = wd)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    Tools.ShippingHierTyped.hierTyped (childMap D.modules) b = true := by
  have hT : Tools.ShippingTextTyped.TypedIn b :=
    Tools.ShippingClosedTyped.core_closed_typedIn d ok hbody hC hslots hdomB hins outTy hnomem
      hB hcore hpost entry closes hon hoty
  have hconn := core_callConns₁ d ok hbody hC hslots hdomB hins hf outTy hnomem hB hcore hpost
    entry closes
  -- a declared wire is no output port
  have hnotX : ∀ x, x ∈ b.wires.map (·.name) → x ∉ b.outputs.map (·.name) := by
    intro x hx hxo'
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hx
    obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hxo'
    have hpn' : p.name = x := hpn
    have hqn' : q.name = x := hqn
    exact hT.ow q hq p hp (hpn'.trans hqn'.symm)
  unfold Tools.ShippingHierTyped.hierTyped
  refine (Bool.and_eq_true _ _).mpr ⟨?_, ?_⟩
  · refine Tools.ShippingTypedWidthOk.kidsTyped_of
      (fun l r hm => Tools.ShippingTypedWidthOk.typedIn_assignTyped hT hm) ?_ hT.kinds
    intro mn iname conns hst
    obtain ⟨k, hk, y, outW, argWs, outP, hre, hfind, houts, hns, hall, hmemO,
      ⟨hxo, bno, hbno, hdwo⟩, hargsC⟩ := hconn mn iname conns hst
    have hCm : childMap D.modules mn = some (y.1, Sparkle.IR.RegDedup.declWidth y.1) :=
      congrArg (fun o : Option Sparkle.IR.AST.Module =>
        o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hfind
    refine ⟨y.1, Sparkle.IR.RegDedup.declWidth y.1, hCm, hkidTy k hk y hre, ?_⟩
    refine Tools.ShippingTypedWidthOk.connsTyped_call houts hall hmemO ?_ ?_
    · intro pn aw hpc hpn
      obtain ⟨j, q, a, bn, hq, hqn, haj, hbn, hxw, hdw⟩ := hargsC pn aw hpc hpn
      obtain ⟨wd, hwd, hws⟩ := hkidInD k hk y hre j q hq
      have h5 := callArgs_width hargs hk haj hbn hwd
      have e1 : Sparkle.IR.RegDedup.declWidth b aw =
          Sparkle.IR.RegDedup.declWidth y.1 pn := by
        rw [hdw, h5, ← hqn, hws]
      exact ⟨hnotX aw hxw, Nat.le_of_eq e1⟩
    · have hp' : outP ∈ y.1.outputs := by
        rw [houts]
        exact List.mem_singleton.mpr rfl
      have h3 := hkidW k hk y hre outP hp'
      rw [hbno] at h3
      have h4 : some ((kindTy bno.2).bitWidth) = some outP.ty.bitWidth := h3
      have h5 := Option.some.inj h4
      have e2 : outP.ty.bitWidth = Sparkle.IR.RegDedup.declWidth b outW := by
        rw [hdwo, h5]
      exact Or.inr (Nat.le_of_eq e2)
  · rw [List.all_eq_true]
    intro p hp
    have hpw : p ∈ b.wires := (List.mem_filter.mp hp).1
    refine Tools.ShippingTypedWidthOk.not_contains (fun hx => ?_)
    obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hx
    have hqn' : q.name = p.name := hqn
    exact hT.ow q hq p hpw hqn'.symm

end Tools.ShippingOneOutConns
