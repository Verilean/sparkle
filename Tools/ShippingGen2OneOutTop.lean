import Tools.ShippingGen2TopContract
import Tools.ShippingGen2FitChain
import Tools.ShippingGen2OneOutNames
set_option autoImplicit false
-- BUILT: g2sb-93e9994c at 93e9994c (exit 0; standard axioms).
-- S1 combined: re-elaborated at 02e828fc in s1c-02e828fc (clean, exit 0, standard axioms).
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # S4 stage B: `RunFacts.wid` of a one-output parent and `oneOut_topShips`
(scripts/gen2/S4_STAGEB_FREEZE.md rev1, approved; §1, §2, §3, §4)

* `core_callPorts_oneA` (freeze §4): `core_callPorts_ranA` (ParentRunFactsA:437-561) on the `hf0` branch of
  `CloseCalls` (`closeInsts_insts`, `callStmt_parts`), with the call's `CallStmt` restated in the TRACE's port names through
  `NamesEq` (`ranA_inputs_machPorts` on `ran`'s own harness run + `machPorts_names_indep`). The `declWidth` part is the
  template's, unchanged. No `children`/`RealChildA` is mentioned.
* `core_instOutWidthsOk_oneA` (freeze §4): `core_instOutWidthsOk_ranA` (ParentRunFactsA:585-609) with `hkidW1`.
* `oneOutWidthAt` (freeze §2): the local width fact of THE served child of call `k` (`Served1P` → `ShipsRes` →
  `ChildShips` output conjunct at `i0`, both `ChildRunN` branches, + `hW`). No `RealChildA` identification.
* `oneOut_topShips` (freeze §3, §4 "Use"): a case split on `Nonempty ι` (freeze §3 names `isEmpty_or_nonempty ι`; the project
  has no Mathlib, so the split is `Classical.em (Nonempty ι)`, the same two cases). Empty: `h`'s own witness, `∀ i`
  closed by `hne ⟨i⟩`. Nonempty `⟨i0⟩`: `RunFacts` from `core_runFactsHA` / `core_linkedWF_ranA` / `wid`, then
  `machine_ships_hierC_run` (FitChain:1073) unchanged, `composed` = `machine_linked_callsServed1F` →
  `composedNWn_of_HBF` → `composedNWRegsF_of_composedNWF` (+ `hWd_of_wired`), assembled as `memParent_topShips`
  (Tools/ShippingGen2MemTop.lean). Telescope: S4_CONSUMER_FREEZE:449-467 WITHOUT `hBd` (STAGEB freeze §5: "`hBd` is NOT a
  stage-B premise"). -/

/-! ## The two run-level lemmas (ambient: the opens of ParentRunFactsA:28-46) -/
namespace Tools.ShippingGen2
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIfaceA Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingChildRunA Tools.ShippingCallWidthsChildRealA Tools.ShippingChildBndCore
open Tools.ShippingChecksCore Tools.ShippingLinkedFresh Tools.ShippingClosedTyped Tools.ShippingParentRanA
open Tools.ShippingParentTailsA Tools.ShippingParentDesignA
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingChecksWidths Tools.ShippingChecksOuts Tools.ShippingChecksRaw Tools.ShippingChecksRun

set_option maxHeartbeats 4000000 in
/-- **The call ports of a one-output parent, in the trace's port names** (freeze §4). Every instance statement of `b` is
the `CallStmt` of a call `k` (the SAME statement), named with `machPorts c ids cache` for ANY `ids` of the binders' length
and any `cache`; the wire an output port drives has the declared width of the call's binder. -/
theorem core_callPorts_oneA {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true) (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ []) (hf0 : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    {ids : List FVarId} (hlen : ids.length = d.shape.binders.length) (cache : IO.Ref (ExprStructMap String)) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, moduleByName D.modules mn = some mc ∧
        ∀ p ∈ mc.outputs, ∀ x, (p.name, Sparkle.IR.AST.Expr.ref x) ∈ conns →
          ∃ (k : Nat) (hk : k < d.shape.insts.length) (args : List Nat),
            (d.shape.insts.map (·.2.1))[k]? = some args ∧
            Tools.ShippingMachineInst.CallStmt (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
              ((machPorts c ids cache d.shape.binders).map (·.name)) k args mc (Stmt.inst mn iname conns) ∧
            ∃ bn, d.shape.binders[nDecl + k]? = some bn ∧
              Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth := by
  have hbody' : b.body = M.body :=
    (Tools.ShippingParentTailsA.core_kids_facts_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran).2.1
  -- the cleanup and the checked merge keep the non-zero wires and add none (template :472-485, verbatim)
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
  obtain ⟨_, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ran0
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, -⟩
  · exact absurd hno hins
  obtain ⟨hMw, -⟩ := hcc.some
  -- the `hf0` branch of `CloseCalls` (the reverse of the template's :460)
  have hI : closeInsts (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
      (t.inputs.map (·.name)) (d.shape.insts.map (·.2.1)) children
      (closeMachine d.shape.layout t', d₀) = some (M, D) := by
    rcases hcc with ⟨-, hI⟩ | ⟨hfne, -, -⟩
    · exact hI
    · exact absurd hf0 hfne
  obtain ⟨hseq0, -, -⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨PI, ls, hin, hPI, _hlsL, _hndI, hinW, _hregs⟩ :=
    Tools.ShippingClosedPorts.closedPorts_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨hwnd, hwal, hinWt, P1, P2, hsp, hP2d, _hP2len, hP2ty⟩ :=
    Tools.ShippingTransitionPortTys.transitionPortTys_of_run d ok hbody hC hslots hdomB run
  have hls : P2 = ls := (List.append_inj' (hsp.symm.trans hin) (by omega)).2
  -- `NamesEq` (freeze §1): from `ran`'s own run, then names are allocator-only
  obtain ⟨ids₀, cache₀, hl₀, hmp⟩ := Tools.ShippingGen2.ranA_inputs_machPorts d ok hbody run
  have hNames : t.inputs.map (·.name) = (machPorts c ids cache d.shape.binders).map (·.name) := by
    rw [← hmp]
    exact Tools.ShippingGen2.machPorts_names_indep c cache₀ cache hl₀ hlen
  intro mn iname conns hst
  rw [hbody'] at hst
  rcases Tools.ShippingMachineInst.closeInsts_insts hI _ hst rfl with
    h0 | ⟨k, args, child, mc, hargs, _hchild, hmc, hcs⟩
  · exact Tools.ShippingChecksDerived.ff_absurd (List.all_eq_true.mp hseq0 _ h0)
  obtain ⟨outW, _argWs, outP, hmn, hout, houts, -, -, -, hconns, -⟩ :=
    Tools.ShippingOneOutClose.callStmt_parts hcs
  have hmcn : mc.name = child.1.name := Tools.ShippingMachineInst.moduleByName_name hmc
  have hfind : moduleByName D.modules mn = some mc := by
    rw [hmn, hmcn]
    exact hmc
  refine ⟨mc, hfind, ?_⟩
  intro p hp x hpc
  have hk : k < d.shape.insts.length := by
    have := (List.getElem?_eq_some_iff.mp hargs).1
    simpa using this
  -- the SAME statement's `CallStmt`, in the trace's port names
  have hcs' : Tools.ShippingMachineInst.CallStmt (machNIn d.shape) d.shape.insts.length
      d.shape.layout.slots.length ((machPorts c ids cache d.shape.binders).map (·.name)) k args mc
      (Stmt.inst mn iname conns) := by
    rw [← hNames]
    exact hcs
  -- the output port is THE output `outP`, and the wire it drives is the call's wire `outW`
  rw [houts] at hp
  have hpo : p = outP := List.mem_singleton.mp hp
  rw [hpo] at hpc
  have hxw : x = outW := by
    rcases hconns _ hpc with he | ⟨q', _hq', aw, _haw, he, hne⟩
    · exact Sparkle.IR.AST.Expr.ref.inj (Prod.mk.inj he).2
    · exact absurd (Prod.mk.inj he).1.symm hne
  rw [hxw]
  have hget := hout
  -- the call port: a transition input, of its binder's type (template :519-561, `e.1` := `k`)
  rw [List.getElem?_map] at hget
  cases hq : t.inputs[machNIn d.shape + k]? with
  | none =>
    rw [hq] at hget
    cases hget
  | some q =>
    rw [hq] at hget
    simp only [Option.map_some, Option.some.injEq] at hget
    have hqm : q ∈ t.inputs := List.mem_of_getElem? hq
    obtain ⟨hqw, hqz⟩ := hinW q hqm
    have hql : ls[k]? = some q := by
      have h1 : (PI ++ ls)[PI.length + k]? = some q := by
        rw [← hin, hPI]
        exact hq
      rw [List.getElem?_append_right (Nat.le_add_right _ _)] at h1
      have h2 : PI.length + k - PI.length = k := by omega
      rw [h2] at h1
      exact h1
    have hlt : k < (d.shape.binders.drop nDecl).length := by
      rw [← hP2d, hls]
      exact (List.getElem?_eq_some_iff.mp hql).1
    have hbn : (d.shape.binders.drop nDecl)[k]? = some (d.shape.binders.drop nDecl)[k] :=
      List.getElem?_eq_getElem hlt
    have hty : q.ty = kindTy ((d.shape.binders.drop nDecl)[k]).2 :=
      hP2ty k q _ (by rw [hls]; exact hql) hbn
    have hbn' : d.shape.binders[nDecl + k]? = some (d.shape.binders.drop nDecl)[k] := by
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
    exact ⟨k, hk, args, hargs, hcs', _, hbn', by rw [← hget, hdw, hty]⟩

set_option maxHeartbeats 4000000 in
/-- **`instOutWidthsOk` of a one-output parent** (freeze §4): `core_instOutWidthsOk_ranA` with `hkidW1` (the width of
the module of THE statement's call `k`, in the trace's port names) for `hkidW`. -/
theorem core_instOutWidthsOk_oneA
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    {c : Name} (d : Tools.ShippingMachineAuto.MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf0 : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged,
      x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {M b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    {ids : List FVarId} (hlen : ids.length = d.shape.binders.length)
    (cache : IO.Ref (ExprStructMap String))
    (hkidW1 : ∀ (k : Nat) (hk : k < d.shape.insts.length) (args : List Nat) (mc : Sparkle.IR.AST.Module)
        (st : Sparkle.IR.AST.Stmt),
      (d.shape.insts.map (·.2.1))[k]? = some args → st ∈ M.body →
      Tools.ShippingMachineInst.CallStmt (Tools.ShippingMachineEntry.machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
        ((Tools.ShippingMachineEntry.machPorts c ids cache d.shape.binders).map (·.name)) k args mc st →
      Sparkle.IR.Machine.moduleByName D.modules mc.name = some mc →
      ∀ outP ∈ mc.outputs, (d.shape.binders[nDecl + k]?).map
        (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) = some outP.ty.bitWidth) :
    Tools.ShippingHierOpen.instOutWidthsOk (Tools.ShippingMachineLinked.childMap D.modules)
      (Sparkle.IR.RegDedup.declWidth b) b.body = true := by
  have hcp := core_callPorts_oneA O d ok hbody hC hslots hdomB hins hf0 outTy hnomem hpost ran hlen cache
  have hbody' : b.body = M.body :=
    (Tools.ShippingParentTailsA.core_kids_facts_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran).2.1
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
  obtain ⟨k, hk, args, hargs, hcs, bn, hbn, hdw⟩ := hports p hp x hpc
  -- `st ∈ M.body` through `b.body = M.body`; the module by its own name
  have hstM : Stmt.inst mn iname conns ∈ M.body := by
    rw [← hbody']
    exact hst
  have hmod : moduleByName D.modules mc.name = some mc := by
    rw [Tools.ShippingMachineInst.moduleByName_name hfind]
    exact hfind
  have hw := hkidW1 k hk args mc (Stmt.inst mn iname conns) hargs hstM hcs hmod p hp
  rw [hbn] at hw
  have hwe : (kindTy bn.2).bitWidth = p.ty.bitWidth := by
    simpa only [Option.map_some, Option.some.injEq] using hw
  rw [hdw, hwe]

end Tools.ShippingGen2

/-! ## The local width fact and the top (ambient: Defs.lean:16-33, as Tools/ShippingGen2MemTop.lean) -/
namespace Tools.ShippingGen2
open Lean hiding Module Expr
open Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingQuadComposed (GenFacts)
open Tools.ShippingMachineShipsDepth (ResetNk)
open Tools.ShippingMachineCallsLinkedT (valsOf MemFacts)
open Tools.ShippingMachineChild (InRange boolsOf bitsOf)
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildCacheA (RealChildA JQC)
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain
open Tools.ShippingChildBndCore (cv dv)

variable {ι : Type} {dom : ι → DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The local width fact** (freeze §2): the module `mc` of THE statement `st`, served at THE call `k` (`Served1P` on the
trace's `ids`/`cache`), has its outputs of the width of call `k`'s binder. Steps: `Served1P` at `(k, st, mc)`; memory
origin excluded (`nomem_tag`); `ShipsRes` → `ChildShips` at `dsn := D`, `i0`; both `ChildRunN` branches give
`mc.outputs = outs.map …`; `CallStmt` gives `mc.outputs = [outP]`; `hW`. -/
theorem oneOutWidthAt (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw : Sparkle.IR.AST.Module} {D : Design} {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)}
    (hS : Served1P (ShipsRes L P) p.decl p.d.shape raw D ids cache)
    (hsimple : p.d.shape.instFields = [])
    (hnomem : ∀ x ∈ p.d.shape.instTagged,
      x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hW : ∀ k, OneOutWidth P p k) (i0 : ι)
    {k : Nat} (hk : k < p.d.shape.insts.length) {args : List Nat} {mc : Sparkle.IR.AST.Module} {st : Stmt}
    (hargs : (p.d.shape.insts.map (·.2.1))[k]? = some args) (hst : st ∈ raw.body)
    (hcs : Tools.ShippingMachineInst.CallStmt (machNIn p.d.shape) p.d.shape.insts.length
      p.d.shape.layout.slots.length ((machPorts p.decl ids cache p.d.shape.binders).map (·.name)) k args mc st)
    (hmod : moduleByName D.modules mc.name = some mc) :
    ∀ outP ∈ mc.outputs,
      (p.d.shape.binders[p.kD + k]?).map (fun bn => (kindTy bn.2).bitWidth) = some outP.ty.bitWidth := by
  intro outP hout
  -- step 1: `Served1P` at THIS `(k, args, mc, st)`
  rcases hS hsimple k hk args mc st hargs hst hcs hmod with ⟨md, hmd, _⟩ | ⟨Dc, hship, hDc⟩
  · -- step 2: a memory-origin instance is excluded by `hnomem`
    rw [Tools.ShippingChildInv.nomem_tag hnomem hk] at hmd
    cases hmd
  · -- step 3: the served result ships with `c`'s package `q`
    obtain ⟨_, ⟨q, n', hq, _, hCS⟩, _⟩ := hship
    -- step 4: its child run at `dsn := D`, `i0`; both branches start with the outputs
    have hmo : mc.outputs = q.d.shape.layout.outs.map (fun o => ({ name := o.name, ty := o.ty } : Port)) := by
      rcases hCS.2 D hDc hmod i0 with hr | hr
      · exact hr.1
      · exact hr.1
    -- step 5: `CallStmt`: the module has ONE output
    obtain ⟨_, _, outP', _, _, _, houts1, _⟩ := hcs
    rw [houts1] at hmo hout
    obtain ⟨o, hsing, hpo⟩ : ∃ o : OutField, q.d.shape.layout.outs = [o] ∧
        outP' = ({ name := o.name, ty := o.ty } : Port) := by
      cases hl : q.d.shape.layout.outs with
      | nil =>
        rw [hl] at hmo
        simp at hmo
      | cons o rest =>
        cases rest with
        | nil =>
          rw [hl] at hmo
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmo
          exact ⟨o, by simp [hl], hmo⟩
        | cons o2 rest2 =>
          rw [hl] at hmo
          simp at hmo
    have hpe : outP = outP' := List.mem_singleton.mp hout
    rw [hpe, hpo]
    -- step 6: `hW` at call `k`, package `q`, output `o`
    exact hW k hk q hq o hsing

/-- **`TopShips` of a one-output parent** (stage B; S4_CONSUMER_FREEZE:449-467 without `hBd`, STAGEB freeze §3-§5). -/
theorem oneOut_topShips (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hnomem : ∀ x ∈ p.d.shape.instTagged,
      x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl : p.d.shape.layout.slots ≠ [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hcore : RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref p.decl p.d.shape)
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hW : ∀ k, OneOutWidth P p k)
    (n : Nat) :
    TopShips p (n + 1) p.decl b raw D := by
  cases Classical.em (Nonempty ι) with
  | inr hne =>
    -- `ι` empty: `h`'s existing witness; `∀ i` is vacuous (freeze §3; `machine_ships_hierC_run` not called)
    obtain ⟨ids, nd, len, cache, regs, rnd, rlen, _⟩ := h
    unfold TopShips
    exact ⟨ids, nd, len, cache, regs, rnd, rlen, fun i => (hne ⟨i⟩).elim⟩
  | inl hne =>
  obtain ⟨i0⟩ := hne
  obtain ⟨hok, hco, hslots, houtTy, hdomB⟩ := hdata.rows
  have hkD := data_hkD p.d p.kD hok hco
  have hI := data_hI hdata
  have hIlen := data_hIlen p.d p.kD hok hco
  have hSL := data_hSL p.d hok
  have hSlen := data_hSlen p.d hok hslots
  have hLlen := data_hLlen p.d hok
  have hNIn := data_hNIn p.d p.kD hok hco hslots
  have ranA := Tools.ShippingRanABridge.machineRanA_of_runJQC L.O hA L.T ran
  -- `kidsCombB` of the run, checked by its one-output closing (as `oneOut_composedNW`)
  obtain ⟨_, _, _, _, _, _, _, _, hcl, _⟩ :=
    Tools.ShippingParentDesignA.core_closeInstsA L.O p.d hins hsimple ranA
  have hkc : kidsCombB D.modules raw.body = true := Tools.ShippingChildServe.closeInsts_kidsComb hcl
  -- the trace's witness: `ids`, `cache` and the served evidence (the SAME `h`)
  obtain ⟨ids, _, len, cache, _, _, _, _, _, _, hx, _⟩ := id h
  -- `RunFacts` (freeze §4 "Use"): `wid` from the local width fact at `i0`
  have factsB : ∀ {b' : Sparkle.IR.AST.Module}, (b' = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b' = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b' := fun hpb =>
    { gate := (Tools.ShippingParentDesignA.core_runFactsHA L.O p.d hok (Pkg.body_eq p) hco hslots hdomB hins hsimple
        houtTy hnomem hpb ranA hsl).gate
      wfB := Tools.ShippingParentTailsA.core_linkedWF_ranA L.O p.d hok (Pkg.body_eq p) hco hslots hdomB hins houtTy
        hnomem hpb ranA
      ndB := (Tools.ShippingParentDesignA.core_runFactsHA L.O p.d hok (Pkg.body_eq p) hco hslots hdomB hins hsimple
        houtTy hnomem hpb ranA hsl).ndB
      self := (Tools.ShippingParentDesignA.core_runFactsHA L.O p.d hok (Pkg.body_eq p) hco hslots hdomB hins hsimple
        houtTy hnomem hpb ranA hsl).self
      outs := (Tools.ShippingParentDesignA.core_runFactsHA L.O p.d hok (Pkg.body_eq p) hco hslots hdomB hins hsimple
        houtTy hnomem hpb ranA hsl).outs
      rst := (Tools.ShippingParentDesignA.core_runFactsHA L.O p.d hok (Pkg.body_eq p) hco hslots hdomB hins hsimple
        houtTy hnomem hpb ranA hsl).rst
      wid := core_instOutWidthsOk_oneA L.O p.d hok (Pkg.body_eq p) (nDecl := p.kD) hco hslots hdomB hins hsimple
        houtTy hnomem hpb ranA len cache
        (fun _ hk _ _ _ hargs hst hcs hmod =>
          oneOutWidthAt L P p hx.2 hsimple hnomem hW i0 hk hargs hst hcs hmod) }
  -- the run-local fit chain (FitChain): `ComposedHBF` → `ComposedNWF` at height `n + 1`
  have hNWF := Tools.ShippingGen2Fit.composedNWn_of_HBF (n + 1) (R := fun _ _ => True)
    (machine_linked_callsServed1F L P p h hsimple hkD hI hIlen hSL hSlen hLlen hNIn hkc hdec hW)
    (by unfold Tools.ShippingMachineDepthH.BoundH; intros; trivial)
    (Tools.ShippingMachineDepthHR.kidsComb_of_B hkc)
  let Bnd : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx' mref' cctx' cref' w' m' D' =>
    mctx' = mctx ∧ mref' = mref ∧ cctx' = cctx ∧ cref' = cref ∧ w' = w ∧ m' = raw ∧ D' = D
  have key := Tools.ShippingSrm33.machine_ships_hierC_run (n := n + 1)
    (fun D' => Tools.ShippingHierStateG.KSn_local _ _) Bnd (fun _ _ _ _ => True)
    p.d (kD := p.kD) (src := p.src) (ext := p.extS) (extB := p.extBS)
    (lsrc := p.lsrc) (srcL := p.src) (extL := p.extS) (extBL := p.extBS)
    (fun {mctx'} {mref'} {cctx'} {cref'} {w'} {w''} {m'} {design'} _ _ _ hB => by
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hB
      exact (Pkg.trace L.O L.T hA p ran).toLB)
    (fun {mctx'} {mref'} {cctx'} {cref'} {w'} {w''} {m'} {design'} {b'} _ hpb _ _ hB _ => by
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hB
      refine Tools.ShippingGen2Fit.composedNWRegsF_of_composedNWF _ hNWF ?_
      intro _ _ _ _ _ _ hWr
      exact Tools.ShippingSrm32.hWd_of_wired hpb (factsB hpb).gate houtTy hWr)
    houtTy (Tools.ShippingC4InitW.hinitW_of_ok p.d hok) hcore hpost entry trivial (fun _ => factsB hpost)
  -- R-G: `key` has the consumer-1 (old) premises; L2 with both memberships from the run (U-TOP-CLKIN)
  obtain ⟨_, _, _, _, _, _, _, _, _, wired, _, _⟩ := id h
  exact topShips_ofOld_wired p (n + 1) wired hsl hpost (key ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

end Tools.ShippingGen2
