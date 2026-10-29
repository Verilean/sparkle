import Tools.ShippingGen2OneOutTop
set_option autoImplicit false
-- Built: g3dsc-1b840215 (clean snapshot, exit 0, standard axioms).
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # U-ARGW-PARENT: the argument-wire widths of a parent's calls (DPORT L2)
(scripts/gen3/UARGW_PARENT_SURVEY.md, approved as a scoped design; issue `sparkle-gen3-uargw-parent`)

* `core_inputWidth_A` (survey §2, route §3): every transition input wire of a closed machine run, named in the trace's
  port names, has its binder's declared width in the post-processed module `b`. The proof is `core_callPorts_oneA`
  (Tools/ShippingGen2OneOutTop.lean:51-196) steps o2-o4, o7-o10, o15-o19 at index `e` (survey §1), verbatim up to the
  index; steps o1, o5, o6, o11-o14 are dropped.
* `argWidth_of_mapM` (the shared `mapM` lemma): from any such width fact, every element `argWs[j]` of a successful
  argument `mapM` over the same names gets the width of binder `nDecl + (kI + (n + args[j]))` (the index form of
  `callArgsOkAt`, Adapt:76).
* `core_callArgPorts_oneA` / `core_callArgPorts_ranA`: thin corollaries (the core, then the shared lemma).

**Scope.** The core is CONDITIONAL on `hins`, `ok`, `hbody`, `hC`, `hslots`, `hdomB`, `hpost` and `ran` (the run).
"No instance" means only that no individual call witness (statement, child, output port, real-child fact) is used. The
`CallStmt`/`CallStmtG` premise of the two corollaries is carried for the consumer (the later PortTie composition) and is
NOT used by the proof (only the `mapM` is). No `hf0`/`hfne`. The optional conns lemma L-AW is not built (no use site
yet). This file alone supplies nothing for `callArgsOkAt`: it is the PARENT side; UCHILD_PORTTYS_TABLE.md supplies the
child side, UARITY_FREEZE.md the matching index range, and only composed with SRC-ARGW's width equality for the SAME call
do they reach `callArgsOkAt`.

**AUDIT.** Expected types: Tests/Gen3/ArgWidthCheck.lean (mechanical, with mutants). No reference to the real-child
predicate (ChildCacheA), the group run lemma (ParentRunFactsA:410) or the closing's instance lemma (MachineInst:295) in
this file (grep for their names finds nothing). Axioms: standard only (checked there). -/

namespace Tools.ShippingGen3ArgWidth
-- the opens of Tools/ShippingGen2OneOutTop.lean:26-45, verbatim
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
/-- **(W) Every transition input wire of a closed machine run has its binder's declared width in `b`.** No instance,
no parent kind, no child. -/
theorem core_inputWidth_A {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true) (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    {ids : List FVarId} (hlen : ids.length = d.shape.binders.length) (cache : IO.Ref (ExprStructMap String)) :
    ∀ (e : Nat) (w : String),
      ((machPorts c ids cache d.shape.binders).map (·.name))[machNIn d.shape + e]? = some w →
      ∃ bn, d.shape.binders[nDecl + e]? = some bn ∧
        Sparkle.IR.RegDedup.declWidth b w = (kindTy bn.2).bitWidth := by
  -- o2/o3: the cleanup and the checked merge keep the non-zero wires and add none (template :78-91, verbatim)
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
  -- o4: the run; `hins` kills the call-free branch; `hMw` from the branch-independent `hcc.some`
  have ran0 := ran
  obtain ⟨_, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ran0
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, -⟩
  · exact absurd hno hins
  obtain ⟨hMw, -⟩ := hcc.some
  -- o7-o9 (template :106-110, verbatim)
  obtain ⟨PI, ls, hin, hPI, _hlsL, _hndI, hinW, _hregs⟩ :=
    Tools.ShippingClosedPorts.closedPorts_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨hwnd, hwal, hinWt, P1, P2, hsp, hP2d, _hP2len, hP2ty⟩ :=
    Tools.ShippingTransitionPortTys.transitionPortTys_of_run d ok hbody hC hslots hdomB run
  have hls : P2 = ls := (List.append_inj' (hsp.symm.trans hin) (by omega)).2
  -- o10: `NamesEq` (template :112-115, verbatim)
  obtain ⟨ids₀, cache₀, hl₀, hmp⟩ := Tools.ShippingGen2.ranA_inputs_machPorts d ok hbody run
  have hNames : t.inputs.map (·.name) = (machPorts c ids cache d.shape.binders).map (·.name) := by
    rw [← hmp]
    exact Tools.ShippingGen2.machPorts_names_indep c cache₀ cache hl₀ hlen
  intro e w hw
  -- o15-o19 at index `e` (template :147-192, `k` := `e`)
  have hget : (t.inputs.map (·.name))[machNIn d.shape + e]? = some w := by
    rw [hNames]
    exact hw
  rw [List.getElem?_map] at hget
  cases hq : t.inputs[machNIn d.shape + e]? with
  | none =>
    rw [hq] at hget
    cases hget
  | some q =>
    rw [hq] at hget
    simp only [Option.map_some, Option.some.injEq] at hget
    have hqm : q ∈ t.inputs := List.mem_of_getElem? hq
    obtain ⟨hqw, hqz⟩ := hinW q hqm
    have hql : ls[e]? = some q := by
      have h1 : (PI ++ ls)[PI.length + e]? = some q := by
        rw [← hin, hPI]
        exact hq
      rw [List.getElem?_append_right (Nat.le_add_right _ _)] at h1
      have h2 : PI.length + e - PI.length = e := by omega
      rw [h2] at h1
      exact h1
    have hlt : e < (d.shape.binders.drop nDecl).length := by
      rw [← hP2d, hls]
      exact (List.getElem?_eq_some_iff.mp hql).1
    have hbn : (d.shape.binders.drop nDecl)[e]? = some (d.shape.binders.drop nDecl)[e] :=
      List.getElem?_eq_getElem hlt
    have hty : q.ty = kindTy ((d.shape.binders.drop nDecl)[e]).2 :=
      hP2ty e q _ (by rw [hls]; exact hql) hbn
    have hbn' : d.shape.binders[nDecl + e]? = some (d.shape.binders.drop nDecl)[e] := by
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
    exact ⟨_, hbn', by rw [← hget, hdw, hty]⟩

/-- **The shared `mapM` lemma.** If every transition input `names[nIn + e]` has the width of binder `nDecl + e`, then
every element of a successful argument `mapM` (`CallStmt` MachineInst:193, `CallStmtG` MachineInstG:23) has the width
of binder `nDecl + (kI + (n + a))` of its argument let `a`. -/
theorem argWidth_of_mapM {names : List String} {nIn kI n nDecl : Nat}
    {binders : List (Name × MixedGateBinder)} {b : Sparkle.IR.AST.Module}
    (hW : ∀ (e : Nat) (w : String), names[nIn + e]? = some w →
      ∃ bn, binders[nDecl + e]? = some bn ∧ Sparkle.IR.RegDedup.declWidth b w = (kindTy bn.2).bitWidth)
    {args : List Nat} {argWs : List String}
    (hm : args.mapM (fun j => names[nIn + kI + n + j]?) = some argWs) :
    ∀ (j a : Nat) (w : String), args[j]? = some a → argWs[j]? = some w →
      ∃ bn, binders[nDecl + (kI + (n + a))]? = some bn ∧
        Sparkle.IR.RegDedup.declWidth b w = (kindTy bn.2).bitWidth := by
  intro j a w ha hw
  obtain ⟨-, hgetW⟩ := Tools.ShippingMachineInst.mapM_some _ _ _ hm
  obtain ⟨hj, haj⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨y, hy, hyr⟩ := hgetW j hj
  have hy' : names[nIn + kI + n + args[j]]? = some y := hy
  have hyw : y = w := Option.some.inj (hyr.symm.trans hw)
  rw [hyw] at hy'
  rw [← haj]
  have h2 : names[nIn + (kI + (n + args[j]))]? = some w := by
    rw [show nIn + (kI + (n + args[j])) = nIn + kI + n + args[j] by omega]
    exact hy'
  exact hW (kI + (n + args[j])) w h2

/-- **(L2, one-output parent)** every argument wire of a call's `CallStmt` (trace names). -/
theorem core_callArgPorts_oneA {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true) (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    {ids : List FVarId} (hlen : ids.length = d.shape.binders.length) (cache : IO.Ref (ExprStructMap String)) :
    ∀ (k : Nat) (args : List Nat) (mc : Sparkle.IR.AST.Module) (st : Stmt),
      Tools.ShippingMachineInst.CallStmt (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
        ((machPorts c ids cache d.shape.binders).map (·.name)) k args mc st →
      ∀ (argWs : List String),
        args.mapM (fun j => ((machPorts c ids cache d.shape.binders).map (·.name))[machNIn d.shape +
          d.shape.insts.length + d.shape.layout.slots.length + j]?) = some argWs →
        ∀ (j a : Nat) (w : String), args[j]? = some a → argWs[j]? = some w →
          ∃ bn, d.shape.binders[nDecl + (d.shape.insts.length + (d.shape.layout.slots.length + a))]? = some bn ∧
            Sparkle.IR.RegDedup.declWidth b w = (kindTy bn.2).bitWidth := by
  intro _k args _mc _st _hcs argWs hm
  exact argWidth_of_mapM (core_inputWidth_A O d ok hbody hC hslots hdomB hins hpost ran hlen cache) hm

/-- **(L2, group parent)** the same for a group statement `CallStmtG`. -/
theorem core_callArgPorts_ranA {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true) (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    {ids : List FVarId} (hlen : ids.length = d.shape.binders.length) (cache : IO.Ref (ExprStructMap String)) :
    ∀ (args : List Nat) (outs : List (Nat × String)) (mc : Sparkle.IR.AST.Module) (st : Stmt),
      Tools.ShippingMachineInstG.CallStmtG (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
        ((machPorts c ids cache d.shape.binders).map (·.name)) args outs mc st →
      ∀ (argWs : List String),
        args.mapM (fun j => ((machPorts c ids cache d.shape.binders).map (·.name))[machNIn d.shape +
          d.shape.insts.length + d.shape.layout.slots.length + j]?) = some argWs →
        ∀ (j a : Nat) (w : String), args[j]? = some a → argWs[j]? = some w →
          ∃ bn, d.shape.binders[nDecl + (d.shape.insts.length + (d.shape.layout.slots.length + a))]? = some bn ∧
            Sparkle.IR.RegDedup.declWidth b w = (kindTy bn.2).bitWidth := by
  intro args _outs _mc _st _hcs argWs hm
  exact argWidth_of_mapM (core_inputWidth_A O d ok hbody hC hslots hdomB hins hpost ran hlen cache) hm

end Tools.ShippingGen3ArgWidth
