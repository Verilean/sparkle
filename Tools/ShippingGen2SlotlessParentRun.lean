import Tools.ShippingGen2SlotlessParent
import Tools.ShippingGen2GroupServed
import Tools.ShippingGen2SlotlessClosed
import Tools.ShippingClosedTransitionTyped
import Tools.ShippingPortWidthsPure
import Tools.ShippingTransitionPortTys
import Tools.ShippingCallsAssemblyG
set_option autoImplicit false
-- WRITTEN, NOT BUILT (2026-10-29). To be confirmed by
-- `kjob lake build Tools.ShippingGen2SlotlessParentRun` (scripts/gen2/S5_SLOTLESS_FREEZE.md §9), after
-- `Tools.ShippingGen2SlotlessParent`.

/-! # S5 stage B: the run-level supplier and `ChildShips` of slotless parents (S5_SLOTLESS_FREEZE.md rev0 §4)

* B1 `slotlessParent_noTouch_ofRun`: from the ONE run `ran` (A boundary) and the module's actual inputs
  (`hrst : "rst" ∉ raw.inputs…`), `NoTouchZ ["rst", "clk"] raw.body`. Proof chain:
  - the trace of THIS run (`Pkg.trace`) gives the wiring: allocated port names (`MachineWired` clause 2), no
    assignment to `"rst"`/`"clk"` (MachineEntry:729), and, for one-output parents, every instance a `CallStmt` over
    those names (clause 6);
  - `machineRanA_of_runJQC` (RanABridge:38) gives the closing (`CloseCalls`): the body is a permutation of
    `closeMachine lay t'`'s body and instance statements (`CloseCalls.some`);
  - `transition_closed` (TransitionClosed:35), `closeLets_closed` (SlotlessClosed:91) and
    `closeMachine_slotless_closed` (:200): `closeMachine lay t'` is read-closed over its inputs, assignments only;
    its inputs are allocated (`closedTransition_of_run`, `closeMachine_inputs`, as SlotlessLeaf:397-420). So an
    assignment reads neither `"rst"` nor `"clk"` (an input would be allocated; a written name is an assignment's
    target, none of which is `"rst"`/`"clk"`);
  - group parents (`closeInstsG`): every instance is a `CallStmtG` of a child `cy ∈ children`
    (`closeInstsG_insts`, `closeInstsG_names`) over the transition's input names (allocated,
    `transitionPortTys_of_run`). If `cy` had a clock/reset input, `withClockFor` would give the parent a `"rst"`
    input (`withClockFor_clk`, `closeInstsG_inputs`; the call ports are allocated): contradicting `hrst`. So the
    instance has no clock/reset connection, and every `.ref` wire is allocated.
  The reset absence comes from the module's ACTUAL inputs (`hrst`), never from a premise on children (no `SeqKid`).
* B2 `oneOutSl_childShips`: `oneOut_childShips` (OneOut:288-331), `hsl` → `hsl0`, last line A3 ∘ B1.
* B3 `groupSl_childShips`: `group_childShips` (GroupServed:294-341), the same two changes. -/
namespace Tools.ShippingGen2
-- GroupServed:247-266 verbatim (Connect.lean:14-34)
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
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

open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingChildInv (Res)
open Tools.ShippingChildBndCore (cv dv)
-- stage A
open Tools.ShippingGen2SlotlessParent (NoTouchZ allocated_notZ)

variable {ι : Type} {dom : ι → DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## Small pure facts -/

/-- A read of a read-closed body is a name of `S` or a name the body writes. -/
theorem slp_readsClosedB_mem : ∀ (body : List Stmt) (S : List String), readsClosedB S body = true →
    ∀ s ∈ body, ∀ n ∈ Sparkle.IR.Reorder.stmtReads s, n ∈ S ∨ n ∈ Sparkle.IR.Reorder.writesOf body
  | [], _, _, _, hs, _, _ => absurd hs List.not_mem_nil
  | st :: rest, S, h, s, hs, n, hn => by
    simp only [readsClosedB, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hhead, htail⟩ := h
    rcases List.mem_cons.mp hs with rfl | hs'
    · exact Or.inl (List.contains_iff_mem.mp (hhead n hn))
    · rcases slp_readsClosedB_mem rest (S ++ Sparkle.IR.Reorder.stmtWrites st) htail s hs' n hn with h1 | h1
      · rcases List.mem_append.mp h1 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (slc_mem_writes List.mem_cons_self h2)
      · obtain ⟨st', hst', hn'⟩ := slc_of_mem_writes h1
        exact Or.inr (slc_mem_writes (List.mem_cons_of_mem _ hst') hn')

/-- Every value an `Option` `mapM` returns is one of its function's values. -/
theorem slp_mapM_mem' {β : Type} {S : List String} {g : β → Option String} (hg : ∀ x y, g x = some y → y ∈ S) :
    ∀ (l : List β) (ws : List String), l.mapM g = some ws → ∀ w ∈ ws, w ∈ S
  | [], ws, h, w, hw => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact absurd hw List.not_mem_nil
  | x :: xs, ws, h, w, hw => by
    simp only [List.mapM_cons, bind, Option.bind_eq_bind] at h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ys, hys, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [pure, Option.some.injEq] at h
    subst h
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact hg x _ hy
    · exact slp_mapM_mem' hg xs ys hys w hw'

theorem slp_mapM_mem {β : Type} {S : List String} {g : β → Option String} {l : List β} {ws : List String}
    (h : l.mapM g = some ws) (hg : ∀ x y, g x = some y → y ∈ S) : ∀ w ∈ ws, w ∈ S :=
  slp_mapM_mem' hg l ws h

/-! ## B1 -/

set_option maxHeartbeats 4000000 in
/-- **B1: a slotless parent without a reset input touches neither the reset nor the clock**, from its run. -/
theorem slotlessParent_noTouch_ofRun (L : Laws mref cref) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hins : p.d.shape.insts ≠ []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hrst : "rst" ∉ raw.inputs.map (·.name)) :
    NoTouchZ ["rst", "clk"] raw.body := by
  obtain ⟨hok, hco, hslots, -, hdomB⟩ := hdata.rows
  -- the wiring of THIS run, from its trace (SlotlessClosed:322-324)
  have hL := (Pkg.trace L.O L.T hA p ran).toLB
  obtain ⟨_, _, _, _, _, _, _, _, _, wired, _⟩ := id hL
  obtain ⟨-, halloc, -, -, -, hinst1, -, -, -, -, -, -, -, -, noRC, -⟩ := wired
  -- the closing of THIS run
  have ranA := Tools.ShippingRanABridge.machineRanA_of_runJQC L.O hA L.T ran
  obtain ⟨_, _, _, _, _, t, t', d₀, run, hcl, hmt⟩ := ranA
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, -⟩
  · exact absurd hno hins
  obtain ⟨-, -, -, L0, hL0, hperm, -⟩ := Tools.ShippingMachineEntry.CloseCalls.some hcc
  -- the closed machine: read-closed over its inputs, assignments only (SlotlessClosed:327-368, steps 3-5)
  have ok := Pkg.ok p
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨_, _, positive, _, _, _, _, _, hwf, hb, hv,
    _, _, _, _, _, _, _, _, _, _, _⟩ := ok
  have hposv : Tools.ShippingMixedEntrySoundness.PositiveBinders p.d.shape.binders := by
    intro name n hmem
    have := List.all_eq_true.mp positive _ hmem
    simpa using this
  have hb' : ∀ j, j < p.d.kb → ∃ name, p.d.shape.binders[p.d.bpos j]? = some (name, .bool) := by
    intro j hj
    have := hb j hj
    cases h : p.d.shape.binders[p.d.bpos j]? with
    | none => rw [h] at this; cases this
    | some pr =>
      obtain ⟨name, k⟩ := pr
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have hv' : ∀ j, j < p.d.kv → ∃ name,
      p.d.shape.binders[p.d.vpos j]? = some (name, .bits (p.d.vw j)) := by
    intro j hj
    have := hv j hj
    cases h : p.d.shape.binders[p.d.vpos j]? with
    | none => rw [h] at this; cases this
    | some pr =>
      obtain ⟨name, k⟩ := pr
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  obtain ⟨ids', cache', returned, st, nd, len, hrun, hm, _, nameLegal⟩ :=
    Tools.ShippingMixedEntrySoundness.synthesizeMixedCertified_returns run
  obtain ⟨hclosed, hassign, -, -, -, -⟩ :=
    Tools.ShippingTransitionClosed.transition_closed nd len hrun hm nameLegal hposv p.d.packed hwf hb' hv'
      (Pkg.body_eq p)
  obtain ⟨h1, h2⟩ := closeLets_closed hcl hclosed hassign
  obtain ⟨hMc, hMa⟩ := closeMachine_slotless_closed (lay := p.d.shape.layout) hsl0 h1 h2
  -- its inputs are allocated (SlotlessLeaf:410-420)
  obtain ⟨Bc, coreW, hbodyc, _, _, namesc, inWc, _⟩ :=
    Tools.ShippingClosedTransitionTyped.closedTransition_of_run p.d hok (Pkg.body_eq p) hco hslots hdomB run hcl
  obtain ⟨hcm0, _⟩ :=
    Tools.ShippingPortWidthsPure.closeMachine_inputs (t := t') (lay := p.d.shape.layout) hbodyc
  have hE : p.d.shape.layout.slots.isEmpty = true := by simp [hsl0]
  have hMalloc : ∀ q ∈ (closeMachine p.d.shape.layout t').inputs, Sparkle.IR.NameHints.Allocated q.name := by
    intro q hq
    rw [hcm0 hE] at hq
    exact namesc q (inWc q (List.mem_of_mem_take hq))
  -- the closed machine's statements are the module's; no assignment targets the reset or the clock
  have hMsub : ∀ s ∈ (closeMachine p.d.shape.layout t').body, s ∈ raw.body :=
    fun s hs => hperm.mem_iff.mp (List.mem_append_left _ hs)
  have hnoW : ∀ z ∈ ["rst", "clk"], ∀ l r, Stmt.assign l r ∈ raw.body → l ≠ z := by
    intro z hz l r hmem hlz
    subst hlz
    rcases List.mem_cons.mp hz with h | h
    · subst h; exact (noRC r).1 hmem
    · rw [List.mem_singleton.mp h] at hmem; exact (noRC r).2 hmem
  intro s hs
  rcases List.mem_append.mp (hperm.mem_iff.mpr hs) with hsM | hsL
  · -- an assignment (of the closed machine)
    left
    obtain ⟨l, r, rfl⟩ := hMa s hsM
    refine ⟨l, r, rfl, fun hl => hnoW l hl l r hs rfl, fun z hz hzr => ?_⟩
    rcases slp_readsClosedB_mem _ _ hMc _ hsM z hzr with hin | hwr
    · obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hin
      exact allocated_notZ (Eq.mp (congrArg Sparkle.IR.NameHints.Allocated hqn) (hMalloc q hq)) hz
    · obtain ⟨s', hs'M, hzs'⟩ := slc_of_mem_writes hwr
      obtain ⟨l', r', rfl⟩ := hMa s' hs'M
      have hzl : z = l' := by simpa [Sparkle.IR.Reorder.stmtWrites] using hzs'
      exact hnoW z hz l' r' (hMsub _ hs'M) hzl.symm
  · -- an instance statement of the closing
    right
    have hIi : Sparkle.IR.Machine.isInst s = true := List.all_eq_true.mp hL0 s hsL
    obtain ⟨mn, iname, conns, rfl⟩ : ∃ mn iname conns, s = Stmt.inst mn iname conns := by
      cases s <;> first | exact ⟨_, _, _, rfl⟩ | simp [Sparkle.IR.Machine.isInst] at hIi
    refine ⟨mn, iname, conns, rfl, fun cn hcn wv hcw hwZ => ?_⟩
    by_cases hfe : p.d.shape.instFields = []
    · -- one-output (`closeInsts`): a `CallStmt` over the wiring's (allocated) names
      obtain ⟨k, args, mc, -, -, hcs⟩ := hinst1 hfe mn iname conns hs
      obtain ⟨outW, argWs, outP, iname', hout, hargs, -, -, -, -, -, -, -, heq⟩ := hcs
      injection heq with e1 e2 e3
      subst e3
      rcases List.mem_append.mp hcn with hc1 | hc1
      · obtain ⟨⟨q, w'⟩, hqw, rfl⟩ := List.mem_map.mp hc1
        have hw' : w' = wv := by simpa using hcw
        subst hw'
        exact allocated_notZ (halloc _ (slp_mapM_mem hargs (fun _ _ h => List.mem_of_getElem? h) _
          (List.of_mem_zip hqw).2)) hwZ
      · rw [List.mem_singleton] at hc1
        subst hc1
        have hw' : outW = wv := by simpa using hcw
        subst hw'
        exact allocated_notZ (halloc _ (List.mem_of_getElem? hout)) hwZ
    · -- group (`closeInstsG`): a `CallStmtG` of a child of the closing over the transition's input names
      rcases hcc with ⟨hf0, -⟩ | ⟨-, hG, -⟩
      · exact absurd hf0 hfe
      obtain ⟨-, hwalloc, hinW, -⟩ :=
        Tools.ShippingTransitionPortTys.transitionPortTys_of_run p.d hok (Pkg.body_eq p) hco hslots hdomB run
      have tAlloc : ∀ x ∈ t.inputs.map (·.name), Sparkle.IR.NameHints.Allocated x := by
        intro x hx
        obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hx
        exact Eq.mp (congrArg Sparkle.IR.NameHints.Allocated hqx) (hwalloc q (hinW q hq))
      rcases Tools.ShippingMachineInstG.closeInstsG_insts hG _ hs rfl with
        hM0 | ⟨args, outs, child, mc, hcs, hmc, houts, hent⟩
      · obtain ⟨l, r, heq⟩ := hMa _ hM0
        cases heq
      obtain ⟨outWs, argWs, iname', houtW, hargW, -, -, -, -, -, -, -, -, -, heq⟩ := hcs
      obtain ⟨e, he⟩ : ∃ e, e ∈ outs := by
        cases outs with
        | nil => exact absurd rfl houts
        | cons e _ => exact ⟨e, List.mem_cons_self⟩
      obtain ⟨-, hch, -⟩ := hent e he
      cases hcy : children[e.1]? with
      | none => rw [hcy] at hch; simp at hch
      | some cy =>
        rw [hcy, Option.map_some, Option.some.injEq] at hch
        have hcym : cy ∈ children := List.mem_of_getElem? hcy
        -- the instance's module IS that child (`closeInstsG_names`)
        have hmcy : mc = cy.1 := by
          have h1 := ((Tools.ShippingMachineInstG.closeInstsG_names hG).2.2.2 cy hcym).1
          rw [hch, hmc] at h1
          exact Option.some.inj h1
        subst hmcy
        -- the child has no clock/reset input: otherwise the parent would have a reset input (`withClockFor`)
        have hns : Tools.ShippingInstStmtG.isSeqChild cy.1 = false := by
          cases hsq : Tools.ShippingInstStmtG.isSeqChild cy.1 with
          | false => rfl
          | true =>
            exfalso
            apply hrst
            obtain ⟨-, pr, hpr, hprn⟩ :=
              Tools.ShippingCallsAssemblyG.withClockFor_clk (m := closeMachine p.d.shape.layout t') hcym hsq
            obtain ⟨outWs0, hmap, hMin⟩ := Tools.ShippingMachineInstG.closeInstsG_inputs hG
            have hkeep : (!outWs0.contains pr.name) = true := by
              rw [hprn]
              cases hc0 : outWs0.contains "rst" with
              | false => rfl
              | true =>
                exfalso
                exact Tools.ShippingRegisterSoundness.not_allocated_rst
                  (tAlloc _ (slp_mapM_mem hmap (fun _ _ h => List.mem_of_getElem? h) _
                    (List.contains_iff_mem.mp hc0)))
            rw [hMin]
            exact List.mem_map.mpr ⟨pr, List.mem_filter.mpr ⟨hpr, hkeep⟩, hprn⟩
        have hany : cy.1.inputs.any (fun p => p.name == "clk" || p.name == "rst") = false := hns
        injection heq with e1 e2 e3
        subst e3
        rw [hany] at hcn
        simp only [Bool.false_eq_true, if_false, List.append_nil] at hcn
        rcases List.mem_append.mp hcn with hc1 | hc1
        · obtain ⟨⟨q, w'⟩, hqw, rfl⟩ := List.mem_map.mp hc1
          have hw' : w' = wv := by simpa using hcw
          subst hw'
          exact allocated_notZ (tAlloc _ (slp_mapM_mem hargW (fun _ _ h => List.mem_of_getElem? h) _
            (List.of_mem_zip hqw).2)) hwZ
        · obtain ⟨⟨f, w'⟩, hfw, rfl⟩ := List.mem_map.mp hc1
          have hw' : w' = wv := by simpa using hcw
          subst hw'
          exact allocated_notZ (tAlloc _ (slp_mapM_mem houtW
            (fun x y h => by obtain ⟨k, f⟩ := x; exact List.mem_of_getElem? h) _
            (List.of_mem_zip hfw).2)) hwZ

/-! ## B2, B3 -/

/-- **B2: a one-output slotless parent ships as a child at `n + 1`** (`oneOut_childShips`, OneOut:288-331, with
`hsl` → `hsl0` and the last line A3 ∘ B1). -/
theorem oneOutSl_childShips (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hext : ExtInS p)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (n : Nat) :
    ChildShips p (n + 1) b D := by
  obtain ⟨hok, hco, hslots, houtTy, -⟩ := hdata.rows
  have hkD := data_hkD p.d p.kD hok hco
  have hIlen := data_hIlen p.d p.kD hok hco
  have hSL := data_hSL p.d hok
  have hSlen := data_hSlen p.d hok hslots
  have hLlen := data_hLlen p.d hok
  have hNIn := data_hNIn p.d p.kD hok hco hslots
  have hNW := oneOut_composedNW L P p hdata hins hsimple hA ran hdec h n
  have ranA := Tools.ShippingRanABridge.machineRanA_of_runJQC L.O hA L.T ran
  -- no self-instantiation, from the run's one-output closing (`closeInsts_acyclic`)
  have acyc : Tools.ShippingHierMono.NoInstOf raw.name raw.body ∧
      ∀ g ∈ D.modules, Tools.ShippingHierMono.NoInstOf raw.name g.body := by
    obtain ⟨_, _, _, _, _, _, _, _, hcl, _⟩ :=
      Tools.ShippingParentDesignA.core_closeInstsA L.O p.d hins hsimple ranA
    obtain ⟨_, h1, h2, _⟩ := Tools.ShippingChildServe.closeInsts_acyclic hcl
    exact ⟨h1, h2⟩
  have hI0 : 0 < p.d.shape.insts.length := by
    cases h : p.d.shape.insts with
    | nil => exact absurd h hins
    | cons _ _ => simp
  intro dsn hcons _ i
  have hEA : Tools.ShippingHierMono.ExtendsAway raw.name (childMap D.modules) (childMap dsn.modules) := by
    refine ⟨?_, ?_⟩
    · intro x r _ hD
      obtain ⟨g, hg, rfl⟩ := Tools.ShippingMachineDepthRun.childMap_some.mp hD
      have hm := Tools.ShippingHierPremisesBase.moduleByName_mem hg
      exact Tools.ShippingMachineDepthRun.childMap_some.mpr ⟨g, by rw [← hm.2]; exact hcons g hm.1, rfl⟩
    · intro x r hD
      obtain ⟨g, hg, rfl⟩ := Tools.ShippingMachineDepthRun.childMap_some.mp hD
      exact acyc.2 g (Tools.ShippingHierPremisesBase.moduleByName_mem hg).1
  exact Tools.ShippingGen2SlotlessParent.childRunN_of_composedNW_runSl n houtTy (ok_outNameOk p.d hok) hsl0 hI0
    hkD hIlen hSL hSlen hLlen hNIn hext.1 hext.2 i hNW hpost hEA acyc.1
    (slotlessParent_noTouch_ofRun L p hdata hins hsl0 hA ran)

/-- **B3: a group slotless parent ships as a child at `n + 1`** (`group_childShips`, GroupServed:294-341, with
`hsl` → `hsl0` and the last line A3 ∘ B1). -/
theorem groupSl_childShips (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hext : ExtInS p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (n : Nat)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsAt L P n) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc) :
    ChildShips p (n + 1) b D := by
  obtain ⟨hok, hco, hslots, houtTy, -⟩ := hdata.rows
  have hkD := data_hkD p.d p.kD hok hco
  have hIlen := data_hIlen p.d p.kD hok hco
  have hSL := data_hSL p.d hok
  have hSlen := data_hSlen p.d hok hslots
  have hLlen := data_hLlen p.d hok
  have hNIn := data_hNIn p.d p.kD hok hco hslots
  have hNW := group_composedNW L P p hdata hfe hdec n h
  have ranA := Tools.ShippingRanABridge.machineRanA_of_runJQC L.O hA L.T ran
  -- no self-instantiation, from the run's group closing (GroupServed:316-325 verbatim)
  have acyc : Tools.ShippingHierMono.NoInstOf raw.name raw.body ∧
      ∀ g ∈ D.modules, Tools.ShippingHierMono.NoInstOf raw.name g.body := by
    obtain ⟨_, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ranA
    rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, -⟩
    · exact absurd hno hins
    rcases hcc with ⟨hf0, -⟩ | ⟨-, hG, -⟩
    · exact absurd hf0 hfe
    obtain ⟨_, h1, h2⟩ := Tools.ShippingChildServe.closeInstsG_acyclic hG
    exact ⟨h1, h2⟩
  have hI0 : 0 < p.d.shape.insts.length := by
    cases h : p.d.shape.insts with
    | nil => exact absurd h hins
    | cons _ _ => simp
  intro dsn hcons _ i
  have hEA : Tools.ShippingHierMono.ExtendsAway raw.name (childMap D.modules) (childMap dsn.modules) := by
    refine ⟨?_, ?_⟩
    · intro x r _ hD
      obtain ⟨g, hg, rfl⟩ := Tools.ShippingMachineDepthRun.childMap_some.mp hD
      have hm := Tools.ShippingHierPremisesBase.moduleByName_mem hg
      exact Tools.ShippingMachineDepthRun.childMap_some.mpr ⟨g, by rw [← hm.2]; exact hcons g hm.1, rfl⟩
    · intro x r hD
      obtain ⟨g, hg, rfl⟩ := Tools.ShippingMachineDepthRun.childMap_some.mp hD
      exact acyc.2 g (Tools.ShippingHierPremisesBase.moduleByName_mem hg).1
  exact Tools.ShippingGen2SlotlessParent.childRunN_of_composedNW_runSl n houtTy (ok_outNameOk p.d hok) hsl0 hI0
    hkD hIlen hSL hSlen hLlen hNIn hext.1 hext.2 i hNW hpost hEA acyc.1
    (slotlessParent_noTouch_ofRun L p hdata hins hsl0 hA ran)

end Tools.ShippingGen2
