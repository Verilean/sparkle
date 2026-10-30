import Tools.ShippingGen2PostFacts
import Tools.ShippingGen2ServedRun
import Tools.ShippingGen2Served
import Tools.ShippingGen2KidsInst
import Tools.ShippingGen2InstKeep
set_option autoImplicit false
-- Built: g3pf3-a9c42458 (clean snapshot, exit 0, standard axioms) (written by reading at 35588c38; scripts/gen2/GPOST_FREEZE.md rev1 §5 + §11,
-- scripts/gen2/GPOST_ASSEMBLY_NOTE.md). No `sorry`, no `axiom`, no `native_decide`.
-- The statements live in Tools/ShippingGen2PostFacts.lean (built at 28476add); that file is NOT edited, so the
-- producer is in this NEW file.

/-! # G-POST assembly: the producer of `PostFactsStmt` (issue `sparkle-gen3-post`)

`postFacts_proved (hrows) (hrow) : PostFactsStmt L P Reach DataOk` — CONDITIONAL on two explicit, UNSUPPLIED data
premises, nothing else:

* `hrows : ∀ q, DataOk q → DataRows q` (freeze §11 S1: kept explicit; `DataOkB` unchanged). Used only for P3
  (`closedBody_kinds_of_run`: the harness design `d₀` has no module).
* `hrow : ∀ q, DataOk q → OneOutNoMemRow q = true` (U1 = G-ONEOUT-REACH, the SAME R-ROW premise as
  `servedShips0_proved`, SERVED_FREEZE rev1 D1/§2.3; through the local copy `hord_of_row`). Used only in the
  one-output closing (`instFields = []`), where `closeInstsM` gives no `MemChildren`: it makes every entry `.ord`-like,
  so `T1Hyp.closed` gives `Reach` and the child's `ShipsRes` (hence `InstClosed`) is available.
  `postFacts_of_hord` states the same with the semantic form `hord` in place of the row.

U2 (G-REACH) is NOT a premise: every module of the core design comes from the closing's `children` (P3 + P8), which
are indexed by `q.d.shape.insts` (the shape `T1Hyp.defines` fixes for the machine run), so `T1Hyp.closed` on
`q.d.shape` is exactly the reach needed; the translator's own calls add no module to `d₀` (P3).

Wiring (freeze §5): P1 = `machineRunInv_of_coreA` + `T1Hyp.closes` (F1, Tools/ShippingGen2ServedRun.lean, imported,
not redefined); P2 = `synthesizeMachineCertified_runsS` (F1); P7 = `closeInsts(G)_kids_inst` with `hlen` from P2's
`ChildrenShipsI` length conjunct; P3 `closedBody_kinds_of_run`; P4/P6 `closeInsts(G)_design`, `closeInsts(G)_acyclic`;
P5 `closeInsts_names` + `closeInsts_acyclic` / `closeInstsG_names`; P8 `mem_designWith` + `mem_visited`;
P9 `instOrigin_child?_mem` (memory module design `[md.1]`, by `rfl` as Srm12Corr.lean:139); P10 `inst_target_full`.

`t1_of_step_rows`: `T1Stmt` CONDITIONAL on `StepStmt`, `hrows`, `hrow` (= `t1_of_stepPF_served` with
`hPF := postFacts_proved …`). Neither result completes G-POST, T1/M3 or FG while `hrows`/`hrow` are unsupplied. -/

namespace Tools.ShippingGen2
open Sparkle.Compiler.Elab
open Sparkle.IR.AST (Stmt Design)
open Tools.ShippingMachineEntry (CloseCalls MemChildren instOrigin_child?_mem)
open Tools.ShippingHierMono (NoInstOf)
open Tools.ShippingChildBndCore (dv)

/-! ## 1. Pure facts of the closing (P4-P8) -/

/-- **The closing facts G-POST uses** (both closings): the design is the joined design (P4), the closed module
instantiates neither itself nor is it instantiated in the design (P6), every child top and child-design module is
found in the design as itself (P5), every child top is instantiated in the closed body (P7, `hlen` from P2), and the
general closing has `MemChildren`. -/
theorem closeCalls_post {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Design}
    {children : List (Sparkle.IR.AST.Module × Design)} {m : Sparkle.IR.AST.Module} {d : Design}
    (h : CloseCalls shape t m₀ d₀ children m d) (hlen : children.length = shape.insts.length) :
    d = Sparkle.IR.Machine.designWith children d₀ ∧
    NoInstOf m.name m.body ∧ (∀ g ∈ d.modules, NoInstOf m.name g.body) ∧
    (∀ c ∈ children, Sparkle.IR.Machine.moduleByName d.modules c.1.name = some c.1 ∧
      ∀ g ∈ c.2.modules, Sparkle.IR.Machine.moduleByName d.modules g.name = some g) ∧
    (∀ c ∈ children, ∃ (i : String) (cs : List (String × Sparkle.IR.AST.Expr)),
      Stmt.inst c.1.name i cs ∈ m.body) := by
  have hlenM : children.length = (shape.insts.map (·.2.1)).length := by
    rw [List.length_map]; exact hlen
  rcases h with ⟨_, hc⟩ | ⟨_, hc, _⟩
  · obtain ⟨_, hn1, hn2, hcons⟩ := Tools.ShippingChildServe.closeInsts_acyclic hc
    obtain ⟨_, hnames⟩ := Tools.ShippingChildServe.closeInsts_names hc
    exact ⟨Tools.ShippingCacheCoherentClose.closeInsts_design hc, hn1, hn2,
      fun c hcm => ⟨hnames c hcm, hcons c hcm⟩,
      Tools.ShippingGen2KidsInst.closeInsts_kids_inst hc hlenM⟩
  · obtain ⟨_, hn1, hn2⟩ := Tools.ShippingChildServe.closeInstsG_acyclic hc
    obtain ⟨_, _, _, hcons⟩ := Tools.ShippingMachineInstG.closeInstsG_names hc
    exact ⟨Tools.ShippingCacheCoherentClose.closeInstsG_design hc, hn1, hn2, hcons,
      Tools.ShippingGen2KidsInst.closeInstsG_kids_inst hc hlenM⟩

/-- `MemChildren` for both closings: given by the general closing; for the one-output closing it holds vacuously
under the U1 condition `hord1` (no memory origin when `instFields = []`). -/
theorem memChildren_of_closeCalls {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Design}
    {children : List (Sparkle.IR.AST.Module × Design)} {m : Sparkle.IR.AST.Module} {d : Design}
    (h : CloseCalls shape t m₀ d₀ children m d)
    (hord1 : shape.instFields = [] → ∀ k, k < shape.insts.length →
      (shape.instOrigins.getD k .ord).child? = none) :
    MemChildren shape children := by
  rcases h with ⟨hf, _⟩ | ⟨_, _, hmc⟩
  · intro k hk md hmd
    rw [hord1 hf k hk] at hmd
    cases hmd
  · exact hmc

/-- **Every module of the joined design has an incoming instance** (P8 + P7 + P5): in the closed body (a child
top, or a memory child's only module), or in a module of the design (a module of an instance-closed child's design;
the instantiating module is the child's top or one of its design's modules, both found in the design by P5). -/
theorem inst_source {raw : Sparkle.IR.AST.Module} {Dg d₀ : Design}
    {children : List (Sparkle.IR.AST.Module × Design)}
    (hd : Dg = Sparkle.IR.Machine.designWith children d₀) (hd0 : d₀.modules = [])
    (hcons : ∀ c ∈ children, Sparkle.IR.Machine.moduleByName Dg.modules c.1.name = some c.1 ∧
      ∀ g ∈ c.2.modules, Sparkle.IR.Machine.moduleByName Dg.modules g.name = some g)
    (hkids : ∀ c ∈ children, ∃ (i : String) (cs : List (String × Sparkle.IR.AST.Expr)),
      Stmt.inst c.1.name i cs ∈ raw.body)
    (hship : ∀ y ∈ children, y.2.modules = [y.1] ∨ InstClosed y) :
    ∀ g ∈ Dg.modules,
      (∃ (i : String) (cs : List (String × Sparkle.IR.AST.Expr)), Stmt.inst g.name i cs ∈ raw.body) ∨
      ∃ h ∈ Dg.modules, ∃ (i : String) (cs : List (String × Sparkle.IR.AST.Expr)),
        Stmt.inst g.name i cs ∈ h.body := by
  intro g hg
  have hg0 := hg
  rw [hd] at hg0
  rcases Tools.ShippingCacheCoherentClose.mem_designWith hg0 with h0 | hv
  · rw [hd0] at h0
    exact absurd h0 (by simp)
  · obtain ⟨c, hc, hgc⟩ := Tools.ShippingDesignWithG.mem_visited.mp hv
    rcases hgc with hgc | hgc
    · rw [hgc]
      exact Or.inl (hkids c hc)
    · rcases hship c hc with hm | hic
      · rw [hm] at hgc
        have hgc' : g = c.1 := List.mem_singleton.mp hgc
        rw [hgc']
        exact Or.inl (hkids c hc)
      · obtain ⟨h, hh, i, cs, hi⟩ := hic g hgc
        refine Or.inr ⟨h, ?_, i, cs, hi⟩
        rcases List.mem_cons.mp hh with hh1 | hh1
        · rw [hh1]
          exact (Tools.ShippingHierPremisesBase.moduleByName_mem (hcons c hc).1).1
        · exact (Tools.ShippingHierPremisesBase.moduleByName_mem ((hcons c hc).2 h hh1)).1

/-- **(i) and (ii) from incoming instances** (P6 + P10): an incoming instance in the closed body or in a design
module excludes the top name (P6); the full entry keeps the core design (`hmods`) and the closed body's instance
targets (P10). -/
theorem post_of_source {raw M' : Sparkle.IR.AST.Module} {Dg Dg' : Design}
    (hsrc : ∀ g ∈ Dg.modules,
      (∃ (i : String) (cs : List (String × Sparkle.IR.AST.Expr)), Stmt.inst g.name i cs ∈ raw.body) ∨
      ∃ h ∈ Dg.modules, ∃ (i : String) (cs : List (String × Sparkle.IR.AST.Expr)),
        Stmt.inst g.name i cs ∈ h.body)
    (hNo1 : NoInstOf raw.name raw.body) (hNo2 : ∀ g ∈ Dg.modules, NoInstOf raw.name g.body)
    (hb : M' = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      M' = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hmods : (∀ x ∈ Dg.modules, x.name ≠ raw.name) → Dg'.modules = Dg.modules) :
    (∀ x ∈ Dg.modules, x.name ≠ raw.name) ∧ InstClosed (M', Dg') := by
  have hi : ∀ x ∈ Dg.modules, x.name ≠ raw.name := by
    intro x hx
    rcases hsrc x hx with ⟨i, cs, h⟩ | ⟨h, hh, i, cs, h'⟩
    · exact hNo1 x.name i cs h
    · exact hNo2 h hh x.name i cs h'
  refine ⟨hi, ?_⟩
  show ∀ g ∈ Dg'.modules, ∃ h ∈ M' :: Dg'.modules,
    ∃ (i : String) (cs : List (String × Sparkle.IR.AST.Expr)), Stmt.inst g.name i cs ∈ h.body
  intro g hg
  have hg' : g ∈ Dg.modules := by rw [← hmods hi]; exact hg
  rcases hsrc g hg' with ⟨i, cs, h⟩ | ⟨h, hh, i, cs, h'⟩
  · obtain ⟨i', cs', h''⟩ := Tools.ShippingGen2InstKeep.inst_target_full hb ⟨i, cs, h⟩
    exact ⟨M', List.mem_cons.mpr (Or.inl rfl), i', cs', h''⟩
  · refine ⟨h, List.mem_cons.mpr (Or.inr ?_), i, cs, h'⟩
    rw [hmods hi]
    exact hh

/-! ## 2. The producer -/

/-- **G-POST producer, semantic form — CONDITIONAL** on `hrows` (freeze §11 S1) and `hord` (U1, the
G-ONEOUT-REACH condition `hord1` of SERVED_FREEZE rev1 §1.5 for every `DataOk` package). -/
theorem postFacts_of_hord {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Lean.Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] → ∀ k, k < q.d.shape.insts.length →
      (q.d.shape.instOrigins.getD k .ord).child? = none) :
    PostFactsStmt L P Reach DataOk := by
  intro hT q mctx cctx u u' w1 M' raw Dg' Dg hR hPq hDq hA hu hIH hKI _hfull hcore hb _htop hmods _htaken
  have entry := hT.defines q.decl hR q hPq mctx cctx hA
  -- P1 (F1 canonical): the machine synthesis inside the core run, from an `InvAt (dv u + 1)` world
  obtain ⟨tenv, b, r, w9, w10, hrun, hw9, hres⟩ := machineRunInv_of_coreA L P Reach hA hcore entry hu
  have hne := hT.closes q.decl hR q hPq mctx cctx hA (tenv := tenv) b (dv u + 1) w9 r w10 hw9.1 (by omega) hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have hres' := hres res rfl
    subst hres'
    -- P2 (F1 canonical): the harness run, the closing and the children at `InvAt`
    obtain ⟨t, t', d₀, run, hcl, hcase⟩ :=
      synthesizeMachineCertified_runsS L P Reach hA hIH hKI hw9 hrun
    -- P3: the harness design has no module (data rows, explicit)
    have hd0 : d₀.modules = [] :=
      (Tools.ShippingClosedKinds.closedBody_kinds_of_run q.d q.ok q.body_eq
        (hrows q hDq).1 (hrows q hDq).2.1 (hrows q hDq).2.2 run hcl).2.2
    rcases hcase with ⟨_, _, hDg⟩ | ⟨_, children, hcc, hCS⟩
    · -- no calls: the core design is `d₀`, empty
      have hD0 : Dg.modules = [] := by rw [hDg]; exact hd0
      have hi : ∀ x ∈ Dg.modules, x.name ≠ raw.name := by
        intro x hx
        rw [hD0] at hx
        exact absurd hx (by simp)
      refine ⟨hi, ?_⟩
      show ∀ g ∈ Dg'.modules, ∃ h ∈ M' :: Dg'.modules,
        ∃ (i : String) (cs : List (String × Sparkle.IR.AST.Expr)), Stmt.inst g.name i cs ∈ h.body
      intro g hg
      have hg' : g ∈ Dg.modules := by rw [← hmods hi]; exact hg
      rw [hD0] at hg'
      exact absurd hg' (by simp)
    · have hlenC : children.length = q.d.shape.insts.length := hCS.1
      obtain ⟨hdes, hNo1, hNo2, hcons, hkids⟩ := closeCalls_post hcc hlenC
      have hmemc : MemChildren q.d.shape children := memChildren_of_closeCalls hcc (hord q hDq)
      -- every child: a memory module (design `[top]`) or instance-closed (`ShipsRes` of a reached child)
      have hship : ∀ y ∈ children, y.2.modules = [y.1] ∨ InstClosed y := by
        intro y hy
        obtain ⟨j, hj, hyj⟩ := List.getElem_of_mem hy
        have hjI : j < q.d.shape.insts.length := by rw [← hlenC]; exact hj
        obtain ⟨y', hy', hor⟩ := hCS.2 j hjI
        rw [List.getElem?_eq_getElem hj, hyj] at hy'
        have hyy : y = y' := Option.some.inj hy'
        rw [← hyy] at hor
        cases ho : (q.d.shape.instOrigins.getD j .ord).child? with
        | some md =>
          have hm := hmemc j hjI md ho
          rw [List.getElem?_eq_getElem hj, hyj] at hm
          have hym : y = md := Option.some.inj hm
          obtain ⟨cb, aw, dw, hmd⟩ := instOrigin_child?_mem ho
          -- `memModule_design_modules` (Srm12Corr.lean:139), by `rfl`
          have hmm : (Sparkle.Compiler.MachMemory.memModule cb aw dw).2.modules =
              [(Sparkle.Compiler.MachMemory.memModule cb aw dw).1] := rfl
          rw [← hmd, ← hym] at hmm
          exact Or.inl hmm
        | none =>
          rcases hor with hsome | ⟨_, hS⟩
          · rw [ho] at hsome
            cases hsome
          · exact Or.inr (hS (hT.closed q.decl hR q hPq j hjI ho)).2.2
      exact post_of_source (inst_source hdes hd0 hcons hkids hship) hNo1 hNo2 hb hmods

/-- **G-POST producer — CONDITIONAL** on the two explicit, UNSUPPLIED data premises `hrows` (freeze §11 S1) and
`hrow` (U1 = G-ONEOUT-REACH, the R-ROW premise of `servedShips0_proved`). NOT `PostFactsStmt` at the abstract
`DataOk`; does not complete G-POST, T1 or FG. -/
theorem postFacts_proved {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Lean.Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true) :
    PostFactsStmt L P Reach DataOk :=
  postFacts_of_hord L P Reach DataOk hrows
    (fun q hq hf k hk => Tools.ShippingGen2DataBridge.hord_of_row (hrow q hq) hf k hk)

/-- **T1 — CONDITIONAL** on `StepStmt` and the two unsupplied data premises `hrows`, `hrow`
(`t1_of_stepPF_served` with `hPF := postFacts_proved …`). Not M2/M3/FG completion. -/
theorem t1_of_step_rows {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Lean.Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hStep : StepStmt L P DataOk) :
    T1Stmt L P Reach DataOk :=
  t1_of_stepPF_served L P Reach DataOk hrow hStep (postFacts_proved L P Reach DataOk hrows hrow)

end Tools.ShippingGen2

#print axioms Tools.ShippingGen2.closeCalls_post
#print axioms Tools.ShippingGen2.memChildren_of_closeCalls
#print axioms Tools.ShippingGen2.inst_source
#print axioms Tools.ShippingGen2.post_of_source
#print axioms Tools.ShippingGen2.postFacts_of_hord
#print axioms Tools.ShippingGen2.postFacts_proved
#print axioms Tools.ShippingGen2.t1_of_step_rows
