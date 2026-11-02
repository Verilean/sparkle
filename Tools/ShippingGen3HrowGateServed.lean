import Tools.ShippingGen3HrowGate
import Tools.ShippingGen5RunReads
import Tools.ShippingGen2PostFactsProof
import Tools.ShippingGen2Served
set_option autoImplicit false

/-! # G-HROW-GATE consumers: `servedShips0_proved` / `postFacts_proved` / `t1_of_stepPF_served` per run

Built: cached target build at 76c9d2ae (kjob lake build in the rt77 Pod; NOT a clean build, the coder runs it), exit 0, standard axioms.

The existing theorems (`Tools/ShippingGen2Served.lean`, `Tools/ShippingGen2PostFactsProof.lean`) stay unchanged. Here:

* `servedShips0_run L P Reach DataOk : ServedShips0Stmt L P Reach DataOk` — NO `hrow`.
* `postFacts_of_run L P Reach DataOk hrows : PostFactsStmt L P Reach DataOk` — NO `hrow` (`hrows` stays).
* `t1_of_stepPF_run L P Reach DataOk hStep hPF : T1Stmt L P Reach DataOk` — NO `hrow`.
* `t1_of_step_rows_run L P Reach DataOk hrows hStep` — NO `hrow`.

**Change of meaning (reviewer's rule: universal → run-scoped is a change of the theorem's meaning).** The old theorems took
`hrow : ∀ q, DataOk q → OneOutNoMemRow q = true`, a premise over EVERY package of the abstract `DataOk`. These take no row
premise. Inside, at the one reached package `p` of the run in hand, `runReads_of_run` (Gen5RunReads, RR3) gives
`RunReadsAt.shapeEq : machineShape? … = some p.d.shape` for that run (inputs: `JQ`/cache from `JQC`, the core run,
`MachineDefines`, `MachineClosesAtA` — the ones the old theorems already held), and `machineShape?_noMemRow` (L2, the
final gate of `machineShape?`) gives `OneOutNoMemRow p`. So the row is no longer a premise but a fact of the run.
It depends on the compiler gate being in force (Elab.lean, commit 72fa2fad of this Issue) and on nothing else new.
No `DataOk`, `T1Hyp`, or shared definition is changed. -/
namespace Tools.ShippingGen2
open Sparkle.Compiler.Elab
open Sparkle.IR.AST (Stmt Design)
open Tools.ShippingMachineEntry (CloseCalls MemChildren instOrigin_child?_mem)
open Tools.ShippingHierMono (NoInstOf)
open Tools.ShippingChildBndCore (dv cv)
open Lean Meta Sparkle.IR.Machine
open Sparkle.Core.Domain
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildCacheA (JQC)
open Tools.ShippingChildRunAKids (MachineClosesAtA)

/-- **`servedShips0_proved` per run — no `hrow`.** -/
theorem servedShips0_run {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop) :
    ServedShips0Stmt L P Reach DataOk := by
  intro hT p mctx cctx w w' raw D hR hP hA hjqc hc hIH hKI hr
  have hdef : MachineDefines mctx mref cctx cref p.decl p.d.shape :=
    hT.defines p.decl hR p hP mctx cctx hA
  have hcl : MachineClosesAtA L.O mctx cctx p.decl p.d.shape :=
    hT.closes p.decl hR p hP mctx cctx hA
  obtain ⟨_, _, _, _, _, _, hRR, -⟩ :=
    Tools.ShippingGen5RunReads.runReads_of_run L.O hA hjqc.1 (Or.inr hjqc.2) hr hdef hcl
  have hrowp : Tools.ShippingGen2DataBridge.OneOutNoMemRow p = true :=
    Tools.ShippingGen3HrowGate.machineShape?_noMemRow hRR.shapeEq
  have ran : MachineRunInv L P Reach mctx cctx (dv w + 1) p.decl p.d.shape raw D :=
    machineRunInv_of_closes0 L P Reach hA hr hdef hcl hjqc hc
  have hX : SoundXAt (ServedP (ShipsRes L P) p.decl p.d.shape raw D) p.decl p.d.shape raw D :=
    soundX_ships_ran L P Reach hA ran hIH hKI
      (fun k hk hn => hT.closed p.decl hR p hP k hk hn)
      (fun hf k hk => Tools.ShippingGen2DataBridge.hord_of_row hrowp hf k hk)
  exact Pkg.traceX p hX

/-- **`t1_of_stepPF_served` per run — no `hrow`.** -/
theorem t1_of_stepPF_run {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hStep : StepStmt L P DataOk) (hPF : PostFactsStmt L P Reach DataOk) :
    T1Stmt L P Reach DataOk :=
  t1_of_stepPF_kc L P Reach DataOk hStep (servedShips0_run L P Reach DataOk) hPF
    (limitStmt_proved L)

/-- **`postFacts_proved` per run — no `hrow`** (`hrows` stays). The proof is that of `postFacts_of_hord`
(Tools/ShippingGen2PostFactsProof.lean) with `hord q hDq` replaced by the per-run `hordq`. -/
theorem postFacts_of_run {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Lean.Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q) :
    PostFactsStmt L P Reach DataOk := by
  intro hT q mctx cctx u u' w1 M' raw Dg' Dg hR hPq hDq hA hu hIH hKI _hfull hcore hb _htop hmods _htaken
  have entry := hT.defines q.decl hR q hPq mctx cctx hA
  -- per-run row (user decision G): the shape of THIS run is the one `machineShape?` returned, and the final gate
  -- of `machineShape?` gives its `OneOutNoMemRow`
  have hcl : MachineClosesAtA L.O mctx cctx q.decl q.d.shape := hT.closes q.decl hR q hPq mctx cctx hA
  obtain ⟨_, _, _, _, _, _, hRR, -⟩ :=
    Tools.ShippingGen5RunReads.runReads_of_run L.O hA hu.1.1 (Or.inr hu.1.2) hcore entry hcl
  have hrowq : Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true :=
    Tools.ShippingGen3HrowGate.machineShape?_noMemRow hRR.shapeEq
  have hordq : q.d.shape.instFields = [] → ∀ k, k < q.d.shape.insts.length →
      (q.d.shape.instOrigins.getD k .ord).child? = none :=
    fun hf k hk => Tools.ShippingGen2DataBridge.hord_of_row hrowq hf k hk
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
      have hmemc : MemChildren q.d.shape children := memChildren_of_closeCalls hcc hordq
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

/-- **T1 — CONDITIONAL on `StepStmt` and `hrows` only** (`t1_of_step_rows` without `hrow`). Not M2/M3/FG completion. -/
theorem t1_of_step_rows_run {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Lean.Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hStep : StepStmt L P DataOk) :
    T1Stmt L P Reach DataOk :=
  t1_of_stepPF_run L P Reach DataOk hStep (postFacts_of_run L P Reach DataOk hrows)

end Tools.ShippingGen2
