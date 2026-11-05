import Tools.ShippingGen5SM7
import Tools.ShippingGen5T2TieCR2
import Tools.ShippingGen5ClosingRun4
import Tools.ShippingGen5T2Tie
set_option autoImplicit false
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # A.P-17: `T1Hyp.dec` derived inside the depth induction (scripts/gen5/AP17_FREEZE.md)

`ihAt_stepPF` / `ih_allPF` / `t1_of_stepPF` (`Tools/ShippingGen2T1.lean`) take `hT : T1Hyp` and use `hT.dec` only at the package
of the current step. Here the same induction runs from `H : T1HypND` (no `dec`): at each step the decoding of the package's
calls is built by `stepDec_of_ties` from `hT2Tie_of_genGP`, whose `hDG_CLOSINGRUN` for the run's own calls is read off the run's
`ClosingShared` (`closingShared_of_runR`, which needs only `IHAt (D+1)` / `ChildKeepsInv (D+1)`, so there is no circularity).
`ServedShips0StmtND` / `PostFactsStmtND` are the two statements `ServedShips0Stmt` / `PostFactsStmt` with `T1HypND` in place
of `T1Hyp` (their proofs are copies; they never used `dec`). CONDITIONAL on the rows listed in the freeze doc; not FG. -/

namespace Tools.ShippingGen2
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingChildInv Tools.ShippingChildInvA
open Tools.ShippingChildCacheA (JQC RealChildA)
open Tools.ShippingMachineDenote Tools.ShippingMachineSource
open Tools.ShippingChildBndCore (dv cv)
open Tools.ShippingChildRunAKids (MachineClosesAtA)
open Tools.ShippingEntrySoundness
open Sparkle.IR.AST (Stmt Design)
open Tools.ShippingMachineEntry (CloseCalls MemChildren instOrigin_child?_mem)
open Tools.ShippingGenFGLedgerPremises Tools.ShippingGen5Sem
open Tools.ShippingGen5ClosingRun2 Tools.ShippingGen5ClosingRun3 Tools.ShippingGen5RunReads Tools.ShippingGen5ClosingRun

variable {ι : Type} {dom : ι → DomainConfig}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

def ServedShips0StmtND {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop) : Prop :=
  T1HypND L P Reach DataOk →
  ∀ (p : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld)
    (raw : Sparkle.IR.AST.Module) (D : Design),
    Reach p.decl → P p.decl = some p → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    (dv w = 0 ∨ CacheShips L P Reach (cv w)) →
    IHAt L P Reach (dv w + 1) → ChildKeepsInv L P Reach (dv w + 1) →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w' →
    Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc

def PostFactsStmtND {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop) : Prop :=
  T1HypND L P Reach DataOk →
  ∀ (q : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (u u' w1 : Void IO.RealWorld)
    (M' raw : Sparkle.IR.AST.Module) (Dg' Dg : Design),
    Reach q.decl → P q.decl = some q → DataOk q → AdmCtx L.O.quiet mctx cctx →
    InvAt L P Reach (dv u) u →
    IHAt L P Reach (dv u + 1) → ChildKeepsInv L P Reach (dv u + 1) →
    RunsTo (synthesizeCombinational q.decl) mctx mref cctx cref u (M', Dg') u' →
    RunsTo (synthesizeCombinationalCore q.decl [] false) mctx mref cctx cref u (raw, Dg) w1 →
    (M' = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      M' = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    Dg'.topModule = Dg.topModule →
    ((∀ x ∈ Dg.modules, x.name ≠ raw.name) → Dg'.modules = Dg.modules) →
    MachineTaken L mctx cctx (dv u + 1) q.decl q.d.shape raw Dg →
    (∀ x ∈ Dg.modules, x.name ≠ raw.name) ∧ InstClosed (M', Dg')

theorem servedShips0_runND {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop) :
    ServedShips0StmtND L P Reach DataOk := by
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

theorem postFacts_of_runND {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Lean.Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q) :
    PostFactsStmtND L P Reach DataOk := by
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

/-! ## The rows `dec` is rebuilt from (A.P-16, A.P-19, A.P-09, A.P-25/D.T-3, D.T-4), over the reached packages of `P` -/

/-- A.P-16 `hG_MEMCALLS` over the reached packages. -/
def HMemRow (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ q : Pkg ι dom, Reach q.decl → P q.decl = some q →
    ∀ k (hk : k < q.d.shape.insts.length), (q.d.shape.instOrigins.getD k .ord).child? ≠ none →
      MemDec q k (q.d.shape.insts[k]).1

/-- A.P-19 / A.P-09 `hG_DATA_CALL_args` over the reached packages. -/
def HArgsRow (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ q : Pkg ι dom, Reach q.decl → P q.decl = some q →
    ∀ k (hk : k < q.d.shape.insts.length), (q.d.shape.instOrigins.getD k .ord).child? = none →
      ∀ q', P (q.d.shape.insts[k]).1 = some q' →
        callArgsOkAt q.d q.kD k q'.portWidths = true ∧ (q.d.shape.insts[k]).2.1.length = q'.ports.length

/-- A.P-25 / D.T-3 `OneOutWidth` over the reached one-output packages. -/
def HOWRow (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ q : Pkg ι dom, Reach q.decl → P q.decl = some q → q.d.shape.instFields = [] → ∀ k, OneOutWidth P q k

/-- D.T-4 `hkidW` over the reached group packages. -/
def HKidWRow {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ q : Pkg ι dom, Reach q.decl → P q.decl = some q → q.d.shape.instFields ≠ [] →
    ∀ (k : Nat) (hk : k < q.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (q.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = q.d.shape.instFields.getD k "" →
        (q.d.shape.binders[q.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth

section APGen
variable (lvl : Lean.Expr → Nat) {initsOf : (d : Tools.ShippingMachineAuto.MachineData) → HList (tys d.ss)}
  (hs : DataOfSound (Tools.ShippingGen5DataOf.dataOfAt lvl) initsOf)
  (genData₀ : (env : Environment) → (E : ConstantInfo) →
    Option (GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (Sparkle.Compiler.Elab.structEnv env)))
  (env : Environment)

local notation "GP" => genGP (ι := ι) (dom := dom) lvl hs genData₀ env

/-- **`dec` of the run's own package** (the content of `T1Hyp.dec` at `q`): `stepDec_of_ties` with `hT2_TIE` from
`hT2Tie_of_genGP`, whose `hDG_CLOSINGRUN` is the run's `ClosingShared` (`closingShared_of_runR`; premises `IHAt` / `ChildKeepsInv`
at `dv u + 1` only). -/
theorem decAt_ND (L : Laws mref cref) {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1HypND L (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) Reach DataOk)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hMEM : HMemRow (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) Reach)
    (hARGS : HArgsRow (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) Reach)
    (hOW : HOWRow (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) Reach)
    (hkidW : HKidWRow L (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) Reach)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {q : Pkg ι dom} (hR : Reach q.decl) (hPq : genGP (ι := ι) (dom := dom) lvl hs genData₀ env q.decl = some q)
    (hDq : DataOk q)
    {u w1 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {Dg : Design}
    (hjqc : JQC L.O (dv u) u) (hcc : dv u = 0 ∨ CacheShips L (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) Reach (cv u))
    (hIH : IHAt L (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) Reach (dv u + 1))
    (hKI : ChildKeepsInv L (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) Reach (dv u + 1))
    (hcore : RunsTo (synthesizeCombinationalCore q.decl [] false) mctx mref cctx cref u (raw, Dg) w1) :
    ∀ k (hk : k < q.d.shape.insts.length), MemDec q k (q.d.shape.insts[k]).1 ∨
      ∃ q', genGP (ι := ι) (dom := dom) lvl hs genData₀ env (q.d.shape.insts[k]).1 = some q' ∧ CallDec q q' k := by
  have hsh := Tools.ShippingGen5ClosingRun3.closingShared_of_runR L _ Reach DataOk H hA hR hPq hjqc hcc hIH hKI hcore
    (fun _ _ _ => True) (fun _ _ _ _ _ _ _ => trivial)
  have hclos : ∀ (k : Nat) (hk : k < q.d.shape.insts.length),
      (q.d.shape.instOrigins.getD k .ord).child? = none →
      ∀ q' : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl hs genData₀ env (q.d.shape.insts[k]).1 = some q' →
      ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
        ShipsRes L (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) (q.d.shape.insts[k]'hk).1 r ∧
        (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
        Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt q k r.1 := by
    intro k hk hord _ _
    by_cases h1 : q.d.shape.instFields = []
    · exact Tools.ShippingGen5T2TieCR.servedCall_of_closingShared_one H hR hPq hsh h1 k hk hord
    · exact Tools.ShippingGen5T2TieCR2.servedCall_of_closingShared_group H hR hPq hsh h1 k hk hord
  have hties := Tools.ShippingGen5SM7.hT2Tie_of_genGP (ι := ι) (dom := dom) lvl hs genData₀ env L H q hR hPq hclos
    (hOW q hR hPq) (hkidW q hR hPq)
  exact stepDec_of_ties _ q
    (fun k hk hn => by
      obtain ⟨q', hq', -, -⟩ := Tools.ShippingGen5T2TieCR2.calleePkg_of_t1ND H hR hPq k hk hn
      exact ⟨q', hq'⟩)
    hties (hrows q hDq).1 (hrows q hDq).2.1 (hARGS q hR hPq) (hMEM q hR hPq)

/-- **Step (ND)**: `ihAt_stepPF` from `T1HypND`; `hT.dec` is replaced by `decAt_ND`. -/
theorem ihAt_stepPF_ND (L : Laws mref cref) {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1HypND L (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) Reach DataOk)
    (hStep : StepStmt L (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) DataOk)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hMEM : HMemRow (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) Reach)
    (hARGS : HArgsRow (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) Reach)
    (hOW : HOWRow (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) Reach)
    (hkidW : HKidWRow L (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) Reach)
    (D : Nat) (hIH : IHAt L (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) Reach (D + 1))
    (hKI : ChildKeepsInv L (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) Reach (D + 1)) :
    IHAt L (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) Reach D := by
  intro c hc mctx cctx u u' r hA hu hr
  have hreal : RealChildA L.O c r := RealChildA.of_jqc L.O hA hu.1 hr
  obtain ⟨M', Dg'⟩ := r
  obtain ⟨M, Dg, w1, hcore, hb, htop, hmods⟩ :=
    Tools.ShippingDesignWriterRun.synthesizeCombinational_designTop hr
  obtain ⟨q, hPq, hqd, hDq⟩ := H.pkg c hc
  subst hqd
  have hdv : dv u = D := hu.1.1.2.2
  have hjqc : JQC L.O (dv u) u := by rw [hdv]; exact hu.1
  have hIH' : IHAt L (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) Reach (dv u + 1) := by rw [hdv]; exact hIH
  have hKI' : ChildKeepsInv L (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) Reach (dv u + 1) := by rw [hdv]; exact hKI
  have hdef : MachineDefines mctx mref cctx cref q.decl q.d.shape := H.defines q.decl hc q hPq mctx cctx hA
  have hcl : MachineClosesAtA L.O mctx cctx q.decl q.d.shape := H.closes q.decl hc q hPq mctx cctx hA
  have hsrv := servedShips0_runND L _ Reach DataOk H q mctx cctx u w1 M Dg hc hPq hA hjqc (Or.inr hu.2) hIH' hKI' hcore
  have htaken : MachineTaken L mctx cctx (dv u + 1) q.decl q.d.shape M Dg :=
    Tools.ShippingServedRealA.machineRunJQC_of_closesA L.O hA hcore hdef hcl hjqc.1 (Or.inr hu.1.2)
  have hdec := decAt_ND lvl hs genData₀ env L H hrows hMEM hARGS hOW hkidW hA hc hPq hDq hjqc (Or.inr hu.2) hIH' hKI' hcore
  obtain ⟨n, -, hCS⟩ :=
    hStep q mctx cctx u w1 M M' Dg hPq hDq hA hjqc hcore hb hdef htaken hdec hsrv
  obtain ⟨hnt, hic⟩ := postFacts_of_runND L _ Reach DataOk hrows H q mctx cctx u u' w1 M' M Dg' Dg hc hPq hDq hA
    (by rw [hdv]; exact hu) hIH' hKI' hr hcore hb htop hmods htaken
  exact ⟨hreal, ⟨q, n, hPq, rfl, childShips_congr q n M' (hmods hnt).symm hCS⟩, hic⟩

/-- **The depth induction (ND)**: `ih_allPF` from `T1HypND`; `dec` is built at every level by `ihAt_stepPF_ND`. -/
theorem ih_allPF_ND (L : Laws mref cref) {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1HypND L GP Reach DataOk)
    (hStep : StepStmt L GP DataOk)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hMEM : HMemRow GP Reach) (hARGS : HArgsRow GP Reach)
    (hOW : HOWRow GP Reach) (hkidW : HKidWRow L GP Reach) :
    ∀ D, 1 ≤ D → IHAt L GP Reach D ∧ ChildKeepsInv L GP Reach D := by
  have key : ∀ k D, sparkleSynthDepthLimit - D = k → 1 ≤ D →
      IHAt L GP Reach D ∧ ChildKeepsInv L GP Reach D := by
    intro k
    induction k with
    | zero =>
      intro D hk hD1
      have hle : sparkleSynthDepthLimit ≤ D := by omega
      have hI : IHAt L GP Reach D := ihAt_limit L GP Reach (limitStmt_proved L) hle
      exact ⟨hI, keepChild_proved L GP Reach D hD1 (fun hlt => absurd hle (by omega)) hI⟩
    | succ k ih =>
      intro D hk hD1
      have hN := ih (D + 1) (by omega) (by omega)
      have hI : IHAt L GP Reach D :=
        ihAt_stepPF_ND lvl hs genData₀ env L H hStep hrows hMEM hARGS hOW hkidW D hN.1 hN.2
      exact ⟨hI, keepChild_proved L GP Reach D hD1 (fun _ => keepBody L GP Reach (D + 1) hN.2) hI⟩
  intro D hD1
  exact key _ D rfl hD1

/-- **T1 (ND)**: `t1_of_stepPF` from `T1HypND`; the top's `dec` is `decAt_ND` at depth `0`. -/
theorem t1_of_stepPF_ND (L : Laws mref cref) {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1HypND L GP Reach DataOk)
    (hStep : StepStmt L GP DataOk)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hMEM : HMemRow GP Reach) (hARGS : HArgsRow GP Reach)
    (hOW : HOWRow GP Reach) (hkidW : HKidWRow L GP Reach) :
    ∀ (c : Name) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
      (raw b : Sparkle.IR.AST.Module) (Dg : Design),
      Reach c → Start L mctx cctx w →
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, Dg) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      ∃ q n, GP c = some q ∧ TopShips q n c b raw Dg := by
  intro c mctx cctx w w1 raw b Dg hc hS hr hb
  obtain ⟨hA, hj0⟩ := hS
  obtain ⟨q, hPq, hqd, hDq⟩ := H.pkg c hc
  subst hqd
  have hdv : dv w = 0 := hj0.1.2.2
  obtain ⟨hI1, hK1⟩ := ih_allPF_ND lvl hs genData₀ env L H hStep hrows hMEM hARGS hOW hkidW 1 (Nat.le_refl 1)
  have hjqc : JQC L.O (dv w) w := by rw [hdv]; exact hj0
  have hI1' : IHAt L GP Reach (dv w + 1) := by rw [hdv]; exact hI1
  have hK1' : ChildKeepsInv L GP Reach (dv w + 1) := by rw [hdv]; exact hK1
  have hdef : MachineDefines mctx mref cctx cref q.decl q.d.shape := H.defines q.decl hc q hPq mctx cctx hA
  have hcl : MachineClosesAtA L.O mctx cctx q.decl q.d.shape := H.closes q.decl hc q hPq mctx cctx hA
  have hsrv := servedShips0_runND L GP Reach DataOk H q mctx cctx w w1 raw Dg hc hPq hA hjqc (Or.inl hdv) hI1' hK1' hr
  have htaken : MachineTaken L mctx cctx (dv w + 1) q.decl q.d.shape raw Dg :=
    Tools.ShippingServedRealA.machineRunJQC_of_closesA L.O hA hr hdef hcl hjqc.1 (Or.inl hdv)
  have hdec := decAt_ND lvl hs genData₀ env L H hrows hMEM hARGS hOW hkidW hA hc hPq hDq hjqc (Or.inl hdv) hI1' hK1' hr
  obtain ⟨n, hTop, -⟩ := hStep q mctx cctx w w1 raw b Dg hPq hDq hA hjqc hr hb hdef htaken hdec hsrv
  exact ⟨q, n, hPq, hTop⟩

/-- `closingRun0_of_runT1` (`Tools.ShippingGen5ClosingRun4`) with `T1HypND` and `ih_allPF_ND`. -/
theorem closingRun0_of_runT1_ND (L : Laws mref cref) {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1HypND L GP Reach DataOk)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hStep : StepStmt L GP DataOk)
    (hMEM : HMemRow GP Reach) (hARGS : HArgsRow GP Reach)
    (hOW : HOWRow GP Reach) (hkidW : HKidWRow L GP Reach)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : GP X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs0 : Start L mctx cctx w) (hd0 : dv w = 0)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR') :
    ClosingRun0 L GP Reach mctx cctx X p Gen w w' raw D :=
  have h := ih_allPF_ND lvl hs genData₀ env L H hStep hrows hMEM hARGS hOW hkidW 1 (Nat.le_refl 1)
  Tools.ShippingGen5ClosingRun3.closingRun0_of_runR L GP Reach DataOk H hR hP hs0 hd0 h.1 h.2 hrun Gen hGen

/-- `closingRun_of_runT1` (`Tools.ShippingGen5ClosingRun4`) with `T1HypND` and `ih_allPF_ND`. -/
theorem closingRun_of_runT1_ND (L : Laws mref cref) {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1HypND L GP Reach DataOk)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hStep : StepStmt L GP DataOk)
    (hMEM : HMemRow GP Reach) (hARGS : HArgsRow GP Reach)
    (hOW : HOWRow GP Reach) (hkidW : HKidWRow L GP Reach)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : GP X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L GP Reach (dv w) w)
    (h1 : 1 ≤ dv w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR') :
    ClosingRun L GP Reach mctx cctx X p Gen w w' raw D :=
  have h := ih_allPF_ND lvl hs genData₀ env L H hStep hrows hMEM hARGS hOW hkidW (dv w + 1) (Nat.succ_pos _)
  Tools.ShippingGen5ClosingRun3.closingRun_of_runR L GP Reach DataOk H hA hR hP hst h.1 h.2 h1 hrun Gen hGen

end APGen

end Tools.ShippingGen2

#print axioms Tools.ShippingGen2.decAt_ND
#print axioms Tools.ShippingGen2.ihAt_stepPF_ND
#print axioms Tools.ShippingGen2.ih_allPF_ND
#print axioms Tools.ShippingGen2.t1_of_stepPF_ND
#print axioms Tools.ShippingGen2.closingRun0_of_runT1_ND
#print axioms Tools.ShippingGen2.closingRun_of_runT1_ND
