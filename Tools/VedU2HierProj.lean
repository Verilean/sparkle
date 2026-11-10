import Tools.VedU2HierSem

/-!
# H2 unit 2: step success, existence of the hierarchical run, projection

Design: docs/VED-HIER-H2-DESIGN.md §2.4, §2.5, §11 (reviewer obligations of 3e04041c).

* §2.5 STEP SUCCESS.  Ordering and wiring alone do not make `evalExpr` succeed on unsupported
  forms.  The conditions are explicit here: `ExprsSupp` (every assign / register input of the top
  evaluates, a syntactic-support check at the all-0 environment; success of `evalExpr` does not
  depend on the environment: `evalExpr_env_some`) and `ChildSucc` (the child's one cycle succeeds
  at ONE point; for a leaf body that is success at every seed).  `childSucc_of_outputsOn` derives
  `ChildSucc` from the child's REAL U1 statement (`OutputsOn`, K = 1, the all-0 stream), so no
  success assumption is left in a final statement: the child's theorem plus the shape supply it.
* §2.4 PROJECTION with an EXPLICIT child state trace (`runModuleTrace`): input and output
  PORTS correspond through the parent environments, internal REGISTERS through the child state
  history; never a claim about the child's whole environment from the connections alone.
-/

namespace Tools.VedU2Hier

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier

/-! ## The H2 shape (depth 1: assignments and registers in the top, leaf children with registers) -/

def isAsgInstReg : Stmt → Bool
  | .assign .. => true
  | .inst .. => true
  | .register .. => true
  | _ => false

/-- A child module's own sanity: its inputs have distinct names, no assignment writes an input,
no register output is an input. -/
def childSane (c : Module) : Bool :=
  decide (inNames c).Nodup &&
  c.body.all (fun s => match s with
    | .assign l _ => !(inNames c).contains l
    | _ => true) &&
  (regOuts c.body).all (fun n => !(inNames c).contains n)

/-- One `inst` against the design (H2): H1's `connsOk` with a child that may carry registers
(`leafBody`), plus `childSane`. -/
def connsOkS (d : Design) (m : Module) (mn : String) (cs : List (String × Expr)) : Bool :=
  match findMod d mn with
  | none => false
  | some c =>
    !c.isPrimitive && c.parameters.isEmpty && c.assertions.isEmpty && leafBody c.body &&
    childSane c &&
    c.outputs.length == 1 && decide (cs.map (·.1)).Nodup &&
    (c.inputs ++ c.outputs).all (fun p => cs.any (fun q => q.1 == p.name)) &&
    cs.all (fun q => (c.inputs ++ c.outputs).any (fun p => p.name == q.1)) &&
    cs.all (fun q => match q.2 with
      | .ref x => (c.inputs ++ c.outputs).any
          (fun p => p.name == q.1 && scalar p.ty && declWidth m x == p.ty.bitWidth)
      | _ => false)

/-- The design checks of H2, the analogue of `HierShape`; plus the clock/reset judgement. -/
def HierShapeS (d : Design) (m : Module) : Bool :=
  d.topModule == m.name && decide (d.modules.map (·.name)).Nodup &&
  !((d.modules.map (·.name)).contains m.name) &&
  m.body.all isAsgInstReg &&
  m.body.all (fun s => match s with
    | .inst mn _ cs => connsOkS d m mn cs
    | _ => true) &&
  decide (instNames m.body).Nodup &&
  d.modules.all (fun c => m.body.any (fun s => match s with
    | .inst mn _ _ => mn == c.name
    | _ => false)) &&
  clkRstOk d m

theorem hierS_inst_unique {d : Design} {m : Module} (h : HierShapeS d m = true) :
    (instNames m.body).Nodup := by
  simp only [HierShapeS, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

theorem hierS_clk {d : Design} {m : Module} (h : HierShapeS d m = true) : clkRstOk d m = true := by
  simp only [HierShapeS, Bool.and_eq_true] at h
  exact h.2

theorem hierS_body {d : Design} {m : Module} (h : HierShapeS d m = true) :
    ∀ s ∈ m.body, isAsgInstReg s = true := by
  have : m.body.all isAsgInstReg = true := by
    simp only [HierShapeS, Bool.and_eq_true] at h
    exact h.1.1.1.1.2
  exact fun s hs => List.all_eq_true.mp this s hs

theorem hierS_inst_ok {d : Design} {m : Module} (h : HierShapeS d m = true) {mn i : String}
    {cs : List (String × Expr)} (hin : Stmt.inst mn i cs ∈ m.body) : connsOkS d m mn cs = true := by
  have h5 : m.body.all (fun s => match s with
      | .inst mn _ cs => connsOkS d m mn cs
      | _ => true) = true := by
    simp only [HierShapeS, Bool.and_eq_true] at h
    exact h.1.1.1.2
  exact List.all_eq_true.mp h5 _ hin

/-- What `connsOkS` gives about the resolved child and the connections. -/
theorem connsOkS_facts {d : Design} {m : Module} {mn : String} {cs : List (String × Expr)}
    (h : connsOkS d m mn cs = true) :
    ∃ c, findMod d mn = some c ∧ c.isPrimitive = false ∧ leafBody c.body = true ∧
      childSane c = true ∧ (inNames c).Nodup ∧ c.outputs.length = 1 ∧
      cs.all (fun p => (c.inputs ++ c.outputs).any (·.name == p.1)) = true ∧
      (∀ p ∈ c.inputs ++ c.outputs, ∃ q ∈ cs, q.1 = p.name) ∧
      (∀ q ∈ cs, ∃ x, q.2 = Expr.ref x) := by
  simp only [connsOkS] at h
  cases hf : findMod d mn with
  | none => simp [hf] at h
  | some c =>
    simp only [hf, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hp, _⟩, _⟩, hl⟩, hsane⟩, hol⟩, _⟩, hcov⟩, hall2⟩, hrefs⟩ := h
    refine ⟨c, rfl, hp, hl, hsane, ?_, hol, hall2, ?_, ?_⟩
    · have := hsane
      simp only [childSane, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1.1
    · intro p hp
      have := List.all_eq_true.mp hcov p hp
      obtain ⟨q, hq, hqe⟩ := List.any_eq_true.mp this
      exact ⟨q, hq, by simpa using hqe⟩
    · intro q hq
      have := List.all_eq_true.mp hrefs q hq
      cases hq2 : q.2 with
      | ref x => exact ⟨x, rfl⟩
      | _ => simp [hq2] at this

/-! ## Step success -/

theorem lookup_some_of_mem {cs : List (String × Expr)} {name : String}
    (h : ∃ q ∈ cs, q.1 = name) : ∃ e, cs.lookup name = some e := by
  obtain ⟨q, hq, hqe⟩ := h
  induction cs with
  | nil => cases hq
  | cons y ys ih =>
    by_cases hy : (name == y.1) = true
    · exact ⟨y.2, by simp [List.lookup, hy]⟩
    · have hq' : q ∈ ys := by
        rcases List.mem_cons.mp hq with rfl | h
        · exact absurd (by simp [hqe]) hy
        · exact h
      obtain ⟨e, he⟩ := ih hq'
      exact ⟨e, by simp [List.lookup, hy, he]⟩

theorem mapM_some_of_forall {α β : Type} (f : α → Option β) :
    ∀ l : List α, (∀ x ∈ l, ∃ y, f x = some y) → ∃ ys, l.mapM f = some ys := by
  intro l
  induction l with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons a rest ih =>
    intro h
    obtain ⟨y, hy⟩ := h a (List.mem_cons_self ..)
    obtain ⟨ys, hys⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨y :: ys, by rw [List.mapM_cons, hy, hys]; rfl⟩

/-- The child's input seed exists when every input port is connected to a `ref`. -/
theorem childSeed_some (c : Module) (cs : List (String × Expr)) (we : WEnv) (env : Env)
    (hin : ∀ p ∈ c.inputs, ∃ q ∈ cs, q.1 = p.name) (href : ∀ q ∈ cs, ∃ x, q.2 = Expr.ref x) :
    ∃ e, childSeed c cs we env = some e := by
  unfold childSeed
  have : ∃ l, (c.inputs.mapM fun (p : Port) => do
      let e ← cs.lookup p.name
      let v ← evalExpr we env e
      pure (p.name, v)) = some l := by
    apply mapM_some_of_forall
    intro p hp
    obtain ⟨e, he⟩ := lookup_some_of_mem (hin p hp)
    obtain ⟨x, hx⟩ := href _ (lookup_mem _ _ _ he)
    simp only at hx
    exact ⟨(p.name, env x), by simp [he, hx, evalExpr]⟩
  obtain ⟨l, hl⟩ := this
  exact ⟨_, by rw [hl]; rfl⟩

theorem outWrites_some (c : Module) (cs : List (String × Expr)) (envC : Env)
    (href : ∀ q ∈ cs, ∃ x, q.2 = Expr.ref x) : ∃ l, outWrites c cs envC = some l := by
  unfold outWrites
  apply mapM_some_of_forall
  intro p hp
  obtain ⟨x, hx⟩ := href p (List.mem_filter.mp hp).1
  exact ⟨(x, envC p.1), by simp [hx]⟩

/-- Success of a leaf body's combinational fold does not depend on the seed. -/
theorem evalAssigns_succ_leaf (we : WEnv) (mems : MEnv) (b : List Stmt) (hb : leafBody b = true)
    (env E : Env) (h : evalAssigns we mems b env = some E) :
    ∀ env', ∃ E', evalAssigns we mems b env' = some E' := by
  intro env'
  rw [← evalAssignsI_leaf we (fun _ _ _ _ => none) mems b env hb] at h
  obtain ⟨E', hE'⟩ := evalAssignsI_succ we (fun _ _ _ _ => none) b env E hb h env'
  exact ⟨E', by rw [← evalAssignsI_leaf we (fun _ _ _ _ => none) mems b env' hb]; exact hE'⟩

/-- Success of a leaf body's register phase does not depend on the environment. -/
theorem regNexts_succ_leaf (we : WEnv) (mems : MEnv) :
    ∀ (b : List Stmt) (env : Env) (l : List (String × Nat)), leafBody b = true →
      regNexts we mems b env = some l → ∀ env', ∃ l', regNexts we mems b env' = some l' := by
  intro b
  induction b with
  | nil => intro env l _ _ env'; exact ⟨[], rfl⟩
  | cons s rest ih =>
    intro env l hl h env'
    cases s with
    | assign x r =>
      simp only [leafBody] at hl
      simp only [regNexts] at h ⊢
      exact ih env l hl h env'
    | register o c r e i =>
      obtain ⟨rn, rk⟩ := r
      simp only [leafBody] at hl
      simp only [regNexts] at h
      cases hv : evalExpr we env e with
      | none => simp [hv] at h
      | some v =>
        cases hn : regNexts we mems rest env with
        | none => simp [hv, hn] at h
        | some nx =>
          obtain ⟨v', hv'⟩ := evalExpr_env_some we env env' e v hv
          obtain ⟨nx', hnx'⟩ := ih env nx hl hn env'
          exact ⟨(o, if env' rn ≠ 0 then encodeInit i (we o) else mask (we o) v') :: nx',
            by simp [regNexts, hv', hnx']⟩
    | memory _ _ _ _ _ _ _ _ _ _ _ _ => simp [leafBody] at hl
    | inst _ _ _ => simp [leafBody] at hl

/-- A child's one cycle succeeds at some point (hence, for a leaf body, at every point). -/
def ChildSucc (c : Module) (b : List Stmt) : Prop :=
  ∃ seed E nx, evalAssigns (declWidth c) (fun _ _ => 0) b seed = some E ∧
    regNexts (declWidth c) (fun _ _ => 0) b E = some nx

/-- THE CHILD'S REAL THEOREM SUPPLIES `ChildSucc`: the child's `OutputsOn` (K = 1, the all-0
input stream, which is in range with reset 0) gives a successful cycle from the initial state. -/
theorem childSucc_of_outputsOn (cc : Contract) (cm : Module) (b : List Stmt) (g : cc.table.Ty)
    (hout : OutputsOn cc cm b g) : ChildSucc cm b := by
  have hok : InputsOk cc cm (fun _ _ => 0) := by
    refine ⟨fun t p _ => Nat.two_pow_pos _, fun t kr _ => rfl⟩
  obtain ⟨envs, hrun, _⟩ := hout _ hok 1
  unfold runModule at hrun
  cases hs : stepModule (declWidth cm) b (seedFwd cm 1 (fun _ _ => 0) 0 (st0 cc cm)) (fun _ _ => 0) with
  | none => simp [hs] at hrun
  | some r =>
    obtain ⟨e, nx, mm⟩ := r
    unfold stepModule at hs
    cases hv : evalAssigns (declWidth cm) (fun _ _ => 0) b (seedFwd cm 1 (fun _ _ => 0) 0 (st0 cc cm)) with
    | none => simp [hv] at hs
    | some E =>
      cases hn : regNexts (declWidth cm) (fun _ _ => 0) b E with
      | none => simp [hv, hn] at hs
      | some N => exact ⟨_, E, N, hv, hn⟩

/-- Support of the top's expressions: every assign and register input evaluates (at the all-0
environment, hence at every environment). -/
def StmtSupp (we : WEnv) : Stmt → Bool
  | .assign _ r => (evalExpr we (fun _ => 0) r).isSome
  | .register _ _ _ e _ => (evalExpr we (fun _ => 0) e).isSome
  | _ => true

def ExprsSupp (m : Module) (b : List Stmt) : Prop := ∀ s ∈ b, StmtSupp (declWidth m) s = true

theorem evalExpr_isSome_any (we : WEnv) (r : Expr) (h : (evalExpr we (fun _ => 0) r).isSome)
    (env : Env) : ∃ v, evalExpr we env r = some v := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  exact evalExpr_env_some we _ env r v hv

theorem regNexts_succ_supp (m : Module) (mems : MEnv) :
    ∀ (b : List Stmt), (∀ s ∈ b, isAsgInstReg s = true) → ExprsSupp m b →
      ∀ env, ∃ l, regNexts (declWidth m) mems b env = some l := by
  intro b
  induction b with
  | nil => intro _ _ env; exact ⟨[], rfl⟩
  | cons s rest ih =>
    intro hb hs env
    have hrest := ih (fun x hx => hb x (List.mem_cons_of_mem _ hx))
      (fun x hx => hs x (List.mem_cons_of_mem _ hx)) env
    obtain ⟨l, hl⟩ := hrest
    cases s with
    | assign x r => exact ⟨l, by simpa [regNexts] using hl⟩
    | inst _ _ _ => exact ⟨l, by simpa [regNexts] using hl⟩
    | register o c r e i =>
      obtain ⟨rn, rk⟩ := r
      have := hs _ (List.mem_cons_self ..)
      simp only [StmtSupp] at this
      obtain ⟨v, hv⟩ := evalExpr_isSome_any _ e this env
      exact ⟨(o, if env rn ≠ 0 then encodeInit i (declWidth m o) else mask (declWidth m o) v) :: l,
        by simp [regNexts, hv, hl]⟩
    | memory _ _ _ _ _ _ _ _ _ _ _ _ => have := hb _ (List.mem_cons_self ..); simp [isAsgInstReg] at this

/-- The instance evaluator succeeds on any environment: the child's success from the child's
own theorem, the wiring from `connsOkS`. -/
theorem instEvalS_succ {d : Design} {m : Module} (arr : Module → List Stmt) (st : HSt) (we : WEnv)
    (mn i : String) (cs : List (String × Expr)) (hok : connsOkS d m mn cs = true)
    (hsucc : ∀ c, findMod d mn = some c → ChildSucc c (arr c))
    (hleafArr : ∀ c, findMod d mn = some c → leafBody (arr c) = true) (env : Env) :
    ∃ l, instEvalS d arr st we mn i cs env = some l := by
  obtain ⟨c, hf, hprim, hleaf, hsane, hnd, hol, hall, hcov, href⟩ := connsOkS_facts hok
  have hinok : instOkS c cs = true := by
    unfold instOkS; rw [hprim, hleaf, hall]; rfl
  obtain ⟨seed0, E0, nx0, hE0, hN0⟩ := hsucc c hf
  have hleafA := hleafArr c hf
  obtain ⟨e, he⟩ := childSeed_some c cs we env (fun p hp => hcov p (List.mem_append_left _ hp)) href
  obtain ⟨E', hE'⟩ := evalAssigns_succ_leaf _ _ _ hleafA seed0 E0 hE0
    (fun n => if (regOuts (arr c)).contains n && !(inNames c).contains n then st [i] n else e n)
  obtain ⟨l, hl⟩ := outWrites_some c cs E' href
  refine ⟨l, ?_⟩
  unfold instEvalS
  simp only [hf, hinok, if_true]
  have : childRunS arr we c cs env (st [i]) = some E' := by
    simp only [childRunS, childSeedS, he, Option.map_some, Option.bind_some]
    exact hE'
  simp only [this, Option.bind_some]
  exact hl

theorem leafBody_iff : ∀ b : List Stmt, leafBody b = true ↔
    ∀ s ∈ b, (∃ l r, s = Stmt.assign l r) ∨ (∃ o c r e i, s = Stmt.register o c r e i) := by
  intro b
  induction b with
  | nil => simp [leafBody]
  | cons s rest ih =>
    cases s with
    | assign l r =>
      simp only [leafBody, ih, List.mem_cons, forall_eq_or_imp]
      constructor
      · intro h; exact ⟨Or.inl ⟨l, r, rfl⟩, h⟩
      · intro h; exact h.2
    | register o c r e i =>
      simp only [leafBody, ih, List.mem_cons, forall_eq_or_imp]
      constructor
      · intro h; exact ⟨Or.inr ⟨o, c, r, e, i, rfl⟩, h⟩
      · intro h; exact h.2
    | memory _ _ _ _ _ _ _ _ _ _ _ _ =>
      simp only [leafBody, Bool.false_eq_true, false_iff]
      intro h
      rcases h _ (List.mem_cons_self ..) with ⟨l, r, h⟩ | ⟨o, c, r, e, i, h⟩ <;> cases h
    | inst _ _ _ =>
      simp only [leafBody, Bool.false_eq_true, false_iff]
      intro h
      rcases h _ (List.mem_cons_self ..) with ⟨l, r, h⟩ | ⟨o, c, r, e, i, h⟩ <;> cases h

theorem leafBody_perm {b b' : List Stmt} (hp : b.Perm b') (h : leafBody b = true) :
    leafBody b' = true := by
  rw [leafBody_iff] at h ⊢
  exact fun s hs => h s (hp.mem_iff.mpr hs)

/-- One child's cycle exists in any enclosing environment and on any state slice. -/
theorem childRun_succ (arr : Module → List Stmt) (we : WEnv) (c : Module) (cs : List (String × Expr))
    (env : Env) (stc : String → Nat)
    (hin : ∀ p ∈ c.inputs, ∃ q ∈ cs, q.1 = p.name) (href : ∀ q ∈ cs, ∃ x, q.2 = Expr.ref x)
    (hsucc : ChildSucc c (arr c)) (hleaf : leafBody (arr c) = true) :
    ∃ envC nx, childRunS arr we c cs env stc = some envC ∧
      regNexts (declWidth c) (fun _ _ => 0) (arr c) envC = some nx := by
  obtain ⟨seed0, E0, nx0, hE0, hN0⟩ := hsucc
  obtain ⟨e, he⟩ := childSeed_some c cs we env hin href
  obtain ⟨E', hE'⟩ := evalAssigns_succ_leaf _ _ _ hleaf seed0 E0 hE0
    (fun n => if (regOuts (arr c)).contains n && !(inNames c).contains n then stc n else e n)
  obtain ⟨nx', hnx'⟩ := regNexts_succ_leaf _ _ _ E0 nx0 hleaf hN0 E'
  refine ⟨E', nx', ?_, hnx'⟩
  simp only [childRunS, childSeedS, he, Option.map_some, Option.bind_some]
  exact hE'

theorem evalAssignsI_succ_S (m : Module) (ie : InstEval) :
    ∀ (b : List Stmt) (env : Env), (∀ s ∈ b, isAsgInstReg s = true) → ExprsSupp m b →
      (∀ mn i cs, Stmt.inst mn i cs ∈ b → ∀ e, ∃ l, ie mn i cs e = some l) →
      ∃ E, evalAssignsI (declWidth m) ie b env = some E := by
  intro b
  induction b with
  | nil => intro env _ _ _; exact ⟨env, rfl⟩
  | cons s rest ih =>
    intro env hb hs hi
    have hl : ∃ l, cellVals (declWidth m) ie s env = some l := by
      cases s with
      | assign x r =>
        have := hs _ (List.mem_cons_self ..)
        simp only [StmtSupp] at this
        obtain ⟨v, hv⟩ := evalExpr_isSome_any _ r this env
        exact ⟨[(x, v)], by simp [cellVals, hv]⟩
      | register _ _ _ _ _ => exact ⟨[], rfl⟩
      | inst mn i cs => exact hi mn i cs (List.mem_cons_self ..) env
      | memory _ _ _ _ _ _ _ _ _ _ _ _ =>
        have := hb _ (List.mem_cons_self ..); simp [isAsgInstReg] at this
    obtain ⟨l, hl⟩ := hl
    obtain ⟨E, hE⟩ := ih (upd env l) (fun x hx => hb x (List.mem_cons_of_mem _ hx))
      (fun x hx => hs x (List.mem_cons_of_mem _ hx))
      (fun mn i cs hm e => hi mn i cs (List.mem_cons_of_mem _ hm) e)
    exact ⟨E, by simp [evalAssignsI, hl, hE]⟩

/-- STEP SUCCESS (§2.5, reviewer obligation 1), from any state and any seed.  The conditions are
EXPLICIT: the shape (`HierShapeS`, which carries the wiring and `clkRstOk`), the admissible
arrangements, `ExprsSupp` for the top's expressions and `ChildSucc` for each child (supplied by the
child's real theorem, `childSucc_of_outputsOn`).  Nothing is read from the hierarchical run. -/
theorem stepHS_succ (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeS d m = true) (hA : AdmArr d m arr) (hsupp : ExprsSupp m (arr m))
    (hch : ∀ c ∈ d.modules, ChildSucc c (arr c)) (st : HSt) (env0 : Env) :
    ∃ r, stepHS d arr m st env0 = some r := by
  have hmem : ∀ s, s ∈ arr m → s ∈ m.body := fun s hs => hA.1.mem_iff.mp hs
  have hai : ∀ s ∈ arr m, isAsgInstReg s = true := fun s hs => hierS_body hS s (hmem s hs)
  have hinst : ∀ mn i cs, Stmt.inst mn i cs ∈ arr m → ∃ c, findMod d mn = some c ∧
      leafBody (arr c) = true ∧ (∀ p ∈ c.inputs, ∃ q ∈ cs, q.1 = p.name) ∧
      (∀ q ∈ cs, ∃ x, q.2 = Expr.ref x) ∧ ChildSucc c (arr c) ∧ instOkS c cs = true := by
    intro mn i cs hin
    obtain ⟨c, hf, hprim, hleaf, hsane, hnd, hol, hall, hcov, href⟩ :=
      connsOkS_facts (hierS_inst_ok hS (hmem _ hin))
    refine ⟨c, hf, leafBody_perm (hA.2.2 c (findMod_mem hf)).1.symm hleaf,
      fun p hp => hcov p (List.mem_append_left _ hp), href, hch c (findMod_mem hf), ?_⟩
    unfold instOkS; rw [hprim, hleaf, hall]; rfl
  have hfold : ∃ E, evalAssignsI (declWidth m) (instEvalS d arr st (declWidth m)) (arr m) env0 = some E := by
    apply evalAssignsI_succ_S m _ _ _ hai hsupp
    intro mn i cs hin e
    obtain ⟨c, hf, hleaf, hin', href, hsucc, hok⟩ := hinst mn i cs hin
    obtain ⟨envC, nx, hr, _⟩ := childRun_succ arr (declWidth m) c cs e (st [i]) hin' href hsucc hleaf
    obtain ⟨l, hl⟩ := outWrites_some c cs envC href
    exact ⟨l, by simp [instEvalS, hf, hok, hr, hl]⟩
  obtain ⟨E, hE⟩ := hfold
  obtain ⟨nxP, hnxP⟩ := regNexts_succ_supp m (fun _ _ => 0) (arr m) hai hsupp E
  have hkids : ∃ ys, (instDecls (arr m)).mapM (childNexts d arr (declWidth m) st E) = some ys := by
    apply mapM_some_of_forall
    rintro ⟨mn, i, cs⟩ hx
    obtain ⟨c, hf, hleaf, hin', href, hsucc, hok⟩ := hinst mn i cs ((mem_instDecls_iff _ _).mp hx)
    obtain ⟨envC, nx, hr, hn⟩ := childRun_succ arr (declWidth m) c cs E (st [i]) hin' href hsucc hleaf
    exact ⟨_, childNexts_some d arr (declWidth m) st E mn i cs c envC nx hf hok hr hn⟩
  obtain ⟨ys, hys⟩ := hkids
  exact ⟨(E, ([], nxP) :: ys), by simp [stepHS, hierS_clk hS, hE, hnxP, hys]⟩

/-- EXISTENCE OF THE HIERARCHICAL RUN, by cycle induction (every cycle's step succeeds from every
state and seed, so the state threads through): for every `K`, every seed discipline and every
state a run exists. -/
theorem runHS_exists (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeS d m = true) (hA : AdmArr d m arr) (hsupp : ExprsSupp m (arr m))
    (hch : ∀ c ∈ d.modules, ChildSucc c (arr c)) (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : HSt), ∃ envs sts, runHSTrace d arr m seed k st = some (envs, sts) := by
  intro k
  induction k with
  | zero => intro st; exact ⟨[], [], rfl⟩
  | succ k ih =>
    intro st
    obtain ⟨⟨envF, ups⟩, hr⟩ := stepHS_succ d arr m hS hA hsupp hch st
      (seed k (restrictTo (regOuts (arr m)) (st [])))
    obtain ⟨envs, sts, hrest⟩ := ih (applyH st ups)
    exact ⟨envF :: envs, st :: sts, by simp [runHSTrace, hr, hrest]⟩

end Tools.VedU2Hier
