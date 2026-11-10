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
      childSane c = true ∧ (inNames c).Nodup ∧ c.outputs.length = 1 ∧ (cs.map (·.1)).Nodup ∧
      cs.all (fun p => (c.inputs ++ c.outputs).any (·.name == p.1)) = true ∧
      (∀ p ∈ c.inputs ++ c.outputs, ∃ q ∈ cs, q.1 = p.name) ∧
      (∀ q ∈ cs, ∃ x, q.2 = Expr.ref x) := by
  simp only [connsOkS] at h
  cases hf : findMod d mn with
  | none => simp [hf] at h
  | some c =>
    simp only [hf, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hp, _⟩, _⟩, hl⟩, hsane⟩, hol⟩, hcsnd⟩, hcov⟩, hall2⟩, hrefs⟩ := h
    refine ⟨c, rfl, hp, hl, hsane, ?_, hol, hcsnd, hall2, ?_, ?_⟩
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
  obtain ⟨c, hf, hprim, hleaf, hsane, hnd, hol, hcsnd, hall, hcov, href⟩ := connsOkS_facts hok
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
    obtain ⟨c, hf, hprim, hleaf, hsane, hnd, hol, hcsnd, hall, hcov, href⟩ :=
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

/-! ## Projection: helper lemmas -/

theorem restrict_applyNexts (names : List String) (s : String → Nat) (nx : List (String × Nat))
    (h : ∀ p ∈ nx, p.1 ∈ names) :
    restrictTo names (applyNexts s nx) = applyNexts (restrictTo names s) nx := by
  funext n
  by_cases hn : n ∈ names
  · simp only [restrictTo, applyNexts, List.contains_eq_mem, decide_eq_true_eq, hn, if_true]
  · have : nx.find? (fun p => p.1 == n) = none := by
      rw [List.find?_eq_none]
      intro p hp
      have := h p hp
      simp only [beq_iff_eq]
      exact fun e => hn (e ▸ this)
    simp [restrictTo, applyNexts, hn, this]

theorem instNames_filterMap (b : List Stmt) :
    instNames b = b.filterMap (fun s => match s with | .inst _ i _ => some i | _ => none) := by
  induction b with
  | nil => rfl
  | cons s rest ih => cases s <;> simp [instNames, ih]

theorem instNames_perm {b b' : List Stmt} (hp : b.Perm b') : (instNames b).Perm (instNames b') := by
  rw [instNames_filterMap, instNames_filterMap]
  exact hp.filterMap _

theorem mapM_fst_eq {α β γ : Type} (f : α → Option β) (g : β → γ) (h : α → γ)
    (hf : ∀ a b, f a = some b → g b = h a) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys → ys.map g = l.map h := by
  intro l
  induction l with
  | nil => intro ys hy; simp at hy; subst hy; rfl
  | cons a rest ih =>
    intro ys hy
    obtain ⟨b, rs, hb, hr, rfl⟩ := (mapM_cons_some _ _ _ _).mp hy
    simp [hf a b hb, ih rs hr]

theorem mapM_mem_ex {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys → ∀ a ∈ l, ∃ b ∈ ys, f a = some b := by
  intro l
  induction l with
  | nil => intro ys _ a ha; cases ha
  | cons a0 rest ih =>
    intro ys hy a ha
    obtain ⟨b, rs, hb, hr, rfl⟩ := (mapM_cons_some _ _ _ _).mp hy
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, List.mem_cons_self .., hb⟩
    · obtain ⟨b', hb', h'⟩ := ih rs hr a ha
      exact ⟨b', List.mem_cons_of_mem _ hb', h'⟩

theorem find_ups : ∀ (ups : Ups), (ups.map (·.1)).Nodup → ∀ u ∈ ups,
    ups.find? (fun v => v.1 == u.1) = some u := by
  intro ups
  induction ups with
  | nil => intro _ u hu; cases hu
  | cons y ys ih =>
    intro hnd u hu
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hu with rfl | hm
    · simp [List.find?_cons]
    · have hne : y.1 ≠ u.1 := fun e => hnd.1 (List.mem_map.mpr ⟨u, hm, e.symm⟩)
      simp [List.find?_cons, hne, ih hnd.2 u hm]

theorem applyH_at (st : HSt) (ups : Ups) (hnd : (ups.map (·.1)).Nodup) (u : Path × List (String × Nat))
    (hu : u ∈ ups) : applyH st ups u.1 = applyNexts (st u.1) u.2 := by
  funext n
  unfold applyH
  rw [find_ups ups hnd u hu]

theorem lookup_of_mem_nodup {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (L : List (α × β)), (L.map Prod.fst).Nodup → ∀ a v, (a, v) ∈ L → L.lookup a = some v := by
  intro L
  induction L with
  | nil => intro _ a v h; cases h
  | cons y ys ih =>
    intro hnd a v h
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h with rfl | hm
    · simp [List.lookup]
    · have hne : y.1 ≠ a := fun e => hnd.1 (List.mem_map.mpr ⟨(a, v), hm, e.symm⟩)
      have hb : (a == y.1) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
      simp [List.lookup, hb, ih hnd.2 a v hm]

theorem lookup_none_of_not_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (L : List (α × β)) (a : α), a ∉ L.map Prod.fst → L.lookup a = none := by
  intro L
  induction L with
  | nil => intro _ _; rfl
  | cons y ys ih =>
    intro a h
    rw [List.map_cons, List.mem_cons, not_or] at h
    have hb : (a == y.1) = false := beq_eq_false_iff_ne.mpr h.1
    simp [List.lookup, hb, ih a h.2]

/-- The shape of the input-seed list `childSeed` builds. -/
theorem mapM_ports_spec (cs : List (String × Expr)) (we : WEnv) (env : Env) :
    ∀ (ports : List Port) (L : List (String × Nat)),
      (ports.mapM fun (p : Port) => do
          let e ← cs.lookup p.name
          let v ← evalExpr we env e
          pure (p.name, v)) = some L →
      L.map Prod.fst = ports.map (·.name) ∧
      ∀ p ∈ ports, ∃ ex v, cs.lookup p.name = some ex ∧ evalExpr we env ex = some v ∧ (p.name, v) ∈ L := by
  intro ports
  induction ports with
  | nil => intro L h; simp at h; subst h; exact ⟨rfl, fun p hp => by cases hp⟩
  | cons p rest ih =>
    intro L h
    obtain ⟨b, rs, hb, hr, rfl⟩ := (mapM_cons_some _ _ _ _).mp h
    obtain ⟨ih1, ih2⟩ := ih rs hr
    cases hl : cs.lookup p.name with
    | none => simp [hl] at hb
    | some ex =>
      cases hv : evalExpr we env ex with
      | none => simp [hl, hv] at hb
      | some v =>
        simp [hl, hv] at hb
        subst hb
        refine ⟨by simp [ih1], ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨ex, v, hl, hv, List.mem_cons_self ..⟩
        · obtain ⟨ex', v', h1, h2, h3⟩ := ih2 q hq
          exact ⟨ex', v', h1, h2, List.mem_cons_of_mem _ h3⟩

theorem childSeed_val (c : Module) (cs : List (String × Expr)) (we : WEnv) (env e0 : Env)
    (h : childSeed c cs we env = some e0) (hnd : (inNames c).Nodup) :
    (∀ n, n ∉ inNames c → e0 n = 0) ∧
    (∀ p ∈ c.inputs, ∃ ex, cs.lookup p.name = some ex ∧ evalExpr we env ex = some (e0 p.name)) := by
  unfold childSeed at h
  obtain ⟨L, hm, hL⟩ := Option.map_eq_some_iff.mp h
  subst hL
  · obtain ⟨hfst, hmem⟩ := mapM_ports_spec cs we env c.inputs L hm
    have hLnd : (L.map Prod.fst).Nodup := by rw [hfst]; exact hnd
    refine ⟨?_, ?_⟩
    · intro n hn
      have : L.lookup n = none := lookup_none_of_not_mem L n (by rw [hfst]; exact hn)
      simp [this]
    · intro p hp
      obtain ⟨ex, v, h1, h2, h3⟩ := hmem p hp
      refine ⟨ex, h1, ?_⟩
      simp [lookup_of_mem_nodup L hLnd _ _ h3, h2]

/-- An assignment fold keeps every name no assignment writes. -/
theorem evalAssigns_keeps (we : WEnv) (mems : MEnv) (n : String) :
    ∀ (b : List Stmt) (env E : Env),
      (∀ s ∈ b, ∀ l r, s = Stmt.assign l r → l ≠ n) → leafBody b = true →
      evalAssigns we mems b env = some E → E n = env n := by
  intro b
  induction b with
  | nil => intro env E _ _ h; simp [evalAssigns] at h; subst h; rfl
  | cons s rest ih =>
    intro env E hw hl h
    cases s with
    | assign l r =>
      simp only [leafBody] at hl
      simp only [evalAssigns] at h
      cases hv : evalExpr we env r with
      | none => simp [hv] at h
      | some v =>
        simp only [hv, Option.bind_some] at h
        have := ih _ E (fun s hs => hw s (List.mem_cons_of_mem _ hs)) hl h
        rw [this]
        have hne := hw _ (List.mem_cons_self ..) l r rfl
        simp [hne.symm]
    | register o c r e i =>
      simp only [leafBody] at hl
      simp only [evalAssigns] at h
      exact ih _ E (fun s hs => hw s (List.mem_cons_of_mem _ hs)) hl h
    | memory _ _ _ _ _ _ _ _ _ _ _ _ => simp [leafBody] at hl
    | inst _ _ _ => simp [leafBody] at hl

theorem outWrites_mem (c : Module) (cs : List (String × Expr)) (envC : Env) (l : List (String × Nat))
    (h : outWrites c cs envC = some l) (qn x : String) (hq : (qn, Expr.ref x) ∈ cs)
    (ho : c.outputs.any (·.name == qn) = true) : (x, envC qn) ∈ l := by
  unfold outWrites at h
  obtain ⟨b, hb, hfb⟩ := mapM_mem_ex _ _ _ h (qn, Expr.ref x) (List.mem_filter.mpr ⟨hq, by simpa using ho⟩)
  simp at hfb
  subst hfb
  exact hb

theorem runModuleTrace_congr_seed (we : WEnv) (body : List Stmt) (seed1 seed2 : Nat → (String → Nat) → Env) :
    ∀ (k : Nat), (∀ j, j < k → seed1 j = seed2 j) →
      ∀ (st : String → Nat) (mems : MEnv),
        runModuleTrace we body seed1 k st mems = runModuleTrace we body seed2 k st mems := by
  intro k
  induction k with
  | zero => intro _ st mems; rfl
  | succ k ih =>
    intro h st mems
    simp only [runModuleTrace]
    rw [h k (Nat.lt_succ_self k)]
    cases stepModule we body (seed2 k st) mems with
    | none => rfl
    | some r =>
      obtain ⟨e, nx, mm⟩ := r
      have hi := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
      simp [hi]

/-! ## Projection -/

/-- The child's input stream: the connection expressions evaluated in the parent's cycle
environments (value 0 outside the trace; the lemma below never reads outside it). -/
def insCOf (we : WEnv) (cs : List (String × Expr)) (envs : List Env) : Nat → String → Nat :=
  fun t n =>
    match envs[t]?, cs.lookup n with
    | some E, some e => (evalExpr we E e).getD 0
    | _, _ => 0

/-- The three correspondences at ONE cycle, kept apart:
* INPUT ports: the child's input value is the connection evaluated in the PARENT's environment;
* OUTPUT ports: the parent wire an output is connected to holds the child's output value;
* REGISTERS: the child's registers are the hierarchical state's slice `[i]`, held in the
  auxiliary child state history.
Nothing is said about any other name of the child's environment. -/
def ProjAt (we : WEnv) (c : Module) (cs : List (String × Expr)) (i : String)
    (E Ec : Env) (S : HSt) (Sc : String → Nat) : Prop :=
  (∀ p ∈ c.inputs, ∃ e, cs.lookup p.name = some e ∧ evalExpr we E e = some (Ec p.name)) ∧
  (∀ q ∈ c.outputs, ∃ x, cs.lookup q.name = some (Expr.ref x) ∧ E x = Ec q.name) ∧
  (∀ r ∈ regOuts c.body, S [i] r = Sc r)

theorem childNexts_fst (d : Design) (arr : Module → List Stmt) (we : WEnv) (st : HSt) (envF : Env)
    (x : String × String × List (String × Expr)) (y : Path × List (String × Nat))
    (h : childNexts d arr we st envF x = some y) : y.1 = [x.2.1] := by
  obtain ⟨mn, i, cs⟩ := x
  unfold childNexts at h
  cases hf : findMod d mn with
  | none => simp [hf] at h
  | some c =>
    simp only [hf] at h
    by_cases hok : instOkS c cs = true
    · simp only [hok, if_true] at h
      cases hr : childRunS arr we c cs envF (st [i]) with
      | none => simp [hr] at h
      | some envC =>
        cases hn : regNexts (declWidth c) (fun _ _ => 0) (arr c) envC with
        | none => simp [hr, hn] at h
        | some nx => simp [hr, hn] at h; rw [← h]
    · simp [hok] at h

/-- Inverting a successful step. -/
theorem stepHS_some_inv {d : Design} {arr : Module → List Stmt} {m : Module} {st : HSt} {env0 envF : Env}
    {ups : Ups} (h : stepHS d arr m st env0 = some (envF, ups)) :
    clkRstOk d m = true ∧
    evalAssignsI (declWidth m) (instEvalS d arr st (declWidth m)) (arr m) env0 = some envF ∧
    ∃ nxP ys, regNexts (declWidth m) (fun _ _ => 0) (arr m) envF = some nxP ∧
      (instDecls (arr m)).mapM (childNexts d arr (declWidth m) st envF) = some ys ∧
      ups = ([], nxP) :: ys := by
  unfold stepHS at h
  by_cases hclk : clkRstOk d m = true
  · rw [if_pos hclk] at h
    cases hf : evalAssignsI (declWidth m) (instEvalS d arr st (declWidth m)) (arr m) env0 with
    | none => simp [hf] at h
    | some E =>
      cases hn : regNexts (declWidth m) (fun _ _ => 0) (arr m) E with
      | none => simp [hf, hn] at h
      | some nxP =>
        cases hk : (instDecls (arr m)).mapM (childNexts d arr (declWidth m) st E) with
        | none => simp [hf, hn, hk] at h
        | some ys =>
          simp [hf, hn, hk] at h
          obtain ⟨h1, h2⟩ := h
          subst h1; subst h2
          exact ⟨hclk, rfl, nxP, ys, hn, hk, rfl⟩
  · rw [if_neg hclk] at h; simp at h

theorem seedFwd_shift (c : Module) (we : WEnv) (cs : List (String × Expr)) (E : Env) (rest : List Env)
    (k j : Nat) (hj : j < k) :
    seedFwd c (k + 1) (insCOf we cs (E :: rest)) j = seedFwd c k (insCOf we cs rest) j := by
  funext st n
  simp only [seedFwd]
  have : k + 1 - 1 - j = (k - 1 - j) + 1 := by omega
  rw [this]
  simp [insCOf]

theorem childSeedS_inv (c : Module) (cs : List (String × Expr)) (we : WEnv) (env : Env)
    (regs : List String) (sti : String → Nat) (seedC : Env)
    (h : childSeedS c cs we env regs sti = some seedC) :
    ∃ e0, childSeed c cs we env = some e0 ∧
      seedC = fun n => if regs.contains n && !(inNames c).contains n then sti n else e0 n := by
  unfold childSeedS at h
  obtain ⟨e0, he0, hs⟩ := Option.map_eq_some_iff.mp h
  exact ⟨e0, he0, hs.symm⟩

/-- The child's standalone seed of the first cycle is the seed the hierarchical step built. -/
theorem seedFwd_first (c : Module) (we : WEnv) (cs : List (String × Expr)) (envF : Env)
    (rest : List Env) (k : Nat) (regs : List String) (sti : String → Nat) (seedC : Env)
    (hnd : (inNames c).Nodup)
    (hseed : childSeedS c cs we envF regs sti = some seedC) :
    seedFwd c (k + 1) (insCOf we cs (envF :: rest)) k (restrictTo regs sti) = seedC := by
  obtain ⟨e0, he0, hsc⟩ := childSeedS_inv c cs we envF regs sti seedC hseed
  obtain ⟨hz, hp⟩ := childSeed_val c cs we envF e0 he0 hnd
  funext n
  subst hsc
  simp only [seedFwd]
  have h0 : k + 1 - 1 - k = 0 := by omega
  rw [h0]
  by_cases hn : (inNames c).contains n = true
  · have hn' : (c.inputs.map (·.name)).contains n = true := hn
    have hmem : n ∈ inNames c := by simpa using hn
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hmem
    obtain ⟨ex, hl, hv⟩ := hp p hp'
    simp only [hn', if_true, hn, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false]
    simp [insCOf, hl, hv]
  · have hn' : (c.inputs.map (·.name)).contains n = false := by
      simpa [inNames] using hn
    have hnot : n ∉ inNames c := by simpa using hn
    simp only [hn', Bool.false_eq_true, if_false]
    have hn0 : (inNames c).contains n = false := by simpa using hn
    simp [restrictTo, hz n hnot, hnot]

theorem leafBody_assign_ne (c : Module) (b : List Stmt) (hperm : b.Perm c.body)
    (hsane : childSane c = true) (n : String) (hn : n ∈ inNames c) :
    ∀ s ∈ b, ∀ l r, s = Stmt.assign l r → l ≠ n := by
  intro s hs l r hsl hln
  subst hsl
  subst hln
  have hs' := hperm.mem_iff.mp hs
  simp only [childSane, Bool.and_eq_true] at hsane
  have := List.all_eq_true.mp hsane.1.2 _ hs'
  simp at this
  exact this hn

/-- THE PROJECTION (aux form: any start state, `k` cycles).  From a successful hierarchical run,
for every instance there is an EXISTENTIAL child trace `cenvs` with an auxiliary child state history
`cstates`: the child's standalone `runModuleTrace` on the input stream the connections produce
(`insCOf`), started from the child's state slice, succeeds, and at every cycle the three
correspondences of `ProjAt` hold. -/
theorem runHS_proj_aux (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeS d m = true) (hA : AdmArr d m arr)
    (mn i : String) (cs : List (String × Expr)) (c : Module)
    (hin : Stmt.inst mn i cs ∈ m.body) (hf : findMod d mn = some c) :
    ∀ (k : Nat) (seedK : Nat → (String → Nat) → Env) (st : HSt) (envs : List Env) (sts : List HSt),
      runHSTrace d arr m seedK k st = some (envs, sts) →
      ∃ cenvs cstates,
        runModuleTrace (declWidth c) (arr c) (seedFwd c k (insCOf (declWidth m) cs envs)) k
          (restrictTo (regOuts (arr c)) (st [i])) (fun _ _ => 0) = some (cenvs, cstates) ∧
        ∀ t, t < k → ∃ E Ec S Sc, envs[t]? = some E ∧ cenvs[t]? = some Ec ∧ sts[t]? = some S ∧
          cstates[t]? = some Sc ∧ ProjAt (declWidth m) c cs i E Ec S Sc := by
  have hmemM : Stmt.inst mn i cs ∈ arr m := hA.1.mem_iff.mpr hin
  obtain ⟨c0, hf0, hprim, hleaf, hsane, hnd, hol, hcsnd, hall, hcov, href⟩ :=
    connsOkS_facts (hierS_inst_ok hS hin)
  have hc : c = c0 := by rw [hf] at hf0; exact Option.some.inj hf0
  subst hc
  have hperm := (hA.2.2 c (findMod_mem hf)).1
  have hleafA := leafBody_perm hperm.symm hleaf
  have hinok : instOkS c cs = true := by unfold instOkS; rw [hprim, hleaf, hall]; rfl
  have hdecl : ((instDecls (arr m)).map (·.2.1)).Nodup := by
    rw [← instNames_eq]
    exact (instNames_perm hA.1).nodup_iff.mpr (hierS_inst_unique hS)
  intro k
  induction k with
  | zero =>
    intro seedK st envs sts hrun
    simp only [runHSTrace, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨[], [], rfl, fun t ht => absurd ht (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro seedK st envs sts hrun
    simp only [runHSTrace] at hrun
    cases hs : stepHS d arr m st (seedK k (restrictTo (regOuts (arr m)) (st []))) with
    | none => simp [hs] at hrun
    | some r =>
      obtain ⟨envF, ups⟩ := r
      cases hr : runHSTrace d arr m seedK k (applyH st ups) with
      | none => simp [hs, hr] at hrun
      | some q =>
        obtain ⟨rest, sts'⟩ := q
        simp [hs, hr] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        obtain ⟨_, hfold, nxP, ys, hnxP, hys, hups⟩ := stepHS_some_inv hs
        have hG := good_of_fold d (declWidth m) _ (instEvalS_laws d arr st (declWidth m)) (arr m) _
          envF hA.2.1 hfold
        obtain ⟨l, hl, hlE⟩ := hG.2 _ hmemM
        have hl' : instEvalS d arr st (declWidth m) mn i cs envF = some l := by simpa [cellVals] using hl
        obtain ⟨c', envC, hf', _, hrunC, hw⟩ := instEvalS_some hl'
        have hcc : c' = c := by rw [hf] at hf'; exact (Option.some.inj hf').symm
        subst hcc
        obtain ⟨y, hy, hyc⟩ := mapM_mem_ex _ _ _ hys (mn, i, cs) ((mem_instDecls_iff _ _).mpr hmemM)
        obtain ⟨nx, hnx, hyeq⟩ : ∃ nx, regNexts (declWidth c') (fun _ _ => 0) (arr c') envC = some nx ∧
            y = ([i], nx) := by
          unfold childNexts at hyc
          simp only [hf, hinok, if_true, hrunC, Option.bind_some] at hyc
          cases hn : regNexts (declWidth c') (fun _ _ => 0) (arr c') envC with
          | none => simp [hn] at hyc
          | some nx => simp [hn] at hyc; exact ⟨nx, rfl, hyc.symm⟩
        subst hyeq
        -- the paths of the updates are distinct
        have hpaths : ys.map (·.1) = (instDecls (arr m)).map (fun x => ([x.2.1] : Path)) :=
          mapM_fst_eq _ _ _ (fun x y h => childNexts_fst d arr (declWidth m) st envF x y h) _ _ hys
        have hupsnd : (ups.map (·.1)).Nodup := by
          rw [hups, List.map_cons, hpaths, List.nodup_cons]
          have h2 : (instDecls (arr m)).map (fun x => ([x.2.1] : Path)) =
              ((instDecls (arr m)).map (·.2.1)).map (fun a => [a]) := by
            simp [List.map_map, Function.comp_def]
          refine ⟨?_, ?_⟩
          · intro hmem
            obtain ⟨x, _, hx⟩ := List.mem_map.mp hmem
            exact absurd hx (List.cons_ne_nil _ _)
          · rw [h2]; exact hdecl.map (fun a => [a]) (fun a b h e => h (by simpa using e))
        have hstate : applyH st ups [i] = applyNexts (st [i]) nx :=
          applyH_at st ups hupsnd ([i], nx) (by rw [hups]; exact List.mem_cons_of_mem _ hy)
        have hnames : ∀ p ∈ nx, p.1 ∈ regOuts (arr c') := regNexts_fst_mem _ _ _ _ _ hleafA hnx
        have hstc' : applyNexts (restrictTo (regOuts (arr c')) (st [i])) nx =
            restrictTo (regOuts (arr c')) (applyH st ups [i]) := by
          rw [hstate, restrict_applyNexts _ _ _ hnames]
        obtain ⟨cenvs', cstates', hrunM', hcorr'⟩ := ih seedK (applyH st ups) rest sts' hr
        obtain ⟨seedC, hseedC, hevC⟩ : ∃ seedC, childSeedS c' cs (declWidth m) envF (regOuts (arr c'))
            (st [i]) = some seedC ∧ evalAssigns (declWidth c') (fun _ _ => 0) (arr c') seedC = some envC := by
          unfold childRunS at hrunC
          cases hh : childSeedS c' cs (declWidth m) envF (regOuts (arr c')) (st [i]) with
          | none => simp [hh] at hrunC
          | some sd => exact ⟨sd, rfl, by simpa [hh] using hrunC⟩
        have hseed1 := seedFwd_first c' (declWidth m) cs envF rest k (regOuts (arr c')) (st [i]) seedC
          hnd hseedC
        have hstepM : stepModule (declWidth c') (arr c')
            (seedFwd c' (k + 1) (insCOf (declWidth m) cs (envF :: rest)) k
              (restrictTo (regOuts (arr c')) (st [i]))) (fun _ _ => 0) =
            some (envC, nx, fun _ _ => 0) := by
          rw [hseed1]
          unfold stepModule
          simp [hevC, hnx, memNexts_leaf _ _ _ _ hleafA]
        refine ⟨envC :: cenvs', restrictTo (regOuts (arr c')) (st [i]) :: cstates', ?_, ?_⟩
        · simp only [runModuleTrace]
          rw [hstepM]
          have hcongr := runModuleTrace_congr_seed (declWidth c') (arr c')
            (seedFwd c' (k + 1) (insCOf (declWidth m) cs (envF :: rest)))
            (seedFwd c' k (insCOf (declWidth m) cs rest)) k
            (fun j hj => seedFwd_shift c' _ cs envF rest k j hj)
            (applyNexts (restrictTo (regOuts (arr c')) (st [i])) nx) (fun _ _ => 0)
          simp only [Option.bind_eq_bind, Option.bind_some]
          rw [hcongr, hstc', hrunM']
          rfl
        · intro t ht
          cases t with
          | succ t =>
            obtain ⟨E, Ec, S, Sc, h1, h2, h3, h4, h5⟩ := hcorr' t (by omega)
            exact ⟨E, Ec, S, Sc, by simpa using h1, by simpa using h2, by simpa using h3,
              by simpa using h4, h5⟩
          | zero =>
            refine ⟨envF, envC, st, restrictTo (regOuts (arr c')) (st [i]), rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
            · intro p hpm
              obtain ⟨e0, he0, hsc⟩ := childSeedS_inv c' cs (declWidth m) envF _ _ seedC hseedC
              obtain ⟨hz, hp⟩ := childSeed_val c' cs (declWidth m) envF e0 he0 hnd
              obtain ⟨ex, hl2, hv⟩ := hp p hpm
              have hpn : p.name ∈ inNames c' := List.mem_map.mpr ⟨p, hpm, rfl⟩
              have hkeep := evalAssigns_keeps (declWidth c') (fun _ _ => 0) p.name (arr c') seedC envC
                (leafBody_assign_ne c' (arr c') hperm hsane p.name hpn) hleafA hevC
              refine ⟨ex, hl2, ?_⟩
              rw [hv, hkeep, hsc]
              simp [hpn]
            · intro q hq
              obtain ⟨qq, hqq, hq1⟩ := hcov q (List.mem_append_right _ hq)
              obtain ⟨x, hx⟩ := href qq hqq
              have hqe : qq = (q.name, Expr.ref x) := by
                obtain ⟨a, b⟩ := qq; simp only at hq1 hx; subst hq1; subst hx; rfl
              rw [hqe] at hqq
              refine ⟨x, lookup_of_mem_nodup cs hcsnd _ _ hqq, ?_⟩
              have hmemo := outWrites_mem c' cs envC l hw q.name x hqq
                (List.any_eq_true.mpr ⟨q, hq, by simp⟩)
              exact hlE _ hmemo
            · intro r hr'
              have : r ∈ regOuts (arr c') := (regOuts_perm_mem hperm r).mpr hr'
              simp [restrictTo, this]

end Tools.VedU2Hier
