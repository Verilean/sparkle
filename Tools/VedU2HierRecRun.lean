import Tools.VedU2HierRecKid
import Tools.VedU2HierProj
import Tools.VedU2HierReg

/-!
# Run existence and the trace facts of the recursive statement (CANDIDATE; Tools/VedU2HierRec.lean)

* `runHSRTrace_cycle` / `runHSRTrace_next`: the per-cycle facts of a successful closed run (the
  analogues of `runHSTrace_cycle` / `runHSTrace_next`);
* `SuccF d arr k x`: the FUEL-INDEXED success predicate of a module (the analogue of `ChildSucc`):
  the module's expressions are supported (`ExprsSupp`) and each instance's child (resolved in `d`)
  succeeds at one fuel level less.  Success is then independent of the state slice, the seed and
  the enclosing environment (`combR_succ`, `upsR_succ`);
* `succF_of_step`: one successful cycle of a module (comb and ups, at fuel `k`) gives `SuccF d arr k`
  (this is where a child's own theorem supplies success: its `OutputsStmtHSR` at `K = 1`);
* `runHSR_exists`: the run exists from any state and any seed, from the shape, the admissible
  arrangement and `SuccF` of the top at `fuelR d`.
-/

namespace Tools.VedU2HierRec

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier

/-! ## Trace facts -/

theorem upsR_some_inv {d : Design} {arr : Module → List Stmt} {k : Nat} {m : Module} {st : HSt}
    {envF : Env} {ups : Ups} (h : upsR d arr (k + 1) m st envF = some ups) :
    ∃ nxP ys, regNexts (declWidth m) (fun _ _ => 0) (arr m) envF = some nxP ∧
      ups = ([], nxP) :: ys := by
  unfold upsR at h
  cases hP : regNexts (declWidth m) (fun _ _ => 0) (arr m) envF with
  | none => simp [hP] at h
  | some nx =>
    cases hm : (instDecls (arr m)).mapM
        (childUpsF d arr (combR d arr k) (upsR d arr k) (declWidth m) st envF) with
    | none => simp [hP, hm] at h
    | some l =>
      simp only [hP, hm, Option.bind_eq_bind, Option.bind, Option.some.injEq] at h
      exact ⟨nx, l.flatten, rfl, h.symm⟩

theorem runHSRTrace_cycle (d : Design) (arr : Module → List Stmt) (m : Module)
    (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : HSt) (envs : List Env) (sts : List HSt),
      runHSRTrace d arr m seed k st = some (envs, sts) →
      ∀ t, t < k → ∃ E S, envs[t]? = some E ∧ sts[t]? = some S ∧
        evalAssignsI (declWidth m)
          (instEvalF d arr (combR d arr (d.modules.length + 1)) S (declWidth m)) (arr m)
          (seed (k - 1 - t) (restrictTo (regOuts (arr m)) (S []))) = some E := by
  intro k
  induction k with
  | zero => intro st envs sts _ t ht; exact absurd ht (Nat.not_lt_zero _)
  | succ k ih =>
    intro st envs sts hrun t ht
    simp only [runHSRTrace] at hrun
    cases hs : stepHSR d arr m st (seed k (restrictTo (regOuts (arr m)) (st []))) with
    | none => simp [hs] at hrun
    | some r =>
      obtain ⟨envF, ups⟩ := r
      cases hr : runHSRTrace d arr m seed k (applyH st ups) with
      | none => simp [hs, hr] at hrun
      | some q =>
        obtain ⟨rest, sts'⟩ := q
        simp [hs, hr] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        cases t with
        | zero =>
          obtain ⟨_, hfold, _⟩ := stepHSR_some_inv hs
          exact ⟨envF, st, rfl, rfl, by simpa using hfold⟩
        | succ t =>
          obtain ⟨E, S, h1, h2, h3⟩ := ih (applyH st ups) rest sts' hr t (by omega)
          refine ⟨E, S, by simpa using h1, by simpa using h2, ?_⟩
          have : k + 1 - 1 - (t + 1) = k - 1 - t := by omega
          rw [this]; exact h3

theorem runHSRTrace_next (d : Design) (arr : Module → List Stmt) (m : Module)
    (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : HSt) (envs : List Env) (sts : List HSt),
      runHSRTrace d arr m seed k st = some (envs, sts) →
      (0 < k → sts[0]? = some st) ∧
      ∀ t, t + 1 < k → ∃ E S S' nx, envs[t]? = some E ∧ sts[t]? = some S ∧ sts[t + 1]? = some S' ∧
        regNexts (declWidth m) (fun _ _ => 0) (arr m) E = some nx ∧ S' [] = applyNexts (S []) nx := by
  intro k
  induction k with
  | zero =>
    intro st envs sts h
    exact ⟨fun h => absurd h (Nat.lt_irrefl _), fun t ht => absurd ht (by omega)⟩
  | succ k ih =>
    intro st envs sts hrun
    simp only [runHSRTrace] at hrun
    cases hs : stepHSR d arr m st (seed k (restrictTo (regOuts (arr m)) (st []))) with
    | none => simp [hs] at hrun
    | some r =>
      obtain ⟨envF, ups⟩ := r
      cases hr : runHSRTrace d arr m seed k (applyH st ups) with
      | none => simp [hs, hr] at hrun
      | some q =>
        obtain ⟨rest, sts'⟩ := q
        simp [hs, hr] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        obtain ⟨_, hfold, hupsR⟩ := stepHSR_some_inv hs
        obtain ⟨nxP, ys, hn, rfl⟩ := upsR_some_inv hupsR
        refine ⟨fun _ => rfl, ?_⟩
        intro t ht
        cases t with
        | zero =>
          obtain ⟨hs0, _⟩ := ih (applyH st (([], nxP) :: ys)) rest sts' hr
          have hk0 : 0 < k := by omega
          obtain ⟨S1, hS1⟩ : ∃ S1, sts'[0]? = some S1 := by
            cases sts' with
            | nil => simp at hs0 <;> omega
            | cons a _ => exact ⟨a, rfl⟩
          have := hs0 hk0
          rw [hS1] at this
          cases this
          exact ⟨envF, st, applyH st (([], nxP) :: ys), nxP, rfl, rfl, by simpa using hS1,
            hn, applyH_root_cons st nxP ys⟩
        | succ t =>
          obtain ⟨_, hrest⟩ := ih (applyH st (([], nxP) :: ys)) rest sts' hr
          obtain ⟨E, S, S', nx, h1, h2, h3, h4, h5⟩ := hrest t (by omega)
          exact ⟨E, S, S', nx, by simpa using h1, by simpa using h2, by simpa using h3, h4, h5⟩

/-! ## Success of a module at a fuel level -/

/-- The fuel-indexed success predicate (the analogue of `ChildSucc`, for modules that have
instances): at fuel `k + 1` the module's expressions are supported and each instance's child
(resolved in `d`) succeeds at fuel `k`.  Fuel `0` never succeeds (`combR d arr 0 = none`). -/
def SuccF (d : Design) (arr : Module → List Stmt) : Nat → Module → Prop
  | 0, _ => False
  | k + 1, x => ExprsSupp x (arr x) ∧
      ∀ mn i cs, Stmt.inst mn i cs ∈ arr x → ∀ c, findMod d mn = some c → SuccF d arr k c

/-- The static facts every module of the design (and the top) has: assignments/instances/registers
only, and each instance resolves with total input and output connections (all `ref`). -/
theorem static_mod (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeR d m = true) (hA : AdmArrR d m arr) (x : Module)
    (hx : x = m ∨ x ∈ d.modules) :
    (∀ s ∈ arr x, isAsgInstReg s = true) ∧
    ∀ mn i cs, Stmt.inst mn i cs ∈ arr x → ∃ c, findMod d mn = some c ∧ instOkR c cs = true ∧
      (∀ p ∈ c.inputs, ∃ q ∈ cs, q.1 = p.name) ∧ (∀ q ∈ cs, ∃ y, q.2 = Expr.ref y) := by
  have hfacts : ∀ y mn cs, connsOkR d y mn cs = true → ∃ c, findMod d mn = some c ∧
      instOkR c cs = true ∧ (∀ p ∈ c.inputs, ∃ q ∈ cs, q.1 = p.name) ∧
      (∀ q ∈ cs, ∃ z, q.2 = Expr.ref z) := by
    intro y mn cs h
    obtain ⟨c, hf, hprim, _, _, _, _, hall, hcov, href⟩ := connsOkR_facts h
    exact ⟨c, hf, by unfold instOkR; rw [hprim, hall]; rfl,
      fun p hp => hcov p (List.mem_append_left _ hp), href⟩
  simp only [HierShapeR, Bool.and_eq_true] at hS
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hbody⟩, h5⟩, _⟩, _⟩, _⟩, hmods⟩ := hS
  rcases hx with rfl | hx
  · have hp := hA.1
    refine ⟨fun s hs => List.all_eq_true.mp hbody s (hp.mem_iff.mp hs), ?_⟩
    intro mn i cs hin
    exact hfacts _ mn cs (List.all_eq_true.mp h5 _ (hp.mem_iff.mp hin))
  · have hp := (hA.2.2 x hx).1
    have hx' := List.all_eq_true.mp hmods x hx
    cases hl : leafBody x.body with
    | true =>
      refine ⟨?_, ?_⟩
      · intro s hs
        rcases (leafBody_iff x.body).mp hl s (hp.mem_iff.mp hs) with ⟨l, r, rfl⟩ | ⟨o, c, r, e, i, rfl⟩
        · rfl
        · rfl
      · intro mn i cs hin
        exact (leafBody_no_inst hl mn i cs (hp.mem_iff.mp hin)).elim
    | false =>
      simp only [hl, Bool.false_or, modShapeR, Bool.and_eq_true] at hx'
      obtain ⟨⟨⟨⟨hb, h2⟩, _⟩, _⟩, _⟩ := hx'
      refine ⟨fun s hs => List.all_eq_true.mp hb s (hp.mem_iff.mp hs), ?_⟩
      intro mn i cs hin
      exact hfacts _ mn cs (List.all_eq_true.mp h2 _ (hp.mem_iff.mp hin))

/-- From success at fuel `k`, one level at a time: every state slice, seed and environment. -/
theorem succ_exists (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeR d m = true) (hA : AdmArrR d m arr) :
    ∀ (k : Nat) (x : Module), (x = m ∨ x ∈ d.modules) → SuccF d arr k x →
      (∀ st env0, ∃ E, combR d arr k x st env0 = some E) ∧
      (∀ st envF, ∃ U, upsR d arr k x st envF = some U) := by
  intro k
  induction k with
  | zero => intro x _ h; exact absurd h (by simp [SuccF])
  | succ k ih =>
    intro x hx hsucc
    obtain ⟨hsupp, hkids⟩ := hsucc
    obtain ⟨hai, hinst⟩ := static_mod d arr m hS hA x hx
    -- the child step exists for every instance of the arrangement
    have hchild : ∀ mn i cs, Stmt.inst mn i cs ∈ arr x → ∀ (st : HSt) (we : WEnv) (env : Env),
        ∃ c seed envC, findMod d mn = some c ∧ instOkR c cs = true ∧
          (∀ q ∈ cs, ∃ y, q.2 = Expr.ref y) ∧
          childSeedS c cs we env (regOuts (arr c)) (st [i]) = some seed ∧
          combR d arr k c (fun p => st (i :: p)) seed = some envC ∧
          (∀ st' envF', ∃ U, upsR d arr k c st' envF' = some U) := by
      intro mn i cs hin st we env
      obtain ⟨c, hf, hok, hcov, href⟩ := hinst mn i cs hin
      obtain ⟨hc1, hc2⟩ := ih c (Or.inr (findMod_mem hf)) (hkids mn i cs hin c hf)
      obtain ⟨e, he⟩ := childSeed_some c cs we env hcov href
      have hs : childSeedS c cs we env (regOuts (arr c)) (st [i]) =
          some (fun n => if (regOuts (arr c)).contains n && !(inNames c).contains n
            then st [i] n else e n) := by
        simp only [childSeedS, he, Option.map_some]
      obtain ⟨envC, hC⟩ := hc1 (fun p => st (i :: p)) (fun n => if (regOuts (arr c)).contains n &&
        !(inNames c).contains n then st [i] n else e n)
      exact ⟨c, _, envC, hf, hok, href, hs, hC, hc2⟩
    refine ⟨?_, ?_⟩
    · intro st env0
      show ∃ E, evalAssignsI (declWidth x) (instEvalF d arr (combR d arr k) st (declWidth x))
        (arr x) env0 = some E
      apply evalAssignsI_succ_S x _ _ _ hai hsupp
      intro mn i cs hin e
      obtain ⟨c, seed, envC, hf, hok, href, hs, hC, _⟩ := hchild mn i cs hin st (declWidth x) e
      obtain ⟨l, hl⟩ := outWrites_some c cs envC href
      exact ⟨l, by simp [instEvalF, hf, hok, hs, hC, hl]⟩
    · intro st envF
      obtain ⟨nxP, hP⟩ := regNexts_succ_supp x (fun _ _ => 0) (arr x) hai hsupp envF
      have hm : ∃ ys, (instDecls (arr x)).mapM
          (childUpsF d arr (combR d arr k) (upsR d arr k) (declWidth x) st envF) = some ys := by
        apply mapM_some_of_forall
        rintro ⟨mn, i, cs⟩ hmem
        obtain ⟨c, seed, envC, hf, hok, href, hs, hC, hU⟩ :=
          hchild mn i cs ((mem_instDecls_iff _ _).mp hmem) st (declWidth x) envF
        obtain ⟨U, hU'⟩ := hU (fun p => st (i :: p)) envC
        exact ⟨U.map (fun u => (i :: u.1, u.2)), by simp [childUpsF, hf, hok, hs, hC, hU']⟩
      obtain ⟨ys, hys⟩ := hm
      exact ⟨([], nxP) :: ys.flatten, by simp [upsR, hP, hys]⟩

/-! ## Existence of the run -/

theorem stepHSR_succ (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeR d m = true) (hA : AdmArrR d m arr) (hsucc : SuccF d arr (fuelR d) m)
    (st : HSt) (env0 : Env) : ∃ r, stepHSR d arr m st env0 = some r := by
  obtain ⟨hc, hu⟩ := succ_exists d arr m hS hA (fuelR d) m (Or.inl rfl) hsucc
  obtain ⟨E, hE⟩ := hc st env0
  obtain ⟨U, hU⟩ := hu st E
  exact ⟨(E, U), by simp [stepHSR, hierR_clk hS, stepR, hE, hU]⟩

/-- RUN EXISTENCE (the analogue of `runHS_exists_multi`): from any state, for any seed. -/
theorem runHSR_exists (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeR d m = true) (hA : AdmArrR d m arr) (hsucc : SuccF d arr (fuelR d) m)
    (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : HSt), ∃ envs sts, runHSRTrace d arr m seed k st = some (envs, sts) := by
  intro k
  induction k with
  | zero => intro st; exact ⟨[], [], rfl⟩
  | succ k ih =>
    intro st
    obtain ⟨⟨envF, ups⟩, hr⟩ := stepHSR_succ d arr m hS hA hsucc st
      (seed k (restrictTo (regOuts (arr m)) (st [])))
    obtain ⟨envs, sts, hrest⟩ := ih (applyH st ups)
    exact ⟨envF :: envs, st :: sts, by simp [runHSRTrace, hr, hrest]⟩

/-! ## Success from one successful cycle (what a child's own theorem supplies) -/

theorem evalAssignsI_assign_supp (we : WEnv) (ie : InstEval) :
    ∀ (b : List Stmt) (env E : Env), evalAssignsI we ie b env = some E →
      ∀ l r, Stmt.assign l r ∈ b → (evalExpr we (fun _ => 0) r).isSome = true := by
  intro b
  induction b with
  | nil => intro env E _ l r h; cases h
  | cons s rest ih =>
    intro env E h l r hmem
    simp only [evalAssignsI] at h
    cases hcv : cellVals we ie s env with
    | none => simp [hcv] at h
    | some lv =>
      simp only [hcv, Option.bind_eq_bind, Option.bind] at h
      rcases List.mem_cons.mp hmem with rfl | hm
      · simp only [cellVals] at hcv
        cases hv : evalExpr we env r with
        | none => simp [hv] at hcv
        | some v =>
          obtain ⟨v', hv'⟩ := evalExpr_env_some we env (fun _ => 0) r v hv
          simp [hv']
      · exact ih _ E h l r hm

theorem evalAssignsI_inst_ex (we : WEnv) (ie : InstEval) :
    ∀ (b : List Stmt) (env E : Env), evalAssignsI we ie b env = some E →
      ∀ mn i cs, Stmt.inst mn i cs ∈ b → ∃ env' l, ie mn i cs env' = some l := by
  intro b
  induction b with
  | nil => intro env E _ mn i cs h; cases h
  | cons s rest ih =>
    intro env E h mn i cs hmem
    simp only [evalAssignsI] at h
    cases hcv : cellVals we ie s env with
    | none => simp [hcv] at h
    | some lv =>
      simp only [hcv, Option.bind_eq_bind, Option.bind] at h
      rcases List.mem_cons.mp hmem with rfl | hm
      · exact ⟨env, lv, by simpa [cellVals] using hcv⟩
      · exact ih _ E h mn i cs hm

theorem regNexts_reg_supp (we : WEnv) (mems : MEnv) :
    ∀ (b : List Stmt) (env : Env) (l : List (String × Nat)), regNexts we mems b env = some l →
      ∀ o c r e i, Stmt.register o c r e i ∈ b → (evalExpr we (fun _ => 0) e).isSome = true := by
  intro b
  induction b with
  | nil => intro env l _ o c r e i h; cases h
  | cons s rest ih =>
    intro env l h o c r e i hmem
    cases s with
    | assign x y =>
      exact ih env l (by simpa [regNexts] using h) o c r e i (by simpa using hmem)
    | inst a b' c' =>
      exact ih env l (by simpa [regNexts] using h) o c r e i (by simpa using hmem)
    | register o' c' r' e' i' =>
      obtain ⟨rn, rk⟩ := r'
      simp only [regNexts] at h
      cases hv : evalExpr we env e' with
      | none => simp [hv] at h
      | some v =>
        cases hn : regNexts we mems rest env with
        | none => simp [hv, hn] at h
        | some nx =>
          rcases List.mem_cons.mp hmem with heq | hm
          · simp only [Stmt.register.injEq] at heq
            obtain ⟨_, _, _, rfl, _⟩ := heq
            obtain ⟨v', hv'⟩ := evalExpr_env_some we env (fun _ => 0) _ v hv
            simp [hv']
          · exact ih env nx hn o c r e i hm
    | memory nm aw dw a1 a2 a3 a4 ra rd cr a5 er =>
      have hm' : Stmt.register o c r e i ∈ rest := by
        rcases List.mem_cons.mp hmem with h' | h'
        · cases h'
        · exact h'
      simp only [regNexts] at h
      split at h
      · exact ih env l h o c r e i hm'
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨_, _, nx, hn, _⟩ := h
        exact ih env nx hn o c r e i hm'

theorem upsR_succ_inv {d : Design} {arr : Module → List Stmt} {k : Nat} {m : Module} {st : HSt}
    {envF : Env} {ups : Ups} (h : upsR d arr (k + 1) m st envF = some ups) :
    ∃ nxP L, regNexts (declWidth m) (fun _ _ => 0) (arr m) envF = some nxP ∧
      (instDecls (arr m)).mapM
        (childUpsF d arr (combR d arr k) (upsR d arr k) (declWidth m) st envF) = some L := by
  unfold upsR at h
  cases hP : regNexts (declWidth m) (fun _ _ => 0) (arr m) envF with
  | none => simp [hP] at h
  | some nx =>
    cases hm : (instDecls (arr m)).mapM
        (childUpsF d arr (combR d arr k) (upsR d arr k) (declWidth m) st envF) with
    | none => simp [hP, hm] at h
    | some l => exact ⟨nx, l, rfl, rfl⟩

/-- ONE successful cycle of a module at fuel `k` (its combinational fold and its updates) gives
`SuccF` at fuel `k`: the converse of `succ_exists`, by which a child's OWN theorem (a successful
run of the child at `K = 1`) supplies success for the parent's run existence. -/
theorem succF_of_step (d : Design) (arr : Module → List Stmt) :
    ∀ (k : Nat) (x : Module) (st : HSt) (env0 E : Env) (U : Ups),
      combR d arr k x st env0 = some E → upsR d arr k x st E = some U → SuccF d arr k x := by
  intro k
  induction k with
  | zero => intro x st env0 E U h; simp [combR] at h
  | succ k ih =>
    intro x st env0 E U hE hU
    have hE' : evalAssignsI (declWidth x) (instEvalF d arr (combR d arr k) st (declWidth x))
        (arr x) env0 = some E := hE
    obtain ⟨nxP, L, hP, hL⟩ := upsR_succ_inv hU
    refine ⟨?_, ?_⟩
    · intro s hs
      cases s with
      | assign l r =>
        exact evalAssignsI_assign_supp _ _ _ _ _ hE' l r hs
      | register o c r e i =>
        exact regNexts_reg_supp _ _ _ _ _ hP o c r e i hs
      | inst _ _ _ => rfl
      | memory _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    · intro mn i cs hin c hf
      obtain ⟨env', l, hl⟩ := evalAssignsI_inst_ex _ _ _ _ _ hE' mn i cs hin
      obtain ⟨c1, seed1, envC1, hf1, _, _, hcc1, _⟩ := instEvalF_some hl
      obtain ⟨us, _, hfx⟩ := mapM_mem_ex _ _ _ hL (mn, i, cs) ((mem_instDecls_iff _ _).mpr hin)
      obtain ⟨c2, seed2, envC2, us', hf2, _, _, hcc2, huu2, _⟩ := childUpsF_inv hfx
      have hc2 : c2 = c := by simp only [] at hf2; rw [hf] at hf2; exact (Option.some.inj hf2).symm
      subst hc2
      exact ih c2 (fun p => st (i :: p)) seed2 envC2 us' hcc2 huu2

end Tools.VedU2HierRec
