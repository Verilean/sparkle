import Tools.VedU2HierNet
import Tools.VedU2HierState

/-!
# H2c-state: an instance's output at ONE cycle, for a combinational child (`kid_step`)

`kid_inst_net` (H2c) applies the child's own theorem (`OutputsStmt`) to a total input stream `F`, and
asks that the parent wire a data port reads carries `F t port` at EVERY cycle `t < K` of the closed
run.  When the wire is a parent REGISTER output that is not available before the parent invariant
(`R`, `outputsOnHS_of_stepRK`) has been proved along the run, so it cannot be a hypothesis of the
run as a whole.

`kid_step` asks the agreement at the one cycle `t` only.  This is sound exactly because the child is
COMBINATIONAL (a body of assignments only): the closed run's cycle-`t` environment of such a body is
computed from the cycle-`t` seed alone (`runModule_asg_nth`), so two runs whose seeds agree at cycle
`t` agree there, whatever they do at the other cycles (`runModule_asg_local`).  The child's own
theorem is applied to the stream `netIn ck cs ins F` for ANY in-range total stream `F`; the parent
supplies only `F t port = (the wire's value at cycle t)`.
-/

namespace Tools.VedU2Hier

open Lean Elab Tactic Meta in
/-- `ved_kernel_exact h` closes the goal by the term `h` WITHOUT checking in the elaborator that `h`'s type is
the goal: the kernel checks the conversion when the theorem is added (a wrong one is a `[kernel]`
refusal).  For the conversions that need the kernel's cheaper unfolding (a parent's loop against the
open parent's loop that differs only in dead code). -/
elab "ved_kernel_exact " t:term : tactic => do
  let g ← getMainGoal
  g.withContext do
    let e ← instantiateMVars (← Term.elabTerm t none)
    g.assign e
    replaceMainGoal []

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier

/-- A concatenation `x ++ y` is `x * 2 ^ n + y` (the form `omega` can use): used by the net evaluation of a
register bundle, whose slices are taken out of such concatenations. -/
theorem or_shl_add_of_lt (x y n : Nat) (h : y < 2 ^ n) : (x <<< n ||| y) = x * 2 ^ n + y := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq]

/-- A body of plain assignments. -/
def asgOnly : List Stmt → Bool
  | [] => true
  | .assign .. :: r => asgOnly r
  | _ => false

theorem regNexts_asg (we : WEnv) (mems : MEnv) (env : Env) :
    ∀ b : List Stmt, asgOnly b = true → regNexts we mems b env = some [] := by
  intro b
  induction b with
  | nil => intro _; rfl
  | cons s rest ih =>
    intro h
    cases s with
    | assign l r => exact ih h
    | _ => simp [asgOnly] at h

theorem memNexts_asg (we : WEnv) (mems : MEnv) (env : Env) :
    ∀ b : List Stmt, asgOnly b = true → memNexts we b mems env = some mems := by
  intro b
  induction b with
  | nil => intro _; rfl
  | cons s rest ih =>
    intro h
    cases s with
    | assign l r => exact ih h
    | _ => simp [asgOnly] at h

theorem applyNexts_nil' (st : String → Nat) : applyNexts st [] = st := by
  funext n; rfl

/-- Cycle `t` of a successful run of an assignment-only body: the run's `t`-th environment is the
evaluation of the body from the seed of index `k - 1 - t` at the (never changing) state. -/
theorem runModule_asg_nth (we : WEnv) (b : List Stmt) (hb : asgOnly b = true)
    (seed : Nat → (String → Nat) → Env) (mems : MEnv) :
    ∀ (k : Nat) (st : String → Nat) (envs : List Env),
      runModule we b seed k st mems = some envs →
      ∀ t, t < k → ∃ E, envs[t]? = some E ∧ evalAssigns we mems b (seed (k - 1 - t) st) = some E := by
  intro k
  induction k with
  | zero => intro st envs _ t ht; omega
  | succ k ih =>
    intro st envs hrun t ht
    simp only [runModule, stepModule, Option.bind_eq_bind] at hrun
    cases hE : evalAssigns we mems b (seed k st) with
    | none => simp [hE] at hrun
    | some envF =>
      simp only [hE, Option.bind_some, regNexts_asg we mems envF b hb, memNexts_asg we mems envF b hb,
        applyNexts_nil'] at hrun
      cases hr : runModule we b seed k st mems with
      | none => simp [hr] at hrun
      | some rest =>
        simp only [hr, Option.bind_some, Option.some.injEq] at hrun
        subst hrun
        cases t with
        | zero => exact ⟨envF, rfl, by simpa using hE⟩
        | succ t =>
          obtain ⟨E, h1, h2⟩ := ih st rest hr t (by omega)
          refine ⟨E, by simpa using h1, ?_⟩
          have : k + 1 - 1 - (t + 1) = k - 1 - t := by omega
          rw [this]; exact h2

/-- Two successful runs of an assignment-only body whose seeds agree at cycle `t` agree there. -/
theorem runModule_asg_local (we : WEnv) (b : List Stmt) (hb : asgOnly b = true)
    (s1 s2 : Nat → (String → Nat) → Env) (mems : MEnv) (st : String → Nat) (k : Nat)
    (e1 e2 : List Env) (h1 : runModule we b s1 k st mems = some e1)
    (h2 : runModule we b s2 k st mems = some e2) (t : Nat) (ht : t < k)
    (hs : s1 (k - 1 - t) st = s2 (k - 1 - t) st) :
    e1[t]? = e2[t]? := by
  obtain ⟨E1, hE1, hv1⟩ := runModule_asg_nth we b hb s1 mems k st e1 h1 t ht
  obtain ⟨E2, hE2, hv2⟩ := runModule_asg_nth we b hb s2 mems k st e2 h2 t ht
  rw [hs] at hv1
  rw [hv1] at hv2
  have := Option.some.inj hv2
  rw [hE1, hE2, this]

theorem asgOnly_mem : ∀ b : List Stmt, asgOnly b = true ↔ ∀ s ∈ b, ∃ l r, s = Stmt.assign l r := by
  intro b
  induction b with
  | nil => simp [asgOnly]
  | cons s rest ih =>
    constructor
    · intro h x hx
      cases s with
      | assign l r =>
        simp only [asgOnly] at h
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨l, r, rfl⟩
        · exact ih.mp h x hx
      | _ => simp [asgOnly] at h
    · intro h
      obtain ⟨l, r, rfl⟩ := h s (List.mem_cons_self ..)
      simp only [asgOnly]
      exact ih.mpr fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem asgOnly_perm {b b' : List Stmt} (hp : b.Perm b') (h : asgOnly b = true) : asgOnly b' = true :=
  (asgOnly_mem b').mpr fun s hs => (asgOnly_mem b).mp h s (hp.mem_iff.mpr hs)

/-- THE SAME-CYCLE CHILD OUTPUT (combinational child): see the file header.  As `kid_inst_net`, but the
agreement of the wires with the total stream `F` is asked at the cycle `t` only. -/
theorem kid_step (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeS d m = true) (hA : AdmArr d m arr)
    (hwr : ∀ n ∈ wrsH d (arr m), n ∉ inNames m)
    (cc : Contract) (htie : cc.clkRst = designClkRst d m)
    (ins : Nat → String → Nat) (hok : InputsOk cc m ins) (K : Nat) (envs : List Env)
    (sts : List HSt)
    (hrun : runHSTrace d arr m (seedFwd m K ins) K (st0H d m) = some (envs, sts))
    (mn i : String) (cs : List (String × Expr)) (hin : Stmt.inst mn i cs ∈ m.body)
    (c : Module) (hf : findMod d mn = some c) (hcomb : asgOnly c.body = true)
    (ck : Contract) (g : ck.table.Ty) (hU : U1Stmt ck c g)
    (hclkc : ck.clkRst = regClkRst c.body)
    (hconn : ∀ p ∈ c.inputs, ∃ x, cs.lookup p.name = some (Expr.ref x) ∧
      (ck.dataInputs.any (·.name == p.name) = true ∨ x ∈ inNames m))
    (hrstnd : ∀ kr, ck.clkRst = some kr → ck.dataInputs.any (·.name == kr.2) = false)
    (F : Nat → String → Nat)
    (hrange : ∀ t, ∀ p ∈ ck.dataInputs, F t p.name < 2 ^ declWidth c p.name)
    (t : Nat) (ht : t < K) (E : Env) (hE : envs[t]? = some E)
    (hrunF : ∀ p ∈ ck.dataInputs,
      ∃ x, cs.lookup p.name = some (Expr.ref x) ∧ E x = F t p.name) :
    ∀ q ∈ c.outputs,
      ∃ x, cs.lookup q.name = some (Expr.ref x) ∧
        E x = srcOf ck g (netIn ck cs ins F) q.name t := by
  obtain ⟨c', cenvs, cstates, hf', hrunM, hrunR, hcorr⟩ :=
    runHS_proj d arr m hS hA ins K envs sts hrun mn i cs hin
  have hcc : c = c' := by rw [hf] at hf'; exact Option.some.inj hf'
  subst hcc
  obtain ⟨_, ⟨hcore, _⟩, _, _, hout⟩ := hU
  have hperm := hA.2.2 c (findMod_mem hf)
  have hinits : (regsOf c.body).map (fun r => (r.1, r.2.2.2)) = ck.inits := hcore.2.2.2.2.2.2.2.1
  have hst0 : st0Of c = st0 ck c := st0Of_eq_st0 ck c hinits
  have hasg : asgOnly (arr c) = true := asgOnly_perm hperm.1.symm hcomb
  -- the child stream is in range
  have hok' : InputsOk ck c (netIn ck cs ins F) := by
    refine ⟨?_, ?_⟩
    · intro t p hp
      have hd : ck.dataInputs.any (·.name == p.name) = true :=
        List.any_eq_true.mpr ⟨p, hp, by simp⟩
      have h1 : netIn ck cs ins F t p.name = F t p.name := by simp [netIn, hd]
      rw [h1]
      exact hrange t p hp
    · intro t kr hkr
      rw [hclkc] at hkr
      have hreg : regsOf c.body ≠ [] := by
        intro h0; simp [regClkRst, h0] at hkr
      obtain ⟨x, y, kc, kr', hrc, h1, h2, hcl, hx, hy, hne, hkc, hkr2⟩ :=
        instPair_tie d m (hierS_clk hS) mn i cs c hin hf hreg cc htie
      have hkk : (kc, kr') = kr := Option.some.inj (hrc.symm.trans hkr)
      subst hkk
      have hnd := hrstnd (kc, kr') (hclkc.trans hrc)
      have : netIn ck cs ins F t kr' = ins t y := by simp [netIn, hnd, insCIn, h2]
      show netIn ck cs ins F t kr' = 0
      rw [this]
      exact hok.2 t (x, y) hcl
  -- the seeds agree at the cycle `t`
  have hpre : ∀ n ∈ inNames c, netIn ck cs ins F t n = insCOf (declWidth m) cs envs t n := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    obtain ⟨x, hl, hx⟩ := hconn p hp
    by_cases hd : ck.dataInputs.any (·.name == p.name) = true
    · obtain ⟨p', hp', hpn⟩ := List.any_eq_true.mp hd
      have hpn' : p'.name = p.name := by simpa using hpn
      obtain ⟨x', hl', hEx'⟩ := hrunF p' hp'
      rw [hpn'] at hl' hEx'
      have hxx : x' = x := by
        rw [hl] at hl'; exact (Expr.ref.inj (Option.some.inj hl')).symm
      subst hxx
      have h1 : netIn ck cs ins F t p.name = F t p.name := by simp [netIn, hd]
      rw [h1, ← hEx']
      simp [insCOf, hl, hE, evalExpr]
    · have hxin : x ∈ inNames m := hx.resolve_left hd
      have hEx := runHS_inputs d arr m hA hwr ins K K (Nat.le_refl K) _ envs sts hrun t ht E hE x hxin
      have hd' : ck.dataInputs.any (·.name == p.name) = false := by simpa using hd
      simp [netIn, hd', insCIn, insCOf, hl, hE, evalExpr, hEx]
  have hs : seedFwd c K (insCOf (declWidth m) cs envs) (K - 1 - t) (st0Of c) =
      seedFwd c K (netIn ck cs ins F) (K - 1 - t) (st0Of c) := by
    funext n
    simp only [seedFwd]
    by_cases hn : (c.inputs.map (·.name)).contains n = true
    · rw [if_pos hn, if_pos hn]
      have h : K - 1 - (K - 1 - t) = t := by omega
      rw [h]
      exact (hpre n (List.contains_iff_mem.mp hn)).symm
    · rw [if_neg hn, if_neg hn]
  obtain ⟨envs', hrun', hall⟩ := hout (arr c) hperm.1 hperm.2 (netIn ck cs ins F) hok' K
  rw [← hst0] at hrun'
  have hloc := runModule_asg_local (declWidth c) (arr c) hasg
    (seedFwd c K (insCOf (declWidth m) cs envs)) (seedFwd c K (netIn ck cs ins F)) (fun _ _ => 0)
    (st0Of c) K cenvs envs' hrunR hrun' t ht hs
  intro q hq
  obtain ⟨E0, Ec, S, Sc, hE0, hEc, _, _, hproj⟩ := hcorr t ht
  have hEE : E = E0 := Option.some.inj (hE.symm.trans hE0)
  subst hEE
  obtain ⟨x, hl, hxv⟩ := hproj.2.1 q hq
  refine ⟨x, hl, ?_⟩
  have hqk : q ∈ ck.outputs := by rw [← hcore.2.2.2.2.2.1]; exact hq
  obtain ⟨env, he, hv⟩ := hall t ht q hqk
  rw [← hloc, hEc] at he
  have hee : env = Ec := (Option.some.inj he).symm
  subst hee
  rw [hxv]; exact hv

/-- A register output carries, in the closed run's cycle `t`, the PRE-update state of that cycle (nothing
in the cycle's assignments or instances writes it): the value the parent's own invariant speaks about. -/
theorem closed_run_reg (d : Design) (arr : Module → List Stmt) (m : Module) (hA : AdmArr d m arr)
    (b0 : List Stmt) (hp : (arr m).Perm b0) (hw0 : WOH d b0)
    (hwb : ∀ n ∈ wrsH d b0, n ∉ regOuts b0) (hri : ∀ n ∈ regOuts b0, n ∉ inNames m)
    (ins : Nat → String → Nat) (K : Nat) (envs : List Env) (sts : List HSt)
    (hrun : runHSTrace d arr m (seedFwd m K ins) K (st0H d m) = some (envs, sts))
    (t : Nat) (ht : t < K) (S : HSt) (E : Env) (hS : sts[t]? = some S) (hE : envs[t]? = some E) :
    ∀ r ∈ regOuts b0, E r = S [] r := by
  intro r hr
  obtain ⟨E', S', hE', hS', hfold⟩ := runHSTrace_cycle d arr m (seedFwd m K ins) K (st0H d m) envs sts hrun t ht
  rw [hE] at hE'; rw [hS] at hS'
  cases hE'; cases hS'
  have hfold0 := evalAssignsI_perm d _ _ (instEvalS_laws d arr S (declWidth m)) hp hA.2.1 hw0 hfold
  have hG := good_of_fold d _ _ (instEvalS_laws d arr S (declWidth m)) b0 _ E hw0 hfold0
  have hnw : r ∉ wrsH d b0 := fun h => hwb r h hr
  rw [hG.1 r hnw]
  have hrA : r ∈ regOuts (arr m) := (regOuts_perm_mem hp r).mpr hr
  have hne : ¬ ∃ a, a ∈ m.inputs ∧ a.name = r := by
    rintro ⟨a, ha, rfl⟩
    exact hri a.name hr (List.mem_map.mpr ⟨a, ha, rfl⟩)
  simp [seedFwd, restrictTo, hne, hrA]

end Tools.VedU2Hier
