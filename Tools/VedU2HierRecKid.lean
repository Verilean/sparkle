import Tools.VedU2HierRecLem

/-!
# Instance step of the recursive statement (CANDIDATE; Tools/VedU2HierRec.lean)

* the laws of the recursive instance evaluator (`instEvalF_laws`), the inversion of one cycle
  (`stepHSR_some_inv`), the closed run with its state history (`runHSRTrace`);
* the child's standalone run on its state slice (`runIn`): L4 prefix (`runIn_prefix`) and seed
  causality (`runIn_congr_seed`), and the transfer of a child theorem stated on a sub-design to the
  parent's real design (`runHSR_runIn`);
* L2 + L5 core (`runIn_proj`): the parent's run, projected on one instance, IS the child's standalone
  run started at the slice `fun p => st (i :: p)`, with the input/output port correspondence.
-/

namespace Tools.VedU2HierRec

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier

theorem instEvalF_some {d : Design} {arr : Module → List Stmt} {comb : Module → HSt → Env → Option Env}
    {st : HSt} {we : WEnv} {mn i : String} {cs : List (String × Expr)} {env : Env}
    {l : List (String × Nat)} (h : instEvalF d arr comb st we mn i cs env = some l) :
    ∃ c seed envC, findMod d mn = some c ∧ instOkR c cs = true ∧
      childSeedS c cs we env (regOuts (arr c)) (st [i]) = some seed ∧
      comb c (fun p => st (i :: p)) seed = some envC ∧ outWrites c cs envC = some l := by
  unfold instEvalF at h
  cases hf : findMod d mn with
  | none => simp [hf] at h
  | some c =>
    simp only [hf] at h
    by_cases hok : instOkR c cs = true
    · simp only [hok, if_true] at h
      cases hsd : childSeedS c cs we env (regOuts (arr c)) (st [i]) with
      | none => simp [hsd] at h
      | some seed =>
        cases hcc : comb c (fun p => st (i :: p)) seed with
        | none => simp [hsd, hcc] at h
        | some envC =>
          simp only [hsd, hcc, Option.bind_eq_bind, Option.bind] at h
          exact ⟨c, seed, envC, rfl, hok, hsd, hcc, h⟩
    · simp [hok] at h

theorem instEvalF_laws (d : Design) (arr : Module → List Stmt)
    (comb : Module → HSt → Env → Option Env) (st : HSt) (we : WEnv) :
    IELaws d (instEvalF d arr comb st we) := by
  constructor
  · intro mn i cs e1 e2 h
    unfold instEvalF
    cases hf : findMod d mn with
    | none => rfl
    | some c =>
      simp only []
      have hseed : childSeedS c cs we e1 (regOuts (arr c)) (st [i]) =
          childSeedS c cs we e2 (regOuts (arr c)) (st [i]) := by
        apply childSeedS_agree
        intro p hp e hl
        apply evalExpr_congr
        intro n hn
        apply h
        simp only [instIns, hf, List.mem_flatMap, List.mem_map, List.mem_filter]
        exact ⟨e, ⟨(p.name, e), ⟨lookup_mem _ _ _ hl, by simpa using ⟨p, hp, rfl⟩⟩, rfl⟩, hn⟩
      simp only [hseed]
  · intro mn i cs e l h
    obtain ⟨c, seed, envC, hf, _, _, _, hw⟩ := instEvalF_some h
    simp only [instOuts, hf]
    exact outWrites_names c cs envC l hw

/-- Inversion of one successful cycle of the top. -/
theorem stepHSR_some_inv {d : Design} {arr : Module → List Stmt} {m : Module} {st : HSt}
    {env0 envF : Env} {ups : Ups} (h : stepHSR d arr m st env0 = some (envF, ups)) :
    clkRstOk d m = true ∧
    evalAssignsI (declWidth m)
      (instEvalF d arr (combR d arr (d.modules.length + 1)) st (declWidth m)) (arr m) env0 = some envF ∧
    upsR d arr (d.modules.length + 1 + 1) m st envF = some ups := by
  unfold stepHSR at h
  by_cases hc : clkRstOk d m = true
  · simp only [hc, if_true] at h
    unfold stepR at h
    cases hE : combR d arr (fuelR d) m st env0 with
    | none => simp [hE] at h
    | some e =>
      cases hu : upsR d arr (fuelR d) m st e with
      | none => simp [hE, hu] at h
      | some u =>
        simp only [hE, hu, Option.bind_eq_bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hc, hE, hu⟩
  · simp [hc] at h

/-- `runHSR` with the pre-update state of every cycle. -/
def runHSRTrace (d : Design) (arr : Module → List Stmt) (m : Module)
    (seed : Nat → (String → Nat) → Env) : Nat → HSt → Option (List Env × List HSt)
  | 0, _ => some ([], [])
  | k + 1, st => do
    let (envF, ups) ← stepHSR d arr m st (seed k (restrictTo (regOuts (arr m)) (st [])))
    let (rest, sts) ← runHSRTrace d arr m seed k (applyH st ups)
    some (envF :: rest, st :: sts)

theorem runHSRTrace_fst (d : Design) (arr : Module → List Stmt) (m : Module)
    (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : HSt),
      (runHSRTrace d arr m seed k st).map Prod.fst = runHSR d arr m seed k st := by
  intro k
  induction k with
  | zero => intro st; rfl
  | succ k ih =>
    intro st
    simp only [runHSRTrace, runHSR]
    cases hs : stepHSR d arr m st (seed k (restrictTo (regOuts (arr m)) (st []))) with
    | none => simp
    | some r =>
      obtain ⟨e, u⟩ := r
      have := ih (applyH st u)
      cases hr : runHSRTrace d arr m seed k (applyH st u) with
      | none =>
        rw [hr] at this; simp only [Option.map_none] at this; simp [hs, hr, ← this]
      | some q =>
        rw [hr] at this; simp only [Option.map_some] at this; simp [hs, hr, ← this]

/-- An input the parent does not write keeps the stream's value, at every cycle of the run. -/
theorem runHSR_inputs (d : Design) (arr : Module → List Stmt) (m : Module)
    (hwm : WOH d (arr m)) (hwr : ∀ n ∈ wrsH d (arr m), n ∉ inNames m) (inp : Nat → String → Nat)
    (K : Nat) :
    ∀ (k : Nat), k ≤ K → ∀ (st : HSt) (envs : List Env) (sts : List HSt),
      runHSRTrace d arr m (seedFwd m K inp) k st = some (envs, sts) →
      ∀ t, t < k → ∀ E, envs[t]? = some E → ∀ n ∈ inNames m, E n = inp (K - k + t) n := by
  intro k
  induction k with
  | zero => intro _ st envs sts _ t ht; exact absurd ht (Nat.not_lt_zero _)
  | succ k ih =>
    intro hk st envs sts hrun t ht E hE n hn
    simp only [runHSRTrace] at hrun
    cases hs : stepHSR d arr m st (seedFwd m K inp k (restrictTo (regOuts (arr m)) (st []))) with
    | none => simp [hs] at hrun
    | some r =>
      obtain ⟨envF, ups⟩ := r
      cases hr : runHSRTrace d arr m (seedFwd m K inp) k (applyH st ups) with
      | none => simp [hs, hr] at hrun
      | some q =>
        obtain ⟨rest, sts'⟩ := q
        simp [hs, hr] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        obtain ⟨_, hfold, _⟩ := stepHSR_some_inv hs
        have hG := good_of_fold d (declWidth m) _ (instEvalF_laws d arr _ st (declWidth m)) (arr m) _
          envF hwm hfold
        cases t with
        | zero =>
          simp at hE; subst hE
          rw [hG.1 n (fun h => hwr n h hn)]
          have hc : (m.inputs.map (·.name)).contains n = true := by simpa [inNames] using hn
          simp only [seedFwd, hc, if_true]
          have : K - 1 - k = K - (k + 1) + 0 := by omega
          rw [this]
        | succ t =>
          have := ih (by omega) _ rest sts' hr t (by omega) E (by simpa using hE) n hn
          rw [this]; congr 1; omega

/-! ## The child's standalone run on its slice -/

/-- The child's cycle on its own state, in the parent's real design `d` at the fuel the parent gives a
child (no clock/reset guard: that is the parent's and the child's own shape judgement). -/
def stepIn (d : Design) (arr : Module → List Stmt) (c : Module)
    (seed : Nat → (String → Nat) → Env) (st : HSt) (j : Nat) : Option (Env × HSt) :=
  match stepR d arr (d.modules.length + 1) c st (seed j (restrictTo (regOuts (arr c)) (st []))) with
  | some (e, ups) => some (e, applyH st ups)
  | none => none

/-- `k` cycles of the child alone (the cycle index passed to `seed` counts down, as `runHSR`). -/
def runIn (d : Design) (arr : Module → List Stmt) (c : Module)
    (seed : Nat → (String → Nat) → Env) : Nat → HSt → Option (List Env)
  | 0, _ => some []
  | k + 1, st => do
    let (e, st') ← stepIn d arr c seed st k
    let rest ← runIn d arr c seed k st'
    some (e :: rest)

/-- L4 (seed causality): the run depends on the seeds of the cycles it runs only. -/
theorem runIn_congr_seed (d : Design) (arr : Module → List Stmt) (c : Module)
    (s1 s2 : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : HSt), (∀ j, j < k → s1 j = s2 j) →
      runIn d arr c s1 k st = runIn d arr c s2 k st := by
  intro k
  induction k with
  | zero => intro st _; rfl
  | succ k ih =>
    intro st h
    have hstep : stepIn d arr c s1 st k = stepIn d arr c s2 st k := by
      simp only [stepIn, h k (Nat.lt_succ_self k)]
    simp only [runIn, hstep, ih _ (fun j hj => h j (by omega))]

/-- L4 (prefix): the first `k` cycles of a successful `k + n`-cycle run are the `k`-cycle run under the
shifted seed. -/
theorem runIn_prefix (d : Design) (arr : Module → List Stmt) (c : Module)
    (seed : Nat → (String → Nat) → Env) :
    ∀ (k n : Nat) (st : HSt) (L : List Env),
      runIn d arr c seed (k + n) st = some L →
      ∃ L', runIn d arr c (fun j => seed (j + n)) k st = some L' ∧ L' = L.take k := by
  intro k
  induction k with
  | zero => intro n st L _; exact ⟨[], rfl, by simp⟩
  | succ k ih =>
    intro n st L h
    have e : k + 1 + n = (k + n) + 1 := by omega
    rw [e] at h
    simp only [runIn] at h
    cases hs : stepIn d arr c seed st (k + n) with
    | none => simp [hs] at h
    | some r =>
      obtain ⟨envF, st'⟩ := r
      cases hr : runIn d arr c seed (k + n) st' with
      | none => simp [hs, hr] at h
      | some rest =>
        simp only [hs, hr, Option.bind_eq_bind, Option.bind, Option.some.injEq] at h
        obtain ⟨L', hL', hLe⟩ := ih n st' rest hr
        refine ⟨envF :: L', ?_, ?_⟩
        · simp only [runIn]
          have hs' : stepIn d arr c (fun j => seed (j + n)) st k = some (envF, st') := hs
          simp only [hs', hL', Option.bind_eq_bind, Option.bind]
        · rw [← h, hLe]
          simp

/-- TRANSFER OF A CHILD THEOREM: a successful run in the sub-design `dC` (its own fuel, its own
clock/reset guard) is the same successful run in the parent's real design. -/
theorem runHSR_runIn {dC d : Design} (hs : SubDesign dC d) (arr : Module → List Stmt)
    (hfuel : fuelR dC ≤ d.modules.length + 1) (c : Module) (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : HSt) (L : List Env),
      runHSR dC arr c seed k st = some L → runIn d arr c seed k st = some L := by
  intro k
  induction k with
  | zero => intro st L h; exact h
  | succ k ih =>
    intro st L h
    simp only [runHSR] at h
    cases hst : stepHSR dC arr c st (seed k (restrictTo (regOuts (arr c)) (st []))) with
    | none => simp [hst] at h
    | some r =>
      obtain ⟨envF, ups⟩ := r
      cases hr : runHSR dC arr c seed k (applyH st ups) with
      | none => simp [hst, hr] at h
      | some rest =>
        simp only [hst, hr, Option.bind_eq_bind, Option.bind, Option.some.injEq] at h
        subst h
        have hstep : stepIn d arr c seed st k = some (envF, applyH st ups) := by
          unfold stepHSR at hst
          by_cases hc : clkRstOk dC c = true
          · simp only [hc, if_true] at hst
            have := stepR_sub_fuel hs arr hfuel c st _ _ hst
            simp only [stepIn, this]
          · simp [hc] at hst
        simp only [runIn, hstep, ih _ rest hr, Option.bind_eq_bind, Option.bind]

end Tools.VedU2HierRec
