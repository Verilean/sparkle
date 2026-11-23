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

/-! ## L2 + L5 core: the parent's run, projected on one instance -/

/-- What `connsOkR` gives about the resolved child and the connections (`connsOkK_facts` without
`leafBody`). -/
theorem connsOkR_facts {d : Design} {m : Module} {mn : String} {cs : List (String × Expr)}
    (h : connsOkR d m mn cs = true) :
    ∃ c, findMod d mn = some c ∧ c.isPrimitive = false ∧
      childSane c = true ∧ (inNames c).Nodup ∧ 1 ≤ c.outputs.length ∧ (cs.map (·.1)).Nodup ∧
      cs.all (fun p => (c.inputs ++ c.outputs).any (·.name == p.1)) = true ∧
      (∀ p ∈ c.inputs ++ c.outputs, ∃ q ∈ cs, q.1 = p.name) ∧
      (∀ q ∈ cs, ∃ x, q.2 = Expr.ref x) := by
  simp only [connsOkR] at h
  cases hf : findMod d mn with
  | none => simp [hf] at h
  | some c =>
    simp only [hf, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, and_assoc] at h
    obtain ⟨hp, _, _, hsane, hol, _, _, hcsnd, hcov, hall2, hrefs⟩ := h
    refine ⟨c, rfl, hp, hsane, ?_, hol, hcsnd, hall2, ?_, ?_⟩
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

theorem hierR_inst_ok {d : Design} {m : Module} (h : HierShapeR d m = true) {mn i : String}
    {cs : List (String × Expr)} (hin : Stmt.inst mn i cs ∈ m.body) : connsOkR d m mn cs = true := by
  simp only [HierShapeR, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, h5⟩, _⟩, _⟩, _⟩, _⟩ := h
  exact List.all_eq_true.mp h5 _ hin

theorem hierR_inst_unique {d : Design} {m : Module} (h : HierShapeR d m = true) :
    (instNames m.body).Nodup := by
  simp only [HierShapeR, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, h6⟩, _⟩, _⟩, _⟩ := h
  exact h6

theorem hierR_clk {d : Design} {m : Module} (h : HierShapeR d m = true) : clkRstOk d m = true := by
  simp only [HierShapeR, Bool.and_eq_true] at h
  obtain ⟨⟨_, hc⟩, _⟩ := h
  exact hc

/-- The correspondences at ONE cycle: the input ports read the connections evaluated in the parent's
environment; the parent wire an output port is connected to holds the child's output. -/
def ProjAtR (we : WEnv) (c : Module) (cs : List (String × Expr)) (E Ec : Env) : Prop :=
  (∀ p ∈ c.inputs, ∃ e, cs.lookup p.name = some e ∧ evalExpr we E e = some (Ec p.name)) ∧
  (∀ q ∈ c.outputs, ∃ x, cs.lookup q.name = some (Expr.ref x) ∧ E x = Ec q.name)

theorem runIn_proj (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeR d m = true) (hA : AdmArrR d m arr)
    (mn i : String) (cs : List (String × Expr)) (hin : Stmt.inst mn i cs ∈ m.body) (c : Module)
    (hf : findMod d mn = some c) (hwoc : WOH d (arr c))
    (hwrc : ∀ n ∈ wrsH d (arr c), n ∉ inNames c) :
    ∀ (k : Nat) (seedK : Nat → (String → Nat) → Env) (st : HSt) (envs : List Env) (sts : List HSt),
      runHSRTrace d arr m seedK k st = some (envs, sts) →
      ∃ cenvs,
        runIn d arr c (seedFwd c k (insCOf (declWidth m) cs envs)) k (fun p => st (i :: p)) =
          some cenvs ∧
        ∀ t, t < k → ∃ E Ec S, envs[t]? = some E ∧ cenvs[t]? = some Ec ∧ sts[t]? = some S ∧
          ProjAtR (declWidth m) c cs E Ec := by
  have hmemM : Stmt.inst mn i cs ∈ arr m := hA.1.mem_iff.mpr hin
  obtain ⟨c0, hf0, hprim, hsane, hnd, hol, hcsnd, hall, hcov, href⟩ :=
    connsOkR_facts (hierR_inst_ok hS hin)
  have hc : c = c0 := by rw [hf] at hf0; exact Option.some.inj hf0
  subst hc
  have hinok : instOkR c cs = true := by unfold instOkR; rw [hprim, hall]; rfl
  have hdecl : ((instDecls (arr m)).map (·.2.1)).Nodup := by
    rw [← instNames_eq]
    exact (instNames_perm hA.1).nodup_iff.mpr (hierR_inst_unique hS)
  have hmemD : (mn, i, cs) ∈ instDecls (arr m) := (mem_instDecls_iff _ _).mpr hmemM
  intro k
  induction k with
  | zero =>
    intro seedK st envs sts hrun
    simp only [runHSRTrace, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨[], rfl, fun t ht => absurd ht (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro seedK st envs sts hrun
    simp only [runHSRTrace] at hrun
    cases hs : stepHSR d arr m st (seedK k (restrictTo (regOuts (arr m)) (st []))) with
    | none => simp [hs] at hrun
    | some r =>
      obtain ⟨envF, ups⟩ := r
      cases hr : runHSRTrace d arr m seedK k (applyH st ups) with
      | none => simp [hs, hr] at hrun
      | some q =>
        obtain ⟨rest, sts'⟩ := q
        simp [hs, hr] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        obtain ⟨_, hfold, hupsR⟩ := stepHSR_some_inv hs
        have hG := good_of_fold d (declWidth m) _ (instEvalF_laws d arr _ st (declWidth m)) (arr m) _
          envF hA.2.1 hfold
        obtain ⟨l, hl, hlE⟩ := hG.2 _ hmemM
        have hl' : instEvalF d arr (combR d arr (d.modules.length + 1)) st (declWidth m) mn i cs envF
            = some l := by simpa [cellVals] using hl
        obtain ⟨c1, seed, envC, hf1, _, hsd, hcc, hw⟩ := instEvalF_some hl'
        have hc1 : c1 = c := by rw [hf] at hf1; exact (Option.some.inj hf1).symm
        subst hc1
        obtain ⟨c2, seed2, envC2, upsC, hf2, _, hsd2, hcc2, hup, hslice⟩ :=
          upsR_slice hupsR hdecl hmemD
        have hc2 : c2 = c1 := by rw [hf] at hf2; exact Option.some.inj hf2 ▸ rfl
        subst hc2
        have hse : seed2 = seed := Option.some.inj (hsd2.symm.trans hsd)
        subst hse
        have hee : envC2 = envC := Option.some.inj (hcc2.symm.trans hcc)
        subst hee
        -- the child's cycle, stand-alone
        have hstepR : stepR d arr (d.modules.length + 1) c2 (fun p => st (i :: p)) seed2 =
            some (envC2, upsC) := by
          unfold stepR
          simp only [hcc, hup, Option.bind_eq_bind, Option.bind]
        have hseed1 := seedFwd_first c2 (declWidth m) cs envF rest k (regOuts (arr c2)) (st [i]) seed2
          hnd hsd
        have hstepIn : stepIn d arr c2 (seedFwd c2 (k + 1) (insCOf (declWidth m) cs (envF :: rest)))
            (fun p => st (i :: p)) k = some (envC2, applyH (fun p => st (i :: p)) upsC) := by
          unfold stepIn
          show (match stepR d arr (d.modules.length + 1) c2 (fun p => st (i :: p))
            (seedFwd c2 (k + 1) (insCOf (declWidth m) cs (envF :: rest)) k
              (restrictTo (regOuts (arr c2)) (st [i]))) with
            | some (e, ups) => some (e, applyH (fun p => st (i :: p)) ups)
            | none => none) = _
          rw [hseed1, hstepR]
        have hnext : (fun p => applyH st ups (i :: p)) = applyH (fun p => st (i :: p)) upsC := by
          rw [applyH_slice, hslice]
        obtain ⟨cenvs', hrunC', hcorr'⟩ := ih seedK (applyH st ups) rest sts' hr
        rw [hnext] at hrunC'
        refine ⟨envC2 :: cenvs', ?_, ?_⟩
        · have hcongr := runIn_congr_seed d arr c2
            (seedFwd c2 (k + 1) (insCOf (declWidth m) cs (envF :: rest)))
            (seedFwd c2 k (insCOf (declWidth m) cs rest)) k (applyH (fun p => st (i :: p)) upsC)
            (fun j hj => seedFwd_shift c2 _ cs envF rest k j hj)
          simp only [runIn, hstepIn, Option.bind_eq_bind, Option.bind]
          rw [hcongr, hrunC']
        · intro t ht
          cases t with
          | succ t =>
            obtain ⟨E, Ec, S, h1, h2, h3, h5⟩ := hcorr' t (by omega)
            exact ⟨E, Ec, S, by simpa using h1, by simpa using h2, by simpa using h3, h5⟩
          | zero =>
            refine ⟨envF, envC2, st, rfl, rfl, rfl, ?_, ?_⟩
            · intro p hpm
              obtain ⟨e0, he0, hsc⟩ := childSeedS_inv c2 cs (declWidth m) envF _ _ seed2 hsd
              obtain ⟨hz, hp⟩ := childSeed_val c2 cs (declWidth m) envF e0 he0 hnd
              obtain ⟨ex, hl2, hv⟩ := hp p hpm
              have hpn : p.name ∈ inNames c2 := List.mem_map.mpr ⟨p, hpm, rfl⟩
              have hfoldC : evalAssignsI (declWidth c2)
                  (instEvalF d arr (combR d arr d.modules.length) (fun q => st (i :: q)) (declWidth c2))
                  (arr c2) seed2 = some envC2 := by
                simpa [combR] using hcc
              have hGc := good_of_fold d (declWidth c2) _
                (instEvalF_laws d arr _ (fun q => st (i :: q)) (declWidth c2)) (arr c2) seed2 envC2
                hwoc hfoldC
              have hkeep := hGc.1 p.name (fun h => hwrc _ h hpn)
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
              have hmemo := outWrites_mem c2 cs envC2 l hw q.name x hqq
                (List.any_eq_true.mpr ⟨q, hq, by simp⟩)
              exact hlE _ hmemo

/-! ## L3 (arrangements): the parent's admissible arrangement restricted to a sub-design -/

theorem rdH_agree {d1 d2 : Design} (s : Stmt)
    (h : ∀ mn i cs, s = Stmt.inst mn i cs → findMod d1 mn = findMod d2 mn) : rdH d1 s = rdH d2 s := by
  cases s with
  | inst mn i cs => simp only [rdH, instIns, h mn i cs rfl]
  | assign l r => rfl
  | register _ _ _ _ _ => rfl
  | memory _ _ _ _ _ _ _ _ _ _ _ _ => rfl

theorem wrH_agree {d1 d2 : Design} (s : Stmt)
    (h : ∀ mn i cs, s = Stmt.inst mn i cs → findMod d1 mn = findMod d2 mn) : wrH d1 s = wrH d2 s := by
  cases s with
  | inst mn i cs => simp only [wrH, instOuts, h mn i cs rfl]
  | assign l r => rfl
  | register _ _ _ _ _ => rfl
  | memory _ _ _ _ _ _ _ _ _ _ _ _ => rfl

theorem wrsH_agree {d1 d2 : Design} : ∀ b : List Stmt,
    (∀ mn i cs, Stmt.inst mn i cs ∈ b → findMod d1 mn = findMod d2 mn) → wrsH d1 b = wrsH d2 b := by
  intro b
  induction b with
  | nil => intro _; rfl
  | cons s rest ih =>
    intro h
    simp only [wrsH, List.flatMap_cons] at ih ⊢
    rw [wrH_agree s (fun mn i cs hs => h mn i cs (hs ▸ List.mem_cons_self ..)),
      ih (fun mn i cs hm => h mn i cs (List.mem_cons_of_mem _ hm))]

/-- `WOH` only reads the resolution of the instances of the body. -/
theorem WOH_agree {d1 d2 : Design} : ∀ b : List Stmt,
    (∀ mn i cs, Stmt.inst mn i cs ∈ b → findMod d1 mn = findMod d2 mn) → WOH d1 b → WOH d2 b := by
  intro b
  induction b with
  | nil => intro _ _; trivial
  | cons s rest ih =>
    intro h hw
    obtain ⟨hrd, hwr, hnd, hrest⟩ := hw
    have hs : ∀ mn i cs, s = Stmt.inst mn i cs → findMod d1 mn = findMod d2 mn :=
      fun mn i cs e => h mn i cs (e ▸ List.mem_cons_self ..)
    have hr : ∀ mn i cs, Stmt.inst mn i cs ∈ rest → findMod d1 mn = findMod d2 mn :=
      fun mn i cs hm => h mn i cs (List.mem_cons_of_mem _ hm)
    refine ⟨?_, ?_, ?_, ih hr hrest⟩
    · intro n hn
      rw [← rdH_agree s hs] at hn
      rw [← wrsH_agree rest hr, ← wrH_agree s hs]
      exact hrd n hn
    · intro n hn
      rw [← wrH_agree s hs] at hn
      rw [← wrsH_agree rest hr]
      exact hwr n hn
    · rw [← wrH_agree s hs]; exact hnd

/-! ## L5: the instance step of a NON-LEAF child, from the child's own stored theorem -/

theorem hierR_names {d : Design} {m : Module} (h : HierShapeR d m = true) :
    (d.modules.map (·.name)).Nodup ∧ ∀ x ∈ d.modules, x ≠ m := by
  simp only [HierShapeR, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, hn⟩, hC⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  refine ⟨hn, ?_⟩
  intro x hx hxm
  subst hxm
  have h2 : (d.modules.map (·.name)).contains x.name = false := hC
  have h3 : x.name ∈ d.modules.map (·.name) := List.mem_map.mpr ⟨x, hx, rfl⟩
  simp [List.contains_eq_mem, h3] at h2

/-- L5. For the instance `inst mn i cs` of the NON-LEAF child `c` (resolved in the parent's real design
`d`), whose own stored theorem `hU : U2HRStmtR ck c dC g` is stated on a sub-design `dC` (its modules are
modules of `d`), every output wire of the instance at cycle `t0` is the child's declared output on the
stream the child's ports read, provided the stream `F` agrees with the parent's wires at the cycles
`≤ t0` (`kid_seq_multi` for a non-leaf child).  The child is NOT unfolded: only `hU`, the projection
`runIn_proj` (L2), the prefix and seed causality (L4) and the transfer `runHSR_runIn` (L3) are used. -/
theorem kid_seq_R (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeR d m = true) (hA : AdmArrR d m arr)
    (hwr : ∀ n ∈ wrsH d (arr m), n ∉ inNames m)
    (cc : Contract) (htie : cc.clkRst = designClkRst d m)
    (ins : Nat → String → Nat) (hok : InputsOk cc m ins) (K : Nat) (envs : List Env)
    (sts : List HSt)
    (hrun : runHSRTrace d arr m (seedFwd m K ins) K (st0HR d m) = some (envs, sts))
    (mn i : String) (cs : List (String × Expr)) (hin : Stmt.inst mn i cs ∈ m.body)
    (c : Module) (hf : findMod d mn = some c)
    (hnl : leafBody c.body = false) (hordc : OrderHS d c)
    (dC : Design) (hsub : ∀ x ∈ dC.modules, x ∈ d.modules)
    (ck : Contract) (g : ck.table.Ty) (hU : U2HRStmtR ck c dC g)
    (hclkc : ck.clkRst = regClkRst c.body)
    (hconn : ∀ p ∈ c.inputs, ∃ x, cs.lookup p.name = some (Expr.ref x) ∧
      (ck.dataInputs.any (·.name == p.name) = true ∨ x ∈ inNames m))
    (hrstnd : ∀ kr, ck.clkRst = some kr → ck.dataInputs.any (·.name == kr.2) = false)
    (F : Nat → String → Nat)
    (hrange : ∀ t, ∀ p ∈ ck.dataInputs, F t p.name < 2 ^ declWidth c p.name)
    (t0 : Nat) (ht0 : t0 < K)
    (hrunF : ∀ s, s ≤ t0 → ∀ E, envs[s]? = some E → ∀ p ∈ ck.dataInputs,
      ∃ x, cs.lookup p.name = some (Expr.ref x) ∧ E x = F s p.name) :
    ∀ E, envs[t0]? = some E → ∀ q ∈ c.outputs,
      ∃ x, cs.lookup q.name = some (Expr.ref x) ∧
        E x = srcOf ck g (netIn ck cs ins F) q.name t0 := by
  obtain ⟨_, hcore, _, hShC, _, _, _, _, hout⟩ := hU
  have hcmem : c ∈ d.modules := findMod_mem hf
  have hndD := (hierR_names hS).1
  have hSub : SubDesign dC d := subDesign_of_subset hndD hsub
  obtain ⟨hresTop, hresMods⟩ := HierShapeR_resolved hShC
  obtain ⟨hndC, hneC⟩ := hierR_names hShC
  have hfuel : fuelR dC ≤ d.modules.length + 1 :=
    fuel_le_of_sub hndC hsub hcmem (fun h => hneC c h rfl)
  have hperm := (hA.2.2 c hcmem).1
  have hwoc : WOH d (arr c) := (hA.2.2 c hcmem).2.2 hnl
  have hwrc : ∀ n ∈ wrsH d (arr c), n ∉ inNames c := by
    obtain ⟨b0, hb0⟩ := hordc
    exact orderOkHS_hwr hb0 hperm
  -- the parent's arrangement is admissible for the child's own design
  have hAdmC : AdmArrR dC c arr := by
    refine ⟨hperm, ?_, ?_⟩
    · refine WOH_agree _ ?_ hwoc
      intro mn' i' cs' hmem
      have hb : Stmt.inst mn' i' cs' ∈ c.body := hperm.mem_iff.mp hmem
      obtain ⟨c', hf'⟩ := hresTop mn' i' cs' hb
      rw [hf', hSub _ _ hf']
    · intro x hx
      obtain ⟨hp, hwo, hwoh⟩ := hA.2.2 x (hsub x hx)
      refine ⟨hp, hwo, fun hl => ?_⟩
      refine WOH_agree _ ?_ (hwoh hl)
      intro mn' i' cs' hmem
      have hb : Stmt.inst mn' i' cs' ∈ x.body := hp.mem_iff.mp hmem
      obtain ⟨c', hf'⟩ := hresMods x hx mn' i' cs' hb
      rw [hf', hSub _ _ hf']
  -- the initial state of the slice is the child's own initial state
  have hslice0 : (fun p => st0HR d m (i :: p)) = st0HR dC c := by
    funext p
    show st0Path d m (i :: p) = st0Path dC c p
    rw [st0Path_cons (hierR_inst_unique hS) hin hf p]
    exact (st0Path_agree hSub hresMods p c hresTop).symm
  obtain ⟨cenvs, hrunC, hcorr⟩ := runIn_proj d arr m hS hA mn i cs hin c hf hwoc hwrc K _ _ envs sts hrun
  rw [hslice0] at hrunC
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
        instPair_tie d m (hierR_clk hS) mn i cs c hin hf hreg cc htie
      have hkk : (kc, kr') = kr := Option.some.inj (hrc.symm.trans hkr)
      subst hkk
      have hnd := hrstnd (kc, kr') (hclkc.trans hrc)
      have : netIn ck cs ins F t kr' = ins t y := by simp [netIn, hnd, insCIn, h2]
      show netIn ck cs ins F t kr' = 0
      rw [this]
      exact hok.2 t (x, y) hcl
  -- the seeds agree at every cycle `s ≤ t0`
  have hpre : ∀ s, s ≤ t0 → ∀ E, envs[s]? = some E → ∀ n ∈ inNames c,
      netIn ck cs ins F s n = insCOf (declWidth m) cs envs s n := by
    intro s hs E hE n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    obtain ⟨x, hl, hx⟩ := hconn p hp
    by_cases hd : ck.dataInputs.any (·.name == p.name) = true
    · obtain ⟨p', hp', hpn⟩ := List.any_eq_true.mp hd
      have hpn' : p'.name = p.name := by simpa using hpn
      obtain ⟨x', hl', hEx'⟩ := hrunF s hs E hE p' hp'
      rw [hpn'] at hl' hEx'
      have hxx : x' = x := by
        rw [hl] at hl'; exact (Expr.ref.inj (Option.some.inj hl')).symm
      subst hxx
      have h1 : netIn ck cs ins F s p.name = F s p.name := by simp [netIn, hd]
      rw [h1, ← hEx']
      simp [insCOf, hl, hE, evalExpr]
    · have hxin : x ∈ inNames m := hx.resolve_left hd
      have hEx := runHSR_inputs d arr m hA.2.1 hwr ins K K (Nat.le_refl K) _ envs sts hrun s (by omega)
        E hE x hxin
      have hd' : ck.dataInputs.any (·.name == p.name) = false := by simpa using hd
      simp [netIn, hd', insCIn, insCOf, hl, hE, evalExpr, hEx]
  have hseed : ∀ j, j < t0 + 1 → seedFwd c (t0 + 1) (insCOf (declWidth m) cs envs) j =
      seedFwd c (t0 + 1) (netIn ck cs ins F) j := by
    intro j hj
    funext st n
    simp only [seedFwd]
    by_cases hn : (c.inputs.map (·.name)).contains n = true
    · rw [if_pos hn, if_pos hn]
      obtain ⟨E, Ec, S, hE, _⟩ := hcorr (t0 + 1 - 1 - j) (by omega)
      exact (hpre _ (by omega) E hE n (List.contains_iff_mem.mp hn)).symm
    · rw [if_neg hn, if_neg hn]
  -- the child's run, cut at `t0 + 1` cycles
  obtain ⟨L', hL', hLe⟩ := runIn_prefix d arr c
    (seedFwd c K (insCOf (declWidth m) cs envs)) (t0 + 1) (K - (t0 + 1)) (st0HR dC c) cenvs
    (by rw [show t0 + 1 + (K - (t0 + 1)) = K by omega]; exact hrunC)
  have hshift : ∀ j, j < t0 + 1 →
      (fun j => seedFwd c K (insCOf (declWidth m) cs envs) (j + (K - (t0 + 1)))) j =
        seedFwd c (t0 + 1) (insCOf (declWidth m) cs envs) j := by
    intro j hj
    funext st n
    simp only [seedFwd]
    have : K - 1 - (j + (K - (t0 + 1))) = t0 + 1 - 1 - j := by omega
    rw [this]
  rw [runIn_congr_seed d arr c _ _ (t0 + 1) _ hshift, runIn_congr_seed d arr c _ _ (t0 + 1) _ hseed]
    at hL'
  obtain ⟨envs', hrun', hall⟩ := hout arr hAdmC (netIn ck cs ins F) hok' (t0 + 1)
  have hrunIn := runHSR_runIn hSub arr hfuel c _ _ _ _ hrun'
  have hce : envs' = L' := Option.some.inj (hrunIn.symm.trans hL')
  intro E hE q hq
  obtain ⟨E0, Ec, S, hE0, hEc, _, hproj⟩ := hcorr t0 ht0
  have hEE : E = E0 := Option.some.inj (hE.symm.trans hE0)
  subst hEE
  obtain ⟨x, hl, hxv⟩ := hproj.2 q hq
  refine ⟨x, hl, ?_⟩
  have hqk : q ∈ ck.outputs := by rw [← hcore.2.2.2.2.2.1]; exact hq
  obtain ⟨env, he, hv⟩ := hall t0 (by omega) q hqk
  rw [hce, hLe, List.getElem?_take_of_lt (by omega), hEc] at he
  have hee : env = Ec := (Option.some.inj he).symm
  subst hee
  rw [hxv]; exact hv

end Tools.VedU2HierRec
