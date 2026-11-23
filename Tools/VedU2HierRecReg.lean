import Tools.VedU2HierRecOr
import Tools.VedU2HierStep
import Tools.VedU2HierNet
import Tools.VedU2HierReg

/-!
# The register parent over the recursive semantics: closed-run facts and the composition theorem (CANDIDATE)

`outputsOnHSR_of_stepR` (the analogue of `outputsOnHS_of_stepR`, whole-run instance facts),
`closed_run_asgR` / `closed_run_asgOfR` / `closed_run_regR` (the analogues of the depth-1 closed-run
facts: an assignment of the arrangement holds in the closed run's environment; a register output
carries the cycle's pre-update state).  The statements are those of the depth-1 lemmas with
`runHSRTrace`, `st0HR`, `AdmArrR` and the recursive instance laws (`instEvalF_laws`).
-/

namespace Tools.VedU2HierRec

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier

theorem closed_run_asgR (d : Design) (arr : Module → List Stmt) (m : Module) (hA : AdmArrR d m arr)
    (b0 : List Stmt) (hp : (arr m).Perm b0) (hw0 : WOH d b0)
    (seed : Nat → (String → Nat) → Env) (K : Nat) (st : HSt) (envs : List Env) (sts : List HSt)
    (hrun : runHSRTrace d arr m seed K st = some (envs, sts)) (t : Nat) (ht : t < K)
    (E : Env) (hE : envs[t]? = some E) :
    ∀ l r, Stmt.assign l r ∈ b0 → evalExpr (declWidth m) E r = some (E l) := by
  intro l r hl
  obtain ⟨E', S, hE', _, hfold⟩ := runHSRTrace_cycle d arr m seed K st envs sts hrun t ht
  rw [hE] at hE'
  cases hE'
  have hfold0 := evalAssignsI_perm d _ _ (instEvalF_laws d arr _ S (declWidth m)) hp hA.2.1 hw0 hfold
  have hG := good_of_fold d _ _ (instEvalF_laws d arr _ S (declWidth m)) b0 _ E hw0 hfold0
  obtain ⟨l', hl', hlE⟩ := hG.2 _ hl
  simp only [cellVals] at hl'
  cases hv : evalExpr (declWidth m) E r with
  | none => simp [hv] at hl'
  | some v =>
    simp only [hv, Option.map_some, Option.some.injEq] at hl'
    subst hl'
    have := hlE (l, v) (List.mem_singleton_self _)
    simp only at this
    rw [this]


theorem closed_run_asgOfR (d : Design) (arr : Module → List Stmt) (m : Module) (hA : AdmArrR d m arr)
    (b0 : List Stmt) (hp : (arr m).Perm b0) (hw0 : WOH d b0)
    (seed : Nat → (String → Nat) → Env) (K : Nat) (st : HSt) (envs : List Env) (sts : List HSt)
    (hrun : runHSRTrace d arr m seed K st = some (envs, sts)) (t : Nat) (ht : t < K)
    (E : Env) (hE : envs[t]? = some E) :
    ∀ l r, asgOf b0 l = some r → evalExpr (declWidth m) E r = some (E l) :=
  fun l r h => closed_run_asgR d arr m hA b0 hp hw0 seed K st envs sts hrun t ht E hE l r (asgOf_mem h)

theorem closed_run_regR (d : Design) (arr : Module → List Stmt) (m : Module) (hA : AdmArrR d m arr)
    (b0 : List Stmt) (hp : (arr m).Perm b0) (hw0 : WOH d b0)
    (hwb : ∀ n ∈ wrsH d b0, n ∉ regOuts b0) (hri : ∀ n ∈ regOuts b0, n ∉ inNames m)
    (ins : Nat → String → Nat) (K : Nat) (envs : List Env) (sts : List HSt)
    (hrun : runHSRTrace d arr m (seedFwd m K ins) K (st0HR d m) = some (envs, sts))
    (t : Nat) (ht : t < K) (S : HSt) (E : Env) (hS : sts[t]? = some S) (hE : envs[t]? = some E) :
    ∀ r ∈ regOuts b0, E r = S [] r := by
  intro r hr
  obtain ⟨E', S', hE', hS', hfold⟩ := runHSRTrace_cycle d arr m (seedFwd m K ins) K (st0HR d m) envs sts hrun t ht
  rw [hE] at hE'; rw [hS] at hS'
  cases hE'; cases hS'
  have hfold0 := evalAssignsI_perm d _ _ (instEvalF_laws d arr _ S (declWidth m)) hp hA.2.1 hw0 hfold
  have hG := good_of_fold d _ _ (instEvalF_laws d arr _ S (declWidth m)) b0 _ E hw0 hfold0
  have hnw : r ∉ wrsH d b0 := fun h => hwb r h hr
  rw [hG.1 r hnw]
  have hrA : r ∈ regOuts (arr m) := (regOuts_perm_mem hp r).mpr hr
  have hne : ¬ ∃ a, a ∈ m.inputs ∧ a.name = r := by
    rintro ⟨a, ha, rfl⟩
    exact hri a.name hr (List.mem_map.mpr ⟨a, ha, rfl⟩)
  simp [seedFwd, restrictTo, hne, hrA]


theorem outputsOnHSR_of_stepR (c : Contract) (m : Module) (d : Design)
    (arr : Module → List Stmt) (f : c.table.Ty)
    (hS : HierShapeR d m = true) (hA : AdmArrR d m arr)
    (hsucc : SuccF d arr (fuelR d) m)
    (b0 : List Stmt) (hp : (arr m).Perm b0) (hw0 : WOH d b0) (hnd : (regOuts b0).Nodup)
    (hai0 : ∀ s ∈ b0, isAsgInstReg s = true)
    (Ow : (Nat → String → Nat) → String → Nat → Nat)
    (hkid : ∀ ins, InputsOk c m ins → ∀ K envs sts,
      runHSRTrace d arr m (seedFwd m K ins) K (st0HR d m) = some (envs, sts) →
      ∀ mn i cs, Stmt.inst mn i cs ∈ m.body → ∀ t, t < K → ∀ E, envs[t]? = some E →
        ∀ y ∈ instOuts d mn cs, E y = Ow ins y t)
    (R : (Nat → String → Nat) → Nat → (String → Nat) → Prop)
    (h0 : ∀ ins, InputsOk c m ins → R ins 0 (st0Of m))
    (hstep : ∀ ins, InputsOk c m ins → ∀ t p, R ins t p →
      ∃ E nx, evalAssignsI (declWidth m) (oracleIE d (fun y => Ow ins y t)) b0
          (seedIn m ins t (restrictTo (regOuts b0) p)) = some E ∧
        regNexts (declWidth m) (fun _ _ => 0) b0 E = some nx ∧
        (∀ o ∈ c.outputs, E o.name = srcOf c f ins o.name t) ∧
        R ins (t + 1) (applyNexts p nx)) :
    OutputsOnHSR c m d arr f := by
  intro ins hok K
  obtain ⟨envs, sts, hrun⟩ := runHSR_exists d arr m hS hA hsucc (seedFwd m K ins) K (st0HR d m)
  refine ⟨envs, ?_, ?_⟩
  · have := runHSRTrace_fst d arr m (seedFwd m K ins) K (st0HR d m)
    rw [hrun] at this
    simp at this
    exact this.symm
  -- one cycle: the closed run's cycle is the open fold, so `hstep` applies
  have cyc : ∀ t, t < K → ∀ S E, sts[t]? = some S → envs[t]? = some E → R ins t (S []) →
      (∀ o ∈ c.outputs, E o.name = srcOf c f ins o.name t) ∧
      ∀ nx, regNexts (declWidth m) (fun _ _ => 0) (arr m) E = some nx →
        R ins (t + 1) (applyNexts (S []) nx) := by
    intro t ht S E hS' hE' hR
    obtain ⟨E', S', hE2, hS2, hfold⟩ := runHSRTrace_cycle d arr m (seedFwd m K ins) K (st0HR d m)
      envs sts hrun t ht
    rw [hE'] at hE2; rw [hS'] at hS2
    cases hE2; cases hS2
    have hseed : seedFwd m K ins (K - 1 - t) (restrictTo (regOuts (arr m)) (S []))
        = seedIn m ins t (restrictTo (regOuts b0) (S [])) := by
      rw [restrictTo_perm hp]
      exact seedFwd_time m K ins ht _
    rw [hseed] at hfold
    have hfold0 := evalAssignsI_perm d _ _ (instEvalF_laws d arr _ S (declWidth m)) hp hA.2.1 hw0 hfold
    have hmem : ∀ s, s ∈ b0 → s ∈ m.body := fun s hs => hA.1.mem_iff.mp (hp.mem_iff.mpr hs)
    have hor := fold_oracle d _ _ (instEvalF_laws d arr _ S (declWidth m)) (fun y => Ow ins y t) b0 _ E
      hw0 hfold0 (fun mn i cs hin y hy => hkid ins hok K envs sts hrun mn i cs (hmem _ hin) t ht E hE' y hy)
    obtain ⟨E1, nx1, hE1, hn1, hout, hR'⟩ := hstep ins hok t (S []) hR
    rw [hE1] at hor
    cases hor
    refine ⟨hout, ?_⟩
    intro nx hnx
    have hperm : nx.Perm nx1 := by
      have := regNexts_perm (declWidth m) (fun _ _ => 0) E hp
      rw [hnx, hn1] at this
      simpa [OPerm] using this
    have hkeys : (nx1.map Prod.fst).Nodup := by
      rw [regNexts_keys _ _ _ b0 nx1 hn1, nextKeys_eq_regOuts b0 hai0]; exact hnd
    have heq : applyNexts (S []) nx = applyNexts (S []) nx1 :=
      applyNexts_perm hperm ((hperm.map Prod.fst).nodup_iff.mpr hkeys) _
    rw [heq]; exact hR'
  -- the invariant along the trace
  have chain : ∀ t, t < K → ∃ S, sts[t]? = some S ∧ R ins t (S []) := by
    intro t
    induction t with
    | zero =>
      intro ht
      obtain ⟨hs0, _⟩ := runHSRTrace_next d arr m (seedFwd m K ins) K (st0HR d m) envs sts hrun
      exact ⟨st0HR d m, hs0 ht, h0 ins hok⟩
    | succ t ih =>
      intro ht
      obtain ⟨S, hS', hR⟩ := ih (by omega)
      obtain ⟨_, hnx⟩ := runHSRTrace_next d arr m (seedFwd m K ins) K (st0HR d m) envs sts hrun
      obtain ⟨E, S2, S3, nx, hE2, hS2, hS3, hnx2, hS3r⟩ := hnx t ht
      rw [hS'] at hS2; cases hS2
      refine ⟨S3, hS3, ?_⟩
      rw [hS3r]
      exact (cyc t (by omega) S E hS' hE2 hR).2 nx hnx2
  intro t ht o ho
  obtain ⟨S, hS', hR⟩ := chain t ht
  obtain ⟨E, S2, hE2, hS2, _⟩ := runHSRTrace_cycle d arr m (seedFwd m K ins) K (st0HR d m) envs sts hrun t ht
  rw [hS'] at hS2; cases hS2
  exact ⟨E, hE2, (cyc t ht S E hS' hE2 hR).1 o ho⟩


/-- `runHSR_inputs` with the admissible-arrangement hypothesis (the shape of the depth-1 `runHS_inputs`). -/
theorem runHS_inputsR (d : Design) (arr : Module → List Stmt) (m : Module) (hA : AdmArrR d m arr)
    (hwr : ∀ n ∈ wrsH d (arr m), n ∉ inNames m) (inp : Nat → String → Nat) (K : Nat) :
    ∀ (k : Nat), k ≤ K → ∀ (st : HSt) (envs : List Env) (sts : List HSt),
      runHSRTrace d arr m (seedFwd m K inp) k st = some (envs, sts) →
      ∀ t, t < k → ∀ E, envs[t]? = some E → ∀ n ∈ inNames m, E n = inp (K - k + t) n :=
  runHSR_inputs d arr m hA.2.1 hwr inp K

end Tools.VedU2HierRec
