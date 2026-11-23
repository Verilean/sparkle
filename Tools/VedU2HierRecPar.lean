import Tools.VedU2HierRecRun
import Tools.VedU2HierMultiOut

/-!
# The parent composition theorem for the recursive statement (CANDIDATE; Tools/VedU2HierRec.lean)

`outputsOnHSR_of_stepRKH` is the analogue of `outputsOnHS_of_stepRKH_multi`: the parent's own
register loop (`hstep`, `h0`) together with a per-instance output fact (`hkid`, supplied for a
leaf child by `kid_seq_multi`-style lemmas and for a NON-LEAF child by `kid_seq_R`, which uses
the child's own `U2HRStmtR` theorem on a sub-design) gives `OutputsOnHSR`.  The run exists by
`runHSR_exists` (from `SuccF` of the top at `fuelR d`); the cycle and next-state facts are
`runHSRTrace_cycle` / `runHSRTrace_next`.  The proof is the structure of the depth-1 proof with
the recursive semantics' laws (`instEvalF_laws`); nothing is unfolded in a child.
-/

namespace Tools.VedU2HierRec

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier

/-- `outputsOnHS_of_stepRK_multi` for a design with a SEQUENTIAL child: `hkid` at cycle `t` also receives the invariant `R` at every
earlier cycle `s ≤ t` (the chain induction already has it; the combinational statement only needed cycle `t`).  Same
conclusion; the proof is the copy with the invariant of `chain` strengthened to the history. -/
theorem outputsOnHSR_of_stepRKH (c : Contract) (m : Module) (d : Design)
    (arr : Module → List Stmt) (f : c.table.Ty)
    (hS : HierShapeR d m = true) (hA : AdmArrR d m arr)
    (hsucc : SuccF d arr (fuelR d) m)
    (b0 : List Stmt) (hp : (arr m).Perm b0) (hw0 : WOH d b0) (hnd : (regOuts b0).Nodup)
    (hai0 : ∀ s ∈ b0, isAsgInstReg s = true)
    (Ow : (Nat → String → Nat) → String → Nat → Nat)
    (R : (Nat → String → Nat) → Nat → (String → Nat) → Prop)
    (h0 : ∀ ins, InputsOk c m ins → R ins 0 (st0Of m))
    (hkid : ∀ ins, InputsOk c m ins → ∀ K envs sts,
      runHSRTrace d arr m (seedFwd m K ins) K (st0HR d m) = some (envs, sts) →
      ∀ t, t < K → ∀ S E, sts[t]? = some S → envs[t]? = some E → R ins t (S []) →
        (∀ s, s ≤ t → ∀ S' E', sts[s]? = some S' → envs[s]? = some E' → R ins s (S' [])) →
        ∀ mn i cs, Stmt.inst mn i cs ∈ m.body → ∀ y ∈ instOuts d mn cs, E y = Ow ins y t)
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
      (∀ s, s ≤ t → ∀ S' E', sts[s]? = some S' → envs[s]? = some E' → R ins s (S' [])) →
      (∀ o ∈ c.outputs, E o.name = srcOf c f ins o.name t) ∧
      ∀ nx, regNexts (declWidth m) (fun _ _ => 0) (arr m) E = some nx →
        R ins (t + 1) (applyNexts (S []) nx) := by
    intro t ht S E hS' hE' hR hh
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
      hw0 hfold0 (fun mn i cs hin y hy => hkid ins hok K envs sts hrun t ht S E hS' hE' hR hh mn i cs (hmem _ hin) y hy)
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
  -- the invariant along the trace, with its history
  have histOf : ∀ t, (∀ s, s ≤ t → ∃ S, sts[s]? = some S ∧ R ins s (S [])) →
      (∀ s, s ≤ t → ∀ S' E', sts[s]? = some S' → envs[s]? = some E' → R ins s (S' [])) := by
    intro t h s hs S' E' hS' _
    obtain ⟨S, hS, hR⟩ := h s hs
    rw [hS'] at hS; cases hS; exact hR
  have chain : ∀ t, t < K → ∀ s, s ≤ t → ∃ S, sts[s]? = some S ∧ R ins s (S []) := by
    intro t
    induction t with
    | zero =>
      intro ht s hs
      have hs0 : s = 0 := by omega
      subst hs0
      obtain ⟨hs0, _⟩ := runHSRTrace_next d arr m (seedFwd m K ins) K (st0HR d m) envs sts hrun
      exact ⟨st0HR d m, hs0 ht, h0 ins hok⟩
    | succ t ih =>
      intro ht s hs
      by_cases hle : s ≤ t
      · exact ih (by omega) s hle
      · have hst : s = t + 1 := by omega
        subst hst
        obtain ⟨S, hS', hR⟩ := ih (by omega) t (Nat.le_refl t)
        obtain ⟨_, hnx⟩ := runHSRTrace_next d arr m (seedFwd m K ins) K (st0HR d m) envs sts hrun
        obtain ⟨E, S2, S3, nx, hE2, hS2, hS3, hnx2, hS3r⟩ := hnx t ht
        rw [hS'] at hS2; cases hS2
        refine ⟨S3, hS3, ?_⟩
        rw [hS3r]
        exact (cyc t (by omega) S E hS' hE2 hR (histOf t (ih (by omega)))).2 nx hnx2
  intro t ht o ho
  obtain ⟨S, hS', hR⟩ := chain t ht t (Nat.le_refl t)
  obtain ⟨E, S2, hE2, hS2, _⟩ := runHSRTrace_cycle d arr m (seedFwd m K ins) K (st0HR d m) envs sts hrun t ht
  rw [hS'] at hS2; cases hS2
  exact ⟨E, hE2, (cyc t ht S E hS' hE2 hR (histOf t (chain t ht))).1 o ho⟩

end Tools.VedU2HierRec
