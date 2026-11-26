import Tools.VedU2HierReg

/-!
# H2c-state: the composition lemma for a parent whose instance inputs read its REGISTERS

`outputsOnHS_of_stepR` (H2b) requires `hkid`, the instances' oracle fact, for every trace of the
closed run.  When an instance's data input is a parent register output, the fact holds only along
states satisfying the parent invariant, so proving it first would be circular.

`outputsOnHS_of_stepRK` is the same theorem with ONE change: `hkid` is asked at cycle `t` only, for
the trace's own pre-update state `S` (`sts[t]? = some S`) AND under the invariant `R ins t (S [])`.
The proof is the same single induction over the cycles (`chain`): the invariant at `t` gives the
instance fact at `t` (`hkid`), which gives the open evaluation (`fold_oracle`), which gives the
outputs and the invariant at `t + 1` (`hstep`).  The instances read the PRE-update state (`S`), never
the next state.  The existence of the run is `runHS_exists`, as before.
-/

namespace Tools.VedU2Hier

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Hier

/-- THE COMPOSITION THEOREM FOR A PARENT WITH REGISTERS (H2b).  See the file header: `R` is the
parent-register invariant, `hkid` the instances' oracle (`kid_inst`), `hstep` one cycle of the open
parent from any state satisfying `R`. -/
theorem outputsOnHS_of_stepRK (c : Contract) (m : Module) (d : Design)
    (arr : Module → List Stmt) (f : c.table.Ty)
    (hS : HierShapeS d m = true) (hA : AdmArr d m arr)
    (hsupp : ExprsSupp m (arr m)) (hch : ∀ x ∈ d.modules, ChildSucc x (arr x))
    (b0 : List Stmt) (hp : (arr m).Perm b0) (hw0 : WOH d b0) (hnd : (regOuts b0).Nodup)
    (hai0 : ∀ s ∈ b0, isAsgInstReg s = true)
    (Ow : (Nat → String → Nat) → String → Nat → Nat)
    (R : (Nat → String → Nat) → Nat → (String → Nat) → Prop)
    (h0 : ∀ ins, InputsOk c m ins → R ins 0 (st0Of m))
    (hkid : ∀ ins, InputsOk c m ins → ∀ K envs sts,
      runHSTrace d arr m (seedFwd m K ins) K (st0H d m) = some (envs, sts) →
      ∀ t, t < K → ∀ S E, sts[t]? = some S → envs[t]? = some E → R ins t (S []) →
        ∀ mn i cs, Stmt.inst mn i cs ∈ m.body → ∀ y ∈ instOuts d mn cs, E y = Ow ins y t)
    (hstep : ∀ ins, InputsOk c m ins → ∀ t p, R ins t p →
      ∃ E nx, evalAssignsI (declWidth m) (oracleIE d (fun y => Ow ins y t)) b0
          (seedIn m ins t (restrictTo (regOuts b0) p)) = some E ∧
        regNexts (declWidth m) (fun _ _ => 0) b0 E = some nx ∧
        (∀ o ∈ c.outputs, E o.name = srcOf c f ins o.name t) ∧
        R ins (t + 1) (applyNexts p nx)) :
    OutputsOnHS c m d arr f := by
  intro ins hok K
  obtain ⟨envs, sts, hrun⟩ := runHS_exists d arr m hS hA hsupp hch (seedFwd m K ins) K (st0H d m)
  refine ⟨envs, ?_, ?_⟩
  · have := runHSTrace_fst d arr m (seedFwd m K ins) K (st0H d m)
    rw [hrun] at this
    simp at this
    exact this.symm
  -- one cycle: the closed run's cycle is the open fold, so `hstep` applies
  have cyc : ∀ t, t < K → ∀ S E, sts[t]? = some S → envs[t]? = some E → R ins t (S []) →
      (∀ o ∈ c.outputs, E o.name = srcOf c f ins o.name t) ∧
      ∀ nx, regNexts (declWidth m) (fun _ _ => 0) (arr m) E = some nx →
        R ins (t + 1) (applyNexts (S []) nx) := by
    intro t ht S E hS' hE' hR
    obtain ⟨E', S', hE2, hS2, hfold⟩ := runHSTrace_cycle d arr m (seedFwd m K ins) K (st0H d m)
      envs sts hrun t ht
    rw [hE'] at hE2; rw [hS'] at hS2
    cases hE2; cases hS2
    have hseed : seedFwd m K ins (K - 1 - t) (restrictTo (regOuts (arr m)) (S []))
        = seedIn m ins t (restrictTo (regOuts b0) (S [])) := by
      rw [restrictTo_perm hp]
      exact seedFwd_time m K ins ht _
    rw [hseed] at hfold
    have hfold0 := evalAssignsI_perm d _ _ (instEvalS_laws d arr S (declWidth m)) hp hA.2.1 hw0 hfold
    have hmem : ∀ s, s ∈ b0 → s ∈ m.body := fun s hs => hA.1.mem_iff.mp (hp.mem_iff.mpr hs)
    have hor := fold_oracle d _ _ (instEvalS_laws d arr S (declWidth m)) (fun y => Ow ins y t) b0 _ E
      hw0 hfold0 (fun mn i cs hin y hy => hkid ins hok K envs sts hrun t ht S E hS' hE' hR mn i cs (hmem _ hin) y hy)
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
      obtain ⟨hs0, _⟩ := runHSTrace_next d arr m (seedFwd m K ins) K (st0H d m) envs sts hrun
      exact ⟨st0H d m, hs0 ht, h0 ins hok⟩
    | succ t ih =>
      intro ht
      obtain ⟨S, hS', hR⟩ := ih (by omega)
      obtain ⟨_, hnx⟩ := runHSTrace_next d arr m (seedFwd m K ins) K (st0H d m) envs sts hrun
      obtain ⟨E, S2, S3, nx, hE2, hS2, hS3, hnx2, hS3r⟩ := hnx t ht
      rw [hS'] at hS2; cases hS2
      refine ⟨S3, hS3, ?_⟩
      rw [hS3r]
      exact (cyc t (by omega) S E hS' hE2 hR).2 nx hnx2
  intro t ht o ho
  obtain ⟨S, hS', hR⟩ := chain t ht
  obtain ⟨E, S2, hE2, hS2, _⟩ := runHSTrace_cycle d arr m (seedFwd m K ins) K (st0H d m) envs sts hrun t ht
  rw [hS'] at hS2; cases hS2
  exact ⟨E, hE2, (cyc t ht S E hS' hE2 hR).1 o ho⟩

end Tools.VedU2Hier
