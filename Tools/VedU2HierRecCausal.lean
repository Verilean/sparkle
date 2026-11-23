import Tools.VedU2HierRecPar

/-!
# Causality of a NON-LEAF child from its own recursive theorem (CANDIDATE; Tools/VedU2HierRec.lean)

The recursive analogues of `srcOf_prefix`, `call_causal`, `bundle_causal`, `bundle_causal_agree`
(`Tools/VedU2HierMultiOut.lean`), with `hU : U2HRStmtR ck c dC g` in place of `hU : U1Stmt ck c g`: the
output of a module at cycle `t` depends on its input stream at the cycles `≤ t` only.  It is what the
open parent's `hOs` needs for a call of a struct-valued SEQUENTIAL middle module (a call's result at
cycle `i` reads the arguments at the cycles `≤ i`).  The only new ingredient is `runHSR_congr_seed`
(the recursive run depends on the seeds of the cycles it runs only; the analogue of `runIn_congr_seed`);
nothing is unfolded in a child.
-/

namespace Tools.VedU2HierRec

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier

theorem runHSR_congr_seed (d : Design) (arr : Module → List Stmt) (m : Module)
    (s1 s2 : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : HSt), (∀ j, j < k → s1 j = s2 j) →
      runHSR d arr m s1 k st = runHSR d arr m s2 k st := by
  intro k
  induction k with
  | zero => intro st _; rfl
  | succ k ih =>
    intro st h
    simp only [runHSR, h k (Nat.lt_succ_self k)]
    cases stepHSR d arr m st (s2 k (restrictTo (regOuts (arr m)) (st []))) with
    | none => rfl
    | some r => simp only [ih _ (fun j hj => h j (by omega))]

/-- CAUSALITY OF A CHILD FROM ITS OWN RECURSIVE THEOREM. -/
theorem srcOf_prefix_R {ck : Contract} {c : Module} {dC : Design} {g : ck.table.Ty} (hU : U2HRStmtR ck c dC g)
    (I1 I2 : Nat → String → Nat) (hok1 : InputsOk ck c I1) (hok2 : InputsOk ck c I2) (t : Nat)
    (h : ∀ t' ≤ t, ∀ n, I1 t' n = I2 t' n) :
    ∀ q ∈ ck.outputs, srcOf ck g I1 q.name t = srcOf ck g I2 q.name t := by
  obtain ⟨_, _, _, _, _, _, _, ⟨arr, harr⟩, hout⟩ := hU
  obtain ⟨e1, r1, a1⟩ := hout arr harr I1 hok1 (t + 1)
  obtain ⟨e2, r2, a2⟩ := hout arr harr I2 hok2 (t + 1)
  have hseed : ∀ j, j < t + 1 → seedFwd c (t + 1) I1 j = seedFwd c (t + 1) I2 j := by
    intro j hj
    funext st n
    simp only [seedFwd]
    split
    · exact h (t + 1 - 1 - j) (by omega) n
    · rfl
  rw [runHSR_congr_seed _ _ _ _ _ (t + 1) _ hseed] at r1
  have he : e1 = e2 := Option.some.inj (r1.symm.trans r2)
  subst he
  intro q hq
  obtain ⟨env1, h1, v1⟩ := a1 t (by omega) q hq
  obtain ⟨env2, h2, v2⟩ := a2 t (by omega) q hq
  have : env1 = env2 := Option.some.inj (h1.symm.trans h2)
  subst this
  rw [← v1, ← v2]

theorem call_causal_R {ck : Contract} {c : Module} {dC : Design} {g : ck.table.Ty} (hU : U2HRStmtR ck c dC g)
    (A B : ArgSigs ck.table.ins) (i : Nat)
    (h : ∀ k ≤ i, obsArgs ck.table.ins A k = obsArgs ck.table.ins B k) :
    ∀ o ∈ ck.outputs,
      ((ck.outNames.zip (ck.table.out.obs ((applyArgs ck.table.ins g A).val i))).lookup o.name).getD 0 =
      ((ck.outNames.zip (ck.table.out.obs ((applyArgs ck.table.ins g B).val i))).lookup o.name).getD 0 := by
  have hcorr := hU.1
  have hwid := hU.2.2.2.2.1
  obtain ⟨_, hlen, _, hnd4, _⟩ := hcorr
  have hnd : ck.inNames.Nodup := by
    have := hnd4
    rw [List.append_assoc] at this
    exact (List.nodup_append.mp this).1
  have hrn : ∀ kr, ck.clkRst = some kr → kr.2 ∉ ck.inNames := by
    intro kr hkr hmem
    rw [List.append_assoc] at hnd4
    exact (List.nodup_append.mp hnd4).2.2 kr.2 hmem kr.2 (by
      rw [List.mem_append]; right; simp [clkRstNames, hkr]) rfl
  have hok : ∀ (X : ArgSigs ck.table.ins),
      InputsOk ck c (streamOf ck.inNames (obsArgs ck.table.ins X)) := by
    intro X
    refine ⟨?_, ?_⟩
    · intro t p hp
      obtain ⟨⟨n, pt⟩, hmem, rfl⟩ := List.mem_map.mp hp
      have h1 := streamOf_lt ck.table.ins ck.inNames X t hnd hlen n pt hmem
      have h2 := (hwid.2.1 ⟨n, pt.hw⟩ (List.mem_map.mpr ⟨(n, pt), hmem, rfl⟩)).2
      rw [h2]
      cases pt <;> simpa [PTy.hw, PTy.width, HWType.bitWidth] using h1
    · intro t kr hkr
      simp only [streamOf]
      rw [List.lookup_eq_none_iff.mpr (fun q hq => by
        have := (List.of_mem_zip hq).1
        have hne : q.1 ≠ kr.2 := fun e => hrn kr hkr (e ▸ this)
        simpa [beq_iff_eq] using Ne.symm hne)]
      rfl
  have hagree : ∀ t' ≤ i, ∀ n, streamOf ck.inNames (obsArgs ck.table.ins A) t' n =
      streamOf ck.inNames (obsArgs ck.table.ins B) t' n := by
    intro t' ht' n
    simp only [streamOf, h t' ht']
  intro o ho
  have := srcOf_prefix_R hU _ _ (hok A) (hok B) i hagree o ho
  rw [srcOf, srcOf] at this
  rw [applyIns_streamOf (R := Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain ck.table.out.val)
      ck.table.ins ck.inNames A g hlen hnd,
    applyIns_streamOf (R := Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain ck.table.out.val)
      ck.table.ins ck.inNames B g hlen hnd] at this
  simpa using this

/-- The call's whole result VALUE at cycle `i` depends on the argument observations at the cycles `≤ i` only. -/
theorem bundle_causal_R {ck : Contract} {c : Module} {dC : Design} {g : ck.table.Ty} (hU : U2HRStmtR ck c dC g)
    (A B : ArgSigs ck.table.ins) (i : Nat)
    (h : ∀ k ≤ i, obsArgs ck.table.ins A k = obsArgs ck.table.ins B k) :
    (applyArgs ck.table.ins g A).val i = (applyArgs ck.table.ins g B).val i := by
  have hc := call_causal_R hU A B i h
  obtain ⟨_, _, hlenO, hnd4, _⟩ := hU.1
  have hnd : ck.outNames.Nodup := (List.nodup_append.mp (List.nodup_append.mp hnd4).1).2.1
  have hl1 : (ck.table.out.obs ((applyArgs ck.table.ins g A).val i)).length = ck.outNames.length := by
    rw [Tools.VedU2Hier.OTy.obs_length, hlenO]
  have hl2 : (ck.table.out.obs ((applyArgs ck.table.ins g B).val i)).length = ck.outNames.length := by
    rw [Tools.VedU2Hier.OTy.obs_length, hlenO]
  refine Tools.VedU2Hier.OTy.obs_inj ck.table.out _ _ (lookup_zip_ext ck.outNames _ _ hnd hl1 hl2 ?_)
  intro n hn
  obtain ⟨pt, hpt⟩ := exists_zip_mem ck.outNames ck.table.out.flat n hlenO hn
  exact hc ⟨n, pt.hw⟩ (List.mem_map.mpr ⟨(n, pt), hpt, rfl⟩)

theorem bundle_causal_agree_R {ck : Contract} {c : Module} {dC : Design} {g : ck.table.Ty} (hU : U2HRStmtR ck c dC g)
    (A B : ArgSigs ck.table.ins) (i : Nat)
    (h : ∀ k ≤ i, ArgsAgree ck.table.ins A B k) :
    (applyArgs ck.table.ins g A).val i = (applyArgs ck.table.ins g B).val i :=
  bundle_causal_R hU A B i (fun k hk => obsArgs_of_agree _ A B k (h k hk))

end Tools.VedU2HierRec
