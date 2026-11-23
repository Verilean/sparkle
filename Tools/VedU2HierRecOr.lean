import Tools.VedU2HierRecPar

/-!
# Pieces of the nested entry (CANDIDATE; Tools/VedU2HierRec.lean)

The register-free parent over a NON-LEAF child, whole-run instance fact:

* `exists_arrHR`: an admissible arrangement exists (the statement is not vacuous);
* `outputsOnHSR_of_oracle`: the analogue of `outputsOnHS_of_oracle` (parent without registers);
* `admArrR_child` / `succF_of_theoremR`: the child's OWN theorem on a sub-design supplies `SuccF`
  (a successful cycle of the child at the parent's fuel) in the parent's REAL design;
* `kid_inst_R`: the instance fact of a non-leaf child whose ports read the parent's inputs, from the
  child's own theorem (`kid_seq_R` with the stream of the connections);
* `U2HRStmtR_of_S`: a depth-1 stored theorem (`U2HRStmt`) on an all-leaf design is a `U2HRStmtR`.
-/

namespace Tools.VedU2HierRec

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier

/-! ## Existence of the arrangement -/

theorem exists_arrHR (d : Design) (m : Module) (hord : OrderHS d m) (hch : OrderModsR d)
    (hne : ∀ x ∈ d.modules, x ≠ m) : ∃ arr, AdmArrR d m arr := by
  classical
  obtain ⟨b0, hb0⟩ := hord
  obtain ⟨hp0, hw0, _⟩ := orderOkHS_sound hb0
  obtain ⟨bc, hbc⟩ : ∃ bc : Module → List Stmt, ∀ x ∈ d.modules,
      (leafBody x.body = true → OrderOk x (bc x) = true) ∧
      (leafBody x.body = false → OrderOkHS d x (bc x) = true) := by
    refine ⟨fun x => if h : x ∈ d.modules then
        (if hl : leafBody x.body = true then Classical.choose ((hch x h).1 hl)
         else Classical.choose ((hch x h).2 (by simpa using hl))) else [], ?_⟩
    intro x hx
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · simp only [hx, dite_true, hl]
      exact Classical.choose_spec ((hch x hx).1 hl)
    · have hl' : ¬ leafBody x.body = true := by simp [hl]
      simp only [hx, dite_true, hl']
      exact Classical.choose_spec ((hch x hx).2 hl)
  refine ⟨fun c => if c = m then b0 else bc c, ?_, ?_, ?_⟩
  · simpa using hp0
  · simpa using hw0
  · intro c hc
    have hcm : c ≠ m := hne c hc
    simp only [hcm, if_false]
    refine ⟨?_, fun hl => ?_, fun hl => ?_⟩
    · cases hl : leafBody c.body with
      | true =>
        have h := (hbc c hc).1 hl
        simp only [OrderOk, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨hp, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
        exact isPermOf_sound hp
      | false =>
        exact (orderOkHS_sound ((hbc c hc).2 hl)).1
    · have h := (hbc c hc).1 hl
      simp only [OrderOk, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨hp, hwo⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
      exact woCheck_sound _ _ hwo
    · exact (orderOkHS_sound ((hbc c hc).2 hl)).2.1

/-! ## The register-free parent: outputs from the open fold and the instance facts -/

theorem outputsOnHSR_of_oracle (c : Contract) (m : Module) (d : Design)
    (arr : Module → List Stmt) (f : c.table.Ty)
    (hS : HierShapeR d m = true) (hA : AdmArrR d m arr) (hnoreg : regsOf m.body = [])
    (hsucc : SuccF d arr (fuelR d) m)
    (b0 : List Stmt) (hp : (arr m).Perm b0) (hw0 : WOH d b0)
    (Ow : (Nat → String → Nat) → String → Nat → Nat)
    (hkid : ∀ ins, InputsOk c m ins → ∀ K envs sts,
      runHSRTrace d arr m (seedFwd m K ins) K (st0HR d m) = some (envs, sts) →
      ∀ mn i cs, Stmt.inst mn i cs ∈ m.body → ∀ t, t < K → ∀ E, envs[t]? = some E →
        ∀ y ∈ instOuts d mn cs, E y = Ow ins y t)
    (hopen : ∀ ins, InputsOk c m ins → ∀ t, ∃ E,
      evalAssignsI (declWidth m) (oracleIE d (fun y => Ow ins y t)) b0
        (seedIn m ins t (fun _ => 0)) = some E ∧
      ∀ o ∈ c.outputs, E o.name = srcOf c f ins o.name t) :
    OutputsOnHSR c m d arr f := by
  intro ins hok K
  obtain ⟨envs, sts, hrun⟩ := runHSR_exists d arr m hS hA hsucc (seedFwd m K ins) K (st0HR d m)
  refine ⟨envs, ?_, ?_⟩
  · have := runHSRTrace_fst d arr m (seedFwd m K ins) K (st0HR d m)
    rw [hrun] at this
    simp at this
    exact this.symm
  · intro t ht o ho
    obtain ⟨E, S, hE, _, hfold⟩ := runHSRTrace_cycle d arr m (seedFwd m K ins) K (st0HR d m) envs sts
      hrun t ht
    refine ⟨E, hE, ?_⟩
    have hreg : regOuts (arr m) = [] := by
      have h0 : regOuts m.body = [] := by simp [regOuts, hnoreg]
      exact regOuts_nil_of_perm hA.1 h0
    have hseed : seedFwd m K ins (K - 1 - t) (restrictTo (regOuts (arr m)) (S [])) =
        seedIn m ins t (fun _ => 0) := by
      rw [hreg, restrictTo_nil]
      exact seedFwd_time m K ins ht _
    rw [hseed] at hfold
    have hfold0 := evalAssignsI_perm d _ _ (instEvalF_laws d arr _ S (declWidth m)) hp hA.2.1 hw0 hfold
    have hmem : ∀ s, s ∈ b0 → s ∈ m.body := fun s hs => hA.1.mem_iff.mp (hp.mem_iff.mpr hs)
    have hor := fold_oracle d _ _ (instEvalF_laws d arr _ S (declWidth m)) (fun y => Ow ins y t) b0 _ E
      hw0 hfold0 (fun mn i cs hin y hy => hkid ins hok K envs sts hrun mn i cs (hmem _ hin) t ht E hE y hy)
    obtain ⟨E', hE', hout⟩ := hopen ins hok t
    rw [hE'] at hor
    cases hor
    exact hout o ho

/-! ## The child's own theorem on a sub-design, in the parent's real design -/

/-- The parent's arrangement, restricted to the child's sub-design, is admissible there. -/
theorem admArrR_child {d dC : Design} (arr : Module → List Stmt) (hSub : SubDesign dC d)
    (hsub : ∀ x ∈ dC.modules, x ∈ d.modules)
    (hmods : ∀ x ∈ d.modules, (arr x).Perm x.body ∧ (leafBody x.body = true → WO [] (arr x)) ∧
      (leafBody x.body = false → WOH d (arr x)))
    {c : Module} (hperm : (arr c).Perm c.body) (hwoc : WOH d (arr c))
    (hShC : HierShapeR dC c = true) : AdmArrR dC c arr := by
  obtain ⟨hresTop, hresMods⟩ := HierShapeR_resolved hShC
  refine ⟨hperm, ?_, ?_⟩
  · refine WOH_agree _ ?_ hwoc
    intro mn' i' cs' hmem
    have hb : Stmt.inst mn' i' cs' ∈ c.body := hperm.mem_iff.mp hmem
    obtain ⟨c', hf'⟩ := hresTop mn' i' cs' hb
    rw [hf', hSub _ _ hf']
  · intro x hx
    obtain ⟨hp, hwo, hwoh⟩ := hmods x (hsub x hx)
    refine ⟨hp, hwo, fun hl => ?_⟩
    refine WOH_agree _ ?_ (hwoh hl)
    intro mn' i' cs' hmem
    have hb : Stmt.inst mn' i' cs' ∈ x.body := hp.mem_iff.mp hmem
    obtain ⟨c', hf'⟩ := hresMods x hx mn' i' cs' hb
    rw [hf', hSub _ _ hf']

theorem stepR_some_inv {d : Design} {arr : Module → List Stmt} {k : Nat} {m : Module} {st : HSt}
    {env0 e : Env} {u : Ups} (h : stepR d arr k m st env0 = some (e, u)) :
    combR d arr k m st env0 = some e ∧ upsR d arr k m st e = some u := by
  unfold stepR at h
  cases hc : combR d arr k m st env0 with
  | none => simp [hc] at h
  | some e' =>
    cases hu : upsR d arr k m st e' with
    | none => simp [hc, hu] at h
    | some u' =>
      simp only [hc, hu, Option.bind_eq_bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hu⟩

/-- THE CHILD'S REAL THEOREM SUPPLIES `SuccF`: a successful cycle of the child (its `U2HRStmtR` on the
sub-design `dC`, `K = 1`, the all-0 input stream), transferred to the parent's real design. -/
theorem succF_of_theoremR (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeR d m = true) (hA : AdmArrR d m arr)
    (c : Module) (hcmem : c ∈ d.modules) (hnl : leafBody c.body = false)
    (dC : Design) (hsub : ∀ x ∈ dC.modules, x ∈ d.modules)
    (ck : Contract) (g : ck.table.Ty) (hU : U2HRStmtR ck c dC g) :
    SuccF d arr (d.modules.length + 1) c := by
  obtain ⟨_, hcore, _, hShC, _, _, _, _, hout⟩ := hU
  have hndD := (hierR_names hS).1
  have hSub : SubDesign dC d := subDesign_of_subset hndD hsub
  obtain ⟨hndC, hneC⟩ := hierR_names hShC
  have hfuel : fuelR dC ≤ d.modules.length + 1 :=
    fuel_le_of_sub hndC hsub hcmem (fun h => hneC c h rfl)
  have hperm := (hA.2.2 c hcmem).1
  have hwoc : WOH d (arr c) := (hA.2.2 c hcmem).2.2 hnl
  have hAdmC : AdmArrR dC c arr := admArrR_child arr hSub hsub hA.2.2 hperm hwoc hShC
  have hok : InputsOk ck c (fun _ _ => 0) :=
    ⟨fun t p _ => Nat.two_pow_pos _, fun t kr _ => rfl⟩
  obtain ⟨envs, hrun, _⟩ := hout arr hAdmC _ hok 1
  simp only [runHSR] at hrun
  cases hst : stepHSR dC arr c (st0HR dC c)
      (seedFwd c 1 (fun _ _ => 0) 0 (restrictTo (regOuts (arr c)) (st0HR dC c []))) with
  | none => simp [hst] at hrun
  | some r =>
    obtain ⟨envF, ups⟩ := r
    unfold stepHSR at hst
    by_cases hc : clkRstOk dC c = true
    · simp only [hc, if_true] at hst
      have h2 := stepR_sub_fuel hSub arr hfuel c _ _ _ hst
      obtain ⟨hE, hu⟩ := stepR_some_inv h2
      exact succF_of_step d arr _ c _ _ _ _ hE hu
    · simp [hc] at hst

/-- `kid_inst` for a NON-LEAF child whose ports read parent inputs (whole run), from the child's own
theorem on a sub-design. -/
theorem kid_inst_R (d : Design) (arr : Module → List Stmt) (m : Module)
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
    (hconn : ∀ p ∈ c.inputs, ∃ x, cs.lookup p.name = some (Expr.ref x) ∧ x ∈ inNames m)
    (hdata : ∀ p ∈ ck.dataInputs, ∃ x, cs.lookup p.name = some (Expr.ref x) ∧
      (∃ q ∈ cc.dataInputs, q.name = x) ∧ declWidth m x = declWidth c p.name)
    (hrstnd : ∀ kr, ck.clkRst = some kr → ck.dataInputs.any (·.name == kr.2) = false) :
    ∀ t, t < K → ∀ E, envs[t]? = some E → ∀ q ∈ c.outputs,
      ∃ x, cs.lookup q.name = some (Expr.ref x) ∧ E x = srcOf ck g (insCIn cs ins) q.name t := by
  have hcore := hU.2.1
  have hnetIn : netIn ck cs ins (insCIn cs ins) = insCIn cs ins := by
    funext t n
    simp only [netIn]
    split <;> rfl
  have hrange : ∀ t, ∀ p ∈ ck.dataInputs, insCIn cs ins t p.name < 2 ^ declWidth c p.name := by
    intro t p hp
    obtain ⟨x, hl, ⟨q, hq, hqn⟩, hw⟩ := hdata p hp
    have h1 : insCIn cs ins t p.name = ins t x := by simp [insCIn, hl]
    rw [h1, ← hw]
    have := hok.1 t q hq
    rw [hqn] at this
    exact this
  intro t ht E hE q hq
  have key := kid_seq_R d arr m hS hA hwr cc htie ins hok K envs sts hrun mn i cs hin c hf hnl hordc dC hsub
    ck g hU hclkc (fun p hp => by
      obtain ⟨x, hl, hx⟩ := hconn p hp
      exact ⟨x, hl, Or.inr hx⟩) hrstnd (insCIn cs ins) hrange t ht (by
      intro s hs E' hE' p hp
      obtain ⟨x, hl, _, _⟩ := hdata p hp
      have hpc : p ∈ c.inputs := by
        have := hcore.2.2.2.2.1
        rw [this]; exact List.mem_append_left _ hp
      obtain ⟨x', hl', hx'⟩ := hconn p hpc
      have hxx : x' = x := by
        rw [hl] at hl'; exact (Expr.ref.inj (Option.some.inj hl')).symm
      subst hxx
      refine ⟨x', hl', ?_⟩
      have hEx := runHSR_inputs d arr m hA.2.1 hwr ins K K (Nat.le_refl K) _ envs sts hrun s (by omega)
        E' hE' x' hx'
      simp [insCIn, hl, hEx])
  obtain ⟨x, hl, hv⟩ := key E hE q hq
  exact ⟨x, hl, by rw [hv, hnetIn]⟩

/-! ## A depth-1 theorem on an all-leaf design is a `U2HRStmtR` -/

theorem U2HRStmtR_of_S (c : Contract) (m : Module) (d : Design) (f : c.table.Ty)
    (hl : allLeafB d = true) (h : U2HRStmt c m d f) : U2HRStmtR c m d f :=
  (U2HRStmtR_iff_K c m d f hl).mpr (U2HRStmtK_of_U2HRStmt c m d f h)

/-- Decidable form of `hrstnd` (the child's reset port is not one of its data ports). -/
theorem rstnd_sound {ck : Contract}
    (h : (match ck.clkRst with | some kr => ck.dataInputs.any (·.name == kr.2) | none => false) = false) :
    ∀ kr, ck.clkRst = some kr → ck.dataInputs.any (·.name == kr.2) = false := by
  intro kr hkr
  rw [hkr] at h
  exact h

/-- Membership by value, from the decidable existential form (a module list has no lawful `BEq`). -/
theorem mem_of_ex {α : Type} {l1 l2 : List α} (h : ∀ x ∈ l1, ∃ y ∈ l2, y = x) : ∀ x ∈ l1, x ∈ l2 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := h x hx
  exact hy

theorem mem_of_ex1 {α : Type} {l : List α} {x : α} (h : ∃ y ∈ l, y = x) : x ∈ l := by
  obtain ⟨y, hy, rfl⟩ := h
  exact hy

end Tools.VedU2HierRec
