import Tools.VedU2HierRecReg
import Tools.VedU2HierRecCausal

/-!
# A LEAF direct child of a nested parent (CANDIDATE; Tools/VedU2HierRec.lean)

The parent of the nested route (`U2HRStmtR`) has instances of NON-LEAF (middle) modules, whose own theorems are
`U2HRStmtR` on their sub-designs (`kid_seq_R`, `succF_of_theoremR`).  This file adds the same facts for a LEAF direct child
(assignments and registers only, e.g. the combinational `keccakRcHW` next to `wKeccakF`), whose own theorem is the
leaf statement `U1Stmt ck c g`.  Nothing is unfolded in the child; the existing statements are untouched.

* `runIn_leaf`: for a leaf arrangement the recursive cycle `stepIn` IS `stepModule` on the root slice (the registers
  restricted to the register outputs), so `runIn d arr c seed k st` is the leaf's own `runModule`;
* `WOH_of_WO_leaf`: for a leaf arrangement, `WO [] b` and the absence of a self-read (read off the leaf's `OrderHS d c`)
  give `WOH d b` (the order the recursive step needs);
* `kid_seq_RL`: `kid_seq_R` for a leaf child (hypothesis `U1Stmt ck c g` in place of `U2HRStmtR ck c dC g`; no
  sub-design); the state path `i :: p` of the parent is the child's own state at `p` (`st0Path_cons`, `runIn_proj`);
* `kid_inst_RL`: `kid_inst_R` for a leaf child (ports read the parent's inputs);
* `succF_of_leaf`: `SuccF` of a leaf child from its `ChildSucc`.
-/

namespace Tools.VedU2HierRec

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier

/-! ## The recursive cycle of a leaf is `stepModule` -/

theorem stepIn_leaf (d : Design) (arr : Module → List Stmt) (c : Module)
    (hl : leafBody (arr c) = true) (seed : Nat → (String → Nat) → Env) (st : HSt) (j : Nat) :
    stepIn d arr c seed st j =
      (stepModule (declWidth c) (arr c) (seed j (restrictTo (regOuts (arr c)) (st []))) (fun _ _ => 0)).map
        (fun r => (r.1, applyH st [([], r.2.1)])) := by
  unfold stepIn stepR
  rw [combR_leaf _ _ _ hl]
  unfold stepModule
  cases hE : evalAssigns (declWidth c) (fun _ _ => 0) (arr c) (seed j (restrictTo (regOuts (arr c)) (st []))) with
  | none => simp [hE]
  | some E =>
    have hu : ∀ envF, upsR d arr (d.modules.length + 1) c st envF =
        (regNexts (declWidth c) (fun _ _ => 0) (arr c) envF).map (fun nx => [([], nx)]) :=
      fun envF => upsR_leaf _ _ _ hl
    cases hN : regNexts (declWidth c) (fun _ _ => 0) (arr c) E with
    | none => simp [hE, hu, hN]
    | some nx => simp [hE, hu, hN, memNexts_leaf (declWidth c) (arr c) (fun _ _ => 0) E hl]

/-- A leaf's recursive run is its own `runModule` (state: the register outputs of the root slice). -/
theorem runIn_leaf (d : Design) (arr : Module → List Stmt) (c : Module)
    (hl : leafBody (arr c) = true) (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : HSt), runIn d arr c seed k st =
      runModule (declWidth c) (arr c) seed k (restrictTo (regOuts (arr c)) (st [])) (fun _ _ => 0) := by
  intro k
  induction k with
  | zero => intro st; rfl
  | succ k ih =>
    intro st
    simp only [runIn, stepIn_leaf d arr c hl, runModule]
    cases hs : stepModule (declWidth c) (arr c) (seed k (restrictTo (regOuts (arr c)) (st []))) (fun _ _ => 0) with
    | none => simp
    | some r =>
      obtain ⟨envF, nx, mems'⟩ := r
      have hmem : mems' = fun _ _ => 0 := by
        unfold stepModule at hs
        cases hE : evalAssigns (declWidth c) (fun _ _ => 0) (arr c)
            (seed k (restrictTo (regOuts (arr c)) (st []))) with
        | none => simp [hE] at hs
        | some E =>
          cases hN : regNexts (declWidth c) (fun _ _ => 0) (arr c) E with
          | none => simp [hE, hN] at hs
          | some nx' =>
            simp [hE, hN, memNexts_leaf _ _ _ _ hl] at hs
            exact hs.2.2.symm
      have hnames : ∀ p ∈ nx, p.1 ∈ regOuts (arr c) := by
        unfold stepModule at hs
        cases hE : evalAssigns (declWidth c) (fun _ _ => 0) (arr c)
            (seed k (restrictTo (regOuts (arr c)) (st []))) with
        | none => simp [hE] at hs
        | some E =>
          cases hN : regNexts (declWidth c) (fun _ _ => 0) (arr c) E with
          | none => simp [hE, hN] at hs
          | some nx' =>
            simp [hE, hN, memNexts_leaf _ _ _ _ hl] at hs
            obtain ⟨_, hnx, _⟩ := hs
            subst hnx
            exact regNexts_fst_mem _ _ _ _ _ hl hN
      have hst : restrictTo (regOuts (arr c)) (applyH st [([], nx)] []) =
          applyNexts (restrictTo (regOuts (arr c)) (st [])) nx := by
        have := applyH_root_cons st nx []
        rw [this]
        exact restrict_applyNexts _ _ _ hnames
      simp [ih, hst, hmem]

/-! ## Order: `WO [] b` and no self-read give `WOH d b` for a leaf arrangement -/

theorem wrsH_leaf (d : Design) : ∀ b : List Stmt, leafBody b = true → wrsH d b = writesOf b := by
  intro b
  induction b with
  | nil => intro _; rfl
  | cons s rest ih =>
    intro hl
    cases s with
    | assign l r =>
      simp only [leafBody] at hl
      simp only [wrsH, writesOf, List.flatMap_cons, wrH, stmtWrites] at ih ⊢
      rw [ih hl]
    | register o c r e i =>
      simp only [leafBody] at hl
      simp only [wrsH, writesOf, List.flatMap_cons, wrH, stmtWrites] at ih ⊢
      rw [ih hl]
    | memory _ _ _ _ _ _ _ _ _ _ _ _ => simp [leafBody] at hl
    | inst _ _ _ => simp [leafBody] at hl

theorem WOH_self (d : Design) : ∀ b : List Stmt, WOH d b → ∀ s ∈ b, ∀ n ∈ rdH d s, n ∉ wrH d s := by
  intro b
  induction b with
  | nil => intro _ s hs; cases hs
  | cons s0 rest ih =>
    intro hw s hs n hn
    obtain ⟨hrd, _, _, hrest⟩ := hw
    rcases List.mem_cons.mp hs with rfl | hm
    · exact (hrd n hn).2
    · exact ih hrest s hm n hn

theorem WOH_of_WO_leaf (d : Design) : ∀ b : List Stmt, leafBody b = true →
    (∀ s ∈ b, ∀ n ∈ rdH d s, n ∉ wrH d s) → ∀ done, WO done b → WOH d b := by
  intro b
  induction b with
  | nil => intro _ _ _ _; trivial
  | cons s rest ih =>
    intro hl hself done hwo
    have hlr : leafBody rest = true := by
      rw [leafBody_iff]
      exact fun x hx => (leafBody_iff _).mp hl x (List.mem_cons_of_mem _ hx)
    rcases (leafBody_iff _).mp hl s (List.mem_cons_self ..) with ⟨l, r, rfl⟩ | ⟨o, c, r, e, i, rfl⟩
    · cases hwo with
      | cons hok hreads hw hrest =>
        refine ⟨?_, ?_, ?_, ih hlr (fun x hx => hself x (List.mem_cons_of_mem _ hx)) _ hrest⟩
        · intro n hn
          refine ⟨?_, hself _ (List.mem_cons_self ..) n hn⟩
          rw [wrsH_leaf d rest hlr]
          exact hreads n (by simpa [rdH, stmtReads] using hn)
        · intro n hn
          rw [wrsH_leaf d rest hlr]
          exact (hw n (by simpa [wrH, stmtWrites] using hn)).2
        · simp [wrH]
    · cases hwo with
      | cons hok hreads hw hrest =>
        refine ⟨?_, ?_, ?_, ih hlr (fun x hx => hself x (List.mem_cons_of_mem _ hx)) _ hrest⟩
        · intro n hn; simp [rdH] at hn
        · intro n hn; simp [wrH] at hn
        · simp [wrH]

/-! ## Success of a leaf child -/

theorem succF_of_leaf (d : Design) (arr : Module → List Stmt) (c : Module)
    (hl : leafBody (arr c) = true) (hs : ChildSucc c (arr c)) (k : Nat) : SuccF d arr (k + 1) c := by
  obtain ⟨seed, E, nx, hE, hN⟩ := hs
  exact succF_of_step d arr (k + 1) c (fun _ _ => 0) seed E [([], nx)]
    (by rw [combR_leaf _ _ _ hl]; exact hE) (by rw [upsR_leaf _ _ _ hl, hN] <;> rfl)

/-! ## The instance step of a LEAF child, from the leaf's own theorem -/

/-- `kid_seq_R` for a LEAF child `c` (resolved in the parent's real design `d`): the child's own theorem is the leaf
statement `hU : U1Stmt ck c g`, its order is `OrderHS d c` (kernel `decide` on the real design), and its state path in
the parent (`i :: p`) is the child's own state at `p`. -/
theorem kid_seq_RL (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeR d m = true) (hA : AdmArrR d m arr)
    (hwr : ∀ n ∈ wrsH d (arr m), n ∉ inNames m)
    (cc : Contract) (htie : cc.clkRst = designClkRst d m)
    (ins : Nat → String → Nat) (hok : InputsOk cc m ins) (K : Nat) (envs : List Env)
    (sts : List HSt)
    (hrun : runHSRTrace d arr m (seedFwd m K ins) K (st0HR d m) = some (envs, sts))
    (mn i : String) (cs : List (String × Expr)) (hin : Stmt.inst mn i cs ∈ m.body)
    (c : Module) (hf : findMod d mn = some c)
    (hleaf : leafBody c.body = true) (hordc : OrderHS d c)
    (ck : Contract) (g : ck.table.Ty) (hU : U1Stmt ck c g)
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
  obtain ⟨_, ⟨hcore, _⟩, _, _, hout⟩ := hU
  have hcmem : c ∈ d.modules := findMod_mem hf
  have hperm := (hA.2.2 c hcmem).1
  have hwo : WO [] (arr c) := (hA.2.2 c hcmem).2.1 hleaf
  have hleafA : leafBody (arr c) = true := leafBody_perm hperm.symm hleaf
  have hwrc : ∀ n ∈ wrsH d (arr c), n ∉ inNames c := by
    obtain ⟨b0, hb0⟩ := hordc
    exact orderOkHS_hwr hb0 hperm
  have hwoc : WOH d (arr c) := by
    obtain ⟨b0, hb0⟩ := hordc
    obtain ⟨hp0, hw0, _⟩ := orderOkHS_sound hb0
    have hself := WOH_self d b0 hw0
    exact WOH_of_WO_leaf d (arr c) hleafA
      (fun s hs n hn => hself s ((hp0.trans hperm.symm).mem_iff.mpr hs) n hn) [] hwo
  -- the child's initial state: the slice at the instance is the child's own initial state
  have hinits : (regsOf c.body).map (fun r => (r.1, r.2.2.2)) = ck.inits := hcore.2.2.2.2.2.2.2.1
  have hst0 : st0Of c = st0 ck c := st0Of_eq_st0 ck c hinits
  have hres : restrictTo (regOuts (arr c)) (st0HR d m [i]) = st0 ck c := by
    have h1 : st0HR d m [i] = st0Of c := by
      show st0Path d m (i :: []) = st0Of c
      rw [st0Path_cons (hierR_inst_unique hS) hin hf []] <;> rfl
    rw [h1, ← hst0]
    funext n
    by_cases hn : n ∈ regOuts (arr c)
    · simp [restrictTo, hn]
    · have : n ∉ regOuts c.body := fun h => hn ((regOuts_perm_mem hperm n).mpr h)
      simp [restrictTo, hn, st0Of_off c n this]
  obtain ⟨cenvs, hrunC, hcorr⟩ := runIn_proj d arr m hS hA mn i cs hin c hf hwoc hwrc K _ _ envs sts hrun
  rw [runIn_leaf d arr c hleafA] at hrunC
  have hrunM : runModule (declWidth c) (arr c) (seedFwd c K (insCOf (declWidth m) cs envs)) K (st0 ck c)
      (fun _ _ => 0) = some cenvs := by
    rw [← hres]; exact hrunC
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
  obtain ⟨L', hL', hLe⟩ := runModule_prefix (declWidth c) (arr c)
    (seedFwd c K (insCOf (declWidth m) cs envs)) (t0 + 1) (K - (t0 + 1)) (st0 ck c) (fun _ _ => 0) cenvs
    (by rw [show t0 + 1 + (K - (t0 + 1)) = K by omega]; exact hrunM)
  have hshift : ∀ j, j < t0 + 1 →
      (fun j => seedFwd c K (insCOf (declWidth m) cs envs) (j + (K - (t0 + 1)))) j =
        seedFwd c (t0 + 1) (insCOf (declWidth m) cs envs) j := by
    intro j hj
    funext st n
    simp only [seedFwd]
    have : K - 1 - (j + (K - (t0 + 1))) = t0 + 1 - 1 - j := by omega
    rw [this]
  rw [runModule_congr_seed _ _ _ _ (t0 + 1) hshift, runModule_congr_seed _ _ _ _ (t0 + 1) hseed] at hL'
  obtain ⟨envs', hrun', hall⟩ := hout (arr c) hperm hwo (netIn ck cs ins F) hok' (t0 + 1)
  have hce : envs' = L' := Option.some.inj (hrun'.symm.trans hL')
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

/-- `kid_inst_R` for a LEAF child whose ports read parent inputs (whole run). -/
theorem kid_inst_RL (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeR d m = true) (hA : AdmArrR d m arr)
    (hwr : ∀ n ∈ wrsH d (arr m), n ∉ inNames m)
    (cc : Contract) (htie : cc.clkRst = designClkRst d m)
    (ins : Nat → String → Nat) (hok : InputsOk cc m ins) (K : Nat) (envs : List Env)
    (sts : List HSt)
    (hrun : runHSRTrace d arr m (seedFwd m K ins) K (st0HR d m) = some (envs, sts))
    (mn i : String) (cs : List (String × Expr)) (hin : Stmt.inst mn i cs ∈ m.body)
    (c : Module) (hf : findMod d mn = some c)
    (hleaf : leafBody c.body = true) (hordc : OrderHS d c)
    (ck : Contract) (g : ck.table.Ty) (hU : U1Stmt ck c g)
    (hclkc : ck.clkRst = regClkRst c.body)
    (hconn : ∀ p ∈ c.inputs, ∃ x, cs.lookup p.name = some (Expr.ref x) ∧ x ∈ inNames m)
    (hdata : ∀ p ∈ ck.dataInputs, ∃ x, cs.lookup p.name = some (Expr.ref x) ∧
      (∃ q ∈ cc.dataInputs, q.name = x) ∧ declWidth m x = declWidth c p.name)
    (hrstnd : ∀ kr, ck.clkRst = some kr → ck.dataInputs.any (·.name == kr.2) = false) :
    ∀ t, t < K → ∀ E, envs[t]? = some E → ∀ q ∈ c.outputs,
      ∃ x, cs.lookup q.name = some (Expr.ref x) ∧ E x = srcOf ck g (insCIn cs ins) q.name t := by
  have hcore := hU.2.1.1
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
  have key := kid_seq_RL d arr m hS hA hwr cc htie ins hok K envs sts hrun mn i cs hin c hf hleaf hordc
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

end Tools.VedU2HierRec
