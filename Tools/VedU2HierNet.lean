import Tools.VedU2HierKid
import Tools.VedU2HierStmt

/-!
# H2c: an instance whose DATA inputs are read from a parent NET (a wire), not a parent input

Design: docs/VED-HIER-H2-DESIGN.md §2.1 (F2: the child stream the closed run produces must be tied
to the stream the declaration's call expects, by the PARENT side), docs/VED-HIER-H2C.md.

`kid_inst` (H2a/H2b) applies the child's own theorem (`OutputsStmt`) to the stream `insCIn cs ins`,
every child input port read from a parent INPUT.  `kid_inst_net` applies it to the stream
`netIn ck cs ins F`: a child DATA port reads `F t port` (a total stream, in range) and every other
port (clock, reset) reads the parent input its connection names, as before.  The tie to the run is
a HYPOTHESIS of the theorem that the entry's generated proof supplies from the closed run
(`closed_run_asg`: every assignment of the checked arrangement holds in the cycle's environment, so
a net's value in the run is computed from the inputs; `hrunF`): for every cycle `t < K` of the run
the parent wire a data port is connected to holds `F t port`.  No new binder reaches the statement.
-/

namespace Tools.VedU2Hier

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier

/-- Every assignment of the checked arrangement holds in the environment of every cycle of a
successful closed run: the evaluated right-hand side is the value the left-hand side carries. -/
theorem closed_run_asg (d : Design) (arr : Module → List Stmt) (m : Module) (hA : AdmArr d m arr)
    (b0 : List Stmt) (hp : (arr m).Perm b0) (hw0 : WOH d b0)
    (seed : Nat → (String → Nat) → Env) (K : Nat) (st : HSt) (envs : List Env) (sts : List HSt)
    (hrun : runHSTrace d arr m seed K st = some (envs, sts)) (t : Nat) (ht : t < K)
    (E : Env) (hE : envs[t]? = some E) :
    ∀ l r, Stmt.assign l r ∈ b0 → evalExpr (declWidth m) E r = some (E l) := by
  intro l r hl
  obtain ⟨E', S, hE', _, hfold⟩ := runHSTrace_cycle d arr m seed K st envs sts hrun t ht
  rw [hE] at hE'
  cases hE'
  have hfold0 := evalAssignsI_perm d _ _ (instEvalS_laws d arr S (declWidth m)) hp hA.2.1 hw0 hfold
  have hG := good_of_fold d _ _ (instEvalS_laws d arr S (declWidth m)) b0 _ E hw0 hfold0
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

/-- The child's input stream when its DATA ports read the total stream `F` and every other port
reads the parent input its connection names. -/
def netIn (ck : Contract) (cs : List (String × Expr)) (ins : Nat → String → Nat)
    (F : Nat → String → Nat) : Nat → String → Nat :=
  fun t n => if ck.dataInputs.any (·.name == n) then F t n else insCIn cs ins t n

/-- Decidable form of the connection conditions of `kid_inst_net`: every input port of the child is
connected to a `ref`; a port that is not a data port of the child's contract reads a parent input
(clock, reset); the child's reset port is not a data port. -/
def connsNet (m : Module) (c : Module) (ck : Contract) (cs : List (String × Expr)) : Bool :=
  c.inputs.all (fun p => match cs.lookup p.name with
    | some (.ref x) => ck.dataInputs.any (·.name == p.name) || (inNames m).contains x
    | _ => false) &&
  (match ck.clkRst with
    | some kr => !(ck.dataInputs.any (·.name == kr.2))
    | none => true)

theorem connsNet_sound {m c : Module} {ck : Contract} {cs : List (String × Expr)}
    (h : connsNet m c ck cs = true) :
    (∀ p ∈ c.inputs, ∃ x, cs.lookup p.name = some (Expr.ref x) ∧
      (ck.dataInputs.any (·.name == p.name) = true ∨ x ∈ inNames m)) ∧
    (∀ kr, ck.clkRst = some kr → ck.dataInputs.any (·.name == kr.2) = false) := by
  simp only [connsNet, Bool.and_eq_true] at h
  refine ⟨?_, ?_⟩
  · intro p hp
    have := List.all_eq_true.mp h.1 p hp
    cases hl : cs.lookup p.name with
    | none => simp [hl] at this
    | some e =>
      cases e with
      | ref x =>
        simp only [hl, Bool.or_eq_true] at this
        refine ⟨x, rfl, ?_⟩
        rcases this with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (List.contains_iff_mem.mp h1)
      | _ => simp [hl] at this
  · intro kr hkr
    have := h.2
    rw [hkr] at this
    simpa using this

theorem kid_inst_net (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeS d m = true) (hA : AdmArr d m arr)
    (hwr : ∀ n ∈ wrsH d (arr m), n ∉ inNames m)
    (cc : Contract) (htie : cc.clkRst = designClkRst d m)
    (ins : Nat → String → Nat) (hok : InputsOk cc m ins) (K : Nat) (envs : List Env)
    (sts : List HSt)
    (hrun : runHSTrace d arr m (seedFwd m K ins) K (st0H d m) = some (envs, sts))
    (mn i : String) (cs : List (String × Expr)) (hin : Stmt.inst mn i cs ∈ m.body)
    (c : Module) (hf : findMod d mn = some c)
    (ck : Contract) (g : ck.table.Ty) (hU : U1Stmt ck c g)
    (hclkc : ck.clkRst = regClkRst c.body)
    (hconn : ∀ p ∈ c.inputs, ∃ x, cs.lookup p.name = some (Expr.ref x) ∧
      (ck.dataInputs.any (·.name == p.name) = true ∨ x ∈ inNames m))
    (hrstnd : ∀ kr, ck.clkRst = some kr → ck.dataInputs.any (·.name == kr.2) = false)
    (F : Nat → String → Nat)
    (hrange : ∀ t, ∀ p ∈ ck.dataInputs, F t p.name < 2 ^ declWidth c p.name)
    (hrunF : ∀ t, t < K → ∀ E, envs[t]? = some E → ∀ p ∈ ck.dataInputs,
      ∃ x, cs.lookup p.name = some (Expr.ref x) ∧ E x = F t p.name) :
    ∀ t, t < K → ∀ E, envs[t]? = some E → ∀ q ∈ c.outputs,
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
  -- the seeds agree at every executed cycle
  have hpre : ∀ t, t < K → ∀ E, envs[t]? = some E → ∀ n ∈ inNames c,
      netIn ck cs ins F t n = insCOf (declWidth m) cs envs t n := by
    intro t ht E hE n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    obtain ⟨x, hl, hx⟩ := hconn p hp
    by_cases hd : ck.dataInputs.any (·.name == p.name) = true
    · obtain ⟨p', hp', hpn⟩ := List.any_eq_true.mp hd
      have hpn' : p'.name = p.name := by simpa using hpn
      obtain ⟨x', hl', hEx'⟩ := hrunF t ht E hE p' hp'
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
  have hseed : ∀ j, j < K → seedFwd c K (insCOf (declWidth m) cs envs) j =
      seedFwd c K (netIn ck cs ins F) j := by
    intro j hj
    funext st n
    simp only [seedFwd]
    by_cases hn : (c.inputs.map (·.name)).contains n = true
    · rw [if_pos hn, if_pos hn]
      obtain ⟨E, Ec, S, Sc, hE, _⟩ := hcorr (K - 1 - j) (by omega)
      exact (hpre _ (by omega) E hE n (List.contains_iff_mem.mp hn)).symm
    · rw [if_neg hn, if_neg hn]
  obtain ⟨envs', hrun', hall⟩ := hout (arr c) hperm.1 hperm.2 (netIn ck cs ins F) hok' K
  have hcongr := runModule_congr_seed (declWidth c) (arr c)
    (seedFwd c K (insCOf (declWidth m) cs envs)) (seedFwd c K (netIn ck cs ins F)) K hseed
    (st0Of c) (fun _ _ => 0)
  rw [hcongr, hst0, hrun'] at hrunR
  have hce : envs' = cenvs := Option.some.inj hrunR
  intro t ht E hE q hq
  obtain ⟨E0, Ec, S, Sc, hE0, hEc, _, _, hproj⟩ := hcorr t ht
  have hEE : E = E0 := Option.some.inj (hE.symm.trans hE0)
  subst hEE
  obtain ⟨x, hl, hxv⟩ := hproj.2.1 q hq
  refine ⟨x, hl, ?_⟩
  have hqk : q ∈ ck.outputs := by rw [← hcore.2.2.2.2.2.1]; exact hq
  obtain ⟨env, he, hv⟩ := hall t ht q hqk
  rw [hce, hEc] at he
  have hee : env = Ec := (Option.some.inj he).symm
  subst hee
  rw [hxv]; exact hv

/-- Reading a bit-vector signal's observation back as a signal gives the signal. -/
theorem sig_obs_bv (w : Nat) (S : Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain (BitVec w)) :
    (PTy.bv w).sig (fun t _ => (S.val t).toNat) "" = S := by
  cases S with
  | mk f =>
    simp only [PTy.sig, BitVec.ofNat_toNat]
    congr 1
    funext t
    simp

theorem sig_obs_bit (S : Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain Bool) :
    PTy.bit.sig (fun t _ => Bool.toNat (S.val t)) "" = S := by
  cases S with
  | mk f =>
    simp only [PTy.sig]
    congr 1
    funext t
    cases h : f t <;> simp [Bool.toNat]

end Tools.VedU2Hier
