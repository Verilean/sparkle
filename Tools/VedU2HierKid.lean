import Tools.VedU2HierStmt

/-!
# H2 unit 3: an instance's output from the child's REAL theorem (`kid_inst`)

Design: docs/VED-HIER-H2-DESIGN.md §2.2 (child as oracle), §2.4, F2.

`kid_inst`: in a successful closed run, at every cycle `t < K`, the parent wire an instance's
output port is connected to carries the value the child's own U1 theorem (`OutputsStmt`) gives
for the child input stream `insCIn cs ins` (every child input port read from the parent INPUT its
connection names; total in `t`).

* the child's run in the hierarchy (`runHS_proj`) is the child's standalone `runModule` on the
  stream the connections produce (`insCOf`, finite);
* it agrees with the run on `insCIn cs ins` because the two seeds agree at every cycle `< K`
  (`runModule_congr_seed`; the parent writes no input: `runHS_inputs`), so the child's theorem,
  applied to the total stream `insCIn cs ins`, gives the outputs;
* `insCIn cs ins` is in range: a data port reads a parent DATA input (range from the parent's
  `InputsOk`), the child's reset port reads the parent's reset input, which the contract tie
  (`instPair_tie`, `cc.clkRst = designClkRst d m`) makes the contract's reset (0); the clock port
  reads the parent clock input with NO range assumption.
-/

namespace Tools.VedU2Hier

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier

/-- A run depends on the seed only at the cycles it executes. -/
theorem runModule_congr_seed (we : WEnv) (body : List Stmt)
    (seed1 seed2 : Nat → (String → Nat) → Env) (k : Nat)
    (h : ∀ j, j < k → seed1 j = seed2 j) (st : String → Nat) (mems : MEnv) :
    runModule we body seed1 k st mems = runModule we body seed2 k st mems := by
  rw [← runModuleTrace_fst, ← runModuleTrace_fst,
    runModuleTrace_congr_seed we body seed1 seed2 k h st mems]

/-- The child's input stream when every input port is connected to a `ref` of a parent input:
each port reads that parent input's stream value (total in `t`). -/
def insCIn (cs : List (String × Expr)) (ins : Nat → String → Nat) : Nat → String → Nat :=
  fun t n => match cs.lookup n with
    | some (.ref x) => ins t x
    | _ => 0

theorem kid_inst (d : Design) (arr : Module → List Stmt) (m : Module)
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
    (hconn : ∀ p ∈ c.inputs, ∃ x, cs.lookup p.name = some (Expr.ref x) ∧ x ∈ inNames m)
    (hdata : ∀ p ∈ ck.dataInputs, ∃ x, cs.lookup p.name = some (Expr.ref x) ∧
      (∃ q ∈ cc.dataInputs, q.name = x) ∧ declWidth m x = declWidth c p.name) :
    ∀ t, t < K → ∀ E, envs[t]? = some E → ∀ q ∈ c.outputs,
      ∃ x, cs.lookup q.name = some (Expr.ref x) ∧ E x = srcOf ck g (insCIn cs ins) q.name t := by
  obtain ⟨c', cenvs, cstates, hf', hrunM, hrunR, hcorr⟩ :=
    runHS_proj d arr m hS hA ins K envs sts hrun mn i cs hin
  have hcc : c = c' := by rw [hf] at hf'; exact Option.some.inj hf'
  subst hcc
  obtain ⟨_, ⟨hcore, _⟩, _, _, hout⟩ := hU
  have hperm := hA.2.2 c (findMod_mem hf)
  have hinits : (regsOf c.body).map (fun r => (r.1, r.2.2.2)) = ck.inits := hcore.2.2.2.2.2.2.2.1
  have hst0 : st0Of c = st0 ck c := st0Of_eq_st0 ck c hinits
  -- the child stream is in range
  have hok' : InputsOk ck c (insCIn cs ins) := by
    refine ⟨?_, ?_⟩
    · intro t p hp
      obtain ⟨x, hl, ⟨q, hq, hqn⟩, hw⟩ := hdata p hp
      have h1 : insCIn cs ins t p.name = ins t x := by simp [insCIn, hl]
      rw [h1, ← hw]
      have := hok.1 t q hq
      rw [hqn] at this
      exact this
    · intro t kr hkr
      rw [hclkc] at hkr
      have hreg : regsOf c.body ≠ [] := by
        intro h0; simp [regClkRst, h0] at hkr
      obtain ⟨x, y, kc, kr', hrc, h1, h2, hcl, hx, hy, hne, hkc, hkr2⟩ :=
        instPair_tie d m (hierS_clk hS) mn i cs c hin hf hreg cc htie
      have hkk : (kc, kr') = kr := Option.some.inj (hrc.symm.trans hkr)
      subst hkk
      have : insCIn cs ins t kr' = ins t y := by simp [insCIn, h2]
      show insCIn cs ins t kr' = 0
      rw [this]
      exact hok.2 t (x, y) hcl
  -- the seeds agree at every executed cycle
  have hpre : ∀ t, t < K → ∀ E, envs[t]? = some E → ∀ n ∈ inNames c,
      insCIn cs ins t n = insCOf (declWidth m) cs envs t n := by
    intro t ht E hE n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    obtain ⟨x, hl, hx⟩ := hconn p hp
    have hEx := runHS_inputs d arr m hA hwr ins K K (Nat.le_refl K) _ envs sts hrun t ht E hE x hx
    simp [insCIn, insCOf, hl, hE, evalExpr, hEx]
  have hseed : ∀ j, j < K → seedFwd c K (insCOf (declWidth m) cs envs) j =
      seedFwd c K (insCIn cs ins) j := by
    intro j hj
    funext st n
    simp only [seedFwd]
    by_cases hn : (c.inputs.map (·.name)).contains n = true
    · rw [if_pos hn, if_pos hn]
      obtain ⟨E, Ec, S, Sc, hE, _⟩ := hcorr (K - 1 - j) (by omega)
      exact (hpre _ (by omega) E hE n (List.contains_iff_mem.mp hn)).symm
    · rw [if_neg hn, if_neg hn]
  obtain ⟨envs', hrun', hall⟩ := hout (arr c) hperm.1 hperm.2 (insCIn cs ins) hok' K
  have hcongr := runModule_congr_seed (declWidth c) (arr c)
    (seedFwd c K (insCOf (declWidth m) cs envs)) (seedFwd c K (insCIn cs ins)) K hseed
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

end Tools.VedU2Hier
