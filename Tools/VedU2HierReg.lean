import Tools.VedU2HierStmt

/-!
# H2b: the statement `U2HRStmt` and the composition theorem for a parent WITH REGISTERS

Design: docs/VED-HIER-H2-DESIGN.md §1.2, §11, §12.  `Tools/VedU2HierStmt.lean` (`U2HStmt`,
`outputsOnHS_of_oracle`) and everything H2a proved are unchanged; this is a separate definition and a
separate theorem.

`U2HRStmt c m d f` is `U2HStmt` WITHOUT the clause `regsOf m.body = []`: the parent may carry
registers.  Its parent-register values live in the root slice `st [] : String → Nat` of the
hierarchical state; `runHS` already updates it simultaneously with every child's (every next value
is computed from the PRE-update state, `stepHS`).  The statement is about the SAME closed run
`runHS` from `st0H d m` (the parent's own register inits and every child's), the same `(m, d)`.

THE COMPOSITION THEOREM (`outputsOnHS_of_stepR`) replaces H2a's per-cycle `hopen` by a state
invariant `R ins t p` on the PARENT's register slice `p`, supplied (not assumed) by the entry from
the facts `#verify_elab_deep` generates for the open parent:

* `h0`: `R ins 0 (st0Of m)` — the parent's own initial registers;
* `hstep`: from any `p` with `R ins t p`, the OPEN evaluation of the checked arrangement `b0` (every
  instance output a free oracle value `Ow ins y t`, `oracleIE`) succeeds, the parent registers'
  next values are computed from it, the outputs are the declaration's, and `R` holds of the
  simultaneously updated slice (`applyNexts p nx`).

The children read only parent INPUTS, so the oracle (`hkid`, from `kid_inst`) does not depend on the
parent registers; the closed run is the open run (`fold_oracle`, as in H2a).
-/

namespace Tools.VedU2Hier

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Hier

/-- The statement the stateful hierarchical entry registers for a parent WITH registers (H2b):
`U2HStmt` minus the register-free clause; every other clause is the same. -/
def U2HRStmt (c : Contract) (m : Module) (d : Design) (f : c.table.Ty) : Prop :=
  CorrStmt c ∧ ShapeCore c m ∧ c.clkRst = designClkRst d m ∧ HierShapeS d m = true ∧
  WidthStmt c m ∧ OrderHS d m ∧ (∀ x ∈ d.modules, OrderStmt x) ∧
  (∃ arr, AdmArr d m arr) ∧ OutputsStmtHS c m d f

/-! ## Facts about the run's root slice -/

theorem nextKeys_eq_regOuts : ∀ b : List Stmt, (∀ s ∈ b, isAsgInstReg s = true) →
    nextKeys b = regOuts b := by
  intro b
  induction b with
  | nil => intro _; rfl
  | cons s rest ih =>
    intro h
    have hr := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases s with
    | assign l r => simp only [nextKeys, List.flatMap_cons, List.nil_append] at hr ⊢; rw [hr, regOuts_asg]
    | inst a b c => simp only [nextKeys, List.flatMap_cons, List.nil_append] at hr ⊢; rw [hr, regOuts_inst]
    | register o c r e i =>
      simp only [nextKeys, List.flatMap_cons] at hr ⊢
      rw [regOuts_reg, hr]; rfl
    | memory _ _ _ _ _ _ _ _ _ _ _ _ =>
      have := h _ (List.mem_cons_self ..); simp [isAsgInstReg] at this

theorem applyH_root_cons (st : HSt) (nx : List (String × Nat)) (ys : Ups) : applyH st (([], nx) :: ys) [] = applyNexts (st []) nx := by
  funext n
  simp [applyH, List.find?_cons]

/-- Per-cycle facts of a successful trace: the cycle's root slice, its next list, and the next
cycle's root slice. -/
theorem runHSTrace_next (d : Design) (arr : Module → List Stmt) (m : Module)
    (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : HSt) (envs : List Env) (sts : List HSt),
      runHSTrace d arr m seed k st = some (envs, sts) →
      (0 < k → sts[0]? = some st) ∧
      ∀ t, t + 1 < k → ∃ E S S' nx, envs[t]? = some E ∧ sts[t]? = some S ∧ sts[t + 1]? = some S' ∧
        regNexts (declWidth m) (fun _ _ => 0) (arr m) E = some nx ∧ S' [] = applyNexts (S []) nx := by
  intro k
  induction k with
  | zero => intro st envs sts h; exact ⟨fun h => absurd h (Nat.lt_irrefl _), fun t ht => absurd ht (by omega)⟩
  | succ k ih =>
    intro st envs sts hrun
    simp only [runHSTrace] at hrun
    cases hs : stepHS d arr m st (seed k (restrictTo (regOuts (arr m)) (st []))) with
    | none => simp [hs] at hrun
    | some r =>
      obtain ⟨envF, ups⟩ := r
      cases hr : runHSTrace d arr m seed k (applyH st ups) with
      | none => simp [hs, hr] at hrun
      | some q =>
        obtain ⟨rest, sts'⟩ := q
        simp [hs, hr] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        obtain ⟨_, _, nxP, ys, hn, hk, rfl⟩ := stepHS_some_inv hs
        refine ⟨fun _ => rfl, ?_⟩
        intro t ht
        cases t with
        | zero =>
          obtain ⟨hs0, _⟩ := ih (applyH st (([], nxP) :: ys)) rest sts' hr
          have hk0 : 0 < k := by omega
          obtain ⟨S1, hS1⟩ : ∃ S1, sts'[0]? = some S1 := by
            cases sts' with
            | nil => simp at hs0 <;> omega
            | cons a _ => exact ⟨a, rfl⟩
          have := hs0 hk0
          rw [hS1] at this
          cases this
          exact ⟨envF, st, applyH st (([], nxP) :: ys), nxP, rfl, rfl, by simpa using hS1,
            hn, applyH_root_cons st nxP ys⟩
        | succ t =>
          obtain ⟨_, hrest⟩ := ih (applyH st (([], nxP) :: ys)) rest sts' hr
          obtain ⟨E, S, S', nx, h1, h2, h3, h4, h5⟩ := hrest t (by omega)
          exact ⟨E, S, S', nx, by simpa using h1, by simpa using h2, by simpa using h3, h4, h5⟩

theorem restrictTo_perm {b b' : List Stmt} (hp : b.Perm b') (q : String → Nat) :
    restrictTo (regOuts b) q = restrictTo (regOuts b') q := by
  funext n
  unfold restrictTo
  have h : (regOuts b).contains n = (regOuts b').contains n := by
    cases h1 : (regOuts b).contains n <;> cases h2 : (regOuts b').contains n <;> try rfl
    · have := (regOuts_perm_mem hp n).mpr (List.contains_iff_mem.mp h2)
      rw [List.contains_iff_mem.mpr this] at h1; cases h1
    · have := (regOuts_perm_mem hp n).mp (List.contains_iff_mem.mp h1)
      rw [List.contains_iff_mem.mpr this] at h2; cases h2
  rw [h]

/-- THE COMPOSITION THEOREM FOR A PARENT WITH REGISTERS (H2b).  See the file header: `R` is the
parent-register invariant, `hkid` the instances' oracle (`kid_inst`), `hstep` one cycle of the open
parent from any state satisfying `R`. -/
theorem outputsOnHS_of_stepR (c : Contract) (m : Module) (d : Design)
    (arr : Module → List Stmt) (f : c.table.Ty)
    (hS : HierShapeS d m = true) (hA : AdmArr d m arr)
    (hsupp : ExprsSupp m (arr m)) (hch : ∀ x ∈ d.modules, ChildSucc x (arr x))
    (b0 : List Stmt) (hp : (arr m).Perm b0) (hw0 : WOH d b0) (hnd : (regOuts b0).Nodup)
    (hai0 : ∀ s ∈ b0, isAsgInstReg s = true)
    (Ow : (Nat → String → Nat) → String → Nat → Nat)
    (hkid : ∀ ins, InputsOk c m ins → ∀ K envs sts,
      runHSTrace d arr m (seedFwd m K ins) K (st0H d m) = some (envs, sts) →
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
