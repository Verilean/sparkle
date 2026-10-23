import Tools.ShippingSrm5Height
import Tools.ShippingDesignSVBack
-- BUILT/UNBUILT: UNBUILT (unit SRM10; build runs are listed in REPORT-SRM10.md).
-- SCOPE (binding): a HEIGHT-INDEXED output check `houtsMod C rk f o` / `houtsCheck C rk f h o` that mirrors SRM5's `hcheck` (rank table `rk` by module NAME; a built memory module is rank 0),
-- and the smallest links to the UNIFORM `outsCheck C n` of `Tools/ShippingDesignSVBack.lean` (the check consumed by `design_sv_backN` / `design_sv_unique` / `design_sv_all`):
--   * `houtsMod`: a rank-0 module needs `outsLeaf` (its outputs are assigned or are the read port of a combinational memory); a module of rank `h+1` needs `outsAssigned` AND, for each of its instances, the edge facts of `hcheck` (target resolves, rank `r ≤ h`, `child.name = mn`) and `houtsMod` of the child.  Unranked / unresolved is a REFUSAL (`false`).
--   * `houtsCheck C rk f h o`: the check of the KIDS of `o` (like `outsCheck`, which also constrains only the kids), `o` of rank `h+1`.
--   * PROVED link A (`outsCheck_of_houtsCheck_uni`): `houtsCheck` plus the rank-uniformity condition `UniRank n o` (every instance of `o` has rank exactly `n`, recursively) gives `outsCheck C n o`.  CONDITIONAL on `UniRank`; it is NOT claimed for unbalanced trees (`outsCheck` there asks `outsAssigned` of a rank-0 memory kid, which `houtsMod` does not give).
--   * PROVED link B (`houtsCheck_of_outsCheck_hcheck`): `hcheck` (SRM5) plus the uniform `outsCheck C (m+1) o` for every `m` gives `houtsCheck` (the per-module check is weaker than the uniform one when the tree is ranked).
-- NOT done here: a height-indexed restatement of `design_sv_backN` itself (that is the SRM6 `HeightBridge`; owner SRM6).  `houtsMod_outs` is the per-kid fact that restatement would consume.
-- No `sorry`, no `axiom`, no `native_decide`, no heartbeat option.

namespace Tools.ShippingSrm10Outs
open Sparkle.IR.AST Sparkle.IR.Semantics Tools.ShippingDesignSV Tools.ShippingSrm5Height Tools.ShippingDesignSVBack

variable (C : String → Option (Module × WEnv)) (rk : String → Option Nat)

/-- **The height-indexed output check of a module at its own rank** (`f` is a fuel, as in `hcheck`). -/
def houtsMod : Nat → Module → Bool
  | 0, o => decide (rk o.name = some 0) && outsLeaf o
  | f + 1, o => match rk o.name with
    | none => false
    | some 0 => outsLeaf o
    | some (h + 1) => outsAssigned o && o.body.all (instOkH C rk (houtsMod f) h)

/-- **The output check of the KIDS of `o`** (the analogue of `outsCheck C n o`, which also constrains only the instances of `o`);
`o` has rank `h + 1`, every kid has rank `r ≤ h`, is identified by name, and passes `houtsMod`. -/
def houtsCheck (f h : Nat) (o : Module) : Bool :=
  o.body.all (instOkH C rk (houtsMod C rk f) h)

/-- **Rank uniformity** (the condition under which the uniform `outsCheck C n` is meaningful): every instance of `o` is of rank exactly `n`,
and (for `n = m+1`) the resolved child satisfies the condition at `m`. -/
def UniRank : Nat → Module → Prop
  | 0, _ => True
  | n + 1, o => ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body →
      rk mn = some (n + 1) ∧ ∀ child cwe, C mn = some (child, cwe) → UniRank n child

variable {C rk}

theorem outsLeaf_of_outsAssigned {m : Module} (h : outsAssigned m = true) : outsLeaf m = true := by
  unfold outsAssigned at h
  unfold outsLeaf
  rw [List.all_eq_true] at h ⊢
  intro p hp
  have := h p hp
  rw [List.any_eq_true] at this ⊢
  obtain ⟨st, hst, hs⟩ := this
  exact ⟨st, hst, by cases st <;> simp_all⟩

/-- rank 0: `outsLeaf` is the check, at every fuel -/
theorem houtsMod_rank0 {o : Module} (hr : rk o.name = some 0) (hl : outsLeaf o = true) (f : Nat) :
    houtsMod C rk f o = true := by
  cases f <;> simp [houtsMod, hr, hl]

/-- positive rank: one statement -/
theorem houtsMod_succ_iff {o : Module} {h : Nat} (hr : rk o.name = some (h + 1)) (f : Nat) :
    houtsMod C rk (f + 1) o = true ↔ outsAssigned o = true ∧ houtsCheck C rk f h o = true := by
  simp [houtsMod, hr, houtsCheck]

/-- **A checked module of positive rank needs fuel and gives `outsAssigned` and the kids' check.** -/
theorem houtsMod_pos {o : Module} {h f : Nat} (hr : rk o.name = some (h + 1))
    (hc : houtsMod C rk f o = true) :
    ∃ f', f = f' + 1 ∧ outsAssigned o = true ∧ houtsCheck C rk f' h o = true := by
  cases f with
  | zero => simp [houtsMod, hr] at hc
  | succ f' => exact ⟨f', rfl, (houtsMod_succ_iff hr f').mp hc⟩

/-- **The per-kid output fact a consumer needs** (what `design_sv_backN` extracts from `outsCheck` for a kid, as `outsLeaf` at the bottom and `outsAssigned` above it):
a checked module has some rank, passes `outsLeaf`, and, when its rank is positive, `outsAssigned`. -/
theorem houtsMod_outs {o : Module} {f : Nat} (hc : houtsMod C rk f o = true) :
    ∃ r, rk o.name = some r ∧ outsLeaf o = true ∧ (0 < r → outsAssigned o = true) := by
  cases f with
  | zero =>
    simp only [houtsMod, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨0, hc.1, hc.2, fun h => absurd h (Nat.lt_irrefl _)⟩
  | succ f' =>
    cases hr : rk o.name with
    | none => simp [houtsMod, hr] at hc
    | some r =>
      cases r with
      | zero =>
        simp only [houtsMod, hr] at hc
        exact ⟨0, rfl, hc, fun h => absurd h (Nat.lt_irrefl _)⟩
      | succ h =>
        have := ((houtsMod_succ_iff hr f').mp hc).1
        exact ⟨h + 1, rfl, outsLeaf_of_outsAssigned this, fun _ => this⟩

/-- the edge facts of `houtsCheck` for one instance -/
theorem houtsCheck_at {f h : Nat} {o : Module} (hc : houtsCheck C rk f h o = true)
    {mn iname conns} (hm : Stmt.inst mn iname conns ∈ o.body) :
    ∃ child cwe r, C mn = some (child, cwe) ∧ rk mn = some r ∧ r ≤ h ∧ child.name = mn ∧
      houtsMod C rk f child = true :=
  instOkH_inst.mp (List.all_eq_true.mp hc _ hm)

theorem kidsPass_of_resolved {F : Module → Bool} {body : List Stmt}
    (h : ∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
      ∃ child cwe, C mn = some (child, cwe) ∧ F child = true) : kidsPass C F body = true := by
  unfold kidsPass
  rw [List.all_eq_true]
  intro st hst
  cases st with
  | inst mn iname conns =>
    obtain ⟨child, cwe, hc, hF⟩ := h mn iname conns hst
    simp [hc, hF]
  | _ => rfl

theorem outsCheck_succ_at {n : Nat} {o : Module} (h : outsCheck C (n + 1) o = true)
    {mn iname conns} {child : Module} {cwe : WEnv} (hm : Stmt.inst mn iname conns ∈ o.body)
    (hc : C mn = some (child, cwe)) : outsAssigned child = true ∧ outsCheck C n child = true := by
  have h' : kidsPass C (fun c => outsAssigned c && outsCheck C n c) o.body = true := h
  have := kidsPass_at h' hm hc
  simpa using this

/-- **LINK A (conditional on `UniRank`).**  The height-indexed check of the kids of `o`, for a tree whose instances have rank exactly the remaining depth
(`UniRank n o`), gives the uniform `outsCheck C n o`.  Range: ONLY balanced trees; the rank of `o` is not needed. -/
theorem outsCheck_of_houtsCheck_uni :
    ∀ (n : Nat) (o : Module) (f h : Nat), houtsCheck C rk f h o = true → UniRank C rk n o →
      outsCheck C n o = true
  | 0, o, f, h, hc, _ => by
    simp only [outsCheck]
    refine kidsPass_of_resolved fun mn iname conns hm => ?_
    obtain ⟨child, cwe, r, h1, -, -, -, h5⟩ := houtsCheck_at hc hm
    exact ⟨child, cwe, h1, (houtsMod_outs h5).choose_spec.2.1⟩
  | n + 1, o, f, h, hc, hu => by
    simp only [outsCheck]
    refine kidsPass_of_resolved fun mn iname conns hm => ?_
    obtain ⟨child, cwe, r, h1, h2, h3, h4, h5⟩ := houtsCheck_at hc hm
    obtain ⟨hr, hkid⟩ := hu mn iname conns hm
    rw [h2] at hr
    cases hr
    have hrc : rk child.name = some (n + 1) := by rw [h4]; exact h2
    obtain ⟨f', rfl, hA, hK⟩ := houtsMod_pos hrc h5
    exact ⟨child, cwe, h1, by
      rw [Bool.and_eq_true]
      exact ⟨hA, outsCheck_of_houtsCheck_uni n child f' n hK (hkid child cwe h1)⟩⟩

/-- **LINK B.**  The per-module check follows from SRM5's `hcheck` (edge facts, ranks) and the uniform `outsCheck C (m+1)` at every `m`:
the height-indexed output check is implied by the uniform one on a ranked tree. -/
theorem houtsMod_of_outsCheck_hcheck :
    ∀ (f : Nat) (k : Module), hcheck C rk f k = true → outsAssigned k = true →
      (∀ m, outsCheck C (m + 1) k = true) → houtsMod C rk f k = true
  | 0, k, hc, hA, _ => by
    simp only [hcheck, Bool.and_eq_true] at hc
    simp only [houtsMod, Bool.and_eq_true]
    exact ⟨hc.1, outsLeaf_of_outsAssigned hA⟩
  | f + 1, k, hc, hA, hoc => by
    cases hr : rk k.name with
    | none => simp [hcheck, hr] at hc
    | some r =>
      cases r with
      | zero => simp only [houtsMod, hr]; exact outsLeaf_of_outsAssigned hA
      | succ h =>
        rw [houtsMod_succ_iff hr]
        refine ⟨hA, ?_⟩
        unfold houtsCheck
        rw [List.all_eq_true]
        intro st hst
        cases st with
        | inst mn iname conns =>
          obtain ⟨child, cwe, r', h1, h2, h3, h4, h5⟩ := ((hcheck_succ_iff hr f).mp hc).2 mn iname conns hst
          have hAc : outsAssigned child = true := (outsCheck_succ_at (hoc 0) hst h1).1
          have := houtsMod_of_outsCheck_hcheck f child h5 hAc (fun m => (outsCheck_succ_at (hoc (m + 1)) hst h1).2)
          exact instOkH_inst.mpr ⟨child, cwe, r', h1, h2, h3, h4, this⟩
        | _ => rfl

/-- **LINK B at the top**: the kids' check of a module of rank `h + 1`. -/
theorem houtsCheck_of_outsCheck_hcheck {o : Module} {h f : Nat} (hr : rk o.name = some (h + 1))
    (hc : hcheck C rk (f + 1) o = true) (hoc : ∀ m, outsCheck C (m + 1) o = true) :
    houtsCheck C rk f h o = true := by
  unfold houtsCheck
  rw [List.all_eq_true]
  intro st hst
  cases st with
  | inst mn iname conns =>
    obtain ⟨child, cwe, r', h1, h2, h3, h4, h5⟩ := ((hcheck_succ_iff hr f).mp hc).2 mn iname conns hst
    have hAc : outsAssigned child = true := (outsCheck_succ_at (hoc 0) hst h1).1
    have := houtsMod_of_outsCheck_hcheck f child h5 hAc (fun m => (outsCheck_succ_at (hoc (m + 1)) hst h1).2)
    exact instOkH_inst.mpr ⟨child, cwe, r', h1, h2, h3, h4, this⟩
  | _ => rfl

/-! ## Refusals: a missing rank, an unresolved target, a non-decreasing edge is `false` (never an assumption) -/

theorem houtsMod_norank {o : Module} {f : Nat} (hr : rk o.name = none) : houtsMod C rk (f + 1) o = false := by
  simp [houtsMod, hr]

theorem houtsCheck_unresolved {f h : Nat} {o : Module} {mn iname conns}
    (hm : Stmt.inst mn iname conns ∈ o.body) (hu : C mn = none) : houtsCheck C rk f h o = false := by
  cases hb : houtsCheck C rk f h o
  · rfl
  · obtain ⟨child, cwe, -, h1, -⟩ := houtsCheck_at hb hm
    rw [hu] at h1; cases h1

theorem houtsCheck_notBelow {f h : Nat} {o : Module} {mn iname conns}
    (hm : Stmt.inst mn iname conns ∈ o.body) {r : Nat} (hrm : rk mn = some r) (hge : h < r) :
    houtsCheck C rk f h o = false := by
  cases hb : houtsCheck C rk f h o
  · rfl
  · obtain ⟨child, cwe, r', -, h2, h3, -⟩ := houtsCheck_at hb hm
    rw [hrm] at h2; cases h2; omega

/-- a rank-0 module whose outputs are neither assigned nor a combinational memory read is refused -/
theorem houtsMod_rank0_refused {o : Module} (hr : rk o.name = some 0) (hl : outsLeaf o = false) (f : Nat) :
    houtsMod C rk f o = false := by
  cases f <;> simp [houtsMod, hr, hl]

end Tools.ShippingSrm10Outs

#print axioms Tools.ShippingSrm10Outs.outsCheck_of_houtsCheck_uni
#print axioms Tools.ShippingSrm10Outs.houtsMod_of_outsCheck_hcheck
#print axioms Tools.ShippingSrm10Outs.houtsCheck_of_outsCheck_hcheck
#print axioms Tools.ShippingSrm10Outs.houtsMod_outs
