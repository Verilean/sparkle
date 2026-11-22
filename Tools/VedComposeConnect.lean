import Lean
import Tools.VedComposeResearchCut
import Tools.DeepElab

/-!
# VED compose, connection (unit `sparkle-ved-compose-connect`): the returned IR's cone to the open parent's deep cone

`Tools/VedComposeResearchCut.lean` (approved) proves `inl_sound`, `bn_sound` and `cone_connect_bn`: the value of an
assignment's right-hand side at the abstract environment `E` of `step_local` equals the value of the NORMALISED INLINED cone at
the leaf valuation `leafEnv` (cycle inputs, pre-state, oracle).  This file adds the three pieces the research note lists as
missing (docs/VED-COMPOSE-RESEARCH.md §7):

* **W (width transport)**: `ren_eval` evaluates a renamed cone under another width environment and another valuation; `tabW`
  is the closed Bool check that every leaf of the returned cone has, in the deep context, the width the returned module's
  `declWidth` gives it.  No width fact is assumed.
* **R (needed-leaf range)**: `needed_range` turns the per-leaf facts the generated script already holds (register invariant,
  input contract, child output width) into the range premise of `cone_connect_bn`, for exactly the leaves the inlined cone reads
  (`neededOk`, closed); the clock is never required to fit its (zero) declared width.
* **F (fidelity)**: `connect_value` takes the fidelity theorem `_deep_fidelity_*` (the compiled deep cone IS the literal `L`) by
  its TYPE; `renE τ c = L` is a closed equation on the returned cone `c`, with `L` unified from the theorem's type.

`reg_connect` and `out_connect` are what the generated proof applies, once per register and once for the port.  Nothing in this
file changes a statement; `U2HRStmt` is untouched.
-/

namespace Tools.VedComposeConnect

open Sparkle.IR.AST Sparkle.IR.Semantics Tools.VedComposeResearch
open Tools.VedU1Hier Tools.VedU2Hier Tools.VedU1Contract

register_option ved.compose.connect : Bool := {
  defValue := false
  descr := "VED compose: close the parent's step by the approved connection lemmas (inl_sound / bn_sound / cone_connect_bn), the deep fidelity facts and a leaf table, instead of per-cone simp"
}

/-! ## Renaming the leaves of a cone -/

mutual
def renE (τ : String → String) : Expr → Expr
  | .ref x => .ref (τ x)
  | .op o as => .op o (renL τ as)
  | .concat as => .concat (renL τ as)
  | .slice e hi lo => .slice (renE τ e) hi lo
  | e => e
def renL (τ : String → String) : List Expr → List Expr
  | [] => []
  | a :: r => renE τ a :: renL τ r
end

theorem renL_eq_map (τ : String → String) : ∀ as : List Expr, renL τ as = as.map (renE τ)
  | [] => rfl
  | a :: r => by simp only [renL, List.map_cons, renL_eq_map τ r]

/-! ## The map lemmas with two width environments -/

theorem width_op_map2 (we1 we2 : WEnv) (f : Expr → Expr) (o : Operator) (as : List Expr)
    (hw : ∀ a ∈ as, widthOf we2 (f a) = widthOf we1 a) :
    widthOf we2 (.op o (as.map f)) = widthOf we1 (.op o as) := by
  rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, r⟩⟩⟩⟩
  · cases o <;> simp [widthOf]
  · have ha := hw a (by simp)
    cases o <;> simp [widthOf, ha]
  · have ha := hw a (by simp)
    have hb := hw b (by simp)
    cases o <;> simp [widthOf, ha, hb]
  · have ha := hw a (by simp)
    have hb := hw b (by simp)
    cases o <;> simp [widthOf, hb]
  · cases o <;> simp [widthOf]

theorem width_concat_map2 (we1 we2 : WEnv) (f : Expr → Expr) (as : List Expr)
    (hw : ∀ a ∈ as, widthOf we2 (f a) = widthOf we1 a) :
    widthOf we2 (.concat (as.map f)) = widthOf we1 (.concat as) := by
  simp only [widthOf]
  induction as with
  | nil => rfl
  | cons a r ih =>
    simp only [List.map_cons, widthOf.go]
    rw [hw a (by simp), ih (fun x hx => hw x (by simp [hx]))]

theorem evalOp_map2 (we1 we2 : WEnv) (f : Expr → Expr) (o : Operator) (as : List Expr) (vals : List Nat) (w : Nat)
    (hw : ∀ a ∈ as, widthOf we2 (f a) = widthOf we1 a) :
    evalOp we2 o (as.map f) vals w = evalOp we1 o as vals w := by
  rcases as with _ | ⟨a, _ | ⟨b, r⟩⟩
  · rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨u, vs⟩⟩⟩⟩ <;> cases o <;> simp [evalOp]
  · have ha := hw a (by simp)
    rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨u, vs⟩⟩⟩⟩ <;> cases o <;> simp [evalOp, ha]
  · have ha := hw a (by simp)
    have hb := hw b (by simp)
    rcases r with _ | ⟨c, r⟩
    · rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨u, vs⟩⟩⟩⟩ <;> cases o <;> simp [evalOp, ha, hb]
    · rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨u, vs⟩⟩⟩⟩ <;> cases o <;> simp [evalOp]

theorem evalList_map2 (we1 we2 : WEnv) (E1 E2 : Env) (f : Expr → Expr) (as : List Expr)
    (h : ∀ a ∈ as, evalExpr we2 E2 (f a) = evalExpr we1 E1 a) :
    evalList we2 E2 (as.map f) = evalList we1 E1 as := by
  induction as with
  | nil => rfl
  | cons a r ih =>
    simp only [List.map_cons, evalList]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem foldl_zip_map2 (we1 we2 : WEnv) (f : Expr → Expr) (as : List Expr) (vs : List Nat) (acc : Nat)
    (hw : ∀ a ∈ as, widthOf we2 (f a) = widthOf we1 a) :
    ((as.map f).zip vs).foldl (fun acc (p : Expr × Nat) => acc + widthOf we2 p.1) acc
      = (as.zip vs).foldl (fun acc (p : Expr × Nat) => acc + widthOf we1 p.1) acc := by
  induction as generalizing vs acc with
  | nil => simp
  | cons a r ih =>
    cases vs with
    | nil => simp
    | cons v vs =>
      simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
      rw [hw a (by simp), ih _ _ (fun x hx => hw x (by simp [hx]))]

theorem go_map2 (we1 we2 : WEnv) (f : Expr → Expr) (as : List Expr) (vs : List Nat)
    (hw : ∀ a ∈ as, widthOf we2 (f a) = widthOf we1 a) :
    evalExpr.go we2 (as.map f) vs = evalExpr.go we1 as vs := by
  induction as generalizing vs with
  | nil => simp [evalExpr.go]
  | cons a r ih =>
    cases vs with
    | nil => simp [evalExpr.go]
    | cons v vs =>
      simp only [List.map_cons, evalExpr.go]
      rw [foldl_zip_map2 we1 we2 f r vs 0 (fun x hx => hw x (by simp [hx])), hw a (by simp),
        ih _ (fun x hx => hw x (by simp [hx]))]

/-! ## Evaluation under a renaming: width and value transfer (W) -/

mutual
/-- Renaming the leaves of `c` by `τ` and evaluating under `(we', E')` is evaluating `c` under `(we, E)`, provided every leaf
agrees: `we' (τ x) = we x` and `E' (τ x) = E x`.  The width of the renamed cone is the width of `c`. -/
theorem ren_eval (we we' : WEnv) (E E' : Env) (τ : String → String) :
    ∀ c : Expr, (∀ x ∈ refs c, we' (τ x) = we x ∧ E' (τ x) = E x) →
      evalExpr we' E' (renE τ c) = evalExpr we E c ∧ widthOf we' (renE τ c) = widthOf we c
  | .const _ _, _ => ⟨rfl, rfl⟩
  | .sliceDim _ _ _, _ => ⟨rfl, rfl⟩
  | .index _ _, _ => ⟨rfl, rfl⟩
  | .ref x, h => by
      have hx := h x (by simp [refs])
      simp only [renE, evalExpr, widthOf]
      rw [hx.1, hx.2]
      exact ⟨rfl, rfl⟩
  | .slice e hi lo, h => by
      have ih := ren_eval we we' E E' τ e (fun x hx => h x (by simpa [refs] using hx))
      simp only [renE, evalExpr, widthOf]
      rw [ih.1]
      exact ⟨rfl, trivial⟩
  | .op o as, h => by
      have hl := ren_evalL we we' E E' τ as (fun x hx => h x (by simpa [refs] using hx))
      have hE : ∀ a ∈ as, evalExpr we' E' (renE τ a) = evalExpr we E a := fun a ha => (hl a ha).1
      have hW : ∀ a ∈ as, widthOf we' (renE τ a) = widthOf we a := fun a ha => (hl a ha).2
      simp only [renE, renL_eq_map]
      refine ⟨?_, width_op_map2 we we' _ o as hW⟩
      simp only [evalExpr]
      rw [evalList_map2 we we' E E' _ as hE, width_op_map2 we we' _ o as hW]
      cases evalList we E as with
      | none => rfl
      | some vals => simp only [Bind.bind, Option.bind]; rw [evalOp_map2 we we' _ o as vals _ hW]
  | .concat as, h => by
      have hl := ren_evalL we we' E E' τ as (fun x hx => h x (by simpa [refs] using hx))
      have hE : ∀ a ∈ as, evalExpr we' E' (renE τ a) = evalExpr we E a := fun a ha => (hl a ha).1
      have hW : ∀ a ∈ as, widthOf we' (renE τ a) = widthOf we a := fun a ha => (hl a ha).2
      simp only [renE, renL_eq_map]
      refine ⟨?_, width_concat_map2 we we' _ as hW⟩
      simp only [evalExpr]
      rw [evalList_map2 we we' E E' _ as hE]
      cases evalList we E as with
      | none => rfl
      | some vals => simp only [Bind.bind, Option.bind]; rw [go_map2 we we' _ as vals hW]
theorem ren_evalL (we we' : WEnv) (E E' : Env) (τ : String → String) :
    ∀ as : List Expr, (∀ x ∈ refsL as, we' (τ x) = we x ∧ E' (τ x) = E x) →
      ∀ a ∈ as, evalExpr we' E' (renE τ a) = evalExpr we E a ∧ widthOf we' (renE τ a) = widthOf we a
  | [], _ => by intro a ha; cases ha
  | b :: r, h => by
      intro a ha
      rcases List.mem_cons.mp ha with h1 | ha
      · rw [h1]
        exact ren_eval we we' E E' τ b (fun x hx => h x (by simp [refsL, hx]))
      · exact ren_evalL we we' E E' τ r (fun x hx => h x (by simp [refsL, hx])) a ha
end

/-! ## The leaf table: returned name ↦ slot of the deep context -/

/-- The renaming of the leaf table: a returned leaf name goes to the name of its slot in the deep context's name function. -/
def tauOf {n : Nat} (nm : Fin n → String) (tab : List (String × Nat)) : String → String :=
  fun x => match tab.lookup x with
    | some j => if h : j < n then nm ⟨j, h⟩ else x
    | none => x

/-- (W, closed) every leaf of the returned cone is in the table, its slot exists, and the width the returned module gives it
(`wm`, i.e. `declWidth m`) is the width of that slot of the deep context `Γ`. -/
def tabW (Γ : List Nat) (wm : WEnv) (tab : List (String × Nat)) (c : Expr) : Bool :=
  (refs c).all fun x => match tab.lookup x with
    | some j => decide (j < Γ.length) && (wm x == Γ.getD j 0)
    | none => false

theorem lookup_mem : ∀ (l : List (String × Nat)) (x : String) (j : Nat), l.lookup x = some j → (x, j) ∈ l
  | [], x, j, h => by simp [List.lookup] at h
  | (a, b) :: r, x, j, h => by
      simp only [List.lookup] at h
      cases hxa : (x == a)
      · rw [hxa] at h
        exact List.mem_cons_of_mem _ (lookup_mem r x j h)
      · rw [hxa] at h
        have h1 : x = a := by simpa using hxa
        have h2 : b = j := by simpa using h
        subst h1; subst h2
        exact List.mem_cons_self ..

theorem tabW_sound {n : Nat} (Γget : Fin n → Nat) (Γ : List Nat) (hΓ : ∀ j : Fin n, Γget j = Γ.getD j.val 0)
    (hn : Γ.length = n) (wm : WEnv) (tab : List (String × Nat)) (c : Expr) (h : tabW Γ wm tab c = true) :
    ∀ x ∈ refs c, ∃ j, ∃ hj : j < n, tab.lookup x = some j ∧ wm x = Γget ⟨j, hj⟩ := by
  intro x hx
  simp only [tabW, List.all_eq_true] at h
  have hx' := h x hx
  cases hl : tab.lookup x with
  | none => rw [hl] at hx'; simp at hx'
  | some j =>
    rw [hl] at hx'
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx'
    refine ⟨j, hn ▸ hx'.1, rfl, ?_⟩
    rw [hΓ ⟨j, hn ▸ hx'.1⟩]
    exact hx'.2

/-- A cone over the returned names, renamed by the leaf table, evaluates in the deep context's environments as it does at the
leaf valuation `Lv`. -/
theorem cone_deep_eval {n : Nat} (nm : Fin n → String) (hinj : ∀ i j, nm i = nm j → i = j)
    (Γget : Fin n → Nat) (V : Fin n → Nat) (wm : WEnv) (Lv : Env) (tab : List (String × Nat)) (c L : Expr)
    (hren : renE (tauOf nm tab) c = L)
    (hW : ∀ x ∈ refs c, ∃ j, ∃ hj : j < n, tab.lookup x = some j ∧ wm x = Γget ⟨j, hj⟩)
    (hV : ∀ q ∈ tab, ∀ hq : q.2 < n, Lv q.1 = V ⟨q.2, hq⟩) :
    evalExpr (weOfC nm Γget) (envOfC nm V) L = evalExpr wm Lv c := by
  subst hren
  refine (ren_eval wm (weOfC nm Γget) Lv (envOfC nm V) (tauOf nm tab) c ?_).1
  intro x hx
  obtain ⟨j, hj, hl, hw⟩ := hW x hx
  have hτ : tauOf nm tab x = nm ⟨j, hj⟩ := by
    simp only [tauOf, hl, dif_pos hj]
  rw [hτ, weOfC_names nm Γget hinj ⟨j, hj⟩, envOfC_names nm V hinj ⟨j, hj⟩]
  exact ⟨hw.symm, (hV (x, j) (lookup_mem tab x j hl) hj).symm⟩

/-! ## R: the range facts of the leaves the inlined cone reads -/

/-- (closed) every leaf of the inlined cone is a needed leaf. -/
def neededOk (needed : List String) (c : Expr) : Bool := (refs c).all fun x => needed.contains x

theorem needed_range (wm : WEnv) (E : Env) (needed : List String) (c : Expr)
    (hn : ∀ x ∈ needed, E x < 2 ^ wm x) (h : neededOk needed c = true) :
    ∀ x ∈ refs c, E x < 2 ^ wm x := by
  intro x hx
  simp only [neededOk, List.all_eq_true] at h
  exact hn x (List.contains_iff_mem.mp (h x hx))

/-! ## Nested bundles: `concat [a, concat rest] = concat (a :: rest)`

The synthesiser bundles the registers of one `circuit do` as a RIGHT-NESTED pair (`concat [r0, concat [r1, r2]]`); the approved
`bn` resolves slices of a FLAT concatenation of refs.  `flat` flattens one nesting level bottom-up; its soundness is
`Tools.ConcatNorm.concat_pivot` (no range fact needed). -/

theorem slice_slice_val (v l1 A hi lo : Nat) (hlo : lo ≤ hi) (hhi : hi + 1 ≤ A) :
    mask (hi - lo + 1) (mask A (v >>> l1) >>> lo) = mask (hi - lo + 1) (v >>> (l1 + lo)) := by
  unfold mask
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases h : i < hi - lo + 1
  · have h2 : lo + i < A := by omega
    have h3 : l1 + (lo + i) = l1 + lo + i := by omega
    simp [h, h2, h3]
  · simp [h]

/-- A slice of a slice that stays inside the inner slice is ONE slice of the inner operand. -/
def slc (hi lo : Nat) : Expr → Expr
  | .slice e h1 l1 => if lo ≤ hi ∧ hi + l1 ≤ h1 then .slice e (l1 + hi) (l1 + lo) else .slice (.slice e h1 l1) hi lo
  | e => .slice e hi lo

theorem slc_sound (we : WEnv) (E : Env) (hi lo : Nat) (e : Expr) :
    evalExpr we E (slc hi lo e) = evalExpr we E (.slice e hi lo) ∧ widthOf we (slc hi lo e) = widthOf we (.slice e hi lo) := by
  cases e with
  | slice e h1 l1 =>
    by_cases hc : lo ≤ hi ∧ hi + l1 ≤ h1
    · have hslc : slc hi lo (.slice e h1 l1) = .slice e (l1 + hi) (l1 + lo) := by simp only [slc]; rw [if_pos hc]
      rw [hslc]
      refine ⟨?_, by simp only [widthOf]; omega⟩
      simp only [evalExpr]
      cases hv : evalExpr we E e with
      | none => rfl
      | some v =>
        simp only [Bind.bind, Option.bind]
        have : l1 + hi - (l1 + lo) = hi - lo := by omega
        rw [this, slice_slice_val v l1 (h1 - l1 + 1) hi lo hc.1 (by omega)]
    · have hslc : slc hi lo (.slice e h1 l1) = .slice (.slice e h1 l1) hi lo := by simp only [slc]; rw [if_neg hc]
      rw [hslc]
      exact ⟨rfl, rfl⟩
  | const _ _ => exact ⟨rfl, rfl⟩
  | ref _ => exact ⟨rfl, rfl⟩
  | op _ _ => exact ⟨rfl, rfl⟩
  | concat _ => exact ⟨rfl, rfl⟩
  | sliceDim _ _ _ => exact ⟨rfl, rfl⟩
  | index _ _ => exact ⟨rfl, rfl⟩

theorem refs_slc (hi lo : Nat) (e : Expr) (x : String) (hx : x ∈ refs (slc hi lo e)) : x ∈ refs e := by
  cases e with
  | slice e h1 l1 =>
    by_cases hc : lo ≤ hi ∧ hi + l1 ≤ h1
    · have hslc : slc hi lo (.slice e h1 l1) = .slice e (l1 + hi) (l1 + lo) := by simp only [slc]; rw [if_pos hc]
      rw [hslc] at hx
      simpa [refs] using hx
    · have hslc : slc hi lo (.slice e h1 l1) = .slice (.slice e h1 l1) hi lo := by simp only [slc]; rw [if_neg hc]
      rw [hslc] at hx
      simpa [refs] using hx
  | const _ _ => simpa [slc, refs] using hx
  | ref _ => simpa [slc, refs] using hx
  | op _ _ => simpa [slc, refs] using hx
  | concat _ => simpa [slc, refs] using hx
  | sliceDim _ _ _ => simpa [slc, refs] using hx
  | index _ _ => simpa [slc, refs] using hx

def flatC : List Expr → Expr
  | [a, .concat rest] => .concat (a :: rest)
  | as => .concat as

def flat : Nat → Expr → Expr
  | 0, e => e
  | n+1, .op o as => .op o (as.map (flat n))
  | n+1, .concat as => flatC (as.map (flat n))
  | n+1, .slice e hi lo => slc hi lo (flat n e)
  | _+1, e => e

theorem flatC_sound (we : WEnv) (E : Env) (l : List Expr) :
    evalExpr we E (flatC l) = evalExpr we E (.concat l) ∧ widthOf we (flatC l) = widthOf we (.concat l) := by
  unfold flatC
  split
  · next a rest =>
    refine ⟨(Tools.ConcatNorm.concat_pivot we E a rest).symm, ?_⟩
    simp [widthOf, widthOf.go]
  · exact ⟨rfl, rfl⟩

theorem refs_flatC (l : List Expr) (x : String) (hx : x ∈ refs (flatC l)) : x ∈ refsL l := by
  unfold flatC at hx
  split at hx
  · next a rest => simp only [refs, refsL, List.append_nil, List.mem_append] at hx ⊢; exact hx
  · simpa [refs] using hx

theorem refs_flat : ∀ n e x, x ∈ refs (flat n e) → x ∈ refs e := by
  intro n
  induction n with
  | zero => intro e x hx; exact hx
  | succ n ih =>
    intro e x hx
    cases e with
    | op o as =>
      simp only [flat, refs] at hx ⊢
      exact refsL_map_sub _ as (fun a _ y hy => ih a y hy) x hx
    | concat as =>
      simp only [flat, refs] at hx ⊢
      exact refsL_map_sub _ as (fun a _ y hy => ih a y hy) x (refs_flatC _ x hx)
    | slice e hi lo =>
      simp only [flat, refs]
      simp only [flat] at hx
      exact ih e x (refs_slc _ _ _ x hx)
    | const _ _ => exact hx
    | ref _ => exact hx
    | sliceDim _ _ _ => exact hx
    | index _ _ => exact hx

theorem flat_sound (we : WEnv) (E : Env) :
    ∀ n e, evalExpr we E (flat n e) = evalExpr we E e ∧ widthOf we (flat n e) = widthOf we e := by
  intro n
  induction n with
  | zero => intro e; exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro e
    cases e with
    | const _ _ => exact ⟨rfl, rfl⟩
    | ref _ => exact ⟨rfl, rfl⟩
    | sliceDim _ _ _ => exact ⟨rfl, rfl⟩
    | index _ _ => exact ⟨rfl, rfl⟩
    | slice e hi lo =>
      simp only [flat]
      have hs := slc_sound we E hi lo (flat n e)
      refine ⟨hs.1.trans ?_, hs.2.trans ?_⟩
      · simp only [evalExpr]; rw [(ih e).1]
      · simp only [widthOf]
    | op o as =>
      simp only [flat]
      have hE : ∀ a ∈ as, evalExpr we E (flat n a) = evalExpr we E a := fun a _ => (ih a).1
      have hW : ∀ a ∈ as, widthOf we (flat n a) = widthOf we a := fun a _ => (ih a).2
      refine ⟨?_, width_op_map we _ o as hW⟩
      simp only [evalExpr]
      rw [evalList_map we E _ as hE, width_op_map we _ o as hW]
      cases evalList we E as with
      | none => rfl
      | some vals => simp only [Bind.bind, Option.bind]; rw [evalOp_map we _ o as vals _ hW]
    | concat as =>
      simp only [flat]
      have hE : ∀ a ∈ as, evalExpr we E (flat n a) = evalExpr we E a := fun a _ => (ih a).1
      have hW : ∀ a ∈ as, widthOf we (flat n a) = widthOf we a := fun a _ => (ih a).2
      have hc := flatC_sound we E (as.map (flat n))
      refine ⟨hc.1.trans ?_, hc.2.trans (width_concat_map we _ as hW)⟩
      simp only [evalExpr]
      rw [evalList_map we E _ as hE]
      cases evalList we E as with
      | none => rfl
      | some vals => simp only [Bind.bind, Option.bind]; rw [go_map we _ as vals hW]

/-- `cone_connect_bn` with the flattening step: the normalised cone is `bn .. (flat .. (inl ..))`. -/
theorem cone_connect_bnf (d : Design) (m : Module) (b0 : List Stmt)
    (Ow : (Nat → String → Nat) → String → Nat → Nat)
    (hwi : ∀ n ∈ wrsH d b0, n ∉ inNames m) (hri : ∀ n ∈ regOuts b0, n ∉ inNames m)
    (hwr : ∀ n ∈ wrsH d b0, n ∉ regOuts b0)
    (hW : WOKb (declWidth m) m b0 = true)
    (ins : Nat → String → Nat) (t : Nat) (p : String → Nat) (E : Env)
    (hasg : ∀ l r, asgOf b0 l = some r → evalExpr (declWidth m) E r = some (E l))
    (hEin : ∀ x ∈ inNames m, E x = ins t x)
    (hEreg : ∀ r ∈ regOuts b0, E r = p r)
    (hEorc : ∀ mn i cs, Stmt.inst mn i cs ∈ b0 → ∀ y ∈ instOuts d mn cs, E y = Ow ins y t)
    (n n2 n3 : Nat) (e : Expr)
    (hrange : ∀ x ∈ refs (inl (Atab m b0) n e), E x < 2 ^ declWidth m x)
    (hl0 : leafOk (cutNames d m b0) (inl (Atab m b0) n e) = true) :
    evalExpr (declWidth m) E e =
      evalExpr (declWidth m) (leafEnv m b0 ins t p Ow) (bn (declWidth m) n2 (flat n3 (inl (Atab m b0) n e))) := by
  have hWo := WOKb_sound _ _ _ hW
  have hs := inl_sound (declWidth m) E (Atab m b0)
    (fun l r h => ⟨hasg l r (by unfold Atab at h; split at h <;> simp_all), hWo l r h⟩) n e
  have hleaf := leafOk_sound _ _ hl0
  have hf := flat_sound (declWidth m) E n3 (inl (Atab m b0) n e)
  have hb := bn_sound (declWidth m) E n2 (flat n3 (inl (Atab m b0) n e))
    (fun x hx => hrange x (refs_flat _ _ x hx))
  rw [← hs.1, ← hf.1, ← hb.1]
  apply eval_congr
  intro x hx
  have hcut := hleaf x (refs_flat _ _ x (refs_bn _ _ _ x hx))
  simp only [cutNames, List.mem_append] at hcut
  unfold leafEnv
  rcases hcut with (h | h) | h
  · rw [if_pos h]; exact hEin x h
  · rw [if_neg (hri x h), if_pos h]; exact hEreg x h
  · obtain ⟨mn, i, cs, hi, hy⟩ := mem_instOutsOf d b0 x h
    have hw := instOutsOf_sub_wrsH d b0 x h
    rw [if_neg (hwi x hw), if_neg (hwr x hw)]
    exact hEorc mn i cs hi x hy

/-! ## F: the connection -/

/-- **The connection (value form).**  The right-hand side `e` of an assignment holds in `E` (`he`); the normalised inlined
cone of `e` renamed by the leaf table is the fidelity literal `L` (`hren`, closed); the leaf table is width-correct (`hTW`,
closed) and value-correct (`hV`: per leaf).  Then `E x` is the value of the DEEP cone `L` in the deep context's environments. -/
theorem connect_value {n : Nat} (nm : Fin n → String) (hinj : ∀ i j, nm i = nm j → i = j)
    (Γ : List Nat) (hn : Γ.length = n)
    (V : Fin n → Nat)
    (d : Design) (m : Module) (b0 : List Stmt)
    (Ow : (Nat → String → Nat) → String → Nat → Nat)
    (hwi : ∀ n ∈ wrsH d b0, n ∉ inNames m) (hri : ∀ n ∈ regOuts b0, n ∉ inNames m)
    (hwr : ∀ n ∈ wrsH d b0, n ∉ regOuts b0)
    (hW : WOKb (declWidth m) m b0 = true)
    (ins : Nat → String → Nat) (t : Nat) (p : String → Nat) (E : Env)
    (hasg : ∀ l r, asgOf b0 l = some r → evalExpr (declWidth m) E r = some (E l))
    (hEin : ∀ x ∈ inNames m, E x = ins t x)
    (hEreg : ∀ r ∈ regOuts b0, E r = p r)
    (hEorc : ∀ mn i cs, Stmt.inst mn i cs ∈ b0 → ∀ y ∈ instOuts d mn cs, E y = Ow ins y t)
    (e : Expr) (x : String) (he : evalExpr (declWidth m) E e = some (E x))
    (nIn n2 n3 : Nat) (needed : List String)
    (hrangeN : ∀ y ∈ needed, E y < 2 ^ declWidth m y)
    (hneed : neededOk needed (inl (Atab m b0) nIn e) = true)
    (hl0 : leafOk (cutNames d m b0) (inl (Atab m b0) nIn e) = true)
    (tab : List (String × Nat)) (L : Expr)
    (hren : renE (tauOf nm tab) (bn (declWidth m) n2 (flat n3 (inl (Atab m b0) nIn e))) = L)
    (hTW : tabW Γ (declWidth m) tab (bn (declWidth m) n2 (flat n3 (inl (Atab m b0) nIn e))) = true)
    (hV : ∀ q ∈ tab, ∀ hq : q.2 < n, leafEnv m b0 ins t p Ow q.1 = V ⟨q.2, hq⟩) :
    evalExpr (weOfC nm (fun j : Fin n => Γ.getD j.val 0)) (envOfC nm V) L = some (E x) := by
  have hcc := cone_connect_bnf d m b0 Ow hwi hri hwr hW ins t p E hasg hEin hEreg hEorc nIn n2 n3 e
    (needed_range _ E needed _ hrangeN hneed) hl0
  rw [he] at hcc
  rw [cone_deep_eval nm hinj (fun j : Fin n => Γ.getD j.val 0) V (declWidth m) (leafEnv m b0 ins t p Ow) tab _ L hren
    (tabW_sound _ Γ (fun _ => rfl) hn _ tab _ hTW) hV]
  exact hcc.symm

theorem bit_toNat (n : Nat) (h : n < 2) : (bif (n != 0) then (1#1 : BitVec 1) else (0#1 : BitVec 1)).toNat = n := by
  rcases Nat.lt_or_ge n 1 with h0 | h0
  · have : n = 0 := by omega
    subst this; decide
  · have : n = 1 := by omega
    subst this; decide

theorem bv_toNat (w n : Nat) (h : n < 2 ^ w) : (BitVec.ofNat w n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The leaf-value obligation, as a name (the generated proof states it once and proves it per table entry). -/
def VOk {Γr Γi : List Nat} {wOut : Nat} (deep : Cdo Γr Γi wOut) (nm : Fin (Γr ++ Γi).length → String)
    (inp : Nat → CEnv Γi) (t : Nat) (m : Module) (b0 : List Stmt) (ins : Nat → String → Nat) (p : String → Nat)
    (Ow : (Nat → String → Nat) → String → Nat → Nat) (tab : List (String × Nat)) : Prop :=
  ∀ q ∈ tab, ∀ hq : q.2 < (Γr ++ Γi).length, leafEnv m b0 ins t p Ow q.1 =
    natJoin (deep.irState nm inp t) (fun j => (inp t j).toNat) ⟨q.2, hq⟩

/-- **Register form**: the deep recurrence at `t + 1` is the value of the register's input wire `x` in `E`. -/
theorem reg_connect {Γr Γi : List Nat} {wOut : Nat} (deep : Cdo Γr Γi wOut)
    (nm : Fin (Γr ++ Γi).length → String) (hinj : ∀ i j, nm i = nm j → i = j)
    (inp : Nat → CEnv Γi) (t : Nat) (i : Fin Γr.length) (L : Expr)
    (hfid : CExpr.compile nm (deep.next i) = L)
    (d : Design) (m : Module) (b0 : List Stmt)
    (Ow : (Nat → String → Nat) → String → Nat → Nat)
    (hwi : ∀ n ∈ wrsH d b0, n ∉ inNames m) (hri : ∀ n ∈ regOuts b0, n ∉ inNames m)
    (hwr : ∀ n ∈ wrsH d b0, n ∉ regOuts b0)
    (hW : WOKb (declWidth m) m b0 = true)
    (ins : Nat → String → Nat) (p : String → Nat) (E : Env)
    (hasg : ∀ l r, asgOf b0 l = some r → evalExpr (declWidth m) E r = some (E l))
    (hEin : ∀ x ∈ inNames m, E x = ins t x)
    (hEreg : ∀ r ∈ regOuts b0, E r = p r)
    (hEorc : ∀ mn i cs, Stmt.inst mn i cs ∈ b0 → ∀ y ∈ instOuts d mn cs, E y = Ow ins y t)
    (x : String) (nIn n2 n3 : Nat) (needed : List String)
    (hrangeN : ∀ y ∈ needed, E y < 2 ^ declWidth m y)
    (hneed : neededOk needed (inl (Atab m b0) nIn (.ref x)) = true)
    (hl0 : leafOk (cutNames d m b0) (inl (Atab m b0) nIn (.ref x)) = true)
    (tab : List (String × Nat))
    (hren : renE (tauOf nm tab) (bn (declWidth m) n2 (flat n3 (inl (Atab m b0) nIn (.ref x)))) = L)
    (hTW : tabW (Γr ++ Γi) (declWidth m) tab (bn (declWidth m) n2 (flat n3 (inl (Atab m b0) nIn (.ref x)))) = true)
    (hV : VOk deep nm inp t m b0 ins p Ow tab) :
    deep.irState nm inp (t + 1) i = E x := by
  have hv := connect_value nm hinj (Γr ++ Γi) rfl
    (natJoin (deep.irState nm inp t) (fun j => (inp t j).toNat)) d m b0 Ow hwi hri hwr hW ins t p E
    hasg hEin hEreg hEorc (.ref x) x rfl nIn n2 n3 needed hrangeN hneed hl0 tab L hren hTW hV
  show (evalExpr (weOfC nm (fun j => (Γr ++ Γi).get j)) (envOfC nm (natJoin (deep.irState nm inp t)
      (fun j => (inp t j).toNat))) ((deep.next i).compile nm)).getD 0 = E x
  rw [hfid]
  have hw : (fun j : Fin (Γr ++ Γi).length => (Γr ++ Γi).getD j.val 0) = fun j => (Γr ++ Γi).get j := by
    funext j; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt]
  rw [hw] at hv
  rw [hv]
  rfl

/-- **Port form**: the open circuit's output at cycle `t` (its IR cone `L`, `_deep_fidelity_out`) is the value of the port's
right-hand side in `E`. -/
theorem out_connect {Γr Γi : List Nat} {wOut : Nat} (deep : Cdo Γr Γi wOut)
    (nm : Fin (Γr ++ Γi).length → String) (hinj : ∀ i j, nm i = nm j → i = j)
    (inp : Nat → CEnv Γi) (t : Nat) (L : Expr)
    (hfid : CExpr.compile nm deep.out = L)
    (d : Design) (m : Module) (b0 : List Stmt)
    (Ow : (Nat → String → Nat) → String → Nat → Nat)
    (hwi : ∀ n ∈ wrsH d b0, n ∉ inNames m) (hri : ∀ n ∈ regOuts b0, n ∉ inNames m)
    (hwr : ∀ n ∈ wrsH d b0, n ∉ regOuts b0)
    (hW : WOKb (declWidth m) m b0 = true)
    (ins : Nat → String → Nat) (p : String → Nat) (E : Env)
    (hasg : ∀ l r, asgOf b0 l = some r → evalExpr (declWidth m) E r = some (E l))
    (hEin : ∀ x ∈ inNames m, E x = ins t x)
    (hEreg : ∀ r ∈ regOuts b0, E r = p r)
    (hEorc : ∀ mn i cs, Stmt.inst mn i cs ∈ b0 → ∀ y ∈ instOuts d mn cs, E y = Ow ins y t)
    (e : Expr) (x : String) (he : evalExpr (declWidth m) E e = some (E x))
    (nIn n2 n3 : Nat) (needed : List String)
    (hrangeN : ∀ y ∈ needed, E y < 2 ^ declWidth m y)
    (hneed : neededOk needed (inl (Atab m b0) nIn e) = true)
    (hl0 : leafOk (cutNames d m b0) (inl (Atab m b0) nIn e) = true)
    (tab : List (String × Nat))
    (hren : renE (tauOf nm tab) (bn (declWidth m) n2 (flat n3 (inl (Atab m b0) nIn e))) = L)
    (hTW : tabW (Γr ++ Γi) (declWidth m) tab (bn (declWidth m) n2 (flat n3 (inl (Atab m b0) nIn e))) = true)
    (hV : VOk deep nm inp t m b0 ins p Ow tab) :
    E x = (evalExpr (weOfC nm (fun j => (Γr ++ Γi).get j)) (envOfC nm (natJoin (deep.irState nm inp t)
      (fun j => (inp t j).toNat))) (CExpr.compile nm deep.out)).getD 0 := by
  have hv := connect_value nm hinj (Γr ++ Γi) rfl
    (natJoin (deep.irState nm inp t) (fun j => (inp t j).toNat)) d m b0 Ow hwi hri hwr hW ins t p E
    hasg hEin hEreg hEorc e x he nIn n2 n3 needed hrangeN hneed hl0 tab L hren hTW hV
  rw [hfid]
  have hw : (fun j : Fin (Γr ++ Γi).length => (Γr ++ Γi).getD j.val 0) = fun j => (Γr ++ Γi).get j := by
    funext j; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt]
  rw [hw] at hv
  rw [hv]
  rfl

/-! ## Batched closed checks (one kernel evaluation for all registers)

`reg_connect` takes four closed facts per register (`hneed`, `hl0`, `hTW`, `hren`).  Proving them by four `decide +kernel` / `rfl`
calls per register re-evaluates the inlined cone, with its `String` table scans, from a cold cache every time (observed: ~1 s each at
13 registers, growing with the register count).  `RegsOk` is ONE Bool over all register slots, evaluated once by the kernel;
`regs_spec` hands each slot's four facts back.  The equation `hren` is decided by `eqE` (a structural equality of expressions, with
`eqE_sound`) against `CExpr.compile nm (deep.next i)`, which the fidelity theorem `hfid` identifies with the literal `L`.  The
statements of `reg_connect` / `out_connect` are unchanged. -/

mutual
/-- Structural equality of the expression forms a returned cone consists of (anything else compares unequal). -/
def eqE : Expr → Expr → Bool
  | .const v w, b => match b with
    | .const v' w' => decide (v = v') && decide (w = w')
    | _ => false
  | .ref x, b => match b with
    | .ref y => decide (x = y)
    | _ => false
  | .op o as, b => match b with
    | .op o' as' => decide (o = o') && eqL as as'
    | _ => false
  | .concat as, b => match b with
    | .concat as' => eqL as as'
    | _ => false
  | .slice e hi lo, b => match b with
    | .slice e' hi' lo' => eqE e e' && decide (hi = hi') && decide (lo = lo')
    | _ => false
  | .sliceDim .., _ => false
  | .index .., _ => false
def eqL : List Expr → List Expr → Bool
  | [], b => match b with
    | [] => true
    | _ => false
  | a :: r, b => match b with
    | c :: s => eqE a c && eqL r s
    | [] => false
end

mutual
theorem eqE_sound : ∀ a b : Expr, eqE a b = true → a = b
  | .const v w, b, h => by
      cases b with
      | const v' w' => simp only [eqE, Bool.and_eq_true, decide_eq_true_eq] at h; rw [h.1, h.2]
      | _ => simp [eqE] at h
  | .ref x, b, h => by
      cases b with
      | ref y => simp only [eqE, decide_eq_true_eq] at h; rw [h]
      | _ => simp [eqE] at h
  | .op o as, b, h => by
      cases b with
      | op o' as' => simp only [eqE, Bool.and_eq_true, decide_eq_true_eq] at h; rw [h.1, eqL_sound as _ h.2]
      | _ => simp [eqE] at h
  | .concat as, b, h => by
      cases b with
      | concat as' => simp only [eqE] at h; rw [eqL_sound as _ h]
      | _ => simp [eqE] at h
  | .slice e hi lo, b, h => by
      cases b with
      | slice e' hi' lo' =>
        simp only [eqE, Bool.and_eq_true, decide_eq_true_eq] at h
        rw [eqE_sound e _ h.1.1, h.1.2, h.2]
      | _ => simp [eqE] at h
  | .sliceDim .., b, h => by simp [eqE] at h
  | .index .., b, h => by simp [eqE] at h
theorem eqL_sound : ∀ as bs : List Expr, eqL as bs = true → as = bs
  | [], b, h => by
      cases b with
      | nil => rfl
      | cons _ _ => simp [eqL] at h
  | a :: r, b, h => by
      cases b with
      | nil => simp [eqL] at h
      | cons c s =>
        simp only [eqL, Bool.and_eq_true] at h
        rw [eqE_sound a _ h.1, eqL_sound r _ h.2]
end

/-- The four closed facts of one register slot: its input wire `x`, the cone compared with `L`. -/
def specOk (d : Design) (m : Module) (b0 : List Stmt) (needed : List String) (Γ : List Nat) (τ : String → String)
    (tab : List (String × Nat)) (nIn n2 n3 : Nat) (x : String) (L : Expr) : Bool :=
  neededOk needed (inl (Atab m b0) nIn (.ref x)) && leafOk (cutNames d m b0) (inl (Atab m b0) nIn (.ref x)) &&
    tabW Γ (declWidth m) tab (bn (declWidth m) n2 (flat n3 (inl (Atab m b0) nIn (.ref x)))) &&
    eqE (renE τ (bn (declWidth m) n2 (flat n3 (inl (Atab m b0) nIn (.ref x))))) L

/-- ONE Bool for all register slots of the deep context (`xs`: the input wire of each slot). -/
def RegsOk {Γr Γi : List Nat} {wOut : Nat} (deep : Cdo Γr Γi wOut) (nm : Fin (Γr ++ Γi).length → String)
    (d : Design) (m : Module) (b0 : List Stmt) (needed : List String) (tab : List (String × Nat)) (nIn n2 n3 : Nat)
    (xs : List String) : Bool :=
  (List.finRange Γr.length).all fun i =>
    specOk d m b0 needed (Γr ++ Γi) (tauOf nm tab) tab nIn n2 n3 (xs.getD i.val "") (CExpr.compile nm (deep.next i))

theorem regs_spec {Γr Γi : List Nat} {wOut : Nat} (deep : Cdo Γr Γi wOut) (nm : Fin (Γr ++ Γi).length → String)
    (d : Design) (m : Module) (b0 : List Stmt) (needed : List String) (tab : List (String × Nat)) (nIn n2 n3 : Nat)
    (xs : List String) (h : RegsOk deep nm d m b0 needed tab nIn n2 n3 xs = true)
    (i : Fin Γr.length) (x : String) (hx : xs.getD i.val "" = x) (L : Expr) (hfid : CExpr.compile nm (deep.next i) = L) :
    neededOk needed (inl (Atab m b0) nIn (.ref x)) = true ∧
    leafOk (cutNames d m b0) (inl (Atab m b0) nIn (.ref x)) = true ∧
    tabW (Γr ++ Γi) (declWidth m) tab (bn (declWidth m) n2 (flat n3 (inl (Atab m b0) nIn (.ref x)))) = true ∧
    renE (tauOf nm tab) (bn (declWidth m) n2 (flat n3 (inl (Atab m b0) nIn (.ref x)))) = L := by
  simp only [RegsOk, List.all_eq_true] at h
  have h1 := h i (List.mem_finRange i)
  rw [hx, hfid] at h1
  simp only [specOk, Bool.and_eq_true] at h1
  exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, eqE_sound _ _ h1.2⟩

/-! ## Small facts the generated proof uses -/

theorem leafEnv_reg {m : Module} {b0 : List Stmt} {ins : Nat → String → Nat} {t : Nat} {p : String → Nat}
    {Ow : (Nat → String → Nat) → String → Nat → Nat} {x : String} (hx : x ∈ regOuts b0) (hn : x ∉ inNames m) :
    leafEnv m b0 ins t p Ow x = p x := by
  unfold leafEnv; rw [if_neg hn, if_pos hx]

theorem leafEnv_in {m : Module} {b0 : List Stmt} {ins : Nat → String → Nat} {t : Nat} {p : String → Nat}
    {Ow : (Nat → String → Nat) → String → Nat → Nat} {x : String} (hx : x ∈ inNames m) :
    leafEnv m b0 ins t p Ow x = ins t x := by
  unfold leafEnv; rw [if_pos hx]

theorem leafEnv_orc {m : Module} {b0 : List Stmt} {ins : Nat → String → Nat} {t : Nat} {p : String → Nat}
    {Ow : (Nat → String → Nat) → String → Nat → Nat} {x : String} (hn : x ∉ inNames m) (hr : x ∉ regOuts b0) :
    leafEnv m b0 ins t p Ow x = Ow ins x t := by
  unfold leafEnv; rw [if_neg hn, if_neg hr]

theorem mask_next {w a v : Nat} (h : v = a) (hlt : v < 2 ^ w) : mask w a = v := by
  subst h; exact Nat.mod_eq_of_lt hlt

open Lean Elab Tactic in
/-- The observable record of the new path: one info line per connection the generated proof applies. -/
elab "ved_connect_log " s:str : tactic => logInfo m!"VED COMPOSE CONNECT: {s.getString}"

end Tools.VedComposeConnect
