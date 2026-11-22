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
    (nIn n2 : Nat) (needed : List String)
    (hrangeN : ∀ y ∈ needed, E y < 2 ^ declWidth m y)
    (hneed : neededOk needed (inl (Atab m b0) nIn e) = true)
    (hl0 : leafOk (cutNames d m b0) (inl (Atab m b0) nIn e) = true)
    (tab : List (String × Nat)) (L : Expr)
    (hren : renE (tauOf nm tab) (bn (declWidth m) n2 (inl (Atab m b0) nIn e)) = L)
    (hTW : tabW Γ (declWidth m) tab (bn (declWidth m) n2 (inl (Atab m b0) nIn e)) = true)
    (hV : ∀ q ∈ tab, ∀ hq : q.2 < n, leafEnv m b0 ins t p Ow q.1 = V ⟨q.2, hq⟩) :
    evalExpr (weOfC nm (fun j : Fin n => Γ.getD j.val 0)) (envOfC nm V) L = some (E x) := by
  have hcc := cone_connect_bn d m b0 Ow hwi hri hwr hW ins t p E hasg hEin hEreg hEorc nIn n2 e _
    (needed_range _ E needed _ hrangeN hneed) rfl hl0
  rw [he] at hcc
  rw [cone_deep_eval nm hinj (fun j : Fin n => Γ.getD j.val 0) V (declWidth m) (leafEnv m b0 ins t p Ow) tab _ L hren
    (tabW_sound _ Γ (fun _ => rfl) hn _ tab _ hTW) hV]
  exact hcc.symm

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
    (x : String) (nIn n2 : Nat) (needed : List String)
    (hrangeN : ∀ y ∈ needed, E y < 2 ^ declWidth m y)
    (hneed : neededOk needed (inl (Atab m b0) nIn (.ref x)) = true)
    (hl0 : leafOk (cutNames d m b0) (inl (Atab m b0) nIn (.ref x)) = true)
    (tab : List (String × Nat))
    (hren : renE (tauOf nm tab) (bn (declWidth m) n2 (inl (Atab m b0) nIn (.ref x))) = L)
    (hTW : tabW (Γr ++ Γi) (declWidth m) tab (bn (declWidth m) n2 (inl (Atab m b0) nIn (.ref x))) = true)
    (hV : ∀ q ∈ tab, ∀ hq : q.2 < (Γr ++ Γi).length, leafEnv m b0 ins t p Ow q.1 =
      natJoin (deep.irState nm inp t) (fun j => (inp t j).toNat) ⟨q.2, hq⟩) :
    deep.irState nm inp (t + 1) i = E x := by
  have hv := connect_value nm hinj (Γr ++ Γi) rfl
    (natJoin (deep.irState nm inp t) (fun j => (inp t j).toNat)) d m b0 Ow hwi hri hwr hW ins t p E
    hasg hEin hEreg hEorc (.ref x) x rfl nIn n2 needed hrangeN hneed hl0 tab L hren hTW hV
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
    (nIn n2 : Nat) (needed : List String)
    (hrangeN : ∀ y ∈ needed, E y < 2 ^ declWidth m y)
    (hneed : neededOk needed (inl (Atab m b0) nIn e) = true)
    (hl0 : leafOk (cutNames d m b0) (inl (Atab m b0) nIn e) = true)
    (tab : List (String × Nat))
    (hren : renE (tauOf nm tab) (bn (declWidth m) n2 (inl (Atab m b0) nIn e)) = L)
    (hTW : tabW (Γr ++ Γi) (declWidth m) tab (bn (declWidth m) n2 (inl (Atab m b0) nIn e)) = true)
    (hV : ∀ q ∈ tab, ∀ hq : q.2 < (Γr ++ Γi).length, leafEnv m b0 ins t p Ow q.1 =
      natJoin (deep.irState nm inp t) (fun j => (inp t j).toNat) ⟨q.2, hq⟩) :
    E x = (evalExpr (weOfC nm (fun j => (Γr ++ Γi).get j)) (envOfC nm (natJoin (deep.irState nm inp t)
      (fun j => (inp t j).toNat))) (CExpr.compile nm deep.out)).getD 0 := by
  have hv := connect_value nm hinj (Γr ++ Γi) rfl
    (natJoin (deep.irState nm inp t) (fun j => (inp t j).toNat)) d m b0 Ow hwi hri hwr hW ins t p E
    hasg hEin hEreg hEorc e x he nIn n2 needed hrangeN hneed hl0 tab L hren hTW hV
  rw [hfid]
  have hw : (fun j : Fin (Γr ++ Γi).length => (Γr ++ Γi).getD j.val 0) = fun j => (Γr ++ Γi).get j := by
    funext j; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt]
  rw [hw] at hv
  rw [hv]
  rfl

end Tools.VedComposeConnect
