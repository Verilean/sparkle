import Lean
import Tools.VedComposeStep
import Tools.VedU2HierMultiBundle

/-!
# VED compose research: the cone connection (prototype, new file, nothing existing is changed)

See docs/VED-COMPOSE-RESEARCH.md.  The published decomposition methods (ACL2 SV override transparency, Kami modular
refinement) both reduce to one local obligation per cut point: *the cone that is proved about equals the cone that the
design computes*.  For Sparkle the cut (instance outputs replaced by oracle wires) is already sound and generic
(`fold_oracle`, `step_local`); what is missing is a kernel-checked statement that the RETURNED statement list, read from
the cut leaves (parent inputs, register outputs, instance outputs), computes the cone literal that the open parent's deep
run was proved about.

`inl` inlines the assigned wires of the returned arrangement.  `inl_sound` is proved ONCE for any arrangement whose
assignments hold in an environment `E` (`hasg` of `step_local`) and whose assignments are width-consistent
(`widthOf we rhs = we lhs`): without the width side condition inlining is NOT sound, because the IR semantics reads the
element widths of a concatenation, of `not`, of the signed comparisons and the context width of every operator off the
*syntax* (`widthOf`), and `widthOf (ref x) = we x` differs from the width of the right-hand side in general.
-/

namespace Tools.VedComposeResearch

open Sparkle.IR.AST Sparkle.IR.Semantics

/-- Inline the assigned wires, `n` levels deep.  `A` is the assignment table of the arrangement. -/
def inl (A : String → Option Expr) : Nat → Expr → Expr
  | 0, e => e
  | n+1, .ref x => match A x with
    | some r => inl A n r
    | none => .ref x
  | n+1, .op o as => .op o (as.map (inl A n))
  | n+1, .concat as => .concat (as.map (inl A n))
  | n+1, .slice e hi lo => .slice (inl A n e) hi lo
  | _+1, e => e

-- Free wire names of an expression (the leaves).
mutual
def refs : Expr → List String
  | .ref x => [x]
  | .op _ as => refsL as
  | .concat as => refsL as
  | .slice e _ _ => refs e
  | _ => []
def refsL : List Expr → List String
  | [] => []
  | a :: r => refs a ++ refsL r
end

theorem width_op_map (we : WEnv) (f : Expr → Expr) (o : Operator) (as : List Expr)
    (hw : ∀ a ∈ as, widthOf we (f a) = widthOf we a) :
    widthOf we (.op o (as.map f)) = widthOf we (.op o as) := by
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

theorem width_concat_map (we : WEnv) (f : Expr → Expr) (as : List Expr)
    (hw : ∀ a ∈ as, widthOf we (f a) = widthOf we a) :
    widthOf we (.concat (as.map f)) = widthOf we (.concat as) := by
  simp only [widthOf]
  induction as with
  | nil => rfl
  | cons a r ih =>
    simp only [List.map_cons, widthOf.go]
    rw [hw a (by simp), ih (fun x hx => hw x (by simp [hx]))]

theorem evalOp_map (we : WEnv) (f : Expr → Expr) (o : Operator) (as : List Expr) (vals : List Nat) (w : Nat)
    (hw : ∀ a ∈ as, widthOf we (f a) = widthOf we a) :
    evalOp we o (as.map f) vals w = evalOp we o as vals w := by
  rcases as with _ | ⟨a, _ | ⟨b, r⟩⟩
  · rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨u, vs⟩⟩⟩⟩ <;> cases o <;> simp [evalOp]
  · have ha := hw a (by simp)
    rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨u, vs⟩⟩⟩⟩ <;> cases o <;> simp [evalOp, ha]
  · have ha := hw a (by simp)
    have hb := hw b (by simp)
    rcases r with _ | ⟨c, r⟩
    · rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨u, vs⟩⟩⟩⟩ <;> cases o <;> simp [evalOp, ha, hb]
    · rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨u, vs⟩⟩⟩⟩ <;> cases o <;> simp [evalOp]

theorem evalList_map (we : WEnv) (E : Env) (f : Expr → Expr) (as : List Expr)
    (h : ∀ a ∈ as, evalExpr we E (f a) = evalExpr we E a) :
    evalList we E (as.map f) = evalList we E as := by
  induction as with
  | nil => rfl
  | cons a r ih =>
    simp only [List.map_cons, evalList]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem foldl_zip_map (we : WEnv) (f : Expr → Expr) (as : List Expr) (vs : List Nat) (acc : Nat)
    (hw : ∀ a ∈ as, widthOf we (f a) = widthOf we a) :
    ((as.map f).zip vs).foldl (fun acc (p : Expr × Nat) => acc + widthOf we p.1) acc
      = (as.zip vs).foldl (fun acc (p : Expr × Nat) => acc + widthOf we p.1) acc := by
  induction as generalizing vs acc with
  | nil => simp
  | cons a r ih =>
    cases vs with
    | nil => simp
    | cons v vs =>
      simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
      rw [hw a (by simp), ih _ _ (fun x hx => hw x (by simp [hx]))]

theorem go_map (we : WEnv) (f : Expr → Expr) (as : List Expr) (vs : List Nat)
    (hw : ∀ a ∈ as, widthOf we (f a) = widthOf we a) :
    evalExpr.go we (as.map f) vs = evalExpr.go we as vs := by
  induction as generalizing vs with
  | nil => simp [evalExpr.go]
  | cons a r ih =>
    cases vs with
    | nil => simp [evalExpr.go]
    | cons v vs =>
      simp only [List.map_cons, evalExpr.go]
      rw [foldl_zip_map we f r vs 0 (fun x hx => hw x (by simp [hx])), hw a (by simp),
        ih _ (fun x hx => hw x (by simp [hx]))]

/-- INLINING IS SOUND, for any fuel, when every assignment of the table holds in `E` and is width-consistent. -/
theorem inl_sound (we : WEnv) (E : Env) (A : String → Option Expr)
    (hA : ∀ l r, A l = some r → evalExpr we E r = some (E l) ∧ widthOf we r = we l) :
    ∀ n e, evalExpr we E (inl A n e) = evalExpr we E e ∧ widthOf we (inl A n e) = widthOf we e := by
  intro n
  induction n with
  | zero => intro e; exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro e
    cases e with
    | const v w => exact ⟨rfl, rfl⟩
    | sliceDim _ _ _ => exact ⟨rfl, rfl⟩
    | index _ _ => exact ⟨rfl, rfl⟩
    | ref x =>
      simp only [inl]
      cases hx : A x with
      | none => exact ⟨rfl, rfl⟩
      | some r =>
        obtain ⟨h1, h2⟩ := hA x r hx
        exact ⟨(ih r).1.trans h1, (ih r).2.trans h2⟩
    | slice e hi lo =>
      simp only [inl, evalExpr, widthOf]
      rw [(ih e).1]
      exact ⟨rfl, trivial⟩
    | op o as =>
      simp only [inl]
      have hE : ∀ a ∈ as, evalExpr we E (inl A n a) = evalExpr we E a := fun a _ => (ih a).1
      have hW : ∀ a ∈ as, widthOf we (inl A n a) = widthOf we a := fun a _ => (ih a).2
      refine ⟨?_, width_op_map we _ o as hW⟩
      simp only [evalExpr]
      rw [evalList_map we E _ as hE, width_op_map we _ o as hW]
      cases evalList we E as with
      | none => rfl
      | some vals => simp only [Bind.bind, Option.bind]; rw [evalOp_map we _ o as vals _ hW]
    | concat as =>
      simp only [inl]
      have hE : ∀ a ∈ as, evalExpr we E (inl A n a) = evalExpr we E a := fun a _ => (ih a).1
      have hW : ∀ a ∈ as, widthOf we (inl A n a) = widthOf we a := fun a _ => (ih a).2
      refine ⟨?_, width_concat_map we _ as hW⟩
      simp only [evalExpr]
      rw [evalList_map we E _ as hE]
      cases evalList we E as with
      | none => rfl
      | some vals => simp only [Bind.bind, Option.bind]; rw [go_map we _ as vals hW]

/-! ## The value of an expression depends only on its leaves -/

mutual
theorem eval_congr (we : WEnv) (E1 E2 : Env) :
    ∀ e : Expr, (∀ x ∈ refs e, E1 x = E2 x) → evalExpr we E1 e = evalExpr we E2 e
  | .const _ _, _ => rfl
  | .sliceDim _ _ _, _ => rfl
  | .index _ _, _ => rfl
  | .ref x, h => by simp only [evalExpr]; rw [h x (by simp [refs])]
  | .slice e hi lo, h => by
      simp only [evalExpr]; rw [eval_congr we E1 E2 e (fun x hx => h x (by simpa [refs] using hx))]
  | .op o as, h => by
      simp only [evalExpr]
      rw [evalList_congr we E1 E2 as (fun x hx => h x (by simpa [refs] using hx))]
  | .concat as, h => by
      simp only [evalExpr]
      rw [evalList_congr we E1 E2 as (fun x hx => h x (by simpa [refs] using hx))]
theorem evalList_congr (we : WEnv) (E1 E2 : Env) :
    ∀ as : List Expr, (∀ x ∈ refsL as, E1 x = E2 x) → evalList we E1 as = evalList we E2 as
  | [], _ => rfl
  | a :: r, h => by
      simp only [evalList]
      rw [eval_congr we E1 E2 a (fun x hx => h x (by simp [refsL, hx])),
        evalList_congr we E1 E2 r (fun x hx => h x (by simp [refsL, hx]))]
end

/-! ## Bundle slices: the narrow normaliser (M2) -/

open Tools.VedU2HierMulti in
/-- Index of the element of a concatenation of refs that an `[hi:lo]` slice spans exactly. -/
def alignedIdx (we : WEnv) : List String → Nat → Nat → Option Nat
  | [], _, _ => none
  | n :: rest, hi, lo =>
    if lo = W we rest ∧ hi + 1 = lo + we n ∧ 0 < we n then some 0
    else (alignedIdx we rest hi lo).map (· + 1)

def refNames : List Expr → Option (List String)
  | [] => some []
  | .ref x :: r => (refNames r).map (x :: ·)
  | _ => none

/-- One slice step on an already normalised operand. -/
def bnS (we : WEnv) (hi lo : Nat) : Expr → Expr
  | .concat es =>
    match refNames es with
    | some names =>
      match alignedIdx we names hi lo with
      | some k => .ref (names.getD k "")
      | none => .slice (.concat es) hi lo
    | none => .slice (.concat es) hi lo
  | .ref x => if lo = 0 ∧ hi + 1 = we x then .ref x else .slice (.ref x) hi lo
  | e => .slice e hi lo

/-- Resolve aligned bundle slices (and full-width slices of a ref), bottom-up, `n` levels deep. -/
def bn (we : WEnv) : Nat → Expr → Expr
  | 0, e => e
  | n+1, .op o as => .op o (as.map (bn we n))
  | n+1, .concat as => .concat (as.map (bn we n))
  | n+1, .slice e hi lo => bnS we hi lo (bn we n e)
  | _+1, e => e

open Tools.VedU2HierMulti in
theorem alignedIdx_spec (we : WEnv) : ∀ (names : List String) (hi lo k : Nat),
    alignedIdx we names hi lo = some k →
    ∃ hk : k < names.length, lo = W we (names.drop (k + 1)) ∧ hi + 1 = lo + we names[k] ∧ 0 < we names[k] := by
  intro names
  induction names with
  | nil => intro hi lo k h; simp [alignedIdx] at h
  | cons n rest ih =>
    intro hi lo k h
    simp only [alignedIdx] at h
    split at h
    · rename_i hc
      cases h
      exact ⟨by simp, by simpa using hc.1, by simpa using hc.2.1, by simpa using hc.2.2⟩
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h
      obtain ⟨hk, h1, h2, h3⟩ := ih hi lo j hj
      exact ⟨by simpa using hk, by simpa using h1, by simpa using h2, by simpa using h3⟩

theorem refNames_eq (es : List Expr) (names : List String) (h : refNames es = some names) :
    es = names.map Expr.ref := by
  induction es generalizing names with
  | nil => simp only [refNames, Option.some.injEq] at h; subst h; rfl
  | cons e r ih =>
    cases e <;> try (simp [refNames] at h; done)
    rename_i x
    simp only [refNames, Option.map_eq_some_iff] at h
    obtain ⟨ns, hns, rfl⟩ := h
    simp only [List.map_cons, List.cons.injEq, true_and]
    exact ih ns hns

theorem refs_concat_refs (names : List String) : refs (.concat (names.map Expr.ref)) = names := by
  simp only [refs]
  induction names with
  | nil => rfl
  | cons n r ih => simp [refsL, refs, ih]

theorem bnS_sound (we : WEnv) (E : Env) (hi lo : Nat) (e : Expr)
    (hr : ∀ x ∈ refs e, E x < 2 ^ we x) :
    evalExpr we E (bnS we hi lo e) = evalExpr we E (.slice e hi lo) ∧
    widthOf we (bnS we hi lo e) = widthOf we (.slice e hi lo) := by
  cases e with
  | concat es =>
    simp only [bnS]
    cases hm : refNames es with
    | none => exact ⟨rfl, rfl⟩
    | some names =>
      simp only
      cases ha : alignedIdx we names hi lo with
      | none => exact ⟨rfl, rfl⟩
      | some k =>
        simp only
        obtain ⟨hk, hlo, hhi, hw0⟩ := alignedIdx_spec we names hi lo k ha
        have hes := refNames_eq es names hm
        subst hes
        have hrk : E names[k] < 2 ^ we names[k] := by
          apply hr
          rw [refs_concat_refs]
          exact List.getElem_mem hk
        have hv : evalExpr we E (.concat (names.map Expr.ref)) = some (evalExpr.go we (names.map Expr.ref) (names.map E)) :=
          Tools.VedU2HierMulti.eval_concat_refs we E names
        have hsl := Tools.VedU2HierMulti.slice_concat_val we E names k hk _ hi lo hv hlo hhi hw0 hrk
        have getD_eq : names.getD k "" = names[k] := by simp [List.getD_eq_getElem?_getD, hk]
        rw [getD_eq]
        refine ⟨?_, ?_⟩
        · have hsl' : evalExpr we E (.slice (.concat (names.map Expr.ref)) hi lo)
              = (evalExpr we E (.concat (names.map Expr.ref))).bind
                  (fun v => some (mask (hi - lo + 1) (v >>> lo))) := rfl
          rw [hsl', hv]
          show some (E names[k]) = some _
          rw [hsl]
        · simp only [widthOf]; omega
  | ref x =>
    simp only [bnS]
    split
    · rename_i hc
      obtain ⟨h0, h1⟩ := hc
      subst h0
      refine ⟨?_, ?_⟩
      · have hx := hr x (by simp [refs])
        have hs : evalExpr we E (.slice (.ref x) hi 0) = some (mask (hi - 0 + 1) (E x >>> 0)) := rfl
        rw [hs]
        show some (E x) = some _
        have hw : hi - 0 + 1 = we x := by omega
        rw [hw]
        simp [mask, Nat.mod_eq_of_lt hx]
      · simp only [widthOf]; omega
    · exact ⟨rfl, rfl⟩
  | const _ _ => exact ⟨rfl, rfl⟩
  | op _ _ => exact ⟨rfl, rfl⟩
  | slice _ _ _ => exact ⟨rfl, rfl⟩
  | sliceDim _ _ _ => exact ⟨rfl, rfl⟩
  | index _ _ => exact ⟨rfl, rfl⟩


theorem refsL_mem_of_mem (as : List Expr) (a : Expr) (ha : a ∈ as) (x : String) (hx : x ∈ refs a) : x ∈ refsL as := by
  induction as with
  | nil => cases ha
  | cons b r ih =>
    simp only [refsL, List.mem_append]
    rcases List.mem_cons.mp ha with rfl | h
    · exact Or.inl hx
    · exact Or.inr (ih h)

theorem refsL_map_sub (f : Expr → Expr) (as : List Expr) (h : ∀ a ∈ as, ∀ x ∈ refs (f a), x ∈ refs a)
    (x : String) (hx : x ∈ refsL (as.map f)) : x ∈ refsL as := by
  induction as with
  | nil => simp [refsL] at hx
  | cons b r ih =>
    simp only [List.map_cons, refsL, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl (h b (by simp) x hx)
    · exact Or.inr (ih (fun a ha y hy => h a (by simp [ha]) y hy) hx)

theorem refs_bnS (we : WEnv) (hi lo : Nat) (e : Expr) (x : String) (hx : x ∈ refs (bnS we hi lo e)) : x ∈ refs e := by
  cases e with
  | concat es =>
    simp only [bnS] at hx
    cases hm : refNames es with
    | none => simpa [hm, refs] using hx
    | some names =>
      cases ha : alignedIdx we names hi lo with
      | none => simpa [hm, ha, refs] using hx
      | some k =>
        simp only [hm, ha, refs, refsL, List.append_nil, List.mem_singleton] at hx
        obtain ⟨hk, _⟩ := alignedIdx_spec we names hi lo k ha
        have hes := refNames_eq es names hm
        subst hes
        rw [refs_concat_refs]
        subst hx
        have : names.getD k "" = names[k] := by simp [List.getD_eq_getElem?_getD, hk]
        rw [this]; exact List.getElem_mem hk
  | ref y =>
    simp only [bnS] at hx
    split at hx
    · exact hx
    · simpa [refs] using hx
  | const _ _ => simpa [bnS, refs] using hx
  | op _ _ => simpa [bnS, refs] using hx
  | slice _ _ _ => simpa [bnS, refs] using hx
  | sliceDim _ _ _ => simpa [bnS, refs] using hx
  | index _ _ => simpa [bnS, refs] using hx

theorem refs_bn (we : WEnv) : ∀ n e x, x ∈ refs (bn we n e) → x ∈ refs e := by
  intro n
  induction n with
  | zero => intro e x hx; exact hx
  | succ n ih =>
    intro e x hx
    cases e with
    | op o as =>
      simp only [bn, refs] at hx ⊢
      exact refsL_map_sub _ as (fun a _ y hy => ih a y hy) x hx
    | concat as =>
      simp only [bn, refs] at hx ⊢
      exact refsL_map_sub _ as (fun a _ y hy => ih a y hy) x hx
    | slice e hi lo =>
      simp only [bn] at hx
      have := refs_bnS we hi lo _ x hx
      simp only [refs]
      exact ih e x this
    | const _ _ => exact hx
    | ref _ => exact hx
    | sliceDim _ _ _ => exact hx
    | index _ _ => exact hx

/-- THE NORMALISER IS SOUND under range facts on the leaves of the expression. -/
theorem bn_sound (we : WEnv) (E : Env) :
    ∀ n e, (∀ x ∈ refs e, E x < 2 ^ we x) →
      evalExpr we E (bn we n e) = evalExpr we E e ∧ widthOf we (bn we n e) = widthOf we e := by
  intro n
  induction n with
  | zero => intro e _; exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro e hr
    cases e with
    | const _ _ => exact ⟨rfl, rfl⟩
    | ref _ => exact ⟨rfl, rfl⟩
    | sliceDim _ _ _ => exact ⟨rfl, rfl⟩
    | index _ _ => exact ⟨rfl, rfl⟩
    | slice e hi lo =>
      simp only [bn]
      have h1 := ih e (by simpa [refs] using hr)
      have h2 := bnS_sound we E hi lo (bn we n e)
        (fun x hx => hr x (by simpa [refs] using refs_bn we n e x hx))
      refine ⟨?_, ?_⟩
      · rw [h2.1]; simp only [evalExpr]; rw [h1.1]
      · rw [h2.2]; rfl
    | op o as =>
      simp only [bn]
      have hE : ∀ a ∈ as, evalExpr we E (bn we n a) = evalExpr we E a :=
        fun a ha => (ih a (fun x hx => hr x (by simpa [refs] using refsL_mem_of_mem as a ha x hx))).1
      have hW : ∀ a ∈ as, widthOf we (bn we n a) = widthOf we a :=
        fun a ha => (ih a (fun x hx => hr x (by simpa [refs] using refsL_mem_of_mem as a ha x hx))).2
      refine ⟨?_, width_op_map we _ o as hW⟩
      simp only [evalExpr]
      rw [evalList_map we E _ as hE, width_op_map we _ o as hW]
      cases evalList we E as with
      | none => rfl
      | some vals => simp only [Bind.bind, Option.bind]; rw [evalOp_map we _ o as vals _ hW]
    | concat as =>
      simp only [bn]
      have hE : ∀ a ∈ as, evalExpr we E (bn we n a) = evalExpr we E a :=
        fun a ha => (ih a (fun x hx => hr x (by simpa [refs] using refsL_mem_of_mem as a ha x hx))).1
      have hW : ∀ a ∈ as, widthOf we (bn we n a) = widthOf we a :=
        fun a ha => (ih a (fun x hx => hr x (by simpa [refs] using refsL_mem_of_mem as a ha x hx))).2
      refine ⟨?_, width_concat_map we _ as hW⟩
      simp only [evalExpr]
      rw [evalList_map we E _ as hE]
      cases evalList we E as with
      | none => rfl
      | some vals => simp only [Bind.bind, Option.bind]; rw [go_map we _ as vals hW]

/-! ## The connection to `step_local` -/

open Tools.VedU1Hier Tools.VedU2Hier Tools.VedU1Contract

/-- The output port names of a module.  An output port is not a declared wire (`declWidth m out = 0`), and nothing reads it. -/
def outsOf (m : Module) : List String := m.outputs.map (·.name)

/-- The inlining table: the assignments of the arrangement, without the output ports. -/
def Atab (m : Module) (b : List Stmt) : String → Option Expr :=
  fun x => if (outsOf m).contains x then none else asgOf b x

/-- Width consistency of the inlined assignments (the side condition of `inl_sound`), decidable.  Observed (scratch/runs/54,
55): on the returned module of EVERY registered toy family (9 modules) the only width-inconsistent assignment of the full
body is the output port `out` (declared width 0 because it is a port, not a wire), which is why the table excludes outputs. -/
def WOKb (we : WEnv) (m : Module) (b : List Stmt) : Bool :=
  b.all fun s => match s with
    | .assign l r => (outsOf m).contains l || widthOf we r == we l
    | _ => true

theorem WOKb_sound (we : WEnv) (m : Module) (b : List Stmt) (h : WOKb we m b = true) :
    ∀ l r, Atab m b l = some r → widthOf we r = we l := by
  intro l r hr
  unfold Atab at hr
  by_cases hm : (outsOf m).contains l = true
  · rw [if_pos hm] at hr; cases hr
  · rw [if_neg hm] at hr
    have hm2 := asgOf_mem hr
    have h3 := List.all_eq_true.mp h _ hm2
    have hc' : (outsOf m).contains l = false := by simpa using hm
    simp only [hc', Bool.false_or, beq_iff_eq] at h3
    exact h3

/-- The cut points: parent inputs, register outputs, instance outputs.  These are the only names whose value the cone
side supplies (`hEin`, `hEreg`, `hEorc` of `step_local`) - the transparency condition of the cut. -/
def cutNames (d : Design) (m : Module) (b0 : List Stmt) : List String :=
  inNames m ++ regOuts b0 ++ instOutsOf d b0

/-- The cone's leaves are all cut points. -/
def leafOk (cut : List String) (c : Expr) : Bool := (refs c).all fun x => cut.contains x

theorem leafOk_sound (cut : List String) (c : Expr) (h : leafOk cut c = true) : ∀ x ∈ refs c, x ∈ cut := by
  intro x hx
  simp only [leafOk, List.all_eq_true] at h
  exact List.contains_iff_mem.mp (h x hx)

theorem mem_instOutsOf (d : Design) : ∀ (b : List Stmt) (n : String), n ∈ instOutsOf d b →
    ∃ mn i cs, Stmt.inst mn i cs ∈ b ∧ n ∈ instOuts d mn cs := by
  intro b
  induction b with
  | nil => intro n h; cases h
  | cons s rest ih =>
    intro n h
    cases s with
    | inst mn i cs =>
      simp only [instOutsOf, List.mem_append] at h
      rcases h with h | h
      · exact ⟨mn, i, cs, List.mem_cons_self .., h⟩
      · obtain ⟨a, b', c, h1, h2⟩ := ih n h
        exact ⟨a, b', c, List.mem_cons_of_mem _ h1, h2⟩
    | assign l r =>
      simp only [instOutsOf] at h
      obtain ⟨a, b', c, h1, h2⟩ := ih n h
      exact ⟨a, b', c, List.mem_cons_of_mem _ h1, h2⟩
    | register _ _ _ _ _ =>
      simp only [instOutsOf] at h
      obtain ⟨a, b', c, h1, h2⟩ := ih n h
      exact ⟨a, b', c, List.mem_cons_of_mem _ h1, h2⟩
    | memory _ _ _ _ _ _ _ _ _ _ _ _ =>
      simp only [instOutsOf] at h
      obtain ⟨a, b', c, h1, h2⟩ := ih n h
      exact ⟨a, b', c, List.mem_cons_of_mem _ h1, h2⟩

/-- The valuation the cone is evaluated at: the cycle's inputs, the pre-update registers, the oracle values. -/
def leafEnv (m : Module) (b0 : List Stmt) (ins : Nat → String → Nat) (t : Nat) (p : String → Nat)
    (Ow : (Nat → String → Nat) → String → Nat → Nat) : Env :=
  fun x => if x ∈ inNames m then ins t x else if x ∈ regOuts b0 then p x else Ow ins x t

/-- **THE CONNECTION PROPOSITION (cone level).**  The hypotheses `hasg hEin hEreg hEorc` are exactly the ones `step_local`
hands to `hloc` for an abstract environment `E`; `hW` is a closed Bool fact about the body; `hc` is a closed equation
(`rfl`) between the inlined right-hand side of ONE register or output and the cone literal; `hl` is a closed Bool fact
about the literal.  Conclusion: the value of that right-hand side at `E` is the value of the cone literal at the
LEAF valuation (inputs of the cycle, pre-state, oracle `Ow`) - the valuation the open parent's deep trace evaluates its
cones at. -/
theorem cone_connect (d : Design) (m : Module) (b0 : List Stmt)
    (Ow : (Nat → String → Nat) → String → Nat → Nat)
    (hwi : ∀ n ∈ wrsH d b0, n ∉ inNames m) (hri : ∀ n ∈ regOuts b0, n ∉ inNames m)
    (hwr : ∀ n ∈ wrsH d b0, n ∉ regOuts b0)
    (hW : WOKb (declWidth m) m b0 = true)
    (ins : Nat → String → Nat) (t : Nat) (p : String → Nat) (E : Env)
    (hasg : ∀ l r, asgOf b0 l = some r → evalExpr (declWidth m) E r = some (E l))
    (hEin : ∀ x ∈ inNames m, E x = ins t x)
    (hEreg : ∀ r ∈ regOuts b0, E r = p r)
    (hEorc : ∀ mn i cs, Stmt.inst mn i cs ∈ b0 → ∀ y ∈ instOuts d mn cs, E y = Ow ins y t)
    (n : Nat) (e c : Expr) (hc : inl (Atab m b0) n e = c)
    (hl : leafOk (cutNames d m b0) c = true) :
    evalExpr (declWidth m) E e = evalExpr (declWidth m) (leafEnv m b0 ins t p Ow) c := by
  have hWo := WOKb_sound _ _ _ hW
  have hs := inl_sound (declWidth m) E (Atab m b0)
    (fun l r h => ⟨hasg l r (by unfold Atab at h; split at h <;> simp_all), hWo l r h⟩) n e
  subst hc
  rw [← hs.1]
  apply eval_congr
  intro x hx
  have hcut := leafOk_sound _ _ hl x hx
  simp only [cutNames, List.mem_append] at hcut
  unfold leafEnv
  rcases hcut with (h | h) | h
  · rw [if_pos h]; exact hEin x h
  · rw [if_neg (hri x h), if_pos h]; exact hEreg x h
  · obtain ⟨mn, i, cs, hi, hy⟩ := mem_instOutsOf d b0 x h
    have hw := instOutsOf_sub_wrsH d b0 x h
    rw [if_neg (hwi x hw), if_neg (hwr x hw)]
    exact hEorc mn i cs hi x hy

/-- **THE CONNECTION PROPOSITION WITH BUNDLE SLICES.**  As `cone_connect`, with the narrow normaliser `bn` applied to the
inlined right-hand side before the comparison.  Closed facts: `hW` (`WOKb`), `hc` (`rfl`), `hl0` (every leaf of the INLINED
expression is a cut point: the fuel sufficed and nothing but inputs, registers and instance outputs is read).  The range facts
`hrange` (`E x < 2 ^ we x`) are what the register invariant, the input contract and the child's output width supply; they are
hypotheses of the per-cone obligation, not assumed done.  REVIEW FIX (P2-1): `hrange` is restricted to the NEEDED leaves, those
read by the inlined expression (`refs (inl ..)`), not the whole `cutNames`.  The earlier form quantified over every cut name,
including unread ones such as `clk` (declared width 0 in `parB`, so `E clk < 1` would force clock = 0, which the clock-universal
input contract cannot supply); `Toy.ctl_clock_old_hrange` shows that form is refused at clock = 1 and
`Toy.parB_connect_clock1` shows the restricted form applies at clock = 1. -/
theorem cone_connect_bn (d : Design) (m : Module) (b0 : List Stmt)
    (Ow : (Nat → String → Nat) → String → Nat → Nat)
    (hwi : ∀ n ∈ wrsH d b0, n ∉ inNames m) (hri : ∀ n ∈ regOuts b0, n ∉ inNames m)
    (hwr : ∀ n ∈ wrsH d b0, n ∉ regOuts b0)
    (hW : WOKb (declWidth m) m b0 = true)
    (ins : Nat → String → Nat) (t : Nat) (p : String → Nat) (E : Env)
    (hasg : ∀ l r, asgOf b0 l = some r → evalExpr (declWidth m) E r = some (E l))
    (hEin : ∀ x ∈ inNames m, E x = ins t x)
    (hEreg : ∀ r ∈ regOuts b0, E r = p r)
    (hEorc : ∀ mn i cs, Stmt.inst mn i cs ∈ b0 → ∀ y ∈ instOuts d mn cs, E y = Ow ins y t)
    (n n2 : Nat) (e c : Expr)
    (hrange : ∀ x ∈ refs (inl (Atab m b0) n e), E x < 2 ^ declWidth m x)
    (hc : bn (declWidth m) n2 (inl (Atab m b0) n e) = c)
    (hl0 : leafOk (cutNames d m b0) (inl (Atab m b0) n e) = true) :
    evalExpr (declWidth m) E e = evalExpr (declWidth m) (leafEnv m b0 ins t p Ow) c := by
  have hWo := WOKb_sound _ _ _ hW
  have hs := inl_sound (declWidth m) E (Atab m b0)
    (fun l r h => ⟨hasg l r (by unfold Atab at h; split at h <;> simp_all), hWo l r h⟩) n e
  have hleaf := leafOk_sound _ _ hl0
  have hb := bn_sound (declWidth m) E n2 (inl (Atab m b0) n e) hrange
  subst hc
  rw [← hs.1, ← hb.1]
  apply eval_congr
  intro x hx
  have hcut := hleaf x (refs_bn _ _ _ x hx)
  simp only [cutNames, List.mem_append] at hcut
  unfold leafEnv
  rcases hcut with (h | h) | h
  · rw [if_pos h]; exact hEin x h
  · rw [if_neg (hri x h), if_pos h]; exact hEreg x h
  · obtain ⟨mn, i, cs, hi, hy⟩ := mem_instOutsOf d b0 x h
    have hw := instOutsOf_sub_wrsH d b0 x h
    rw [if_neg (hwi x hw), if_neg (hwr x hw)]
    exact hEorc mn i cs hi x hy

end Tools.VedComposeResearch

/-! # Toy: one parent, a register, two instances of one child; accepted cone and refused controls -/

namespace Tools.VedComposeResearch.Toy

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Tools.VedU1Hier Tools.VedU2Hier Tools.VedU1Contract Tools.VedComposeResearch

def bv (n : String) : Port := ⟨n, .bitVector 4⟩

def kid : Module :=
  { name := "kid", inputs := [bv "a"], outputs := [bv "y"], wires := [], body := [] }

def dsg : Design := { topModule := "par", modules := [kid] }

def parWires : List Port := ["r", "w1", "w2", "w3", "o0", "o1", "out", "x"].map bv

/-- The parent: `r <= (o0 xor r) + o1`, where `o0 = kid(r + x)` and `o1 = kid(o0 xor r)`. -/
def par : Module :=
  { name := "par", inputs := [bv "x", ⟨"clk", .bit⟩, ⟨"rst", .bit⟩], outputs := [bv "out"], wires := parWires,
    body :=
      [ .assign "w1" (.op .add [.ref "r", .ref "x"]),
        .inst "kid" "i0" [("a", .ref "w1"), ("y", .ref "o0")],
        .assign "w2" (.op .xor [.ref "o0", .ref "r"]),
        .inst "kid" "i1" [("a", .ref "w2"), ("y", .ref "o1")],
        .assign "w3" (.op .add [.ref "w2", .ref "o1"]),
        .register "r" "clk" ("rst", .synchronous) (.ref "w3") 0,
        .assign "out" (.ref "w3") ] }

/-- The cone literal the open parent's deep run is proved about (leaves: the register, the oracle wires). -/
def coneR : Expr := .op .add [.op .xor [.ref "o0", .ref "r"], .ref "o1"]

/-! ## Accepted -/

theorem par_widths : WOKb (declWidth par) par par.body = true := by decide +kernel
theorem par_cone : inl (Atab par par.body) 6 (.ref "w3") = coneR := rfl
theorem par_leaves : leafOk (cutNames dsg par par.body) coneR = true := by decide +kernel
theorem par_out_cone : inl (Atab par par.body) 6 (.ref "w3") = coneR := rfl

theorem par_hwi : ∀ n ∈ wrsH dsg par.body, n ∉ inNames par := by decide +kernel
theorem par_hri : ∀ n ∈ regOuts par.body, n ∉ inNames par := by decide +kernel
theorem par_hwr : ∀ n ∈ wrsH dsg par.body, n ∉ regOuts par.body := by decide +kernel

/-- The register's next-value expression at an abstract environment satisfying the `step_local` facts is the cone literal at the
leaf valuation. -/
theorem par_connect (Ow : (Nat → String → Nat) → String → Nat → Nat)
    (ins : Nat → String → Nat) (t : Nat) (p : String → Nat) (E : Env)
    (hasg : ∀ l r, asgOf par.body l = some r → evalExpr (declWidth par) E r = some (E l))
    (hEin : ∀ x ∈ inNames par, E x = ins t x)
    (hEreg : ∀ r ∈ regOuts par.body, E r = p r)
    (hEorc : ∀ mn i cs, Stmt.inst mn i cs ∈ par.body → ∀ y ∈ instOuts dsg mn cs, E y = Ow ins y t) :
    evalExpr (declWidth par) E (.ref "w3")
      = evalExpr (declWidth par) (leafEnv par par.body ins t p Ow) coneR :=
  cone_connect dsg par par.body Ow par_hwi par_hri par_hwr par_widths ins t p E hasg hEin hEreg hEorc 6 _ _ par_cone
    par_leaves

/-! ## Negative controls (all refused by closed kernel evaluation) -/

/-- (1) mis-wiring: the two oracle wires swapped (instance i0 paired with i1's call). -/
def coneSwap : Expr := .op .add [.op .xor [.ref "o1", .ref "r"], .ref "o0"]
theorem ctl_swap : inl (Atab par par.body) 6 (.ref "w3") ≠ coneSwap := by
  rw [par_cone]; intro h; simp [coneR, coneSwap] at h

/-- (2) independence faking: the cone is read at a COMPUTED wire (`w2`) as if it were a free cut point.  The equation with a
too-small fuel holds, the leaf (transparency) check refuses. -/
def coneFake : Expr := .op .add [.ref "w2", .ref "o1"]
theorem ctl_fake_eq : inl (Atab par par.body) 2 (.ref "w3") = coneFake := rfl
theorem ctl_fake_leaf : leafOk (cutNames dsg par par.body) coneFake = false := by decide +kernel

/-- (3) different artifact (a): a cone of another module (`sub` for the outer `add`). -/
def coneOther : Expr := .op .sub [.op .xor [.ref "o0", .ref "r"], .ref "o1"]
theorem ctl_other : inl (Atab par par.body) 6 (.ref "w3") ≠ coneOther := by
  rw [par_cone]; intro h; simp [coneR, coneOther] at h

/-- (3b) different artifact (b): the same literal against a design in which the child has no output port `y`: the oracle
wires are no cut points. -/
def kidNoOut : Module := { kid with outputs := [] }
def dsgNoOut : Design := { topModule := "par", modules := [kidNoOut] }
theorem ctl_design : leafOk (cutNames dsgNoOut par par.body) coneR = false := by decide +kernel

/-- (4) the width side condition is real: a wire declared 4 bits wide whose right-hand side is 2 bits wide makes `WOKb`
false, and inlining it changes the value the IR semantics gives. -/
def bodyBad : List Stmt :=
  [ .assign "b" (.const 3 2), .assign "c" (.concat [.ref "a", .ref "b"]) ]
def weBad : WEnv := fun n => if n = "c" then 8 else 4
theorem ctl_width_check : WOKb weBad par bodyBad = false := by decide +kernel
def envBad : Env := fun n => if n = "a" then 5 else if n = "b" then 3 else if n = "c" then 83 else 0
/-- Both assignments HOLD in `envBad` under `weBad` (`b = 3`, `c = 5 <<< 4 ||| 3 = 83`), yet inlining changes the value of `c`
(the concatenation then reads the 2-bit constant's own width: `5 <<< 2 ||| 3 = 23`). -/
theorem ctl_width_holds_b : evalExpr weBad envBad (.const 3 2) = some (envBad "b") := by decide +kernel
theorem ctl_width_holds_c : evalExpr weBad envBad (.concat [.ref "a", .ref "b"]) = some (envBad "c") := by decide +kernel
theorem ctl_width_semantics :
    evalExpr weBad envBad (.ref "c") ≠ evalExpr weBad envBad (inl (Atab par bodyBad) 3 (.ref "c")) := by decide +kernel


/-! ## Toy 2: register bundle read through slices (the shape of the real synthesiser output) -/

def bundleWires : List Port :=
  [bv "r0", bv "r1", bv "sa", bv "sb", bv "s0", bv "n0", bv "n1", bv "o0", bv "x", ⟨"bun", .bitVector 8⟩]

/-- Registers `r0`, `r1` are read through the bundle `bun = {r0, r1}`: `s0 = bun[7:4]`, `sb = (bun[3:0])[3:0]`. -/
def parB : Module :=
  { name := "parB", inputs := [bv "x", ⟨"clk", .bit⟩, ⟨"rst", .bit⟩], outputs := [bv "out"], wires := bundleWires,
    body :=
      [ .assign "bun" (.concat [.ref "r0", .ref "r1"]),
        .assign "s0" (.slice (.ref "bun") 7 4),
        .assign "sa" (.slice (.ref "bun") 3 0),
        .assign "sb" (.slice (.ref "sa") 3 0),
        .inst "kid" "i0" [("a", .ref "sb"), ("y", .ref "o0")],
        .assign "n0" (.op .add [.ref "s0", .ref "o0"]),
        .assign "n1" (.op .add [.ref "sb", .ref "x"]),
        .register "r0" "clk" ("rst", .synchronous) (.ref "n0") 0,
        .register "r1" "clk" ("rst", .synchronous) (.ref "n1") 0,
        .assign "out" (.ref "n1") ] }

def coneB0 : Expr := .op .add [.ref "r0", .ref "o0"]
def coneB1 : Expr := .op .add [.ref "r1", .ref "x"]

theorem parB_widths : WOKb (declWidth parB) parB parB.body = true := by decide +kernel
theorem parB_c0 : bn (declWidth parB) 20 (inl (Atab parB parB.body) 20 (.ref "n0")) = coneB0 := rfl
theorem parB_c1 : bn (declWidth parB) 20 (inl (Atab parB parB.body) 20 (.ref "n1")) = coneB1 := rfl
theorem parB_l0 : leafOk (cutNames dsg parB parB.body) (inl (Atab parB parB.body) 20 (.ref "n0")) = true := by
  decide +kernel
theorem parB_l1 : leafOk (cutNames dsg parB parB.body) (inl (Atab parB parB.body) 20 (.ref "n1")) = true := by
  decide +kernel
theorem parB_hwi : ∀ n ∈ wrsH dsg parB.body, n ∉ inNames parB := by decide +kernel
theorem parB_hri : ∀ n ∈ regOuts parB.body, n ∉ inNames parB := by decide +kernel
theorem parB_hwr : ∀ n ∈ wrsH dsg parB.body, n ∉ regOuts parB.body := by decide +kernel

theorem parB_connect0 (Ow : (Nat → String → Nat) → String → Nat → Nat)
    (ins : Nat → String → Nat) (t : Nat) (p : String → Nat) (E : Env)
    (hasg : ∀ l r, asgOf parB.body l = some r → evalExpr (declWidth parB) E r = some (E l))
    (hEin : ∀ x ∈ inNames parB, E x = ins t x)
    (hEreg : ∀ r ∈ regOuts parB.body, E r = p r)
    (hEorc : ∀ mn i cs, Stmt.inst mn i cs ∈ parB.body → ∀ y ∈ instOuts dsg mn cs, E y = Ow ins y t)
    (hrange : ∀ x ∈ refs (inl (Atab parB parB.body) 20 (.ref "n0")), E x < 2 ^ declWidth parB x) :
    evalExpr (declWidth parB) E (.ref "n0")
      = evalExpr (declWidth parB) (leafEnv parB parB.body ins t p Ow) coneB0 :=
  cone_connect_bn dsg parB parB.body Ow parB_hwi parB_hri parB_hwr parB_widths ins t p E hasg hEin hEreg hEorc
    20 20 _ _ hrange parB_c0 parB_l0

/-- (5) a misaligned slice is NOT resolved: `bun[6:3]` spans two registers. -/
def parC : Module :=
  { parB with body := parB.body.map fun s => match s with
      | .assign "s0" _ => .assign "s0" (.slice (.ref "bun") 6 3)
      | s => s }
theorem ctl_misaligned : bn (declWidth parC) 20 (inl (Atab parC parC.body) 20 (.ref "n0")) ≠ coneB0 := by
  intro h
  have : bn (declWidth parC) 20 (inl (Atab parC parC.body) 20 (.ref "n0")) =
      .op .add [.slice (.concat [.ref "r0", .ref "r1"]) 6 3, .ref "o0"] := rfl
  rw [this] at h
  simp [coneB0] at h

/-- (6) the range hypothesis of `bn_sound` is real: a slice of a ref is the ref only if the value fits. -/
theorem ctl_range :
    evalExpr (fun _ => 4) (fun _ => 20) (.slice (.ref "x") 3 0) ≠ evalExpr (fun _ => 4) (fun _ => 20) (.ref "x") := by
  decide +kernel

/-! ## Clock = 1 control (P2-1): the connection applies with every needed premise discharged -/

/-- An environment with clock = 1 (`clk = 1`, `rst = 0`) satisfying every assignment of `parB` (4-bit wraparound is not hit). -/
def envC : Env := fun n => match n with
  | "x" => 2 | "clk" => 1 | "rst" => 0 | "r0" => 3 | "r1" => 5 | "bun" => 53 | "s0" => 3 | "sa" => 5 | "sb" => 5
  | "o0" => 1 | "n0" => 4 | "n1" => 7 | "out" => 7 | _ => 0

theorem envC_clock : envC "clk" = 1 := rfl

theorem envC_hasg_all : parB.body.all (fun s => match s with
    | .assign l r => evalExpr (declWidth parB) envC r == some (envC l)
    | _ => true) = true := by decide +kernel

theorem envC_hasg : ∀ l r, asgOf parB.body l = some r → evalExpr (declWidth parB) envC r = some (envC l) := by
  intro l r h
  have h3 := List.all_eq_true.mp envC_hasg_all _ (asgOf_mem h)
  simpa using h3

/-- the needed leaves of `n0` are in range at `envC` -/
theorem envC_hrange :
    ∀ x ∈ refs (inl (Atab parB parB.body) 20 (.ref "n0")), envC x < 2 ^ declWidth parB x := by decide +kernel

/-- (7) the OLD whole-`cutNames` range hypothesis is unsatisfiable at clock = 1: `clk` has declared width 0. -/
theorem ctl_clock_old_hrange : ¬ (∀ x ∈ cutNames dsg parB parB.body, envC x < 2 ^ declWidth parB x) := by
  decide +kernel

/-- **Clock = 1 control.**  The connection theorem applies at an environment with clock = 1: `hEin`, `hEreg`, `hEorc`, `hasg`
and the needed-leaf `hrange` are all discharged, no free premise remains. -/
theorem parB_connect_clock1 :
    evalExpr (declWidth parB) envC (.ref "n0")
      = evalExpr (declWidth parB) (leafEnv parB parB.body (fun _ n => envC n) 0 envC (fun _ y _ => envC y)) coneB0 := by
  refine parB_connect0 (fun _ y _ => envC y) (fun _ n => envC n) 0 envC envC envC_hasg ?_ ?_ ?_ envC_hrange
  · intro x _; rfl
  · intro r _; rfl
  · intro mn i cs _ y _; rfl

end Tools.VedComposeResearch.Toy

#print axioms Tools.VedComposeResearch.Toy.par_connect
#print axioms Tools.VedComposeResearch.Toy.ctl_swap
#print axioms Tools.VedComposeResearch.cone_connect

#print axioms Tools.VedComposeResearch.Toy.parB_connect0
#print axioms Tools.VedComposeResearch.cone_connect_bn
#print axioms Tools.VedComposeResearch.bn_sound
#print axioms Tools.VedComposeResearch.inl_sound
#print axioms Tools.VedComposeResearch.Toy.ctl_misaligned
#print axioms Tools.VedComposeResearch.Toy.ctl_range
#print axioms Tools.VedComposeResearch.Toy.parB_connect_clock1
#print axioms Tools.VedComposeResearch.Toy.ctl_clock_old_hrange
#print axioms Tools.VedComposeResearch.Toy.envC_hasg
