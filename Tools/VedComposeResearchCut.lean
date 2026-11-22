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

end Tools.VedComposeResearch
