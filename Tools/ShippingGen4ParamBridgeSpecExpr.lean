import Tools.ShippingGen4ParamBridgeCompose
set_option autoImplicit false
-- NOT BUILT: implementation of scripts/gen4/PARAMETRIC_BRIDGE_UNIT5_FREEZE.md §2 (F2, approved freeze d49d342a). Awaiting clean issue-linked build.

/-! # M4 parametric, bridge unit 5 (F2: model-level lift of D1 to whole expressions) (scripts/gen4/PARAMETRIC_BRIDGE_UNIT5_FREEZE.md §2)

`specExprM` is a total model copied from the text of `specializeExpr` (Specialize.lean:71-93), clause by clause; the production
`arguments.mapM (specializeExpr bindings)` is modelled by the mutual list function. `evalM` replaces `DimExpr.evaluate`
(B1 NOT claimed). It is NOT claimed equal to `specializeExpr` (that is B3, unsupplied). Nothing here is a production I5b supply,
discharges T, changes FG, or adds a law / TRUSTED boundary. B1-B4, T, FG remain unsupplied. -/

namespace Tools.ShippingGen4ParamBridgeSpecExpr
open Sparkle.IR.Type Sparkle.IR.AST Tools.ShippingGen4ParamLayerA Tools.ShippingGen4ParamBridgeShape Tools.ShippingGen4ParamBridgeCompose

mutual
def specExprM (θ : Binding) : Expr → Except String Expr
  | .const value width => .ok (.const value width)
  | .ref name => .ok (.ref name)
  | .op operator arguments => (specExprsM θ arguments).bind fun a => .ok (.op operator a)
  | .concat arguments => (specExprsM θ arguments).bind fun a => .ok (.concat a)
  | .slice expression hi lo => (specExprM θ expression).bind fun e => .ok (.slice e hi lo)
  | .sliceDim expression hi lo =>
      (evalM θ hi).bind fun concreteHi =>
        (evalM θ lo).bind fun concreteLo =>
          if concreteHi < concreteLo then
            .error s!"invalid specialized slice [{concreteHi}:{concreteLo}]: high bound is below low bound"
          else (specExprM θ expression).bind fun e => .ok (.slice e concreteHi concreteLo)
  | .index array index =>
      (specExprM θ array).bind fun a => (specExprM θ index).bind fun i => .ok (.index a i)
def specExprsM (θ : Binding) : List Expr → Except String (List Expr)
  | [] => .ok []
  | e :: es => (specExprM θ e).bind fun e' => (specExprsM θ es).bind fun es' => .ok (e' :: es')
end

mutual
def ExprOK (θ : Binding) : Expr → Prop
  | .const _ _ => True
  | .ref _ => True
  | .op _ arguments => ExprsOK θ arguments
  | .concat arguments => ExprsOK θ arguments
  | .slice expression _ _ => ExprOK θ expression
  | .sliceDim expression hi lo => SliceOK hi lo ∧ Bound θ hi ∧ Bound θ lo ∧ ExprOK θ expression
  | .index array index => ExprOK θ array ∧ ExprOK θ index
def ExprsOK (θ : Binding) : List Expr → Prop
  | [] => True
  | e :: es => ExprOK θ e ∧ ExprsOK θ es
end

mutual
def NoDim : Expr → Prop
  | .const _ _ => True
  | .ref _ => True
  | .op _ arguments => NoDims arguments
  | .concat arguments => NoDims arguments
  | .slice expression _ _ => NoDim expression
  | .sliceDim .. => False
  | .index array index => NoDim array ∧ NoDim index
def NoDims : List Expr → Prop
  | [] => True
  | e :: es => NoDim e ∧ NoDims es
end

mutual
theorem specExprM_ok_aux {θ : Binding} (ha : AllPos θ) : (e : Expr) → ExprOK θ e → ∃ e', specExprM θ e = .ok e'
  | .const v w, _ => ⟨_, rfl⟩
  | .ref n, _ => ⟨_, rfl⟩
  | .op o args, h => by
      obtain ⟨a, hx⟩ := specExprsM_ok_aux ha args h
      exact ⟨.op o a, by simp [specExprM, hx, Except.bind]⟩
  | .concat args, h => by
      obtain ⟨a, hx⟩ := specExprsM_ok_aux ha args h
      exact ⟨.concat a, by simp [specExprM, hx, Except.bind]⟩
  | .slice e hi lo, h => by
      obtain ⟨a, hx⟩ := specExprM_ok_aux ha e h
      exact ⟨.slice a hi lo, by simp [specExprM, hx, Except.bind]⟩
  | .sliceDim e hi lo, h => by
      obtain ⟨hs, hbh, hbl, he⟩ := h
      obtain ⟨h', l', e1, e2, hle⟩ := sliceOK_order hs ⟨hbh, hbl⟩ ha
      obtain ⟨a, hx⟩ := specExprM_ok_aux ha e he
      have hn : ¬ h' < l' := by omega
      exact ⟨.slice a h' l', by simp [specExprM, e1, e2, hn, hx, Except.bind]⟩
  | .index x y, h => by
      obtain ⟨a, hx⟩ := specExprM_ok_aux ha x h.1
      obtain ⟨b, hy⟩ := specExprM_ok_aux ha y h.2
      exact ⟨.index a b, by simp [specExprM, hx, hy, Except.bind]⟩
theorem specExprsM_ok_aux {θ : Binding} (ha : AllPos θ) : (es : List Expr) → ExprsOK θ es → ∃ es', specExprsM θ es = .ok es'
  | [], _ => ⟨_, rfl⟩
  | e :: es, h => by
      obtain ⟨a, hx⟩ := specExprM_ok_aux ha e h.1
      obtain ⟨b, hy⟩ := specExprsM_ok_aux ha es h.2
      exact ⟨a :: b, by simp [specExprsM, hx, hy, Except.bind]⟩
end

mutual
theorem specExprM_noDim_aux (θ : Binding) : (e : Expr) → ∀ e', specExprM θ e = .ok e' → NoDim e'
  | .const v w, e', h => by simp [specExprM] at h; subst h; trivial
  | .ref n, e', h => by simp [specExprM] at h; subst h; trivial
  | .op o args, e', h => by
      simp only [specExprM] at h
      cases hx : specExprsM θ args with
      | error _ => simp [hx, Except.bind] at h
      | ok a =>
        simp [hx, Except.bind] at h; subst h
        exact specExprsM_noDim_aux θ args a hx
  | .concat args, e', h => by
      simp only [specExprM] at h
      cases hx : specExprsM θ args with
      | error _ => simp [hx, Except.bind] at h
      | ok a =>
        simp [hx, Except.bind] at h; subst h
        exact specExprsM_noDim_aux θ args a hx
  | .slice e hi lo, e', h => by
      simp only [specExprM] at h
      cases hx : specExprM θ e with
      | error _ => simp [hx, Except.bind] at h
      | ok a =>
        simp [hx, Except.bind] at h; subst h
        exact specExprM_noDim_aux θ e a hx
  | .sliceDim e hi lo, e', h => by
      simp only [specExprM] at h
      cases h1 : evalM θ hi with
      | error _ => simp [h1, Except.bind] at h
      | ok x =>
        cases h2 : evalM θ lo with
        | error _ => simp [h1, h2, Except.bind] at h
        | ok y =>
          by_cases hlt : x < y
          · simp [h1, h2, hlt, Except.bind] at h
          · cases hx : specExprM θ e with
            | error _ => simp [h1, h2, hlt, hx, Except.bind] at h
            | ok a =>
              simp [h1, h2, hlt, hx, Except.bind] at h; subst h
              exact specExprM_noDim_aux θ e a hx
  | .index x y, e', h => by
      simp only [specExprM] at h
      cases hx : specExprM θ x with
      | error _ => simp [hx, Except.bind] at h
      | ok a =>
        cases hy : specExprM θ y with
        | error _ => simp [hx, hy, Except.bind] at h
        | ok b =>
          simp [hx, hy, Except.bind] at h; subst h
          exact ⟨specExprM_noDim_aux θ x a hx, specExprM_noDim_aux θ y b hy⟩
theorem specExprsM_noDim_aux (θ : Binding) : (es : List Expr) → ∀ es', specExprsM θ es = .ok es' → NoDims es'
  | [], es', h => by simp [specExprsM] at h; subst h; trivial
  | e :: es, es', h => by
      simp only [specExprsM] at h
      cases hx : specExprM θ e with
      | error _ => simp [hx, Except.bind] at h
      | ok a =>
        cases hy : specExprsM θ es with
        | error _ => simp [hx, hy, Except.bind] at h
        | ok b =>
          simp [hx, hy, Except.bind] at h; subst h
          exact ⟨specExprM_noDim_aux θ e a hx, specExprsM_noDim_aux θ es b hy⟩
end

-- F2a
theorem specExprM_ok {θ : Binding} {e : Expr} (hok : ExprOK θ e) (ha : AllPos θ) :
    ∃ e', specExprM θ e = .ok e' :=
  specExprM_ok_aux ha e hok

-- F2b
theorem specExprM_noDim {θ : Binding} {e e' : Expr} (h : specExprM θ e = .ok e') : NoDim e' :=
  specExprM_noDim_aux θ e e' h

-- F2c
theorem specExprM_startLength {θ : Binding} {src : Expr} {s l : DimExpr}
    (hs : NonNegDim s) (hl : PosDim l) (hb : Bound θ s ∧ Bound θ l) (ha : AllPos θ) (hsrc : ExprOK θ src) :
    ∃ e', specExprM θ (Sparkle.Compiler.Elab.makeSliceFromStartLength src s l) = .ok e' := by
  obtain ⟨a, hx⟩ := specExprM_ok hsrc ha
  rcases startLength_node_ordered (src := src) hs hl hb ha with ⟨hn, h', l', e1, e2, hle⟩ | ⟨a', b', hn, e1, e2, hle⟩
  · rw [hn]
    have hn' : ¬ h' < l' := by omega
    exact ⟨.slice a h' l', by simp [specExprM, e1, e2, hn', hx, Except.bind]⟩
  · rw [hn]
    exact ⟨.slice a a' b', by simp [specExprM, hx, Except.bind]⟩

end Tools.ShippingGen4ParamBridgeSpecExpr
