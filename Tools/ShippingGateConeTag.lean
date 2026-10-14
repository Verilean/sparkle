import Tools.ShippingGateDefines

/-! # The tag of a cone's instance leaf, from the gate's acceptance (worker N, round 4)

WRITTEN, NOT BUILT.

`gate_cone_runG` exposes the environment `envR` the full entry read together
with the mixed gate's acceptance of the body at `instancePredicate envR`. An
instance leaf `InstLeafK` asks `isHardwareModule envR mn = true` of its
callee. This file derives that tag from the acceptance, for ANY cone body
and ANY leaf, under one pure per-declaration fact:

    GateLeafSel kinds body leaf :=
      ∀ isInst sc, isInst leaf = false → mixedGateCond isInst kinds body sc = false

("only a predicate that designates `leaf` can make the gate accept `body`" —
the leaf twin of the built `MixedGateSel`, which is about the body itself).

* `gate_leaf_pred`: acceptance under `instancePredicate env` + `GateLeafSel`
  ⟹ `instancePredicate env leaf = true` (the text of the built `gate_pred`);
* `gate_leaf_tag` / `gate_leaf_tag'`: for a leaf `instEN mn lvls dE (poss.map
  (inputExpr n))` with `poss ≠ []` (a call on binders), the head is tagged
  (the built `instEN_pred_tag`); `'` reads the acceptance in the
  `∃ dv, …` form `gate_cone_runG` concludes with;
* `bvarCall` / `bvarCallE` / `bvarCall_sound`: a Boolean, kernel-reducible
  recogniser of one call `.const mn []` on bound variables, sound for
  equality (no `DecidableEq Expr` is needed);
* `gateLeafSel_of`: `GateLeafSel` from a CLOSED evaluation — the gate's
  condition under the predicate `fun e => !bvarCall mn is e && isInst e`
  (which refuses the leaf) is `false` for every `isInst`. By function
  extensionality this predicate IS `isInst` once `isInst leaf = false`. Per
  declaration the evaluation is kernel `rfl` after the two disjuncts that
  consult the predicate on the body itself are reduced (their spines are
  closed facts). -/
namespace Tools.ShippingGateConeTag
open Lean Sparkle.Compiler.Elab
open Tools.ShippingGateDefines (mixedGateCond mixedShape_cond instEN_pred_tag)
open Tools.ShippingInstanceEntrySoundness (instEN)
open Tools.ShippingMixedSourceBridge (inputExpr)

/-- **The leaf selection fact** (pure, per declaration): a predicate that
does not designate `leaf` makes the gate's condition on `body` false. -/
def GateLeafSel (kinds : Array MixedGateBinder) (body leaf : Lean.Expr) : Prop :=
  ∀ (isInst : Lean.Expr → Bool) (sc : Bool), isInst leaf = false →
    mixedGateCond isInst kinds body sc = false

/-- **The run's predicate designates the leaf of an accepted body.** -/
theorem gate_leaf_pred {env : Environment} {d : DefinitionVal}
    {bs : List (Name × MixedGateBinder)} {body leaf : Lean.Expr}
    (hshape : mixedCertifiedShape? false [] (.defnInfo d) (instancePredicate env) = some (bs, body))
    (hsel : GateLeafSel (bs.map (·.2)).toArray body leaf) :
    instancePredicate env leaf = true := by
  cases hb : instancePredicate env leaf with
  | true => rfl
  | false =>
    have hc := (mixedShape_cond hshape).2
    rw [hsel _ _ hb] at hc
    cases hc

/-- **The callee of an instance leaf on binders is tagged** in the
environment whose predicate the gate accepted the body under. -/
theorem gate_leaf_tag {env : Environment} {d : DefinitionVal}
    {bs : List (Name × MixedGateBinder)} {body : Lean.Expr}
    {mn : Name} {lvls : List Level} {dE : Lean.Expr} {n : Nat} {poss : List Nat}
    (hshape : mixedCertifiedShape? false [] (.defnInfo d) (instancePredicate env) = some (bs, body))
    (hne : poss ≠ [])
    (hsel : GateLeafSel (bs.map (·.2)).toArray body (instEN mn lvls dE (poss.map (inputExpr n)))) :
    Sparkle.Compiler.isHardwareModule env mn = true :=
  instEN_pred_tag hne (gate_leaf_pred hshape hsel)

/-- `gate_leaf_tag` on the acceptance as `gate_cone_runG` states it. -/
theorem gate_leaf_tag' {env : Environment}
    {bs : List (Name × MixedGateBinder)} {body : Lean.Expr}
    {mn : Name} {lvls : List Level} {dE : Lean.Expr} {n : Nat} {poss : List Nat}
    (hacc : ∃ dv : DefinitionVal,
      mixedCertifiedShape? false [] (.defnInfo dv) (instancePredicate env) = some (bs, body))
    (hne : poss ≠ [])
    (hsel : GateLeafSel (bs.map (·.2)).toArray body (instEN mn lvls dE (poss.map (inputExpr n)))) :
    Sparkle.Compiler.isHardwareModule env mn = true := by
  obtain ⟨dv, hshape⟩ := hacc
  exact gate_leaf_tag hshape hne hsel

/-! ## Discharging `GateLeafSel` by evaluation -/

/-- `.const mn []` applied to the bound variables `is`, LAST argument first
(`bvarCallE mn [i₀, i₁, i₂] = (((mn) (bvar i₂)) (bvar i₁)) (bvar i₀)`). -/
def bvarCallE (mn : Name) : List Nat → Lean.Expr
  | [] => .const mn []
  | i :: is => .app (bvarCallE mn is) (.bvar i)

/-- A kernel-reducible recogniser of `bvarCallE mn is`. -/
def bvarCall (mn : Name) : List Nat → Lean.Expr → Bool
  | [], .const n us => decide (n = mn) && us.isEmpty
  | i :: is, .app f (.bvar k) => decide (k = i) && bvarCall mn is f
  | _, _ => false

/-- The recogniser is sound for equality. -/
theorem bvarCall_sound (mn : Name) :
    ∀ (is : List Nat) (e : Lean.Expr), bvarCall mn is e = true → e = bvarCallE mn is
  | [], e, h => by
    cases e
    case const n us =>
      simp only [bvarCall, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1, h2]
      try rfl
    all_goals (first | cases h | (simp [bvarCall] at h))
  | i :: is, e, h => by
    cases e
    case app f a =>
      cases a
      case bvar k =>
        simp only [bvarCall, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨h1, h2⟩ := h
        subst h1
        rw [bvarCall_sound mn is f h2]
        try rfl
      all_goals (first | cases h | (simp [bvarCall] at h))
    all_goals (first | cases h | (simp [bvarCall] at h))

/-- **`GateLeafSel` from a closed evaluation**: under the predicate that
refuses exactly the leaf (and is `isInst` elsewhere), the gate's condition is
false. -/
theorem gateLeafSel_of {kinds : Array MixedGateBinder} {body : Lean.Expr} {mn : Name}
    {is : List Nat}
    (hc : ∀ (isInst : Lean.Expr → Bool) (sc : Bool),
      mixedGateCond (fun e => !bvarCall mn is e && isInst e) kinds body sc = false) :
    GateLeafSel kinds body (bvarCallE mn is) := by
  intro isInst sc hI
  have heq : (fun e => !bvarCall mn is e && isInst e) = isInst := by
    funext e
    show (!bvarCall mn is e && isInst e) = isInst e
    cases ht : bvarCall mn is e with
    | false => rfl
    | true =>
      have he := bvarCall_sound mn is e ht
      subst he
      rw [hI]
      try rfl
  rw [← heq]
  exact hc isInst sc

end Tools.ShippingGateConeTag
