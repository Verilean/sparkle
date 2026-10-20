import Tools.ShippingReaderComplete

/-! # The binder tables are consistent, for every binder list (G3)

`Tools.ShippingReaderComplete.kindsCfg_complete` asks `KindsOK ks`: the
`j`-th listed Bool (BitVec) position is inside the list, carries a Bool
(BitVec, of the listed width) binder, and has rank `j`. This is the converse
of `posB_rankB` / `posV_rankV` / `widV_rankV`.

Proved here for EVERY binder list (`kindsOK`), by recursion on the list with
the position offset generalised (`posB_spec`, `posV_spec`). Hence

* `kindsCfg_complete'`: the endpoints' configuration is `Complete` whenever
  the domain test accepts the domain — no condition on the binders;
* `readTerm_expr_quote'`: completeness under binders with the structural
  domain test, whose hypotheses are only `core t` and `t.WF …`.

Nothing else is claimed. -/
namespace Tools.ShippingReaderKinds
open Sparkle.Compiler.Elab
open Tools.ShippingUnifiedSource
open Tools.ShippingReaderTerm Tools.ShippingReaderInputs Tools.ShippingReaderComplete
open Tools.ShippingMixedSourceBridge (inputExpr)

/-- The `j`-th Bool position: where it is, what is there, and its rank. -/
theorem posB_spec : ∀ (ks : List MixedGateBinder) (o j : Nat), j < (posB o ks).length →
    ∃ p, (posB o ks)[j]? = some (o + p) ∧ p < ks.length ∧
      ks[p]? = some MixedGateBinder.bool ∧ rankB ks p = j
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | .bool :: _, _, 0, _ => ⟨0, rfl, Nat.succ_pos _, rfl, rfl⟩
  | .bool :: r, o, j + 1, h => by
    obtain ⟨p, h1, h2, h3, h4⟩ := posB_spec r (o + 1) j (Nat.lt_of_succ_lt_succ h)
    exact ⟨p + 1, h1.trans (congrArg some (by omega)), Nat.succ_lt_succ h2, h3,
      congrArg (fun x => x + 1) h4⟩
  | .domain :: r, o, j, h => by
    obtain ⟨p, h1, h2, h3, h4⟩ := posB_spec r (o + 1) j h
    exact ⟨p + 1, h1.trans (congrArg some (by omega)), Nat.succ_lt_succ h2, h3, h4⟩
  | .bits _ :: r, o, j, h => by
    obtain ⟨p, h1, h2, h3, h4⟩ := posB_spec r (o + 1) j h
    exact ⟨p + 1, h1.trans (congrArg some (by omega)), Nat.succ_lt_succ h2, h3, h4⟩

/-- The `j`-th BitVec position: where it is, its width, and its rank. -/
theorem posV_spec : ∀ (ks : List MixedGateBinder) (o j : Nat), j < (posV o ks).length →
    ∃ p, (posV o ks)[j]? = some (o + p) ∧ p < ks.length ∧
      ∃ w, ks[p]? = some (MixedGateBinder.bits w) ∧ (widV ks)[j]? = some w ∧ rankV ks p = j
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | .bits w :: _, _, 0, _ => ⟨0, rfl, Nat.succ_pos _, w, rfl, rfl, rfl⟩
  | .bits _ :: r, o, j + 1, h => by
    obtain ⟨p, h1, h2, w, h3, h4, h5⟩ := posV_spec r (o + 1) j (Nat.lt_of_succ_lt_succ h)
    exact ⟨p + 1, h1.trans (congrArg some (by omega)), Nat.succ_lt_succ h2, w, h3, h4,
      congrArg (fun x => x + 1) h5⟩
  | .bool :: r, o, j, h => by
    obtain ⟨p, h1, h2, w, h3, h4, h5⟩ := posV_spec r (o + 1) j h
    exact ⟨p + 1, h1.trans (congrArg some (by omega)), Nat.succ_lt_succ h2, w, h3, h4, h5⟩
  | .domain :: r, o, j, h => by
    obtain ⟨p, h1, h2, w, h3, h4, h5⟩ := posV_spec r (o + 1) j h
    exact ⟨p + 1, h1.trans (congrArg some (by omega)), Nat.succ_lt_succ h2, w, h3, h4, h5⟩

/-- **Every binder list is consistent with its tables.** -/
theorem kindsOK (ks : List MixedGateBinder) : KindsOK ks where
  boolAt := fun j hj => by
    obtain ⟨p, h1, h2, h3, h4⟩ := posB_spec ks 0 j hj
    have e : (posB 0 ks).getD j 0 = p :=
      (Eq.trans List.getD_eq_getElem?_getD
        (congrArg (fun (o : Option Nat) => o.getD 0) h1)).trans (Nat.zero_add p)
    rw [e]
    exact ⟨h2, h3, h4⟩
  bitsAt := fun j hj _ => by
    obtain ⟨p, h1, h2, w, h3, h4, h5⟩ := posV_spec ks 0 j hj
    have e : (posV 0 ks).getD j 0 = p :=
      (Eq.trans List.getD_eq_getElem?_getD
        (congrArg (fun (o : Option Nat) => o.getD 0) h1)).trans (Nat.zero_add p)
    have ew : (widV ks).getD j 0 = w :=
      Eq.trans List.getD_eq_getElem?_getD (congrArg (fun (o : Option Nat) => o.getD 0) h4)
    rw [e, ew]
    exact ⟨h2, h3, h5⟩

/-- The endpoints' configuration is complete: no condition on the binders. -/
theorem kindsCfg_complete' (dom : Lean.Expr) (isDom : Lean.Expr → Bool)
    (hdom : isDom dom = true) (ks : List MixedGateBinder) :
    Complete (kindsCfg dom isDom ks) :=
  kindsCfg_complete dom isDom hdom ks (kindsOK ks)

/-- **Completeness under binders**, with the structural domain test: for
every binder list and every well-formed core term. -/
theorem readTerm_expr_quote' (dom : Lean.Expr) (ks : List MixedGateBinder)
    {s : SType} (t : Term s) (ht : core t)
    (hw : t.WF (posB 0 ks).length (posV 0 ks).length (fun j => (widV ks).getD j 0)) :
    readTerm (kindsCfg dom (isExpr dom) ks)
      (quote dom (fun j => inputExpr ks.length ((posB 0 ks).getD j 0))
        (fun j => inputExpr ks.length ((posV 0 ks).getD j 0)) t) = some ⟨s, t⟩ :=
  readTerm_expr_quote dom ks (kindsOK ks) t ht hw

end Tools.ShippingReaderKinds
