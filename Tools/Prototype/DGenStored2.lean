import Tools.Prototype.DGenStored

/-! # Unit DGEN4: read-back of the remaining `StoredFromRead` fields (part 1: `Name`, `String`, `Nat` literal) -/

namespace Tools.Prototype.DGenStored2
open Lean Meta Elab Term

/-- A reference to a PRIVATE core constant of `Lean/ToExpr.lean` (`Name.toExprAux` and its helpers), by its mangled name. -/
elab "priv%" s:str : term => do
  let n := Name.mkNum `_private.Lean.ToExpr 0 ++ s.getString.toName
  return mkConst n

def evStr : Lean.Expr → Option String
  | .lit (.strVal s) => some s
  | _ => none

/-- Read-back of `toExpr : Nat → Expr` (`mkNatLit n = OfNat.ofNat Nat n (instOfNatNat n)`). -/
def evNatLit : Lean.Expr → Option Nat
  | .app (.app (.app (.const c _) (.const t _)) (.lit (.natVal n))) (.app (.const i _) (.lit (.natVal m))) =>
    if c = ``OfNat.ofNat ∧ t = ``Nat ∧ i = ``instOfNatNat ∧ n = m then some n else none
  | _ => none

def evSpine : Lean.Expr → Option (Name × List String)
  | .const c _ => some (c, [])
  | .app f (.lit (.strVal s)) => (evSpine f).map fun (c, l) => (c, l ++ [s])
  | _ => none

def ofStrs (l : List String) : Name := l.foldl Name.str .anonymous

def mkStrName (k : Nat) : Name := Name.str ``Lean.Name ("mkStr" ++ toString k)

def evMkStr (e : Lean.Expr) : Option Name := do
  let (c, l) ← evSpine e
  if c = mkStrName l.length ∧ 1 ≤ l.length ∧ l.length ≤ 8 then some (ofStrs l) else none

/-- Read-back of core's `toExpr : Name → Expr`: `Name.anonymous`, `Name.str`, `Name.num`, and the `Name.mkStr1 … mkStr8` shortcuts. -/
def evName : Lean.Expr → Option Name
  | .const c _ => if c = ``Lean.Name.anonymous then some .anonymous else none
  | e@(.app (.app (.const c _) p) s) =>
    if c = ``Lean.Name.str then do
      let p' ← evName p
      let s' ← evStr s
      some (Name.str p' s')
    else if c = ``Lean.Name.num then do
      let p' ← evName p
      let k ← evNatLit s
      some (Name.num p' k)
    else evMkStr e
  | e@(.app _ _) => evMkStr e
  | _ => none

theorem evStr_toExpr (s : String) : evStr (toExpr s) = some s := rfl

theorem evNatLit_toExpr (n : Nat) : evNatLit (toExpr n) = some n := by
  simp [toExpr, mkNatLit, mkNatLitCore, mkRawNatLit, evNatLit, Lean.mkApp3, Lean.mkApp, Lean.mkConst, mkAppB, mkLit, mkInstOfNatNat]

/-! ### `go` (the general case) -/

theorem evName_go (n : Name) : evName ((priv% "Lean.Name.toExprAux.go") n) = some n := by
  induction n with
  | anonymous => rfl
  | str p s ih =>
    show evName (mkApp2 (mkConst ``Lean.Name.str) ((priv% "Lean.Name.toExprAux.go") p) (toExpr s)) = _
    simp [Lean.mkApp2, Lean.mkApp, Lean.mkConst, evName, ih, evStr_toExpr]
  | num p k ih =>
    show evName (mkApp2 (mkConst ``Lean.Name.num) ((priv% "Lean.Name.toExprAux.go") p) (toExpr k)) = _
    simp [Lean.mkApp2, Lean.mkApp, Lean.mkConst, evName, ih, evNatLit_toExpr]

/-! ### the `mkStrK` shortcut -/

def strsOf : Name → List String
  | .str p s => strsOf p ++ [s]
  | _ => []

theorem mkStr_spec (n : Name) :
    ∀ (sz : Nat) (args : Array Lean.Expr), (priv% "Lean.Name.toExprAux.isSimple") n sz = true →
      (priv% "Lean.Name.toExprAux.mkStr") n sz args =
        ((strsOf n).map toExpr ++ args.toList.reverse).foldl Lean.mkApp
          (Lean.mkConst (mkStrName (sz + (strsOf n).length))) := by
  induction n with
  | anonymous =>
    intro sz args _
    show mkAppN _ _ = _
    simp [mkAppN, strsOf, Array.foldl_toList, Array.toList_reverse, mkStrName]
  | str p s ih =>
    intro sz args h
    have h' : (priv% "Lean.Name.toExprAux.isSimple") p (sz + 1) = true := h
    show (priv% "Lean.Name.toExprAux.mkStr") p (sz + 1) (args.push (toExpr s)) = _
    rw [ih _ _ h']
    have : sz + 1 + (strsOf p).length = sz + (strsOf (Name.str p s)).length := by
      simp [strsOf]; omega
    rw [this]
    simp [strsOf, Array.toList_push]
  | num p k ih => intro sz args h; cases h

theorem ofStrs_strsOf (n : Name) :
    ∀ sz, (priv% "Lean.Name.toExprAux.isSimple") n sz = true →
      ofStrs (strsOf n) = n ∧ 0 < sz + (strsOf n).length ∧ sz + (strsOf n).length ≤ 8 := by
  induction n with
  | anonymous =>
    intro sz h
    have h' : (decide (0 < sz) && decide (sz ≤ 8)) = true := h
    simp at h'
    simp [ofStrs, strsOf]; omega
  | str p s ih =>
    intro sz h
    have h' : (priv% "Lean.Name.toExprAux.isSimple") p (sz + 1) = true := h
    obtain ⟨h1, h2, h3⟩ := ih _ h'
    refine ⟨?_, ?_, ?_⟩
    · simp [strsOf, ofStrs] at h1 ⊢; rw [h1]
    · simp [strsOf]; omega
    · simp [strsOf]; omega
  | num p k ih => intro sz h; cases h

theorem evSpine_foldl (xs : List String) :
    ∀ (e : Lean.Expr) (c : Name) (l : List String), evSpine e = some (c, l) →
      evSpine ((xs.map toExpr).foldl Lean.mkApp e) = some (c, l ++ xs) := by
  induction xs with
  | nil => intro e c l h; simpa using h
  | cons x xs ih =>
    intro e c l h
    have : evSpine (Lean.mkApp e (toExpr x)) = some (c, l ++ [x]) := by
      simp [Lean.mkApp, toExpr, mkStrLit, evSpine, h]
    simpa using ih _ c _ this

theorem evName_mkStrK (xs : List String) (h1 : 1 ≤ xs.length) (h8 : xs.length ≤ 8) :
    evName ((xs.map toExpr).foldl Lean.mkApp (Lean.mkConst (mkStrName xs.length))) = some (ofStrs xs) := by
  match xs, h1, h8 with
  | [a], _, _ => simp [evName, evMkStr, evSpine, ofStrs, mkStrName, toExpr, mkStrLit, Lean.mkApp, Lean.mkConst] <;> first | done | decide
  | [a, b], _, _ => simp [evName, evMkStr, evSpine, ofStrs, mkStrName, toExpr, mkStrLit, Lean.mkApp, Lean.mkConst] <;> first | done | decide
  | [a, b, c], _, _ => simp [evName, evMkStr, evSpine, ofStrs, mkStrName, toExpr, mkStrLit, Lean.mkApp, Lean.mkConst] <;> first | done | decide
  | [a, b, c, d], _, _ => simp [evName, evMkStr, evSpine, ofStrs, mkStrName, toExpr, mkStrLit, Lean.mkApp, Lean.mkConst] <;> first | done | decide
  | [a, b, c, d, e], _, _ => simp [evName, evMkStr, evSpine, ofStrs, mkStrName, toExpr, mkStrLit, Lean.mkApp, Lean.mkConst] <;> first | done | decide
  | [a, b, c, d, e, f], _, _ => simp [evName, evMkStr, evSpine, ofStrs, mkStrName, toExpr, mkStrLit, Lean.mkApp, Lean.mkConst] <;> first | done | decide
  | [a, b, c, d, e, f, g], _, _ => simp [evName, evMkStr, evSpine, ofStrs, mkStrName, toExpr, mkStrLit, Lean.mkApp, Lean.mkConst] <;> first | done | decide
  | [a, b, c, d, e, f, g, h], _, _ => simp [evName, evMkStr, evSpine, ofStrs, mkStrName, toExpr, mkStrLit, Lean.mkApp, Lean.mkConst] <;> first | done | decide

/-- **PROVED**: core's `toExpr : Name → Expr` (private `Name.toExprAux`, `Name.mkStr1..8` shortcuts and `go`) reads back as the name. -/
theorem nameRefl : DGenStored.NameRefl evName := by
  intro n
  have e1 : toExpr n = if (priv% "Lean.Name.toExprAux.isSimple") n 0 = true then
      (priv% "Lean.Name.toExprAux.mkStr") n 0 #[] else (priv% "Lean.Name.toExprAux.go") n := rfl
  rw [e1]
  by_cases h : (priv% "Lean.Name.toExprAux.isSimple") n 0 = true
  · rw [if_pos h, mkStr_spec n 0 #[] h]
    obtain ⟨h1, h2, h3⟩ := ofStrs_strsOf n 0 h
    have := evName_mkStrK (strsOf n) (by omega) (by omega)
    simp only [Nat.zero_add, Array.toList_empty, List.reverse_nil, List.append_nil]
    rw [this, h1]
  · rw [if_neg h]
    exact evName_go n

/-! ## Part 2: `reflExpr` (a `partial def`) — a structural total copy, and the read-back of what it builds -/

open Tools.ShippingEntrySoundness Tools.Prototype.DGenStored

def evBool : Lean.Expr → Option Bool
  | .const c _ => if c = ``Bool.true then some true else if c = ``Bool.false then some false else none
  | _ => none

theorem evBool_toExpr (b : Bool) : evBool (toExpr b) = some b := by cases b <;> rfl

def evLevel : Lean.Expr → Option Level
  | .const c _ => if c = ``Lean.Level.zero then some .zero else none
  | .app (.const c _) l => if c = ``Lean.Level.succ then (evLevel l).map Level.succ else none
  | _ => none

def evBinderInfo : Lean.Expr → Option BinderInfo
  | .const c _ =>
    if c = ``Lean.BinderInfo.default then some .default
    else if c = ``Lean.BinderInfo.implicit then some .implicit
    else if c = ``Lean.BinderInfo.strictImplicit then some .strictImplicit
    else if c = ``Lean.BinderInfo.instImplicit then some .instImplicit else none
  | _ => none

/-- Read-back of the `Expr`-of-`Expr` that `reflExpr` builds: the forms `reflExpr` supports. -/
def evExpr : Lean.Expr → Option Lean.Expr
  | .app (.const c _) x =>
    if c = ``Lean.Expr.bvar then (evNatLit x).map Lean.Expr.bvar
    else if c = ``Lean.Expr.sort then (evLevel x).map Lean.Expr.sort
    else if c = ``Lean.Expr.lit then
      (match x with
        | .app (.const l _) k => if l = ``Lean.Literal.natVal then (evNatLit k).map fun k => Lean.Expr.lit (.natVal k) else none
        | _ => none)
    else none
  | .app (.app (.const c _) x) y =>
    if c = ``Lean.Expr.app then do
      let f ← evExpr x
      let a ← evExpr y
      pure (Lean.Expr.app f a)
    else if c = ``Lean.Expr.const then do
      let n ← evName x
      let ls ← evList evLevel y
      pure (Lean.Expr.const n ls)
    else none
  | .app (.app (.app (.app (.const c _) n) t) b) bi =>
    if c = ``Lean.Expr.lam then do
      let n' ← evName n
      let t' ← evExpr t
      let b' ← evExpr b
      let bi' ← evBinderInfo bi
      pure (Lean.Expr.lam n' t' b' bi')
    else if c = ``Lean.Expr.forallE then do
      let n' ← evName n
      let t' ← evExpr t
      let b' ← evExpr b
      let bi' ← evBinderInfo bi
      pure (Lean.Expr.forallE n' t' b' bi')
    else none
  | .app (.app (.app (.app (.app (.const c _) n) t) v) b) nd =>
    if c = ``Lean.Expr.letE then do
      let n' ← evName n
      let t' ← evExpr t
      let v' ← evExpr v
      let b' ← evExpr b
      let nd' ← evBool nd
      pure (Lean.Expr.letE n' t' v' b' nd')
    else none
  | _ => none

/-- A structural total copy of `reflLevel` (a `partial def`, opaque to proofs). -/
def reflLevelS : Level → Except String Lean.Expr
  | .zero => pure (mkConst ``Level.zero)
  | .succ l => return mkApp (mkConst ``Level.succ) (← reflLevelS l)
  | l => throw s!"level {l} not supported"

/-- A structural total copy of `reflExpr` (a `partial def`, opaque to proofs: no equation lemma).  Same cases, same order. -/
def reflExprS : Lean.Expr → Except String Lean.Expr
  | .bvar i => pure (mkApp (mkConst ``Lean.Expr.bvar) (toExpr i))
  | .const n ls => do
    let ls ← ls.mapM reflLevelS
    return mkApp2 (mkConst ``Lean.Expr.const) (toExpr n) (← pure (ls.foldr
      (fun l acc => mkApp3 (mkConst ``List.cons [.zero]) (mkConst ``Level) l acc)
      (mkApp (mkConst ``List.nil [.zero]) (mkConst ``Level))))
  | .app f a => return mkApp2 (mkConst ``Lean.Expr.app) (← reflExprS f) (← reflExprS a)
  | .lam n t b bi => do
    let rt ← reflExprS t
    let rb ← reflExprS b
    return mkApp4 (mkConst ``Lean.Expr.lam) (toExpr n) rt rb (reflBinderInfo bi)
  | .forallE n t b bi => do
    let rt ← reflExprS t
    let rb ← reflExprS b
    return mkApp4 (mkConst ``Lean.Expr.forallE) (toExpr n) rt rb (reflBinderInfo bi)
  | .lit (.natVal k) =>
    pure (mkApp (mkConst ``Lean.Expr.lit) (mkApp (mkConst ``Literal.natVal) (toExpr k)))
  | .sort l => do
    return mkApp (mkConst ``Lean.Expr.sort) (← reflLevelS l)
  | .letE n t v b nd => do
    let rt ← reflExprS t
    let rv ← reflExprS v
    let rb ← reflExprS b
    return mkApp5 (mkConst ``Lean.Expr.letE) (toExpr n) rt rv rb (toExpr nd)
  | e => throw s!"unsupported expression form {e}"

theorem evBinderInfo_reflBinderInfo (bi : BinderInfo) : evBinderInfo (reflBinderInfo bi) = some bi := by
  cases bi <;> rfl

theorem evLevel_reflLevelS (l : Level) : ∀ b, reflLevelS l = .ok b → evLevel b = some l := by
  induction l with
  | zero => intro b h; simp [reflLevelS, pure, Except.pure] at h; subst h; rfl
  | succ l ih =>
    intro b h
    cases hl : reflLevelS l with
    | error m => simp [reflLevelS, hl, bind, Except.bind] at h
    | ok x =>
      simp [reflLevelS, hl, bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [evLevel, Lean.mkApp, Lean.mkConst, ih x hl]
  | max a b _ _ => intro b h; simp [reflLevelS] at h
  | imax a b _ _ => intro b h; simp [reflLevelS] at h
  | param n => intro b h; simp [reflLevelS] at h
  | mvar n => intro b h; simp [reflLevelS] at h

theorem mapM_cons_ok {α β : Type} (f : α → Except String β) (a : α) (tl : List α) (ys : List β)
    (h : (a :: tl).mapM f = .ok ys) : ∃ y ys', f a = .ok y ∧ tl.mapM f = .ok ys' ∧ ys = y :: ys' := by
  rw [List.mapM_cons] at h
  cases ha : f a with
  | error m => simp [ha, bind, Except.bind] at h
  | ok y =>
    cases hs : tl.mapM f with
    | error m => simp [ha, hs, bind, Except.bind] at h
    | ok ys' =>
      simp [ha, hs, bind, Except.bind, pure, Except.pure] at h
      exact ⟨y, ys', rfl, rfl, h.symm⟩

def levelListE (xs : List Lean.Expr) : Lean.Expr :=
  xs.foldr (fun l acc => Lean.mkApp3 (Lean.mkConst ``List.cons [.zero]) (Lean.mkConst ``Level) l acc)
    (Lean.mkApp (Lean.mkConst ``List.nil [.zero]) (Lean.mkConst ``Level))

theorem evList_levels (ls : List Level) : ∀ xs, ls.mapM reflLevelS = .ok xs →
    evList evLevel (levelListE xs) = some ls := by
  induction ls with
  | nil =>
    intro xs h
    simp [List.mapM_nil, pure, Except.pure] at h
    subst h
    rfl
  | cons l ls ih =>
    intro xs h
    obtain ⟨y, ys, hy, hs, rfl⟩ := mapM_cons_ok _ _ _ _ h
    have e : levelListE (y :: ys) =
        Lean.mkApp3 (Lean.mkConst ``List.cons [.zero]) (Lean.mkConst ``Level) y (levelListE ys) := rfl
    have := ih ys hs
    rw [e]
    simp [evList, Lean.mkApp3, Lean.mkApp, Lean.mkConst, evLevel_reflLevelS l y hy, this]

theorem evExpr_reflExprS (e : Lean.Expr) : ∀ b, reflExprS e = .ok b → evExpr b = some e := by
  induction e with
  | bvar i =>
    intro b h
    simp [reflExprS, pure, Except.pure] at h
    subst h
    simp [evExpr, Lean.mkApp, Lean.mkConst, evNatLit_toExpr]
  | fvar _ => intro b h; simp [reflExprS] at h
  | mvar _ => intro b h; simp [reflExprS] at h
  | sort l =>
    intro b h
    cases hl : reflLevelS l with
    | error m => simp [reflExprS, hl, bind, Except.bind] at h
    | ok x =>
      simp [reflExprS, hl, bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [evExpr, Lean.mkApp, Lean.mkConst, evLevel_reflLevelS l x hl]
  | const n ls =>
    intro b h
    cases hl : ls.mapM reflLevelS with
    | error m => simp [reflExprS, hl, bind, Except.bind] at h
    | ok xs =>
      simp [reflExprS, hl, bind, Except.bind, pure, Except.pure] at h
      subst h
      have := evList_levels ls xs hl
      show evExpr (Lean.mkApp2 (Lean.mkConst ``Lean.Expr.const) (toExpr n) (levelListE xs)) = _
      simp [evExpr, Lean.mkApp2, Lean.mkApp, Lean.mkConst, nameRefl n, this]
  | app f a ihf iha =>
    intro b h
    cases hf : reflExprS f with
    | error m => simp [reflExprS, hf, bind, Except.bind] at h
    | ok x =>
      cases ha : reflExprS a with
      | error m => simp [reflExprS, hf, ha, bind, Except.bind] at h
      | ok y =>
        simp [reflExprS, hf, ha, bind, Except.bind, pure, Except.pure] at h
        subst h
        simp [evExpr, Lean.mkApp2, Lean.mkApp, Lean.mkConst, ihf x hf, iha y ha]
  | lam n t body bi iht ihb =>
    intro b h
    cases ht : reflExprS t with
    | error m => simp [reflExprS, ht, bind, Except.bind] at h
    | ok x =>
      cases hb : reflExprS body with
      | error m => simp [reflExprS, ht, hb, bind, Except.bind] at h
      | ok y =>
        simp [reflExprS, ht, hb, bind, Except.bind, pure, Except.pure] at h
        subst h
        simp [evExpr, Lean.mkApp4, Lean.mkApp3, Lean.mkApp2, Lean.mkApp, Lean.mkConst, iht x ht, ihb y hb,
          nameRefl n, evBinderInfo_reflBinderInfo]
  | forallE n t body bi iht ihb =>
    intro b h
    cases ht : reflExprS t with
    | error m => simp [reflExprS, ht, bind, Except.bind] at h
    | ok x =>
      cases hb : reflExprS body with
      | error m => simp [reflExprS, ht, hb, bind, Except.bind] at h
      | ok y =>
        simp [reflExprS, ht, hb, bind, Except.bind, pure, Except.pure] at h
        subst h
        simp [evExpr, Lean.mkApp4, Lean.mkApp3, Lean.mkApp2, Lean.mkApp, Lean.mkConst, iht x ht, ihb y hb,
          nameRefl n, evBinderInfo_reflBinderInfo]
  | letE n t v body nd iht ihv ihb =>
    intro b h
    cases ht : reflExprS t with
    | error m => simp [reflExprS, ht, bind, Except.bind] at h
    | ok x =>
      cases hv : reflExprS v with
      | error m => simp [reflExprS, ht, hv, bind, Except.bind] at h
      | ok z =>
        cases hb : reflExprS body with
        | error m => simp [reflExprS, ht, hv, hb, bind, Except.bind] at h
        | ok y =>
          simp [reflExprS, ht, hv, hb, bind, Except.bind, pure, Except.pure] at h
          subst h
          simp [evExpr, Lean.mkApp5, Lean.mkApp4, Lean.mkApp3, Lean.mkApp2, Lean.mkApp, Lean.mkConst, iht x ht,
            ihv z hv, ihb y hb, nameRefl n, evBool_toExpr]
  | lit l =>
    intro b h
    cases l with
    | natVal k =>
      simp [reflExprS, pure, Except.pure] at h
      subst h
      simp [evExpr, Lean.mkApp, Lean.mkConst, evNatLit_toExpr]
    | strVal _ => simp [reflExprS] at h
  | mdata _ _ _ => intro b h; simp [reflExprS] at h
  | proj _ _ _ _ => intro b h; simp [reflExprS] at h

end Tools.Prototype.DGenStored2
