import Tools.Prototype.DGenStored

/-! # Unit DGEN4: read-back of the remaining `StoredFromRead` fields (part 1: `Name`, `String`, `Nat` literal) -/

namespace Tools.Prototype.DGenStored2
open Lean Meta

/-- A reference to a PRIVATE core constant of `Lean/ToExpr.lean` (`Name.toExprAux` and its helpers), by its mangled name. -/
elab "priv%" s:str : term => do
  let n := Name.mkNum `_private.Lean.ToExpr 0 ++ s.getString.toName
  return Lean.mkConst n

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

/-! ## Part 3: layout, instFields, instOrigins; the shape as `dataE` builds it -/

section Part3
open Sparkle.IR.Machine Sparkle.Compiler.MachInstOrigin Tools.ShippingMachineCommand Tools.ShippingMachineAuto
open Sparkle.Compiler.Elab

def evHW : Lean.Expr → Option Sparkle.IR.Type.HWType
  | .const c _ => if c = ``Sparkle.IR.Type.HWType.bit then some .bit else none
  | .app (.const c _) w =>
    if c = ``Sparkle.IR.Type.HWType.bitVector then (evNat w).map Sparkle.IR.Type.HWType.bitVector else none
  | _ => none

def evResetKind : Lean.Expr → Option Sparkle.IR.Type.ResetKind
  | .const c _ =>
    if c = ``Sparkle.IR.Type.ResetKind.synchronous then some .synchronous
    else if c = ``Sparkle.IR.Type.ResetKind.asynchronous then some .asynchronous else none
  | _ => none

def evSlot : Lean.Expr → Option SlotField
  | .app (.app (.app (.const c _) lo) w) i =>
    if c = ``SlotField.mk then do
      let lo' ← evNat lo
      let w' ← evNat w
      let i' ← evNat i
      pure ⟨lo', w', i'⟩
    else none
  | _ => none

def evOut : Lean.Expr → Option OutField
  | .app (.app (.app (.app (.const c _) nm) lo) w) ty =>
    if c = ``OutField.mk then do
      let nm' ← evStr nm
      let lo' ← evNat lo
      let w' ← evNat w
      let ty' ← evHW ty
      pure ⟨nm', lo', w', ty'⟩
    else none
  | _ => none

def evLayout : Lean.Expr → Option Layout
  | .app (.app (.app (.app (.const c _) sl) os) rk) lets =>
    if c = ``Layout.mk then do
      let sl' ← evList evSlot sl
      let os' ← evList evOut os
      let rk' ← evResetKind rk
      let lets' ← evNat lets
      pure ⟨sl', os', rk', lets'⟩
    else none
  | _ => none

def evOrigin : Lean.Expr → Option InstOrigin
  | .const c _ => if c = ``InstOrigin.ord then some .ord else none
  | .app (.const c _) i => if c = ``InstOrigin.field then (evNat i).map InstOrigin.field else none
  | .app (.app (.app (.const c _) cb) aw) dw =>
    if c = ``InstOrigin.mem then do
      let cb' ← evBool cb
      let aw' ← evNat aw
      let dw' ← evNat dw
      pure (.mem cb' aw' dw')
    else none
  | _ => none

/-- A generic version of `evList_listE` for an encoder that can fail (`layoutE`'s `mapM`). -/
theorem evList_listE_mapM {α : Type} (ev : Lean.Expr → Option α) (f : α → Option Lean.Expr) (ty : Lean.Expr) (u : Level)
    (hf : ∀ x e, f x = some e → ev e = some x) :
    ∀ (xs : List α) (es : List Lean.Expr), xs.mapM f = some es → evList ev (listE ty es u) = some xs := by
  intro xs
  induction xs with
  | nil => intro es h; simp [List.mapM_nil, pure] at h; subst h; simp [listE, evList, Lean.mkApp, Lean.mkConst]
  | cons x xs ih =>
    intro es h
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx, bind] at h
    | some e =>
      cases hs : xs.mapM f with
      | none => simp [hx, hs, bind] at h
      | some es' =>
        simp [hx, hs, bind, pure] at h
        subst h
        show evList ev (.app (.app (.app (.const ``List.cons [u]) ty) e) (listE ty es' u)) = _
        rw [evList]
        simp [hf x e hx, ih es' hs]

theorem evHW_hwTypeE (t : Sparkle.IR.Type.HWType) (e : Lean.Expr) (h : hwTypeE t = some e) : evHW e = some t := by
  cases t <;> simp [hwTypeE] at h <;> subst h <;> simp [evHW, evNat_natL, Lean.mkApp, Lean.mkConst]

theorem evResetKind_resetKindE (k : Sparkle.IR.Type.ResetKind) : evResetKind (resetKindE k) = some k := by
  cases k <;> rfl

theorem evSlot_enc (f : SlotField) :
    evSlot (Lean.mkApp3 (Lean.mkConst ``SlotField.mk) (natL f.lo) (natL f.width) (natL f.init)) = some f := by
  cases f; simp [evSlot, Lean.mkApp3, Lean.mkApp, Lean.mkConst, evNat_natL]

theorem evOut_enc (o : OutField) (ty : Lean.Expr) (hty : hwTypeE o.ty = some ty) :
    evOut (Lean.mkApp4 (Lean.mkConst ``OutField.mk) (toExpr o.name) (natL o.lo) (natL o.width) ty) = some o := by
  rcases o with ⟨name, lo, width, t⟩
  change hwTypeE t = some ty at hty
  have := evHW_hwTypeE t ty hty
  simp [evOut, Lean.mkApp4, Lean.mkApp3, Lean.mkApp, Lean.mkConst, evNat_natL, evStr_toExpr, this]

/-- `layoutE`'s per-output encoder. -/
def outEnc (o : OutField) : Option Lean.Expr := do
  let ty ← hwTypeE o.ty
  some (Lean.mkApp4 (Lean.mkConst ``OutField.mk) (toExpr o.name) (natL o.lo) (natL o.width) ty)

/-- `layoutE` is this, definitionally (the guard that the restated pieces are the compiler's). -/
theorem layoutE_eq (l : Layout) : layoutE l = (l.outs.mapM outEnc).bind fun outs =>
    some (Lean.mkApp4 (Lean.mkConst ``Layout.mk)
      (listE (Lean.mkConst ``SlotField) (l.slots.map fun f =>
        Lean.mkApp3 (Lean.mkConst ``SlotField.mk) (natL f.lo) (natL f.width) (natL f.init)))
      (listE (Lean.mkConst ``OutField) outs) (resetKindE l.resetKind) (natL l.lets)) := rfl

theorem evLayout_app4 (a b c d : Lean.Expr) :
    evLayout (Lean.mkApp4 (Lean.mkConst ``Layout.mk) a b c d) =
      (evList evSlot a).bind fun sl => (evList evOut b).bind fun os => (evResetKind c).bind fun rk =>
        (evNat d).bind fun lets => some ⟨sl, os, rk, lets⟩ := by
  simp [evLayout, Lean.mkApp4, Lean.mkApp3, Lean.mkApp, Lean.mkConst]

theorem evLayout_layoutE (l : Layout) (e : Lean.Expr) (h : layoutE l = some e) : evLayout e = some l := by
  rw [layoutE_eq] at h
  cases hm : l.outs.mapM outEnc with
  | none => simp [hm] at h
  | some outs =>
    simp [hm] at h
    subst h
    have hsl := evList_listE evSlot (fun f : SlotField =>
      Lean.mkApp3 (Lean.mkConst ``SlotField.mk) (natL f.lo) (natL f.width) (natL f.init))
      (Lean.mkConst ``SlotField) .zero evSlot_enc l.slots
    have hos := evList_listE_mapM evOut outEnc (Lean.mkConst ``OutField) .zero ?_ l.outs outs hm
    · rw [evLayout_app4, hsl, hos, evResetKind_resetKindE, evNat_natL]
      cases l; rfl
    · intro o e he
      cases hty : hwTypeE o.ty with
      | none => simp [outEnc, hty] at he
      | some ty =>
        simp [outEnc, hty] at he
        subst he
        exact evOut_enc o ty hty

/-! ### `dataE` after the extraction of its pure builders (candidate change in `Tools/ShippingMachineCommand.lean`)

`dataE` now calls `dataPure`/`dataShapeE`/`dataPairsE`/`dataInstsE`/`dataOriginE`.  `dataEOrig` below is the text of `dataE` BEFORE that
change, verbatim (local closures); `dataE_unchanged` is the kernel check that the extraction did not change `dataE` as a function. -/

def dataEOrig (r : Read) : MetaM Lean.Expr := do
  let body ← match reflExpr r.shape.body with
    | .ok b => pure b
    | .error msg => throwError msg
  let dom ← match reflExpr r.dom with
    | .ok b => pure b
    | .error msg => throwError msg
  let some layout := layoutE r.shape.layout | throwError "an output type is not a bit vector"
  let natPairT := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Nat) (mkConst ``Nat)
  let runs := listE natPairT (r.shape.runs.map fun (a, b) =>
    mkApp4 (mkConst ``Prod.mk [.zero, .zero]) (mkConst ``Nat) (mkConst ``Nat) (natL a) (natL b))
  let instT := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Lean.Name)
    (mkApp2 (mkConst ``Prod [.zero, .zero]) (mkApp (mkConst ``List [.zero]) (mkConst ``Nat))
      (mkConst ``MixedGateBinder))
  let insts := listE instT (r.shape.insts.map fun (c, js, k) =>
    mkApp4 (mkConst ``Prod.mk [.zero, .zero]) (mkConst ``Lean.Name)
      (mkApp2 (mkConst ``Prod [.zero, .zero]) (mkApp (mkConst ``List [.zero]) (mkConst ``Nat))
        (mkConst ``MixedGateBinder))
      (toExpr c)
      (mkApp4 (mkConst ``Prod.mk [.zero, .zero]) (mkApp (mkConst ``List [.zero]) (mkConst ``Nat))
        (mkConst ``MixedGateBinder) (natListE js) (binderKindE k)))
  let loops := listE natPairT (r.shape.loops.map fun (a, b) =>
    mkApp4 (mkConst ``Prod.mk [.zero, .zero]) (mkConst ``Nat) (mkConst ``Nat) (natL a) (natL b))
  -- origin dispatch (patched compiler): `MachineShape` has an 8th field, the
  -- entries' origins; the data carries them (the closing reads them)
  let originT := mkConst ``Sparkle.Compiler.MachInstOrigin.InstOrigin
  let originE : Sparkle.Compiler.MachInstOrigin.InstOrigin → Lean.Expr
    | .ord => mkConst ``Sparkle.Compiler.MachInstOrigin.InstOrigin.ord
    | .field i => mkApp (mkConst ``Sparkle.Compiler.MachInstOrigin.InstOrigin.field) (natL i)
    | .mem cb aw dw => mkApp3 (mkConst ``Sparkle.Compiler.MachInstOrigin.InstOrigin.mem)
        (toExpr cb) (natL aw) (natL dw)
  let shape := mkAppN (mkConst ``MachineShape.mk) #[listE binderT (r.shape.binders.map binderE),
    body, layout, runs, insts, loops, listE (mkConst ``String) (r.shape.instFields.map toExpr),
    listE originT (r.shape.instOrigins.map originE)]
  return mkAppN (mkConst ``MachineData.mk)
    #[shape, natL r.nIn, dom, natListE r.bposL, natListE r.vposL, natListE r.vwL,
      listE stypeT (r.nexts.map fun t => stypeE t.1), listE anyTermT (r.ls.map anyTermE),
      listE anyTermT (r.outs.map anyTermE), termsE r.nexts]

/-- **KERNEL-CHECKED (candidate-change guard)**: the extracted `dataE` is, as a function `Read → MetaM Expr`, definitionally the
pre-extraction text `dataEOrig` (so the generated constants are unchanged for EVERY `Read`).  SCOPE: this relates `dataE` to its own
previous text; it does not say that `generateCore` stores `dataE r` (see `generateCore_mentions`, names only). -/
theorem dataE_unchanged : Tools.ShippingMachineCommand.dataE = dataEOrig := rfl

theorem evOrigin_dataOriginE (o : Sparkle.Compiler.MachInstOrigin.InstOrigin) : evOrigin (dataOriginE o) = some o := by
  cases o <;> simp [dataOriginE, evOrigin, Lean.mkApp3, Lean.mkApp, Lean.mkConst, evNat_natL, evBool_toExpr]

/-- Read-back of the `MachineShape` constructor application. -/
def evShape : Lean.Expr → Option MachineShape
  | .app (.app (.app (.app (.app (.app (.app (.app (.const c _) b1) b2) b3) b4) b5) b6) b7) b8 =>
    if c = ``MachineShape.mk then do
      let bs ← evList (evPair evName evKind) b1
      let body ← evExpr b2
      let lay ← evLayout b3
      let runs ← evList (evPair evNat evNat) b4
      let insts ← evList (evPair evName (evPair (evList evNat) evKind)) b5
      let loops ← evList (evPair evNat evNat) b6
      let iF ← evList evStr b7
      let iO ← evList evOrigin b8
      pure ⟨bs, body, lay, runs, insts, loops, iF, iO⟩
    else none
  | _ => none

/-- `dataShapeE` unfolded to the eight nested applications. -/
theorem dataShapeE_app (s : MachineShape) (body layout : Lean.Expr) :
    dataShapeE s body layout =
      .app (.app (.app (.app (.app (.app (.app (.app (Lean.mkConst ``MachineShape.mk)
        (listE binderT (s.binders.map binderE))) body) layout) (dataPairsE s.runs)) (dataInstsE s.insts))
        (dataPairsE s.loops)) (listE (Lean.mkConst ``String) (s.instFields.map toExpr)))
        (listE dataOriginT (s.instOrigins.map dataOriginE)) := rfl

/-- **PROVED**: the shape expression `dataE` builds reads back as `r.shape`, GIVEN that its two reflected pieces (`body` via
`reflExpr`, `layout` via `layoutE`) read back as `r.shape.body`/`r.shape.layout`.  `Name`/`String`/`Nat`/`List`/`Prod`/`SType`
pieces need no premise (`nameRefl`). -/
theorem evShape_dataShapeE (r : Read) (body layout : Lean.Expr)
    (hb : evExpr body = some r.shape.body) (hl : evLayout layout = some r.shape.layout) :
    evShape (dataShapeE r.shape body layout) = some r.shape := by
  have h1 := evList_binders evName nameRefl r.shape.binders
  have h4 : evList (evPair evNat evNat) (dataPairsE r.shape.runs) = some r.shape.runs := evList_runs _
  have h5 : evList (evPair evName (evPair (evList evNat) evKind)) (dataInstsE r.shape.insts) = some r.shape.insts :=
    evList_insts evName nameRefl _
  have h6 : evList (evPair evNat evNat) (dataPairsE r.shape.loops) = some r.shape.loops := evList_runs _
  have h7 := evList_listE evStr toExpr (Lean.mkConst ``String) .zero evStr_toExpr r.shape.instFields
  simp only [Lean.mkConst] at h7
  have h8 := evList_listE evOrigin dataOriginE dataOriginT .zero evOrigin_dataOriginE r.shape.instOrigins
  simp only [dataShapeE_app, Lean.mkConst, evShape, if_true, h1, hb, hl, h4, h5, h6, h7, h8]
  rfl

/-! ### The named premise per partial def, and the assembled theorem -/

/-- **PREMISE** (OPEN, one per `partial def`: `reflExpr`; `reflLevel` is only called from `reflExpr`, so it is covered by the same
statement): the compiler's `reflExpr` (a `partial def`, opaque to proofs) agrees with the structural copy `reflExprS`.  Evidence is
only the sample check `reflExpr_samples` below (a throwing meta-check on a finite list), NOT a proof. -/
def ReflExprAgree : Prop := ∀ e, reflExpr e = reflExprS e

/-- **PROVED** (from `ReflExprAgree`): what `reflExpr` builds reads back as its argument (`body` and `dom` of `dataE`). -/
theorem body_readback (hag : ReflExprAgree) (e b : Lean.Expr) (h : reflExpr e = .ok b) : evExpr b = some e :=
  evExpr_reflExprS e b (by rw [← hag e]; exact h)

/-- `ShapeDenotes e v`: the `Expr` `e` denotes the `MachineShape` `v` under the constructor-application reading `evShape` (a relation with
the declaration's `Expr` and the value as EXPLICIT arguments, in the sense of review item (a)).  What is NOT formulated in the current
implementation / not proved on this route is the link from the stored CONSTANT to such an `e`/`v` pair: that the declared value of the
constant `x.machineData` is `dataE r` and that the Lean value `d` it defines is the `v` this reading gives. -/
def ShapeDenotes (e : Lean.Expr) (v : MachineShape) : Prop := evShape e = some v

/-- **PROVED, conditional on `ReflExprAgree` and the denotation premise `hK`**: `StoredFromRead d r`.
* `hb`, `hl`: `dataE r` did not throw (its `reflExpr` of the body and its `layoutE` succeeded, with results `b`, `lay`);
* `hK` (**PREMISE (B)**: the stored `d.shape` is the denotation, under `evShape`, of the shape expression `dataE` declared it with: the
  constant-to-`Expr` link is not formulated in the current implementation and not proved on this route);
* nothing about `Name`/`String`/`Nat`/`List`/`Prod`/`SType`/`binders`/`insts`/`runs`/`loops`/`instFields`/`instOrigins`/`layout`: PROVED. -/
theorem storedFromRead_of_kernelRead (hag : ReflExprAgree) (d : MachineData) (r : Read) (b lay : Lean.Expr)
    (hb : reflExpr r.shape.body = .ok b) (hl : layoutE r.shape.layout = some lay)
    (hK : ShapeDenotes (dataShapeE r.shape b lay) d.shape) : DGenProv.StoredFromRead d r := by
  have h := evShape_dataShapeE r b lay (body_readback hag _ _ hb) (evLayout_layoutE _ _ hl)
  unfold ShapeDenotes at hK
  rw [h] at hK
  exact (Option.some.inj hK).symm

/-- The domain expression of `dataE` reads back as `r.dom` (not part of `StoredFromRead`, which is about the shape only). -/
theorem dom_readback (hag : ReflExprAgree) (r : Read) (dom : Lean.Expr) (h : reflExpr r.dom = .ok dom) :
    evExpr dom = some r.dom := body_readback hag _ _ h

end Part3

/-! ## Meta-checks (THROW at build time) -/

open Lean Meta in
/-- Sample agreement of `reflExpr` and `reflExprS` (finite evidence for `ReflExprAgree`, not a proof). -/
def reflExpr_samples : MetaM Unit := do
  let n := Lean.mkConst `Nat.add [.zero, .succ .zero]
  let samples : List Lean.Expr :=
    [.bvar 3, .const `Nat [], n, .app n (.bvar 0), .lam `x (.const `Nat []) (.bvar 0) .default,
     .lam `x (.const `Nat []) (.bvar 0) .instImplicit, .forallE `y (.sort (.succ .zero)) (.bvar 0) .implicit,
     .letE `z (.const `Nat []) (.lit (.natVal 5)) (.bvar 0) true, .lit (.natVal 7), .sort .zero,
     .lit (.strVal "s"), .mdata {} (.bvar 0), .fvar ⟨`f⟩, .sort (.param `u), .const `A [.param `u],
     .app (.lam `a.b.c (.sort (.succ .zero)) (.app (.bvar 0) (.lit (.natVal 1))) .strictImplicit) (.mdata {} (.bvar 0))]
  for e in samples do
    let a := reflExpr e
    let b := reflExprS e
    let same := match a, b with
      | .ok x, .ok y => x == y
      | .error x, .error y => x == y
      | _, _ => false
    unless same do throwError "reflExpr and reflExprS differ on {e}"

run_meta reflExpr_samples

open Lean Meta in
/-- THROWS unless `generateCore`'s code (its `_unsafe_rec`, since it is a `partial def`) mentions `dataE`, `addDef` and `readMachine`.  SCOPE: constant-name MENTIONS only; it does not check that the stored value is `dataE r`, nor the order. -/
def generateCore_mentions : MetaM Unit := do
  let ci ← getConstInfo `Tools.ShippingMachineCommand.generateCore._unsafe_rec
  let some v := ci.value? | throwError "generateCore._unsafe_rec has no value"
  for c in [``Tools.ShippingMachineCommand.dataE, ``Tools.ShippingMachineCommand.addDef,
      ``Tools.ShippingMachineCommand.readMachine] do
    unless (v.find? fun e => e.isConstOf c).isSome do
      throwError "generateCore no longer mentions {c}: the stored-data read-back may be stale"

run_meta generateCore_mentions

#print axioms nameRefl
#print axioms evExpr_reflExprS
#print axioms evLayout_layoutE
#print axioms evShape_dataShapeE
#print axioms dataE_unchanged
#print axioms body_readback
#print axioms storedFromRead_of_kernelRead

end Tools.Prototype.DGenStored2
