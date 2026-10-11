import Tools.ShippingReaderTerm
import Tools.ShippingMixedSourceBridge

/-! # The reader's leaf tables, from a transition's binder kinds (G3)

`Tools.ShippingReaderTerm.readTerm_sound` is stated over a configuration
`Cfg` whose leaf tables satisfy the contract `Cfg.Sound`. This file builds
the configuration the machine endpoints use and PROVES its contract, so the
contract is not a premise of the instantiated theorem:

* inputs are numbered as `Tools.ShippingMachineAuto.MachineData` numbers
  them — Bool input `j` is the `j`-th Bool binder, BitVec input `j` the
  `j`-th BitVec binder — and written `inputExpr count position` (the reverse
  de Bruijn index of the binder);
* `posB` / `posV` / `widV`: the positions of the Bool binders, of the BitVec
  binders, and the BitVec widths, in binder order; `rankB` / `rankV`: the
  number of a binder among its sort;
* `posB_rankB`, `posV_rankV`, `widV_rankV`: a binder's rank selects its own
  position (and width) — for every binder list;
* `kindsCfg_sound`: the configuration's contract, from a sound domain test;
* `isBVar_sound`, `isConst_dom`: the two domain tests the machine route
  needs (`machDom?` returns a bound variable or the constant
  `defaultDomain`); `isExpr_sound`: the test for ANY domain expression, by
  the compiler's structural `exprDecEq`;
* `readTerm_kinds_sound`, `readTerm_kinds_exists`: reader soundness in the
  endpoints' vocabulary, with the domain test's soundness as its only
  premise; `readTerm_expr_sound`: the same with the structural test — no
  premise besides the reading.

What is NOT proved here: that `posB 0 kinds` is the list the endpoint
generator computes (`readMachine`: a `filterMap` over the indexed kinds).
They are the same list; the generator should use these definitions, or the
equality be proved (an induction on the binder list). -/
namespace Tools.ShippingReaderInputs
open Sparkle.Compiler.Elab
open Tools.ShippingUnifiedSource Tools.ShippingReaderTerm
open Tools.ShippingMixedSourceBridge (inputExpr)

/-! ## Positions and ranks -/

/-- The positions of the Bool binders, counted from `o`. -/
def posB : Nat → List MixedGateBinder → List Nat
  | _, [] => []
  | o, .bool :: r => o :: posB (o + 1) r
  | o, .domain :: r => posB (o + 1) r
  | o, .bits _ :: r => posB (o + 1) r

/-- The number of Bool binders before position `p`. -/
def rankB : List MixedGateBinder → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | .bool :: r, p + 1 => rankB r p + 1
  | .domain :: r, p + 1 => rankB r p
  | .bits _ :: r, p + 1 => rankB r p

/-- A Bool binder's rank selects its position. -/
theorem posB_rankB : ∀ (ks : List MixedGateBinder) (o p : Nat),
    ks[p]? = some MixedGateBinder.bool → (posB o ks)[rankB ks p]? = some (o + p)
  | [], _, _, h => none_ne h
  | .bool :: _, _, 0, _ => rfl
  | .bool :: r, o, p + 1, h => by
    have h' : r[p]? = some MixedGateBinder.bool := h
    have ih := posB_rankB r (o + 1) p h'
    show (posB (o + 1) r)[rankB r p]? = some (o + (p + 1))
    rw [ih]
    exact congrArg some (by omega)
  | .domain :: _, _, 0, h => by
    have h' : some MixedGateBinder.domain = some MixedGateBinder.bool := h
    cases h'
  | .domain :: r, o, p + 1, h => by
    have h' : r[p]? = some MixedGateBinder.bool := h
    have ih := posB_rankB r (o + 1) p h'
    show (posB (o + 1) r)[rankB r p]? = some (o + (p + 1))
    rw [ih]
    exact congrArg some (by omega)
  | .bits w' :: _, _, 0, h => by
    have h' : some (MixedGateBinder.bits w') = some MixedGateBinder.bool := h
    cases h'
  | .bits _ :: r, o, p + 1, h => by
    have h' : r[p]? = some MixedGateBinder.bool := h
    have ih := posB_rankB r (o + 1) p h'
    show (posB (o + 1) r)[rankB r p]? = some (o + (p + 1))
    rw [ih]
    exact congrArg some (by omega)

/-- The positions of the BitVec binders, counted from `o`. -/
def posV : Nat → List MixedGateBinder → List Nat
  | _, [] => []
  | o, .bits _ :: r => o :: posV (o + 1) r
  | o, .bool :: r => posV (o + 1) r
  | o, .domain :: r => posV (o + 1) r

/-- The widths of the BitVec binders, in order. -/
def widV : List MixedGateBinder → List Nat
  | [] => []
  | .bits w :: r => w :: widV r
  | .bool :: r => widV r
  | .domain :: r => widV r

/-- The number of BitVec binders before position `p`. -/
def rankV : List MixedGateBinder → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | .bits _ :: r, p + 1 => rankV r p + 1
  | .bool :: r, p + 1 => rankV r p
  | .domain :: r, p + 1 => rankV r p

/-- A BitVec binder's rank selects its position. -/
theorem posV_rankV : ∀ (ks : List MixedGateBinder) (o p w : Nat),
    ks[p]? = some (MixedGateBinder.bits w) → (posV o ks)[rankV ks p]? = some (o + p)
  | [], _, _, _, h => none_ne h
  | .bits _ :: _, _, 0, _, _ => rfl
  | .bits _ :: r, o, p + 1, w, h => by
    have h' : r[p]? = some (MixedGateBinder.bits w) := h
    have ih := posV_rankV r (o + 1) p w h'
    show (posV (o + 1) r)[rankV r p]? = some (o + (p + 1))
    rw [ih]
    exact congrArg some (by omega)
  | .bool :: _, _, 0, w, h => by
    have h' : some MixedGateBinder.bool = some (MixedGateBinder.bits w) := h
    cases h'
  | .bool :: r, o, p + 1, w, h => by
    have h' : r[p]? = some (MixedGateBinder.bits w) := h
    have ih := posV_rankV r (o + 1) p w h'
    show (posV (o + 1) r)[rankV r p]? = some (o + (p + 1))
    rw [ih]
    exact congrArg some (by omega)
  | .domain :: _, _, 0, w, h => by
    have h' : some MixedGateBinder.domain = some (MixedGateBinder.bits w) := h
    cases h'
  | .domain :: r, o, p + 1, w, h => by
    have h' : r[p]? = some (MixedGateBinder.bits w) := h
    have ih := posV_rankV r (o + 1) p w h'
    show (posV (o + 1) r)[rankV r p]? = some (o + (p + 1))
    rw [ih]
    exact congrArg some (by omega)

/-- A BitVec binder's rank selects its width. -/
theorem widV_rankV : ∀ (ks : List MixedGateBinder) (p w : Nat),
    ks[p]? = some (MixedGateBinder.bits w) → (widV ks)[rankV ks p]? = some w
  | [], _, _, h => none_ne h
  | .bits w' :: _, 0, w, h => by
    have h' : some (MixedGateBinder.bits w') = some (MixedGateBinder.bits w) := h
    cases h'
    rfl
  | .bits _ :: r, p + 1, w, h => by
    have h' : r[p]? = some (MixedGateBinder.bits w) := h
    exact widV_rankV r p w h'
  | .bool :: _, 0, w, h => by
    have h' : some MixedGateBinder.bool = some (MixedGateBinder.bits w) := h
    cases h'
  | .bool :: r, p + 1, w, h => by
    have h' : r[p]? = some (MixedGateBinder.bits w) := h
    exact widV_rankV r p w h'
  | .domain :: _, 0, w, h => by
    have h' : some MixedGateBinder.domain = some (MixedGateBinder.bits w) := h
    cases h'
  | .domain :: r, p + 1, w, h => by
    have h' : r[p]? = some (MixedGateBinder.bits w) := h
    exact widV_rankV r p w h'

/-! ## The leaf tables -/

/-- The Bool input a loose bound variable is: the binder it refers to is a
Bool binder; its number is the binder's rank. -/
def inBoolOf (ks : List MixedGateBinder) (i : Nat) : Option Nat :=
  if i < ks.length then
    if ks[ks.length - 1 - i]? = some MixedGateBinder.bool then
      some (rankB ks (ks.length - 1 - i))
    else none
  else none

theorem inBoolOf_sound (ks : List MixedGateBinder) (i j : Nat)
    (h : inBoolOf ks i = some j) :
    inputExpr ks.length ((posB 0 ks).getD j 0) = .bvar i ∧ j < (posB 0 ks).length := by
  unfold inBoolOf at h
  split at h
  · rename_i hi
    split at h
    · rename_i hk
      cases h
      have hp := posB_rankB ks 0 _ hk
      rw [Nat.zero_add] at hp
      have e1 : (posB 0 ks).getD (rankB ks (ks.length - 1 - i)) 0 = ks.length - 1 - i :=
        Eq.trans List.getD_eq_getElem?_getD
          (congrArg (fun (o : Option Nat) => o.getD 0) hp)
      refine ⟨?_, (List.getElem?_eq_some_iff.mp hp).1⟩
      show Lean.Expr.bvar
        (ks.length - 1 - (posB 0 ks).getD (rankB ks (ks.length - 1 - i)) 0) = .bvar i
      rw [e1]
      exact congrArg Lean.Expr.bvar (by omega)
    · cases h
  · cases h

/-- The width of a BitVec binder. -/
def kindWidth? : Option MixedGateBinder → Option Nat
  | some (.bits w) => some w
  | _ => none

theorem kindWidth?_sound {k : Option MixedGateBinder} {w : Nat}
    (h : kindWidth? k = some w) : k = some (MixedGateBinder.bits w) := by
  revert h
  unfold kindWidth?
  split
  · intro h
    cases h
    rfl
  · intro h; cases h

/-- The BitVec input a loose bound variable is, with its width (positive). -/
def inBitsOf (ks : List MixedGateBinder) (i : Nat) : Option (Nat × Nat) :=
  if i < ks.length then
    (kindWidth? (ks[ks.length - 1 - i]?)).bind fun w =>
      if 0 < w then some (w, rankV ks (ks.length - 1 - i)) else none
  else none

theorem inBitsOf_sound (ks : List MixedGateBinder) (i w j : Nat)
    (h : inBitsOf ks i = some (w, j)) :
    inputExpr ks.length ((posV 0 ks).getD j 0) = .bvar i ∧ j < (posV 0 ks).length ∧
      (widV ks).getD j 0 = w ∧ 0 < w := by
  unfold inBitsOf at h
  split at h
  · rename_i hi
    obtain ⟨w', hk, hb1⟩ := Option.bind_eq_some_iff.mp h
    split at hb1
    · rename_i hw
      cases hb1
      have hk' := kindWidth?_sound hk
      have hp := posV_rankV ks 0 _ _ hk'
      rw [Nat.zero_add] at hp
      have hwd := widV_rankV ks _ _ hk'
      have e1 : (posV 0 ks).getD (rankV ks (ks.length - 1 - i)) 0 = ks.length - 1 - i :=
        Eq.trans List.getD_eq_getElem?_getD
          (congrArg (fun (o : Option Nat) => o.getD 0) hp)
      refine ⟨?_, (List.getElem?_eq_some_iff.mp hp).1,
        Eq.trans List.getD_eq_getElem?_getD
          (congrArg (fun (o : Option Nat) => o.getD 0) hwd), hw⟩
      show Lean.Expr.bvar
        (ks.length - 1 - (posV 0 ks).getD (rankV ks (ks.length - 1 - i)) 0) = .bvar i
      rw [e1]
      exact congrArg Lean.Expr.bvar (by omega)
    · cases hb1
  · cases h

/-! ## Domain tests -/

/-- The domain is the bound variable `k` (a declaration with a domain
binder). -/
def isBVar (k : Nat) : Lean.Expr → Bool
  | .bvar i => decide (i = k)
  | _ => false

theorem isBVar_sound (k : Nat) : ∀ d, isBVar k d = true → d = .bvar k := by
  intro d h
  revert h
  unfold isBVar
  split
  · intro h
    exact congrArg Lean.Expr.bvar (of_decide_eq_true h)
  · intro h; cases h

/-- The domain is the closed constant `n` (a declaration at a fixed domain). -/
theorem isConst_dom (n : Lean.Name) : ∀ d, isConst n d = true → d = .const n [] :=
  fun _ h => isConst_sound h

/-- Any domain expression: the structural decision of equality the compiler
already has (`Sparkle.Compiler.ExprDecEq.exprDecEq`, standard axioms). -/
def isExpr (dom d : Lean.Expr) : Bool :=
  @decide (d = dom) (Sparkle.Compiler.ExprDecEq.exprDecEq d dom)

theorem isExpr_sound (dom : Lean.Expr) : ∀ d, isExpr dom d = true → d = dom :=
  fun d h => @of_decide_eq_true (d = dom) (Sparkle.Compiler.ExprDecEq.exprDecEq d dom) h

/-! ## The configuration -/

/-- The reader's configuration for a body under binders of kinds `ks`. -/
def kindsCfg (dom : Lean.Expr) (isDom : Lean.Expr → Bool) (ks : List MixedGateBinder) :
    Cfg where
  dom := dom
  bools := fun j => inputExpr ks.length ((posB 0 ks).getD j 0)
  bits := fun j => inputExpr ks.length ((posV 0 ks).getD j 0)
  isDom := isDom
  inBool := inBoolOf ks
  inBits := inBitsOf ks
  kb := (posB 0 ks).length
  kv := (posV 0 ks).length
  vw := fun j => (widV ks).getD j 0

theorem kindsCfg_sound (dom : Lean.Expr) (isDom : Lean.Expr → Bool)
    (hdom : ∀ d, isDom d = true → d = dom) (ks : List MixedGateBinder) :
    (kindsCfg dom isDom ks).Sound where
  domEq := hdom
  boolIn := fun i j h => inBoolOf_sound ks i j h
  bitsIn := fun i w j h => inBitsOf_sound ks i w j h

/-- **Reader soundness under binders.** For every binder list, domain
expression with a sound test, and expression: if the reader returns a term,
the expression is the term's quotation at the binders' input expressions,
and the term is well formed for the binders' counts and widths. -/
theorem readTerm_kinds_sound (dom : Lean.Expr) (isDom : Lean.Expr → Bool)
    (hdom : ∀ d, isDom d = true → d = dom) (ks : List MixedGateBinder)
    (e : Lean.Expr) (r : AnyTerm) (h : readTerm (kindsCfg dom isDom ks) e = some r) :
    quote dom (fun j => inputExpr ks.length ((posB 0 ks).getD j 0))
        (fun j => inputExpr ks.length ((posV 0 ks).getD j 0)) r.2 = e ∧
      r.2.WF (posB 0 ks).length (posV 0 ks).length (fun j => (widV ks).getD j 0) :=
  readTerm_sound (kindsCfg dom isDom ks) (kindsCfg_sound dom isDom hdom ks) e r h

/-- **Reader soundness, no premise.** With the structural domain test: for
every domain expression, binder list and expression, a term the reader
returns quotes back to the expression and is well formed. -/
theorem readTerm_expr_sound (dom : Lean.Expr) (ks : List MixedGateBinder)
    (e : Lean.Expr) (r : AnyTerm) (h : readTerm (kindsCfg dom (isExpr dom) ks) e = some r) :
    quote dom (fun j => inputExpr ks.length ((posB 0 ks).getD j 0))
        (fun j => inputExpr ks.length ((posV 0 ks).getD j 0)) r.2 = e ∧
      r.2.WF (posB 0 ks).length (posV 0 ks).length (fun j => (widV ks).getD j 0) :=
  readTerm_kinds_sound dom (isExpr dom) (isExpr_sound dom) ks e r h

/-- The form a check run by the compiler would give: acceptance by the
reader alone yields a well-formed term whose quotation is the expression. -/
theorem readTerm_kinds_exists (dom : Lean.Expr) (isDom : Lean.Expr → Bool)
    (hdom : ∀ d, isDom d = true → d = dom) (ks : List MixedGateBinder)
    (e : Lean.Expr) (h : (readTerm (kindsCfg dom isDom ks) e).isSome = true) :
    ∃ r : AnyTerm,
      quote dom (fun j => inputExpr ks.length ((posB 0 ks).getD j 0))
        (fun j => inputExpr ks.length ((posV 0 ks).getD j 0)) r.2 = e ∧
      r.2.WF (posB 0 ks).length (posV 0 ks).length (fun j => (widV ks).getD j 0) := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h
  exact ⟨r, readTerm_kinds_sound dom isDom hdom ks e r hr⟩

end Tools.ShippingReaderInputs
