import Tools.Prototype.DGenProv

/-! # Unit DGEN3: what can be proved about `StoredFromRead` (the reflection `dataE` of a `Read` into a closed constant)

BUILT (unit DGEN3): g1 exit 1 (namespace/`as` keyword), g2 exit 1 (cons case), g3 `build Tools.Prototype.DGenStored` exit 0. No sorry/axiom/native_decide; axioms of the lemmas: propext, Classical.choice, Quot.sound.

`dataE r : MetaM Lean.Expr` builds the CONSTRUCTOR-APPLICATION term of `MachineData` that `generateCore` stores with `addDef`.
`StoredFromRead d r := d.shape = r.shape` asks that the Lean VALUE `d` of that constant be `r`'s shape.  Two different steps:

* (A) the `Expr` built from `r.f` DENOTES `r.f`: an evaluator `ev : Lean.Expr → Option α` that reads back a constructor-application
  `Expr`, applied to the builder's output, returns `some (r.f)`.  This is a statement about pure Lean functions; PROVED here for the
  builders that are structural definitions (`natL`, `listE`, `natListE`, `stypeE`, `binderKindE`, `binderE`, the `runs`/`loops`/`insts`
  pairs).
* (B) the Lean value of a constant whose declared value is the constructor-application `Expr` `e` is `ev e` — i.e. the KERNEL reads a
  constructor application as that constructor application.  This is not a statement of the logic (a Lean term cannot talk about the
  `Expr` that is its own declared value), so it is NOT proved and not stated as a Lean `Prop`; it is the one meta-fact the stored
  constant needs, stated in the REPORT per type (Nat raw literal, List.cons/nil, Prod.mk, the constructors of `SType`/`MixedGateBinder`;
  and for `Name`/`String` the core `ToExpr` instances).

NOT covered (OPEN, with the reason): `shape.body` and `dom` go through `reflExpr`, a `partial def` (opaque to proofs: no equation lemma);
`Name` (`instToExprName`: private `Name.toExprAux`, `Name.mkStrN` constants) and `String` (`mkStrLit`) are kept as the named
hypothesis `NameRefl`; `layout` and the `Term`s (`termE`, 20 constructors) are not done here. -/

namespace Tools.Prototype.DGenStored
open Lean Sparkle.Compiler.Elab Tools.ShippingMachineCommand Tools.ShippingMachineAuto Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.Prototype.DGenProv

/-! ## Read-back of constructor applications -/

def evNat : Lean.Expr → Option Nat
  | .lit (.natVal n) => some n
  | _ => none

def evList {α : Type} (ev : Lean.Expr → Option α) : Lean.Expr → Option (List α)
  | .app (.app (.app (.const n _) _) x) xs =>
    if n = ``List.cons then do
      let a ← ev x
      let rest ← evList ev xs
      pure (a :: rest)
    else none
  | .app (.const n _) _ => if n = ``List.nil then some [] else none
  | _ => none

def evPair {α β : Type} (eva : Lean.Expr → Option α) (evb : Lean.Expr → Option β) : Lean.Expr → Option (α × β)
  | .app (.app (.app (.app (.const n _) _) _) a) b =>
    if n = ``Prod.mk then do
      let x ← eva a
      let y ← evb b
      pure (x, y)
    else none
  | _ => none

def evSType : Lean.Expr → Option SType
  | .const n _ => if n = ``SType.bool then some .bool else none
  | .app (.const n _) w => if n = ``SType.bits then (evNat w).map SType.bits else none
  | _ => none

def evKind : Lean.Expr → Option MixedGateBinder
  | .const n _ =>
    if n = ``MixedGateBinder.domain then some .domain
    else if n = ``MixedGateBinder.bool then some .bool else none
  | .app (.const n _) w => if n = ``MixedGateBinder.bits then (evNat w).map MixedGateBinder.bits else none
  | _ => none

/-! ## (A) the builders denote their argument -/

theorem evNat_natL (n : Nat) : evNat (natL n) = some n := rfl

theorem evList_listE {α : Type} (ev : Lean.Expr → Option α) (enc : α → Lean.Expr) (ty : Lean.Expr) (u : Level)
    (hev : ∀ x, ev (enc x) = some x) (xs : List α) :
    evList ev (listE ty (xs.map enc) u) = some xs := by
  induction xs with
  | nil => simp [listE, evList, mkApp, mkConst]
  | cons x xs ih =>
    show evList ev (.app (.app (.app (.const ``List.cons [u]) ty) (enc x)) (listE ty (xs.map enc) u)) = _
    rw [evList]
    simp [hev, ih]

theorem evList_natListE (xs : List Nat) : evList evNat (natListE xs) = some xs := by
  unfold natListE
  exact evList_listE evNat natL _ _ evNat_natL xs

theorem evSType_stypeE (s : SType) : evSType (stypeE s) = some s := by
  cases s <;> simp [stypeE, evSType, evNat_natL, mkApp, mkConst]

theorem evKind_binderKindE (k : MixedGateBinder) : evKind (binderKindE k) = some k := by
  cases k <;> simp [binderKindE, evKind, evNat_natL, mkApp, mkConst]

theorem evPair_mk {α β : Type} (eva : Lean.Expr → Option α) (evb : Lean.Expr → Option β)
    (ta tb : Lean.Expr) (us : List Level) (a : α) (b : β) (ea eb : Lean.Expr)
    (ha : eva ea = some a) (hb : evb eb = some b) :
    evPair eva evb (mkApp4 (mkConst ``Prod.mk us) ta tb ea eb) = some (a, b) := by
  simp [mkApp4, evPair, mkConst, ha, hb]

/-- The ONE `Name` fact: the core `instToExprName` read back (a statement about core's `ToExpr Name` instance; `String` likewise via
`mkStrLit`).  A premise, per type, not proved here. -/
def NameRefl (evName : Lean.Expr → Option Name) : Prop := ∀ n : Name, evName (toExpr n) = some n

/-- `shape.runs` and `shape.loops` (the lists of `(Nat × Nat)` as `dataE` builds them). -/
theorem evList_runs (xs : List (Nat × Nat)) :
    evList (evPair evNat evNat)
      (listE (mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Nat) (mkConst ``Nat))
        (xs.map fun (a, b) =>
          mkApp4 (mkConst ``Prod.mk [.zero, .zero]) (mkConst ``Nat) (mkConst ``Nat) (natL a) (natL b))) =
      some xs := by
  refine evList_listE (evPair evNat evNat) (fun p : Nat × Nat =>
    mkApp4 (mkConst ``Prod.mk [.zero, .zero]) (mkConst ``Nat) (mkConst ``Nat) (natL p.1) (natL p.2))
    _ _ ?_ xs
  intro p
  exact evPair_mk _ _ _ _ _ _ _ _ _ (evNat_natL _) (evNat_natL _)

/-- `shape.binders` (`binderE` per entry), given the `Name` fact. -/
theorem evList_binders (evName : Lean.Expr → Option Name) (hN : NameRefl evName)
    (xs : List (Name × MixedGateBinder)) :
    evList (evPair evName evKind) (listE binderT (xs.map binderE)) = some xs := by
  refine evList_listE (evPair evName evKind) binderE _ _ ?_ xs
  intro b
  exact evPair_mk _ _ _ _ _ _ _ _ _ (hN b.1) (evKind_binderKindE b.2)

/-- `shape.insts` entries `(callee, argument lets, result kind)` as `dataE` builds them. -/
theorem evList_insts (evName : Lean.Expr → Option Name) (hN : NameRefl evName)
    (xs : List (Name × List Nat × MixedGateBinder)) :
    evList (evPair evName (evPair (evList evNat) evKind))
      (listE (mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Lean.Name)
          (mkApp2 (mkConst ``Prod [.zero, .zero]) (mkApp (mkConst ``List [.zero]) (mkConst ``Nat))
            (mkConst ``MixedGateBinder)))
        (xs.map fun (c, js, k) =>
          mkApp4 (mkConst ``Prod.mk [.zero, .zero]) (mkConst ``Lean.Name)
            (mkApp2 (mkConst ``Prod [.zero, .zero]) (mkApp (mkConst ``List [.zero]) (mkConst ``Nat))
              (mkConst ``MixedGateBinder))
            (toExpr c)
            (mkApp4 (mkConst ``Prod.mk [.zero, .zero]) (mkApp (mkConst ``List [.zero]) (mkConst ``Nat))
              (mkConst ``MixedGateBinder) (natListE js) (binderKindE k)))) = some xs := by
  refine evList_listE (evPair evName (evPair (evList evNat) evKind))
    (fun p : Name × List Nat × MixedGateBinder =>
      mkApp4 (mkConst ``Prod.mk [.zero, .zero]) (mkConst ``Lean.Name)
        (mkApp2 (mkConst ``Prod [.zero, .zero]) (mkApp (mkConst ``List [.zero]) (mkConst ``Nat))
          (mkConst ``MixedGateBinder))
        (toExpr p.1)
        (mkApp4 (mkConst ``Prod.mk [.zero, .zero]) (mkApp (mkConst ``List [.zero]) (mkConst ``Nat))
          (mkConst ``MixedGateBinder) (natListE p.2.1) (binderKindE p.2.2))) _ _ ?_ xs
  intro p
  exact evPair_mk _ _ _ _ _ _ _ _ _ (hN p.1)
    (evPair_mk _ _ _ _ _ _ _ _ _ (evList_natListE _) (evKind_binderKindE _))

/-! ## `StoredFromRead` splits field by field -/

/-- `StoredFromRead` is exactly the eight field equalities of `MachineShape`. -/
theorem storedFromRead_iff (d : MachineData) (r : Read) :
    StoredFromRead d r ↔
      (d.shape.binders = r.shape.binders ∧ d.shape.body = r.shape.body ∧ d.shape.layout = r.shape.layout ∧
        d.shape.runs = r.shape.runs ∧ d.shape.insts = r.shape.insts ∧ d.shape.loops = r.shape.loops ∧
        d.shape.instFields = r.shape.instFields ∧ d.shape.instOrigins = r.shape.instOrigins) := by
  unfold StoredFromRead
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    cases hd : d.shape; cases hr : r.shape
    rw [hd, hr] at h1 h2 h3 h4 h5 h6 h7 h8
    simp only at h1 h2 h3 h4 h5 h6 h7 h8
    subst h1 h2 h3 h4 h5 h6 h7 h8
    rfl

#print axioms evList_listE
#print axioms evList_natListE
#print axioms evList_runs
#print axioms evList_binders
#print axioms evList_insts
#print axioms storedFromRead_iff

end Tools.Prototype.DGenStored
