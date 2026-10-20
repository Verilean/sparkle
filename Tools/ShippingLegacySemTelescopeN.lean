import Tools.ShippingLegacySemEntryList

/-! # The Meta-library fact about `lambdaTelescope`, for `n` binders

`LamTelescopeOne` (`Tools/ShippingLegacySemEntryOne.lean`) states what
`lambdaTelescope` does on a one-binder lambda. Here: on `n` nested lambdas.

**Defined here**

* `lams sp b` — `fun (n₁ : d₁) … (nₖ : dₖ) => b` for the binder list
  `sp = [(n₁, d₁, bi₁), …]` (types and body with loose bound variables, as in
  the constant's value).
* `DeclsOpen mctx sp ids fvars` — the variables `ids` are declared in `mctx`,
  the `j`-th with user name `nⱼ` and type
  `dⱼ.instantiateRevRange 0 fvars.size fvars`, where `fvars` is the array of
  the variables opened before it (extended by `push`, as
  `lambdaTelescopeImp.process` does; `src/lean/Lean/Meta/Basic.lean`,
  v4.32.1, lines 1598–1628).
* `LamTelescopeN` — THE META-LIBRARY FACT: for every binder list `sp` and
  every body `b` that is not a lambda, a successful run of
  `lambdaTelescope (lams sp b) k` is a successful run, in a context `mctx`,
  of `k fvars (b.instantiateRevRange 0 fvars.size fvars)` with
  `fvars = (ids.map .fvar).toArray` for some variables `ids` with
  `DeclsOpen mctx sp ids #[]`. No compiler definition in it. Not provable
  (`lambdaTelescopeImp` is `private partial`).
  Two remarks on its exact form: (1) the final array is written
  `(ids.map .fvar).toArray`, while the code builds it by `push` — the same
  array; (2) that each variable is still FOUND in the final local context
  (`find?`) uses that the fresh variables are distinct — part of the fact.
  `LamTelescopeOne` is its instance at one binder up to those two forms.

**Proved here**: `telescopeIn_of_lam2` — the hand-over `ListScope` for a
declaration with TWO scalar binders, from `LamTelescopeN` and the body's
shape (`body = fun (n₁ : T₁) (n₂ : T₂) => b`, `b` not a lambda, the three
instantiations). The list of variables the fact returns is unknown; its
length is forced to two by `DeclsOpen`. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness

/-- Nested lambdas over a body. -/
def lams : List (Name × Lean.Expr × BinderInfo) → Lean.Expr → Lean.Expr
  | [], b => b
  | (n, d, bi) :: sp, b => Lean.Expr.lam n d (lams sp b) bi

/-- The declarations `lambdaTelescope` installs for the binders `sp`, the
variables `fvars` being already opened. -/
def DeclsOpen (mctx : Meta.Context) :
    List (Name × Lean.Expr × BinderInfo) → List FVarId → Array Lean.Expr → Prop
  | [], [], _ => True
  | (n, d, _) :: sp, id :: ids, fvars =>
    (∃ d0 : LocalDecl, mctx.lctx.find? id = some d0 ∧ d0.userName = n ∧
      d0.type = d.instantiateRevRange 0 fvars.size fvars) ∧
    DeclsOpen mctx sp ids (fvars.push (Lean.Expr.fvar id))
  | _, _, _ => False

/-- **The Meta-library fact about `lambdaTelescope`, for `n` binders.** -/
def LamTelescopeN : Prop :=
  ∀ (sp : List (Name × Lean.Expr × BinderInfo)) (b : Lean.Expr), b.isLambda = false →
  ∀ (α : Type) (k : Array Lean.Expr → Lean.Expr → MetaM α) (r : α),
    MReturns (Lean.Meta.lambdaTelescope (lams sp b) k) r →
    ∃ (mctx : Meta.Context) (ids : List FVarId),
      DeclsOpen mctx sp ids #[] ∧
      MRunsIn (k (ids.map Lean.Expr.fvar).toArray
        (b.instantiateRevRange 0 (ids.map Lean.Expr.fvar).toArray.size
          (ids.map Lean.Expr.fvar).toArray)) mctx r

/-- The array of the first variable, as the telescope builds it. -/
abbrev fv1 (id1 : FVarId) : Array Lean.Expr := (#[] : Array Lean.Expr).push (Lean.Expr.fvar id1)

/-- The array of two variables, as the continuation receives it. -/
abbrev fv2 (id1 id2 : FVarId) : Array Lean.Expr := ([id1, id2].map Lean.Expr.fvar).toArray

/-- **The telescope's hand-over for a two-binder body**, from the
Meta-library fact and the body's shape. -/
theorem telescopeIn_of_lam2 (htel : LamTelescopeN) {body : Lean.Expr} {n1 n2 : Name}
    {T1 T2 b xTy yTy : Lean.Expr} {bi1 bi2 : BinderInfo} {k1 k2 : MixedGateBinder}
    {leafOf : List FVarId → Lean.Expr}
    (hb : body = Lean.Expr.lam n1 T1 (Lean.Expr.lam n2 T2 b bi2) bi1)
    (hl : b.isLambda = false)
    (hT1 : T1.instantiateRevRange 0 (#[] : Array Lean.Expr).size #[] = xTy)
    (hT2 : ∀ id1 : FVarId, T2.instantiateRevRange 0 (fv1 id1).size (fv1 id1) = yTy)
    (hi : ∀ id1 id2 : FVarId,
      b.instantiateRevRange 0 (fv2 id1 id2).size (fv2 id1 id2) = leafOf [id1, id2]) :
    TelescopeIn body (ListScope [(n1, k1, xTy), (n2, k2, yTy)] leafOf) := by
  intro α k r hrun
  rw [hb] at hrun
  obtain ⟨mctx, ids, hdecl, hk⟩ :=
    htel [(n1, T1, bi1), (n2, T2, bi2)] b hl α k r hrun
  rcases ids with _ | ⟨id1, _ | ⟨id2, _ | ⟨id3, ids⟩⟩⟩
  · exact False.elim hdecl
  · obtain ⟨_, h2⟩ := hdecl
    exact False.elim h2
  · obtain ⟨⟨d1, hf1, hn1, ht1⟩, ⟨d2, hf2, hn2, ht2⟩, _⟩ := hdecl
    have hk' : MRunsIn (k (fv2 id1 id2) (leafOf [id1, id2])) mctx r := by
      rw [← hi id1 id2]
      exact hk
    have h0 : 0 < (fv2 id1 id2).size := Nat.zero_lt_succ 1
    have h1 : 0 + 1 < (fv2 id1 id2).size := Nat.lt_succ_self 1
    have hx0 : ((fv2 id1 id2)[0]'h0).fvarId! = id1 := by
      first | rfl | simp [fv2, Lean.Expr.fvarId!]
    have hx1 : ((fv2 id1 id2)[0 + 1]'h1).fvarId! = id2 := by
      first | rfl | simp [fv2, Lean.Expr.fvarId!]
    have hend : (fv2 id1 id2).size ≤ 0 + 1 + 1 := Nat.le_refl 2
    have hdecls : DeclsAt mctx (fv2 id1 id2) 0 [(n1, k1, xTy), (n2, k2, yTy)] [id1, id2] :=
      And.intro
        (Exists.intro h0 (And.intro hx0 (Exists.intro d1
          (And.intro hf1 (And.intro hn1 (ht1.trans hT1))))))
        (And.intro
          (Exists.intro h1 (And.intro hx1 (Exists.intro d2
            (And.intro hf2 (And.intro hn2 (ht2.trans (hT2 id1)))))))
          hend)
    have hs : ListScope [(n1, k1, xTy), (n2, k2, yTy)] leafOf mctx (fv2 id1 id2)
        (leafOf [id1, id2]) := by
      unfold ListScope
      exact ⟨[id1, id2], rfl, hdecls⟩
    exact ⟨mctx, fv2 id1 id2, leafOf [id1, id2], hs, hk'⟩
  · obtain ⟨_, _, h3⟩ := hdecl
    exact False.elim h3

end Tools.ShippingLegacySem
