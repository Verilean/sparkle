import Tools.ShippingGen5PTLit
import Tools.ShippingGen5RowTypedV
set_option autoImplicit false
-- D.D-4 final, the concrete table `PTcorpus` (Issue sparkle-ledger-dd4-final). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Ordinary definitions and theorems checked by the kernel.

/-! # `PTcorpus`: a concrete `PrimTableK` for the residue keys of the corpus

A row is written as a Lean TERM of the value telescope it denotes (`TmTele` / `TyTele`, indexed by the argument kinds): a term argument `tm A (fun a => …)`, a type argument `ty (fun T => …)`, and the result `done R v`.
`TmTele.run` interprets an argument list: a term argument is accepted only at the Lean type `A` (the cast is `Classical.propDecidable`), a type argument at any `Type`. So a constructor row IS the constructor:
`Nat.succ` is `tm Nat (fun n => done Nat (Nat.succ n))`, `Signal.mk` is `tm DomainConfig (fun d => ty (fun α => tm (Nat → α) (fun f => done (Signal d α) ⟨f⟩)))`.

* `PTcorpus.tys` / `PTcorpus.tms` look the key `(Name, levels)` up in a finite table (`tysTable` / `tmsTable`); the levels of a key are numerals (`lvNats`), other level lists have no row.
* A key of the K1 list that has NO row here is a named obligation (`Missing`): recursors (a motive is a function into `Sort u`, which has no `Arg` form: `Dyn.ty : Type`), constants whose declared type lives above `Type 0`,
  and declarations of the corpus modules (they cannot be imported into `Tools`). The per-key list and the reasons are printed by `Tests/Gen5/PTCorpusCheck.lean`.
* Per-row facts that are provable are theorems about `PTcorpus` itself (`TmSpec` / `TyConSpec` by construction); the env facts stay hypotheses, checked in the real environment by the Check. -/

namespace Tools.ShippingGen5PTCorpus
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey
open Tools.ShippingGen5RowTypedK (TmSpec TyConSpec)

/-- Value telescope with the argument kinds as the index (`true` = term argument, `false` = type argument). -/
inductive TmTele : List Bool → Type 1
  | done (R : Type) (v : R) : TmTele []
  | tm {ks : List Bool} (A : Type) (k : A → TmTele ks) : TmTele (true :: ks)
  | ty {ks : List Bool} (k : (T : Type) → TmTele ks) : TmTele (false :: ks)

/-- Type-former telescope. -/
inductive TyTele : List Bool → Type 1
  | done (T : Type) : TyTele []
  | tm {ks : List Bool} (A : Type) (k : A → TyTele ks) : TyTele (true :: ks)
  | ty {ks : List Bool} (k : (T : Type) → TyTele ks) : TyTele (false :: ks)

open Classical in
noncomputable def TmTele.run : {ks : List Bool} → TmTele ks → List Arg → Option Dyn
  | _, .done R v, [] => some ⟨R, v⟩
  | _, .tm A k, .tm ⟨α, a⟩ :: xs => if h : α = A then (k (cast h a)).run xs else none
  | _, .ty k, .ty T :: xs => (k T).run xs
  | _, _, _ => none

open Classical in
noncomputable def TyTele.run : {ks : List Bool} → TyTele ks → List Arg → Option Type
  | _, .done T, [] => some T
  | _, .tm A k, .tm ⟨α, a⟩ :: xs => if h : α = A then (k (cast h a)).run xs else none
  | _, .ty k, .ty T :: xs => (k T).run xs
  | _, _, _ => none

noncomputable def TmTele.row {ks : List Bool} (t : TmTele ks) : TmRow := ⟨ks, t.run⟩
noncomputable def TyTele.row {ks : List Bool} (t : TyTele ks) : TyRow := ⟨ks, t.run⟩

/-- Every value the telescope produces has the Lean type `T`. -/
def TmTele.ResTy : {ks : List Bool} → TmTele ks → Type → Prop
  | _, .done R _, T => R = T
  | _, .tm _ k, T => ∀ a, (k a).ResTy T
  | _, .ty k, T => ∀ X, (k X).ResTy T

theorem TmTele.run_ty : ∀ {ks : List Bool} (t : TmTele ks) (T : Type), t.ResTy T → ∀ (xs : List Arg) (d : Dyn), t.run xs = some d → d.ty = T
  | _, .done R v, T, h, [], d, hd => by
      simp only [TmTele.run] at hd; cases hd; exact h
  | _, .done _ _, _, _, _ :: _, _, hd => by simp [TmTele.run] at hd
  | _, .tm A k, T, h, [], d, hd => by simp [TmTele.run] at hd
  | _, .tm A k, T, h, .ty _ :: xs, d, hd => by simp [TmTele.run] at hd
  | _, .tm A k, T, h, .tm ⟨α, a⟩ :: xs, d, hd => by
      simp only [TmTele.run] at hd
      split at hd
      · exact TmTele.run_ty (k _) T (h _) xs d hd
      · cases hd
  | _, .ty k, T, h, [], d, hd => by simp [TmTele.run] at hd
  | _, .ty k, T, h, .tm _ :: xs, d, hd => by simp [TmTele.run] at hd
  | _, .ty k, T, h, .ty X :: xs, d, hd => by
      simp only [TmTele.run] at hd
      exact TmTele.run_ty (k X) T (h X) xs d hd

theorem TmTele.spec {ks : List Bool} (t : TmTele ks) (T : Type) (h : t.ResTy T) {PT : PrimTableK} {c : Name} {ls : List Level}
    (hrow : PT.tms c ls = some t.row) : TmSpec PT c ls ks T :=
  ⟨t.row, hrow, rfl, fun xs d hd => TmTele.run_ty t T h xs d hd⟩

theorem TyTele.spec_nullary (T : Type) {PT : PrimTableK} {D : Name} {Ls : List Level}
    (hrow : PT.tys D Ls = some (TyTele.done T).row) : TyConSpec PT D Ls T :=
  ⟨_, hrow, rfl, by simp [TyTele.row, TyTele.run]⟩

end Tools.ShippingGen5PTCorpus
