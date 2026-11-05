import Sparkle.Core.Domain
import Tools.ShippingGen5ConstValueESoundK
set_option autoImplicit false
/-! # Per-row `RowTypedAt` proofs (issue sparkle-ledger-dd4-rows; draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md §Rows)

No TRUSTED, axiom, `sorry` or `native_decide`. `PT` stays an arbitrary parameter: every theorem takes the row of its key as a SPEC (`TmSpec` / `TyConSpec`) about `PT`,
and the facts about the environment as hypotheses (`EnvType` / `EnvClosedPi` / `¬ IsDefn env D`). That a real environment satisfies them is shown by a meta check
(`Tests/Gen5/RowTypedKCheck.lean`), not here. The real `PT` is not in this repository, so the specs are not discharged against it; `Check` discharges them against a model table (non-vacuity).

* §1 Specs and the generic lemma for a row without arguments whose declared type is a closed constant: NO bridge (D1) needed. Six keys.
* §2 Option (a) of D1: rows with arguments and a closed codomain, over the structural `substS` (`instForallS`). This is the PROOF SHAPE only; it is stated for `RowTypedAtS`
  (`instForallS`), and turns into `RowTypedAt` only through `OblInst1Agree` (`rowTypedAt_of_S`), a named obligation that nothing here assumes. Four keys.
* Dependent keys (the codomain mentions an argument) are not proved: they need `OblInst1Agree`/`substS` AND a substitution lemma for `TDenK` (`OblDenSubst`). -/
namespace Tools.ShippingGen5RowTypedK
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK

/-! ## §1 Specs, and rows without arguments -/

/-- Spec of a type-former row of arity 0 that denotes `T` (the `tys` row of a plain inductive such as `Nat`, `Bool`). -/
def TyConSpec (PT : PrimTableK) (D : Name) (Ls : List Level) (T : Type) : Prop :=
  ∃ trow : TyRow, PT.tys D Ls = some trow ∧ trow.kinds = [] ∧ trow.den [] = some T

/-- Spec of a term row with the given `kinds`, all of whose denotations live in the Lean type `T`. -/
def TmSpec (PT : PrimTableK) (c : Name) (ls : List Level) (ks : List Bool) (T : Type) : Prop :=
  ∃ row : TmRow, PT.tms c ls = some row ∧ row.kinds = ks ∧ ∀ (as : List Arg) (d : Dyn), row.den as = some d → d.ty = T

/-- ENV FACT: the declared type of `c`, instantiated at `ls`, is `E` (a fact about the environment, not about `PT`). -/
def EnvType (env : Environment) (c : Name) (ls : List Level) (E : Expr) : Prop :=
  ∀ ci : ConstantInfo, env.find? c = some ci → ci.type.instantiateLevelParams ci.levelParams ls = E

theorem rowTypedAt_nullary_const (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (D : Name) (Ls : List Level) (T : Type)
    (hr : TmSpec PT c ls [] T) (ht : TyConSpec PT D Ls T) (hnd : ¬ IsDefn env D) (hT : EnvType env c ls (.const D Ls)) :
    RowTypedAt PT env c ls := by
  obtain ⟨row, hrow, hk, hden⟩ := hr
  obtain ⟨trow, htrow, htk, htd⟩ := ht
  refine rowTypedAt_nullary PT env c ls row hrow hk ?_
  intro ci ρ as d hci _ hd
  rw [hT ci hci, hden as d hd]
  have hargs : ArgsDenK PT env ρ trow.kinds ([] : List Expr) ([] : List Arg) := by rw [htk]; exact .nil
  exact .tcon htrow hnd hargs htd (by simp [mkAppN])

/-! ### The six keys (Type 0, no arguments) -/
section nullary
variable (PT : PrimTableK) (env : Environment)

theorem rowTyped_Nat_zero (hr : TmSpec PT ``Nat.zero [] [] Nat) (ht : TyConSpec PT ``Nat [] Nat) (hnd : ¬ IsDefn env ``Nat)
    (hT : EnvType env ``Nat.zero [] (.const ``Nat [])) : RowTypedAt PT env ``Nat.zero [] :=
  rowTypedAt_nullary_const PT env _ _ _ _ _ hr ht hnd hT

theorem rowTyped_Bool_false (hr : TmSpec PT ``Bool.false [] [] Bool) (ht : TyConSpec PT ``Bool [] Bool) (hnd : ¬ IsDefn env ``Bool)
    (hT : EnvType env ``Bool.false [] (.const ``Bool [])) : RowTypedAt PT env ``Bool.false [] :=
  rowTypedAt_nullary_const PT env _ _ _ _ _ hr ht hnd hT

theorem rowTyped_Bool_true (hr : TmSpec PT ``Bool.true [] [] Bool) (ht : TyConSpec PT ``Bool [] Bool) (hnd : ¬ IsDefn env ``Bool)
    (hT : EnvType env ``Bool.true [] (.const ``Bool [])) : RowTypedAt PT env ``Bool.true [] :=
  rowTypedAt_nullary_const PT env _ _ _ _ _ hr ht hnd hT

theorem rowTyped_PUnit_unit1 (hr : TmSpec PT ``PUnit.unit [.succ .zero] [] PUnit.{1}) (ht : TyConSpec PT ``PUnit [.succ .zero] PUnit.{1})
    (hnd : ¬ IsDefn env ``PUnit) (hT : EnvType env ``PUnit.unit [.succ .zero] (.const ``PUnit [.succ .zero])) :
    RowTypedAt PT env ``PUnit.unit [.succ .zero] :=
  rowTypedAt_nullary_const PT env _ _ _ _ _ hr ht hnd hT

theorem rowTyped_ActiveEdge_rising (hr : TmSpec PT `Sparkle.Core.Domain.ActiveEdge.rising [] [] Sparkle.Core.Domain.ActiveEdge)
    (ht : TyConSpec PT `Sparkle.Core.Domain.ActiveEdge [] Sparkle.Core.Domain.ActiveEdge) (hnd : ¬ IsDefn env `Sparkle.Core.Domain.ActiveEdge)
    (hT : EnvType env `Sparkle.Core.Domain.ActiveEdge.rising [] (.const `Sparkle.Core.Domain.ActiveEdge [])) :
    RowTypedAt PT env `Sparkle.Core.Domain.ActiveEdge.rising [] :=
  rowTypedAt_nullary_const PT env _ _ _ _ _ hr ht hnd hT

theorem rowTyped_ResetKind_synchronous (hr : TmSpec PT `Sparkle.IR.Type.ResetKind.synchronous [] [] Sparkle.IR.Type.ResetKind)
    (ht : TyConSpec PT `Sparkle.IR.Type.ResetKind [] Sparkle.IR.Type.ResetKind) (hnd : ¬ IsDefn env `Sparkle.IR.Type.ResetKind)
    (hT : EnvType env `Sparkle.IR.Type.ResetKind.synchronous [] (.const `Sparkle.IR.Type.ResetKind [])) :
    RowTypedAt PT env `Sparkle.IR.Type.ResetKind.synchronous [] :=
  rowTypedAt_nullary_const PT env _ _ _ _ _ hr ht hnd hT

end nullary

/-! ## §2 Option (a) of D1: closed codomains over the structural substitution (PROOF SHAPE; needs `OblInst1Agree` to reach `RowTypedAt`) -/

/-- `instForall` with the structural `substS` in place of `instantiate1` (what the carrier would say under D1 option (a)). -/
def instForallS : Expr → List Expr → Expr
  | .forallE _ _ b _, a :: as => instForallS (substS b 0 a) as
  | e, _ => e

/-- `RowTypedAt` over `instForallS`. -/
def RowTypedAtS (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) : Prop :=
  ∀ (ci : ConstantInfo) (row : TmRow) (ρ : Val) (args : List Expr) (as : List Arg) (d : Dyn),
    env.find? c = some ci → PT.tms c ls = some row → ArgsDenK PT env ρ row.kinds args as → row.den as = some d →
    TDenK PT env ρ (instForallS (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty

theorem instForallS_nil (e : Expr) : instForallS e [] = e := by cases e <;> rfl

/-- The telescope has `n` binders, each body closed (no dependency on any argument), and ends in `R`. -/
def ClosedPi : Expr → Nat → Expr → Prop
  | T, 0, R => T = R
  | T, n + 1, R => ∃ (x : Name) (A B : Expr) (bi : BinderInfo), T = .forallE x A B bi ∧ lbr B = 0 ∧ ClosedPi B n R

theorem instForallS_closedPi : ∀ (n : Nat) (T R : Expr) (args : List Expr), ClosedPi T n R → args.length = n → instForallS T args = R
  | 0, T, R, args, h, hl => by
    have : args = [] := List.length_eq_zero_iff.mp hl
    subst this; rw [instForallS_nil]; exact h
  | n + 1, T, R, args, ⟨x, A, B, bi, hT, hB, hrest⟩, hl => by
    subst hT
    match args, hl with
    | a :: as, hl =>
      have hl' : as.length = n := by simpa using hl
      show instForallS (substS B 0 a) as = R
      rw [substS_closed B hB a]
      exact instForallS_closedPi n B R as hrest hl'

/-- ENV FACT for option (a): the instantiated declared type is a closed telescope of `n` binders ending in `R`. -/
def EnvClosedPi (env : Environment) (c : Name) (ls : List Level) (n : Nat) (R : Expr) : Prop :=
  ∀ ci : ConstantInfo, env.find? c = some ci → ClosedPi (ci.type.instantiateLevelParams ci.levelParams ls) n R

/-- A row with arguments and a closed codomain: its `RowTypedAtS` follows from the spec, the env fact, and `R` being a plain type constant. The number of binders is `kinds.length`. -/
theorem rowTypedAtS_closedPi (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (ks : List Bool) (D : Name) (Ls : List Level) (T : Type)
    (hr : TmSpec PT c ls ks T) (ht : TyConSpec PT D Ls T) (hnd : ¬ IsDefn env D) (hT : EnvClosedPi env c ls ks.length (.const D Ls)) :
    RowTypedAtS PT env c ls := by
  obtain ⟨row, hrow, hk, hden⟩ := hr
  obtain ⟨trow, htrow, htk, htd⟩ := ht
  intro ci row' ρ args as d hci hrow' hargs hd
  rw [hrow] at hrow'; cases hrow'
  have hl : args.length = ks.length := by have := (argsDenK_length hargs).1; rwa [hk] at this
  rw [instForallS_closedPi ks.length _ _ args (hT ci hci) hl, hden as d hd]
  have hargs' : ArgsDenK PT env ρ trow.kinds ([] : List Expr) ([] : List Arg) := by rw [htk]; exact .nil
  exact .tcon htrow hnd hargs' htd (by simp [mkAppN])

/-- The bridge, as an implication between named obligations: under `OblInst1Agree` the structural telescope is the kernel's. -/
theorem instForallS_eq (hi : OblInst1Agree) : ∀ (args : List Expr) (T : Expr), instForallS T args = instForall T args
  | [], T => by rw [instForallS_nil, instForall_nil]
  | a :: as, T => by
    cases T with
    | forallE n A B bi => show instForallS (substS B 0 a) as = instForall (B.instantiate1 a) as; rw [hi B a]; exact instForallS_eq hi as _
    | _ => rfl

theorem rowTypedAt_of_S (hi : OblInst1Agree) (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level)
    (h : RowTypedAtS PT env c ls) : RowTypedAt PT env c ls := by
  intro ci row ρ args as d hci hrow hargs hd
  have := h ci row ρ args as d hci hrow hargs hd
  rwa [instForallS_eq hi] at this

/-! ### The four keys (Type 0, arguments, closed codomain) -/
section nondep
variable (PT : PrimTableK) (env : Environment)

theorem rowTypedS_Nat_succ (hr : TmSpec PT ``Nat.succ [] [true] Nat) (ht : TyConSpec PT ``Nat [] Nat) (hnd : ¬ IsDefn env ``Nat)
    (hT : EnvClosedPi env ``Nat.succ [] 1 (.const ``Nat [])) : RowTypedAtS PT env ``Nat.succ [] :=
  rowTypedAtS_closedPi PT env _ _ _ _ _ _ hr ht hnd hT

theorem rowTypedS_Int_ofNat (hr : TmSpec PT ``Int.ofNat [] [true] Int) (ht : TyConSpec PT ``Int [] Int) (hnd : ¬ IsDefn env ``Int)
    (hT : EnvClosedPi env ``Int.ofNat [] 1 (.const ``Int [])) : RowTypedAtS PT env ``Int.ofNat [] :=
  rowTypedAtS_closedPi PT env _ _ _ _ _ _ hr ht hnd hT

theorem rowTypedS_Int_negSucc (hr : TmSpec PT ``Int.negSucc [] [true] Int) (ht : TyConSpec PT ``Int [] Int) (hnd : ¬ IsDefn env ``Int)
    (hT : EnvClosedPi env ``Int.negSucc [] 1 (.const ``Int [])) : RowTypedAtS PT env ``Int.negSucc [] :=
  rowTypedAtS_closedPi PT env _ _ _ _ _ _ hr ht hnd hT

theorem rowTypedS_DomainConfig_mk (hr : TmSpec PT `Sparkle.Core.Domain.DomainConfig.mk [] [true, true, true] Sparkle.Core.Domain.DomainConfig)
    (ht : TyConSpec PT `Sparkle.Core.Domain.DomainConfig [] Sparkle.Core.Domain.DomainConfig) (hnd : ¬ IsDefn env `Sparkle.Core.Domain.DomainConfig)
    (hT : EnvClosedPi env `Sparkle.Core.Domain.DomainConfig.mk [] 3 (.const `Sparkle.Core.Domain.DomainConfig [])) :
    RowTypedAtS PT env `Sparkle.Core.Domain.DomainConfig.mk [] :=
  rowTypedAtS_closedPi PT env _ _ _ _ _ _ hr ht hnd hT

end nondep

end Tools.ShippingGen5RowTypedK
