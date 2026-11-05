import Tools.ShippingGen5ConstValueESProof
import Tools.ShippingGen5RowTypedK
set_option autoImplicit false
/-! # `RowTypedAt` over the syntactic carrier (issue sparkle-ledger-dd4-sound; draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md §SoundS2)

`RowTypedAtES` is `RowTypedAt` with `ArgsDenS` / `TDenS` / `instForallS` of the `CVEKS` carrier (no `instantiate1`, no `liftLooseBVars`, no bridge `OblInst1Agree`).
`OblRowTypedS` is its conjunction over all keys. The four rows with arguments and a CLOSED codomain are proved (`DomainConfig.mk`, `Int.ofNat`, `Int.negSucc`, `Nat.succ`),
from specs about `PT` (`TmSpec` / `TyConSpec`, arbitrary `PT`) and env facts (`EnvClosedPi`, `¬ IsDefn`). The 30 dependent rows are NOT proved: they wait on the design question Q1 (`OblDenSubstS`).
No TRUSTED, axiom, `sorry`, `native_decide`. -/
namespace Tools.ShippingGen5RowTypedS
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueES
open Tools.ShippingGen5RowTypedK (TmSpec TyConSpec EnvType ClosedPi EnvClosedPi)

/-- The obligation of ONE key `(c, ls)` on the syntactic carrier. -/
def RowTypedAtES (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) : Prop :=
  ∀ (ci : ConstantInfo) (row : TmRow) (ρ : Val) (args : List Expr) (as : List Arg) (d : Dyn),
    env.find? c = some ci → PT.tms c ls = some row → ArgsDenS PT env ρ row.kinds args as → row.den as = some d →
    TDenS PT env ρ (instForallS (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty

/-- `OblRowTypedS`: every key. -/
def OblRowTypedS (PT : PrimTableK) (env : Environment) : Prop := ∀ (c : Name) (ls : List Level), RowTypedAtES PT env c ls

theorem rowTypedAtES_of_none (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (h : PT.tms c ls = none) : RowTypedAtES PT env c ls := by
  intro ci row ρ args as d _ hrow; rw [h] at hrow; cases hrow

theorem rowTypedAtES_of_den_none (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (row : TmRow)
    (hrow : PT.tms c ls = some row) (hden : ∀ as, row.den as = none) : RowTypedAtES PT env c ls := by
  intro ci row' ρ args as d _ hrow' _ hd
  rw [hrow] at hrow'; cases hrow'
  rw [hden] at hd; cases hd

/-- A finite table: outside the key list there is no row; the obligation is the conjunction over the list. -/
theorem oblRowTypedS_of_keys (PT : PrimTableK) (env : Environment) (keys : List (Name × List Level))
    (hkeys : ∀ c ls, PT.tms c ls ≠ none → (c, ls) ∈ keys) (h : ∀ k ∈ keys, RowTypedAtES PT env k.1 k.2) : OblRowTypedS PT env := fun c ls => by
  by_cases hn : PT.tms c ls = none
  · exact rowTypedAtES_of_none PT env c ls hn
  · exact h (c, ls) (hkeys c ls hn)

/-! ## Closed codomain (arguments allowed) -/

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

/-- A row with arguments and a closed codomain `.const D Ls` that is a plain type constant: `RowTypedAtES` from the specs and env facts. `ArgsDenS` only supplies the argument count. -/
theorem rowTypedAtES_closedPi (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (ks : List Bool) (D : Name) (Ls : List Level) (T : Type)
    (hr : TmSpec PT c ls ks T) (ht : TyConSpec PT D Ls T) (hnd : ¬ IsDefn env D) (hT : EnvClosedPi env c ls ks.length (.const D Ls)) :
    RowTypedAtES PT env c ls := by
  obtain ⟨row, hrow, hk, hden⟩ := hr
  obtain ⟨trow, htrow, htk, htd⟩ := ht
  intro ci row' ρ args as d hci hrow' hargs hd
  rw [hrow] at hrow'; cases hrow'
  have hl : args.length = ks.length := by have := (argsdens_length hargs).1; rwa [hk] at this
  rw [instForallS_closedPi ks.length _ _ args (hT ci hci) hl, hden as d hd]
  have hargs' : ArgsDenS PT env ρ trow.kinds ([] : List Expr) ([] : List Arg) := by rw [htk]; exact .nil
  exact .tcon htrow hnd hargs' htd (by simp [mkAppN])

section closed
variable (PT : PrimTableK) (env : Environment)

theorem rowTypedES_Nat_succ (hr : TmSpec PT ``Nat.succ [] [true] Nat) (ht : TyConSpec PT ``Nat [] Nat) (hnd : ¬ IsDefn env ``Nat)
    (hT : EnvClosedPi env ``Nat.succ [] 1 (.const ``Nat [])) : RowTypedAtES PT env ``Nat.succ [] :=
  rowTypedAtES_closedPi PT env _ _ _ _ _ _ hr ht hnd hT

theorem rowTypedES_Int_ofNat (hr : TmSpec PT ``Int.ofNat [] [true] Int) (ht : TyConSpec PT ``Int [] Int) (hnd : ¬ IsDefn env ``Int)
    (hT : EnvClosedPi env ``Int.ofNat [] 1 (.const ``Int [])) : RowTypedAtES PT env ``Int.ofNat [] :=
  rowTypedAtES_closedPi PT env _ _ _ _ _ _ hr ht hnd hT

theorem rowTypedES_Int_negSucc (hr : TmSpec PT ``Int.negSucc [] [true] Int) (ht : TyConSpec PT ``Int [] Int) (hnd : ¬ IsDefn env ``Int)
    (hT : EnvClosedPi env ``Int.negSucc [] 1 (.const ``Int [])) : RowTypedAtES PT env ``Int.negSucc [] :=
  rowTypedAtES_closedPi PT env _ _ _ _ _ _ hr ht hnd hT

theorem rowTypedES_DomainConfig_mk (hr : TmSpec PT `Sparkle.Core.Domain.DomainConfig.mk [] [true, true, true] Sparkle.Core.Domain.DomainConfig)
    (ht : TyConSpec PT `Sparkle.Core.Domain.DomainConfig [] Sparkle.Core.Domain.DomainConfig) (hnd : ¬ IsDefn env `Sparkle.Core.Domain.DomainConfig)
    (hT : EnvClosedPi env `Sparkle.Core.Domain.DomainConfig.mk [] 3 (.const `Sparkle.Core.Domain.DomainConfig [])) :
    RowTypedAtES PT env `Sparkle.Core.Domain.DomainConfig.mk [] :=
  rowTypedAtES_closedPi PT env _ _ _ _ _ _ hr ht hnd hT

end closed

end Tools.ShippingGen5RowTypedS
