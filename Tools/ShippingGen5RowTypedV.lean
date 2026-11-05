import Tools.ShippingGen5ConstValueEVL
import Tools.ShippingGen5RowTypedS
set_option autoImplicit false
/-! # Rows on the valuation carrier `CVEKVL` (issue sparkle-ledger-dd4-v2; draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md §V2)

No TRUSTED, axiom, `sorry`, `native_decide`. `PT` is an arbitrary parameter: every theorem takes the row of its key as a SPEC about `PT` and the facts about the environment as hypotheses.
Existing files are unchanged.

* §1 Literal rows (the `V` version of `oblDenLits_of_rows`).
* §2 `RowTypedAtV` / `OblRowTypedV` (the `hty` of the `prim` rule of `CVEKVL`), the 6 argument-free rows, the 4 closed-codomain rows.
* §3 The dependent rows whose result is a type former applied to the FIRST argument (`Foo dom`, `Fin n`, `BitVec w`, `Decidable p`): `RowTypedAtV` is proved for the shape (`PiN` telescope, result `D (bvar n)`),
  with `instForallS`/`substS` computed (`instForallS_depFirst`). That is the result of `CVEKVL`'s `prim` rule with NO `OblDenSubstS`: only the argument's own `CVEKV` derivation is needed.
* §4 The argument typing (`RowTeleEvAt`, with the evidence-carrying conversion of `CVEKVL`) per row: for a closed telescope of constant term binders (`ConstPi`): a per-row theorem. -/
namespace Tools.ShippingGen5RowTypedV
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueES
  Tools.ShippingGen5ConstValueESL Tools.ShippingGen5ConstValueEVL
open Tools.ShippingGen5RowTypedK (TmSpec TyConSpec ClosedPi)
open Tools.ShippingGen5RowTypedS (instForallS_closedPi)

/-! ## §1 Literal rows -/

theorem tdenv_const_nullary {PT : PrimTableK} {env : Environment} {ρ : Val} {c : Name} {ls : List Level} {row : TyRow} {T : Type}
    (hrow : PT.tys c ls = some row) (hnd : ¬ IsDefn env c) (hk : row.kinds = []) (hT : row.den [] = some T) :
    TDenV PT env ρ (.const c ls) T :=
  .tcon (args := []) (as := []) hrow hnd (by rw [hk]; exact .nil) hT rfl

/-- `OblDenLits` on the valuation carrier: the `Nat` / `String` rows (nullary `tys` rows, not definitions) make the two literal labels denote `Nat` / `String` at every valuation. -/
theorem oblDenLitsV_of_rows {PT : PrimTableK} {env : Environment} {rn rs : TyRow}
    (hn : PT.tys `Nat [] = some rn) (hnnd : ¬ IsDefn env `Nat) (hnk : rn.kinds = []) (hnT : rn.den [] = some Nat)
    (hs : PT.tys `String [] = some rs) (hsnd : ¬ IsDefn env `String) (hsk : rs.kinds = []) (hsT : rs.den [] = some String) :
    (∀ ρ : Val, TDenV PT env ρ (.const `Nat []) Nat) ∧ (∀ ρ : Val, TDenV PT env ρ (.const `String []) String) :=
  ⟨fun _ => tdenv_const_nullary hn hnnd hnk hnT, fun _ => tdenv_const_nullary hs hsnd hsk hsT⟩

/-- The literal RULES are typed on `CVEKVL` from the two rows alone (no valuation condition, no `EnvDeclClosed`): the label of `natLit` / `strLit` denotes its Lean type. -/
theorem natLit_typed {PT : PrimTableK} {env : Environment} {rn : TyRow} (hn : PT.tys `Nat [] = some rn) (hnnd : ¬ IsDefn env `Nat)
    (hnk : rn.kinds = []) (hnT : rn.den [] = some Nat) {ρ : Val} {n : Nat} (_ : CVEKVB PT env ρ (.lit (.natVal n)) (.const `Nat []) Nat n) :
    TDenV PT env ρ (.const `Nat []) Nat :=
  tdenv_const_nullary hn hnnd hnk hnT

theorem strLit_typed {PT : PrimTableK} {env : Environment} {rs : TyRow} (hs : PT.tys `String [] = some rs) (hsnd : ¬ IsDefn env `String)
    (hsk : rs.kinds = []) (hsT : rs.den [] = some String) {ρ : Val} {s : String} (_ : CVEKVB PT env ρ (.lit (.strVal s)) (.const `String []) String s) :
    TDenV PT env ρ (.const `String []) String :=
  tdenv_const_nullary hs hsnd hsk hsT

/-- With the literal rows and `EnvDeclClosed`, every `CVEKVL` derivation at a well-formed valuation is typed (`denTypedVL`, discharged with `oblDenLitsV_of_rows`). -/
theorem denTypedVL_of_rows {PT : PrimTableK} {env : Environment} (hcl : EnvDeclClosed env) {rn rs : TyRow}
    (hn : PT.tys `Nat [] = some rn) (hnnd : ¬ IsDefn env `Nat) (hnk : rn.kinds = []) (hnT : rn.den [] = some Nat)
    (hs : PT.tys `String [] = some rs) (hsnd : ¬ IsDefn env `String) (hsk : rs.kinds = []) (hsT : rs.den [] = some String) :
    OblDenTypedV PT env :=
  let h := oblDenLitsV_of_rows hn hnnd hnk hnT hs hsnd hsk hsT
  denTypedVL hcl h.1 h.2

/-! ## §2 `RowTypedAtV`: the `hty` obligation of `CVEKVL`'s `prim` rule -/

/-- The obligation of ONE key `(c, ls)` on `CVEKVL`: the declared type, instantiated syntactically and applied (`instForallS`) to the row's arguments, denotes the row's value type. -/
def RowTypedAtV (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) : Prop :=
  ∀ (ci : ConstantInfo) (row : TmRow) (ρ : Val) (args : List Expr) (as : List Arg) (d : Dyn),
    env.find? c = some ci → PT.tms c ls = some row → ArgsDenV PT env ρ row.kinds args as → row.den as = some d →
    TDenV PT env ρ (instForallS (instantiateLevelParamsS ci.levelParams ls ci.type) args) d.ty

def OblRowTypedV (PT : PrimTableK) (env : Environment) : Prop := ∀ (c : Name) (ls : List Level), RowTypedAtV PT env c ls

theorem rowTypedAtV_of_none (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (h : PT.tms c ls = none) : RowTypedAtV PT env c ls := by
  intro ci row ρ args as d _ hrow; rw [h] at hrow; cases hrow

theorem rowTypedAtV_of_den_none (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (row : TmRow)
    (hrow : PT.tms c ls = some row) (hden : ∀ as, row.den as = none) : RowTypedAtV PT env c ls := by
  intro ci row' ρ args as d _ hrow' _ hd
  rw [hrow] at hrow'; cases hrow'
  rw [hden] at hd; cases hd

theorem oblRowTypedV_of_keys (PT : PrimTableK) (env : Environment) (keys : List (Name × List Level))
    (hkeys : ∀ c ls, PT.tms c ls ≠ none → (c, ls) ∈ keys) (h : ∀ k ∈ keys, RowTypedAtV PT env k.1 k.2) : OblRowTypedV PT env := fun c ls => by
  by_cases hn : PT.tms c ls = none
  · exact rowTypedAtV_of_none PT env c ls hn
  · exact h (c, ls) (hkeys c ls hn)

/-- ENV FACT (syntactic levels): the declared type of `c`, instantiated by `instantiateLevelParamsS`, is `E`. -/
def EnvTypeL (env : Environment) (c : Name) (ls : List Level) (E : Expr) : Prop :=
  ∀ ci : ConstantInfo, env.find? c = some ci → instantiateLevelParamsS ci.levelParams ls ci.type = E

/-- ENV FACT: the instantiated declared type is a closed telescope of `n` binders ending in `R`. -/
def EnvClosedPiL (env : Environment) (c : Name) (ls : List Level) (n : Nat) (R : Expr) : Prop :=
  ∀ ci : ConstantInfo, env.find? c = some ci → ClosedPi (instantiateLevelParamsS ci.levelParams ls ci.type) n R

/-- A row without arguments whose declared type is a plain type constant. Six keys. -/
theorem rowTypedAtV_nullary_const (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (D : Name) (Ls : List Level) (T : Type)
    (hr : TmSpec PT c ls [] T) (ht : TyConSpec PT D Ls T) (hnd : ¬ IsDefn env D) (hT : EnvTypeL env c ls (.const D Ls)) :
    RowTypedAtV PT env c ls := by
  obtain ⟨row, hrow, hk, hden⟩ := hr
  obtain ⟨trow, htrow, htk, htd⟩ := ht
  intro ci row' ρ args as d hci hrow' hargs hd
  rw [hrow] at hrow'; cases hrow'
  have hl : args.length = 0 := by have := (argsdenv_length hargs).1; rwa [hk] at this
  have : args = [] := List.length_eq_zero_iff.mp hl
  subst this
  rw [instForallS_nil, hT ci hci, hden as d hd]
  have hargs' : ArgsDenV PT env ρ trow.kinds ([] : List Expr) ([] : List Arg) := by rw [htk]; exact .nil
  exact .tcon htrow hnd hargs' htd (by first | simp [mkAppN, mkApp] | (simp [mkAppN]; rfl))

/-- A row with arguments and a CLOSED codomain: `instForallS` returns the codomain (`substS_closed`), so nothing depends on the arguments. Four keys. -/
theorem rowTypedAtV_closedPi (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (ks : List Bool) (D : Name) (Ls : List Level) (T : Type)
    (hr : TmSpec PT c ls ks T) (ht : TyConSpec PT D Ls T) (hnd : ¬ IsDefn env D) (hT : EnvClosedPiL env c ls ks.length (.const D Ls)) :
    RowTypedAtV PT env c ls := by
  obtain ⟨row, hrow, hk, hden⟩ := hr
  obtain ⟨trow, htrow, htk, htd⟩ := ht
  intro ci row' ρ args as d hci hrow' hargs hd
  rw [hrow] at hrow'; cases hrow'
  have hl : args.length = ks.length := by have := (argsdenv_length hargs).1; rwa [hk] at this
  rw [instForallS_closedPi ks.length _ _ args (hT ci hci) hl, hden as d hd]
  have hargs' : ArgsDenV PT env ρ trow.kinds ([] : List Expr) ([] : List Arg) := by rw [htk]; exact .nil
  exact .tcon htrow hnd hargs' htd (by first | simp [mkAppN, mkApp] | (simp [mkAppN]; rfl))

section keys
variable (PT : PrimTableK) (env : Environment)

theorem rowTypedV_Nat_zero (hr : TmSpec PT ``Nat.zero [] [] Nat) (ht : TyConSpec PT ``Nat [] Nat) (hnd : ¬ IsDefn env ``Nat)
    (hT : EnvTypeL env ``Nat.zero [] (.const ``Nat [])) : RowTypedAtV PT env ``Nat.zero [] :=
  rowTypedAtV_nullary_const PT env _ _ _ _ _ hr ht hnd hT

theorem rowTypedV_Bool_false (hr : TmSpec PT ``Bool.false [] [] Bool) (ht : TyConSpec PT ``Bool [] Bool) (hnd : ¬ IsDefn env ``Bool)
    (hT : EnvTypeL env ``Bool.false [] (.const ``Bool [])) : RowTypedAtV PT env ``Bool.false [] :=
  rowTypedAtV_nullary_const PT env _ _ _ _ _ hr ht hnd hT

theorem rowTypedV_Bool_true (hr : TmSpec PT ``Bool.true [] [] Bool) (ht : TyConSpec PT ``Bool [] Bool) (hnd : ¬ IsDefn env ``Bool)
    (hT : EnvTypeL env ``Bool.true [] (.const ``Bool [])) : RowTypedAtV PT env ``Bool.true [] :=
  rowTypedAtV_nullary_const PT env _ _ _ _ _ hr ht hnd hT

theorem rowTypedV_PUnit_unit1 (hr : TmSpec PT ``PUnit.unit [.succ .zero] [] PUnit.{1}) (ht : TyConSpec PT ``PUnit [.succ .zero] PUnit.{1})
    (hnd : ¬ IsDefn env ``PUnit) (hT : EnvTypeL env ``PUnit.unit [.succ .zero] (.const ``PUnit [.succ .zero])) :
    RowTypedAtV PT env ``PUnit.unit [.succ .zero] :=
  rowTypedAtV_nullary_const PT env _ _ _ _ _ hr ht hnd hT

theorem rowTypedV_ActiveEdge_rising (hr : TmSpec PT `Sparkle.Core.Domain.ActiveEdge.rising [] [] Sparkle.Core.Domain.ActiveEdge)
    (ht : TyConSpec PT `Sparkle.Core.Domain.ActiveEdge [] Sparkle.Core.Domain.ActiveEdge) (hnd : ¬ IsDefn env `Sparkle.Core.Domain.ActiveEdge)
    (hT : EnvTypeL env `Sparkle.Core.Domain.ActiveEdge.rising [] (.const `Sparkle.Core.Domain.ActiveEdge [])) :
    RowTypedAtV PT env `Sparkle.Core.Domain.ActiveEdge.rising [] :=
  rowTypedAtV_nullary_const PT env _ _ _ _ _ hr ht hnd hT

theorem rowTypedV_ResetKind_synchronous (hr : TmSpec PT `Sparkle.IR.Type.ResetKind.synchronous [] [] Sparkle.IR.Type.ResetKind)
    (ht : TyConSpec PT `Sparkle.IR.Type.ResetKind [] Sparkle.IR.Type.ResetKind) (hnd : ¬ IsDefn env `Sparkle.IR.Type.ResetKind)
    (hT : EnvTypeL env `Sparkle.IR.Type.ResetKind.synchronous [] (.const `Sparkle.IR.Type.ResetKind [])) :
    RowTypedAtV PT env `Sparkle.IR.Type.ResetKind.synchronous [] :=
  rowTypedAtV_nullary_const PT env _ _ _ _ _ hr ht hnd hT

theorem rowTypedV_Nat_succ (hr : TmSpec PT ``Nat.succ [] [true] Nat) (ht : TyConSpec PT ``Nat [] Nat) (hnd : ¬ IsDefn env ``Nat)
    (hT : EnvClosedPiL env ``Nat.succ [] 1 (.const ``Nat [])) : RowTypedAtV PT env ``Nat.succ [] :=
  rowTypedAtV_closedPi PT env _ _ _ _ _ _ hr ht hnd hT

theorem rowTypedV_Int_ofNat (hr : TmSpec PT ``Int.ofNat [] [true] Int) (ht : TyConSpec PT ``Int [] Int) (hnd : ¬ IsDefn env ``Int)
    (hT : EnvClosedPiL env ``Int.ofNat [] 1 (.const ``Int [])) : RowTypedAtV PT env ``Int.ofNat [] :=
  rowTypedAtV_closedPi PT env _ _ _ _ _ _ hr ht hnd hT

theorem rowTypedV_Int_negSucc (hr : TmSpec PT ``Int.negSucc [] [true] Int) (ht : TyConSpec PT ``Int [] Int) (hnd : ¬ IsDefn env ``Int)
    (hT : EnvClosedPiL env ``Int.negSucc [] 1 (.const ``Int [])) : RowTypedAtV PT env ``Int.negSucc [] :=
  rowTypedAtV_closedPi PT env _ _ _ _ _ _ hr ht hnd hT

theorem rowTypedV_DomainConfig_mk (hr : TmSpec PT `Sparkle.Core.Domain.DomainConfig.mk [] [true, true, true] Sparkle.Core.Domain.DomainConfig)
    (ht : TyConSpec PT `Sparkle.Core.Domain.DomainConfig [] Sparkle.Core.Domain.DomainConfig) (hnd : ¬ IsDefn env `Sparkle.Core.Domain.DomainConfig)
    (hT : EnvClosedPiL env `Sparkle.Core.Domain.DomainConfig.mk [] 3 (.const `Sparkle.Core.Domain.DomainConfig [])) :
    RowTypedAtV PT env `Sparkle.Core.Domain.DomainConfig.mk [] :=
  rowTypedAtV_closedPi PT env _ _ _ _ _ _ hr ht hnd hT

end keys

/-! ## §3 Dependent rows whose result is a type former applied to the first argument

The shape: the instantiated declared type has `n + 1` leading binders (arbitrary binder types and bodies: `instForallS` never looks at them) and its result is `D (bvar n)`, i.e. `D` applied to the FIRST binder.
`instForallS` of the telescope at arguments `a0 :: as` is then `D a0` (`instForallS_depFirst`). The result type of the row is `D` at the first argument: that is the spec `FirstArgSpec` about `PT`. -/

/-- `n` leading binders (any binder types, any bodies), then the body `R`. -/
def PiN : Expr → Nat → Expr → Prop
  | T, 0, R => T = R
  | T, n + 1, R => ∃ (x : Name) (A B : Expr) (bi : BinderInfo), T = .forallE x A B bi ∧ PiN B n R

theorem piN_substS : ∀ (n : Nat) (T R : Expr) (k : Nat) (x : Expr), PiN T n R → PiN (substS T k x) n (substS R (k + n) x)
  | 0, T, R, k, x, h => by
    have h' : T = R := h
    subst h'
    exact rfl
  | n + 1, T, R, k, x, ⟨y, A, B, bi, hT, hB⟩ => by
    subst hT
    refine ⟨y, substS A k x, substS B (k + 1) x, bi, rfl, ?_⟩
    have := piN_substS n B R (k + 1) x hB
    rwa [show k + 1 + n = k + (n + 1) by omega] at this

theorem instForallS_piN_lift (C : Expr) (hC : ∀ (k : Nat) (x : Expr), substS C k x = C) (a : Expr) :
    ∀ (m : Nat) (T : Expr) (args : List Expr), PiN T m (.app C (liftS a 0 m)) → args.length = m → instForallS T args = .app C a
  | 0, T, args, h, hl => by
    have : args = [] := List.length_eq_zero_iff.mp hl
    subst this
    have h' : T = .app C (liftS a 0 0) := h
    rw [instForallS_nil, h', liftS_zero]
  | m + 1, T, args, ⟨y, A, B, bi, hT, hB⟩, hl => by
    subst hT
    match args, hl with
    | b :: as, hl =>
      have hl' : as.length = m := by simpa using hl
      show instForallS (substS B 0 b) as = _
      have h1 := piN_substS m B _ 0 b hB
      have h2 : substS (.app C (liftS a 0 (m + 1))) (0 + m) b = .app C (liftS a 0 m) := by
        simp only [substS, hC, Nat.zero_add]
        rw [substS_liftS_in a 0 (m + 1) m b (by omega) (by omega)]
        rfl
      rw [h2] at h1
      exact instForallS_piN_lift C hC a m _ as h1 hl'

/-- The computed `instForallS`: a telescope with `n + 1` binders and result `C (bvar n)` applied to `a0 :: as` is `C a0`. -/
theorem instForallS_depFirst (C : Expr) (hC : ∀ (k : Nat) (x : Expr), substS C k x = C) (n : Nat) (T : Expr) (a0 : Expr) (as : List Expr)
    (h : PiN T (n + 1) (.app C (.bvar n))) (hl : as.length = n) : instForallS T (a0 :: as) = .app C a0 := by
  obtain ⟨y, A, B, bi, hT, hB⟩ := h
  subst hT
  show instForallS (substS B 0 a0) as = _
  have h1 := piN_substS n B _ 0 a0 hB
  have h2 : substS (.app C (.bvar n)) (0 + n) a0 = .app C (liftS a0 0 n) := by
    simp [substS, hC]
  rw [h2] at h1
  exact instForallS_piN_lift C hC a0 n _ as h1 hl

/-- ENV FACT: the instantiated declared type of `c` is `n + 1` binders then `D Ls (bvar n)`. -/
def EnvDepFirst (env : Environment) (c : Name) (ls : List Level) (n : Nat) (D : Name) (Ls : List Level) : Prop :=
  ∀ ci : ConstantInfo, env.find? c = some ci → PiN (instantiateLevelParamsS ci.levelParams ls ci.type) (n + 1) (.app (.const D Ls) (.bvar n))

/-- Spec of a row (about `PT`): its argument kinds are `k0 :: ks'`, and the value type it produces is the denotation of the type former `D` at the FIRST argument. -/
def FirstArgSpec (PT : PrimTableK) (c : Name) (ls : List Level) (k0 : Bool) (ks' : List Bool) (D : Name) (Ls : List Level) : Prop :=
  ∃ (row : TmRow) (trow : TyRow), PT.tms c ls = some row ∧ row.kinds = k0 :: ks' ∧ PT.tys D Ls = some trow ∧ trow.kinds = [k0] ∧
    ∀ (as : List Arg) (d : Dyn), row.den as = some d → ∃ (a0 : Arg) (rest : List Arg), as = a0 :: rest ∧ trow.den [a0] = some d.ty

theorem argsDenV_head {PT : PrimTableK} {env : Environment} {ρ : Val} {k0 : Bool} {ks : List Bool} {args : List Expr} {a0 : Arg} {rest : List Arg}
    (h : ArgsDenV PT env ρ (k0 :: ks) args (a0 :: rest)) :
    ∃ (e : Expr) (es : List Expr), args = e :: es ∧ ArgsDenV PT env ρ [k0] [e] [a0] :=
  match h with
  | .ty hT _ => ⟨_, _, rfl, .ty hT .nil⟩
  | .tm hv _ => ⟨_, _, rfl, .tm hv .nil⟩

/-- A dependent row of the first-argument shape: `RowTypedAtV` from the spec and the env fact. NO `OblDenSubstS`: the result `D a0` is typed by the row of `D` and the FIRST argument's own derivation. -/
theorem rowTypedAtV_depFirst (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (k0 : Bool) (ks' : List Bool) (D : Name) (Ls : List Level)
    (hs : FirstArgSpec PT c ls k0 ks' D Ls) (hnd : ¬ IsDefn env D) (hT : EnvDepFirst env c ls ks'.length D Ls) : RowTypedAtV PT env c ls := by
  obtain ⟨row, trow, hrow, hk, htrow, htk, hden⟩ := hs
  intro ci row' ρ args as d hci hrow' hargs hd
  rw [hrow] at hrow'; cases hrow'
  obtain ⟨a0, rest, has, htd⟩ := hden as d hd
  subst has
  rw [hk] at hargs
  obtain ⟨e, es, rfl, hhead⟩ := argsDenV_head hargs
  have hl : es.length = ks'.length := by
    have := (argsdenv_length hargs).1
    simpa using this
  rw [instForallS_depFirst (.const D Ls) (fun _ _ => rfl) ks'.length _ e es (hT ci hci) hl]
  have hargs' : ArgsDenV PT env ρ trow.kinds [e] [a0] := by rw [htk]; exact hhead
  exact .tcon htrow hnd hargs' htd (by first | simp [mkAppN, mkApp] | (simp [mkAppN]; rfl))

/-! ## §4 Argument typing per row: `RowTeleEvAt` for a closed telescope of constant term binders

`RowTeleEvAt` (in `ShippingGen5ConstValueEVL`) is the residual of `OblPrimArgsV` after the conversion rule: per term binder, the binder type denotes the argument's Lean type; per type binder, the binder is a sort.
For a closed telescope whose binders are the constants `bs` (term arguments), it follows from two per-row facts: the row accepts only arguments of the Lean types `Ts` (`ArgsTySpec`), and each binder constant denotes its `T` at every valuation (`BindersDen`; `Sparkle.Core.Domain.ResetKind` is an alias, so its binder goes through `tdenv_const_unfold`). -/

def ConstPi : Expr → List (Name × List Level) → Expr → Prop
  | T, [], R => T = R
  | T, b :: bs, R => ∃ (x : Name) (B : Expr) (bi : BinderInfo), T = .forallE x (.const b.1 b.2) B bi ∧ lbr B = 0 ∧ ConstPi B bs R

def EnvConstPi (env : Environment) (c : Name) (ls : List Level) (bs : List (Name × List Level)) (R : Expr) : Prop :=
  ∀ ci : ConstantInfo, env.find? c = some ci → ConstPi (instantiateLevelParamsS ci.levelParams ls ci.type) bs R

/-- A nullary constant that is a DEFINITION (an alias such as `abbrev ResetKind := …`) denotes what its body denotes (`tunfold` with no arguments). -/
theorem tdenv_const_unfold {PT : PrimTableK} {env : Environment} {ρ : Val} {c : Name} {ls : List Level} {d : DefinitionVal} {T : Type}
    (hd : env.find? c = some (.defnInfo d)) (hb : TDenV PT env ρ (instantiateLevelParamsS d.levelParams ls d.value) T) :
    TDenV PT env ρ (.const c ls) T :=
  .tunfold (args := []) hd (by rw [betaS_nil]; exact hb) rfl

/-- Each binder constant denotes its Lean type at every valuation (by a `tys` row: `tdenv_const_nullary`, or, for an alias, by unfolding: `tdenv_const_unfold`). -/
def BindersDen (PT : PrimTableK) (env : Environment) : List (Name × List Level) → List Type → Prop
  | [], [] => True
  | b :: bs, T :: Ts => (∀ ρ : Val, TDenV PT env ρ (.const b.1 b.2) T) ∧ BindersDen PT env bs Ts
  | _, _ => False

def ArgsAreTys : List Arg → List Type → Prop
  | [], [] => True
  | .tm d :: as, T :: Ts => d.ty = T ∧ ArgsAreTys as Ts
  | _, _ => False

theorem bindersDen_length {PT : PrimTableK} {env : Environment} : ∀ {bs : List (Name × List Level)} {Ts : List Type}, BindersDen PT env bs Ts → Ts.length = bs.length
  | [], [], _ => rfl
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h
  | _ :: bs, _ :: Ts, h => by have := bindersDen_length (bs := bs) (Ts := Ts) h.2; simp [this]

/-- Spec of a row (about `PT`): one term argument per entry of `Ts`, and every accepted argument list consists of values of the Lean types `Ts`. -/
def ArgsTySpec (PT : PrimTableK) (c : Name) (ls : List Level) (Ts : List Type) : Prop :=
  ∃ row : TmRow, PT.tms c ls = some row ∧ row.kinds = List.replicate Ts.length true ∧ ∀ (as : List Arg) (d : Dyn), row.den as = some d → ArgsAreTys as Ts

theorem teleEv_constPi (PT : PrimTableK) (env : Environment) (ρ : Val) : ∀ (bs : List (Name × List Level)) (Ts : List Type) (T R : Expr) (es : List Expr) (as : List Arg),
    BindersDen PT env bs Ts → ConstPi T bs R → es.length = bs.length → ArgsAreTys as Ts →
    TeleEv PT env ρ T (List.replicate bs.length true) es as
  | [], Ts, T, R, es, as, hb, hT, hl, ha => by
    cases Ts with
    | nil =>
      have : es = [] := List.length_eq_zero_iff.mp hl
      cases as with
      | nil => subst this; exact .nil
      | cons _ _ => exact absurd ha (by simp [ArgsAreTys])
    | cons _ _ => exact False.elim hb
  | b :: bs, Ts, T, R, es, as, hb, hT, hl, ha => by
    cases Ts with
    | nil => exact False.elim hb
    | cons T0 Ts =>
      obtain ⟨hden, hb'⟩ := hb
      obtain ⟨x, B, bi, rfl, hB, hT'⟩ := hT
      cases es with
      | nil => simp at hl
      | cons a es =>
        cases as with
        | nil => exact absurd ha (by simp [ArgsAreTys])
        | cons arg as =>
          cases arg with
          | ty _ => exact absurd ha (by simp [ArgsAreTys])
          | tm d =>
            obtain ⟨hd, ha'⟩ := ha
            obtain ⟨TA, av⟩ := d
            simp only at hd
            subst hd
            have hA : TDenV PT env ρ (.const b.1 b.2) TA := hden ρ
            have ih := teleEv_constPi PT env ρ bs Ts B R es as hb' hT' (by simpa using hl) ha'
            exact .tm hA (by rw [substS_closed B hB a]; exact ih)

/-- `RowTeleEvAt` of a row over a closed constant-binder telescope, from the two per-row facts and the env fact. -/
theorem rowTeleEvAt_constPi (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (bs : List (Name × List Level)) (Ts : List Type) (R : Expr)
    (hr : ArgsTySpec PT c ls Ts) (hb : BindersDen PT env bs Ts) (hT : EnvConstPi env c ls bs R) : RowTeleEvAt PT env c ls := by
  obtain ⟨row0, hrow0, hk, hden⟩ := hr
  have hlen := bindersDen_length hb
  intro ρ args ci row as d hci hrow hargs hd
  rw [hrow0] at hrow; cases hrow
  rw [hk] at hargs ⊢
  rw [hlen] at hargs ⊢
  have hl : args.length = bs.length := by have := (argsdenv_length hargs).1; simpa using this
  exact teleEv_constPi PT env ρ bs Ts _ R args as hb (hT ci hci) hl (hden as d hd)

section teles
variable (PT : PrimTableK) (env : Environment)

theorem teleEv_Nat_succ (hr : ArgsTySpec PT ``Nat.succ [] [Nat]) (hb : BindersDen PT env [(``Nat, [])] [Nat])
    (hT : EnvConstPi env ``Nat.succ [] [(``Nat, [])] (.const ``Nat [])) : RowTeleEvAt PT env ``Nat.succ [] :=
  rowTeleEvAt_constPi PT env _ _ _ _ _ hr hb hT

theorem teleEv_Int_ofNat (hr : ArgsTySpec PT ``Int.ofNat [] [Nat]) (hb : BindersDen PT env [(``Nat, [])] [Nat])
    (hT : EnvConstPi env ``Int.ofNat [] [(``Nat, [])] (.const ``Int [])) : RowTeleEvAt PT env ``Int.ofNat [] :=
  rowTeleEvAt_constPi PT env _ _ _ _ _ hr hb hT

theorem teleEv_Int_negSucc (hr : ArgsTySpec PT ``Int.negSucc [] [Nat]) (hb : BindersDen PT env [(``Nat, [])] [Nat])
    (hT : EnvConstPi env ``Int.negSucc [] [(``Nat, [])] (.const ``Int [])) : RowTeleEvAt PT env ``Int.negSucc [] :=
  rowTeleEvAt_constPi PT env _ _ _ _ _ hr hb hT

theorem teleEv_DomainConfig_mk (hr : ArgsTySpec PT `Sparkle.Core.Domain.DomainConfig.mk [] [Nat, Sparkle.Core.Domain.ActiveEdge, Sparkle.IR.Type.ResetKind])
    (hb : BindersDen PT env [(``Nat, []), (`Sparkle.Core.Domain.ActiveEdge, []), (`Sparkle.Core.Domain.ResetKind, [])]
      [Nat, Sparkle.Core.Domain.ActiveEdge, Sparkle.IR.Type.ResetKind])
    (hT : EnvConstPi env `Sparkle.Core.Domain.DomainConfig.mk [] [(``Nat, []), (`Sparkle.Core.Domain.ActiveEdge, []), (`Sparkle.Core.Domain.ResetKind, [])]
      (.const `Sparkle.Core.Domain.DomainConfig [])) : RowTeleEvAt PT env `Sparkle.Core.Domain.DomainConfig.mk [] :=
  rowTeleEvAt_constPi PT env _ _ _ _ _ hr hb hT

end teles

/-! ## §5 The old carrier `CVEKS` against `CVEKVL`: what is and is not mapped (item 4)

A MAP of derivations `CVEKS ⇒ CVEKVL` is not built (reasons in draft §V2: the `lam` rule shares one body label for all `a`, the `app` / `letE` labels differ, label uniformity needs derivations at valuations whose Lean types differ).
What IS proved is the rule-level correspondence: the conclusion of the OLD `app` / `letE` rules is a `conv` of the new rules' conclusion, exactly when the substituted label denotes the same Lean type
(`hsub`: the V form of one instance of `OblDenSubstS`). So the old rule is derivable from the new rule plus that instance; no more, and no less, is needed. -/

/-- Old `app` conclusion (label `substS B 0 x`) from the new rule and one instance of the substitution fact `hsub`. The premises other than `hsub` are those of `CVEKVB.app`. -/
theorem cvekv_app_old_of_new {PT : PrimTableK} {env : Environment} {ρ : Val} {fe x A B : Expr} {n : Name} {bi : BinderInfo} {TA : Type} (TB : TA → Type)
    {fv : (a : TA) → TB a} {av : TA}
    (hA : TDenV PT env ρ A TA) (hB : ∀ a : TA, TDenV PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a))
    (hf : CVEKVB PT env ρ fe (.forallE n A B bi) ((a : TA) → TB a) fv) (hx : CVEKV PT env ρ x A TA av)
    (hnh : ¬ ∃ (c : Name) (ls : List Level), fe.getAppFn = .const c ls)
    (hsub : TDenV PT env ρ (substS B 0 x) (TB av)) :
    CVEKV PT env ρ (.app fe x) (substS B 0 x) (TB av) (fv av) :=
  .conv (CVEKVB.app TB hA hB hf hx hnh) (.tlet hA hx (hB av)) hsub

/-- Old `letE` conclusion (label `substS B 0 v`) from the new rule and the substitution fact. -/
theorem cvekv_letE_old_of_new {PT : PrimTableK} {env : Environment} {ρ : Val} {n : Name} {A v b B : Expr} {nd : Bool} {TA : Type} {TB : Type} {av : TA} {bv : TB}
    (hA : TDenV PT env ρ A TA) (hv : CVEKV PT env ρ v A TA av) (hb : CVEKVB PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) b B TB bv)
    (hB : TDenV PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) B TB) (hsub : TDenV PT env ρ (substS B 0 v) TB) :
    CVEKV PT env ρ (.letE n A v b nd) (substS B 0 v) TB bv :=
  .conv (CVEKVB.letE hA hv hb) (.tlet hA hv hB) hsub

end Tools.ShippingGen5RowTypedV
