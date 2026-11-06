import Tools.ShippingFGCircuitFunc
set_option autoImplicit false
-- FG circuit pilot S1m: the environment-tied extension CDX of the applied-unit denotation CD (FREEZE DRAFT, docs/FG-CIRCUIT-PILOT.md §17).
-- No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # `CDX`: `CD` plus (1) unfolding a user definition of the environment, (2) structure projection

`CD` (Tools/ShippingFGCircuit.lean) has no rule for a user constant and none for `Expr.proj`. This file defines a NEW pair `TDX`/`CDX`, parameterised by a FIXED
`env : Environment`, that contains every rule of `TD`/`CD` unchanged (`cdx_of_cd`) and four new rules. Nothing in the existing files is edited.

New rules (each mirrors a Lean operation: delta/beta/zeta/projection/iota. That the rewrite preserves the meaning of the original Lean term is NOT proved here; see docs §17.8):

* `unf`      delta + beta: `e = c.{ls} args` with `c` a `defnInfo` of `env` that is NOT a primitive head of `CD`; the denotation of `e` is the denotation of
             `(d.value)[levelParams := ls] args` (beta). Termination: a derivation is a finite tree (inductive `Prop`); for a recursive or cyclic definition `unf` alone does not close a derivation (a traversal stops there; the derivation is unsupplied, which is not a non-existence proof). There is no fuel and no size measure; functionality is proved by recursion on the derivation, not on the expression.
* `zeta`     `let x : A := v; b` with `A` not a core type head: denote `b[x := v]`. (For a core type `A` the old `letE` rule applies; the two never overlap.)
* `projStep` `e = Expr.proj S i x`, one weak-head step of the structure argument `x` (`whStep`: zeta, beta, or delta of a `defnInfo`): denote `Expr.proj S i x'`.
* `projCtor` `e = Expr.proj S i x` with `x = ctor params fields`, `ctor` a `ctorInfo` of `env` whose inductive is `S`: denote the `i`-th field (iota).

The `bvar` valuation `ρ` is untouched by the new rules, so substituted arguments may mention it (`instE` lifts loose bvars, as `Expr.instantiate` does). -/
namespace Tools.ShippingFGCircuitS1mCD
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5ConstValueE Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit

/-! ## 1. kernel-evaluable Expr operations (own definitions: `Expr.instantiate` is an opaque extern) -/

def appFn : Expr → Expr
  | .app f _ => appFn f
  | e => e

def appArgs : Expr → List Expr
  | .app f a => appArgs f ++ [a]
  | _ => []

def mkApps : Expr → List Expr → Expr
  | f, [] => f
  | f, a :: xs => mkApps (.app f a) xs

/-- lift the loose bvars `≥ k` by `n` -/
def liftE : Expr → Nat → Nat → Expr
  | .bvar i, n, k => if i < k then .bvar i else .bvar (i + n)
  | .app f a, n, k => .app (liftE f n k) (liftE a n k)
  | .lam x t b bi, n, k => .lam x (liftE t n k) (liftE b n (k + 1)) bi
  | .forallE x t b bi, n, k => .forallE x (liftE t n k) (liftE b n (k + 1)) bi
  | .letE x t v b nd, n, k => .letE x (liftE t n k) (liftE v n k) (liftE b n (k + 1)) nd
  | .mdata m e, n, k => .mdata m (liftE e n k)
  | .proj s i e, n, k => .proj s i (liftE e n k)
  | e, _, _ => e

/-- `instE b s k`: replace the bvar `k` of `b` by `s` (lifted under the binders passed) and lower the bvars above `k` -/
def instE : Expr → Expr → Nat → Expr
  | .bvar i, s, k => if i < k then .bvar i else if i == k then liftE s k 0 else .bvar (i - 1)
  | .app f a, s, k => .app (instE f s k) (instE a s k)
  | .lam x t b bi, s, k => .lam x (instE t s k) (instE b s (k + 1)) bi
  | .forallE x t b bi, s, k => .forallE x (instE t s k) (instE b s (k + 1)) bi
  | .letE x t v b nd, s, k => .letE x (instE t s k) (instE v s k) (instE b s (k + 1)) nd
  | .mdata m e, s, k => .mdata m (instE e s k)
  | .proj n i e, s, k => .proj n i (instE e s k)
  | e, _, _ => e

/-- `(fun x₁ … => b) a₁ … ` : beta for as many arguments as there are binders -/
def betaApp : Expr → List Expr → Expr
  | f, [] => f
  | .lam _ _ b _, a :: xs => betaApp (instE b a 0) xs
  | f, a :: xs => mkApps f (a :: xs)

def lookupL : List Name → List Level → Name → Level
  | p :: ps, l :: ls, n => if p == n then l else lookupL ps ls n
  | _, _, n => .param n

def instL (ps : List Name) (ls : List Level) : Level → Level
  | .succ l => .succ (instL ps ls l)
  | .max a b => .max (instL ps ls a) (instL ps ls b)
  | .imax a b => .imax (instL ps ls a) (instL ps ls b)
  | .param n => lookupL ps ls n
  | l => l

/-- instantiate the universe parameters `ps := ls` -/
def instLE (ps : List Name) (ls : List Level) : Expr → Expr
  | .sort u => .sort (instL ps ls u)
  | .const c us => .const c (us.map (instL ps ls))
  | .app f a => .app (instLE ps ls f) (instLE ps ls a)
  | .lam x t b bi => .lam x (instLE ps ls t) (instLE ps ls b) bi
  | .forallE x t b bi => .forallE x (instLE ps ls t) (instLE ps ls b) bi
  | .letE x t v b nd => .letE x (instLE ps ls t) (instLE ps ls v) (instLE ps ls b) nd
  | .mdata m e => .mdata m (instLE ps ls e)
  | .proj s i e => .proj s i (instLE ps ls e)
  | e => e

/-- delta (+ beta) of the head constant of `e`, when it is a `defnInfo` of `env` with the right number of levels -/
def unfoldAt (env : Environment) (e : Expr) : Option Expr :=
  match appFn e with
  | .const c ls =>
    match env.find? c with
    | some (.defnInfo d) =>
      if d.levelParams.length = ls.length then some (betaApp (instLE d.levelParams ls d.value) (appArgs e)) else none
    | _ => none
  | _ => none

/-- iota for `Expr.proj s j y` when `y` is a saturated constructor application of the inductive `s` -/
def iotaAt (env : Environment) (s : Name) (j : Nat) (y : Expr) : Option Expr :=
  match appFn y with
  | .const c _ =>
    match env.find? c with
    | some (.ctorInfo cv) =>
      if cv.induct == s && (appArgs y).length == cv.numParams + cv.numFields then (appArgs y)[cv.numParams + j]? else none
    | _ => none
  | _ => none

/-- one weak-head step of a structure argument, one application argument at a time: zeta, beta, delta of the head constant, a step under a projection, or iota of a projection -/
def whStep (env : Environment) : Expr → Option Expr
  | .letE _ _ v b _ => some (instE b v 0)
  | .proj s j y =>
    match whStep env y with
    | some y' => some (.proj s j y')
    | none => iotaAt env s j y
  | .app f a =>
    match f with
    | .lam _ _ b _ => some (instE b a 0)
    | .letE _ _ v b _ => some (.app (instE b v 0) a)
    | _ => (whStep env f).map fun f' => .app f' a
  | x => unfoldAt env x

/-- a head redex of the expression itself that is not a delta step of a constant: a beta redex `(fun x => b) a …`, a `let` applied to arguments `(let x := v; b) a …`, or a projection applied to arguments `(p.i) a …` whose head steps (`whStep`) -/
def headRedex (env : Environment) (e : Expr) : Option Expr :=
  match appFn e, appArgs e with
  | .lam .., _ :: _ => some (betaApp (appFn e) (appArgs e))
  | .letE _ _ v b _, _ :: _ => some (mkApps (instE b v 0) (appArgs e))
  | .proj s j y, _ :: _ => (whStep env (.proj s j y)).map fun h' => mkApps h' (appArgs e)
  | _, _ => none

/-- the heads of the primitive rules of `CD` (a `defnInfo` among them must not be unfolded: the primitive rule is the meaning) -/
def primHeads : List Name :=
  [``OfNat.ofNat, ``Sparkle.Core.Domain.defaultDomain, ``BitVec.ofNat, ``BitVec.instInhabited, ``instInhabitedBool, ``Signal.pure, ``Signal.register,
   ``Signal.mux, ``HAdd.hAdd, ``Signal.loop, ``Sparkle.Core.Signal.Signal.beq, ``HAnd.hAnd, ``HOr.hOr, ``Complement.complement]

/-- `c` is not unfolded by `unf`: a primitive head, or a `bvAbbrev` row -/
def stopC (c : Name) : Bool := primHeads.contains c || (bvAbbrevRow c).isSome

/-- the head of `e` is a stop constant -/
def headStop (e : Expr) : Bool :=
  match appFn e with
  | .const c _ => stopC c
  | _ => false

/-- the type heads `TD` knows; `zeta` is for a `let` whose type has another head -/
def coreHead (A : Expr) : Bool :=
  match appFn A with
  | .const c _ => [``Nat, ``Bool, ``Sparkle.Core.Domain.DomainConfig, ``BitVec, ``Signal].contains c
  | _ => false

/-! ## 2. the relation -/

/-- the result of a judgement: a type (`TDX`) or a typed value (`CDX`). One inductive family, so that the functionality proof is an `induction` on the derivation. -/
inductive Res : Type 1
  | ty (T : Type) : Res
  | val (α : Type) (v : α) : Res

section
local macro "CDx " env:term:max ρ:term:max e:term:max α:term:max v:term:max : term => `($(Lean.mkIdent `Tools.ShippingFGCircuitS1mCD.DX) $env $ρ $e (Res.val $α $v))
local macro "TDx " env:term:max ρ:term:max e:term:max T:term:max : term => `($(Lean.mkIdent `Tools.ShippingFGCircuitS1mCD.DX) $env $ρ $e (Res.ty $T))
inductive DX (env : Environment) : Val → Expr → Res → Prop
  | nat {ρ : Val} {e : Expr} (he : e = .const ``Nat []) : TDx env ρ e Nat
  | bool {ρ : Val} {e : Expr} (he : e = .const ``Bool []) : TDx env ρ e Bool
  | domainConfig {ρ : Val} {e : Expr} (he : e = .const ``Sparkle.Core.Domain.DomainConfig []) : TDx env ρ e DomainConfig
  | bitvec {ρ : Val} {e w : Expr} {n : Nat} (he : e = appN ``BitVec [] [w]) (hw : CDx env ρ w Nat n) : TDx env ρ e (BitVec n)
  | signal {ρ : Val} {e d t : Expr} {D : DomainConfig} {T : Type} (he : e = appN ``Signal [.zero] [d, t])
      (hd : CDx env ρ d DomainConfig D) (ht : TDx env ρ t T) : TDx env ρ e (Signal D T)

  | bvar {ρ : Val} {i : Nat} {τ : Expr} {T : Type} {a : T} (h : ρ[i]? = some ⟨τ, ⟨T, a⟩⟩) : CDx env ρ (.bvar i) T a
  | natLit {ρ : Val} {e : Expr} {n : Nat}
      (he : e = appN ``OfNat.ofNat [.zero] [.const ``Nat [], .lit (.natVal n), appN ``instOfNatNat [] [.lit (.natVal n)]]) :
      CDx env ρ e Nat n
  | domDefault {ρ : Val} {e : Expr} (he : e = .const ``Sparkle.Core.Domain.defaultDomain []) :
      CDx env ρ e DomainConfig defaultDomain
  | bvOfNat {ρ : Val} {e w k : Expr} {W K : Nat} (he : e = appN ``BitVec.ofNat [] [w, k])
      (hw : CDx env ρ w Nat W) (hk : CDx env ρ k Nat K) : CDx env ρ e (BitVec W) (BitVec.ofNat W K)
  | bvInhabited {ρ : Val} {e w : Expr} {W : Nat} (he : e = appN ``BitVec.instInhabited [] [w]) (hw : CDx env ρ w Nat W) :
      CDx env ρ e (Inhabited (BitVec W)) (inferInstance : Inhabited (BitVec W))
  | boolInhabited {ρ : Val} {e : Expr} (he : e = .const ``instInhabitedBool []) :
      CDx env ρ e (Inhabited Bool) (inferInstance : Inhabited Bool)
  | sigPure {ρ : Val} {e d t x : Expr} {D : DomainConfig} {T : Type} {a : T}
      (he : e = appN ``Signal.pure [.zero] [d, t, x]) (hd : CDx env ρ d DomainConfig D) (ht : TDx env ρ t T) (hx : CDx env ρ x T a) :
      CDx env ρ e (Signal D T) (Signal.pure a)
  | sigRegister {ρ : Val} {e d t i s : Expr} {D : DomainConfig} {T : Type} {a : T} {sv : Signal D T}
      (he : e = appN ``Signal.register [.zero] [d, t, i, s]) (hd : CDx env ρ d DomainConfig D) (ht : TDx env ρ t T)
      (hi : CDx env ρ i T a) (hs : CDx env ρ s (Signal D T) sv) : CDx env ρ e (Signal D T) (Signal.register a sv)
  | sigMux {ρ : Val} {e d t c a b : Expr} {D : DomainConfig} {T : Type} {cv : Signal D Bool} {av bv : Signal D T}
      (he : e = appN ``Signal.mux [.zero] [d, t, c, a, b]) (hd : CDx env ρ d DomainConfig D) (ht : TDx env ρ t T)
      (hc : CDx env ρ c (Signal D Bool) cv) (ha : CDx env ρ a (Signal D T) av) (hb : CDx env ρ b (Signal D T) bv) :
      CDx env ρ e (Signal D T) (Signal.mux cv av bv)
  | sigAddBV {ρ : Val} {e d w a b : Expr} {D : DomainConfig} {W : Nat} {av bv : Signal D (BitVec W)}
      (he : e = appN ``HAdd.hAdd [.zero, .zero, .zero]
        [appN ``Signal [.zero] [d, appN ``BitVec [] [w]], appN ``Signal [.zero] [d, appN ``BitVec [] [w]],
         appN ``Signal [.zero] [d, appN ``BitVec [] [w]], appN ``Sparkle.Core.Signal.instHAddSignalBitVec [] [d, w], a, b])
      (hd : CDx env ρ d DomainConfig D) (hw : CDx env ρ w Nat W)
      (ha : CDx env ρ a (Signal D (BitVec W)) av) (hb : CDx env ρ b (Signal D (BitVec W)) bv) :
      CDx env ρ e (Signal D (BitVec W)) (@HAdd.hAdd _ _ _ (@Sparkle.Core.Signal.instHAddSignalBitVec D W) av bv)
  | sigLoop {ρ : Val} {e d t inst f : Expr} {D : DomainConfig} {T : Type} {iv : Inhabited T} {g : Signal D T → Signal D T}
      (he : e = appN ``Signal.loop [] [d, t, inst, f]) (hd : CDx env ρ d DomainConfig D) (ht : TDx env ρ t T)
      (hi : CDx env ρ inst (Inhabited T) iv) (hf : CDx env ρ f (Signal D T → Signal D T) g) :
      CDx env ρ e (Signal D T) (@Signal.loop D T iv g)
  | lam {ρ : Val} {e A body : Expr} {n : Name} {bi : BinderInfo} {TA : Type} {TB : TA → Type} {f : (a : TA) → TB a}
      (he : e = .lam n A body bi) (hA : TDx env ρ A TA) (hb : ∀ a : TA, CDx env (⟨A, ⟨TA, a⟩⟩ :: ρ) body (TB a) (f a)) :
      CDx env ρ e ((a : TA) → TB a) f
  | letE {ρ : Val} {e A v body : Expr} {n : Name} {nd : Bool} {TA T : Type} {a : TA} {r : T}
      (he : e = .letE n A v body nd) (hA : TDx env ρ A TA) (hv : CDx env ρ v TA a) (hb : CDx env (⟨A, ⟨TA, a⟩⟩ :: ρ) body T r) : CDx env ρ e T r
  | sigBeqBV {ρ : Val} {e d w a b : Expr} {D : DomainConfig} {W : Nat} {av bv : Signal D (BitVec W)}
      (he : e = appN ``Sparkle.Core.Signal.Signal.beq []
        [appN ``BitVec [] [w], d, appN ``instBEqOfDecidableEq [.zero] [appN ``BitVec [] [w], appN ``instDecidableEqBitVec [] [w]], a, b])
      (hd : CDx env ρ d DomainConfig D) (hw : CDx env ρ w Nat W)
      (ha : CDx env ρ a (Signal D (BitVec W)) av) (hb : CDx env ρ b (Signal D (BitVec W)) bv) :
      CDx env ρ e (Signal D Bool) (@Signal.beq (BitVec W) D (@instBEqOfDecidableEq (BitVec W) (@instDecidableEqBitVec W)) av bv)
  | sigAndBool {ρ : Val} {e d a b : Expr} {D : DomainConfig} {av bv : Signal D Bool}
      (he : e = appN ``HAnd.hAnd [.zero, .zero, .zero]
        [appN ``Signal [.zero] [d, .const ``Bool []], appN ``Signal [.zero] [d, .const ``Bool []],
         appN ``Signal [.zero] [d, .const ``Bool []], appN ``Sparkle.Core.Signal.instHAndSignalBool [] [d], a, b])
      (hd : CDx env ρ d DomainConfig D) (ha : CDx env ρ a (Signal D Bool) av) (hb : CDx env ρ b (Signal D Bool) bv) :
      CDx env ρ e (Signal D Bool) (@HAnd.hAnd _ _ _ (@Sparkle.Core.Signal.instHAndSignalBool D) av bv)
  | sigOrBool {ρ : Val} {e d a b : Expr} {D : DomainConfig} {av bv : Signal D Bool}
      (he : e = appN ``HOr.hOr [.zero, .zero, .zero]
        [appN ``Signal [.zero] [d, .const ``Bool []], appN ``Signal [.zero] [d, .const ``Bool []],
         appN ``Signal [.zero] [d, .const ``Bool []], appN ``Sparkle.Core.Signal.instHOrSignalBool [] [d], a, b])
      (hd : CDx env ρ d DomainConfig D) (ha : CDx env ρ a (Signal D Bool) av) (hb : CDx env ρ b (Signal D Bool) bv) :
      CDx env ρ e (Signal D Bool) (@HOr.hOr _ _ _ (@Sparkle.Core.Signal.instHOrSignalBool D) av bv)
  | sigNotBool {ρ : Val} {e d a : Expr} {D : DomainConfig} {av : Signal D Bool}
      (he : e = appN ``Complement.complement [.zero]
        [appN ``Signal [.zero] [d, .const ``Bool []], appN ``Sparkle.Core.Signal.instComplementSignalBool [] [d], a])
      (hd : CDx env ρ d DomainConfig D) (ha : CDx env ρ a (Signal D Bool) av) :
      CDx env ρ e (Signal D Bool) (@Complement.complement _ (@Sparkle.Core.Signal.instComplementSignalBool D) av)
  | bvAbbrev {ρ : Val} {e : Expr} {c : Name} {n : Nat} {v : BitVec n} (he : e = .const c []) (h : bvAbbrevRow c = some ⟨n, v⟩) :
      CDx env ρ e (BitVec n) v
  /-- NEW. delta + beta of a user definition of `env` (`unfoldAt`: the head is a `defnInfo` of `env` with matching universe arity), the head not a stop constant. The value is the value of the unfolded expression. -/
  | unf {ρ : Val} {e e' : Expr} {α : Type} {v : α}
      (hs : headStop e = false) (hu : unfoldAt env e = some e') (h : CDx env ρ e' α v) : CDx env ρ e α v
  /-- NEW. a head redex (`headRedex`: beta, let-application, projection-application) of the expression itself (arguments substituted by `unf` can create it). -/
  | beta {ρ : Val} {e e' : Expr} {α : Type} {v : α}
      (hb : headRedex env e = some e') (h : CDx env ρ e' α v) : CDx env ρ e α v
  /-- NEW. `let` of a non-core type: substitute (the old `letE` handles core types). -/
  | zeta {ρ : Val} {e A v body : Expr} {n : Name} {nd : Bool} {α : Type} {r : α}
      (he : e = .letE n A v body nd) (hA : coreHead A = false) (h : CDx env ρ (instE body v 0) α r) : CDx env ρ e α r
  /-- NEW. a weak-head step of the structure argument of a projection. -/
  | projStep {ρ : Val} {e x x' : Expr} {S : Name} {i : Nat} {α : Type} {v : α}
      (he : e = .proj S i x) (hx : whStep env x = some x') (h : CDx env ρ (.proj S i x') α v) : CDx env ρ e α v
  /-- NEW. projection of a constructor application (iota); `ctor` is a `ctorInfo` of `env` of the inductive `S`. -/
  | projCtor {ρ : Val} {e x fld : Expr} {S ctor : Name} {ls : List Level} {cv : ConstructorVal} {i : Nat} {α : Type} {v : α}
      (he : e = .proj S i x) (hh : appFn x = .const ctor ls) (hc : env.find? ctor = some (.ctorInfo cv)) (hS : cv.induct = S)
      (hn : (appArgs x).length = cv.numParams + cv.numFields) (hf : (appArgs x)[cv.numParams + i]? = some fld)
      (h : CDx env ρ fld α v) : CDx env ρ e α v
end

abbrev TDX (env : Environment) (ρ : Val) (e : Expr) (T : Type) : Prop := DX env ρ e (.ty T)
abbrev CDX (env : Environment) (ρ : Val) (e : Expr) (α : Type) (v : α) : Prop := DX env ρ e (.val α v)

/-! ## 3. the embedding `CD → CDX` -/

theorem appN_1' (c : Name) (ls : List Level) (a : Expr) : appN c ls [a] = .app (.const c ls) a := rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
mutual
theorem tdx_of_td {env : Environment} {ρ : Val} {e : Expr} {T : Type} (h : TD ρ e T) : TDX env ρ e T := by
  cases h with
  | nat he => exact .nat he
  | bool he => exact .bool he
  | domainConfig he => exact .domainConfig he
  | bitvec he hw => exact .bitvec he (cdx_of_cd hw)
  | signal he hd ht => exact .signal he (cdx_of_cd hd) (tdx_of_td ht)
termination_by sizeOf e
decreasing_by all_goals (simp_wf; first | (subst_vars; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.sizeOf_spec, Expr.lam.sizeOf_spec, Expr.letE.sizeOf_spec, Expr.const.sizeOf_spec]; omega) | (trace_state; fail))

theorem cdx_of_cd {env : Environment} {ρ : Val} {e : Expr} {α : Type} {v : α} (h : CD ρ e α v) : CDX env ρ e α v := by
  cases h with
  | bvar hb => exact .bvar hb
  | natLit he => exact .natLit he
  | domDefault he => exact .domDefault he
  | bvOfNat he hw hk => exact .bvOfNat he (cdx_of_cd hw) (cdx_of_cd hk)
  | bvInhabited he hw => exact .bvInhabited he (cdx_of_cd hw)
  | boolInhabited he => exact .boolInhabited he
  | sigPure he hd ht hx => exact .sigPure he (cdx_of_cd hd) (tdx_of_td ht) (cdx_of_cd hx)
  | sigRegister he hd ht hi hs => exact .sigRegister he (cdx_of_cd hd) (tdx_of_td ht) (cdx_of_cd hi) (cdx_of_cd hs)
  | sigMux he hd ht hc ha hb => exact .sigMux he (cdx_of_cd hd) (tdx_of_td ht) (cdx_of_cd hc) (cdx_of_cd ha) (cdx_of_cd hb)
  | sigAddBV he hd hw ha hb => exact .sigAddBV he (cdx_of_cd hd) (cdx_of_cd hw) (cdx_of_cd ha) (cdx_of_cd hb)
  | sigLoop he hd ht hi hf => exact .sigLoop he (cdx_of_cd hd) (tdx_of_td ht) (cdx_of_cd hi) (cdx_of_cd hf)
  | lam he hA hb => exact .lam he (tdx_of_td hA) (fun a => cdx_of_cd (hb a))
  | letE he hA hv hb => exact .letE he (tdx_of_td hA) (cdx_of_cd hv) (cdx_of_cd hb)
  | sigBeqBV he hd hw ha hb => exact .sigBeqBV he (cdx_of_cd hd) (cdx_of_cd hw) (cdx_of_cd ha) (cdx_of_cd hb)
  | sigAndBool he hd ha hb => exact .sigAndBool he (cdx_of_cd hd) (cdx_of_cd ha) (cdx_of_cd hb)
  | sigOrBool he hd ha hb => exact .sigOrBool he (cdx_of_cd hd) (cdx_of_cd ha) (cdx_of_cd hb)
  | sigNotBool he hd ha => exact .sigNotBool he (cdx_of_cd hd) (cdx_of_cd ha)
  | bvAbbrev he hr => exact .bvAbbrev he hr
termination_by sizeOf e
decreasing_by all_goals (simp_wf; first | (subst_vars; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.sizeOf_spec, Expr.lam.sizeOf_spec, Expr.letE.sizeOf_spec, Expr.const.sizeOf_spec]; omega) | (trace_state; fail))
end

/-- the circuit-core denotation of a declaration, over an environment: `CircCV` with `CDX env` -/
def CircCVX (env : Environment) : ConstValueRel := fun env' X α v =>
  ∃ d : DefinitionVal, env'.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ CDX env [] d.value α v

theorem circCV_to_X (env : Environment) {X : Name} {α : Type} {v : α} (h : CircCV env X α v) : CircCVX env env X α v := by
  obtain ⟨d, hd, hl, hv⟩ := h
  exact ⟨d, hd, hl, cdx_of_cd hv⟩

/-! ## 4. functionality: by induction on the first derivation (NOT on the size of the expression: `unf` makes the expression larger) -/

theorem stopC_ofNat : stopC ``OfNat.ofNat = true := by decide
theorem stopC_defaultDomain : stopC ``Sparkle.Core.Domain.defaultDomain = true := by decide
theorem stopC_bvOfNat : stopC ``BitVec.ofNat = true := by decide
theorem stopC_bvInh : stopC ``BitVec.instInhabited = true := by decide
theorem stopC_boolInh : stopC ``instInhabitedBool = true := by decide
theorem stopC_pure : stopC ``Signal.pure = true := by decide
theorem stopC_register : stopC ``Signal.register = true := by decide
theorem stopC_mux : stopC ``Signal.mux = true := by decide
theorem stopC_hadd : stopC ``HAdd.hAdd = true := by decide
theorem stopC_loop : stopC ``Signal.loop = true := by decide
theorem stopC_beq : stopC ``Sparkle.Core.Signal.Signal.beq = true := by decide
theorem stopC_hand : stopC ``HAnd.hAnd = true := by decide
theorem stopC_hor : stopC ``HOr.hOr = true := by decide
theorem stopC_compl : stopC ``Complement.complement = true := by decide

theorem stopC_of_row {c : Name} {r : Σ n : Nat, BitVec n} (h : bvAbbrevRow c = some r) : stopC c = true := by
  simp [stopC, h]

theorem appFn_appN (c : Name) (ls : List Level) (args : List Expr) : appFn (appN c ls args) = .const c ls := by
  unfold appN mkAppN
  rw [← Array.foldl_toList]
  simp only [List.toList_toArray]
  suffices ∀ (f : Expr) (xs : List Expr), appFn f = .const c ls → appFn (xs.foldl mkApp f) = .const c ls from this _ _ rfl
  intro f xs
  induction xs generalizing f with
  | nil => intro h; exact h
  | cons a xs ih => intro h; exact ih (mkApp f a) (by simpa [mkApp, appFn] using h)

theorem coreHead_td {env : Environment} {ρ : Val} {A : Expr} {T : Type} (h : TDX env ρ A T) : coreHead A = true := by
  cases h with
  | nat he => subst he; decide
  | bool he => subst he; decide
  | domainConfig he => subst he; decide
  | bitvec he hw => subst he; simp [coreHead, appFn_appN]
  | signal he hd ht => subst he; simp [coreHead, appFn_appN]

/-- the kind of a judgement: a type or a value (functionality is per kind: an expression is not both) -/
def Res.kind : Res → Bool
  | .ty _ => false
  | .val _ _ => true

theorem val_inj {α α' : Type} {v : α} {v' : α'} (h : Res.val α v = Res.val α' v') : α = α' ∧ HEq v v' := by
  injection h with h1 h2; exact ⟨h1, h2⟩
theorem val_eq {α : Type} {v v' : α} (h : Res.val α v = Res.val α v') : v = v' := eq_of_heq (val_inj h).2
theorem ty_eq {T T' : Type} (h : Res.ty T = Res.ty T') : T = T' := by injection h

theorem unfoldAt_bvar (env : Environment) (i : Nat) : unfoldAt env (.bvar i) = none := by simp [unfoldAt, appFn]
theorem unfoldAt_lam (env : Environment) (n : Name) (A b : Expr) (bi : BinderInfo) : unfoldAt env (.lam n A b bi) = none := by simp [unfoldAt, appFn]
theorem unfoldAt_letE (env : Environment) (n : Name) (A v b : Expr) (nd : Bool) : unfoldAt env (.letE n A v b nd) = none := by simp [unfoldAt, appFn]
theorem unfoldAt_proj (env : Environment) (S : Name) (i : Nat) (x : Expr) : unfoldAt env (.proj S i x) = none := by simp [unfoldAt, appFn]

theorem headRedex_const {env : Environment} {x : Expr} {c : Name} {ls : List Level} (hh : appFn x = .const c ls) : headRedex env x = none := by
  simp [headRedex, hh]

theorem unfoldAt_none_of_beta {env : Environment} {e : Expr} (h : (headRedex env e).isSome = true) : unfoldAt env e = none := by
  cases hf : appFn e <;> simp [headRedex, unfoldAt, hf] at h ⊢

macro "clashx" : tactic =>
  `(tactic| (exfalso
             try subst_vars
             try simp_all [Res.kind, headStop, appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, appFn, stopC_ofNat, stopC_defaultDomain, stopC_bvOfNat, stopC_bvInh,
               stopC_boolInh, stopC_pure, stopC_register, stopC_mux, stopC_hadd, stopC_loop, stopC_beq, stopC_hand, stopC_hor, stopC_compl, bvAbbrevRow_defaultDomain,
               bvAbbrevRow_instInhabitedBool, stopC_of_row, unfoldAt_bvar, unfoldAt_lam, unfoldAt_letE, unfoldAt_proj]
             try simp_all [Res.kind, headStop, headRedex, appArgs, appFn, appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, unfoldAt_none_of_beta]))

theorem whStep_ctor {env : Environment} {ctor : Name} {ls : List Level} {cv : ConstructorVal} (hc : env.find? ctor = some (.ctorInfo cv)) :
    ∀ x : Expr, appFn x = .const ctor ls → whStep env x = none := by
  intro x
  induction x with
  | const c l =>
    intro hh
    simp only [appFn, Expr.const.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    simp [whStep, unfoldAt, appFn, hc]
  | app f a ihf _ =>
    intro hh
    have hf : appFn f = .const ctor ls := by simpa [appFn] using hh
    have := ihf hf
    cases f <;> first | (simp [appFn] at hf; done) | simp_all [whStep]
  | _ => intro hh; simp [appFn] at hh

macro "injx" he:ident he':ident : tactic =>
  `(tactic| (have h := Eq.trans (Eq.symm $he) $he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.proj.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **functionality** of the relation: two derivations of the same expression in the same valuation, of the same kind (both a type, or both a value), have the same result (the type; or the type and the value). -/
theorem dx_fun {env : Environment} {ρ : Val} {e : Expr} {r : Res} (h : DX env ρ e r) : ∀ {r' : Res}, DX env ρ e r' → r.kind = r'.kind → r = r' := by
  induction h with
  | nat he => intro r' h' hk; cases h' with
    | nat he' => rfl
    | _ => clashx
  | bool he => intro r' h' hk; cases h' with
    | bool he' => rfl
    | _ => clashx
  | domainConfig he => intro r' h' hk; cases h' with
    | domainConfig he' => rfl
    | _ => clashx
  | bitvec he hw ihw => intro r' h' hk; cases h' with
    | bitvec he' hw' =>
      injx he he'
      have := val_eq (ihw hw' rfl)
      subst this; rfl
    | _ => clashx
  | signal he hd ht ihd iht => intro r' h' hk; cases h' with
    | signal he' hd' ht' =>
      injx he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2; rfl
    | _ => clashx
  | bvar hb => intro r' h' hk; cases h' with
    | bvar hb' =>
      have := Option.some.inj (hb.symm.trans hb')
      cases this
      rfl
    | _ => clashx
  | natLit he => intro r' h' hk; cases h' with
    | natLit he' =>
      injx he he'
      rfl
    | _ => clashx
  | domDefault he => intro r' h' hk; cases h' with
    | domDefault he' => rfl
    | bvAbbrev he' hr' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_defaultDomain] at hr'; cases hr'
    | _ => clashx
  | bvOfNat he hw hk ihw ihk => intro r' h' hk; cases h' with
    | bvOfNat he' hw' hk' =>
      injx he he'
      have h1 := val_eq (ihw hw' rfl)
      subst h1
      have h2 := val_eq (ihk hk' rfl)
      subst h2; rfl
    | _ => clashx
  | bvInhabited he hw ihw => intro r' h' hk; cases h' with
    | bvInhabited he' hw' =>
      injx he he'
      have h1 := val_eq (ihw hw' rfl)
      subst h1; rfl
    | _ => clashx
  | boolInhabited he => intro r' h' hk; cases h' with
    | boolInhabited he' => rfl
    | bvAbbrev he' hr' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_instInhabitedBool] at hr'; cases hr'
    | _ => clashx
  | sigPure he hd ht hx ihd iht ihx => intro r' h' hk; cases h' with
    | sigPure he' hd' ht' hx' =>
      injx he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihx hx' rfl)
      subst h3; rfl
    | _ => clashx
  | sigRegister he hd ht hi hs ihd iht ihi ihs => intro r' h' hk; cases h' with
    | sigRegister he' hd' ht' hi' hs' =>
      injx he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihi hi' rfl)
      subst h3
      have h4 := val_eq (ihs hs' rfl)
      subst h4; rfl
    | _ => clashx
  | sigMux he hd ht hc ha hb ihd iht ihc iha ihb => intro r' h' hk; cases h' with
    | sigMux he' hd' ht' hc' ha' hb' =>
      injx he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihc hc' rfl)
      subst h3
      have h4 := val_eq (iha ha' rfl)
      subst h4
      have h5 := val_eq (ihb hb' rfl)
      subst h5; rfl
    | _ => clashx
  | sigAddBV he hd hw ha hb ihd ihw iha ihb => intro r' h' hk; cases h' with
    | sigAddBV he' hd' hw' ha' hb' =>
      injx he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := val_eq (ihw hw' rfl)
      subst h2
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashx
  | sigLoop he hd ht hi hf ihd iht ihi ihf => intro r' h' hk; cases h' with
    | sigLoop he' hd' ht' hi' hf' =>
      injx he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihi hi' rfl)
      subst h3
      have h4 := val_eq (ihf hf' rfl)
      subst h4; rfl
    | _ => clashx
  | lam he hA hb ihA ihb => intro r' h' hk; cases h' with
    | lam he' hA' hb' =>
      injx he he'
      have h1 := ty_eq (ihA hA' rfl)
      subst h1
      have h2 : ∀ a, _ = _ := fun a => (val_inj (ihb a (hb' a) rfl)).1
      have h2' := funext h2
      subst h2'
      have h3 : _ = _ := funext fun a => eq_of_heq (val_inj (ihb a (hb' a) rfl)).2
      subst h3; rfl
    | _ => clashx
  | letE he hA hv hb ihA ihv ihb => intro r' h' hk; cases h' with
    | letE he' hA' hv' hb' =>
      injx he he'
      have h1 := ty_eq (ihA hA' rfl)
      subst h1
      have h2 := val_eq (ihv hv' rfl)
      subst h2
      exact ihb hb' rfl
    | zeta he' hA' h2 =>
      injx he he'
      have := coreHead_td hA
      simp_all
    | _ => clashx
  | sigBeqBV he hd hw ha hb ihd ihw iha ihb => intro r' h' hk; cases h' with
    | sigBeqBV he' hd' hw' ha' hb' =>
      injx he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := val_eq (ihw hw' rfl)
      subst h2
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashx
  | sigAndBool he hd ha hb ihd iha ihb => intro r' h' hk; cases h' with
    | sigAndBool he' hd' ha' hb' =>
      injx he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashx
  | sigOrBool he hd ha hb ihd iha ihb => intro r' h' hk; cases h' with
    | sigOrBool he' hd' ha' hb' =>
      injx he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashx
  | sigNotBool he hd ha ihd iha => intro r' h' hk; cases h' with
    | sigNotBool he' hd' ha' =>
      injx he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h3 := val_eq (iha ha' rfl)
      subst h3; rfl
    | _ => clashx
  | bvAbbrev he hr => intro r' h' hk; cases h' with
    | bvAbbrev he' hr' =>
      have hc : _ := (Expr.const.inj (he.symm.trans he')).1
      subst hc
      rw [hr] at hr'
      cases hr'
      rfl
    | domDefault he' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_defaultDomain] at hr; cases hr
    | boolInhabited he' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_instInhabitedBool] at hr; cases hr
    | unf hs' _ _ =>
      subst he
      have := stopC_of_row hr
      simp_all [headStop, appFn]
    | _ => clashx
  | unf hs hu h ih => intro r' h' hk; cases h' with
    | unf hs' hu' h' =>
      have e1 := Option.some.inj (hu.symm.trans hu')
      subst e1
      exact ih h' rfl
    | _ => clashx
  | beta hb h ih => intro r' h' hk; cases h' with
    | beta hb' h' =>
      have e1 := Option.some.inj (hb.symm.trans hb')
      subst e1
      exact ih h' rfl
    | _ => clashx
  | zeta he hA h ih => intro r' h' hk; cases h' with
    | zeta he' hA' h' =>
      injx he he'
      exact ih h' rfl
    | letE he' hA' hv' hb' =>
      injx he he'
      have := coreHead_td hA'
      simp_all
    | _ => clashx
  | projStep he hx h ih => intro r' h' hk; cases h' with
    | projStep he' hx' h' =>
      injx he he'
      have e1 := Option.some.inj (hx.symm.trans hx')
      subst e1
      exact ih h' rfl
    | projCtor he' hh' hc' hS' hn' hf' h' =>
      injx he he'
      have := whStep_ctor hc' _ hh'
      rw [hx] at this; cases this
    | _ => clashx
  | projCtor he hh hc hS hn hf h ih => intro r' h' hk; cases h' with
    | projCtor he' hh' hc' hS' hn' hf' h' =>
      injx he he'
      have h1 := Expr.const.inj (hh.symm.trans hh')
      obtain ⟨rfl, rfl⟩ := h1
      have h2 := ConstantInfo.ctorInfo.inj (Option.some.inj (hc.symm.trans hc'))
      subst h2
      have h3 := Option.some.inj (hf.symm.trans hf')
      subst h3
      exact ih h' rfl
    | projStep he' hx' h' =>
      injx he he'
      have := whStep_ctor hc _ hh
      rw [hx'] at this; cases this
    | _ => clashx

theorem cdx_fun {env : Environment} {ρ : Val} {e : Expr} {α α' : Type} {v : α} {v' : α'} (h : CDX env ρ e α v) (h' : CDX env ρ e α' v') :
    α = α' ∧ HEq v v' := val_inj (dx_fun h h' rfl)

theorem tdx_fun {env : Environment} {ρ : Val} {e : Expr} {T T' : Type} (h : TDX env ρ e T) (h' : TDX env ρ e T') : T = T' := ty_eq (dx_fun h h' rfl)

theorem cdx_eq {env : Environment} {ρ : Val} {e : Expr} {α : Type} {v v' : α} (h : CDX env ρ e α v) (h' : CDX env ρ e α v') : v = v' :=
  eq_of_heq (cdx_fun h h').2

/-- `CircCVX env` is functional at the environment it is parameterised by -/
theorem circCVX_functional (env : Environment) : ConstValueFunctional (CircCVX env) := by
  intro env' c α β v w ⟨d, hd, _, hv⟩ ⟨d', hd', _, hv'⟩
  rw [hd] at hd'
  have := ConstantInfo.defnInfo.inj (Option.some.inj hd')
  subst this
  exact cdx_fun hv hv'

/-! ## 5. building derivations in a closed context from a table of environment facts -/

/-- a definition row: the universe parameters and the value of a `defnInfo` -/
structure DefRow where
  lps : List Name
  value : Expr

/-- the facts about the run's environment that a concrete derivation uses (the hypothesis `EnvDefs env Δ`; the meta check compares `Δ` with the environment) -/
def EnvDefs (env : Environment) (Δ : Name → Option DefRow) : Prop :=
  ∀ c r, Δ c = some r → ∃ d : DefinitionVal, env.find? c = some (.defnInfo d) ∧ d.levelParams = r.lps ∧ d.value = r.value

/-- a constructor row -/
structure CtorRow where
  induct : Name
  numParams : Nat
  numFields : Nat

def EnvCtors (env : Environment) (Γ : Name → Option CtorRow) : Prop :=
  ∀ c r, Γ c = some r → ∃ cv : ConstructorVal, env.find? c = some (.ctorInfo cv) ∧ cv.induct = r.induct ∧ cv.numParams = r.numParams ∧ cv.numFields = r.numFields

theorem cdx_unf_tbl {env : Environment} {Δ : Name → Option DefRow} (hΔ : EnvDefs env Δ) {ρ : Val} {e e' : Expr} {c : Name} {ls : List Level} {r : DefRow}
    {α : Type} {v : α} (hh : appFn e = .const c ls) (hs : stopC c = false) (hr : Δ c = some r) (hl : r.lps.length = ls.length)
    (he' : e' = betaApp (instLE r.lps ls r.value) (appArgs e)) (h : CDX env ρ e' α v) : CDX env ρ e α v := by
  obtain ⟨d, hd, hlp, hv⟩ := hΔ c r hr
  refine DX.unf (by simp [headStop, hh, hs]) ?_ h
  simp [unfoldAt, hh, hd, hlp, hv, hl, he']

theorem cdx_projCtor_tbl {env : Environment} {Γ : Name → Option CtorRow} (hΓ : EnvCtors env Γ) {ρ : Val} {e x fld : Expr} {S ctor : Name} {ls : List Level}
    {r : CtorRow} {i : Nat} {α : Type} {v : α} (he : e = .proj S i x) (hh : appFn x = .const ctor ls) (hr : Γ ctor = some r) (hS : r.induct = S)
    (hn : (appArgs x).length = r.numParams + r.numFields) (hf : (appArgs x)[r.numParams + i]? = some fld) (h : CDX env ρ fld α v) : CDX env ρ e α v := by
  obtain ⟨cv, hc, h1, h2, h3⟩ := hΓ ctor r hr
  refine DX.projCtor he hh hc (by rw [h1, hS]) (by rw [h2, h3]; exact hn) (by rw [h2]; exact hf) h

end Tools.ShippingFGCircuitS1mCD

#print axioms Tools.ShippingFGCircuitS1mCD.cdx_of_cd
#print axioms Tools.ShippingFGCircuitS1mCD.tdx_of_td
#print axioms Tools.ShippingFGCircuitS1mCD.cdx_fun
#print axioms Tools.ShippingFGCircuitS1mCD.tdx_fun
#print axioms Tools.ShippingFGCircuitS1mCD.circCVX_functional
#print axioms Tools.ShippingFGCircuitS1mCD.circCV_to_X
#print axioms Tools.ShippingFGCircuitS1mCD.cdx_unf_tbl
#print axioms Tools.ShippingFGCircuitS1mCD.cdx_projCtor_tbl
