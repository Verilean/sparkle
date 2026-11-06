import Tools.ShippingFGCircuitS2iSh
set_option autoImplicit false
-- FG circuit pilot S2i: the bridge family `DT` on top of the primitive/constructor rules of `DS`, with CLOSURE environments, docs/FG-CIRCUIT-PILOT.md §35.
-- No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.

/-! # `DT`

`DT` = the VALUE/TYPE rules of `DS` (S2b) over a closure environment `Cx` (a variable bound to `Ent.val` is read xs before; `Ent.clo` is new: `bvarClo`),
WITHOUT the substitution rules `unf`/`beta`/`zeta`/`projStep`/`projCtor`/`recIota`/`projRec` (their work is done by the closure machine `Sh`, which has no substitution), plus:
* `viaSh` (the bridge, above), `bvarClo`, `boolFalse`/`boolTrue` (ctor values of `Bool`);
* the narrow wiring rules `mapFst`/`mapSnd` WITHOUT the `MapStuck` premise (it only separated them from `unf`, which `DT` does not have; `Signal.map` is a stop head of `Sh`).
Exclusivity is by head: `viaOK e` is false for a `bvar`, a `lam`, and an application of a head that has a direct rule (`directHead`); a `let` is `letE` (core type) or `Sh.letZ` (other type), never both.
There is NO general `Signal.mk` rule and no rule that derives an arbitrary stream. `Sh` correspondence with substitution is not a theorem (audit); `DT` is a family of its own with its own functionality `dt_fun`. -/
namespace Tools.ShippingFGCircuitS2iDT
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5ConstValueE Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD Tools.ShippingFGCircuitS1sCD
open Tools.ShippingFGCircuitS2iSh

/-- the heads with a DIRECT rule of `DT` (the stop heads of `Sh`, and the constructors that have a value rule) -/
def directHead (c : Name) : Bool := stopD c || [``Prod.mk, ``PUnit.unit, ``Inhabited.mk, ``Bool.false, ``Bool.true].contains c

/-- `viaSh` may conclude about `e`: the head is not a direct head; a bare variable / `lam` is never `viaSh` (it is `bvar`/`bvarClo`/`lam`) -/
def viaOK (e : Expr) : Bool :=
  match appFn e with
  | .const c _ => !directHead c
  | .bvar _ => !(appArgs e).isEmpty
  | .lam .. => !(appArgs e).isEmpty
  | .letE _ A .. => !coreHead A
  | _ => true

theorem viaOK_bvar (i : Nat) : viaOK (.bvar i) = false := rfl
theorem viaOK_lam (n : Name) (A b : Expr) (bi : BinderInfo) : viaOK (.lam n A b bi) = false := rfl
theorem viaOK_appN {c : Name} (ls : List Level) (args : List Expr) (hd : directHead c = true) : viaOK (appN c ls args) = false := by
  unfold viaOK
  rw [appFn_appN]
  simp [hd]
theorem viaOK_const {c : Name} (ls : List Level) (hd : directHead c = true) : viaOK (.const c ls) = false := by
  simp [viaOK, appFn, hd]

section
local macro "CDt " env:term:max ρ:term:max e:term:max α:term:max v:term:max : term => `($(Lean.mkIdent `Tools.ShippingFGCircuitS2iDT.DT) $env $ρ $e (Res.val $α $v))
local macro "TDt " env:term:max ρ:term:max e:term:max T:term:max : term => `($(Lean.mkIdent `Tools.ShippingFGCircuitS2iDT.DT) $env $ρ $e (Res.ty $T))
inductive DT (env : Environment) : Cx → Expr → Res → Prop
  | nat {ρ : Cx} {e : Expr} (he : e = .const ``Nat []) : TDt env ρ e Nat
  | bool {ρ : Cx} {e : Expr} (he : e = .const ``Bool []) : TDt env ρ e Bool
  | domainConfig {ρ : Cx} {e : Expr} (he : e = .const ``Sparkle.Core.Domain.DomainConfig []) : TDt env ρ e DomainConfig
  | bitvec {ρ : Cx} {e w : Expr} {n : Nat} (he : e = appN ``BitVec [] [w]) (hw : CDt env ρ w Nat n) : TDt env ρ e (BitVec n)
  | signal {ρ : Cx} {e d t : Expr} {D : DomainConfig} {T : Type} (he : e = appN ``Signal [.zero] [d, t])
      (hd : CDt env ρ d DomainConfig D) (ht : TDt env ρ t T) : TDt env ρ e (Signal D T)

  | bvar {ρ : Cx} {i : Nat} {τ : Expr} {T : Type} {a : T} (h : ρ[i]? = some (Ent.val ⟨τ, ⟨T, a⟩⟩)) : CDt env ρ (.bvar i) T a
  | natLit {ρ : Cx} {e : Expr} {n : Nat}
      (he : e = appN ``OfNat.ofNat [.zero] [.const ``Nat [], .lit (.natVal n), appN ``instOfNatNat [] [.lit (.natVal n)]]) :
      CDt env ρ e Nat n
  | domDefault {ρ : Cx} {e : Expr} (he : e = .const ``Sparkle.Core.Domain.defaultDomain []) :
      CDt env ρ e DomainConfig defaultDomain
  | bvOfNat {ρ : Cx} {e w k : Expr} {W K : Nat} (he : e = appN ``BitVec.ofNat [] [w, k])
      (hw : CDt env ρ w Nat W) (hk : CDt env ρ k Nat K) : CDt env ρ e (BitVec W) (BitVec.ofNat W K)
  | bvInhabited {ρ : Cx} {e w : Expr} {W : Nat} (he : e = appN ``BitVec.instInhabited [] [w]) (hw : CDt env ρ w Nat W) :
      CDt env ρ e (Inhabited (BitVec W)) (inferInstance : Inhabited (BitVec W))
  | boolInhabited {ρ : Cx} {e : Expr} (he : e = .const ``instInhabitedBool []) :
      CDt env ρ e (Inhabited Bool) (inferInstance : Inhabited Bool)
  | sigPure {ρ : Cx} {e d t x : Expr} {D : DomainConfig} {T : Type} {a : T}
      (he : e = appN ``Signal.pure [.zero] [d, t, x]) (hd : CDt env ρ d DomainConfig D) (ht : TDt env ρ t T) (hx : CDt env ρ x T a) :
      CDt env ρ e (Signal D T) (Signal.pure a)
  | sigRegister {ρ : Cx} {e d t i s : Expr} {D : DomainConfig} {T : Type} {a : T} {sv : Signal D T}
      (he : e = appN ``Signal.register [.zero] [d, t, i, s]) (hd : CDt env ρ d DomainConfig D) (ht : TDt env ρ t T)
      (hi : CDt env ρ i T a) (hs : CDt env ρ s (Signal D T) sv) : CDt env ρ e (Signal D T) (Signal.register a sv)
  | sigMux {ρ : Cx} {e d t c a b : Expr} {D : DomainConfig} {T : Type} {cv : Signal D Bool} {av bv : Signal D T}
      (he : e = appN ``Signal.mux [.zero] [d, t, c, a, b]) (hd : CDt env ρ d DomainConfig D) (ht : TDt env ρ t T)
      (hc : CDt env ρ c (Signal D Bool) cv) (ha : CDt env ρ a (Signal D T) av) (hb : CDt env ρ b (Signal D T) bv) :
      CDt env ρ e (Signal D T) (Signal.mux cv av bv)
  | sigAddBV {ρ : Cx} {e d w a b : Expr} {D : DomainConfig} {W : Nat} {av bv : Signal D (BitVec W)}
      (he : e = appN ``HAdd.hAdd [.zero, .zero, .zero]
        [appN ``Signal [.zero] [d, appN ``BitVec [] [w]], appN ``Signal [.zero] [d, appN ``BitVec [] [w]],
         appN ``Signal [.zero] [d, appN ``BitVec [] [w]], appN ``Sparkle.Core.Signal.instHAddSignalBitVec [] [d, w], a, b])
      (hd : CDt env ρ d DomainConfig D) (hw : CDt env ρ w Nat W)
      (ha : CDt env ρ a (Signal D (BitVec W)) av) (hb : CDt env ρ b (Signal D (BitVec W)) bv) :
      CDt env ρ e (Signal D (BitVec W)) (@HAdd.hAdd _ _ _ (@Sparkle.Core.Signal.instHAddSignalBitVec D W) av bv)
  | sigLoop {ρ : Cx} {e d t inst f : Expr} {D : DomainConfig} {T : Type} {iv : Inhabited T} {g : Signal D T → Signal D T}
      (he : e = appN ``Signal.loop [] [d, t, inst, f]) (hd : CDt env ρ d DomainConfig D) (ht : TDt env ρ t T)
      (hi : CDt env ρ inst (Inhabited T) iv) (hf : CDt env ρ f (Signal D T → Signal D T) g) :
      CDt env ρ e (Signal D T) (@Signal.loop D T iv g)
  | lam {ρ : Cx} {e A body : Expr} {n : Name} {bi : BinderInfo} {TA : Type} {TB : TA → Type} {f : (a : TA) → TB a}
      (he : e = .lam n A body bi) (hA : TDt env ρ A TA) (hb : ∀ a : TA, CDt env (Ent.val ⟨A, ⟨TA, a⟩⟩ :: ρ) body (TB a) (f a)) :
      CDt env ρ e ((a : TA) → TB a) f
  | letE {ρ : Cx} {e A v body : Expr} {n : Name} {nd : Bool} {TA T : Type} {a : TA} {r : T}
      (he : e = .letE n A v body nd) (hA : TDt env ρ A TA) (hc : coreHead A = true) (hv : CDt env ρ v TA a)
      (hb : CDt env (Ent.val ⟨A, ⟨TA, a⟩⟩ :: ρ) body T r) : CDt env ρ e T r
  | sigBeqBV {ρ : Cx} {e d w a b : Expr} {D : DomainConfig} {W : Nat} {av bv : Signal D (BitVec W)}
      (he : e = appN ``Sparkle.Core.Signal.Signal.beq []
        [appN ``BitVec [] [w], d, appN ``instBEqOfDecidableEq [.zero] [appN ``BitVec [] [w], appN ``instDecidableEqBitVec [] [w]], a, b])
      (hd : CDt env ρ d DomainConfig D) (hw : CDt env ρ w Nat W)
      (ha : CDt env ρ a (Signal D (BitVec W)) av) (hb : CDt env ρ b (Signal D (BitVec W)) bv) :
      CDt env ρ e (Signal D Bool) (@Signal.beq (BitVec W) D (@instBEqOfDecidableEq (BitVec W) (@instDecidableEqBitVec W)) av bv)
  | sigAndBool {ρ : Cx} {e d a b : Expr} {D : DomainConfig} {av bv : Signal D Bool}
      (he : e = appN ``HAnd.hAnd [.zero, .zero, .zero]
        [appN ``Signal [.zero] [d, .const ``Bool []], appN ``Signal [.zero] [d, .const ``Bool []],
         appN ``Signal [.zero] [d, .const ``Bool []], appN ``Sparkle.Core.Signal.instHAndSignalBool [] [d], a, b])
      (hd : CDt env ρ d DomainConfig D) (ha : CDt env ρ a (Signal D Bool) av) (hb : CDt env ρ b (Signal D Bool) bv) :
      CDt env ρ e (Signal D Bool) (@HAnd.hAnd _ _ _ (@Sparkle.Core.Signal.instHAndSignalBool D) av bv)
  | sigOrBool {ρ : Cx} {e d a b : Expr} {D : DomainConfig} {av bv : Signal D Bool}
      (he : e = appN ``HOr.hOr [.zero, .zero, .zero]
        [appN ``Signal [.zero] [d, .const ``Bool []], appN ``Signal [.zero] [d, .const ``Bool []],
         appN ``Signal [.zero] [d, .const ``Bool []], appN ``Sparkle.Core.Signal.instHOrSignalBool [] [d], a, b])
      (hd : CDt env ρ d DomainConfig D) (ha : CDt env ρ a (Signal D Bool) av) (hb : CDt env ρ b (Signal D Bool) bv) :
      CDt env ρ e (Signal D Bool) (@HOr.hOr _ _ _ (@Sparkle.Core.Signal.instHOrSignalBool D) av bv)
  | sigNotBool {ρ : Cx} {e d a : Expr} {D : DomainConfig} {av : Signal D Bool}
      (he : e = appN ``Complement.complement [.zero]
        [appN ``Signal [.zero] [d, .const ``Bool []], appN ``Sparkle.Core.Signal.instComplementSignalBool [] [d], a])
      (hd : CDt env ρ d DomainConfig D) (ha : CDt env ρ a (Signal D Bool) av) :
      CDt env ρ e (Signal D Bool) (@Complement.complement _ (@Sparkle.Core.Signal.instComplementSignalBool D) av)
  | bvAbbrev {ρ : Cx} {e : Expr} {c : Name} {n : Nat} {v : BitVec n} (he : e = .const c []) (h : bvAbbrevRow c = some ⟨n, v⟩) :
      CDt env ρ e (BitVec n) v
  /-- NEW (S1r). `Prod a b` -/
  | prodTy {ρ : Cx} {e a b : Expr} {A B : Type} (he : e = appN ``Prod [.zero, .zero] [a, b]) (ha : TDt env ρ a A) (hb : TDt env ρ b B) : TDt env ρ e (A × B)
  /-- NEW (S1r). `PUnit.{1}` (the type `Unit` unfolds to it by `unf`) -/
  | punitTy {ρ : Cx} {e : Expr} (he : e = .const ``PUnit [.succ .zero]) : TDt env ρ e Unit
  /-- NEW (S1r). `PUnit.unit.{1}`; the constructor is a `ctorInfo` of `env` (so no other rule applies) -/
  | unitVal {ρ : Cx} {e : Expr} {cv : ConstructorVal} (he : e = .const ``PUnit.unit [.succ .zero]) (hc : env.find? ``PUnit.unit = some (.ctorInfo cv)) :
      CDt env ρ e Unit ()
  /-- NEW (S1r). `Prod.mk a b x y`; the constructor is a `ctorInfo` of `env` -/
  | prodMk {ρ : Cx} {e a b x y : Expr} {A B : Type} {xv : A} {yv : B} {cv : ConstructorVal}
      (he : e = appN ``Prod.mk [.zero, .zero] [a, b, x, y]) (hc : env.find? ``Prod.mk = some (.ctorInfo cv))
      (ha : TDt env ρ a A) (hb : TDt env ρ b B) (hx : CDt env ρ x A xv) (hy : CDt env ρ y B yv) : CDt env ρ e (A × B) (xv, yv)
  /-- NEW (S1r). `Signal.map Prod.fst s` : the head constant, the function `Prod.fst`, the pair signal. The value is Lean's `Signal.map Prod.fst sv`; `signal_map_fst_at` is its equation at every time. -/
  | mapFst {ρ : Cx} {e d tp ta a b s : Expr} {D : DomainConfig} {A B : Type} {sv : Signal D (A × B)}
      (he : e = appN ``Signal.map [.zero] [d, tp, ta, appN ``Prod.fst [.zero, .zero] [a, b], s])
      (hd : CDt env ρ d DomainConfig D) (hp : TDt env ρ tp (A × B)) (ht : TDt env ρ ta A) (ha : TDt env ρ a A) (hb : TDt env ρ b B)
      (hs : CDt env ρ s (Signal D (A × B)) sv) : CDt env ρ e (Signal D A) (Signal.map Prod.fst sv)
  /-- NEW (S1r). `Signal.map Prod.snd s` -/
  | mapSnd {ρ : Cx} {e d tp tb a b s : Expr} {D : DomainConfig} {A B : Type} {sv : Signal D (A × B)}
      (he : e = appN ``Signal.map [.zero] [d, tp, tb, appN ``Prod.snd [.zero, .zero] [a, b], s])
      (hd : CDt env ρ d DomainConfig D) (hp : TDt env ρ tp (A × B)) (ht : TDt env ρ tb B) (ha : TDt env ρ a A) (hb : TDt env ρ b B)
      (hs : CDt env ρ s (Signal D (A × B)) sv) : CDt env ρ e (Signal D B) (Signal.map Prod.snd sv)
  /-- NEW (S2b). `Inhabited.mk.{u} T x` with ONE level `u` whose closed value is `1` (`lvlNatT u = some 1`, evidence by `Eq.refl`, no `Level.normalize`: that is `opaque`, the kernel cannot run it):
      the instance VALUE `⟨v⟩` from the derivation of the field `x ↦ v`; a constructor of `env` (so no other rule applies). `T : Type` stays; the old rule is the case `u = 1`. -/
  | inhMk {ρ : Cx} {e t x : Expr} {u : Level} {T : Type} {v : T} {cv : ConstructorVal} (he : e = appN ``Inhabited.mk [u] [t, x]) (hu : lvlNatT u = some 1)
      (hc : env.find? ``Inhabited.mk = some (.ctorInfo cv)) (ht : TDt env ρ t T) (hx : CDt env ρ x T v) : CDt env ρ e (Inhabited T) (⟨v⟩ : Inhabited T)
  /-- NEW (S1s). `Inhabited.default.{1} T inst`: the default of the SAME instance, `iv.default`. `Inhabited.default` is a stop head of `unf` (`newStopS`) -/
  | inhDefault {ρ : Cx} {e t inst : Expr} {T : Type} {iv : Inhabited T} (he : e = appN ``Inhabited.default [.succ .zero] [t, inst])
      (ht : TDt env ρ t T) (hi : CDt env ρ inst (Inhabited T) iv) : CDt env ρ e T iv.default
  /-- NEW (S1s). `bundle2.{0} d A B a b` (same `d` for both): the pairing of two signals of the same domain. The value is Lean's `bundle2 av bv` (its LOGICAL definition; `bundle2` has `implemented_by`, which is not proved to agree). `bundle2` is a stop head of `unf` -/
  | bundle2 {ρ : Cx} {e d ta tb a b : Expr} {D : DomainConfig} {A B : Type} {av : Signal D A} {bv : Signal D B}
      (he : e = appN ``Sparkle.Core.Signal.bundle2 [.zero] [d, ta, tb, a, b]) (hd : CDt env ρ d DomainConfig D) (hta : TDt env ρ ta A) (htb : TDt env ρ tb B)
      (ha : CDt env ρ a (Signal D A) av) (hb : CDt env ρ b (Signal D B) bv) : CDt env ρ e (Signal D (A × B)) (Sparkle.Core.Signal.bundle2 av bv)
  /-- NEW (S2i). `Bool.false` / `Bool.true`: the constructor values of the finite type `Bool` (a `ctorInfo` of the SAME env) -/
  | boolFalse {ρ : Cx} {e : Expr} {cv : ConstructorVal} (he : e = .const ``Bool.false []) (hc : env.find? ``Bool.false = some (.ctorInfo cv)) : CDt env ρ e Bool false
  | boolTrue {ρ : Cx} {e : Expr} {cv : ConstructorVal} (he : e = .const ``Bool.true []) (hc : env.find? ``Bool.true = some (.ctorInfo cv)) : CDt env ρ e Bool true
  /-- NEW (S2i). a variable bound to a CLOSURE (call-by-name): its meaning is the meaning of the closure's expression in the captured environment -/
  | bvarClo {ρ : Cx} {i : Nat} {e' : Expr} {ρ' : Cx} {r : Res} (hb : ρ[i]? = some (Ent.clo e' ρ')) (h : DT env ρ' e' r) : DT env ρ (.bvar i) r
  /-- NEW (S2i), the BRIDGE. `e` weak-head evaluates in the closure environment machine `Sh` (empty spine) to a constructor / stuck head `c ls` whose spine is `args` xs closures over ONE common environment `ρ₀`
      (so the arguments are ordinary expressions of `ρ₀`); then the meaning of `e` is the meaning of `c ls args` in `ρ₀`, which is a primitive/constructor rule of this family (`viaOK`: `e` itself is not such a form).
      `hcan` makes `ρ₀` canonical when there are no arguments. -/
  | viaSh {ρ : Cx} {e : Expr} {hn : Hn} {args : List Expr} {ρ₀ : Cx} {r : Res} (hv : viaOK e = true) (hnv : hn.isVar = false) (hsh : Sh env ρ e [] hn)
      (hsp : hn.head.2.2 = args.map (fun a => Ent.clo a ρ₀)) (hcan : args = [] → ρ₀ = []) (h : DT env ρ₀ (appN hn.head.1 hn.head.2.1 args) r) : DT env ρ e r
  /-- NEW (S2p), the VALUE-HEAD bridge. `e` (not a bare variable: `viaOK`) evaluates in `Sh` (empty spine) to a bare VALUE entry, the variable `i` of `ρ₀`: the meaning of `e` is the meaning of `#i` in `ρ₀`
      (which is the `bvar` rule: the entry's own value). Exclusive with `viaSh` by `hnv` (that rule needs a constructor / stuck head). -/
  | viaVar {ρ : Cx} {e : Expr} {ρ₀ : Cx} {i : Nat} {r : Res} (hv : viaOK e = true) (hsh : Sh env ρ e [] (Hn.var ρ₀ i)) (h : DT env ρ₀ (.bvar i) r) : DT env ρ e r
end

abbrev TDT (env : Environment) (ρ : Cx) (e : Expr) (T : Type) : Prop := DT env ρ e (.ty T)
abbrev CDT (env : Environment) (ρ : Cx) (e : Expr) (α : Type) (v : α) : Prop := DT env ρ e (.val α v)

theorem map_clo_eq : ∀ {args args' : List Expr} {ρ ρ' : Cx}, args.map (fun a => Ent.clo a ρ) = args'.map (fun a => Ent.clo a ρ') →
    (args = [] ∧ args' = []) ∨ (args = args' ∧ ρ = ρ')
  | [], [], _, _, _ => Or.inl ⟨rfl, rfl⟩
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: xs, a' :: xs', ρ, ρ', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨e1, e2⟩ := Ent.clo_inj h1
    subst e1; subst e2
    rcases map_clo_eq h2 with ⟨r1, r2⟩ | ⟨r1, r2⟩
    · subst r1; subst r2; exact Or.inr ⟨rfl, rfl⟩
    · subst r1; exact Or.inr ⟨rfl, rfl⟩

end Tools.ShippingFGCircuitS2iDT
