import Tools.ShippingFGCircuitS1pCD
set_option autoImplicit false
-- FG circuit pilot S1r: the `Signal.map Prod.fst / Prod.snd` wiring rules (narrow, structural) on top of `DY`, the family `DZ`, docs/FG-CIRCUIT-PILOT.md §22.
-- No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.

/-! # S1r

`DZ` = `DY` + the narrow wiring rules; `dy_to_dz` embeds `DY` (hence `DX`, `CD`). `DY` and `DX` are not edited.

New rules (all over a fixed `env`):
* types: `prodTy` (`Prod a b`), `punitTy` (`PUnit.{1}`).
* values: `unitVal` (`PUnit.unit.{1}`), `prodMk` (`Prod.mk a b x y`), `mapFst`, `mapSnd` (`Signal.map Prod.fst/Prod.snd s`, the value is Lean's own `Signal.map Prod.fst sv`).
* `unf`, `beta`, `projStep`, `projCtor`, `recIota` are stated for an arbitrary result `r : Res` (type or value) instead of values only, so that a TYPE such as `HList [α, β]` is unfolded by the same
  delta/beta/projection/`List.rec` steps; the stop condition `stopR r e` is the old `headStop` for a value and `tyHeadStop` for a type (the core type heads are never unfolded).
* `letE` gets one more premise `coreHead A = true` (before, it followed from the type judgement: `coreHead_ty`; with the type-level unfolding it must be stated, so that `letE` and `zeta` stay exclusive).

The rules `mapFst`/`mapSnd` do not interpret the body of `Signal.map` (no rule for an arbitrary `Signal.mk` / `Nat → α`): they are stated for the head constant `Signal.map` with the function `Prod.fst`/`Prod.snd`,
and carry the premise `MapStuck env e` (unfolding `e` with `unf` would reach the constructor `Signal.mk`, on which no rule exists). The Lean equations (`signal_map_*`) are proved for every signal and every time. -/
namespace Tools.ShippingFGCircuitS1rCD
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5ConstValueE Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingEntrySoundness (RunsTo)

/-! ## 1. the Lean equations of the wiring (for all signals, all times) -/

theorem signal_map_eq {D : DomainConfig} {A B : Type} (f : A → B) (s : Signal D A) : Signal.map f s = ⟨fun t => f (s.val t)⟩ := rfl
theorem signal_map_fst_at {D : DomainConfig} {A B : Type} (sv : Signal D (A × B)) (t : Nat) : (Signal.map Prod.fst sv).val t = (sv.val t).1 := rfl
theorem signal_map_snd_at {D : DomainConfig} {A B : Type} (sv : Signal D (A × B)) (t : Nat) : (Signal.map Prod.snd sv).val t = (sv.val t).2 := rfl
/-- the unfolded body of `Signal.map Prod.fst` (the stuck `Signal.mk` of the traversal) is the rule's value -/
theorem signal_mk_fst_eq {D : DomainConfig} {A B : Type} (sv : Signal D (A × B)) : (⟨fun t => (sv.val t).1⟩ : Signal D A) = Signal.map Prod.fst sv := rfl
theorem signal_mk_snd_eq {D : DomainConfig} {A B : Type} (sv : Signal D (A × B)) : (⟨fun t => (sv.val t).2⟩ : Signal D B) = Signal.map Prod.snd sv := rfl
/-- two signals agree iff they agree at every time -/
theorem signal_ext' {D : DomainConfig} {A : Type} {s s' : Signal D A} (h : ∀ t, s.val t = s'.val t) : s = s' := by
  cases s; cases s'; congr; funext t; exact h t
/-- the projections of a `map`ped pair signal, pointwise: `(map fst sv, map snd sv)` reassemble `sv` at every time -/
theorem signal_map_pair_at {D : DomainConfig} {A B : Type} (sv : Signal D (A × B)) (t : Nat) :
    ((Signal.map Prod.fst sv).val t, (Signal.map Prod.snd sv).val t) = sv.val t := rfl
/-- pointwise equation of the rule value with the source `Signal.map` of the projection, at a pair-valued signal built by `Signal.pure` -/
theorem signal_map_fst_pure {D : DomainConfig} {A B : Type} (a : A) (b : B) : Signal.map Prod.fst (Signal.pure (D := D) (a, b)) = Signal.pure a := rfl
theorem signal_map_snd_pure {D : DomainConfig} {A B : Type} (a : A) (b : B) : Signal.map Prod.snd (Signal.pure (D := D) (a, b)) = Signal.pure b := rfl

/-! ## 2. stops, side conditions -/

def tyStopC (c : Name) : Bool := [``Nat, ``Bool, ``Sparkle.Core.Domain.DomainConfig, ``BitVec, ``Signal, ``Prod, ``PUnit].contains c
def tyHeadStop (e : Expr) : Bool :=
  match appFn e with
  | .const c _ => tyStopC c
  | _ => false
/-- the stop condition of `unf`: for a value the old `headStop`; for a type the core type heads -/
def stopR (r : Res) (e : Expr) : Bool := if r.kind then headStop e else tyHeadStop e

theorem tyStopC_nat : tyStopC ``Nat = true := by decide
theorem tyStopC_bool : tyStopC ``Bool = true := by decide
theorem tyStopC_dc : tyStopC ``Sparkle.Core.Domain.DomainConfig = true := by decide
theorem tyStopC_bitvec : tyStopC ``BitVec = true := by decide
theorem tyStopC_signal : tyStopC ``Signal = true := by decide
theorem tyStopC_prod : tyStopC ``Prod = true := by decide
theorem tyStopC_punit : tyStopC ``PUnit = true := by decide

/-- the unfolding of `e` (a `Signal.map` application) reaches a constructor application of `Signal.mk`, which has no rule. The rules `mapFst`/`mapSnd` are the only way for such an `e`. -/
def MapStuck (env : Environment) (e : Expr) : Prop :=
  ∃ (e' : Expr) (ls : List Level) (cv : ConstructorVal), unfoldAt env e = some e' ∧ appFn e' = .const ``Signal.mk ls ∧ env.find? ``Signal.mk = some (.ctorInfo cv)

theorem stopC_mk : stopC ``Signal.mk = false := by decide
theorem bvAbbrevRow_mk : bvAbbrevRow ``Signal.mk = none := by
  cases h : bvAbbrevRow ``Signal.mk with
  | none => rfl
  | some r => have := stopC_of_row h; rw [stopC_mk] at this; cases this

/-! ## 3. the relation -/

section
local macro "CDz " env:term:max ρ:term:max e:term:max α:term:max v:term:max : term => `($(Lean.mkIdent `Tools.ShippingFGCircuitS1rCD.DZ) $env $ρ $e (Res.val $α $v))
local macro "TDz " env:term:max ρ:term:max e:term:max T:term:max : term => `($(Lean.mkIdent `Tools.ShippingFGCircuitS1rCD.DZ) $env $ρ $e (Res.ty $T))
inductive DZ (env : Environment) : Val → Expr → Res → Prop
  | nat {ρ : Val} {e : Expr} (he : e = .const ``Nat []) : TDz env ρ e Nat
  | bool {ρ : Val} {e : Expr} (he : e = .const ``Bool []) : TDz env ρ e Bool
  | domainConfig {ρ : Val} {e : Expr} (he : e = .const ``Sparkle.Core.Domain.DomainConfig []) : TDz env ρ e DomainConfig
  | bitvec {ρ : Val} {e w : Expr} {n : Nat} (he : e = appN ``BitVec [] [w]) (hw : CDz env ρ w Nat n) : TDz env ρ e (BitVec n)
  | signal {ρ : Val} {e d t : Expr} {D : DomainConfig} {T : Type} (he : e = appN ``Signal [.zero] [d, t])
      (hd : CDz env ρ d DomainConfig D) (ht : TDz env ρ t T) : TDz env ρ e (Signal D T)

  | bvar {ρ : Val} {i : Nat} {τ : Expr} {T : Type} {a : T} (h : ρ[i]? = some ⟨τ, ⟨T, a⟩⟩) : CDz env ρ (.bvar i) T a
  | natLit {ρ : Val} {e : Expr} {n : Nat}
      (he : e = appN ``OfNat.ofNat [.zero] [.const ``Nat [], .lit (.natVal n), appN ``instOfNatNat [] [.lit (.natVal n)]]) :
      CDz env ρ e Nat n
  | domDefault {ρ : Val} {e : Expr} (he : e = .const ``Sparkle.Core.Domain.defaultDomain []) :
      CDz env ρ e DomainConfig defaultDomain
  | bvOfNat {ρ : Val} {e w k : Expr} {W K : Nat} (he : e = appN ``BitVec.ofNat [] [w, k])
      (hw : CDz env ρ w Nat W) (hk : CDz env ρ k Nat K) : CDz env ρ e (BitVec W) (BitVec.ofNat W K)
  | bvInhabited {ρ : Val} {e w : Expr} {W : Nat} (he : e = appN ``BitVec.instInhabited [] [w]) (hw : CDz env ρ w Nat W) :
      CDz env ρ e (Inhabited (BitVec W)) (inferInstance : Inhabited (BitVec W))
  | boolInhabited {ρ : Val} {e : Expr} (he : e = .const ``instInhabitedBool []) :
      CDz env ρ e (Inhabited Bool) (inferInstance : Inhabited Bool)
  | sigPure {ρ : Val} {e d t x : Expr} {D : DomainConfig} {T : Type} {a : T}
      (he : e = appN ``Signal.pure [.zero] [d, t, x]) (hd : CDz env ρ d DomainConfig D) (ht : TDz env ρ t T) (hx : CDz env ρ x T a) :
      CDz env ρ e (Signal D T) (Signal.pure a)
  | sigRegister {ρ : Val} {e d t i s : Expr} {D : DomainConfig} {T : Type} {a : T} {sv : Signal D T}
      (he : e = appN ``Signal.register [.zero] [d, t, i, s]) (hd : CDz env ρ d DomainConfig D) (ht : TDz env ρ t T)
      (hi : CDz env ρ i T a) (hs : CDz env ρ s (Signal D T) sv) : CDz env ρ e (Signal D T) (Signal.register a sv)
  | sigMux {ρ : Val} {e d t c a b : Expr} {D : DomainConfig} {T : Type} {cv : Signal D Bool} {av bv : Signal D T}
      (he : e = appN ``Signal.mux [.zero] [d, t, c, a, b]) (hd : CDz env ρ d DomainConfig D) (ht : TDz env ρ t T)
      (hc : CDz env ρ c (Signal D Bool) cv) (ha : CDz env ρ a (Signal D T) av) (hb : CDz env ρ b (Signal D T) bv) :
      CDz env ρ e (Signal D T) (Signal.mux cv av bv)
  | sigAddBV {ρ : Val} {e d w a b : Expr} {D : DomainConfig} {W : Nat} {av bv : Signal D (BitVec W)}
      (he : e = appN ``HAdd.hAdd [.zero, .zero, .zero]
        [appN ``Signal [.zero] [d, appN ``BitVec [] [w]], appN ``Signal [.zero] [d, appN ``BitVec [] [w]],
         appN ``Signal [.zero] [d, appN ``BitVec [] [w]], appN ``Sparkle.Core.Signal.instHAddSignalBitVec [] [d, w], a, b])
      (hd : CDz env ρ d DomainConfig D) (hw : CDz env ρ w Nat W)
      (ha : CDz env ρ a (Signal D (BitVec W)) av) (hb : CDz env ρ b (Signal D (BitVec W)) bv) :
      CDz env ρ e (Signal D (BitVec W)) (@HAdd.hAdd _ _ _ (@Sparkle.Core.Signal.instHAddSignalBitVec D W) av bv)
  | sigLoop {ρ : Val} {e d t inst f : Expr} {D : DomainConfig} {T : Type} {iv : Inhabited T} {g : Signal D T → Signal D T}
      (he : e = appN ``Signal.loop [] [d, t, inst, f]) (hd : CDz env ρ d DomainConfig D) (ht : TDz env ρ t T)
      (hi : CDz env ρ inst (Inhabited T) iv) (hf : CDz env ρ f (Signal D T → Signal D T) g) :
      CDz env ρ e (Signal D T) (@Signal.loop D T iv g)
  | lam {ρ : Val} {e A body : Expr} {n : Name} {bi : BinderInfo} {TA : Type} {TB : TA → Type} {f : (a : TA) → TB a}
      (he : e = .lam n A body bi) (hA : TDz env ρ A TA) (hb : ∀ a : TA, CDz env (⟨A, ⟨TA, a⟩⟩ :: ρ) body (TB a) (f a)) :
      CDz env ρ e ((a : TA) → TB a) f
  | letE {ρ : Val} {e A v body : Expr} {n : Name} {nd : Bool} {TA T : Type} {a : TA} {r : T}
      (he : e = .letE n A v body nd) (hA : TDz env ρ A TA) (hc : coreHead A = true) (hv : CDz env ρ v TA a)
      (hb : CDz env (⟨A, ⟨TA, a⟩⟩ :: ρ) body T r) : CDz env ρ e T r
  | sigBeqBV {ρ : Val} {e d w a b : Expr} {D : DomainConfig} {W : Nat} {av bv : Signal D (BitVec W)}
      (he : e = appN ``Sparkle.Core.Signal.Signal.beq []
        [appN ``BitVec [] [w], d, appN ``instBEqOfDecidableEq [.zero] [appN ``BitVec [] [w], appN ``instDecidableEqBitVec [] [w]], a, b])
      (hd : CDz env ρ d DomainConfig D) (hw : CDz env ρ w Nat W)
      (ha : CDz env ρ a (Signal D (BitVec W)) av) (hb : CDz env ρ b (Signal D (BitVec W)) bv) :
      CDz env ρ e (Signal D Bool) (@Signal.beq (BitVec W) D (@instBEqOfDecidableEq (BitVec W) (@instDecidableEqBitVec W)) av bv)
  | sigAndBool {ρ : Val} {e d a b : Expr} {D : DomainConfig} {av bv : Signal D Bool}
      (he : e = appN ``HAnd.hAnd [.zero, .zero, .zero]
        [appN ``Signal [.zero] [d, .const ``Bool []], appN ``Signal [.zero] [d, .const ``Bool []],
         appN ``Signal [.zero] [d, .const ``Bool []], appN ``Sparkle.Core.Signal.instHAndSignalBool [] [d], a, b])
      (hd : CDz env ρ d DomainConfig D) (ha : CDz env ρ a (Signal D Bool) av) (hb : CDz env ρ b (Signal D Bool) bv) :
      CDz env ρ e (Signal D Bool) (@HAnd.hAnd _ _ _ (@Sparkle.Core.Signal.instHAndSignalBool D) av bv)
  | sigOrBool {ρ : Val} {e d a b : Expr} {D : DomainConfig} {av bv : Signal D Bool}
      (he : e = appN ``HOr.hOr [.zero, .zero, .zero]
        [appN ``Signal [.zero] [d, .const ``Bool []], appN ``Signal [.zero] [d, .const ``Bool []],
         appN ``Signal [.zero] [d, .const ``Bool []], appN ``Sparkle.Core.Signal.instHOrSignalBool [] [d], a, b])
      (hd : CDz env ρ d DomainConfig D) (ha : CDz env ρ a (Signal D Bool) av) (hb : CDz env ρ b (Signal D Bool) bv) :
      CDz env ρ e (Signal D Bool) (@HOr.hOr _ _ _ (@Sparkle.Core.Signal.instHOrSignalBool D) av bv)
  | sigNotBool {ρ : Val} {e d a : Expr} {D : DomainConfig} {av : Signal D Bool}
      (he : e = appN ``Complement.complement [.zero]
        [appN ``Signal [.zero] [d, .const ``Bool []], appN ``Sparkle.Core.Signal.instComplementSignalBool [] [d], a])
      (hd : CDz env ρ d DomainConfig D) (ha : CDz env ρ a (Signal D Bool) av) :
      CDz env ρ e (Signal D Bool) (@Complement.complement _ (@Sparkle.Core.Signal.instComplementSignalBool D) av)
  | bvAbbrev {ρ : Val} {e : Expr} {c : Name} {n : Nat} {v : BitVec n} (he : e = .const c []) (h : bvAbbrevRow c = some ⟨n, v⟩) :
      CDz env ρ e (BitVec n) v
  /-- delta + beta of a user definition, for a value OR a type; `stopR r e` is false (not a primitive head / a core type head) -/
  | unf {ρ : Val} {e e' : Expr} {r : Res}
      (hs : stopR r e = false) (hu : unfoldAt env e = some e') (h : DZ env ρ e' r) : DZ env ρ e r
  | beta {ρ : Val} {e e' : Expr} {r : Res}
      (hb : headRedexR env e = some e') (h : DZ env ρ e' r) : DZ env ρ e r
  | zeta {ρ : Val} {e A v body : Expr} {n : Name} {nd : Bool} {α : Type} {r : α}
      (he : e = .letE n A v body nd) (hA : coreHead A = false) (h : CDz env ρ (instE body v 0) α r) : CDz env ρ e α r
  | projStep {ρ : Val} {e x x' : Expr} {S : Name} {i : Nat} {r : Res}
      (he : e = .proj S i x) (hx : whStepR env x = some x') (h : DZ env ρ (.proj S i x') r) : DZ env ρ e r
  | projCtor {ρ : Val} {e x fld : Expr} {S ctor : Name} {ls : List Level} {cv : ConstructorVal} {i : Nat} {r : Res}
      (he : e = .proj S i x) (hh : appFn x = .const ctor ls) (hc : env.find? ctor = some (.ctorInfo cv)) (hS : cv.induct = S)
      (hn : (appArgs x).length = cv.numParams + cv.numFields) (hf : (appArgs x)[cv.numParams + i]? = some fld)
      (h : DZ env ρ fld r) : DZ env ρ e r
  | recIota {ρ : Val} {e e' : Expr} {ls : List Level} {ri : RecursorVal} {r : Res}
      (hf : appFn e = .const ``List.rec ls) (hi : env.find? ``List.rec = some (.recInfo ri)) (hr : recStep env e = some e') (h : DZ env ρ e' r) : DZ env ρ e r
  /-- NEW (S1r). `Prod a b` -/
  | prodTy {ρ : Val} {e a b : Expr} {A B : Type} (he : e = appN ``Prod [.zero, .zero] [a, b]) (ha : TDz env ρ a A) (hb : TDz env ρ b B) : TDz env ρ e (A × B)
  /-- NEW (S1r). `PUnit.{1}` (the type `Unit` unfolds to it by `unf`) -/
  | punitTy {ρ : Val} {e : Expr} (he : e = .const ``PUnit [.succ .zero]) : TDz env ρ e Unit
  /-- NEW (S1r). `PUnit.unit.{1}`; the constructor is a `ctorInfo` of `env` (so `unf` cannot also apply) -/
  | unitVal {ρ : Val} {e : Expr} {cv : ConstructorVal} (he : e = .const ``PUnit.unit [.succ .zero]) (hc : env.find? ``PUnit.unit = some (.ctorInfo cv)) :
      CDz env ρ e Unit ()
  /-- NEW (S1r). `Prod.mk a b x y`; the constructor is a `ctorInfo` of `env` -/
  | prodMk {ρ : Val} {e a b x y : Expr} {A B : Type} {xv : A} {yv : B} {cv : ConstructorVal}
      (he : e = appN ``Prod.mk [.zero, .zero] [a, b, x, y]) (hc : env.find? ``Prod.mk = some (.ctorInfo cv))
      (ha : TDz env ρ a A) (hb : TDz env ρ b B) (hx : CDz env ρ x A xv) (hy : CDz env ρ y B yv) : CDz env ρ e (A × B) (xv, yv)
  /-- NEW (S1r). `Signal.map Prod.fst s` : the head constant, the function `Prod.fst`, the pair signal. The value is Lean's `Signal.map Prod.fst sv`; `signal_map_fst_at` is its equation at every time. -/
  | mapFst {ρ : Val} {e d tp ta a b s : Expr} {D : DomainConfig} {A B : Type} {sv : Signal D (A × B)}
      (he : e = appN ``Signal.map [.zero] [d, tp, ta, appN ``Prod.fst [.zero, .zero] [a, b], s])
      (hd : CDz env ρ d DomainConfig D) (hp : TDz env ρ tp (A × B)) (ht : TDz env ρ ta A) (ha : TDz env ρ a A) (hb : TDz env ρ b B)
      (hs : CDz env ρ s (Signal D (A × B)) sv) (hstuck : MapStuck env e) : CDz env ρ e (Signal D A) (Signal.map Prod.fst sv)
  /-- NEW (S1r). `Signal.map Prod.snd s` -/
  | mapSnd {ρ : Val} {e d tp tb a b s : Expr} {D : DomainConfig} {A B : Type} {sv : Signal D (A × B)}
      (he : e = appN ``Signal.map [.zero] [d, tp, tb, appN ``Prod.snd [.zero, .zero] [a, b], s])
      (hd : CDz env ρ d DomainConfig D) (hp : TDz env ρ tp (A × B)) (ht : TDz env ρ tb B) (ha : TDz env ρ a A) (hb : TDz env ρ b B)
      (hs : CDz env ρ s (Signal D (A × B)) sv) (hstuck : MapStuck env e) : CDz env ρ e (Signal D B) (Signal.map Prod.snd sv)
end

abbrev TDZ (env : Environment) (ρ : Val) (e : Expr) (T : Type) : Prop := DZ env ρ e (.ty T)
abbrev CDZ (env : Environment) (ρ : Val) (e : Expr) (α : Type) (v : α) : Prop := DZ env ρ e (.val α v)

/-! ## 4. the embedding `DY → DZ` (hence `DX → DZ`, `CD → DZ`) -/

theorem stopR_val (α : Type) (v : α) (e : Expr) : stopR (.val α v) e = headStop e := by simp [stopR, Res.kind]

theorem dy_to_dz {env : Environment} {ρ : Val} {e : Expr} {r : Res} (h : DY env ρ e r) : DZ env ρ e r := by
  induction h with
  | nat he => exact .nat he
  | bool he => exact .bool he
  | domainConfig he => exact .domainConfig he
  | bitvec he _ ih => exact .bitvec he ih
  | signal he _ _ ih1 ih2 => exact .signal he ih1 ih2
  | bvar h => exact .bvar h
  | natLit he => exact .natLit he
  | domDefault he => exact .domDefault he
  | bvOfNat he _ _ ih1 ih2 => exact .bvOfNat he ih1 ih2
  | bvInhabited he _ ih => exact .bvInhabited he ih
  | boolInhabited he => exact .boolInhabited he
  | sigPure he _ _ _ ih1 ih2 ih3 => exact .sigPure he ih1 ih2 ih3
  | sigRegister he _ _ _ _ ih1 ih2 ih3 ih4 => exact .sigRegister he ih1 ih2 ih3 ih4
  | sigMux he _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 => exact .sigMux he ih1 ih2 ih3 ih4 ih5
  | sigAddBV he _ _ _ _ ih1 ih2 ih3 ih4 => exact .sigAddBV he ih1 ih2 ih3 ih4
  | sigLoop he _ _ _ _ ih1 ih2 ih3 ih4 => exact .sigLoop he ih1 ih2 ih3 ih4
  | lam he _ _ ih1 ih2 => exact .lam he ih1 ih2
  | letE he hA _ _ ih1 ih2 ih3 => exact .letE he ih1 (coreHead_ty hA) ih2 ih3
  | sigBeqBV he _ _ _ _ ih1 ih2 ih3 ih4 => exact .sigBeqBV he ih1 ih2 ih3 ih4
  | sigAndBool he _ _ _ ih1 ih2 ih3 => exact .sigAndBool he ih1 ih2 ih3
  | sigOrBool he _ _ _ ih1 ih2 ih3 => exact .sigOrBool he ih1 ih2 ih3
  | sigNotBool he _ _ ih1 ih2 => exact .sigNotBool he ih1 ih2
  | bvAbbrev he hr => exact .bvAbbrev he hr
  | unf hs hu _ ih => exact .unf (by rw [stopR_val]; exact hs) hu ih
  | beta hb _ ih => exact .beta hb ih
  | zeta he hA _ ih => exact .zeta he hA ih
  | projStep he hx _ ih => exact .projStep he hx ih
  | projCtor he hh hc hS hn hf _ ih => exact .projCtor he hh hc hS hn hf ih
  | recIota hf hi hr _ ih => exact .recIota hf hi hr ih

theorem dx_to_dz {env : Environment} {ρ : Val} {e : Expr} {r : Res} (h : DX env ρ e r) : DZ env ρ e r := dy_to_dz (dx_to_dy h)

/-! ## 5. exclusivity of the constructor-headed `Signal.mk` -/

theorem headRedexR_const {env : Environment} {x : Expr} {c : Name} {ls : List Level} (hh : appFn x = .const c ls) : headRedexR env x = none := by
  simp [headRedexR, hh]

/-- there is no derivation for an expression headed by the constructor `Signal.mk` (of `env`): no rule has that head -/
theorem dz_signalMk_false {env : Environment} {ρ : Val} {e : Expr} {r : Res} (h : DZ env ρ e r) {ls : List Level} {cv : ConstructorVal}
    (hf : appFn e = .const ``Signal.mk ls) (hc : env.find? ``Signal.mk = some (.ctorInfo cv)) : False := by
  cases h with
  | unf hs hu h' => simp [unfoldAt, hf, hc] at hu
  | beta hb h' => simp [headRedexR_const hf] at hb
  | bvAbbrev he hr =>
    subst he
    simp only [appFn, Expr.const.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    rw [bvAbbrevRow_mk] at hr; cases hr
  | _ => first
    | (subst_vars; simp [appFn, appFn_appN] at hf; done)
    | (simp_all [appFn, appFn_appN]; done)

/-- the premise of `mapFst`/`mapSnd` excludes `unf` at the same expression -/
theorem mapStuck_unf_false {env : Environment} {ρ : Val} {e e' : Expr} {r : Res} (hs : MapStuck env e) (hu : unfoldAt env e = some e') (h : DZ env ρ e' r) : False := by
  obtain ⟨e1, ls, cv, hu1, hf, hc⟩ := hs
  rw [hu1] at hu
  have := Option.some.inj hu
  subst this
  exact dz_signalMk_false h hf hc

/-! ## 6. functionality -/

macro "clashz" : tactic =>
  `(tactic| (exfalso
             try subst_vars
             try simp_all [Res.kind, stopR, tyHeadStop, headStop, appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, appFn, stopC_ofNat, stopC_defaultDomain, stopC_bvOfNat, stopC_bvInh,
               stopC_boolInh, stopC_pure, stopC_register, stopC_mux, stopC_hadd, stopC_loop, stopC_beq, stopC_hand, stopC_hor, stopC_compl, bvAbbrevRow_defaultDomain,
               bvAbbrevRow_instInhabitedBool, stopC_of_row, unfoldAt_bvar, unfoldAt_lam, unfoldAt_letE, unfoldAt_proj, unfoldAt_rec, headRedexR_rec, stopC_rec, bvAbbrevRow_rec,
               tyStopC_nat, tyStopC_bool, tyStopC_dc, tyStopC_bitvec, tyStopC_signal, tyStopC_prod, tyStopC_punit]
             try simp_all [Res.kind, stopR, tyHeadStop, headStop, headRedexR, appArgs, appFn, appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, unfoldAt_none_of_betaR, unfoldAt_rec, headRedexR_rec,
               tyStopC_nat, tyStopC_bool, tyStopC_dc, tyStopC_bitvec, tyStopC_signal, tyStopC_prod, tyStopC_punit]))

macro "injz" he:ident he':ident : tactic =>
  `(tactic| (have h := Eq.trans (Eq.symm $he) $he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.proj.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **functionality** of `DZ`: two derivations of the same expression in the same valuation, of the same kind, have the same result. -/
theorem dz_fun {env : Environment} {ρ : Val} {e : Expr} {r : Res} (h : DZ env ρ e r) : ∀ {r' : Res}, DZ env ρ e r' → r.kind = r'.kind → r = r' := by
  induction h with
  | nat he => intro r' h' hk; cases h' with
    | nat he' => rfl
    | _ => clashz
  | bool he => intro r' h' hk; cases h' with
    | bool he' => rfl
    | _ => clashz
  | domainConfig he => intro r' h' hk; cases h' with
    | domainConfig he' => rfl
    | _ => clashz
  | bitvec he hw ihw => intro r' h' hk; cases h' with
    | bitvec he' hw' =>
      injz he he'
      have := val_eq (ihw hw' rfl)
      subst this; rfl
    | _ => clashz
  | signal he hd ht ihd iht => intro r' h' hk; cases h' with
    | signal he' hd' ht' =>
      injz he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2; rfl
    | _ => clashz
  | bvar hb => intro r' h' hk; cases h' with
    | bvar hb' =>
      have := Option.some.inj (hb.symm.trans hb')
      cases this
      rfl
    | _ => clashz
  | natLit he => intro r' h' hk; cases h' with
    | natLit he' =>
      injz he he'
      rfl
    | _ => clashz
  | domDefault he => intro r' h' hk; cases h' with
    | domDefault he' => rfl
    | bvAbbrev he' hr' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_defaultDomain] at hr'; cases hr'
    | _ => clashz
  | bvOfNat he hw hk ihw ihk => intro r' h' hk; cases h' with
    | bvOfNat he' hw' hk' =>
      injz he he'
      have h1 := val_eq (ihw hw' rfl)
      subst h1
      have h2 := val_eq (ihk hk' rfl)
      subst h2; rfl
    | _ => clashz
  | bvInhabited he hw ihw => intro r' h' hk; cases h' with
    | bvInhabited he' hw' =>
      injz he he'
      have h1 := val_eq (ihw hw' rfl)
      subst h1; rfl
    | _ => clashz
  | boolInhabited he => intro r' h' hk; cases h' with
    | boolInhabited he' => rfl
    | bvAbbrev he' hr' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_instInhabitedBool] at hr'; cases hr'
    | _ => clashz
  | sigPure he hd ht hx ihd iht ihx => intro r' h' hk; cases h' with
    | sigPure he' hd' ht' hx' =>
      injz he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihx hx' rfl)
      subst h3; rfl
    | _ => clashz
  | sigRegister he hd ht hi hs ihd iht ihi ihs => intro r' h' hk; cases h' with
    | sigRegister he' hd' ht' hi' hs' =>
      injz he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihi hi' rfl)
      subst h3
      have h4 := val_eq (ihs hs' rfl)
      subst h4; rfl
    | _ => clashz
  | sigMux he hd ht hc ha hb ihd iht ihc iha ihb => intro r' h' hk; cases h' with
    | sigMux he' hd' ht' hc' ha' hb' =>
      injz he he'
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
    | _ => clashz
  | sigAddBV he hd hw ha hb ihd ihw iha ihb => intro r' h' hk; cases h' with
    | sigAddBV he' hd' hw' ha' hb' =>
      injz he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := val_eq (ihw hw' rfl)
      subst h2
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashz
  | sigLoop he hd ht hi hf ihd iht ihi ihf => intro r' h' hk; cases h' with
    | sigLoop he' hd' ht' hi' hf' =>
      injz he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihi hi' rfl)
      subst h3
      have h4 := val_eq (ihf hf' rfl)
      subst h4; rfl
    | _ => clashz
  | lam he hA hb ihA ihb => intro r' h' hk; cases h' with
    | lam he' hA' hb' =>
      injz he he'
      have h1 := ty_eq (ihA hA' rfl)
      subst h1
      have h2 : ∀ a, _ = _ := fun a => (val_inj (ihb a (hb' a) rfl)).1
      have h2' := funext h2
      subst h2'
      have h3 : _ = _ := funext fun a => eq_of_heq (val_inj (ihb a (hb' a) rfl)).2
      subst h3; rfl
    | _ => clashz
  | letE he hA hc hv hb ihA ihv ihb => intro r' h' hk; cases h' with
    | letE he' hA' hc' hv' hb' =>
      injz he he'
      have h1 := ty_eq (ihA hA' rfl)
      subst h1
      have h2 := val_eq (ihv hv' rfl)
      subst h2
      exact ihb hb' rfl
    | zeta he' hA' h2 =>
      injz he he'
      simp_all
    | _ => clashz
  | sigBeqBV he hd hw ha hb ihd ihw iha ihb => intro r' h' hk; cases h' with
    | sigBeqBV he' hd' hw' ha' hb' =>
      injz he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := val_eq (ihw hw' rfl)
      subst h2
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashz
  | sigAndBool he hd ha hb ihd iha ihb => intro r' h' hk; cases h' with
    | sigAndBool he' hd' ha' hb' =>
      injz he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashz
  | sigOrBool he hd ha hb ihd iha ihb => intro r' h' hk; cases h' with
    | sigOrBool he' hd' ha' hb' =>
      injz he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashz
  | sigNotBool he hd ha ihd iha => intro r' h' hk; cases h' with
    | sigNotBool he' hd' ha' =>
      injz he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h3 := val_eq (iha ha' rfl)
      subst h3; rfl
    | _ => clashz
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
      simp_all [stopR, Res.kind, headStop, appFn]
    | _ => clashz
  | unf hs hu h ih => intro r' h' hk; cases h' with
    | unf hs' hu' h' =>
      have e1 := Option.some.inj (hu.symm.trans hu')
      subst e1
      exact ih h' hk
    | mapFst he' hd' hp' ht' ha' hb' hs' hstuck' => exact (mapStuck_unf_false hstuck' hu h).elim
    | mapSnd he' hd' hp' ht' ha' hb' hs' hstuck' => exact (mapStuck_unf_false hstuck' hu h).elim
    | prodMk he' hc' ha' hb' hx' hy' => subst he'; simp [unfoldAt, appFn_appN, hc'] at hu
    | unitVal he' hc' => subst he'; simp [unfoldAt, appFn, hc'] at hu
    | _ => clashz
  | beta hb h ih => intro r' h' hk; cases h' with
    | beta hb' h' =>
      have e1 := Option.some.inj (hb.symm.trans hb')
      subst e1
      exact ih h' hk
    | _ => clashz
  | zeta he hA h ih => intro r' h' hk; cases h' with
    | zeta he' hA' h' =>
      injz he he'
      exact ih h' rfl
    | letE he' hA' hc' hv' hb' =>
      injz he he'
      simp_all
    | _ => clashz
  | projStep he hx h ih => intro r' h' hk; cases h' with
    | projStep he' hx' h' =>
      injz he he'
      have e1 := Option.some.inj (hx.symm.trans hx')
      subst e1
      exact ih h' hk
    | projCtor he' hh' hc' hS' hn' hf' h' =>
      injz he he'
      have := whStepR_ctor hc' _ hh'
      rw [hx] at this; cases this
    | _ => clashz
  | projCtor he hh hc hS hn hf h ih => intro r' h' hk; cases h' with
    | projCtor he' hh' hc' hS' hn' hf' h' =>
      injz he he'
      have h1 := Expr.const.inj (hh.symm.trans hh')
      obtain ⟨rfl, rfl⟩ := h1
      have h2 := ConstantInfo.ctorInfo.inj (Option.some.inj (hc.symm.trans hc'))
      subst h2
      have h3 := Option.some.inj (hf.symm.trans hf')
      subst h3
      exact ih h' hk
    | projStep he' hx' h' =>
      injz he he'
      have := whStepR_ctor hc _ hh
      rw [hx'] at this; cases this
    | _ => clashz
  | recIota hf hi hr h ih => intro r' h' hk; cases h' with
    | recIota hf' hi' hr' h' =>
      have e1 := Option.some.inj (hr.symm.trans hr')
      subst e1
      exact ih h' hk
    | _ => clashz
  | prodTy he ha hb iha ihb => intro r' h' hk; cases h' with
    | prodTy he' ha' hb' =>
      injz he he'
      have h1 := ty_eq (iha ha' rfl)
      subst h1
      have h2 := ty_eq (ihb hb' rfl)
      subst h2; rfl
    | _ => clashz
  | punitTy he => intro r' h' hk; cases h' with
    | punitTy he' => rfl
    | _ => clashz
  | unitVal he hc => intro r' h' hk; cases h' with
    | unitVal he' hc' => rfl
    | unf hs' hu' h' => subst he; simp [unfoldAt, appFn, hc] at hu'
    | _ => clashz
  | prodMk he hc ha hb hx hy iha ihb ihx ihy => intro r' h' hk; cases h' with
    | prodMk he' hc' ha' hb' hx' hy' =>
      injz he he'
      have h1 := ty_eq (iha ha' rfl)
      subst h1
      have h2 := ty_eq (ihb hb' rfl)
      subst h2
      have h3 := val_eq (ihx hx' rfl)
      subst h3
      have h4 := val_eq (ihy hy' rfl)
      subst h4; rfl
    | unf hs' hu' h' => subst he; simp [unfoldAt, appFn_appN, hc] at hu'
    | _ => clashz
  | mapFst he hd hp ht ha hb hs hstuck ihd ihp iht iha ihb ihs => intro r' h' hk; cases h' with
    | mapFst he' hd' hp' ht' ha' hb' hs' hstuck' =>
      injz he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iha ha' rfl)
      subst h2
      have h3 := ty_eq (ihb hb' rfl)
      subst h3
      have h4 := val_eq (ihs hs' rfl)
      subst h4; rfl
    | unf hs' hu' h' => exact (mapStuck_unf_false hstuck hu' h').elim
    | _ => clashz
  | mapSnd he hd hp ht ha hb hs hstuck ihd ihp iht iha ihb ihs => intro r' h' hk; cases h' with
    | mapSnd he' hd' hp' ht' ha' hb' hs' hstuck' =>
      injz he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iha ha' rfl)
      subst h2
      have h3 := ty_eq (ihb hb' rfl)
      subst h3
      have h4 := val_eq (ihs hs' rfl)
      subst h4; rfl
    | unf hs' hu' h' => exact (mapStuck_unf_false hstuck hu' h').elim
    | _ => clashz

theorem cdz_fun {env : Environment} {ρ : Val} {e : Expr} {α α' : Type} {v : α} {v' : α'} (h : CDZ env ρ e α v) (h' : CDZ env ρ e α' v') :
    α = α' ∧ HEq v v' := val_inj (dz_fun h h' rfl)

theorem tdz_fun {env : Environment} {ρ : Val} {e : Expr} {T T' : Type} (h : TDZ env ρ e T) (h' : TDZ env ρ e T') : T = T' := ty_eq (dz_fun h h' rfl)

theorem cdz_eq {env : Environment} {ρ : Val} {e : Expr} {α : Type} {v v' : α} (h : CDZ env ρ e α v) (h' : CDZ env ρ e α v') : v = v' :=
  eq_of_heq (cdz_fun h h').2

theorem cdz_of_cdy {env : Environment} {ρ : Val} {e : Expr} {α : Type} {v : α} (h : CDY env ρ e α v) : CDZ env ρ e α v := dy_to_dz h
theorem cdz_of_cdx {env : Environment} {ρ : Val} {e : Expr} {α : Type} {v : α} (h : CDX env ρ e α v) : CDZ env ρ e α v := dx_to_dz h

/-! ## 7. the carriers and their consumers, in ONE environment

`CircCVY` (S1p) is over `DY`; `CircCVZ` is over `DZ`. Both read the declaration and unfold it in the same `env`. There is NO map `CDY → CDX` or `CDZ → CDY`: a derivation that uses `recIota` or a wiring rule is a
`CDY`/`CDZ` derivation only. The statement `HftObCDX` (S1p) can be filled only by a `CDX` derivation (no `recIota`); the obligations below are the ones a `recIota`/wiring derivation can fill. -/

def CircCVZ : ConstValueRel := fun env X α v =>
  ∃ d : DefinitionVal, env.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ CDZ env [] d.value α v

theorem circCVY_to_Z (env : Environment) {X : Name} {α : Type} {v : α} (h : CircCVY env X α v) : CircCVZ env X α v := by
  obtain ⟨d, hd, hl, hv⟩ := h
  exact ⟨d, hd, hl, dy_to_dz hv⟩

theorem circCVS_to_Z (env : Environment) {X : Name} {α : Type} {v : α} (h : CircCVS env X α v) : CircCVZ env X α v := circCVY_to_Z env (circCVS_to_Y env h)

theorem circCVZ_functional : ConstValueFunctional CircCVZ := by
  intro env c α β v w ⟨d, hd, _, hv⟩ ⟨d', hd', _, hv'⟩
  rw [hd] at hd'
  have := ConstantInfo.defnInfo.inj (Option.some.inj hd')
  subst this
  exact cdz_fun hv hv'

/-- the source meanings over the `DY` / `DZ` carriers (same shape as `SourceDenotes`) -/
def SourceDenotesY (env : Environment) (source : Name) (params : List (String × Nat)) (sh : SigShape) (m : sh.Ty) : Prop :=
  params = [] ∧ ∃ ci : ConstantInfo, env.find? source = some ci ∧ shapeOf ci = some sh ∧ CircCVY env source sh.Ty m
def SourceDenotesZ (env : Environment) (source : Name) (params : List (String × Nat)) (sh : SigShape) (m : sh.Ty) : Prop :=
  params = [] ∧ ∃ ci : ConstantInfo, env.find? source = some ci ∧ shapeOf ci = some sh ∧ CircCVZ env source sh.Ty m

theorem sourceDenotesS_to_Y {env : Environment} {source : Name} {params : List (String × Nat)} {sh : SigShape} {m : sh.Ty}
    (h : SourceDenotesS env source params sh m) : SourceDenotesY env source params sh m := by
  obtain ⟨hp, ci, hci, hsh, hcv⟩ := h
  exact ⟨hp, ci, hci, hsh, circCVS_to_Y env hcv⟩

theorem sourceDenotesY_to_Z {env : Environment} {source : Name} {params : List (String × Nat)} {sh : SigShape} {m : sh.Ty}
    (h : SourceDenotesY env source params sh m) : SourceDenotesZ env source params sh m := by
  obtain ⟨hp, ci, hci, hsh, hcv⟩ := h
  exact ⟨hp, ci, hci, hsh, circCVY_to_Z env hcv⟩

/-- `DeclConnect` is monotone in the carrier -/
theorem declConnect_of_cv {ι : Type} {dom : ι → DomainConfig} (CV CV' : ConstValueRel) (hCV : ∀ env X α (v : α), CV env X α v → CV' env X α v)
    (env₀ : Environment) (P : Pkgs ι dom) (Tgt : Name → Prop) (h : DeclConnect CV env₀ P Tgt) : DeclConnect CV' env₀ P Tgt := by
  rw [declConnect_eq] at h ⊢
  intro X hX p hp
  obtain ⟨ci, sh, v, h1, h2, h3, h4, h5⟩ := h X hX p hp
  exact ⟨ci, sh, v, h1, h2, h3, hCV env₀ X sh.Ty v h4, h5⟩

theorem declConnect_S_to_Y {ι : Type} {dom : ι → DomainConfig} (env₀ : Environment) (P : Pkgs ι dom) (Tgt : Name → Prop)
    (h : DeclConnect CircCVS env₀ P Tgt) : DeclConnect CircCVY env₀ P Tgt := declConnect_of_cv _ _ (fun env _ _ _ hv => circCVS_to_Y env hv) env₀ P Tgt h
theorem declConnect_Y_to_Z {ι : Type} {dom : ι → DomainConfig} (env₀ : Environment) (P : Pkgs ι dom) (Tgt : Name → Prop)
    (h : DeclConnect CircCVY env₀ P Tgt) : DeclConnect CircCVZ env₀ P Tgt := declConnect_of_cv _ _ (fun env _ _ _ hv => circCVY_to_Z env hv) env₀ P Tgt h

/-- the obligation of the S1k statement over `DY` / `DZ`, in ONE environment -/
def HftObCDY (env : Environment) : Prop := CDY env [] Tools.ShippingFGCircuitS1kStmt.hftRootValue (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft)
  Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte
def HftObCDZ (env : Environment) : Prop := CDZ env [] Tools.ShippingFGCircuitS1kStmt.hftRootValue (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft)
  Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte

theorem hftObCDY_of_X {env : Environment} (h : HftObCDX env) : HftObCDY env := dx_to_dy h
theorem hftObCDZ_of_Y {env : Environment} (h : HftObCDY env) : HftObCDZ env := dy_to_dz h

theorem circCVY_hft_of_obCDY {env : Environment} {d : DefinitionVal} (hd : env.find? Tools.ShippingFGCircuitS1kStmt.hftRoot = some (.defnInfo d))
    (hl : d.levelParams = []) (hv : d.value = Tools.ShippingFGCircuitS1kStmt.hftRootValue) (h : HftObCDY env) :
    CircCVY env Tools.ShippingFGCircuitS1kStmt.hftRoot (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft) Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte :=
  ⟨d, hd, hl, by rw [hv]; exact h⟩

theorem circCVZ_hft_of_obCDZ {env : Environment} {d : DefinitionVal} (hd : env.find? Tools.ShippingFGCircuitS1kStmt.hftRoot = some (.defnInfo d))
    (hl : d.levelParams = []) (hv : d.value = Tools.ShippingFGCircuitS1kStmt.hftRootValue) (h : HftObCDZ env) :
    CircCVZ env Tools.ShippingFGCircuitS1kStmt.hftRoot (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft) Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte :=
  ⟨d, hd, hl, by rw [hv]; exact h⟩

/-- run side: the carriers read at the START world's environment -/
def CircCVYAt (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (X : Name) (α : Type) (v : α) : Prop := CircCVY (envAt cref w) X α v
def CircCVZAt (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (X : Name) (α : Type) (v : α) : Prop := CircCVZ (envAt cref w) X α v

theorem circCVZ_at_of_getEnv {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {e : Environment} (h : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w e w') {X : Name} {α : Type} {v : α} :
    CircCVZ e X α v ↔ CircCVZ (envAt cref w) X α v := by
  rw [Tools.ShippingEntryReadsLinked.getEnv_value h]

theorem circCVY_at_of_getEnv {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {e : Environment} (h : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w e w') {X : Name} {α : Type} {v : α} :
    CircCVY e X α v ↔ CircCVY (envAt cref w) X α v := by
  rw [Tools.ShippingEntryReadsLinked.getEnv_value h]

theorem circCVZ_hft_run (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) {d : DefinitionVal}
    (hd : (envAt cref w).find? Tools.ShippingFGCircuitS1kStmt.hftRoot = some (.defnInfo d)) (hl : d.levelParams = [])
    (hv : d.value = Tools.ShippingFGCircuitS1kStmt.hftRootValue) (h : HftObCDZ (envAt cref w)) :
    CircCVZAt cref w Tools.ShippingFGCircuitS1kStmt.hftRoot (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft) Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte :=
  circCVZ_hft_of_obCDZ hd hl hv h

theorem circCVY_hft_run (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) {d : DefinitionVal}
    (hd : (envAt cref w).find? Tools.ShippingFGCircuitS1kStmt.hftRoot = some (.defnInfo d)) (hl : d.levelParams = [])
    (hv : d.value = Tools.ShippingFGCircuitS1kStmt.hftRootValue) (h : HftObCDY (envAt cref w)) :
    CircCVYAt cref w Tools.ShippingFGCircuitS1kStmt.hftRoot (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft) Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte :=
  circCVY_hft_of_obCDY hd hl hv h

end Tools.ShippingFGCircuitS1rCD

#print axioms Tools.ShippingFGCircuitS1rCD.dy_to_dz
#print axioms Tools.ShippingFGCircuitS1rCD.dz_fun
