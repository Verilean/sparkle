import Tools.ShippingFGCircuitS1wTbl
set_option autoImplicit false
-- FG circuit pilot S2b: the family `DS` = `DW` with a NARROW level rule for `Inhabited.mk` (one level `u`, closed value 1, evidence by `Eq.refl`), docs/FG-CIRCUIT-PILOT.md §30.
-- No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.

/-! # S2b: `DS`

`DS` has exactly the constructors of `DW` (S1s, docs §23) except that `inhMk` is generalised from the level list `[1]` to `[u]` with the evidence `lvlNat u = some 1`.
`lvlNat` is an own, kernel-evaluable evaluator of CLOSED levels (`zero`/`succ`/`max`/`imax`; a `param`/`mvar` gives `none`): `Lean.Level.normalize` is `opaque` (the kernel cannot run it),
so it cannot be the evidence. The old rule is the case `u = 1` (`ds_inhMk_one`). Nothing else is generalised; `T : Type`, the same-env constructor fact and the typed derivations of `t`, `x` stay. -/
namespace Tools.ShippingFGCircuitS2bShare
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5ConstValueE Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD Tools.ShippingFGCircuitS1wTbl
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingEntrySoundness (RunsTo)

/-- the value of a CLOSED level (kernel-evaluable; `none` for a parameter or a metavariable) -/
def lvlNat : Level → Option Nat
  | .zero => some 0
  | .succ l => (lvlNat l).map (· + 1)
  | .max a b => match lvlNat a, lvlNat b with
    | some x, some y => some (if x ≤ y then y else x)
    | _, _ => none
  | .imax a b => match lvlNat a, lvlNat b with
    | some x, some y => some (if y = 0 then 0 else if x ≤ y then y else x)
    | _, _ => none
  | _ => none

theorem lvlNat_one : lvlNat (.succ .zero) = some 1 := rfl
theorem lvlNat_max11 : lvlNat (.max (.succ .zero) (.succ .zero)) = some 1 := rfl
theorem lvlNat_max12 : lvlNat (.max (.succ .zero) (.succ (.succ .zero))) = some 2 := rfl
theorem lvlNat_zero : lvlNat .zero = some 0 := rfl
theorem lvlNat_param (n : Name) : lvlNat (.param n) = none := rfl

/-! ## 2. the stop heads -/

def newStopSC (c : Name) : Bool := [``Sparkle.Core.Signal.bundle2, ``Inhabited.default].contains c
def newStopS (e : Expr) : Bool :=
  match appFn e with
  | .const c _ => newStopSC c
  | _ => false
/-- the stop condition of `unf` in `DS`: the `DZ` one, or a new stop head -/
def stopS (r : Res) (e : Expr) : Bool := stopR r e || newStopS e

theorem newStopSC_bundle2 : newStopSC ``Sparkle.Core.Signal.bundle2 = true := by decide
theorem newStopSC_default : newStopSC ``Inhabited.default = true := by decide

/-! ## 3. the relation -/


section
local macro "CDs " env:term:max ρ:term:max e:term:max α:term:max v:term:max : term => `($(Lean.mkIdent `Tools.ShippingFGCircuitS2bShare.DS) $env $ρ $e (Res.val $α $v))
local macro "TDs " env:term:max ρ:term:max e:term:max T:term:max : term => `($(Lean.mkIdent `Tools.ShippingFGCircuitS2bShare.DS) $env $ρ $e (Res.ty $T))
inductive DS (env : Environment) : Val → Expr → Res → Prop
  | nat {ρ : Val} {e : Expr} (he : e = .const ``Nat []) : TDs env ρ e Nat
  | bool {ρ : Val} {e : Expr} (he : e = .const ``Bool []) : TDs env ρ e Bool
  | domainConfig {ρ : Val} {e : Expr} (he : e = .const ``Sparkle.Core.Domain.DomainConfig []) : TDs env ρ e DomainConfig
  | bitvec {ρ : Val} {e w : Expr} {n : Nat} (he : e = appN ``BitVec [] [w]) (hw : CDs env ρ w Nat n) : TDs env ρ e (BitVec n)
  | signal {ρ : Val} {e d t : Expr} {D : DomainConfig} {T : Type} (he : e = appN ``Signal [.zero] [d, t])
      (hd : CDs env ρ d DomainConfig D) (ht : TDs env ρ t T) : TDs env ρ e (Signal D T)

  | bvar {ρ : Val} {i : Nat} {τ : Expr} {T : Type} {a : T} (h : ρ[i]? = some ⟨τ, ⟨T, a⟩⟩) : CDs env ρ (.bvar i) T a
  | natLit {ρ : Val} {e : Expr} {n : Nat}
      (he : e = appN ``OfNat.ofNat [.zero] [.const ``Nat [], .lit (.natVal n), appN ``instOfNatNat [] [.lit (.natVal n)]]) :
      CDs env ρ e Nat n
  | domDefault {ρ : Val} {e : Expr} (he : e = .const ``Sparkle.Core.Domain.defaultDomain []) :
      CDs env ρ e DomainConfig defaultDomain
  | bvOfNat {ρ : Val} {e w k : Expr} {W K : Nat} (he : e = appN ``BitVec.ofNat [] [w, k])
      (hw : CDs env ρ w Nat W) (hk : CDs env ρ k Nat K) : CDs env ρ e (BitVec W) (BitVec.ofNat W K)
  | bvInhabited {ρ : Val} {e w : Expr} {W : Nat} (he : e = appN ``BitVec.instInhabited [] [w]) (hw : CDs env ρ w Nat W) :
      CDs env ρ e (Inhabited (BitVec W)) (inferInstance : Inhabited (BitVec W))
  | boolInhabited {ρ : Val} {e : Expr} (he : e = .const ``instInhabitedBool []) :
      CDs env ρ e (Inhabited Bool) (inferInstance : Inhabited Bool)
  | sigPure {ρ : Val} {e d t x : Expr} {D : DomainConfig} {T : Type} {a : T}
      (he : e = appN ``Signal.pure [.zero] [d, t, x]) (hd : CDs env ρ d DomainConfig D) (ht : TDs env ρ t T) (hx : CDs env ρ x T a) :
      CDs env ρ e (Signal D T) (Signal.pure a)
  | sigRegister {ρ : Val} {e d t i s : Expr} {D : DomainConfig} {T : Type} {a : T} {sv : Signal D T}
      (he : e = appN ``Signal.register [.zero] [d, t, i, s]) (hd : CDs env ρ d DomainConfig D) (ht : TDs env ρ t T)
      (hi : CDs env ρ i T a) (hs : CDs env ρ s (Signal D T) sv) : CDs env ρ e (Signal D T) (Signal.register a sv)
  | sigMux {ρ : Val} {e d t c a b : Expr} {D : DomainConfig} {T : Type} {cv : Signal D Bool} {av bv : Signal D T}
      (he : e = appN ``Signal.mux [.zero] [d, t, c, a, b]) (hd : CDs env ρ d DomainConfig D) (ht : TDs env ρ t T)
      (hc : CDs env ρ c (Signal D Bool) cv) (ha : CDs env ρ a (Signal D T) av) (hb : CDs env ρ b (Signal D T) bv) :
      CDs env ρ e (Signal D T) (Signal.mux cv av bv)
  | sigAddBV {ρ : Val} {e d w a b : Expr} {D : DomainConfig} {W : Nat} {av bv : Signal D (BitVec W)}
      (he : e = appN ``HAdd.hAdd [.zero, .zero, .zero]
        [appN ``Signal [.zero] [d, appN ``BitVec [] [w]], appN ``Signal [.zero] [d, appN ``BitVec [] [w]],
         appN ``Signal [.zero] [d, appN ``BitVec [] [w]], appN ``Sparkle.Core.Signal.instHAddSignalBitVec [] [d, w], a, b])
      (hd : CDs env ρ d DomainConfig D) (hw : CDs env ρ w Nat W)
      (ha : CDs env ρ a (Signal D (BitVec W)) av) (hb : CDs env ρ b (Signal D (BitVec W)) bv) :
      CDs env ρ e (Signal D (BitVec W)) (@HAdd.hAdd _ _ _ (@Sparkle.Core.Signal.instHAddSignalBitVec D W) av bv)
  | sigLoop {ρ : Val} {e d t inst f : Expr} {D : DomainConfig} {T : Type} {iv : Inhabited T} {g : Signal D T → Signal D T}
      (he : e = appN ``Signal.loop [] [d, t, inst, f]) (hd : CDs env ρ d DomainConfig D) (ht : TDs env ρ t T)
      (hi : CDs env ρ inst (Inhabited T) iv) (hf : CDs env ρ f (Signal D T → Signal D T) g) :
      CDs env ρ e (Signal D T) (@Signal.loop D T iv g)
  | lam {ρ : Val} {e A body : Expr} {n : Name} {bi : BinderInfo} {TA : Type} {TB : TA → Type} {f : (a : TA) → TB a}
      (he : e = .lam n A body bi) (hA : TDs env ρ A TA) (hb : ∀ a : TA, CDs env (⟨A, ⟨TA, a⟩⟩ :: ρ) body (TB a) (f a)) :
      CDs env ρ e ((a : TA) → TB a) f
  | letE {ρ : Val} {e A v body : Expr} {n : Name} {nd : Bool} {TA T : Type} {a : TA} {r : T}
      (he : e = .letE n A v body nd) (hA : TDs env ρ A TA) (hc : coreHead A = true) (hv : CDs env ρ v TA a)
      (hb : CDs env (⟨A, ⟨TA, a⟩⟩ :: ρ) body T r) : CDs env ρ e T r
  | sigBeqBV {ρ : Val} {e d w a b : Expr} {D : DomainConfig} {W : Nat} {av bv : Signal D (BitVec W)}
      (he : e = appN ``Sparkle.Core.Signal.Signal.beq []
        [appN ``BitVec [] [w], d, appN ``instBEqOfDecidableEq [.zero] [appN ``BitVec [] [w], appN ``instDecidableEqBitVec [] [w]], a, b])
      (hd : CDs env ρ d DomainConfig D) (hw : CDs env ρ w Nat W)
      (ha : CDs env ρ a (Signal D (BitVec W)) av) (hb : CDs env ρ b (Signal D (BitVec W)) bv) :
      CDs env ρ e (Signal D Bool) (@Signal.beq (BitVec W) D (@instBEqOfDecidableEq (BitVec W) (@instDecidableEqBitVec W)) av bv)
  | sigAndBool {ρ : Val} {e d a b : Expr} {D : DomainConfig} {av bv : Signal D Bool}
      (he : e = appN ``HAnd.hAnd [.zero, .zero, .zero]
        [appN ``Signal [.zero] [d, .const ``Bool []], appN ``Signal [.zero] [d, .const ``Bool []],
         appN ``Signal [.zero] [d, .const ``Bool []], appN ``Sparkle.Core.Signal.instHAndSignalBool [] [d], a, b])
      (hd : CDs env ρ d DomainConfig D) (ha : CDs env ρ a (Signal D Bool) av) (hb : CDs env ρ b (Signal D Bool) bv) :
      CDs env ρ e (Signal D Bool) (@HAnd.hAnd _ _ _ (@Sparkle.Core.Signal.instHAndSignalBool D) av bv)
  | sigOrBool {ρ : Val} {e d a b : Expr} {D : DomainConfig} {av bv : Signal D Bool}
      (he : e = appN ``HOr.hOr [.zero, .zero, .zero]
        [appN ``Signal [.zero] [d, .const ``Bool []], appN ``Signal [.zero] [d, .const ``Bool []],
         appN ``Signal [.zero] [d, .const ``Bool []], appN ``Sparkle.Core.Signal.instHOrSignalBool [] [d], a, b])
      (hd : CDs env ρ d DomainConfig D) (ha : CDs env ρ a (Signal D Bool) av) (hb : CDs env ρ b (Signal D Bool) bv) :
      CDs env ρ e (Signal D Bool) (@HOr.hOr _ _ _ (@Sparkle.Core.Signal.instHOrSignalBool D) av bv)
  | sigNotBool {ρ : Val} {e d a : Expr} {D : DomainConfig} {av : Signal D Bool}
      (he : e = appN ``Complement.complement [.zero]
        [appN ``Signal [.zero] [d, .const ``Bool []], appN ``Sparkle.Core.Signal.instComplementSignalBool [] [d], a])
      (hd : CDs env ρ d DomainConfig D) (ha : CDs env ρ a (Signal D Bool) av) :
      CDs env ρ e (Signal D Bool) (@Complement.complement _ (@Sparkle.Core.Signal.instComplementSignalBool D) av)
  | bvAbbrev {ρ : Val} {e : Expr} {c : Name} {n : Nat} {v : BitVec n} (he : e = .const c []) (h : bvAbbrevRow c = some ⟨n, v⟩) :
      CDs env ρ e (BitVec n) v
  /-- delta + beta of a user definition, for a value OR a type; `stopS r e` is false (not a primitive head / a core type head) -/
  | unf {ρ : Val} {e e' : Expr} {r : Res}
      (hs : stopS r e = false) (hu : unfoldAt env e = some e') (h : DS env ρ e' r) : DS env ρ e r
  | beta {ρ : Val} {e e' : Expr} {r : Res}
      (hb : headRedexR env e = some e') (h : DS env ρ e' r) : DS env ρ e r
  | zeta {ρ : Val} {e A v body : Expr} {n : Name} {nd : Bool} {α : Type} {r : α}
      (he : e = .letE n A v body nd) (hA : coreHead A = false) (h : CDs env ρ (instE body v 0) α r) : CDs env ρ e α r
  | projStep {ρ : Val} {e x x' : Expr} {S : Name} {i : Nat} {r : Res}
      (he : e = .proj S i x) (hx : whStepR env x = some x') (h : DS env ρ (.proj S i x') r) : DS env ρ e r
  | projCtor {ρ : Val} {e x fld : Expr} {S ctor : Name} {ls : List Level} {cv : ConstructorVal} {i : Nat} {r : Res}
      (he : e = .proj S i x) (hh : appFn x = .const ctor ls) (hc : env.find? ctor = some (.ctorInfo cv)) (hS : cv.induct = S)
      (hn : (appArgs x).length = cv.numParams + cv.numFields) (hf : (appArgs x)[cv.numParams + i]? = some fld)
      (h : DS env ρ fld r) : DS env ρ e r
  | recIota {ρ : Val} {e e' : Expr} {ls : List Level} {ri : RecursorVal} {r : Res}
      (hf : appFn e = .const ``List.rec ls) (hi : env.find? ``List.rec = some (.recInfo ri)) (hr : recStep env e = some e') (h : DS env ρ e' r) : DS env ρ e r
  /-- NEW (S1r). a projection whose structure argument is itself a `List.rec` redex (`recStep`): step inside (`whStepR` does this only under another projection/application) -/
  | projRec {ρ : Val} {e x x' : Expr} {S : Name} {i : Nat} {ls : List Level} {ri : RecursorVal} {r : Res}
      (he : e = .proj S i x) (hf : appFn x = .const ``List.rec ls) (hi : env.find? ``List.rec = some (.recInfo ri)) (hr : recStep env x = some x')
      (h : DS env ρ (.proj S i x') r) : DS env ρ e r
  /-- NEW (S1r). `Prod a b` -/
  | prodTy {ρ : Val} {e a b : Expr} {A B : Type} (he : e = appN ``Prod [.zero, .zero] [a, b]) (ha : TDs env ρ a A) (hb : TDs env ρ b B) : TDs env ρ e (A × B)
  /-- NEW (S1r). `PUnit.{1}` (the type `Unit` unfolds to it by `unf`) -/
  | punitTy {ρ : Val} {e : Expr} (he : e = .const ``PUnit [.succ .zero]) : TDs env ρ e Unit
  /-- NEW (S1r). `PUnit.unit.{1}`; the constructor is a `ctorInfo` of `env` (so `unf` cannot also apply) -/
  | unitVal {ρ : Val} {e : Expr} {cv : ConstructorVal} (he : e = .const ``PUnit.unit [.succ .zero]) (hc : env.find? ``PUnit.unit = some (.ctorInfo cv)) :
      CDs env ρ e Unit ()
  /-- NEW (S1r). `Prod.mk a b x y`; the constructor is a `ctorInfo` of `env` -/
  | prodMk {ρ : Val} {e a b x y : Expr} {A B : Type} {xv : A} {yv : B} {cv : ConstructorVal}
      (he : e = appN ``Prod.mk [.zero, .zero] [a, b, x, y]) (hc : env.find? ``Prod.mk = some (.ctorInfo cv))
      (ha : TDs env ρ a A) (hb : TDs env ρ b B) (hx : CDs env ρ x A xv) (hy : CDs env ρ y B yv) : CDs env ρ e (A × B) (xv, yv)
  /-- NEW (S1r). `Signal.map Prod.fst s` : the head constant, the function `Prod.fst`, the pair signal. The value is Lean's `Signal.map Prod.fst sv`; `signal_map_fst_at` is its equation at every time. -/
  | mapFst {ρ : Val} {e d tp ta a b s : Expr} {D : DomainConfig} {A B : Type} {sv : Signal D (A × B)}
      (he : e = appN ``Signal.map [.zero] [d, tp, ta, appN ``Prod.fst [.zero, .zero] [a, b], s])
      (hd : CDs env ρ d DomainConfig D) (hp : TDs env ρ tp (A × B)) (ht : TDs env ρ ta A) (ha : TDs env ρ a A) (hb : TDs env ρ b B)
      (hs : CDs env ρ s (Signal D (A × B)) sv) (hstuck : MapStuck env e) : CDs env ρ e (Signal D A) (Signal.map Prod.fst sv)
  /-- NEW (S1r). `Signal.map Prod.snd s` -/
  | mapSnd {ρ : Val} {e d tp tb a b s : Expr} {D : DomainConfig} {A B : Type} {sv : Signal D (A × B)}
      (he : e = appN ``Signal.map [.zero] [d, tp, tb, appN ``Prod.snd [.zero, .zero] [a, b], s])
      (hd : CDs env ρ d DomainConfig D) (hp : TDs env ρ tp (A × B)) (ht : TDs env ρ tb B) (ha : TDs env ρ a A) (hb : TDs env ρ b B)
      (hs : CDs env ρ s (Signal D (A × B)) sv) (hstuck : MapStuck env e) : CDs env ρ e (Signal D B) (Signal.map Prod.snd sv)
  /-- NEW (S2b). `Inhabited.mk.{u} T x` with ONE level `u` whose closed value is `1` (`lvlNat u = some 1`, evidence by `Eq.refl`, no `Level.normalize`: that is `opaque`, the kernel cannot run it):
      the instance VALUE `⟨v⟩` from the derivation of the field `x ↦ v`; a constructor of `env` (so `unf` cannot also apply). `T : Type` stays; the old rule is the case `u = 1`. -/
  | inhMk {ρ : Val} {e t x : Expr} {u : Level} {T : Type} {v : T} {cv : ConstructorVal} (he : e = appN ``Inhabited.mk [u] [t, x]) (hu : lvlNat u = some 1)
      (hc : env.find? ``Inhabited.mk = some (.ctorInfo cv)) (ht : TDs env ρ t T) (hx : CDs env ρ x T v) : CDs env ρ e (Inhabited T) (⟨v⟩ : Inhabited T)
  /-- NEW (S1s). `Inhabited.default.{1} T inst`: the default of the SAME instance, `iv.default`. `Inhabited.default` is a stop head of `unf` (`newStopS`) -/
  | inhDefault {ρ : Val} {e t inst : Expr} {T : Type} {iv : Inhabited T} (he : e = appN ``Inhabited.default [.succ .zero] [t, inst])
      (ht : TDs env ρ t T) (hi : CDs env ρ inst (Inhabited T) iv) : CDs env ρ e T iv.default
  /-- NEW (S1s). `bundle2.{0} d A B a b` (same `d` for both): the pairing of two signals of the same domain. The value is Lean's `bundle2 av bv` (its LOGICAL definition; `bundle2` has `implemented_by`, which is not proved to agree). `bundle2` is a stop head of `unf` -/
  | bundle2 {ρ : Val} {e d ta tb a b : Expr} {D : DomainConfig} {A B : Type} {av : Signal D A} {bv : Signal D B}
      (he : e = appN ``Sparkle.Core.Signal.bundle2 [.zero] [d, ta, tb, a, b]) (hd : CDs env ρ d DomainConfig D) (hta : TDs env ρ ta A) (htb : TDs env ρ tb B)
      (ha : CDs env ρ a (Signal D A) av) (hb : CDs env ρ b (Signal D B) bv) : CDs env ρ e (Signal D (A × B)) (Sparkle.Core.Signal.bundle2 av bv)
end

abbrev TDS (env : Environment) (ρ : Val) (e : Expr) (T : Type) : Prop := DS env ρ e (.ty T)
abbrev CDS (env : Environment) (ρ : Val) (e : Expr) (α : Type) (v : α) : Prop := DS env ρ e (.val α v)

/-! ## 4. exclusivity and functionality -/


/-- there is no derivation for an expression headed by the constructor `Signal.mk` (of `env`): no rule has that head -/
theorem ds_signalMk_false {env : Environment} {ρ : Val} {e : Expr} {r : Res} (h : DS env ρ e r) {ls : List Level} {cv : ConstructorVal}
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
theorem mapStuckS_unf_false {env : Environment} {ρ : Val} {e e' : Expr} {r : Res} (hs : MapStuck env e) (hu : unfoldAt env e = some e') (h : DS env ρ e' r) : False := by
  obtain ⟨e1, ls, cv, hu1, hf, hc⟩ := hs
  rw [hu1] at hu
  have := Option.some.inj hu
  subst this
  exact ds_signalMk_false h hf hc

/-! ## 6. functionality -/

macro "clashs" : tactic =>
  `(tactic| (exfalso
             try subst_vars
             try simp_all [Res.kind, stopS, stopR, newStopS, newStopSC_bundle2, newStopSC_default, tyHeadStop, headStop, appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, appFn, stopC_ofNat, stopC_defaultDomain, stopC_bvOfNat, stopC_bvInh,
               stopC_boolInh, stopC_pure, stopC_register, stopC_mux, stopC_hadd, stopC_loop, stopC_beq, stopC_hand, stopC_hor, stopC_compl, bvAbbrevRow_defaultDomain,
               bvAbbrevRow_instInhabitedBool, stopC_of_row, unfoldAt_bvar, unfoldAt_lam, unfoldAt_letE, unfoldAt_proj, unfoldAt_rec, headRedexR_rec, stopC_rec, bvAbbrevRow_rec,
               tyStopC_nat, tyStopC_bool, tyStopC_dc, tyStopC_bitvec, tyStopC_signal, tyStopC_prod, tyStopC_punit]
             try simp_all [Res.kind, stopS, stopR, newStopS, newStopSC_bundle2, newStopSC_default, tyHeadStop, headStop, headRedexR, appArgs, appFn, appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, unfoldAt_none_of_betaR, unfoldAt_rec, headRedexR_rec,
               tyStopC_nat, tyStopC_bool, tyStopC_dc, tyStopC_bitvec, tyStopC_signal, tyStopC_prod, tyStopC_punit]))

macro "injs" he:ident he':ident : tactic =>
  `(tactic| (have h := Eq.trans (Eq.symm $he) $he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.proj.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **functionality** of `DS`: two derivations of the same expression in the same valuation, of the same kind, have the same result. -/
theorem ds_fun {env : Environment} {ρ : Val} {e : Expr} {r : Res} (h : DS env ρ e r) : ∀ {r' : Res}, DS env ρ e r' → r.kind = r'.kind → r = r' := by
  induction h with
  | nat he => intro r' h' hk; cases h' with
    | nat he' => rfl
    | _ => clashs
  | bool he => intro r' h' hk; cases h' with
    | bool he' => rfl
    | _ => clashs
  | domainConfig he => intro r' h' hk; cases h' with
    | domainConfig he' => rfl
    | _ => clashs
  | bitvec he hw ihw => intro r' h' hk; cases h' with
    | bitvec he' hw' =>
      injs he he'
      have := val_eq (ihw hw' rfl)
      subst this; rfl
    | _ => clashs
  | signal he hd ht ihd iht => intro r' h' hk; cases h' with
    | signal he' hd' ht' =>
      injs he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2; rfl
    | _ => clashs
  | bvar hb => intro r' h' hk; cases h' with
    | bvar hb' =>
      have := Option.some.inj (hb.symm.trans hb')
      cases this
      rfl
    | _ => clashs
  | natLit he => intro r' h' hk; cases h' with
    | natLit he' =>
      injs he he'
      rfl
    | _ => clashs
  | domDefault he => intro r' h' hk; cases h' with
    | domDefault he' => rfl
    | bvAbbrev he' hr' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_defaultDomain] at hr'; cases hr'
    | _ => clashs
  | bvOfNat he hw hk ihw ihk => intro r' h' hk; cases h' with
    | bvOfNat he' hw' hk' =>
      injs he he'
      have h1 := val_eq (ihw hw' rfl)
      subst h1
      have h2 := val_eq (ihk hk' rfl)
      subst h2; rfl
    | _ => clashs
  | bvInhabited he hw ihw => intro r' h' hk; cases h' with
    | bvInhabited he' hw' =>
      injs he he'
      have h1 := val_eq (ihw hw' rfl)
      subst h1; rfl
    | _ => clashs
  | boolInhabited he => intro r' h' hk; cases h' with
    | boolInhabited he' => rfl
    | bvAbbrev he' hr' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_instInhabitedBool] at hr'; cases hr'
    | _ => clashs
  | sigPure he hd ht hx ihd iht ihx => intro r' h' hk; cases h' with
    | sigPure he' hd' ht' hx' =>
      injs he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihx hx' rfl)
      subst h3; rfl
    | _ => clashs
  | sigRegister he hd ht hi hs ihd iht ihi ihs => intro r' h' hk; cases h' with
    | sigRegister he' hd' ht' hi' hs' =>
      injs he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihi hi' rfl)
      subst h3
      have h4 := val_eq (ihs hs' rfl)
      subst h4; rfl
    | _ => clashs
  | sigMux he hd ht hc ha hb ihd iht ihc iha ihb => intro r' h' hk; cases h' with
    | sigMux he' hd' ht' hc' ha' hb' =>
      injs he he'
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
    | _ => clashs
  | sigAddBV he hd hw ha hb ihd ihw iha ihb => intro r' h' hk; cases h' with
    | sigAddBV he' hd' hw' ha' hb' =>
      injs he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := val_eq (ihw hw' rfl)
      subst h2
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashs
  | sigLoop he hd ht hi hf ihd iht ihi ihf => intro r' h' hk; cases h' with
    | sigLoop he' hd' ht' hi' hf' =>
      injs he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihi hi' rfl)
      subst h3
      have h4 := val_eq (ihf hf' rfl)
      subst h4; rfl
    | _ => clashs
  | lam he hA hb ihA ihb => intro r' h' hk; cases h' with
    | lam he' hA' hb' =>
      injs he he'
      have h1 := ty_eq (ihA hA' rfl)
      subst h1
      have h2 : ∀ a, _ = _ := fun a => (val_inj (ihb a (hb' a) rfl)).1
      have h2' := funext h2
      subst h2'
      have h3 : _ = _ := funext fun a => eq_of_heq (val_inj (ihb a (hb' a) rfl)).2
      subst h3; rfl
    | _ => clashs
  | letE he hA hc hv hb ihA ihv ihb => intro r' h' hk; cases h' with
    | letE he' hA' hc' hv' hb' =>
      injs he he'
      have h1 := ty_eq (ihA hA' rfl)
      subst h1
      have h2 := val_eq (ihv hv' rfl)
      subst h2
      exact ihb hb' rfl
    | zeta he' hA' h2 =>
      injs he he'
      simp_all
    | _ => clashs
  | sigBeqBV he hd hw ha hb ihd ihw iha ihb => intro r' h' hk; cases h' with
    | sigBeqBV he' hd' hw' ha' hb' =>
      injs he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := val_eq (ihw hw' rfl)
      subst h2
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashs
  | sigAndBool he hd ha hb ihd iha ihb => intro r' h' hk; cases h' with
    | sigAndBool he' hd' ha' hb' =>
      injs he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashs
  | sigOrBool he hd ha hb ihd iha ihb => intro r' h' hk; cases h' with
    | sigOrBool he' hd' ha' hb' =>
      injs he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashs
  | sigNotBool he hd ha ihd iha => intro r' h' hk; cases h' with
    | sigNotBool he' hd' ha' =>
      injs he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h3 := val_eq (iha ha' rfl)
      subst h3; rfl
    | _ => clashs
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
      simp_all [stopS, stopR, newStopS, Res.kind, headStop, appFn]
    | _ => clashs
  | unf hs hu h ih => intro r' h' hk; cases h' with
    | unf hs' hu' h' =>
      have e1 := Option.some.inj (hu.symm.trans hu')
      subst e1
      exact ih h' hk
    | mapFst he' hd' hp' ht' ha' hb' hs' hstuck' => exact (mapStuckS_unf_false hstuck' hu h).elim
    | mapSnd he' hd' hp' ht' ha' hb' hs' hstuck' => exact (mapStuckS_unf_false hstuck' hu h).elim
    | prodMk he' hc' ha' hb' hx' hy' => subst he'; simp [unfoldAt, appFn_appN, hc'] at hu
    | unitVal he' hc' => subst he'; simp [unfoldAt, appFn, hc'] at hu
    | inhMk he' hu' hc' ht' hx' => subst he'; simp [unfoldAt, appFn_appN, hc'] at hu
    | _ => clashs
  | beta hb h ih => intro r' h' hk; cases h' with
    | beta hb' h' =>
      have e1 := Option.some.inj (hb.symm.trans hb')
      subst e1
      exact ih h' hk
    | _ => clashs
  | zeta he hA h ih => intro r' h' hk; cases h' with
    | zeta he' hA' h' =>
      injs he he'
      exact ih h' rfl
    | letE he' hA' hc' hv' hb' =>
      injs he he'
      simp_all
    | _ => clashs
  | projStep he hx h ih => intro r' h' hk; cases h' with
    | projStep he' hx' h' =>
      injs he he'
      have e1 := Option.some.inj (hx.symm.trans hx')
      subst e1
      exact ih h' hk
    | projCtor he' hh' hc' hS' hn' hf' h' =>
      injs he he'
      have := whStepR_ctor hc' _ hh'
      rw [hx] at this; cases this
    | projRec he' hf' hi' hr' h' =>
      injs he he'
      have := whStepR_listRec hi' _ hf'
      rw [hx] at this; cases this
    | _ => clashs
  | projCtor he hh hc hS hn hf h ih => intro r' h' hk; cases h' with
    | projCtor he' hh' hc' hS' hn' hf' h' =>
      injs he he'
      have h1 := Expr.const.inj (hh.symm.trans hh')
      obtain ⟨rfl, rfl⟩ := h1
      have h2 := ConstantInfo.ctorInfo.inj (Option.some.inj (hc.symm.trans hc'))
      subst h2
      have h3 := Option.some.inj (hf.symm.trans hf')
      subst h3
      exact ih h' hk
    | projStep he' hx' h' =>
      injs he he'
      have := whStepR_ctor hc _ hh
      rw [hx'] at this; cases this
    | projRec he' hf' hi' hr' h' =>
      injs he he'
      have h1 := Expr.const.inj (hh.symm.trans hf')
      obtain ⟨rfl, rfl⟩ := h1
      rw [hc] at hi'; cases hi'
    | _ => clashs
  | recIota hf hi hr h ih => intro r' h' hk; cases h' with
    | recIota hf' hi' hr' h' =>
      have e1 := Option.some.inj (hr.symm.trans hr')
      subst e1
      exact ih h' hk
    | _ => clashs
  | projRec he hf hi hr h ih => intro r' h' hk; cases h' with
    | projRec he' hf' hi' hr' h' =>
      injs he he'
      have e1 := Option.some.inj (hr.symm.trans hr')
      subst e1
      exact ih h' hk
    | projStep he' hx' h' =>
      injs he he'
      have := whStepR_listRec hi _ hf
      rw [hx'] at this; cases this
    | projCtor he' hh' hc' hS' hn' hf' h' =>
      injs he he'
      have h1 := Expr.const.inj (hh'.symm.trans hf)
      obtain ⟨rfl, rfl⟩ := h1
      rw [hc'] at hi; cases hi
    | _ => clashs
  | prodTy he ha hb iha ihb => intro r' h' hk; cases h' with
    | prodTy he' ha' hb' =>
      injs he he'
      have h1 := ty_eq (iha ha' rfl)
      subst h1
      have h2 := ty_eq (ihb hb' rfl)
      subst h2; rfl
    | _ => clashs
  | punitTy he => intro r' h' hk; cases h' with
    | punitTy he' => rfl
    | _ => clashs
  | unitVal he hc => intro r' h' hk; cases h' with
    | unitVal he' hc' => rfl
    | unf hs' hu' h' => subst he; simp [unfoldAt, appFn, hc] at hu'
    | _ => clashs
  | prodMk he hc ha hb hx hy iha ihb ihx ihy => intro r' h' hk; cases h' with
    | prodMk he' hc' ha' hb' hx' hy' =>
      injs he he'
      have h1 := ty_eq (iha ha' rfl)
      subst h1
      have h2 := ty_eq (ihb hb' rfl)
      subst h2
      have h3 := val_eq (ihx hx' rfl)
      subst h3
      have h4 := val_eq (ihy hy' rfl)
      subst h4; rfl
    | unf hs' hu' h' => subst he; simp [unfoldAt, appFn_appN, hc] at hu'
    | _ => clashs
  | mapFst he hd hp ht ha hb hs hstuck ihd ihp iht iha ihb ihs => intro r' h' hk; cases h' with
    | mapFst he' hd' hp' ht' ha' hb' hs' hstuck' =>
      injs he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iha ha' rfl)
      subst h2
      have h3 := ty_eq (ihb hb' rfl)
      subst h3
      have h4 := val_eq (ihs hs' rfl)
      subst h4; rfl
    | unf hs' hu' h' => exact (mapStuckS_unf_false hstuck hu' h').elim
    | _ => clashs
  | mapSnd he hd hp ht ha hb hs hstuck ihd ihp iht iha ihb ihs => intro r' h' hk; cases h' with
    | mapSnd he' hd' hp' ht' ha' hb' hs' hstuck' =>
      injs he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iha ha' rfl)
      subst h2
      have h3 := ty_eq (ihb hb' rfl)
      subst h3
      have h4 := val_eq (ihs hs' rfl)
      subst h4; rfl
    | unf hs' hu' h' => exact (mapStuckS_unf_false hstuck hu' h').elim
    | _ => clashs
  | inhMk he hu0 hc ht hx iht ihx => intro r' h' hk; cases h' with
    | inhMk he' hu' hc' ht' hx' =>
      injs he he'
      have h1 := ty_eq (iht ht' rfl)
      subst h1
      have h2 := val_eq (ihx hx' rfl)
      subst h2; rfl
    | unf hs' hu' h' => subst he; simp [unfoldAt, appFn_appN, hc] at hu'
    | _ => clashs
  | inhDefault he ht hi iht ihi => intro r' h' hk; cases h' with
    | inhDefault he' ht' hi' =>
      injs he he'
      have h1 := ty_eq (iht ht' rfl)
      subst h1
      have h2 := val_eq (ihi hi' rfl)
      subst h2; rfl
    | _ => clashs
  | bundle2 he hd hta htb ha hb ihd ihta ihtb iha ihb => intro r' h' hk; cases h' with
    | bundle2 he' hd' hta' htb' ha' hb' =>
      injs he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (ihta hta' rfl)
      subst h2
      have h3 := ty_eq (ihtb htb' rfl)
      subst h3
      have h4 := val_eq (iha ha' rfl)
      subst h4
      have h5 := val_eq (ihb hb' rfl)
      subst h5; rfl
    | _ => clashs


theorem cds_fun {env : Environment} {ρ : Val} {e : Expr} {α α' : Type} {v : α} {v' : α'} (h : CDS env ρ e α v) (h' : CDS env ρ e α' v') :
    α = α' ∧ HEq v v' := val_inj (ds_fun h h' rfl)

theorem tds_fun {env : Environment} {ρ : Val} {e : Expr} {T T' : Type} (h : TDS env ρ e T) (h' : TDS env ρ e T') : T = T' := ty_eq (ds_fun h h' rfl)

theorem cds_eq {env : Environment} {ρ : Val} {e : Expr} {α : Type} {v v' : α} (h : CDS env ρ e α v) (h' : CDS env ρ e α v') : v = v' :=
  eq_of_heq (cds_fun h h').2



/-! ## the old rule is the case `u = 1` -/

theorem ds_inhMk_one {env : Environment} {ρ : Val} {e t x : Expr} {T : Type} {v : T} {cv : ConstructorVal} (he : e = appN ``Inhabited.mk [.succ .zero] [t, x])
    (hc : env.find? ``Inhabited.mk = some (.ctorInfo cv)) (ht : TDS env ρ t T) (hx : CDS env ρ x T v) : CDS env ρ e (Inhabited T) (⟨v⟩ : Inhabited T) :=
  DS.inhMk he lvlNat_one hc ht hx

theorem ds_default_of_mk {env : Environment} {ρ : Val} {t x : Expr} {T : Type} {v : T} {cv : ConstructorVal}
    (hc : env.find? ``Inhabited.mk = some (.ctorInfo cv)) (ht : TDS env ρ t T) (hx : CDS env ρ x T v) :
    CDS env ρ (appN ``Inhabited.default [.succ .zero] [t, appN ``Inhabited.mk [.succ .zero] [t, x]]) T v :=
  DS.inhDefault rfl ht (ds_inhMk_one rfl hc ht hx)

/-! ## the carrier and the obligation, in ONE environment -/

def CircCVS : ConstValueRel := fun env X α v =>
  ∃ d : DefinitionVal, env.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ CDS env [] d.value α v

theorem circCVS_functional : ConstValueFunctional CircCVS := by
  intro env c α β v w ⟨d, hd, _, hv⟩ ⟨d', hd', _, hv'⟩
  rw [hd] at hd'
  have := ConstantInfo.defnInfo.inj (Option.some.inj hd')
  subst this
  exact cds_fun hv hv'

/-- the obligation of the S1k statement over `DS`, in ONE environment (the same shape as `HftObCDW`) -/
def HftObCDS (env : Environment) : Prop := CDS env [] Tools.ShippingFGCircuitS1kStmt.hftRootValue (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft)
  Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte

theorem circCVS_hft_of_obCDS {env : Environment} {d : DefinitionVal} (hd : env.find? Tools.ShippingFGCircuitS1kStmt.hftRoot = some (.defnInfo d))
    (hl : d.levelParams = []) (hv : d.value = Tools.ShippingFGCircuitS1kStmt.hftRootValue) (h : HftObCDS env) :
    CircCVS env Tools.ShippingFGCircuitS1kStmt.hftRoot (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft) Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte :=
  ⟨d, hd, hl, by rw [hv]; exact h⟩

def CircCVSAt (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (X : Name) (α : Type) (v : α) : Prop := CircCVS (envAt cref w) X α v

theorem circCVS_at_of_getEnv {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {e : Environment} (h : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w e w') {X : Name} {α : Type} {v : α} :
    CircCVS e X α v ↔ CircCVS (envAt cref w) X α v := by
  rw [Tools.ShippingEntryReadsLinked.getEnv_value h]

theorem circCVS_hft_run (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) {d : DefinitionVal}
    (hd : (envAt cref w).find? Tools.ShippingFGCircuitS1kStmt.hftRoot = some (.defnInfo d)) (hl : d.levelParams = [])
    (hv : d.value = Tools.ShippingFGCircuitS1kStmt.hftRootValue) (h : HftObCDS (envAt cref w)) :
    CircCVSAt cref w Tools.ShippingFGCircuitS1kStmt.hftRoot (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft) Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte :=
  circCVS_hft_of_obCDS hd hl hv h

/-- the final consumer: the S1k statement with `hcd : HftObCDS (envAt cref w)` (the same `HftFinalStmtWith` as S1r/S1s, with the new family) -/
def HftFinalStmtS : Prop := Tools.ShippingFGCircuitS1rCD.Stmt.HftFinalStmtWith HftObCDS


/-! ## the table versions of the rules that read the environment (as in S1wTbl, for `DS`) -/

section Rules
variable {env : Environment} {lk : Look} (hlk : EnvLk env lk) {ρ : Val}
include hlk

theorem ds_unf_t {e e' : Expr} {r : Res} (hs : stopS r e = false) (hu : unfoldL lk e = some (some e')) (h : DS env ρ e' r) : DS env ρ e r :=
  DS.unf hs (unfoldL_sound hlk hu) h

theorem ds_beta_t {e e' : Expr} {r : Res} (hb : headRedexRL lk e = some (some e')) (h : DS env ρ e' r) : DS env ρ e r :=
  DS.beta (headRedexRL_sound hlk hb) h

theorem ds_projStep_t {e x x' : Expr} {S : Name} {i : Nat} {r : Res} (he : e = .proj S i x) (hx : whStepRL lk x = some (some x'))
    (h : DS env ρ (.proj S i x') r) : DS env ρ e r :=
  DS.projStep he (whStepRL_sound hlk x hx) h

theorem ds_projCtor_t {e x fld : Expr} {S ctor : Name} {ls : List Level} {cw : CtorRow} {i : Nat} {r : Res}
    (he : e = .proj S i x) (hh : appFn x = .const ctor ls) (hr : lk ctor = some (.ctor cw)) (hS : cw.induct = S)
    (hn : (appArgs x).length = cw.numParams + cw.numFields) (hf : (appArgs x)[cw.numParams + i]? = some fld) (h : DS env ρ fld r) : DS env ρ e r := by
  obtain ⟨cv, hc, h1, h2, h3⟩ := hlk ctor _ hr
  exact DS.projCtor he hh hc (by rw [h1, hS]) (by rw [h2, h3]; exact hn) (by rw [h2]; exact hf) h

theorem ds_recIota_t {e e' : Expr} {ls : List Level} {r : Res} (hf : appFn e = .const ``List.rec ls) (hrec : lk ``List.rec = some .recl)
    (hr : recStepL lk e = some (some e')) (h : DS env ρ e' r) : DS env ρ e r := by
  obtain ⟨ri, hi⟩ := hlk _ _ hrec
  exact DS.recIota hf hi (recStepL_sound hlk hr) h

theorem ds_projRec_t {e x x' : Expr} {S : Name} {i : Nat} {ls : List Level} {r : Res} (he : e = .proj S i x) (hf : appFn x = .const ``List.rec ls)
    (hrec : lk ``List.rec = some .recl) (hr : recStepL lk x = some (some x')) (h : DS env ρ (.proj S i x') r) : DS env ρ e r := by
  obtain ⟨ri, hi⟩ := hlk _ _ hrec
  exact DS.projRec he hf hi (recStepL_sound hlk hr) h

theorem ds_unitVal_t {e : Expr} {cw : CtorRow} (he : e = .const ``PUnit.unit [.succ .zero]) (hr : lk ``PUnit.unit = some (.ctor cw)) :
    CDS env ρ e Unit () := by
  obtain ⟨cv, hc, _⟩ := hlk _ _ hr
  exact DS.unitVal he hc

theorem ds_prodMk_t {e a b x y : Expr} {A B : Type} {xv : A} {yv : B} {cw : CtorRow}
    (he : e = appN ``Prod.mk [.zero, .zero] [a, b, x, y]) (hr : lk ``Prod.mk = some (.ctor cw))
    (ha : TDS env ρ a A) (hb : TDS env ρ b B) (hx : CDS env ρ x A xv) (hy : CDS env ρ y B yv) : CDS env ρ e (A × B) (xv, yv) := by
  obtain ⟨cv, hc, _⟩ := hlk _ _ hr
  exact DS.prodMk he hc ha hb hx hy

theorem ds_inhMk_t {e t x : Expr} {u : Level} {T : Type} {v : T} {cw : CtorRow} (he : e = appN ``Inhabited.mk [u] [t, x]) (hu : lvlNat u = some 1)
    (hr : lk ``Inhabited.mk = some (.ctor cw)) (ht : TDS env ρ t T) (hx : CDS env ρ x T v) : CDS env ρ e (Inhabited T) (⟨v⟩ : Inhabited T) := by
  obtain ⟨cv, hc, _⟩ := hlk _ _ hr
  exact DS.inhMk he hu hc ht hx

theorem ds_mapFst_t {e d tp ta a b s u : Expr} {D : DomainConfig} {A B : Type} {sv : Signal D (A × B)} {ls' : List Level} {cw : CtorRow}
    (he : e = appN ``Signal.map [.zero] [d, tp, ta, appN ``Prod.fst [.zero, .zero] [a, b], s])
    (hd : CDS env ρ d DomainConfig D) (hp : TDS env ρ tp (A × B)) (ht : TDS env ρ ta A) (ha : TDS env ρ a A) (hb : TDS env ρ b B)
    (hs : CDS env ρ s (Signal D (A × B)) sv) (hu : unfoldL lk e = some (some u)) (hm : appFn u = .const ``Signal.mk ls')
    (hr : lk ``Signal.mk = some (.ctor cw)) : CDS env ρ e (Signal D A) (Signal.map Prod.fst sv) := by
  obtain ⟨cv, hc, _⟩ := hlk _ _ hr
  exact DS.mapFst he hd hp ht ha hb hs ⟨u, ls', cv, unfoldL_sound hlk hu, hm, hc⟩

theorem ds_mapSnd_t {e d tp tb a b s u : Expr} {D : DomainConfig} {A B : Type} {sv : Signal D (A × B)} {ls' : List Level} {cw : CtorRow}
    (he : e = appN ``Signal.map [.zero] [d, tp, tb, appN ``Prod.snd [.zero, .zero] [a, b], s])
    (hd : CDS env ρ d DomainConfig D) (hp : TDS env ρ tp (A × B)) (ht : TDS env ρ tb B) (ha : TDS env ρ a A) (hb : TDS env ρ b B)
    (hs : CDS env ρ s (Signal D (A × B)) sv) (hu : unfoldL lk e = some (some u)) (hm : appFn u = .const ``Signal.mk ls')
    (hr : lk ``Signal.mk = some (.ctor cw)) : CDS env ρ e (Signal D B) (Signal.map Prod.snd sv) := by
  obtain ⟨cv, hc, _⟩ := hlk _ _ hr
  exact DS.mapSnd he hd hp ht ha hb hs ⟨u, ls', cv, unfoldL_sound hlk hu, hm, hc⟩

end Rules

end Tools.ShippingFGCircuitS2bShare

#print axioms Tools.ShippingFGCircuitS2bShare.ds_fun
