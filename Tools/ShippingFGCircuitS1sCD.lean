import Tools.ShippingFGCircuitS1rCD
set_option autoImplicit false
-- FG circuit pilot S1s: the narrow `bundle2` pairing rule and the `Inhabited.mk` / `Inhabited.default` rules, the family `DW`, docs/FG-CIRCUIT-PILOT.md §23.
-- No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.

/-! # S1s

`DW` = the 23 value/type rules of `DZ` (copied), the wiring rules `mapFst`/`mapSnd`/`prodMk`/`unitVal`/`prodTy`/`punitTy`, and three NEW rules:
* `inhMk`      `Inhabited.mk.{1} T x` : the instance VALUE `⟨v⟩` from the derivation of the field `x ↦ v` (a constructor of `env`).
* `inhDefault` `Inhabited.default.{1} T inst` : `iv.default` of the SAME instance `iv` that `inst` denotes. No type-class search; the instance argument is never erased.
* `bundle2`    `bundle2.{0} d A B a b` : the pairing of two signals of the same domain; value Lean's `bundle2 av bv`. `bundle2` has `@[implemented_by bundle2Impl]`: what is
               proved (`bundle2_val_at`, by `rfl`) is agreement with the LOGICAL definition `(·, ·) <$> a <*> b`; agreement with the unsafe implementation is NOT proved.
`bundle2` and `Inhabited.default` are stop heads of `unf` (`newStop`, inside `stopW`), so `unf` and the new rules are exclusive (`dw_fun`). Consequence: a `DZ` derivation that unfolds
a `bundle2`/`Inhabited.default` application with `unf` has no `DW` copy (the old constructors are otherwise the same: Check17 compares them one by one). -/
namespace Tools.ShippingFGCircuitS1sCD
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5ConstValueE Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingEntrySoundness (RunsTo)

/-! ## 1. the Lean equations (logical definitions, every signal, every time) -/

theorem bundle2_val_at {D : DomainConfig} {A B : Type} (a : Signal D A) (b : Signal D B) (t : Nat) :
    (Sparkle.Core.Signal.bundle2 a b).val t = (a.val t, b.val t) := rfl
theorem bundle2_eq_mk {D : DomainConfig} {A B : Type} (a : Signal D A) (b : Signal D B) :
    Sparkle.Core.Signal.bundle2 a b = ⟨fun t => (a.val t, b.val t)⟩ := rfl
/-- the unfolded form that the traversal meets: `seq` keeps its `Unit` thunk -/
theorem bundle2_eq_seq {D : DomainConfig} {A B : Type} (a : Signal D A) (b : Signal D B) :
    Sparkle.Core.Signal.bundle2 a b = Signal.seq (Signal.map (fun x y => (x, y)) a) (fun _ => b) := rfl
theorem bundle2_eq_ap {D : DomainConfig} {A B : Type} (a : Signal D A) (b : Signal D B) :
    Sparkle.Core.Signal.bundle2 a b = Signal.ap (Signal.map (fun x y => (x, y)) a) b := rfl
theorem seq_val_at {D : DomainConfig} {A B : Type} (sf : Signal D (A → B)) (s : Unit → Signal D A) (t : Nat) :
    (Signal.seq sf s).val t = sf.val t ((s ()).val t) := rfl
theorem ap_val_at {D : DomainConfig} {A B : Type} (sf : Signal D (A → B)) (s : Signal D A) (t : Nat) :
    (Signal.ap sf s).val t = sf.val t (s.val t) := rfl
/-- the projections of a `bundle2` give back the components, at every time -/
theorem bundle2_fst_at {D : DomainConfig} {A B : Type} (a : Signal D A) (b : Signal D B) (t : Nat) :
    (Signal.map Prod.fst (Sparkle.Core.Signal.bundle2 a b)).val t = a.val t := rfl
theorem bundle2_snd_at {D : DomainConfig} {A B : Type} (a : Signal D A) (b : Signal D B) (t : Nat) :
    (Signal.map Prod.snd (Sparkle.Core.Signal.bundle2 a b)).val t = b.val t := rfl
/-- a swap is a different signal pointwise (negative control at the Lean level): `bundle2 a b` at `t` is not `(b.val t, a.val t)` in general -/
theorem bundle2_swap_ne : ∃ (a b : Signal defaultDomain Nat), ∃ t, (Sparkle.Core.Signal.bundle2 a b).val t ≠ (Sparkle.Core.Signal.bundle2 b a).val t :=
  ⟨Signal.pure 0, Signal.pure 1, 0, by decide⟩

theorem inhabited_default_mk {T : Type} (v : T) : (⟨v⟩ : Inhabited T).default = v := rfl
theorem inhabited_prod_mk {A B : Type} (ia : Inhabited A) (ib : Inhabited B) :
    (⟨(ia.default, ib.default)⟩ : Inhabited (A × B)).default = (ia.default, ib.default) := rfl
theorem inhabited_inst_prod {A B : Type} [ia : Inhabited A] [ib : Inhabited B] : (default : A × B) = (ia.default, ib.default) := rfl
/-- two instances of the SAME type with different defaults: the instance argument matters -/
theorem inhabited_instances_differ : ∃ i j : Inhabited Nat, i.default ≠ j.default := ⟨⟨0⟩, ⟨5⟩, by decide⟩
/-- `Signal.loop` reads the default of ITS instance -/
theorem loop_val_eq {D : DomainConfig} {T : Type} (iv : Inhabited T) (g : Signal D T → Signal D T) (t : Nat) :
    (@Signal.loop D T iv g).val t = (g ⟨fun i => if i < t then Signal.loopGo g i else iv.default⟩).val t := Signal.loopGo_eq g t

/-! ## 2. the stop heads -/

def newStopC (c : Name) : Bool := [``Sparkle.Core.Signal.bundle2, ``Inhabited.default].contains c
def newStop (e : Expr) : Bool :=
  match appFn e with
  | .const c _ => newStopC c
  | _ => false
/-- the stop condition of `unf` in `DW`: the `DZ` one, or a new stop head -/
def stopW (r : Res) (e : Expr) : Bool := stopR r e || newStop e

theorem newStopC_bundle2 : newStopC ``Sparkle.Core.Signal.bundle2 = true := by decide
theorem newStopC_default : newStopC ``Inhabited.default = true := by decide

/-! ## 3. the relation -/


section
local macro "CDw " env:term:max ρ:term:max e:term:max α:term:max v:term:max : term => `($(Lean.mkIdent `Tools.ShippingFGCircuitS1sCD.DW) $env $ρ $e (Res.val $α $v))
local macro "TDw " env:term:max ρ:term:max e:term:max T:term:max : term => `($(Lean.mkIdent `Tools.ShippingFGCircuitS1sCD.DW) $env $ρ $e (Res.ty $T))
inductive DW (env : Environment) : Val → Expr → Res → Prop
  | nat {ρ : Val} {e : Expr} (he : e = .const ``Nat []) : TDw env ρ e Nat
  | bool {ρ : Val} {e : Expr} (he : e = .const ``Bool []) : TDw env ρ e Bool
  | domainConfig {ρ : Val} {e : Expr} (he : e = .const ``Sparkle.Core.Domain.DomainConfig []) : TDw env ρ e DomainConfig
  | bitvec {ρ : Val} {e w : Expr} {n : Nat} (he : e = appN ``BitVec [] [w]) (hw : CDw env ρ w Nat n) : TDw env ρ e (BitVec n)
  | signal {ρ : Val} {e d t : Expr} {D : DomainConfig} {T : Type} (he : e = appN ``Signal [.zero] [d, t])
      (hd : CDw env ρ d DomainConfig D) (ht : TDw env ρ t T) : TDw env ρ e (Signal D T)

  | bvar {ρ : Val} {i : Nat} {τ : Expr} {T : Type} {a : T} (h : ρ[i]? = some ⟨τ, ⟨T, a⟩⟩) : CDw env ρ (.bvar i) T a
  | natLit {ρ : Val} {e : Expr} {n : Nat}
      (he : e = appN ``OfNat.ofNat [.zero] [.const ``Nat [], .lit (.natVal n), appN ``instOfNatNat [] [.lit (.natVal n)]]) :
      CDw env ρ e Nat n
  | domDefault {ρ : Val} {e : Expr} (he : e = .const ``Sparkle.Core.Domain.defaultDomain []) :
      CDw env ρ e DomainConfig defaultDomain
  | bvOfNat {ρ : Val} {e w k : Expr} {W K : Nat} (he : e = appN ``BitVec.ofNat [] [w, k])
      (hw : CDw env ρ w Nat W) (hk : CDw env ρ k Nat K) : CDw env ρ e (BitVec W) (BitVec.ofNat W K)
  | bvInhabited {ρ : Val} {e w : Expr} {W : Nat} (he : e = appN ``BitVec.instInhabited [] [w]) (hw : CDw env ρ w Nat W) :
      CDw env ρ e (Inhabited (BitVec W)) (inferInstance : Inhabited (BitVec W))
  | boolInhabited {ρ : Val} {e : Expr} (he : e = .const ``instInhabitedBool []) :
      CDw env ρ e (Inhabited Bool) (inferInstance : Inhabited Bool)
  | sigPure {ρ : Val} {e d t x : Expr} {D : DomainConfig} {T : Type} {a : T}
      (he : e = appN ``Signal.pure [.zero] [d, t, x]) (hd : CDw env ρ d DomainConfig D) (ht : TDw env ρ t T) (hx : CDw env ρ x T a) :
      CDw env ρ e (Signal D T) (Signal.pure a)
  | sigRegister {ρ : Val} {e d t i s : Expr} {D : DomainConfig} {T : Type} {a : T} {sv : Signal D T}
      (he : e = appN ``Signal.register [.zero] [d, t, i, s]) (hd : CDw env ρ d DomainConfig D) (ht : TDw env ρ t T)
      (hi : CDw env ρ i T a) (hs : CDw env ρ s (Signal D T) sv) : CDw env ρ e (Signal D T) (Signal.register a sv)
  | sigMux {ρ : Val} {e d t c a b : Expr} {D : DomainConfig} {T : Type} {cv : Signal D Bool} {av bv : Signal D T}
      (he : e = appN ``Signal.mux [.zero] [d, t, c, a, b]) (hd : CDw env ρ d DomainConfig D) (ht : TDw env ρ t T)
      (hc : CDw env ρ c (Signal D Bool) cv) (ha : CDw env ρ a (Signal D T) av) (hb : CDw env ρ b (Signal D T) bv) :
      CDw env ρ e (Signal D T) (Signal.mux cv av bv)
  | sigAddBV {ρ : Val} {e d w a b : Expr} {D : DomainConfig} {W : Nat} {av bv : Signal D (BitVec W)}
      (he : e = appN ``HAdd.hAdd [.zero, .zero, .zero]
        [appN ``Signal [.zero] [d, appN ``BitVec [] [w]], appN ``Signal [.zero] [d, appN ``BitVec [] [w]],
         appN ``Signal [.zero] [d, appN ``BitVec [] [w]], appN ``Sparkle.Core.Signal.instHAddSignalBitVec [] [d, w], a, b])
      (hd : CDw env ρ d DomainConfig D) (hw : CDw env ρ w Nat W)
      (ha : CDw env ρ a (Signal D (BitVec W)) av) (hb : CDw env ρ b (Signal D (BitVec W)) bv) :
      CDw env ρ e (Signal D (BitVec W)) (@HAdd.hAdd _ _ _ (@Sparkle.Core.Signal.instHAddSignalBitVec D W) av bv)
  | sigLoop {ρ : Val} {e d t inst f : Expr} {D : DomainConfig} {T : Type} {iv : Inhabited T} {g : Signal D T → Signal D T}
      (he : e = appN ``Signal.loop [] [d, t, inst, f]) (hd : CDw env ρ d DomainConfig D) (ht : TDw env ρ t T)
      (hi : CDw env ρ inst (Inhabited T) iv) (hf : CDw env ρ f (Signal D T → Signal D T) g) :
      CDw env ρ e (Signal D T) (@Signal.loop D T iv g)
  | lam {ρ : Val} {e A body : Expr} {n : Name} {bi : BinderInfo} {TA : Type} {TB : TA → Type} {f : (a : TA) → TB a}
      (he : e = .lam n A body bi) (hA : TDw env ρ A TA) (hb : ∀ a : TA, CDw env (⟨A, ⟨TA, a⟩⟩ :: ρ) body (TB a) (f a)) :
      CDw env ρ e ((a : TA) → TB a) f
  | letE {ρ : Val} {e A v body : Expr} {n : Name} {nd : Bool} {TA T : Type} {a : TA} {r : T}
      (he : e = .letE n A v body nd) (hA : TDw env ρ A TA) (hc : coreHead A = true) (hv : CDw env ρ v TA a)
      (hb : CDw env (⟨A, ⟨TA, a⟩⟩ :: ρ) body T r) : CDw env ρ e T r
  | sigBeqBV {ρ : Val} {e d w a b : Expr} {D : DomainConfig} {W : Nat} {av bv : Signal D (BitVec W)}
      (he : e = appN ``Sparkle.Core.Signal.Signal.beq []
        [appN ``BitVec [] [w], d, appN ``instBEqOfDecidableEq [.zero] [appN ``BitVec [] [w], appN ``instDecidableEqBitVec [] [w]], a, b])
      (hd : CDw env ρ d DomainConfig D) (hw : CDw env ρ w Nat W)
      (ha : CDw env ρ a (Signal D (BitVec W)) av) (hb : CDw env ρ b (Signal D (BitVec W)) bv) :
      CDw env ρ e (Signal D Bool) (@Signal.beq (BitVec W) D (@instBEqOfDecidableEq (BitVec W) (@instDecidableEqBitVec W)) av bv)
  | sigAndBool {ρ : Val} {e d a b : Expr} {D : DomainConfig} {av bv : Signal D Bool}
      (he : e = appN ``HAnd.hAnd [.zero, .zero, .zero]
        [appN ``Signal [.zero] [d, .const ``Bool []], appN ``Signal [.zero] [d, .const ``Bool []],
         appN ``Signal [.zero] [d, .const ``Bool []], appN ``Sparkle.Core.Signal.instHAndSignalBool [] [d], a, b])
      (hd : CDw env ρ d DomainConfig D) (ha : CDw env ρ a (Signal D Bool) av) (hb : CDw env ρ b (Signal D Bool) bv) :
      CDw env ρ e (Signal D Bool) (@HAnd.hAnd _ _ _ (@Sparkle.Core.Signal.instHAndSignalBool D) av bv)
  | sigOrBool {ρ : Val} {e d a b : Expr} {D : DomainConfig} {av bv : Signal D Bool}
      (he : e = appN ``HOr.hOr [.zero, .zero, .zero]
        [appN ``Signal [.zero] [d, .const ``Bool []], appN ``Signal [.zero] [d, .const ``Bool []],
         appN ``Signal [.zero] [d, .const ``Bool []], appN ``Sparkle.Core.Signal.instHOrSignalBool [] [d], a, b])
      (hd : CDw env ρ d DomainConfig D) (ha : CDw env ρ a (Signal D Bool) av) (hb : CDw env ρ b (Signal D Bool) bv) :
      CDw env ρ e (Signal D Bool) (@HOr.hOr _ _ _ (@Sparkle.Core.Signal.instHOrSignalBool D) av bv)
  | sigNotBool {ρ : Val} {e d a : Expr} {D : DomainConfig} {av : Signal D Bool}
      (he : e = appN ``Complement.complement [.zero]
        [appN ``Signal [.zero] [d, .const ``Bool []], appN ``Sparkle.Core.Signal.instComplementSignalBool [] [d], a])
      (hd : CDw env ρ d DomainConfig D) (ha : CDw env ρ a (Signal D Bool) av) :
      CDw env ρ e (Signal D Bool) (@Complement.complement _ (@Sparkle.Core.Signal.instComplementSignalBool D) av)
  | bvAbbrev {ρ : Val} {e : Expr} {c : Name} {n : Nat} {v : BitVec n} (he : e = .const c []) (h : bvAbbrevRow c = some ⟨n, v⟩) :
      CDw env ρ e (BitVec n) v
  /-- delta + beta of a user definition, for a value OR a type; `stopW r e` is false (not a primitive head / a core type head) -/
  | unf {ρ : Val} {e e' : Expr} {r : Res}
      (hs : stopW r e = false) (hu : unfoldAt env e = some e') (h : DW env ρ e' r) : DW env ρ e r
  | beta {ρ : Val} {e e' : Expr} {r : Res}
      (hb : headRedexR env e = some e') (h : DW env ρ e' r) : DW env ρ e r
  | zeta {ρ : Val} {e A v body : Expr} {n : Name} {nd : Bool} {α : Type} {r : α}
      (he : e = .letE n A v body nd) (hA : coreHead A = false) (h : CDw env ρ (instE body v 0) α r) : CDw env ρ e α r
  | projStep {ρ : Val} {e x x' : Expr} {S : Name} {i : Nat} {r : Res}
      (he : e = .proj S i x) (hx : whStepR env x = some x') (h : DW env ρ (.proj S i x') r) : DW env ρ e r
  | projCtor {ρ : Val} {e x fld : Expr} {S ctor : Name} {ls : List Level} {cv : ConstructorVal} {i : Nat} {r : Res}
      (he : e = .proj S i x) (hh : appFn x = .const ctor ls) (hc : env.find? ctor = some (.ctorInfo cv)) (hS : cv.induct = S)
      (hn : (appArgs x).length = cv.numParams + cv.numFields) (hf : (appArgs x)[cv.numParams + i]? = some fld)
      (h : DW env ρ fld r) : DW env ρ e r
  | recIota {ρ : Val} {e e' : Expr} {ls : List Level} {ri : RecursorVal} {r : Res}
      (hf : appFn e = .const ``List.rec ls) (hi : env.find? ``List.rec = some (.recInfo ri)) (hr : recStep env e = some e') (h : DW env ρ e' r) : DW env ρ e r
  /-- NEW (S1r). a projection whose structure argument is itself a `List.rec` redex (`recStep`): step inside (`whStepR` does this only under another projection/application) -/
  | projRec {ρ : Val} {e x x' : Expr} {S : Name} {i : Nat} {ls : List Level} {ri : RecursorVal} {r : Res}
      (he : e = .proj S i x) (hf : appFn x = .const ``List.rec ls) (hi : env.find? ``List.rec = some (.recInfo ri)) (hr : recStep env x = some x')
      (h : DW env ρ (.proj S i x') r) : DW env ρ e r
  /-- NEW (S1r). `Prod a b` -/
  | prodTy {ρ : Val} {e a b : Expr} {A B : Type} (he : e = appN ``Prod [.zero, .zero] [a, b]) (ha : TDw env ρ a A) (hb : TDw env ρ b B) : TDw env ρ e (A × B)
  /-- NEW (S1r). `PUnit.{1}` (the type `Unit` unfolds to it by `unf`) -/
  | punitTy {ρ : Val} {e : Expr} (he : e = .const ``PUnit [.succ .zero]) : TDw env ρ e Unit
  /-- NEW (S1r). `PUnit.unit.{1}`; the constructor is a `ctorInfo` of `env` (so `unf` cannot also apply) -/
  | unitVal {ρ : Val} {e : Expr} {cv : ConstructorVal} (he : e = .const ``PUnit.unit [.succ .zero]) (hc : env.find? ``PUnit.unit = some (.ctorInfo cv)) :
      CDw env ρ e Unit ()
  /-- NEW (S1r). `Prod.mk a b x y`; the constructor is a `ctorInfo` of `env` -/
  | prodMk {ρ : Val} {e a b x y : Expr} {A B : Type} {xv : A} {yv : B} {cv : ConstructorVal}
      (he : e = appN ``Prod.mk [.zero, .zero] [a, b, x, y]) (hc : env.find? ``Prod.mk = some (.ctorInfo cv))
      (ha : TDw env ρ a A) (hb : TDw env ρ b B) (hx : CDw env ρ x A xv) (hy : CDw env ρ y B yv) : CDw env ρ e (A × B) (xv, yv)
  /-- NEW (S1r). `Signal.map Prod.fst s` : the head constant, the function `Prod.fst`, the pair signal. The value is Lean's `Signal.map Prod.fst sv`; `signal_map_fst_at` is its equation at every time. -/
  | mapFst {ρ : Val} {e d tp ta a b s : Expr} {D : DomainConfig} {A B : Type} {sv : Signal D (A × B)}
      (he : e = appN ``Signal.map [.zero] [d, tp, ta, appN ``Prod.fst [.zero, .zero] [a, b], s])
      (hd : CDw env ρ d DomainConfig D) (hp : TDw env ρ tp (A × B)) (ht : TDw env ρ ta A) (ha : TDw env ρ a A) (hb : TDw env ρ b B)
      (hs : CDw env ρ s (Signal D (A × B)) sv) (hstuck : MapStuck env e) : CDw env ρ e (Signal D A) (Signal.map Prod.fst sv)
  /-- NEW (S1r). `Signal.map Prod.snd s` -/
  | mapSnd {ρ : Val} {e d tp tb a b s : Expr} {D : DomainConfig} {A B : Type} {sv : Signal D (A × B)}
      (he : e = appN ``Signal.map [.zero] [d, tp, tb, appN ``Prod.snd [.zero, .zero] [a, b], s])
      (hd : CDw env ρ d DomainConfig D) (hp : TDw env ρ tp (A × B)) (ht : TDw env ρ tb B) (ha : TDw env ρ a A) (hb : TDw env ρ b B)
      (hs : CDw env ρ s (Signal D (A × B)) sv) (hstuck : MapStuck env e) : CDw env ρ e (Signal D B) (Signal.map Prod.snd sv)
  /-- NEW (S1s). `Inhabited.mk.{1} T x`: the instance VALUE `⟨v⟩` built from the derivation of the field `x ↦ v`; a constructor of `env` (so `unf` cannot also apply) -/
  | inhMk {ρ : Val} {e t x : Expr} {T : Type} {v : T} {cv : ConstructorVal} (he : e = appN ``Inhabited.mk [.succ .zero] [t, x])
      (hc : env.find? ``Inhabited.mk = some (.ctorInfo cv)) (ht : TDw env ρ t T) (hx : CDw env ρ x T v) : CDw env ρ e (Inhabited T) (⟨v⟩ : Inhabited T)
  /-- NEW (S1s). `Inhabited.default.{1} T inst`: the default of the SAME instance, `iv.default`. `Inhabited.default` is a stop head of `unf` (`newStop`) -/
  | inhDefault {ρ : Val} {e t inst : Expr} {T : Type} {iv : Inhabited T} (he : e = appN ``Inhabited.default [.succ .zero] [t, inst])
      (ht : TDw env ρ t T) (hi : CDw env ρ inst (Inhabited T) iv) : CDw env ρ e T iv.default
  /-- NEW (S1s). `bundle2.{0} d A B a b` (same `d` for both): the pairing of two signals of the same domain. The value is Lean's `bundle2 av bv` (its LOGICAL definition; `bundle2` has `implemented_by`, which is not proved to agree). `bundle2` is a stop head of `unf` -/
  | bundle2 {ρ : Val} {e d ta tb a b : Expr} {D : DomainConfig} {A B : Type} {av : Signal D A} {bv : Signal D B}
      (he : e = appN ``Sparkle.Core.Signal.bundle2 [.zero] [d, ta, tb, a, b]) (hd : CDw env ρ d DomainConfig D) (hta : TDw env ρ ta A) (htb : TDw env ρ tb B)
      (ha : CDw env ρ a (Signal D A) av) (hb : CDw env ρ b (Signal D B) bv) : CDw env ρ e (Signal D (A × B)) (Sparkle.Core.Signal.bundle2 av bv)
end

abbrev TDW (env : Environment) (ρ : Val) (e : Expr) (T : Type) : Prop := DW env ρ e (.ty T)
abbrev CDW (env : Environment) (ρ : Val) (e : Expr) (α : Type) (v : α) : Prop := DW env ρ e (.val α v)

/-! ## 4. exclusivity and functionality -/


/-- there is no derivation for an expression headed by the constructor `Signal.mk` (of `env`): no rule has that head -/
theorem dw_signalMk_false {env : Environment} {ρ : Val} {e : Expr} {r : Res} (h : DW env ρ e r) {ls : List Level} {cv : ConstructorVal}
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
theorem mapStuckW_unf_false {env : Environment} {ρ : Val} {e e' : Expr} {r : Res} (hs : MapStuck env e) (hu : unfoldAt env e = some e') (h : DW env ρ e' r) : False := by
  obtain ⟨e1, ls, cv, hu1, hf, hc⟩ := hs
  rw [hu1] at hu
  have := Option.some.inj hu
  subst this
  exact dw_signalMk_false h hf hc

/-! ## 6. functionality -/

macro "clashw" : tactic =>
  `(tactic| (exfalso
             try subst_vars
             try simp_all [Res.kind, stopW, stopR, newStop, newStopC_bundle2, newStopC_default, tyHeadStop, headStop, appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, appFn, stopC_ofNat, stopC_defaultDomain, stopC_bvOfNat, stopC_bvInh,
               stopC_boolInh, stopC_pure, stopC_register, stopC_mux, stopC_hadd, stopC_loop, stopC_beq, stopC_hand, stopC_hor, stopC_compl, bvAbbrevRow_defaultDomain,
               bvAbbrevRow_instInhabitedBool, stopC_of_row, unfoldAt_bvar, unfoldAt_lam, unfoldAt_letE, unfoldAt_proj, unfoldAt_rec, headRedexR_rec, stopC_rec, bvAbbrevRow_rec,
               tyStopC_nat, tyStopC_bool, tyStopC_dc, tyStopC_bitvec, tyStopC_signal, tyStopC_prod, tyStopC_punit]
             try simp_all [Res.kind, stopW, stopR, newStop, newStopC_bundle2, newStopC_default, tyHeadStop, headStop, headRedexR, appArgs, appFn, appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, unfoldAt_none_of_betaR, unfoldAt_rec, headRedexR_rec,
               tyStopC_nat, tyStopC_bool, tyStopC_dc, tyStopC_bitvec, tyStopC_signal, tyStopC_prod, tyStopC_punit]))

macro "injw" he:ident he':ident : tactic =>
  `(tactic| (have h := Eq.trans (Eq.symm $he) $he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.proj.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **functionality** of `DW`: two derivations of the same expression in the same valuation, of the same kind, have the same result. -/
theorem dw_fun {env : Environment} {ρ : Val} {e : Expr} {r : Res} (h : DW env ρ e r) : ∀ {r' : Res}, DW env ρ e r' → r.kind = r'.kind → r = r' := by
  induction h with
  | nat he => intro r' h' hk; cases h' with
    | nat he' => rfl
    | _ => clashw
  | bool he => intro r' h' hk; cases h' with
    | bool he' => rfl
    | _ => clashw
  | domainConfig he => intro r' h' hk; cases h' with
    | domainConfig he' => rfl
    | _ => clashw
  | bitvec he hw ihw => intro r' h' hk; cases h' with
    | bitvec he' hw' =>
      injw he he'
      have := val_eq (ihw hw' rfl)
      subst this; rfl
    | _ => clashw
  | signal he hd ht ihd iht => intro r' h' hk; cases h' with
    | signal he' hd' ht' =>
      injw he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2; rfl
    | _ => clashw
  | bvar hb => intro r' h' hk; cases h' with
    | bvar hb' =>
      have := Option.some.inj (hb.symm.trans hb')
      cases this
      rfl
    | _ => clashw
  | natLit he => intro r' h' hk; cases h' with
    | natLit he' =>
      injw he he'
      rfl
    | _ => clashw
  | domDefault he => intro r' h' hk; cases h' with
    | domDefault he' => rfl
    | bvAbbrev he' hr' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_defaultDomain] at hr'; cases hr'
    | _ => clashw
  | bvOfNat he hw hk ihw ihk => intro r' h' hk; cases h' with
    | bvOfNat he' hw' hk' =>
      injw he he'
      have h1 := val_eq (ihw hw' rfl)
      subst h1
      have h2 := val_eq (ihk hk' rfl)
      subst h2; rfl
    | _ => clashw
  | bvInhabited he hw ihw => intro r' h' hk; cases h' with
    | bvInhabited he' hw' =>
      injw he he'
      have h1 := val_eq (ihw hw' rfl)
      subst h1; rfl
    | _ => clashw
  | boolInhabited he => intro r' h' hk; cases h' with
    | boolInhabited he' => rfl
    | bvAbbrev he' hr' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_instInhabitedBool] at hr'; cases hr'
    | _ => clashw
  | sigPure he hd ht hx ihd iht ihx => intro r' h' hk; cases h' with
    | sigPure he' hd' ht' hx' =>
      injw he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihx hx' rfl)
      subst h3; rfl
    | _ => clashw
  | sigRegister he hd ht hi hs ihd iht ihi ihs => intro r' h' hk; cases h' with
    | sigRegister he' hd' ht' hi' hs' =>
      injw he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihi hi' rfl)
      subst h3
      have h4 := val_eq (ihs hs' rfl)
      subst h4; rfl
    | _ => clashw
  | sigMux he hd ht hc ha hb ihd iht ihc iha ihb => intro r' h' hk; cases h' with
    | sigMux he' hd' ht' hc' ha' hb' =>
      injw he he'
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
    | _ => clashw
  | sigAddBV he hd hw ha hb ihd ihw iha ihb => intro r' h' hk; cases h' with
    | sigAddBV he' hd' hw' ha' hb' =>
      injw he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := val_eq (ihw hw' rfl)
      subst h2
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashw
  | sigLoop he hd ht hi hf ihd iht ihi ihf => intro r' h' hk; cases h' with
    | sigLoop he' hd' ht' hi' hf' =>
      injw he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihi hi' rfl)
      subst h3
      have h4 := val_eq (ihf hf' rfl)
      subst h4; rfl
    | _ => clashw
  | lam he hA hb ihA ihb => intro r' h' hk; cases h' with
    | lam he' hA' hb' =>
      injw he he'
      have h1 := ty_eq (ihA hA' rfl)
      subst h1
      have h2 : ∀ a, _ = _ := fun a => (val_inj (ihb a (hb' a) rfl)).1
      have h2' := funext h2
      subst h2'
      have h3 : _ = _ := funext fun a => eq_of_heq (val_inj (ihb a (hb' a) rfl)).2
      subst h3; rfl
    | _ => clashw
  | letE he hA hc hv hb ihA ihv ihb => intro r' h' hk; cases h' with
    | letE he' hA' hc' hv' hb' =>
      injw he he'
      have h1 := ty_eq (ihA hA' rfl)
      subst h1
      have h2 := val_eq (ihv hv' rfl)
      subst h2
      exact ihb hb' rfl
    | zeta he' hA' h2 =>
      injw he he'
      simp_all
    | _ => clashw
  | sigBeqBV he hd hw ha hb ihd ihw iha ihb => intro r' h' hk; cases h' with
    | sigBeqBV he' hd' hw' ha' hb' =>
      injw he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := val_eq (ihw hw' rfl)
      subst h2
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashw
  | sigAndBool he hd ha hb ihd iha ihb => intro r' h' hk; cases h' with
    | sigAndBool he' hd' ha' hb' =>
      injw he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashw
  | sigOrBool he hd ha hb ihd iha ihb => intro r' h' hk; cases h' with
    | sigOrBool he' hd' ha' hb' =>
      injw he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashw
  | sigNotBool he hd ha ihd iha => intro r' h' hk; cases h' with
    | sigNotBool he' hd' ha' =>
      injw he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h3 := val_eq (iha ha' rfl)
      subst h3; rfl
    | _ => clashw
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
    | _ => clashw
  | unf hs hu h ih => intro r' h' hk; cases h' with
    | unf hs' hu' h' =>
      have e1 := Option.some.inj (hu.symm.trans hu')
      subst e1
      exact ih h' hk
    | mapFst he' hd' hp' ht' ha' hb' hs' hstuck' => exact (mapStuckW_unf_false hstuck' hu h).elim
    | mapSnd he' hd' hp' ht' ha' hb' hs' hstuck' => exact (mapStuckW_unf_false hstuck' hu h).elim
    | prodMk he' hc' ha' hb' hx' hy' => subst he'; simp [unfoldAt, appFn_appN, hc'] at hu
    | unitVal he' hc' => subst he'; simp [unfoldAt, appFn, hc'] at hu
    | inhMk he' hc' ht' hx' => subst he'; simp [unfoldAt, appFn_appN, hc'] at hu
    | _ => clashw
  | beta hb h ih => intro r' h' hk; cases h' with
    | beta hb' h' =>
      have e1 := Option.some.inj (hb.symm.trans hb')
      subst e1
      exact ih h' hk
    | _ => clashw
  | zeta he hA h ih => intro r' h' hk; cases h' with
    | zeta he' hA' h' =>
      injw he he'
      exact ih h' rfl
    | letE he' hA' hc' hv' hb' =>
      injw he he'
      simp_all
    | _ => clashw
  | projStep he hx h ih => intro r' h' hk; cases h' with
    | projStep he' hx' h' =>
      injw he he'
      have e1 := Option.some.inj (hx.symm.trans hx')
      subst e1
      exact ih h' hk
    | projCtor he' hh' hc' hS' hn' hf' h' =>
      injw he he'
      have := whStepR_ctor hc' _ hh'
      rw [hx] at this; cases this
    | projRec he' hf' hi' hr' h' =>
      injw he he'
      have := whStepR_listRec hi' _ hf'
      rw [hx] at this; cases this
    | _ => clashw
  | projCtor he hh hc hS hn hf h ih => intro r' h' hk; cases h' with
    | projCtor he' hh' hc' hS' hn' hf' h' =>
      injw he he'
      have h1 := Expr.const.inj (hh.symm.trans hh')
      obtain ⟨rfl, rfl⟩ := h1
      have h2 := ConstantInfo.ctorInfo.inj (Option.some.inj (hc.symm.trans hc'))
      subst h2
      have h3 := Option.some.inj (hf.symm.trans hf')
      subst h3
      exact ih h' hk
    | projStep he' hx' h' =>
      injw he he'
      have := whStepR_ctor hc _ hh
      rw [hx'] at this; cases this
    | projRec he' hf' hi' hr' h' =>
      injw he he'
      have h1 := Expr.const.inj (hh.symm.trans hf')
      obtain ⟨rfl, rfl⟩ := h1
      rw [hc] at hi'; cases hi'
    | _ => clashw
  | recIota hf hi hr h ih => intro r' h' hk; cases h' with
    | recIota hf' hi' hr' h' =>
      have e1 := Option.some.inj (hr.symm.trans hr')
      subst e1
      exact ih h' hk
    | _ => clashw
  | projRec he hf hi hr h ih => intro r' h' hk; cases h' with
    | projRec he' hf' hi' hr' h' =>
      injw he he'
      have e1 := Option.some.inj (hr.symm.trans hr')
      subst e1
      exact ih h' hk
    | projStep he' hx' h' =>
      injw he he'
      have := whStepR_listRec hi _ hf
      rw [hx'] at this; cases this
    | projCtor he' hh' hc' hS' hn' hf' h' =>
      injw he he'
      have h1 := Expr.const.inj (hh'.symm.trans hf)
      obtain ⟨rfl, rfl⟩ := h1
      rw [hc'] at hi; cases hi
    | _ => clashw
  | prodTy he ha hb iha ihb => intro r' h' hk; cases h' with
    | prodTy he' ha' hb' =>
      injw he he'
      have h1 := ty_eq (iha ha' rfl)
      subst h1
      have h2 := ty_eq (ihb hb' rfl)
      subst h2; rfl
    | _ => clashw
  | punitTy he => intro r' h' hk; cases h' with
    | punitTy he' => rfl
    | _ => clashw
  | unitVal he hc => intro r' h' hk; cases h' with
    | unitVal he' hc' => rfl
    | unf hs' hu' h' => subst he; simp [unfoldAt, appFn, hc] at hu'
    | _ => clashw
  | prodMk he hc ha hb hx hy iha ihb ihx ihy => intro r' h' hk; cases h' with
    | prodMk he' hc' ha' hb' hx' hy' =>
      injw he he'
      have h1 := ty_eq (iha ha' rfl)
      subst h1
      have h2 := ty_eq (ihb hb' rfl)
      subst h2
      have h3 := val_eq (ihx hx' rfl)
      subst h3
      have h4 := val_eq (ihy hy' rfl)
      subst h4; rfl
    | unf hs' hu' h' => subst he; simp [unfoldAt, appFn_appN, hc] at hu'
    | _ => clashw
  | mapFst he hd hp ht ha hb hs hstuck ihd ihp iht iha ihb ihs => intro r' h' hk; cases h' with
    | mapFst he' hd' hp' ht' ha' hb' hs' hstuck' =>
      injw he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iha ha' rfl)
      subst h2
      have h3 := ty_eq (ihb hb' rfl)
      subst h3
      have h4 := val_eq (ihs hs' rfl)
      subst h4; rfl
    | unf hs' hu' h' => exact (mapStuckW_unf_false hstuck hu' h').elim
    | _ => clashw
  | mapSnd he hd hp ht ha hb hs hstuck ihd ihp iht iha ihb ihs => intro r' h' hk; cases h' with
    | mapSnd he' hd' hp' ht' ha' hb' hs' hstuck' =>
      injw he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iha ha' rfl)
      subst h2
      have h3 := ty_eq (ihb hb' rfl)
      subst h3
      have h4 := val_eq (ihs hs' rfl)
      subst h4; rfl
    | unf hs' hu' h' => exact (mapStuckW_unf_false hstuck hu' h').elim
    | _ => clashw
  | inhMk he hc ht hx iht ihx => intro r' h' hk; cases h' with
    | inhMk he' hc' ht' hx' =>
      injw he he'
      have h1 := ty_eq (iht ht' rfl)
      subst h1
      have h2 := val_eq (ihx hx' rfl)
      subst h2; rfl
    | unf hs' hu' h' => subst he; simp [unfoldAt, appFn_appN, hc] at hu'
    | _ => clashw
  | inhDefault he ht hi iht ihi => intro r' h' hk; cases h' with
    | inhDefault he' ht' hi' =>
      injw he he'
      have h1 := ty_eq (iht ht' rfl)
      subst h1
      have h2 := val_eq (ihi hi' rfl)
      subst h2; rfl
    | _ => clashw
  | bundle2 he hd hta htb ha hb ihd ihta ihtb iha ihb => intro r' h' hk; cases h' with
    | bundle2 he' hd' hta' htb' ha' hb' =>
      injw he he'
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
    | _ => clashw


theorem cdw_fun {env : Environment} {ρ : Val} {e : Expr} {α α' : Type} {v : α} {v' : α'} (h : CDW env ρ e α v) (h' : CDW env ρ e α' v') :
    α = α' ∧ HEq v v' := val_inj (dw_fun h h' rfl)

theorem tdw_fun {env : Environment} {ρ : Val} {e : Expr} {T T' : Type} (h : TDW env ρ e T) (h' : TDW env ρ e T') : T = T' := ty_eq (dw_fun h h' rfl)

theorem cdw_eq {env : Environment} {ρ : Val} {e : Expr} {α : Type} {v v' : α} (h : CDW env ρ e α v) (h' : CDW env ρ e α v') : v = v' :=
  eq_of_heq (cdw_fun h h').2

/-! ## 5. derived rules (the equations of the task: from `x ↦ v`, `Inhabited.mk v`, and the default of that instance is `v`) -/

theorem dw_default_of_mk {env : Environment} {ρ : Val} {t x : Expr} {T : Type} {v : T} {cv : ConstructorVal}
    (hc : env.find? ``Inhabited.mk = some (.ctorInfo cv)) (ht : TDW env ρ t T) (hx : CDW env ρ x T v) :
    CDW env ρ (appN ``Inhabited.default [.succ .zero] [t, appN ``Inhabited.mk [.succ .zero] [t, x]]) T v :=
  DW.inhDefault rfl ht (DW.inhMk rfl hc ht hx)

/-- the `Prod` instance built from the two components' actual defaults: `Inhabited.mk (A×B) (Prod.mk A B x y)` -/
theorem dw_prod_inhabited {env : Environment} {ρ : Val} {a b x y : Expr} {A B : Type} {xv : A} {yv : B} {cv cp : ConstructorVal}
    (hc : env.find? ``Inhabited.mk = some (.ctorInfo cv)) (hp : env.find? ``Prod.mk = some (.ctorInfo cp))
    (ha : TDW env ρ a A) (hb : TDW env ρ b B) (hx : CDW env ρ x A xv) (hy : CDW env ρ y B yv) :
    CDW env ρ (appN ``Inhabited.mk [.succ .zero] [appN ``Prod [.zero, .zero] [a, b], appN ``Prod.mk [.zero, .zero] [a, b, x, y]]) (Inhabited (A × B)) (⟨(xv, yv)⟩ : Inhabited (A × B)) :=
  DW.inhMk rfl hc (DW.prodTy rfl ha hb) (DW.prodMk rfl hp ha hb hx hy)

/-! ## 6. the carrier and the obligation, in ONE environment -/

def CircCVW : ConstValueRel := fun env X α v =>
  ∃ d : DefinitionVal, env.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ CDW env [] d.value α v

theorem circCVW_functional : ConstValueFunctional CircCVW := by
  intro env c α β v w ⟨d, hd, _, hv⟩ ⟨d', hd', _, hv'⟩
  rw [hd] at hd'
  have := ConstantInfo.defnInfo.inj (Option.some.inj hd')
  subst this
  exact cdw_fun hv hv'

/-- the obligation of the S1k statement over `DW`, in ONE environment (the new family; `HftObCDZ` does not imply it and it does not imply `HftObCDZ`) -/
def HftObCDW (env : Environment) : Prop := CDW env [] Tools.ShippingFGCircuitS1kStmt.hftRootValue (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft)
  Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte

theorem circCVW_hft_of_obCDW {env : Environment} {d : DefinitionVal} (hd : env.find? Tools.ShippingFGCircuitS1kStmt.hftRoot = some (.defnInfo d))
    (hl : d.levelParams = []) (hv : d.value = Tools.ShippingFGCircuitS1kStmt.hftRootValue) (h : HftObCDW env) :
    CircCVW env Tools.ShippingFGCircuitS1kStmt.hftRoot (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft) Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte :=
  ⟨d, hd, hl, by rw [hv]; exact h⟩

def CircCVWAt (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (X : Name) (α : Type) (v : α) : Prop := CircCVW (envAt cref w) X α v

theorem circCVW_at_of_getEnv {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {e : Environment} (h : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w e w') {X : Name} {α : Type} {v : α} :
    CircCVW e X α v ↔ CircCVW (envAt cref w) X α v := by
  rw [Tools.ShippingEntryReadsLinked.getEnv_value h]

theorem circCVW_hft_run (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) {d : DefinitionVal}
    (hd : (envAt cref w).find? Tools.ShippingFGCircuitS1kStmt.hftRoot = some (.defnInfo d)) (hl : d.levelParams = [])
    (hv : d.value = Tools.ShippingFGCircuitS1kStmt.hftRootValue) (h : HftObCDW (envAt cref w)) :
    CircCVWAt cref w Tools.ShippingFGCircuitS1kStmt.hftRoot (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft) Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte :=
  circCVW_hft_of_obCDW hd hl hv h

/-- the final consumer: the S1k statement with `hcd : HftObCDW (envAt cref w)` (the same `HftFinalStmtWith` as S1r, with the new family) -/
def HftFinalStmtW : Prop := Tools.ShippingFGCircuitS1rCD.Stmt.HftFinalStmtWith HftObCDW

end Tools.ShippingFGCircuitS1sCD

#print axioms Tools.ShippingFGCircuitS1sCD.dw_fun
