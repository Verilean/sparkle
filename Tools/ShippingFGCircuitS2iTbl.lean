import Tools.ShippingFGCircuitS1wTbl
import Tools.ShippingFGCircuitS2iDTFun
set_option autoImplicit false
-- FG circuit pilot S2i: the TABLE versions of the rules of `Sh` / `DT` that read the environment (as S1wTbl / S2bShare `Rules` for `DS`), docs/FG-CIRCUIT-PILOT.md §35.
-- No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.
namespace Tools.ShippingFGCircuitS2iTbl
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5ConstValueE Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD
open Tools.ShippingFGCircuitS1rCD Tools.ShippingFGCircuitS1sCD Tools.ShippingFGCircuitS1wTbl Tools.ShippingFGCircuitS2iSh Tools.ShippingFGCircuitS2iDT

theorem instL_nil : ∀ l : Level, instL [] [] l = l
  | .zero => rfl
  | .succ l => by simp [instL, instL_nil l]
  | .max a b => by simp [instL, instL_nil a, instL_nil b]
  | .imax a b => by simp [instL, instL_nil a, instL_nil b]
  | .param n => rfl
  | .mvar _ => rfl

theorem instLE_nil : ∀ e : Expr, instLE [] [] e = e
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .mvar _ => rfl
  | .sort u => by simp [instLE, instL_nil]
  | .const c us => by
    have : (instL [] []) = id := funext instL_nil
    simp [instLE, this]
  | .app f a => by simp [instLE, instLE_nil f, instLE_nil a]
  | .lam x t b bi => by simp [instLE, instLE_nil t, instLE_nil b]
  | .forallE x t b bi => by simp [instLE, instLE_nil t, instLE_nil b]
  | .letE x t v b nd => by simp [instLE, instLE_nil t, instLE_nil v, instLE_nil b]
  | .lit _ => rfl
  | .mdata m e => by simp [instLE, instLE_nil e]
  | .proj s i e => by simp [instLE, instLE_nil e]

theorem canon_nil : ([] : List Expr) = [] → ([] : Cx) = [] := fun _ => rfl
theorem canon_cons (ρ : Cx) (a : Expr) (xs : List Expr) : (a :: xs = []) → ρ = [] := fun h => nomatch h

section Rules
variable {env : Environment} {lk : Look} (hlk : EnvLk env lk)
include hlk

theorem sh_unf_t {ρ : Cx} {c : Name} {ls : List Level} {r : DefRow} {sp : List Ent} {hn : Hn} {e' : Expr} (hr : lk c = some (.defn r))
    (hl : r.lps.length = ls.length) (hs : stopD c = false) (he' : instLE r.lps ls r.value = e') (h : Sh env [] e' sp hn) : Sh env ρ (.const c ls) sp hn := by
  obtain ⟨d, hd, h1, h2⟩ := hlk c _ hr
  subst he'
  exact Sh.unf hd (by rw [h1]; exact hl) hs (by rw [h1, h2]; exact h)

/-- a definition without universe parameters: no `instLE` to evaluate -/
theorem sh_unf0_t {ρ : Cx} {c : Name} {v : Expr} {sp : List Ent} {hn : Hn} (hr : lk c = some (.defn ⟨[], v⟩)) (hs : stopD c = false)
    (h : Sh env [] v sp hn) : Sh env ρ (.const c []) sp hn :=
  sh_unf_t hlk hr rfl hs (instLE_nil v) h

theorem sh_ctor_t {ρ : Cx} {c : Name} {ls : List Level} {r : CtorRow} {sp : List Ent} (hr : lk c = some (.ctor r)) (hs : stopD c = false)
    (hn : sp.length = r.numParams + r.numFields) : Sh env ρ (.const c ls) sp (.ctor c ls r.numParams sp) := by
  obtain ⟨cv, hc, h1, h2, h3⟩ := hlk c _ hr
  have := Sh.ctor (env := env) (ρ := ρ) (ls := ls) (sp := sp) hc hs (by rw [h2, h3]; exact hn)
  rw [h2] at this
  exact this

theorem sh_proj_t {ρ : Cx} {S : Name} {i : Nat} {x : Expr} {sp : List Ent} {hn : Hn} {c : Name} {ls : List Level} {np : Nat} {args : List Ent}
    {e' : Expr} {ρ' : Cx} {r : CtorRow} (hx : Sh env ρ x [] (.ctor c ls np args)) (hr : lk c = some (.ctor r)) (hS : r.induct = S)
    (hf : args[np + i]? = some (.clo e' ρ')) (h : Sh env ρ' e' sp hn) : Sh env ρ (.proj S i x) sp hn := by
  obtain ⟨cv, hc, h1, h2, h3⟩ := hlk c _ hr
  exact Sh.proj hx ⟨cv, hc, by rw [h1, hS]⟩ hf h

theorem sh_recNil_t {ρ : Cx} {ls : List Level} {a0 mot consc : Ent} {em : Expr} {ρm : Cx} {extra : List Ent} {lsN : List Level} {sp1 : List Ent}
    {en : Expr} {ρn : Cx} {hn : Hn} (hrec : lk ``List.rec = some .recl)
    (hm : Sh env ρm em [] (.ctor ``List.nil lsN 1 sp1)) (h : Sh env ρn en extra hn) :
    Sh env ρ (.const ``List.rec ls) (a0 :: mot :: .clo en ρn :: consc :: .clo em ρm :: extra) hn := by
  obtain ⟨ri, hi⟩ := hlk _ _ hrec
  exact Sh.recNil hi hm h

theorem sh_recCons_t {ρ : Cx} {ls : List Level} {a0 mot nilc : Ent} {em : Expr} {ρm : Cx} {extra : List Ent} {lsC : List Level} {al hd tl : Ent}
    {ec : Expr} {ρc : Cx} {hn : Hn} (hrec : lk ``List.rec = some .recl)
    (hm : Sh env ρm em [] (.ctor ``List.cons lsC 1 [al, hd, tl]))
    (h : Sh env ρc ec (hd :: tl :: .clo (recCallE ls) [tl, .clo ec ρc, nilc, mot, a0] :: extra) hn) :
    Sh env ρ (.const ``List.rec ls) (a0 :: mot :: nilc :: .clo ec ρc :: .clo em ρm :: extra) hn := by
  obtain ⟨ri, hi⟩ := hlk _ _ hrec
  exact Sh.recCons hi hm h

theorem dt_unitVal_t {ρ : Cx} {e : Expr} {cw : CtorRow} (he : e = .const ``PUnit.unit [.succ .zero]) (hr : lk ``PUnit.unit = some (.ctor cw)) :
    CDT env ρ e Unit () := by
  obtain ⟨cv, hc, _⟩ := hlk _ _ hr
  exact DT.unitVal he hc

theorem dt_boolFalse_t {ρ : Cx} {e : Expr} {cw : CtorRow} (he : e = .const ``Bool.false []) (hr : lk ``Bool.false = some (.ctor cw)) :
    CDT env ρ e Bool false := by
  obtain ⟨cv, hc, _⟩ := hlk _ _ hr
  exact DT.boolFalse he hc

theorem dt_boolTrue_t {ρ : Cx} {e : Expr} {cw : CtorRow} (he : e = .const ``Bool.true []) (hr : lk ``Bool.true = some (.ctor cw)) :
    CDT env ρ e Bool true := by
  obtain ⟨cv, hc, _⟩ := hlk _ _ hr
  exact DT.boolTrue he hc

theorem dt_prodMk_t {ρ : Cx} {e a b x y : Expr} {A B : Type} {xv : A} {yv : B} {cw : CtorRow}
    (he : e = appN ``Prod.mk [.zero, .zero] [a, b, x, y]) (hr : lk ``Prod.mk = some (.ctor cw))
    (ha : TDT env ρ a A) (hb : TDT env ρ b B) (hx : CDT env ρ x A xv) (hy : CDT env ρ y B yv) : CDT env ρ e (A × B) (xv, yv) := by
  obtain ⟨cv, hc, _⟩ := hlk _ _ hr
  exact DT.prodMk he hc ha hb hx hy

theorem dt_inhMk_t {ρ : Cx} {e t x : Expr} {u : Level} {T : Type} {v : T} {cw : CtorRow} (he : e = appN ``Inhabited.mk [u] [t, x]) (hu : lvlNatT u = some 1)
    (hr : lk ``Inhabited.mk = some (.ctor cw)) (ht : TDT env ρ t T) (hx : CDT env ρ x T v) : CDT env ρ e (Inhabited T) (⟨v⟩ : Inhabited T) := by
  obtain ⟨cv, hc, _⟩ := hlk _ _ hr
  exact DT.inhMk he hu hc ht hx

end Rules

end Tools.ShippingFGCircuitS2iTbl
