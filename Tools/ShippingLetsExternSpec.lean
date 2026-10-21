import Tools.ShippingBundleIotaRange
import Tools.ShippingLetsSigTy

/-! # Unit LC5: LC3's cannot-unfold facts through SPEC models and a fuel twin

BUILT: lc5a1 exit 0 (LC5); LC6 revision: lc6a1 exit 0 (Tools.ShippingLetsExternSpec), audit lc6b exit 0.

LC6 revision (supersedes LC5's agreement conditions): the interface `PureFacts` (Base) was narrowed to what the
reader's static call sites use: `rootFloat` only on `LetOk 0` inputs, `liftLooseBVars` only at `(0,1)`/`(1,1)` on
`LetOk 0` inputs. The agreement premises are narrowed the same way (`LiftAgrees`, `RootFloatAgrees`); `Inst1Agrees`
is unchanged. `rootFloatF` / `RootFloatTwin` (finite fuel for every `Expr`) are REPLACED by the TOTAL model
`rootFloatS` whose termination is PROVED, so the premise is only `rootFloat e = rootFloatS e` (`LetOk 0 e`).
Direct unfolding of the externs / `partial def` is unavailable; the correspondence is still UNPROVED (PREMISE).
Number of premises: still 4 (`LiftAgrees`, `Inst1Agrees`, `RootFloatAgrees`, `EnvTypesFVarFree`), each narrower
than before except `Inst1Agrees`/`EnvTypesFVarFree`.

* `liftSpec` / `inst1Spec`: PURE structural models of the documented semantics of the two externs.
  PROVED: they invent no `_machLet j` placeholder (`liftSpec_ok`, `inst1Spec_ok`).
* `rootFloatS`: total model of `rootFloat` (extern lift replaced by `liftSpec`); PROVED terminating, PROVED range
  (`rootFloatS_ok`, no use of any extern premise).
* `real_*` corollaries replace the ranges of LC4a's primed theorems by `LiftAgrees`, `Inst1Agrees`,
  `RootFloatAgrees`, `EnvTypesFVarFree env`.

No sorry, no axiom, no native_decide. -/
namespace Tools.ShippingLetsReaderInv
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsAliasInv Tools.ShippingReaderFuel
open Sparkle.Compiler.MachRawSurface

/-- Model of `Expr.liftLooseBVars e s d`: loose bound variables `≥ s` are raised by `d`. -/
def liftSpec : Expr → Nat → Nat → Expr
  | .bvar i, s, d => if i < s then .bvar i else .bvar (i + d)
  | .app f a, s, d => .app (liftSpec f s d) (liftSpec a s d)
  | .lam n t b bi, s, d => .lam n (liftSpec t s d) (liftSpec b (s + 1) d) bi
  | .forallE n t b bi, s, d => .forallE n (liftSpec t s d) (liftSpec b (s + 1) d) bi
  | .letE n t v b nd, s, d => .letE n (liftSpec t s d) (liftSpec v s d) (liftSpec b (s + 1) d) nd
  | .mdata m e, s, d => .mdata m (liftSpec e s d)
  | .proj n i e, s, d => .proj n i (liftSpec e s d)
  | e, _, _ => e

/-- Model of `Expr.instantiate1 b a` through the offset form: loose `bvar off` becomes `a` (lifted by `off`),
larger ones are lowered. -/
def inst1Spec : Expr → Expr → Nat → Expr
  | .bvar i, a, off =>
    if i < off then .bvar i else if i = off then liftSpec a 0 off else .bvar (i - 1)
  | .app f x, a, off => .app (inst1Spec f a off) (inst1Spec x a off)
  | .lam n t b bi, a, off => .lam n (inst1Spec t a off) (inst1Spec b a (off + 1)) bi
  | .forallE n t b bi, a, off => .forallE n (inst1Spec t a off) (inst1Spec b a (off + 1)) bi
  | .letE n t v b nd, a, off =>
    .letE n (inst1Spec t a off) (inst1Spec v a off) (inst1Spec b a (off + 1)) nd
  | .mdata m e, a, off => .mdata m (inst1Spec e a off)
  | .proj n i e, a, off => .proj n i (inst1Spec e a off)
  | e, _, _ => e

theorem liftSpec_ok (n : Nat) : ∀ (e : Expr) s d, LetOk n e = true → LetOk n (liftSpec e s d) = true := by
  intro e
  induction e with
  | bvar i => intro s d _; unfold liftSpec; split <;> rfl
  | app f a ihf iha =>
    intro s d h; simp only [LetOk, Bool.and_eq_true] at h
    simp only [liftSpec, LetOk, Bool.and_eq_true]; exact ⟨ihf _ _ h.1, iha _ _ h.2⟩
  | lam _ t b _ iht ihb =>
    intro s d h; simp only [LetOk, Bool.and_eq_true] at h
    simp only [liftSpec, LetOk, Bool.and_eq_true]; exact ⟨iht _ _ h.1, ihb _ _ h.2⟩
  | forallE _ t b _ iht ihb =>
    intro s d h; simp only [LetOk, Bool.and_eq_true] at h
    simp only [liftSpec, LetOk, Bool.and_eq_true]; exact ⟨iht _ _ h.1, ihb _ _ h.2⟩
  | letE _ t v b _ iht ihv ihb =>
    intro s d h; simp only [LetOk, Bool.and_eq_true] at h
    simp only [liftSpec, LetOk, Bool.and_eq_true]
    exact ⟨⟨iht _ _ h.1.1, ihv _ _ h.1.2⟩, ihb _ _ h.2⟩
  | mdata _ e ih => intro s d h; simp only [LetOk] at h; simp only [liftSpec, LetOk]; exact ih _ _ h
  | proj _ _ e ih => intro s d h; simp only [LetOk] at h; simp only [liftSpec, LetOk]; exact ih _ _ h
  | fvar _ => intro s d h; exact h
  | mvar _ => intro s d h; exact h
  | sort _ => intro s d h; exact h
  | const _ _ => intro s d h; exact h
  | lit _ => intro s d h; exact h

theorem inst1Spec_ok (n : Nat) (a : Expr) (ha : LetOk n a = true) :
    ∀ (e : Expr) off, LetOk n e = true → LetOk n (inst1Spec e a off) = true := by
  intro e
  induction e with
  | bvar i =>
    intro off _; unfold inst1Spec; split
    · rfl
    · split
      · exact liftSpec_ok n a _ _ ha
      · rfl
  | app f x ihf ihx =>
    intro off h; simp only [LetOk, Bool.and_eq_true] at h
    simp only [inst1Spec, LetOk, Bool.and_eq_true]; exact ⟨ihf _ h.1, ihx _ h.2⟩
  | lam _ t b _ iht ihb =>
    intro off h; simp only [LetOk, Bool.and_eq_true] at h
    simp only [inst1Spec, LetOk, Bool.and_eq_true]; exact ⟨iht _ h.1, ihb _ h.2⟩
  | forallE _ t b _ iht ihb =>
    intro off h; simp only [LetOk, Bool.and_eq_true] at h
    simp only [inst1Spec, LetOk, Bool.and_eq_true]; exact ⟨iht _ h.1, ihb _ h.2⟩
  | letE _ t v b _ iht ihv ihb =>
    intro off h; simp only [LetOk, Bool.and_eq_true] at h
    simp only [inst1Spec, LetOk, Bool.and_eq_true]
    exact ⟨⟨iht _ h.1.1, ihv _ h.1.2⟩, ihb _ h.2⟩
  | mdata _ e ih => intro off h; simp only [LetOk] at h; simp only [inst1Spec, LetOk]; exact ih _ h
  | proj _ _ e ih => intro off h; simp only [LetOk] at h; simp only [inst1Spec, LetOk]; exact ih _ h
  | fvar _ => intro off h; exact h
  | mvar _ => intro off h; exact h
  | sort _ => intro off h; exact h
  | const _ _ => intro off h; exact h
  | lit _ => intro off h; exact h

/-- PREMISE (OPEN; C++ extern), WEAKENED by LC6 to the calls the reader makes: on inputs with no `_machLet`
placeholder (`LetOk 0`), `liftLooseBVars` at `(0,1)` and `(1,1)` agrees with its model. These are the only
`(start, shift)` pairs the reader's `.letE` arms use (`conv_letE_sat`, the `machChain` twin of it:
`Tools/ShippingLetsReaderInv.lean`, 4 call sites; the induction covers every reader path, so this is a
property of the STATIC call sites, not of the twin's success). -/
def LiftAgrees : Prop :=
  ∀ e, LetOk 0 e = true → e.liftLooseBVars 0 1 = liftSpec e 0 1 ∧ e.liftLooseBVars 1 1 = liftSpec e 1 1

/-- PREMISE (OPEN; C++ extern): `instantiate1` agrees with its model. Unchanged from LC5: the only use is the
`forallE`-body instantiation of `instRes` (offset 0), but the interface `PureFacts.inst1` quantifies over the
level `n` and the body, and the callers' `n` and arguments are not narrowed here. -/
def Inst1Agrees : Prop := ∀ b a, b.instantiate1 a = inst1Spec b a 0

theorem liftRange_of_agrees (h : LiftAgrees) : LiftRange := by
  intro e he
  obtain ⟨h0, h1⟩ := h e he
  rw [h0, h1]; exact ⟨liftSpec_ok 0 e _ _ he, liftSpec_ok 0 e _ _ he⟩

theorem inst1Range_of_agrees (h : Inst1Agrees) : Inst1Range := by
  intro n b a hb ha; rw [h]; exact inst1Spec_ok n a ha b 0 hb

/-! ## `rootFloat`: a TOTAL model, termination PROVED

`rootFloat` is a `partial def`, so nothing about it can be unfolded. `rootFloatS` is its verbatim transcription
with `liftLooseBVars` replaced by `liftSpec`; it is NOT a fuel twin: it is a total function, its termination is
PROVED below (measure `nu`: the value of a `let`/the argument of an application is weighted double; `liftSpec`
preserves `nsz` and `nu`). The remaining link `rootFloat = rootFloatS` is the named PREMISE `RootFloatAgrees`;
no finite-fuel existence is assumed any more (LC5's `RootFloatAgrees` asked for that for every `Expr`). -/

/-- Node count (every `bvar`/leaf counts 1, so `liftSpec` preserves it). -/
def nsz : Expr → Nat
  | .app f a => nsz f + nsz a + 1
  | .lam _ t b _ => nsz t + nsz b + 1
  | .forallE _ t b _ => nsz t + nsz b + 1
  | .letE _ t v b _ => nsz t + nsz v + nsz b + 1
  | .mdata _ e => nsz e + 1
  | .proj _ _ e => nsz e + 1
  | _ => 1

/-- Termination measure of `rootFloatS`. -/
def nu : Expr → Nat
  | .letE _ _ v b _ => 2 * nsz v + nu b + 1
  | .app f a => nsz f + nu a + 1
  | _ => 0

theorem nsz_liftSpec : ∀ (e : Expr) s d, nsz (liftSpec e s d) = nsz e := by
  intro e
  induction e with
  | bvar i => intro s d; unfold liftSpec; split <;> rfl
  | app f a ihf iha => intro s d; simp [liftSpec, nsz, ihf, iha]
  | lam _ t b _ iht ihb => intro s d; simp [liftSpec, nsz, iht, ihb]
  | forallE _ t b _ iht ihb => intro s d; simp [liftSpec, nsz, iht, ihb]
  | letE _ t v b _ iht ihv ihb => intro s d; simp [liftSpec, nsz, iht, ihv, ihb]
  | mdata _ e ih => intro s d; simp [liftSpec, nsz, ih]
  | proj _ _ e ih => intro s d; simp [liftSpec, nsz, ih]
  | fvar _ => intro s d; rfl
  | mvar _ => intro s d; rfl
  | sort _ => intro s d; rfl
  | const _ _ => intro s d; rfl
  | lit _ => intro s d; rfl

theorem nu_liftSpec : ∀ (e : Expr) s d, nu (liftSpec e s d) = nu e := by
  intro e
  induction e with
  | bvar i => intro s d; unfold liftSpec; split <;> rfl
  | app f a ihf iha => intro s d; simp [liftSpec, nu, nsz_liftSpec, iha]
  | lam _ t b _ iht ihb => intro s d; rfl
  | forallE _ t b _ iht ihb => intro s d; rfl
  | letE _ t v b _ iht ihv ihb => intro s d; simp [liftSpec, nu, nsz_liftSpec, ihb]
  | mdata _ e ih => intro s d; rfl
  | proj _ _ e ih => intro s d; rfl
  | fvar _ => intro s d; rfl
  | mvar _ => intro s d; rfl
  | sort _ => intro s d; rfl
  | const _ _ => intro s d; rfl
  | lit _ => intro s d; rfl

/-- TOTAL model of `rootFloat` (see the section header). -/
def rootFloatS : Expr → Expr
  | .letE n t (.letE n2 t2 v2 w nd2) b nd =>
    rootFloatS (.letE n2 t2 v2 (.letE n (liftSpec t 0 1) w (liftSpec b 1 1) nd) nd2)
  | .letE n t v b nd => .letE n t v (rootFloatS b) nd
  | .app f (.letE n t v b nd) => .letE n t v (rootFloatS (.app (liftSpec f 0 1) b)) nd
  | e => e
termination_by e => nu e
decreasing_by
  all_goals simp_wf
  all_goals simp [nu, nsz, nu_liftSpec, nsz_liftSpec]
  all_goals omega

theorem rootFloatS_ok (n : Nat) : ∀ e : Expr, LetOk n e = true → LetOk n (rootFloatS e) = true := by
  intro e
  induction e using rootFloatS.induct with
  | case1 nm t n2 t2 v2 w nd2 b nd ih =>
    intro he
    rw [rootFloatS]
    simp only [LetOk, Bool.and_eq_true, and_assoc] at he
    obtain ⟨ht, ht2, hv2, hw, hb⟩ := he
    refine ih ?_
    simp only [LetOk, Bool.and_eq_true, and_assoc]
    exact ⟨ht2, hv2, liftSpec_ok n t _ _ ht, hw, liftSpec_ok n b _ _ hb⟩
  | case2 nm t v b nd hv ih =>
    intro he
    rw [rootFloatS]
    · simp only [LetOk, Bool.and_eq_true] at he ⊢
      exact ⟨he.1, ih he.2⟩
    · exact hv
  | case3 f nm t v b nd ih =>
    intro he
    rw [rootFloatS]
    simp only [LetOk, Bool.and_eq_true, and_assoc] at he ⊢
    obtain ⟨hf, ht, hv, hb⟩ := he
    refine ⟨ht, hv, ih ?_⟩
    simp only [LetOk, Bool.and_eq_true]
    exact ⟨liftSpec_ok n f _ _ hf, hb⟩
  | case4 e h1 h2 h3 =>
    intro he
    rw [rootFloatS]
    · exact he
    · exact h1
    · exact h2
    · exact h3

/-- PREMISE (OPEN; `partial def`), WEAKENED by LC6: on a `_machLet`-free input (`LetOk 0`; the only calls of the
reader: `rootFloat v` for a `let` value `v` with `LetOk 0 v`) the real `rootFloat` equals the total model.
Totality of the model is PROVED (`rootFloatS`), so the finite-fuel part of LC5's `RootFloatAgrees` is gone; what
remains is the faithfulness of the transcription (including `liftLooseBVars` = `liftSpec`). -/
def RootFloatAgrees : Prop := ∀ e, LetOk 0 e = true → rootFloat e = rootFloatS e

theorem rootFloatRange_of_agrees (ht : RootFloatAgrees) : RootFloatRange := by
  intro v hv; rw [ht v hv]; exact rootFloatS_ok 0 v hv

/-! ## LC4a's primed theorems with the four cannot-unfold premises replaced

`LiftAgrees`, `Inst1Agrees`, `RootFloatAgrees` (OPEN, named) and, for the signature table of the real
`structEnv env`, the kernel-side environment condition `EnvTypesFVarFree env` (excludes free variables only). -/

section
variable (hla : LiftAgrees) (hia : Inst1Agrees) (hrt : RootFloatAgrees) (env₀ : Lean.Environment)
  (hK : EnvTypesFVarFree env₀)
include hla hia hrt hK

theorem machConvF_post'' {n : Nat} {env : List MachVal} {d : Nat}
    {e : Lean.Expr} {st st' : MachRead} {r : Lean.Expr} (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : machConvF n (structEnv env₀) env d e st = some (some (r, st'))) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size r = true :=
  machConvF_post' (rootFloatRange_of_agrees hrt) (liftRange_of_agrees hla)
    (inst1Range_of_agrees hia) (sigTyRange_structEnv env₀ hK) hst hE hl h

theorem machChainF_post'' {n : Nat} {env : List MachVal} {e : Lean.Expr}
    {st st' : MachRead} {ws : List (Nat × Lean.Expr)} {v : Lean.Expr} (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : machChainF n (structEnv env₀) env e st = some (some (ws, v, st'))) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size v = true :=
  machChainF_post' (rootFloatRange_of_agrees hrt) (liftRange_of_agrees hla)
    (inst1Range_of_agrees hia) (sigTyRange_structEnv env₀ hK) hst hE hl h

theorem machConvF_init'' {n : Nat} {env : List MachVal} {d : Nat}
    {e : Lean.Expr} {st' : MachRead} {r : Lean.Expr} (hE : EnvOk 0 env) (hl : LetOk 0 e = true)
    (h : machConvF n (structEnv env₀) env d e ({} : MachRead) = some (some (r, st'))) :
    NoLetAlias st'.lets ∧ ∀ j, r = machLet j → j < st'.lets.size :=
  machConvF_init' (rootFloatRange_of_agrees hrt) (liftRange_of_agrees hla)
    (inst1Range_of_agrees hia) (sigTyRange_structEnv env₀ hK) hE hl h

theorem machChainF_init'' {n : Nat} {env : List MachVal} {e : Lean.Expr}
    {st' : MachRead} {ws : List (Nat × Lean.Expr)} {v : Lean.Expr} (hE : EnvOk 0 env)
    (hl : LetOk 0 e = true)
    (h : machChainF n (structEnv env₀) env e ({} : MachRead) = some (some (ws, v, st'))) :
    NoLetAlias st'.lets ∧ ∀ j, v = machLet j → j < st'.lets.size :=
  machChainF_init' (rootFloatRange_of_agrees hrt) (liftRange_of_agrees hla)
    (inst1Range_of_agrees hia) (sigTyRange_structEnv env₀ hK) hE hl h

theorem real_conv_post'' {G : OldFns} {S : Call → Prop}
    (hcov : TwinCoverAt (structEnv env₀) G S)
    {env : List MachVal} {d : Nat} {e : Lean.Expr} {st st' : MachRead} {r : Lean.Expr}
    (hS : S (Call.conv env d e st))
    (hst : RdOk st) (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : G.conv env d e st = some (r, st')) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size r = true :=
  real_conv_post' (rootFloatRange_of_agrees hrt) (liftRange_of_agrees hla)
    (inst1Range_of_agrees hia) (sigTyRange_structEnv env₀ hK) hcov hS hst hE hl h
end

end Tools.ShippingLetsReaderInv
