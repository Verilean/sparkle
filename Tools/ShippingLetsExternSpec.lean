import Tools.ShippingBundleIotaRange
import Tools.ShippingLetsSigTy

/-! # Unit LC5: LC3's cannot-unfold facts through SPEC models and a fuel twin

BUILT: lc5a1 exit 0 (Tools.ShippingLetsExternSpec); audit lc5b exit 0 (ChildVertAuditTest).

`Expr.liftLooseBVars` and `Expr.instantiate1` are `extern` (C++), `rootFloat` is a `partial def`: none can be
unfolded, so `LiftRange` / `Inst1Range` / `RootFloatRange` (LC3) cannot be proved about them directly.
Route taken here:

* `liftSpec` / `inst1Spec`: PURE structural models of the documented semantics of the two externs.
  PROVED: they invent no `_machLet j` placeholder (`liftSpec_ok`, `inst1Spec_ok`). The link extern = model is
  the named PREMISE `LiftAgrees` / `Inst1Agrees` (OPEN: it is a statement about C++ code).
* `rootFloatF`: a fuel TWIN of `rootFloat` (verbatim transcription). PROVED: a successful twin answer is in range
  when `liftLooseBVars` is (`rootFloatF_ok`). The twin → real link is the named PREMISE `RootFloatTwin`
  (OPEN: `partial def` has no equation lemma). A twin result is not a result about the real function.
* `real_*` corollaries replace `RootFloatRange`, `LiftRange`, `Inst1Range`, `SigTyRange` of LC4a's primed
  theorems by `LiftAgrees`, `Inst1Agrees`, `RootFloatTwin` and `EnvTypesFVarFree env`.

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

/-- PREMISE (OPEN; C++ extern): `liftLooseBVars` agrees with its model. -/
def LiftAgrees : Prop := ∀ e s d, e.liftLooseBVars s d = liftSpec e s d

/-- PREMISE (OPEN; C++ extern): `instantiate1` agrees with its model. -/
def Inst1Agrees : Prop := ∀ b a, b.instantiate1 a = inst1Spec b a 0

theorem liftRange_of_agrees (h : LiftAgrees) : LiftRange := by
  intro n e k m he; rw [h]; exact liftSpec_ok n e k m he

theorem inst1Range_of_agrees (h : Inst1Agrees) : Inst1Range := by
  intro n b a hb ha; rw [h]; exact inst1Spec_ok n a ha b 0 hb

/-- Fuel twin of `rootFloat` (verbatim transcription; `none` = fuel exhausted). -/
def rootFloatF : Nat → Expr → Option Expr
  | 0, _ => none
  | fuel + 1, e =>
    match e with
    | .letE n t (.letE n2 t2 v2 w nd2) b nd =>
      rootFloatF fuel (.letE n2 t2 v2 (.letE n (t.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2)
    | .letE n t v b nd => (rootFloatF fuel b).map fun r => .letE n t v r nd
    | .app f a =>
      match a with
      | .letE n t v b nd =>
        (rootFloatF fuel (.app (f.liftLooseBVars 0 1) b)).map fun r => .letE n t v r nd
      | _ => some (.app f a)
    | e => some e

theorem rootFloatF_ok (hl : LiftRange) (n : Nat) :
    ∀ fuel (e r : Expr), rootFloatF fuel e = some r → LetOk n e = true → LetOk n r = true := by
  intro fuel
  induction fuel with
  | zero => intro e r h; simp [rootFloatF] at h
  | succ k ih =>
    intro e r h he
    cases e with
    | letE nm t v b nd =>
      by_cases hv : ∃ n2 t2 v2 w nd2, v = Expr.letE n2 t2 v2 w nd2
      · obtain ⟨n2, t2, v2, w, nd2, rfl⟩ := hv
        simp only [rootFloatF] at h
        simp only [LetOk, Bool.and_eq_true, and_assoc] at he
        obtain ⟨ht, ht2, hv2, hw, hb⟩ := he
        refine ih _ _ h ?_
        simp only [LetOk, Bool.and_eq_true, and_assoc]
        exact ⟨ht2, hv2, hl _ _ _ _ ht, hw, hl _ _ _ _ hb⟩
      · have e1 : rootFloatF (k + 1) (Expr.letE nm t v b nd)
            = (rootFloatF k b).map fun r => Expr.letE nm t v r nd := by
          cases v <;> first | rfl | (exfalso; exact hv ⟨_, _, _, _, _, rfl⟩)
        rw [e1] at h
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨r0, hr0, rfl⟩ := h
        simp only [LetOk, Bool.and_eq_true] at he ⊢
        exact ⟨he.1, ih _ _ hr0 he.2⟩
    | app f a =>
      by_cases ha : ∃ nm t v b nd, a = Expr.letE nm t v b nd
      · obtain ⟨nm, t, v, b, nd, rfl⟩ := ha
        simp only [rootFloatF, Option.map_eq_some_iff] at h
        obtain ⟨r0, hr0, rfl⟩ := h
        simp only [LetOk, Bool.and_eq_true, and_assoc] at he ⊢
        obtain ⟨hf, ht, hv, hb⟩ := he
        refine ⟨ht, hv, ih _ _ hr0 ?_⟩
        simp only [LetOk, Bool.and_eq_true]
        exact ⟨hl _ _ _ _ hf, hb⟩
      · have e1 : rootFloatF (k + 1) (Expr.app f a) = some (Expr.app f a) := by
          cases a <;> first | rfl | (exfalso; exact ha ⟨_, _, _, _, _, rfl⟩)
        rw [e1] at h; cases h; exact he
    | bvar _ => simp only [rootFloatF] at h; cases h; exact he
    | fvar _ => simp only [rootFloatF] at h; cases h; exact he
    | mvar _ => simp only [rootFloatF] at h; cases h; exact he
    | sort _ => simp only [rootFloatF] at h; cases h; exact he
    | const _ _ => simp only [rootFloatF] at h; cases h; exact he
    | lam _ _ _ _ => simp only [rootFloatF] at h; cases h; exact he
    | forallE _ _ _ _ => simp only [rootFloatF] at h; cases h; exact he
    | lit _ => simp only [rootFloatF] at h; cases h; exact he
    | mdata _ _ => simp only [rootFloatF] at h; cases h; exact he
    | proj _ _ _ => simp only [rootFloatF] at h; cases h; exact he

/-- PREMISE (OPEN; `partial def`): `rootFloat e` is the answer of the twin at some fuel. -/
def RootFloatTwin : Prop := ∀ e, ∃ fuel, rootFloatF fuel e = some (rootFloat e)

theorem rootFloatRange_of_twin (hl : LiftRange) (ht : RootFloatTwin) : RootFloatRange := by
  intro n v hv
  obtain ⟨fuel, hf⟩ := ht v
  exact rootFloatF_ok hl n fuel v _ hf hv

/-! ## LC4a's primed theorems with the four cannot-unfold premises replaced

`LiftAgrees`, `Inst1Agrees`, `RootFloatTwin` (OPEN, named) and, for the signature table of the real
`structEnv env`, the kernel-side environment condition `EnvTypesFVarFree env` (excludes free variables only). -/

section
variable (hla : LiftAgrees) (hia : Inst1Agrees) (hrt : RootFloatTwin) (env₀ : Lean.Environment)
  (hK : EnvTypesFVarFree env₀)
include hla hia hrt hK

theorem machConvF_post'' {n : Nat} {env : List MachVal} {d : Nat}
    {e : Lean.Expr} {st st' : MachRead} {r : Lean.Expr} (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : machConvF n (structEnv env₀) env d e st = some (some (r, st'))) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size r = true :=
  machConvF_post' (rootFloatRange_of_twin (liftRange_of_agrees hla) hrt) (liftRange_of_agrees hla)
    (inst1Range_of_agrees hia) (sigTyRange_structEnv env₀ hK) hst hE hl h

theorem machChainF_post'' {n : Nat} {env : List MachVal} {e : Lean.Expr}
    {st st' : MachRead} {ws : List (Nat × Lean.Expr)} {v : Lean.Expr} (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : machChainF n (structEnv env₀) env e st = some (some (ws, v, st'))) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size v = true :=
  machChainF_post' (rootFloatRange_of_twin (liftRange_of_agrees hla) hrt) (liftRange_of_agrees hla)
    (inst1Range_of_agrees hia) (sigTyRange_structEnv env₀ hK) hst hE hl h

theorem machConvF_init'' {n : Nat} {env : List MachVal} {d : Nat}
    {e : Lean.Expr} {st' : MachRead} {r : Lean.Expr} (hE : EnvOk 0 env) (hl : LetOk 0 e = true)
    (h : machConvF n (structEnv env₀) env d e ({} : MachRead) = some (some (r, st'))) :
    NoLetAlias st'.lets ∧ ∀ j, r = machLet j → j < st'.lets.size :=
  machConvF_init' (rootFloatRange_of_twin (liftRange_of_agrees hla) hrt) (liftRange_of_agrees hla)
    (inst1Range_of_agrees hia) (sigTyRange_structEnv env₀ hK) hE hl h

theorem machChainF_init'' {n : Nat} {env : List MachVal} {e : Lean.Expr}
    {st' : MachRead} {ws : List (Nat × Lean.Expr)} {v : Lean.Expr} (hE : EnvOk 0 env)
    (hl : LetOk 0 e = true)
    (h : machChainF n (structEnv env₀) env e ({} : MachRead) = some (some (ws, v, st'))) :
    NoLetAlias st'.lets ∧ ∀ j, v = machLet j → j < st'.lets.size :=
  machChainF_init' (rootFloatRange_of_twin (liftRange_of_agrees hla) hrt) (liftRange_of_agrees hla)
    (inst1Range_of_agrees hia) (sigTyRange_structEnv env₀ hK) hE hl h

theorem real_conv_post'' {G : OldFns} {S : Call → Prop}
    (hcov : TwinCoverAt (structEnv env₀) G S)
    {env : List MachVal} {d : Nat} {e : Lean.Expr} {st st' : MachRead} {r : Lean.Expr}
    (hS : S (Call.conv env d e st))
    (hst : RdOk st) (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : G.conv env d e st = some (r, st')) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size r = true :=
  real_conv_post' (rootFloatRange_of_twin (liftRange_of_agrees hla) hrt) (liftRange_of_agrees hla)
    (inst1Range_of_agrees hia) (sigTyRange_structEnv env₀ hK) hcov hS hst hE hl h
end

end Tools.ShippingLetsReaderInv
