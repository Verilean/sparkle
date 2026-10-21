import Tools.ShippingLetsReaderInvMain

/-! # Unit LC4b: where `SigTyRange` comes from

BUILT: lc4b1 exit 0 (Tools.ShippingLetsSigTy); audit lc4b2.

Trace (Sparkle/Compiler/Elab.lean): `synthesizeCombinational` calls `machineShape? … (structEnv env)`
(5314); `structEnv env` (4394) sets `instS := instSignatureS? env` (4385). `instSignatureS? env n` is a TOTAL
function: it returns `(kinds, ci.type)` for a constant `ci` found by `env.find? n`. So every type in `senv.instS`
is the declared type of an environment constant. `_machLet j` is an `Expr.fvar`; the reader invents it
(`machLet`, Elab 3502) and it is never written into the environment. A declared type that has NO free variable
cannot mention it.

PROVED here: `SigTyRange (structEnv env)` follows from `EnvTypesFVarFree env`.
PREMISE (named, not an axiom): `EnvTypesFVarFree env` — every constant of `env` has a type with no `fvar`.
This is a fact about Lean's kernel (`addDecl` rejects declarations with free variables); it is NOT proved here
(`Lean.Environment` is not modelled), and the twin/real-reader link stays OPEN.
The declaration BODY input `LetOk 0 e`: the reader is not called on `d.value` but on the result of
`packTupleInputs`, `mixedGatePeel`, `machNorm`, `inlFoldNat`, `zeroLit`, `rootFloat`, `machLoopAsLet`, `machRoot`
(partial / extern functions); `LetOk 0` of that is NOT derived (OPEN, exact Prop `BodyLetOk` below). -/
namespace Tools.ShippingLetsReaderInv
open Lean Sparkle.Compiler.Elab

/-- No free variable at all (structural). -/
def NoFv : Lean.Expr → Bool
  | .fvar _ => false
  | .app f a => NoFv f && NoFv a
  | .lam _ t b _ => NoFv t && NoFv b
  | .forallE _ t b _ => NoFv t && NoFv b
  | .letE _ t v b _ => NoFv t && NoFv v && NoFv b
  | .mdata _ e => NoFv e
  | .proj _ _ e => NoFv e
  | _ => true

theorem letOk_of_noFv (n : Nat) : ∀ e : Lean.Expr, NoFv e = true → LetOk n e = true
  | .bvar _, _ => rfl
  | .fvar _, h => by simp [NoFv] at h
  | .mvar _, _ => rfl
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .lit _, _ => rfl
  | .app f a, h => by
    simp only [NoFv, Bool.and_eq_true] at h
    simp [LetOk, letOk_of_noFv n f h.1, letOk_of_noFv n a h.2]
  | .lam _ t b _, h => by
    simp only [NoFv, Bool.and_eq_true] at h
    simp [LetOk, letOk_of_noFv n t h.1, letOk_of_noFv n b h.2]
  | .forallE _ t b _, h => by
    simp only [NoFv, Bool.and_eq_true] at h
    simp [LetOk, letOk_of_noFv n t h.1, letOk_of_noFv n b h.2]
  | .letE _ t v b _, h => by
    simp only [NoFv, Bool.and_eq_true] at h
    simp [LetOk, letOk_of_noFv n t h.1.1, letOk_of_noFv n v h.1.2, letOk_of_noFv n b h.2]
  | .mdata _ e, h => by
    simp only [NoFv] at h
    simp [LetOk, letOk_of_noFv n e h]
  | .proj _ _ e, h => by
    simp only [NoFv] at h
    simp [LetOk, letOk_of_noFv n e h]

/-- PREMISE (kernel fact, NOT proved here): the declared type of every constant of `env` is free-variable-free
(Lean's `addDecl` rejects free variables; `Environment` is not modelled in this development). -/
def EnvTypesFVarFree (env : Lean.Environment) : Prop :=
  ∀ n ci, env.find? n = some ci → NoFv ci.type = true

/-- PROVED: the types stored in `instSignatureS? env` are declared types of environment constants. -/
theorem instSignatureS_type (env : Lean.Environment) (n : Name) (kinds ty)
    (h : instSignatureS? env n = some (kinds, ty)) :
    ∃ ci, env.find? n = some ci ∧ ci.type = ty := by
  unfold instSignatureS? at h
  split at h
  · simp at h
  · split at h
    · rename_i ci hci
      split at h
      · simp at h
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨k, _, hk⟩ := h
        simp only [Prod.mk.injEq] at hk
        exact ⟨ci, hci, hk.2⟩
    · simp at h

/-- PROVED: `SigTyRange` of the real `structEnv env`, from the kernel premise `EnvTypesFVarFree env`. -/
theorem sigTyRange_structEnv (env : Lean.Environment) (hK : EnvTypesFVarFree env) :
    SigTyRange (structEnv env) := by
  intro c kinds ty h n
  have h' : instSignatureS? env c = some (kinds, ty) := h
  obtain ⟨ci, hci, rfl⟩ := instSignatureS_type env c kinds ty h'
  exact letOk_of_noFv n _ (hK c ci hci)

/-- PROVED: the raw declaration value is free-variable-free (kernel fact `hv`), so `LetOk 0` holds of it.
This is only the INPUT of `machineShape?`; the reader receives the expression AFTER `packTupleInputs`,
`mixedGatePeel` (which instantiates binders with `_machIn`-style fvars, so `NoFv` is NOT preserved),
`machNorm`, `inlFoldNat`, `zeroLit`, `rootFloat`, `machLoopAsLet`, `machRoot` (partial / extern).
OPEN, exact Prop (consumer: the entry condition `LetOk 0 e` of `machConvF_post` & co.):
`LetOk 0 (the expression machineShape? hands to machConv/machChain/machLoopRoot) = true`; not derived. -/
theorem letOk_declValue (n : Nat) (value : Lean.Expr) (hv : NoFv value = true) : LetOk n value = true :=
  letOk_of_noFv n value hv

end Tools.ShippingLetsReaderInv
