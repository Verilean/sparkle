import Tools.ShippingGen5ReaderTraceExtract
import Tools.ShippingLetsSigTy
import Tools.Assume.EnvSigTy
set_option autoImplicit false
-- NOT BUILT: written against freeze rev9 `scripts/gen5/DG_READERTRACE_FREEZE_REV9.md` §3 (U-R4e2: `ty` component of `machInstCallS?`, under the named condition `SigTyClosed`). No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R4e2: the `ty` component of `machInstCallS?` is `NoPh ∧ BvarLt 0`

`ty` comes from the table `senv.instS`, not from the input. `NoPh ty` follows from the existing T1L-53 `EnvTypesFVarFree`
(a lemma: no `fvar` at all ⇒ no placeholder). `BvarLt 0 ty` is the named condition `SigTyClosed`
(`Tools/Assume/EnvSigTy.lean`, FG +1), taken as a hypothesis; nothing is assumed in this file. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Assume.EnvSigTy

theorem noPh_of_noFv : ∀ e : Lean.Expr, NoFv e = true → NoPh e = true
  | .fvar _, h => by simp [NoFv] at h
  | .bvar _, _ => rfl
  | .mvar _, _ => rfl
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .lit _, _ => rfl
  | .app f a, h => by
    simp only [NoFv, Bool.and_eq_true] at h
    simp [NoPh, noPh_of_noFv f h.1, noPh_of_noFv a h.2]
  | .lam _ t b _, h => by
    simp only [NoFv, Bool.and_eq_true] at h
    simp [NoPh, noPh_of_noFv t h.1, noPh_of_noFv b h.2]
  | .forallE _ t b _, h => by
    simp only [NoFv, Bool.and_eq_true] at h
    simp [NoPh, noPh_of_noFv t h.1, noPh_of_noFv b h.2]
  | .letE _ t v b _, h => by
    simp only [NoFv, Bool.and_eq_true] at h
    simp [NoPh, noPh_of_noFv t h.1.1, noPh_of_noFv v h.1.2, noPh_of_noFv b h.2]
  | .mdata _ e, h => by
    simp only [NoFv] at h
    simp [NoPh, noPh_of_noFv e h]
  | .proj _ _ e, h => by
    simp only [NoFv] at h
    simp [NoPh, noPh_of_noFv e h]

/-- the form U-R8 uses: every `instS` type is placeholder-free and closed. -/
def SigTyPh (senv : StructEnv) : Prop :=
  ∀ (c : Lean.Name) (kinds : List MixedGateBinder) (ty : Lean.Expr),
    senv.instS c = some (kinds, ty) → NoPh ty = true ∧ BvarLt 0 ty = true

theorem sigTyPh_of (env : Lean.Environment) (hK : EnvTypesFVarFree env) (hC : SigTyClosed (structEnv env)) :
    SigTyPh (structEnv env) := by
  intro c kinds ty h
  refine ⟨?_, hC c kinds ty h⟩
  obtain ⟨ci, hf, rfl⟩ := instSignatureS_type env c kinds ty h
  exact noPh_of_noFv _ (hK c ci hf)

theorem machInstCallS?_ty_ph {senv : StructEnv} (hS : SigTyPh senv) {e : Lean.Expr} {c : Name}
    {kinds : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr}
    (h : machInstCallS? senv e = some (c, kinds, ty, args)) : NoPh ty = true ∧ BvarLt 0 ty = true :=
  hS c kinds ty (machInstCallS?_spec h).1

end Tools.ShippingGen5ReaderTrace
