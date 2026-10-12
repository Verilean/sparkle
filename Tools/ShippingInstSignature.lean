import Sparkle.Compiler.Elab

/-! # P1 — what `instSignature?` / `instSignatureS?` return

`docs/parallel/B-callkinds.md` §7, invariant P1: the signature of a callee
the parent's reader uses (`StructEnv.inst`, `StructEnv.instS` of
`structEnv env`) is read off the callee's CONSTANT in `env` — its type's
binder kinds (`telescopeKinds`) and, for the one-Signal case, its result
kind (`machResultKind?`). Both functions are plain definitions; the lemmas
are inversions of their `Option` values.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingInstSignature
open Lean
open Sparkle.Compiler.Elab

/-- **P1** (one-Signal callee). -/
theorem instSignature?_some {env : Environment} {n : Name}
    {kinds : List MixedGateBinder} {res : MixedGateBinder}
    (h : instSignature? env n = some (kinds, res)) :
    Sparkle.Compiler.isHardwareModule env n = true ∧
    ∃ ci, env.find? n = some ci ∧ telescopeKinds ci.type = some kinds ∧
      machResultKind? ci.type = some res := by
  unfold instSignature? at h
  split at h
  next => cases h
  next hhw =>
    split at h
    next ci hfind =>
      cases hk : telescopeKinds ci.type with
      | none => simp [hk] at h
      | some ks =>
        cases hr : machResultKind? ci.type with
        | none => simp [hk, hr] at h
        | some r =>
          simp [hk, hr] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨by simpa using hhw, ci, hfind, hk, hr⟩
    next => cases h

/-- **P1** (structure callee): the type handed to the reader is the
constant's, the constant has no universe parameter and is not a one-Signal
callee. -/
theorem instSignatureS?_some {env : Environment} {n : Name}
    {kinds : List MixedGateBinder} {ty : Lean.Expr}
    (h : instSignatureS? env n = some (kinds, ty)) :
    Sparkle.Compiler.isHardwareModule env n = true ∧
    ∃ ci, env.find? n = some ci ∧ telescopeKinds ci.type = some kinds ∧ ty = ci.type ∧
      machResultKind? ci.type = none := by
  unfold instSignatureS? at h
  split at h
  next => cases h
  next hhw =>
    split at h
    next ci hfind =>
      split at h
      next => cases h
      next hno =>
        cases hk : telescopeKinds ci.type with
        | none => simp [hk] at h
        | some ks =>
          simp [hk] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨by simpa using hhw, ci, hfind, hk, rfl, ?_⟩
          cases hr : machResultKind? ci.type with
          | none => rfl
          | some r => simp [hr] at hno
    next => cases h

/-- The reader's environment reads the two signatures by these functions. -/
theorem structEnv_inst (env : Environment) : (structEnv env).inst = instSignature? env := rfl

theorem structEnv_instS (env : Environment) : (structEnv env).instS = instSignatureS? env := rfl

end Tools.ShippingInstSignature
