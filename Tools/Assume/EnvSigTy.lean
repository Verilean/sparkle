import Tools.ShippingGen5ReaderTrace
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.Assume.EnvSigTy, exit 0) on the tree of this file's commit. Assumption module (statements only; no theorems).

/-! # Environment assumption: `instS` signature types are closed (`SigTyClosed`)

**This file holds ONLY an assumption statement** — a `Prop` definition that proofs take as a hypothesis. It is not an
`axiom` and not a theorem. A change here is a change of what is assumed and needs reviewer approval; proof files must
not redefine it.

Design: `scripts/gen5/DG_READERTRACE_FREEZE_REV9.md` §3 (reviewer-approved: type and domain as written there).

* What is assumed: every type `ty` returned by `senv.instS c = some (kinds, ty)` has no loose bound variable
  (`BvarLt 0 ty = true`). For `senv = structEnv env₀`, `ty` is the declared type `ci.type` of an environment constant
  (`instSignatureS_type`, proved in `Tools/ShippingLetsSigTy.lean`), so this is the kernel fact that a declared type is
  a closed term.
* Why not proved: `Lean.Environment` is not modelled in this development, and `EnvTypesFVarFree` (T1L-53) does not give
  it (absence of `fvar` and absence of loose `bvar` are different properties). This investigation found no supplier
  or route for it in the development; that is not a claim that it is underivable.
* Ledger: counted once as **FG +1** (shared environment fact of C0; DG-ENV `sparkle-gen5-dg-env` is the owner of the
  placement, next to the `inst` / `instS` SigEq condition and separate from `EnvTypesFVarFree`). It does not
  change T1L-53. Registered by the commit that adds this file.
* The `NoPh` half needed by the reader trace is NOT assumed here: it follows from `EnvTypesFVarFree` by a lemma
  (`Tools/ShippingGen5ReaderTraceSigTy.lean`). -/

namespace Tools.Assume.EnvSigTy
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5ReaderTrace

/-- **ASSUMPTION `SigTyClosed` (FG +1).** Every signature type in the `instS` table has no loose bound variable.
* Domain: every `(c, kinds, ty)` with `senv.instS c = some (kinds, ty)`; for `senv = structEnv env₀`, `env₀` is the single
  environment carried by DG-ENV's C0. -/
def SigTyClosed (senv : StructEnv) : Prop :=
  ∀ (c : Lean.Name) (kinds : List MixedGateBinder) (ty : Lean.Expr),
    senv.instS c = some (kinds, ty) → BvarLt 0 ty = true

end Tools.Assume.EnvSigTy
