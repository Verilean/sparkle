import Tools.ShippingGen5ReaderTrace
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.Assume.NormNodePh, exit 0) on the Lean content of 2b771482e278441fbc250ef0bd5e962a81358be6 (this header is comment-only). Assumption module (statements only; no theorems).

/-! # Assumption: N3-b `RawNodePh` / `NormNodePh`

**This file holds ONLY assumption statements** — `Prop` definitions that proofs take as hypotheses. They are not
`axiom`s and not theorems. A change here is a change of what is assumed and needs reviewer approval; proof files must
not redefine them.

Design: `scripts/gen5/RT_U2_FREEZE.md` §1 (reviewer-approved design, conditional). The statements are moved verbatim from
`Tools/ShippingGen5ReaderTraceDirect.lean` (same namespaces, names, types).

* What is assumed: `rawNode` and `machNormNode` preserve `NoPh ∧ BvarLt L` on an `app` of such arguments.
* Why not proved: both are `partial`/extern-backed in production; this investigation found no route; not a claim that it is underivable.
* Ledger: FG +2 (one each; see freeze §5; counted only when the U2 composition is accepted).
-/

namespace Tools.Assume.NormNodePh
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5ReaderTrace
def RawNodePh (senv : StructEnv) : Prop :=
  ∀ (L : Nat) (f a e' : Lean.Expr),
    NoPh f = true → NoPh a = true → BvarLt L f = true → BvarLt L a = true →
    Sparkle.Compiler.MachRawSurface.rawNode senv.prodMatch (.app f a) = some e' →
    NoPh e' = true ∧ BvarLt L e' = true
def NormNodePh (senv : StructEnv) : Prop :=
  ∀ (L : Nat) (f a : Lean.Expr),
    NoPh f = true → NoPh a = true → BvarLt L f = true → BvarLt L a = true →
    NoPh (machNormNode senv (.app f a)) = true ∧ BvarLt L (machNormNode senv (.app f a)) = true
end Tools.Assume.NormNodePh
