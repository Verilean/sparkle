import Tools.ShippingGen5ReaderTrace
set_option autoImplicit false
-- NOT BUILT yet (registration of Tools.Assume.EnvDeclValue; build SHA is recorded in a later comment-only commit). Assumption module (statements only; no theorems).

/-! # Assumption: N1-a `DeclValuePh`

**This file holds ONLY assumption statements** — `Prop` definitions that proofs take as hypotheses. They are not
`axiom`s and not theorems. A change here is a change of what is assumed and needs reviewer approval; proof files must
not redefine them.

Design: `scripts/gen5/RT_U2_FREEZE.md` §1 (reviewer-approved design, conditional). The statements are moved verbatim from
`Tools/ShippingGen5ReaderTraceDirect.lean` (same namespaces, names, types).

* What is assumed: every `defnInfo` value of `env` has no placeholder (`NoPh`) and is closed (`BvarLt 0`).
* Why not proved: `Lean.Environment` is not modelled in this development; `NoPh` is a Sparkle-internal notion, not a kernel check.
  This investigation found no supplier or route for it; that is not a claim that it is underivable, nor that it holds for accepted sources.
* Ledger: FG +1 (see freeze §5; counted only when the U2 composition is accepted).
-/

namespace Tools.Assume.EnvDeclValue
open Lean Tools.ShippingGen5ReaderTrace
def DeclValuePh (env : Lean.Environment) : Prop :=
  ∀ (n : Lean.Name) (d : Lean.DefinitionVal),
    env.find? n = some (.defnInfo d) → NoPh d.value = true ∧ BvarLt 0 d.value = true
end Tools.Assume.EnvDeclValue
