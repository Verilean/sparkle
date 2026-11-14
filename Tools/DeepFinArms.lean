/-
  `finTailArm` — the tail arm of a generated `match` on a `Fin n` literal index.

  The generators of `#verify_elab_deep` emit `match i with | ⟨0, _⟩ => … | ⟨n-1, _⟩ => …`
  with NO catch-all (a catch-all `| _ => …` defeats the `simp` proofs that discharge
  "n is none of the slots").  The match compiler closes the remaining
  `Fin.mk (succ^k _) _` case by `contradiction` against the bound, whose search
  has a fixed fuel of 16: with more than ~16 arms it reports "Missing cases".

  The tail arm `| ⟨k + n, h⟩ => absurd h (by simp)` closes that case explicitly.  It is
  appended only when there are more than 15 arms (smaller matches keep their exact
  generated shape) and leaves the literal arms untouched, so `f ⟨i, _⟩` still
  iota-reduces for every real slot.
-/
import Lean
open Lean Elab

namespace Tools.DeepElab

/-- Append the tail arm to `arms` (the `n` literal arms `⟨0,_⟩ … ⟨n-1,_⟩`) when `n > 15`. -/
def finTailArm {m : Type → Type} [Monad m] [MonadQuotation m]
    (arms : Array (TSyntax ``Lean.Parser.Term.matchAlt)) (n : Nat) :
    m (Array (TSyntax ``Lean.Parser.Term.matchAlt)) := do
  if n ≤ 15 then return arms
  let tail ← `(Lean.Parser.Term.matchAltExpr|
    | ⟨k + $(quote n), h⟩ => absurd h (by simp))
  return arms.push tail

end Tools.DeepElab
