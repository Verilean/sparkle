/-
  Sparkle.Core.Lut — `kLut!` macro for constant-table mux.

  Background: Sparkle's IR elaborator can't synth through
  `Id.run do`, recursive `def`s (lifted via `Nat.brecOn`),
  or closures over `Nat`.  Writing a 64-way constant-table
  mux (e.g. SHA-256's K-table) ergonomically would
  naturally reach for one of those three patterns — and
  each one yields a "Cannot synthesise X: not inlinable"
  at synth time.

  This macro lets the user write
    `kLut! cnt [v0, v1, …, v_{N-1}]`
  and have it expand at TERM-elaboration time (i.e. BEFORE
  Sparkle synthesis runs) into a fully-unrolled nested
  `Signal.mux` chain
    `Signal.mux ((· == ·) <$> cnt <*> Signal.pure 0) v0
      (Signal.mux ((· == ·) <$> cnt <*> Signal.pure 1) v1
        … v_{N-1})`

  The user writes O(1) source; the elaborator gets O(N)
  expression that the IR elab already handles.

  The BitVec width of the counter values is inferred from
  `cnt`'s type via Lean's normal type-class resolution —
  no width annotation needed at the macro site.

  Usage in a hardware module:
    @[hardware_module] def kMux64 {dom : DomainConfig}
        (cnt : Signal dom (BitVec 7)) : Signal dom (BitVec 32) :=
      kLut! cnt [
        Signal.pure 0x428a2f98#32, Signal.pure 0x71374491#32, …
      ]
-/

import Sparkle.Core.Signal
import Lean
import Lean.Elab.Term

namespace Sparkle.Core

/-- `kLut! cnt [v0, v1, …, v_{N-1}]` expands to a
    fully-unrolled `Signal.mux` chain.  See module
    docstring for the rationale. -/
syntax (name := kLutMacro) "kLut!" term:max "[" term,* "]" : term

open Lean Elab Term

@[term_elab kLutMacro]
def elabKLut : TermElab := fun stx _ => do
  match stx with
  | `(kLut! $sel:term [$args,*]) => do
    let values := args.getElems
    let n := values.size
    if n = 0 then
      throwErrorAt sel "kLut! requires at least one value"
    -- Walk values back-to-front, wrapping each in a mux.
    let mut acc := values[n - 1]!
    let mut k : Nat := n - 1
    while k > 0 do
      k := k - 1
      let kStx : TSyntax `term := Syntax.mkNumLit (toString k)
      -- The selector `eqStx` uses the same Applicative form
      -- the IR elab understands.  We elaborate the BitVec
      -- width via Lean's standard num-literal coercion based
      -- on `cnt`'s type.
      let eqStx ← `((· == ·) <$> $sel <*> (Sparkle.Core.Signal.Signal.pure $kStx))
      let vk := values[k]!
      acc ← `(Sparkle.Core.Signal.Signal.mux $eqStx $vk $acc)
    Lean.Elab.Term.elabTerm acc none
  | _ => Lean.Elab.throwUnsupportedSyntax

end Sparkle.Core
