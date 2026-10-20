import Tools.ShippingReaderFuelKleene

/-! # Rewriting a run of the fuel computations (shared pure lemmas)

BUILT on poc after 65eaccbb (run `r5`). Worker R5, branch `par/r-7`. No `sorry`, no axiom, no
`native_decide`. Imports only `Tools/ShippingReaderFuelDefs.lean` (through
`Tools/ShippingReaderFuelKleene.lean`), both BUILT on poc.

The three `run_*` lemmas that `Tools/ShippingReaderFuelR5.lean` uses, taken
verbatim (statement and proof) from the OldEq draft
(`a-fuel-pending/ShippingReaderFuelOldEq.lean`, section `Run`). Each is `rfl`:
`FM.pure`, `FM.bind` and `bindO` are structure literals whose `run` field is
the stated function.

NOTE for the OldEq repair: that draft declares the same three names in the
same namespace. If it is rebuilt importing this file, its copies of
`run_pure`, `run_bind`, `run_bindO` must be dropped (duplicate declarations
otherwise); its other `run_*` lemmas are not here. -/
namespace Tools.ShippingReaderFuel
open Lean
open Sparkle.Compiler.Elab

section Run
variable {κ : Type} {R : κ → Type} {α β : Type}

theorem run_pure (h : (c : κ) → Option (R c)) (a : α) : (FM.pure a : FM κ R α).run h = some a :=
  rfl

theorem run_bind (h : (c : κ) → Option (R c)) (x : FM κ R α) (f : α → FM κ R β) :
    (FM.bind x f).run h = (x.run h).bind fun a => (f a).run h := rfl

theorem run_bindO (h : (c : κ) → Option (R c)) (x : FM κ R (Option α))
    (f : α → FM κ R (Option β)) :
    (bindO x f).run h = (x.run h).bind fun o => (optK o f).run h := rfl

end Run

end Tools.ShippingReaderFuel
