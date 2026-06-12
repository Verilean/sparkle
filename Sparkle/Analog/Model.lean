import Sparkle.Analog.IR.Expr

/-!
# Polymorphic device models

Device constitutive laws written **once**, polymorphic in the numeric carrier, so
the very same definition is what the simulator runs and what the proofs reason
about — no parallel "spec" copy that could drift from the implementation.

A model needs ordinary arithmetic plus the transcendental functions. Arithmetic
and numerals already exist for every carrier we care about (`Float`, `AExpr`, and
— in the proofs library — `ℝ`); the only extra piece is `HasExp`, a minimal
transcendental interface with an instance per carrier.

The simulator instantiates these at `AExpr` (to build the branch equation, which
the solver then evaluates at `Float`); the `Sparkle.Analog.Proofs` library
instantiates the same definitions at `ℝ` to prove their properties.
-/

namespace Sparkle.Analog

/-- The transcendental functions a device law may use, abstracted over the
numeric carrier. Instances exist for `Float` and `AExpr` here; the proofs library
adds the `ℝ` instance. -/
class HasExp (α : Type) where
  exp : α → α

instance : HasExp Float := ⟨Float.exp⟩
instance : HasExp AExpr := ⟨AExpr.exp⟩

/-- Shockley diode current as a function of branch voltage `v`, with saturation
current `Is` and thermal voltage `Vt` — written once, polymorphic in `α`. The
device constructor instantiates this at `AExpr`; the proofs instantiate it at `ℝ`
and show it is monotone and passive. -/
def diodeCurrent {α : Type} [Mul α] [Sub α] [Div α] [OfNat α 1] [HasExp α]
    (Is Vt v : α) : α :=
  Is * (HasExp.exp (v / Vt) - 1)

end Sparkle.Analog
