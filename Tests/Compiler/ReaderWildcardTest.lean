import Tools.ShippingUnifiedSource

/-! # The wildcard gap of the gate recognisers (G3 evidence)

Logs — it does not assert — whether the compiler's Bool-valued recognisers
accept expressions that are NOT quotations: a `Signal.pure` at universe
level 1 over an arbitrary "domain" expression, and a `Signal.mux` whose
sub-nodes mention different domain expressions. Expected from reading the
definitions (`unifiedGateBoolBody`, arms 2 and 5): accepted, and different
from every `literalE dom true`. See docs/parallel/G3-reader.md §3.

Compiled evaluation only; no theorem is stated here. -/
namespace Tests.Compiler.ReaderWildcardTest
open Sparkle.Compiler.Elab

/-- An arbitrary expression in the domain position (not a domain). -/
def junk (n : Nat) : Lean.Expr := .lit (.natVal n)

/-- `Signal.pure.{1} X Bool Bool.true`: wrong level, arbitrary `X`. -/
def wildPure (x : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.pure [.succ .zero]) x)
    (.const ``Bool [])) (.const ``Bool.true [])

/-- The quotation of `Signal.pure true` at domain `x`. -/
def quoted (x : Lean.Expr) : Lean.Expr :=
  Tools.ShippingBoolLiteralSoundness.literalE x true

/-- A Bool `mux` whose four nodes mention four different domain positions. -/
def wildMux : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.mux [.zero]) (junk 0))
    (.const ``Bool [])) (quoted (junk 1))) (quoted (junk 2))) (quoted (junk 3))

#eval do
  IO.println s!"WILDCARD pure level-1: unifiedGateBoolBody = {unifiedGateBoolBody #[] (wildPure (junk 7))}"
  IO.println s!"WILDCARD pure level-1: unifiedGateRoot = {unifiedGateRoot #[] (wildPure (junk 7))}"
  IO.println s!"WILDCARD pure level-1: mixedGateBoolBody = {mixedGateBoolBody #[] (wildPure (junk 7))}"
  IO.println s!"WILDCARD pure level-1: equals its quotation = {wildPure (junk 7) == quoted (junk 7)}"
  IO.println s!"WILDCARD mux mixed domains: unifiedGateBoolBody = {unifiedGateBoolBody #[] wildMux}"
  IO.println s!"WILDCARD mux mixed domains: unifiedGateRoot = {unifiedGateRoot #[] wildMux}"
  IO.println s!"CONTROL quoted literal: unifiedGateBoolBody = {unifiedGateBoolBody #[] (quoted (junk 7))}"

end Tests.Compiler.ReaderWildcardTest
