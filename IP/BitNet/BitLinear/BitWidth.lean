/-
  BitNet BitLinear BitWidth — Pure helpers

  Bit-width tracking helpers retained from CircuitM migration.
  SizedExpr removed (CircuitM-specific).
-/

namespace Sparkle.IP.BitNet.BitLinear

/-- The bit-width rule for signed addition: max(n,m) + 1 -/
def addBitWidth (a b : Nat) : Nat := max a b + 1

end Sparkle.IP.BitNet.BitLinear
