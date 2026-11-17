import Lean

/-!
# Range facts for the `^^^` chains of the loop script (U1)

An `xor` of two in-range operands is taken mod `2 ^ w` by the module's semantics (`evalOp_xor_raw`), the declaration
(`BitVec.toNat_xor`) has none; for a chain of three or more operands the inner `(a ^^^ b) % 256` stays in the goal as
a different `omega` atom from `a ^^^ b`.  With these two facts as simp lemmas the closing `simp` discharges
`Nat.mod_eq_of_lt` for the inner xor and the atoms agree.  UNTRUSTED routing: the kernel checks what results.
-/

namespace Tools.VedU1LoopXor

theorem xor_lt_256 (a b : Nat) (ha : a < 256) (hb : b < 256) : a ^^^ b < 256 := by
  have := Nat.xor_lt_two_pow (n := 8) (x := a) (y := b) ha hb
  simpa using this

theorem xor_lt_65536 (a b : Nat) (ha : a < 65536) (hb : b < 65536) : a ^^^ b < 65536 := by
  have := Nat.xor_lt_two_pow (n := 16) (x := a) (y := b) ha hb
  simpa using this

theorem xor_mod_256 (a b : Nat) (ha : a < 256) (hb : b < 256) : (a ^^^ b) % 256 = a ^^^ b :=
  Nat.mod_eq_of_lt (xor_lt_256 a b ha hb)

theorem xor_mod_65536 (a b : Nat) (ha : a < 65536) (hb : b < 65536) : (a ^^^ b) % 65536 = a ^^^ b :=
  Nat.mod_eq_of_lt (xor_lt_65536 a b ha hb)

theorem bv8_lt (x : BitVec 8) : x.toNat < 256 := by simpa using x.isLt

theorem bv16_lt (x : BitVec 16) : x.toNat < 65536 := by simpa using x.isLt

end Tools.VedU1LoopXor
