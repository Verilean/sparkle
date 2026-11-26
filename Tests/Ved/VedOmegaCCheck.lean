import Tools.VedU1ScriptSeqGen

/-!
# Regression check: `ved_omega_c` (interval-bound prover `vedUb` + cache) and `ved_pack_simp_c`

The register-block closing stage of the U1 loop script reads packed words `a * 2^k + b` (20 registers,
4359 bits in the widest row).  `ved_pack_simp_c` is `ved_pack_simp` whose side conditions
(`0 < m`, `T < N`) are discharged by `ved_omega_c`: first the interval prover `vedUb` (a bound for a
term built from `+ * % /`, `if`, literals and atoms with a hypothesis `x < N` / `x ≤ N`; the proof is
built from `Nat.add_le_add`, `Nat.mul_le_mul`, `Nat.mod_le`, ... and `decide` numerals), then `omega`
with a cache of found proofs and failures.  The examples are small; the packing factors are
`2 ^ 4353` / `2 ^ 4097` (`Nat.reducePow` does not evaluate them) and the kernel checks every proof.
-/

namespace Tests.Ved.VedOmegaCCheck

-- the recursion bound the generated scripts run under (`ved.u1.proofRecDepth`, default 20000)
set_option maxRecDepth 20000

/-- the range side condition of a packed word, from the field bounds only (interval prover) -/
theorem pack_lt (x y : Nat) (hx : x < 2 ^ 256) (hy : y < 2 ^ 4097) :
    x * 2 ^ 4097 + y < 2 ^ 4353 := by
  ved_omega_c

/-- an `if` and a `%` inside the bounded term -/
theorem pack_lt_ite (c : Prop) [Decidable c] (x y : Nat) (hx : x < 2 ^ 256) (hy : y < 2 ^ 4097) :
    (if c then x else 0) * 2 ^ 4097 + y % 2 ^ 4097 < 2 ^ 4353 := by
  ved_omega_c

-- a bound that is exceeded is refused at once (no `omega` run)
/-- error: ved_omega_c: bound exceeds -/
#guard_msgs in
theorem pack_too_wide (x y : Nat) (hx : x < 2 ^ 300) (hy : y < 2 ^ 4097) :
    x * 2 ^ 4097 + y < 2 ^ 4353 := by
  ved_omega_c

/-- `ved_pack_simp_c`: read a field of a packed word back (`div_pack`, `mod_pack`, side conditions by `ved_omega_c`) -/
theorem pack_div (x y : Nat) (hy : y < 2 ^ 4353) : (x * 2 ^ 4353 + y) / 2 ^ 4353 = x := by
  ved_pack_simp_c

theorem pack_mod (x y : Nat) (hy : y < 2 ^ 4353) : (x * 2 ^ 4353 + y) % 2 ^ 4353 = y := by
  ved_pack_simp_c

/-- the constant-1 field of a register above the others (`ved_div_self_add`) -/
theorem pack_one (b : Nat) (hb : b < 2 ^ 4353) : (2 ^ 4353 + b) / 2 ^ 4353 = 1 := by
  ved_pack_simp_c

/-- info: 'Tests.Ved.VedOmegaCCheck.pack_lt' does not depend on any axioms -/
#guard_msgs in #print axioms pack_lt

/-- info: 'Tests.Ved.VedOmegaCCheck.pack_lt_ite' depends on axioms: [propext] -/
#guard_msgs in #print axioms pack_lt_ite

/-- info: 'Tests.Ved.VedOmegaCCheck.pack_div' depends on axioms: [propext] -/
#guard_msgs in #print axioms pack_div

/-- info: 'Tests.Ved.VedOmegaCCheck.pack_mod' depends on axioms: [propext] -/
#guard_msgs in #print axioms pack_mod

/-- info: 'Tests.Ved.VedOmegaCCheck.pack_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms pack_one


end Tests.Ved.VedOmegaCCheck
