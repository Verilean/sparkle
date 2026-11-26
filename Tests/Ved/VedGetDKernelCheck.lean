import Tools.VedU1ScriptSeqGen

/-!
# Regression check: `Option.getD (some X) 0 =?= X` in the kernel (`vedGetD_some`)

`simp` applies the rfl theorem `Option.getD_some` WITHOUT a proof term, so the kernel itself must decide
`Option.getD (some X) 0 =?= X`. Observed (Lean 4.32.1, this expression path): for `X` an `ite` on symbolic
`a * 2 ^ k` the kernel evaluates the condition by unary recursion on the literal `2 ^ k` (k = 18: seconds
and GBs; k = 4359, the width of a real row: out of memory). `ved_seq_simp` therefore uses the non-rfl
restatement `Tools.VedU1ScriptSeq.vedGetD_some` (explicit proof term) with `-Option.getD_some`.

Records, kept apart, all under the SAME fixed budget (`maxHeartbeats 5000`; the kernel honours it, so the
outcome is deterministic, not a wall-clock threshold) and with the kernel run synchronously
(`Elab.async false`: with the default async `addDecl` the kernel cost would go unobserved):
* POSITIVE: the `ved_seq_simp` step closes the tiny goal at k = 4359 (and a small k), axioms std3-only;
* CONTROL (old route): the default-set `simp [e]` (uses `Option.getD_some`) on the SAME goal at the small
  k = 18 is refused by the kernel with a deterministic timeout under that budget. The old route at
  k = 4359 is deliberately NOT run here (it exhausts memory; see the report measurement).
-/

namespace Tests.Ved.VedGetDKernelCheck

set_option Elab.async false
set_option maxHeartbeats 5000

/-! ## Positive: `ved_seq_simp` (with `vedGetD_some`) at the width of a real row -/

theorem new_big (o : Option Nat) (a : Nat)
    (e : o = some (if a * 2 ^ 4359 = 1 then 1 else 0)) :
    o.getD 0 % 4 = (if a * 2 ^ 4359 = 1 then 1 else 0) % 4 := by
  ved_seq_simp [e]

/-- info: 'Tests.Ved.VedGetDKernelCheck.new_big' depends on axioms: [propext] -/
#guard_msgs in #print axioms new_big

theorem new_small (o : Option Nat) (a : Nat)
    (e : o = some (if a * 2 ^ 18 = 1 then 1 else 0)) :
    o.getD 0 % 4 = (if a * 2 ^ 18 = 1 then 1 else 0) % 4 := by
  ved_seq_simp [e]

/-- info: 'Tests.Ved.VedGetDKernelCheck.new_small' depends on axioms: [propext] -/
#guard_msgs in #print axioms new_small

/-! ## Control: the old route (`Option.getD_some` as a proof-free rfl step), small k, same budget -/

/-- error: (kernel) deterministic timeout -/
#guard_msgs in
theorem old_small (o : Option Nat) (a : Nat)
    (e : o = some (if a * 2 ^ 18 = 1 then 1 else 0)) :
    o.getD 0 % 4 = (if a * 2 ^ 18 = 1 then 1 else 0) % 4 := by
  simp [e]

end Tests.Ved.VedGetDKernelCheck
