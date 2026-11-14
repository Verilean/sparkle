import Tests.Ved.U1MultiLoopRow
import Tests.IP.Crypto.Fp2MulHWTest

/-!
# `#ved_u1` on a real `Signal.loop` row, part 6 (Fp2 multiplier controller, 384-bit registers)

`synth_fp2MulC0` (registers 2/2/384/384/384/384/384/384/1 bits): the original `private` declaration is accepted
by `#ved_u1` with the strict audit, then `checkRows` compares the stored type with `==` and checks the axioms.
`U1MultiLoopAll` checks all rows together.

In the measured run (RSS guard 14 GiB) the elaboration of the generated proof finished; the kernel ran out of memory on the
first normalising step.  The loop script's `simp` calls (`ved_loop_simp`, `ved_loopw_simp`) now record their definitional
steps as proof terms (`-implicitDefEqProofs`, `Tools/VedU1Entry.lean`), so the kernel checks each step instead of
one comparison of the goal with its 110 000-node normal form.
-/

set_option exponentiation.threshold 4096

namespace Tests.Ved.U1MultiLoopFull6

open Lean Elab Command
open Tests.Ved.U1MultiLoopRow

#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Crypto.Fp2MulHWTest synth_fp2MulC0

def rows : List (Name × Name) :=
  [(`Tests.IP.Crypto.Fp2MulHWTest, `synth_fp2MulC0)]

/-- info: OK 1 rows: stored type = U1Stmt c m F, axioms within std3 -/
#guard_msgs in
run_cmd checkRows rows

example : rows.length = 1 := by decide

end Tests.Ved.U1MultiLoopFull6
