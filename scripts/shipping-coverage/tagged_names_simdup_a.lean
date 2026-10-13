import Sparkle

/-! # `#sim` file names by last component, file A of two

Elaborated by `scripts/shipping-coverage/tagged_names_sim.sh` BEFORE
`tagged_names_simdup_b.lean`, each in its own Lean process (two files that
do not import each other). `DupA.tnzDup` and `DupB.tnzDup` are two
declarations with two module names (`DupA_tnzDup`, `DupB_tnzDup`); `#sim`
writes both to `.lake/build/gen/sim/tnzDup_jit.c` and `tnzDup.sv`.
WRITTEN, not run. -/

open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit

namespace DupA
def tnzDup (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))
end DupA

#sim DupA.tnzDup
