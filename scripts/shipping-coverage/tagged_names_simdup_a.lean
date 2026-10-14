import Sparkle

/-! # `#sim` file names of two declarations with one last component, file A of two

Elaborated by `scripts/shipping-coverage/tagged_names_sim.sh` BEFORE
`tagged_names_simdup_b.lean`, each in its own Lean process (two files that
do not import each other), and once more afterwards (row `simrerun`).
`DupA.tnzDup` and `DupB.tnzDup` are two declarations with two module names
(`DupA_tnzDup`, `DupB_tnzDup`). Before the J5 fix `#sim` wrote both to
`.lake/build/gen/sim/tnzDup_jit.c` and `tnzDup.sv` (measured: a silent
overwrite). Since the fix (`Sparkle/Compiler/SimNames.lean`) the stems are the
module names: `DupA_tnzDup_jit.c`, `DupB_tnzDup_jit.c`.
WRITTEN, not run. -/

open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit

namespace DupA
def tnzDup (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))
end DupA

#sim DupA.tnzDup
