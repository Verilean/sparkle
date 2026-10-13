import Sparkle

/-! # `#sim` file names by last component, file B of two

See `tagged_names_simdup_a.lean`. `DupB.tnzDup` adds 2 where `DupA.tnzDup`
adds 1; the file `.lake/build/gen/sim/tnzDup_jit.c` holds whichever was
elaborated last. WRITTEN, not run. -/

open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit

namespace DupB
def tnzDup (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 2#8 : Signal defaultDomain (BitVec 8))
end DupB

#sim DupB.tnzDup
