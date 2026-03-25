import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

-- Signal.circuit works for both synthesis AND simulation (single macro)
def counterCircuit : Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let count ← Signal.reg 0#8;
    count <~ count + 1#8;
    return count

def pipelineCircuit : Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let a ← Signal.reg (0#8 : BitVec 8);
    let b ← Signal.reg (0#8 : BitVec 8);
    a <~ a + 1#8;
    b <~ a;
    return b

def main : IO Unit := do
  -- Test 1: Counter
  let vals := counterCircuit.sample 10
  IO.println s!"counter: {vals}"
  assert! vals == [0#8, 1#8, 2#8, 3#8, 4#8, 5#8, 6#8, 7#8, 8#8, 9#8]
  IO.println "✓ counter correct"

  -- Test 2: Two-register pipeline (b follows a with 1-cycle delay)
  let pvals := pipelineCircuit.sample 6
  IO.println s!"pipeline: {pvals}"
  assert! pvals == [0#8, 0#8, 1#8, 2#8, 3#8, 4#8]
  IO.println "✓ pipeline correct"

  IO.println "\nAll Signal.circuit simulation tests passed!"
