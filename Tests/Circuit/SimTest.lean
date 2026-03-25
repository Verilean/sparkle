import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

def mkCounter : IO (Signal defaultDomain (BitVec 8)) :=
  Signal.circuitIO do
    let count ← Signal.reg 0#8;
    count <~ count + 1#8;
    return count

def mkPipeline : IO (Signal defaultDomain (BitVec 8)) :=
  Signal.circuitIO do
    let a ← Signal.reg (0#8 : BitVec 8);
    let b ← Signal.reg (0#8 : BitVec 8);
    a <~ a + 1#8;
    b <~ a;
    return b

def main : IO Unit := do
  let count ← mkCounter
  let vals := count.sample 10
  IO.println s!"counter: {vals}"
  -- Expected: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  assert! vals == [0#8, 1#8, 2#8, 3#8, 4#8, 5#8, 6#8, 7#8, 8#8, 9#8]
  IO.println "✓ counter correct"

  let pipe ← mkPipeline
  let pvals := pipe.sample 6
  IO.println s!"pipeline: {pvals}"
  -- b follows a with 1-cycle delay: a=[0,1,2,3,4,5], b=[0,0,1,2,3,4]
  assert! pvals == [0#8, 0#8, 1#8, 2#8, 3#8, 4#8]
  IO.println "✓ pipeline correct"

  IO.println "All Signal.circuitIO simulation tests passed!"
