-- Minimal JIT memory isolation: top-level memory, narrow (8-bit) and
-- wide (256-bit) data.  Pinpoints whether the JIT memory failure is
-- generic, wide-only, or hierarchy-only.
--   lake env lean fpga/tangNano20k/build/GenMemTest.lean
import Sparkle
open Sparkle.Core.Domain Sparkle.Core.Signal

abbrev D := defaultDomain

set_option maxRecDepth 100000

/-- Top-level 8-bit memory (registered read, 1-cycle latency). -/
def mem8Top
    (wa : Signal D (BitVec 6)) (wd : Signal D (BitVec 8))
    (we : Signal D Bool) (ra : Signal D (BitVec 6)) : Signal D (BitVec 8) :=
  Signal.memory wa wd we ra

/-- Top-level 256-bit memory. -/
def mem256Top
    (wa : Signal D (BitVec 6)) (wd : Signal D (BitVec 256))
    (we : Signal D Bool) (ra : Signal D (BitVec 6)) : Signal D (BitVec 256) :=
  Signal.memory wa wd we ra

#sim mem8Top
#sim mem256Top
