-- Submodule-memory isolation: the regFile (a @[hardware_module] wrapping a
-- 256-bit BRAM) instantiated under a thin top.  If this fails while the
-- top-level mem256Top passes, the bug is JIT submodule-state handling.
--   lake env lean fpga/tangNano20k/build/GenRfTest.lean
import Sparkle
import IP.Crypto.EcdsaSignSmall
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignSmall

abbrev D := defaultDomain
set_option maxRecDepth 100000

def regFileTop
    (wa : Signal D (BitVec 6)) (wd : Signal D (BitVec 256))
    (we : Signal D Bool) (ra : Signal D (BitVec 6)) : Signal D (BitVec 256) :=
  (regFile wa wd we ra).rdata

#sim regFileTop
