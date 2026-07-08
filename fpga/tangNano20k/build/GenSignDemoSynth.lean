-- Emit the UART signing demo (baked key) to hierarchical Verilog for flashing.
--   lake env lean fpga/tangNano20k/build/GenSignDemoSynth.lean
import Sparkle
import IP.Crypto.EcdsaSignSmallDemo
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignSmallDemo
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

-- Baked demo private key d = 12345 (a valid nonzero scalar < n; matches the
-- JIT-verified demo).  Replace with a real key for production.
def signDemoTop
    (uartRx : Signal defaultDomain Bool) (bitDiv : Signal defaultDomain (BitVec 16)) :
    DemoOut defaultDomain :=
  signSmallDemo (BitVec.ofNat 256 12345) uartRx bitDiv

#writeVerilogDesign signDemoTop "fpga/tangNano20k/build/sign_demo.v"
