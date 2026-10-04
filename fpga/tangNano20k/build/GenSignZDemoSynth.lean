-- k-on-chip UART signer (no on-chip Keccak) → hierarchical Verilog for the 20k.
--   lake env lean fpga/tangNano20k/build/GenSignZDemoSynth.lean
import Sparkle
import IP.Crypto.EcdsaSignMsgDemo
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignMsgDemo
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def signZDemoTop
    (uartRx : Signal defaultDomain Bool) (bitDiv : Signal defaultDomain (BitVec 16)) :
    Sparkle.IP.Crypto.EcdsaSignSmallDemo.DemoOut defaultDomain :=
  signZDemo uartRx bitDiv
#writeVerilogDesign signZDemoTop "fpga/tangNano20k/build/sign_z_demo.v"
