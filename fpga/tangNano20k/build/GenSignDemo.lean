import Sparkle
import IP.Crypto.EcdsaSignSmallDemo
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignSmallDemo
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
-- Baked test key d = 12345 (a valid nonzero scalar < n).
def demoTop (uartRx : Signal defaultDomain Bool) (bitDiv : Signal defaultDomain (BitVec 16)) : DemoOut defaultDomain :=
  signSmallDemo (BitVec.ofNat 256 12345) uartRx bitDiv
#sim demoTop
