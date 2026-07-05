import Sparkle
open Sparkle.Core.Domain Sparkle.Core.Signal
set_option maxRecDepth 100000

def blinkyTop (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 25) :=
  circuit do
    let cnt ← Signal.reg (0#25)
    let inc := ((· + ·) <$> (cnt : Signal defaultDomain (BitVec 25)) <*> (Signal.pure 1#25))
    cnt <~ Signal.mux en inc (cnt : Signal defaultDomain (BitVec 25))
    return (cnt : Signal defaultDomain (BitVec 25))

#writeVerilogDesign blinkyTop "fpga/tangNano20k/blinky/blinky.v"
