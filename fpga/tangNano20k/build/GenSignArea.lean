-- Area-check wrapper: reduce signCtrl's 785 port bits to a handful of pins so
-- nextpnr can place it and report real utilisation.  A 1-bit serial input
-- feeds a 256-bit shift register that drives the wide inputs (so none fold to
-- constants); the wide output is XOR-reduced to 1 bit.
--   lake env lean fpga/tangNano20k/build/GenSignArea.lean
import Sparkle
import IP.Crypto.EcdsaSignSmall
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignSmall
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def signAreaTop (din : Signal defaultDomain Bool) : Signal defaultDomain Bool :=
  circuit do
    let shR ← Signal.reg (0#256)
    let outR ← Signal.reg false
    let sh := (shR : Signal defaultDomain (BitVec 256))
    -- shift the serial bit into a 256-bit register (keeps wide inputs live).
    let dinBv := (Signal.mux din (Signal.pure 1#256 : Signal defaultDomain (BitVec 256)) (Signal.pure 0#256) : Signal defaultDomain (BitVec 256))
    let shNext := ((· ||| ·) <$> ((· <<< ·) <$> sh <*> (Signal.pure 1#256 : Signal defaultDomain (BitVec 256))) <*> dinBv : Signal defaultDomain (BitVec 256))
    shR <~ shNext
    let addr6 := ((BitVec.extractLsb' 0 6 ·) <$> sh : Signal defaultDomain (BitVec 6))
    let out := signCtrl din din addr6 sh sh addr6
    -- reduce probeVal to 1 bit (nonzero test) and OR in halted.
    let nz := ((fun v => !(v == 0#256)) <$> out.probeVal : Signal defaultDomain Bool)
    outR <~ ((· || ·) <$> nz <*> out.halted : Signal defaultDomain Bool)
    return (outR : Signal defaultDomain Bool)

#writeVerilogDesign signAreaTop "fpga/tangNano20k/build/sign_area.v"
