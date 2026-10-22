import Tests.Compiler.SeqDeepGenInstTest
import Tools.ShippingSeqParentGenD2M
namespace Tests.Compiler.SeqDeepGenDiffTest
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Sparkle.Tests.Compiler.ShippingChildBoundaryTest
open Tests.Compiler.SeqDeepGenInstTest

/-- a second leaf, DIFFERENT from `acc` -/
@[hardware_module] def acc2 {dom : DomainConfig} (x : Signal dom (BitVec 8)) : AccOut dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    r <~ rs + x + x
    return ({ s := rs, odd := rs === (Signal.pure 3#8 : Signal dom (BitVec 8)) } : AccOut dom)

@[hardware_module] def wrap2 {dom : DomainConfig} (x y : Signal dom (BitVec 8)) : AccOut dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let a := acc2 x
    r <~ a.s + y
    return ({ s := rs, odd := a.odd } : AccOut dom)

def topdiff2 (en : Signal defaultDomain Bool) (v w : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let m := wrap v w
    let m2 := wrap2 w v
    r <~ Signal.mux (m.odd &&& m2.odd &&& en) (rs + v) rs
    return rs

#machine_endpoint topdiff2

set_option maxHeartbeats 0 in
#machine_design_svNR Tests.Compiler.SeqDeepGenDiffTest.topdiff2 2

set_option maxHeartbeats 0 in
#machine_seq_parent_endpoint Tests.Compiler.SeqDeepGenDiffTest.topdiff2

end Tests.Compiler.SeqDeepGenDiffTest
