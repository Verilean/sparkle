import Sparkle
import Sparkle.Compiler.Elab
import Tests.SignalLoopTest
import IP.Arbiter.RoundRobin
import IP.Bus.PCIeHFT
-- FG circuit pilot S1q: output comparison module.  Its build log (the IR text of `#synthesize` and the SV text of `#synthesizeVerilog`) is compared before / after the profile-free entry (docs/FG-CIRCUIT-PILOT.md §21.6).  No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.
namespace Tests.Gen5.FGCircuitPilotCompare15
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Tests.SignalLoopTest

def cmpEnable (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  (counterEnableLoop en)

def cmpArbiter (reqA reqB : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 2) :=
  Sparkle.IP.Arbiter.RoundRobin.arbiterSignal reqA reqB

def cmpHftOutByte
    (rxByte : Signal defaultDomain (BitVec 8))
    (rxValid sopTlp : Signal defaultDomain Bool)
    (dataDword : Signal defaultDomain (BitVec 32))
    (cplId : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain (BitVec 8) :=
  (Sparkle.IP.Bus.PCIeHFT.hftPcieLoop rxByte rxValid sopTlp dataDword cplId).outByte

end Tests.Gen5.FGCircuitPilotCompare15

#synthesize Sparkle.Tests.SignalLoopTest.counterLoop
#synthesize Sparkle.Tests.SignalLoopTest.shift4Loop
#synthesize Tests.Gen5.FGCircuitPilotCompare15.cmpEnable
#synthesize Tests.Gen5.FGCircuitPilotCompare15.cmpArbiter
#synthesize Tests.Gen5.FGCircuitPilotCompare15.cmpHftOutByte
#synthesizeVerilog Sparkle.Tests.SignalLoopTest.counterLoop
#synthesizeVerilog Sparkle.Tests.SignalLoopTest.shift4Loop
#synthesizeVerilog Tests.Gen5.FGCircuitPilotCompare15.cmpEnable
#synthesizeVerilog Tests.Gen5.FGCircuitPilotCompare15.cmpArbiter
#synthesizeVerilog Tests.Gen5.FGCircuitPilotCompare15.cmpHftOutByte
