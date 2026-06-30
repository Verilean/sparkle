/-
  Synthesis check for the top-level Tang Nano 50K USB-Web
  server module.  Build-time only — `lake build` succeeds iff
  the synth elaborator can lower the entire pipeline to Verilog.
-/
import IP.Net.UsbWebServer

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.UsbWebServer

namespace Sparkle.Tests.IP.Net.UsbWebServerSynth

set_option maxHeartbeats 4000000 in
private def synth_usbWebServer
    (uartRxLine : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain Bool :=
  (usbWebServer uartRxLine bitDiv).uartTx

set_option maxHeartbeats 4000000 in
#synthesizeVerilog synth_usbWebServer

end Sparkle.Tests.IP.Net.UsbWebServerSynth
