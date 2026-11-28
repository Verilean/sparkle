/-
  NOT in CI (known design defect, reported to the coordinator).

  `uartRxHW`: for a frame whose stop bit is low (0x3C, stop low, then 40 idle
  cycles at bitDiv = 15) the byte is correctly not reported, but the receiver
  returns to idle in the middle of the low stop slot, sees the still-low line
  as a new start bit, samples the following idle-high line as 8 data bits and
  a high stop, and pulses `rxValid` with a phantom byte about 10 bit times
  after the bad frame (observed 0x2B at cycle 536 for a frame starting at
  230).  The following real frame 0xA5 (start at 430) is then reported as 0xFF
  (cycle 695), because the phantom receive is still running when it starts.
  Expected: no `rxValid` for the bad frame and none after it until the next
  real frame.  Suspected source: IP/Net/UART.lean, `stateNext`/`startEdge`
  (idle detection does not require the line to have been high since the stop
  slot).
-/
import Tests.IP.Net.UartHWJITTest

def main : IO Unit := Sparkle.Tests.IP.Net.UartHWJITTest.mainFramingError
