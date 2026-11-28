/-
  `uartRxHW` framing error (CI group `ethernet`): for a frame whose stop bit
  is low (0x3C, stop low, then 40 idle cycles at bitDiv = 15) the byte is not
  reported, no phantom byte follows (the receiver waits for the line to return
  high before re-arming), and the next real frame 0xA5 is received intact.
-/
import Tests.IP.Net.UartHWJITTest

def main : IO Unit := Sparkle.Tests.IP.Net.UartHWJITTest.mainFramingError
