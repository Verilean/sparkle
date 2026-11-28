/-
  NOT in CI (known design defect of `slipDeframerHW`, reported to the
  coordinator).

  A frame whose first payload byte is END (0xC0) or ESC (0xDB) is sent by the
  framer as ESC + 0xDC / 0xDD (correct, checked in slip-hw-jit-test), but the
  deframer, in state idle, treats ANY non-END byte as data: the ESC (0xDB) is
  emitted as a payload byte and the following 0xDC / 0xDD is then taken as data
  as well.  Input wire `C0 DB DC 01 C0` (payload [C0, 01]) decodes to
  [DB, DC, 01] (3 bytes, outValid at the ESC cycle + 1); `C0 DB DD 02 C0`
  (payload [DB, 02]) decodes to [DB, DD, 02].  Expected: ESC in idle starts an
  escape, nothing is emitted for it.  `frameDone` is correct.
  Suspected source: IP/Net/SLIP.lean slipDeframerHW, `evIdleData` (idle + any
  non-END byte) should send ESC to the escape state, like `evBodyEsc`.  The
  same bug breaks framer → deframer loopback of every payload that starts with
  0xC0 or 0xDB.
-/
import Tests.IP.Net.SlipHWJITTest

def main : IO Unit := Sparkle.Tests.IP.Net.SlipHWJITTest.mainDefects
