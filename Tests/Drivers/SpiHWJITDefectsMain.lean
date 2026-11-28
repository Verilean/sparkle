/-
  NOT in CI (known design defects of `spiMasterHW`, reported to the coordinator).

  (1) MOSI is one bit early: the byte is loaded into the shift register and the
      first shift happens on the same tick that raises SCLK, so the 8 values on
      MOSI at the 8 leading edges are bits 6..0 of the byte followed by 0 (0xA5
      goes out as 0x4A).  Expected: the 8 leading edges see the byte MSB first.
      Suspected source: IP/Bus/SPIHW.lean `shiftMosi` fires on the first
      active tick (bc even) together with the SCLK toggle.
  (2) `start` is only accepted on a divider-tick cycle (dc == 0).  A 1-cycle
      pulse at any other phase (bitDiv = 3, start at cycle 13; cs low for the rest of the run, 418 cycles) pulls `cs` low
      (csGoLow does not wait for the tick), reloads the divider and leaves the
      FSM idle: cs stays low, SCLK never moves, `done` never fires.  A start
      held for 2+ cycles starves the divider (reloaded every cycle).
      Suspected source: IP/Bus/SPIHW.lean `csGoLow` / `dcAfterStart` / `tick`.
  Also: `_cpha` is unused, so modes 1 and 3 behave like 0 and 2.
-/
import Tests.IP.Bus.SpiHWJITTest

def main : IO Unit := Sparkle.Tests.IP.Bus.SpiHWJITTest.mainDefects
