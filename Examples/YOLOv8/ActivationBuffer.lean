/-
  Activation Double Buffer -- Signal DSL

  Ping-pong buffer using two memory banks. While one bank is being
  written (current layer output), the other is read (next layer input).
  The `bufferSel` signal swaps banks between layers.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.YOLOv8.Types

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Sparkle.Examples.YOLOv8.ActivationBuffer

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Ping-pong double buffer for activation data.

    Two memory banks, selected by `bufferSel`:
    - bufferSel=false: write to bank0, read from bank1
    - bufferSel=true:  write to bank1, read from bank0

    Parameters:
      - writeAddr: write address (20-bit, supports up to 1M entries)
      - readAddr:  read address
      - writeData: INT8 data to write
      - writeEn:   write enable
      - bufferSel: which buffer to write to (toggle between layers)

    Returns: INT8 read data from the non-writing bank
-/
def activationDoubleBuffer {dom : DomainConfig}
    (writeAddr readAddr : Signal dom (BitVec 20))
    (writeData : Signal dom (BitVec 8))
    (writeEn bufferSel : Signal dom Bool)
    : Signal dom (BitVec 8) :=
  -- Write enables: only write to selected bank
  let writeEn0 := writeEn &&& ((fun b => !b) <$> bufferSel)
  let writeEn1 := writeEn &&& bufferSel

  -- Two memory banks
  let bank0 := Signal.memory writeAddr writeData writeEn0 readAddr
  let bank1 := Signal.memory writeAddr writeData writeEn1 readAddr

  -- Read from the non-writing bank
  Signal.mux bufferSel bank0 bank1

#synthesizeVerilog activationDoubleBuffer

end Sparkle.Examples.YOLOv8.ActivationBuffer
