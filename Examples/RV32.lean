/-
  Sparkle Examples -- RV32I Verified RISC-V Core

  A formally verified 4-stage pipelined RV32I core generated via Sparkle HDL.
  Harvard architecture with separate I-mem and D-mem interfaces for FPGA BRAMs.

  Pipeline: IF -> ID -> EX/MEM -> WB
  Hazard handling: Load-use stalling (no forwarding, for verification tractability)
-/

import Examples.RV32.Types
import Examples.RV32.Decode
import Examples.RV32.Core
