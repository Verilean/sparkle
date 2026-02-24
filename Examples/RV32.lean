/-
  Sparkle Examples -- RV32I Verified RISC-V Core

  A formally verified 4-stage pipelined RV32I core generated via Sparkle HDL.
  Harvard architecture with separate I-mem and D-mem interfaces for FPGA BRAMs.

  Pipeline: IF -> ID -> EX/MEM -> WB
  Hazard handling: Load-use stalling (no forwarding, for verification tractability)
-/

import Examples.RV32.Types
import Examples.RV32.CSR.Types
import Examples.RV32.Core
import Examples.RV32.Pipeline
import Examples.RV32.SoC
import Examples.RV32.Bus
import Examples.RV32.UART
import Examples.RV32.CLINT
import Examples.RV32.Trap
import Examples.RV32.CSR.File
import Examples.RV32.CSR.Supervisor
import Examples.RV32.MMU.Top
