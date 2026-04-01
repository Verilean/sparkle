/-
  Sparkle Examples -- RV32I Verified RISC-V Core

  A formally verified 4-stage pipelined RV32I core generated via Sparkle HDL.
  Harvard architecture with separate I-mem and D-mem interfaces for FPGA BRAMs.

  Pipeline: IF -> ID -> EX/MEM -> WB
  Hazard handling: Load-use stalling (no forwarding, for verification tractability)
-/

import IP.RV32.Types
import IP.RV32.CSR.Types
import IP.RV32.Core
import IP.RV32.Pipeline
import IP.RV32.SoC
import IP.RV32.Bus
import IP.RV32.UART
import IP.RV32.CLINT
import IP.RV32.Trap
import IP.RV32.CSR.File
import IP.RV32.CSR.Supervisor
import IP.RV32.MMU.Top
