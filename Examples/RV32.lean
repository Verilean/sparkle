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
-- CircuitM modules
import Examples.RV32.Bus
import Examples.RV32.UART
import Examples.RV32.CLINT
import Examples.RV32.Trap
import Examples.RV32.SoC
import Examples.RV32.CSR.Types
import Examples.RV32.CSR.File
import Examples.RV32.CSR.Supervisor
import Examples.RV32.MMU.Top
import Examples.RV32.MMU.TLB
import Examples.RV32.MMU.PageWalker
-- Signal DSL modules
import Examples.RV32.CoreSignal
import Examples.RV32.PipelineSignal
import Examples.RV32.SoCSignal
import Examples.RV32.BusSignal
import Examples.RV32.UARTSignal
import Examples.RV32.CLINTSignal
import Examples.RV32.TrapSignal
import Examples.RV32.CSR.FileSignal
import Examples.RV32.CSR.SupervisorSignal
import Examples.RV32.MMU.TopSignal
