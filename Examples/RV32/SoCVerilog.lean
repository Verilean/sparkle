/-
  RV32I SoC Verilog Synthesis

  Generates synthesizable SystemVerilog from the Signal DSL SoC.
  Uses `Signal.memoryComboRead` for IMEM (combinational read, loaded via
  external write port during reset) and external DMEM write ports for
  binary preloading.

  The #synthesizeVerilog command lives here rather than in SoC.lean to
  prevent module-init stack overflow (closed Signal terms get evaluated
  eagerly when DomainConfig is erased).

  Output is a packed tuple:
    (pcReg : BitVec 32, uartTxValid : BitVec 32, prevStoreData : BitVec 32)
  A thin SV wrapper (rv32i_soc_wrapper.sv) unpacks these into named ports
  matching the Verilator testbench interface (tb_soc.cpp).
-/
import Sparkle
import Sparkle.Compiler.Elab
import Examples.RV32.SoC

set_option maxRecDepth 65536
set_option maxHeartbeats 64000000

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.RV32.SoC

namespace Sparkle.Examples.RV32.SoCVerilog

/-- RV32I SoC for Verilog synthesis.

    Inputs (external ports):
    - imem_wr_en/addr/data: IMEM write port for firmware loading during reset
    - dmem_wr_en/addr/data: DMEM write port for binary preloading during reset

    Output (packed 96-bit tuple):
    - pcReg [95:64]: current PC
    - uartTxValid [63:32]: UART TX valid (0 or 1, encoded as 32-bit)
    - prevStoreData [31:0]: UART TX data (store data from WB stage)

    IMEM uses memoryComboRead (same-cycle read) for instruction fetch.
    DMEM uses 4 byte-wide registered memories (Signal.memory) for data access,
    plus 4 byte-wide combo-read memories for DRAM instruction fetch. -/
def rv32iSoCSynth {dom : DomainConfig}
    (imem_wr_en : Signal dom Bool)
    (imem_wr_addr : Signal dom (BitVec 12))
    (imem_wr_data : Signal dom (BitVec 32))
    (dmem_wr_en : Signal dom Bool)
    (dmem_wr_addr : Signal dom (BitVec 23))
    (dmem_wr_data : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) :=
  -- Run the SoC loop
  let state := Signal.loop fun state =>
    -- Compute IMEM read data from state (fetchPC → address → memoryComboRead)
    let fetchPC := projN! state 122 1
    let imem_addr := fetchPC.map (BitVec.extractLsb' 2 12 ·)
    let imem_rdata := Signal.memoryComboRead imem_wr_addr imem_wr_data imem_wr_en imem_addr
    rv32iSoCBody imem_rdata dmem_wr_en dmem_wr_addr dmem_wr_data state
  -- Extract outputs from state tuple
  let pcReg         := projN! state 122 0
  let prevStoreAddr := projN! state 122 42
  let prevStoreData := projN! state 122 43
  let prevStoreEn   := projN! state 122 44
  -- Debug outputs: satp + PTW state
  let satpReg       := projN! state 122 77
  let ptwPteReg     := projN! state 122 83
  let ptwVaddrReg   := projN! state 122 82
  -- UART TX detection: store to 0x10xxxxxx (UART base), offset 0 (THR register)
  let addrHi := prevStoreAddr.map (BitVec.extractLsb' 24 8 ·)
  let isUartAddr := (· == ·) <$> addrHi <*> Signal.pure 0x10#8
  let addrLo3 := prevStoreAddr.map (BitVec.extractLsb' 0 3 ·)
  let isOffset0 := (· == ·) <$> addrLo3 <*> Signal.pure 0#3
  let uartTxValid := (· && ·) <$> prevStoreEn <*> ((· && ·) <$> isUartAddr <*> isOffset0)
  -- Encode Bool as 32-bit for uniform output packing
  let uartValidBV := Signal.mux uartTxValid (Signal.pure 1#32) (Signal.pure 0#32)
  -- Pack output: (pc, uart_valid, uart_data, satp, ptwPte, ptwVaddr)
  bundleAll! [pcReg, uartValidBV, prevStoreData, satpReg, ptwPteReg, ptwVaddrReg]

#writeDesign rv32iSoCSynth "verilator/generated_soc.sv" "verilator/generated_soc_cppsim.h" SoCOutput.wireNames

end Sparkle.Examples.RV32.SoCVerilog
