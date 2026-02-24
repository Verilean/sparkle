/-
  Bus Address Decoder

  Routes memory requests to the appropriate peripheral based on address.

  Address Map:
    0x00000000 - 0x0001FFFF : DRAM (128KB, via MMU when enabled)
    0x02000000 - 0x0200FFFF : CLINT (Core Local Interruptor)
    0x10000000 - 0x100000FF : UART (optional, TX-only console)
    0x80000000 - 0x8001FFFF : DRAM boot region (identity-mapped)
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.RV32.CSR.Types

set_option maxRecDepth 4096

namespace Sparkle.Examples.RV32.Bus

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open CircuitM

/-- Device select enumeration (encoded as 3-bit) -/
def devDRAM  : Nat := 0
def devCLINT : Nat := 1
def devUART  : Nat := 2
def devBOOT  : Nat := 3
def devNONE  : Nat := 7

/-- Generate the bus address decoder.

    Inputs:
      clk, rst
      addr[31:0]          - Full 32-bit address from core
      wdata[31:0]         - Write data from core
      we                  - Write enable from core
      re                  - Read enable from core

      -- Device responses
      dram_rdata[31:0]    - Read data from DRAM
      clint_rdata[31:0]   - Read data from CLINT
      uart_rdata[31:0]    - Read data from UART
      boot_rdata[31:0]    - Read data from boot ROM/DRAM

    Outputs:
      -- Device selects
      dram_sel            - DRAM selected
      clint_sel           - CLINT selected
      uart_sel            - UART selected
      boot_sel            - Boot region selected

      -- Forwarded signals per device
      dram_addr[31:0]     - Address to DRAM
      clint_addr[15:0]    - Address offset to CLINT
      uart_addr[7:0]      - Address offset to UART
      boot_addr[31:0]     - Address to boot DRAM

      -- Forwarded control
      dev_wdata[31:0]     - Write data (forwarded)
      dev_we              - Write enable (forwarded, qualified by device select)
      dev_re              - Read enable (forwarded, qualified by device select)

      -- Muxed read data back to core
      rdata[31:0]         - Read data returned to core
-/
def generateBus : CircuitM Unit := do
  addInput "clk" .bit
  addInput "rst" .bit
  addInput "addr" (.bitVector 32)
  addInput "wdata" (.bitVector 32)
  addInput "we" .bit
  addInput "re" .bit

  addInput "dram_rdata" (.bitVector 32)
  addInput "clint_rdata" (.bitVector 32)
  addInput "uart_rdata" (.bitVector 32)
  addInput "boot_rdata" (.bitVector 32)

  addOutput "dram_sel" .bit
  addOutput "clint_sel" .bit
  addOutput "uart_sel" .bit
  addOutput "boot_sel" .bit

  addOutput "dram_addr" (.bitVector 32)
  addOutput "clint_addr" (.bitVector 16)
  addOutput "uart_addr" (.bitVector 8)
  addOutput "boot_addr" (.bitVector 32)

  addOutput "dev_wdata" (.bitVector 32)
  addOutput "dev_we" .bit
  addOutput "dev_re" .bit
  addOutput "rdata" (.bitVector 32)

  let fullAddr := Expr.ref "addr"
  let we := Expr.ref "we"
  let re := Expr.ref "re"

  -- =========================================================================
  -- Address Decode
  -- =========================================================================

  -- CLINT: 0x02000000 - 0x0200FFFF (check addr[31:16] == 0x0200)
  let isCLINT ← makeWire "is_clint" .bit
  emitAssign isCLINT (.op .eq [.slice fullAddr 31 16, .const 0x0200 16])

  -- UART: 0x10000000 - 0x100000FF (check addr[31:8] == 0x100000)
  let isUART ← makeWire "is_uart" .bit
  emitAssign isUART (.op .eq [.slice fullAddr 31 8, .const 0x100000 24])

  -- Boot DRAM: 0x80000000 - 0x8001FFFF (check addr[31:17] == 0x4000)
  -- addr[31]=1, addr[30:17]=0 → addr[31:17] = 0b1_0000_0000_0000_0 = 0x4000
  let isBoot ← makeWire "is_boot" .bit
  emitAssign isBoot (.op .eq [.slice fullAddr 31 17, .const 0x4000 15])

  -- DRAM: 0x00000000 - 0x0001FFFF (default if not CLINT/UART/Boot)
  -- More precisely: addr[31:17] == 0
  let isDRAM ← makeWire "is_dram" .bit
  let notClint ← makeWire "not_clint" .bit
  emitAssign notClint (.op .not [.ref isCLINT])
  let notUart ← makeWire "not_uart" .bit
  emitAssign notUart (.op .not [.ref isUART])
  let notBoot ← makeWire "not_boot" .bit
  emitAssign notBoot (.op .not [.ref isBoot])
  emitAssign isDRAM (.op .and [.ref notClint, .op .and [.ref notUart, .ref notBoot]])

  -- Drive device select outputs
  emitAssign "dram_sel" (.ref isDRAM)
  emitAssign "clint_sel" (.ref isCLINT)
  emitAssign "uart_sel" (.ref isUART)
  emitAssign "boot_sel" (.ref isBoot)

  -- =========================================================================
  -- Address Extraction per Device
  -- =========================================================================

  -- DRAM: pass full address through
  emitAssign "dram_addr" fullAddr

  -- CLINT: extract offset [15:0]
  emitAssign "clint_addr" (.slice fullAddr 15 0)

  -- UART: extract offset [7:0]
  emitAssign "uart_addr" (.slice fullAddr 7 0)

  -- Boot: pass full address through (mapped at 0x80000000)
  emitAssign "boot_addr" fullAddr

  -- =========================================================================
  -- Control Signal Qualification
  -- =========================================================================

  -- Forward write data
  emitAssign "dev_wdata" (.ref "wdata")

  -- Qualify write/read enables with any device select
  let anyDev ← makeWire "any_dev" .bit
  emitAssign anyDev (.op .or [.ref isDRAM,
    .op .or [.ref isCLINT,
    .op .or [.ref isUART, .ref isBoot]]])
  emitAssign "dev_we" (.op .and [we, .ref anyDev])
  emitAssign "dev_re" (.op .and [re, .ref anyDev])

  -- =========================================================================
  -- Read Data Mux
  -- =========================================================================

  -- Priority mux: CLINT > UART > Boot > DRAM (default)
  emitAssign "rdata"
    (Expr.mux (.ref isCLINT) (.ref "clint_rdata")
    (Expr.mux (.ref isUART) (.ref "uart_rdata")
    (Expr.mux (.ref isBoot) (.ref "boot_rdata")
      (.ref "dram_rdata"))))

/-- Build the bus decoder module -/
def buildBus : Module :=
  CircuitM.runModule "RV32I_Bus" do
    generateBus

end Sparkle.Examples.RV32.Bus
