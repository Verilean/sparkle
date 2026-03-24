/-
  Bus Address Decoder — Signal DSL

  Routes memory requests to the appropriate peripheral based on address.
  Pure combinational logic (no Signal.loop needed).

  Address Map:
    0x00000000 - 0x0001FFFF : DRAM (128KB, via MMU when enabled)
    0x02000000 - 0x0200FFFF : CLINT (Core Local Interruptor)
    0x10000000 - 0x100000FF : UART (optional, TX-only console)
    0x80000000 - 0x8001FFFF : DRAM boot region (identity-mapped)
-/

import Sparkle
import Sparkle.Compiler.Elab

set_option maxRecDepth 4096

namespace Sparkle.Examples.RV32.Bus

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Bus address decoder — Signal DSL.

    Inputs:
      addr[31:0]          - Full 32-bit address from core
      wdata[31:0]         - Write data from core
      we                  - Write enable from core
      re                  - Read enable from core
      dram_rdata[31:0]    - Read data from DRAM
      clint_rdata[31:0]   - Read data from CLINT
      uart_rdata[31:0]    - Read data from UART
      boot_rdata[31:0]    - Read data from boot ROM/DRAM

    Output (nested tuple):
      (dram_sel × clint_sel × uart_sel × boot_sel ×
       dram_addr[31:0] × clint_addr[15:0] × uart_addr[7:0] × boot_addr[31:0] ×
       dev_wdata[31:0] × dev_we × dev_re × rdata[31:0]) -/
def busDecoderSignal {dom : DomainConfig}
    (addr : Signal dom (BitVec 32))
    (wdata : Signal dom (BitVec 32))
    (we : Signal dom Bool)
    (re : Signal dom Bool)
    (dram_rdata : Signal dom (BitVec 32))
    (clint_rdata : Signal dom (BitVec 32))
    (uart_rdata : Signal dom (BitVec 32))
    (boot_rdata : Signal dom (BitVec 32))
    : Signal dom (Bool × (Bool × (Bool × (Bool ×
       (BitVec 32 × (BitVec 16 × (BitVec 8 × (BitVec 32 ×
       (BitVec 32 × (Bool × (Bool × BitVec 32))))))))))) :=
  -- Address decode
  -- CLINT: 0x02000000 - 0x0200FFFF (addr[31:16] == 0x0200)
  let isCLINT := (addr.map (BitVec.extractLsb' 16 16 ·)) === 0x0200#16
  -- UART: 0x10000000 - 0x100000FF (addr[31:8] == 0x100000)
  let isUART := (addr.map (BitVec.extractLsb' 8 24 ·)) === 0x100000#24
  -- Boot DRAM: 0x80000000 - 0x8001FFFF (addr[31:17] == 0x4000)
  let isBoot := (addr.map (BitVec.extractLsb' 17 15 ·)) === 0x4000#15
  -- DRAM: default (not CLINT, not UART, not Boot)
  let notClint := ~~~isCLINT
  let notUart := ~~~isUART
  let notBoot := ~~~isBoot
  let isDRAM := notClint &&& (notUart &&& notBoot)

  -- Address extraction per device
  let dramAddr := addr
  let clintAddr := addr.map (BitVec.extractLsb' 0 16 ·)
  let uartAddr := addr.map (BitVec.extractLsb' 0 8 ·)
  let bootAddr := addr

  -- Control signal qualification
  let anyDev := (isDRAM ||| isCLINT) ||| (isUART ||| isBoot)
  let devWE := we &&& anyDev
  let devRE := re &&& anyDev

  -- Read data mux: CLINT > UART > Boot > DRAM (default)
  let rdata := Signal.mux isCLINT clint_rdata
    (Signal.mux isUART uart_rdata
    (Signal.mux isBoot boot_rdata
      dram_rdata))

  -- Bundle all outputs
  bundleAll! [
    isDRAM, isCLINT, isUART, isBoot,
    dramAddr, clintAddr, uartAddr, bootAddr,
    wdata, devWE, devRE, rdata
  ]

#synthesizeVerilog busDecoderSignal

end Sparkle.Examples.RV32.Bus
