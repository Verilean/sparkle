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
import IP.RV32.JITDebug
import IP.RV32.Bus
import IP.RV32.Bus.Decoder
import IP.RV32.Bus.StoreWidth
import IP.RV32.Bus.StoreData
import IP.RV32.Bus.LoadWidth
import IP.RV32.Bus.PeripheralWE
import IP.RV32.Bus.RdataMux
import IP.RV32.UART
import IP.RV32.UART.Decode
import IP.RV32.UART.ReadMux
import IP.RV32.MMIO.BitNet
import IP.RV32.CLINT
import IP.RV32.CLINT.Decode
import IP.RV32.CLINT.Timer
import IP.RV32.Trap
import IP.RV32.CSR.File
import IP.RV32.CSR.Supervisor
import IP.RV32.MMU.Top
import IP.RV32.MMU.IfetchFault
import IP.RV32.MMU.DMiss
import IP.RV32.MMU.PA
import IP.RV32.MMU.Satp
import IP.RV32.MMU.State
import IP.RV32.MMU.FSM
import IP.RV32.MMU.PTWFSM
import IP.RV32.MMU.PTWLatch
import IP.RV32.MMU.PTE
import IP.RV32.MMU.TLB
import IP.RV32.MMU.Fill
import IP.RV32.MMU.NeedTranslate
import IP.RV32.MMU.PTWReq
import IP.RV32.MMU.PTWAddr
import IP.RV32.AMO.Reservation
import IP.RV32.AMO.Compute
import IP.RV32.AMO.Decode
import IP.RV32.AMO.SC
import IP.RV32.AMO.PendingWrite
import IP.RV32.AMO.LRSCAcrossTrap
import IP.RV32.ALU.Compute
import IP.RV32.Decoder.ImmGen
import IP.RV32.Decoder.AluControl
import IP.RV32.Decoder.Control
import IP.RV32.Decoder.Fields
import IP.RV32.Decoder.System
import IP.RV32.Decoder.Opcode
import IP.RV32.Mext.Mul
import IP.RV32.Mext.Div
import IP.RV32.Mext.DivPending
import IP.RV32.Privilege.PrivMode
import IP.RV32.Trap.TrapPC
import IP.RV32.Trap.Delegation
import IP.RV32.Trap.IRQEnable
import IP.RV32.Trap.Cause
import IP.RV32.Trap.TrapTaken
import IP.RV32.Trap.Entry
import IP.RV32.CSR.MStatus
import IP.RV32.CSR.MStatusNext
import IP.RV32.CSR.NewValue
import IP.RV32.CSR.Commit
import IP.RV32.CSR.MIP
import IP.RV32.CSR.MipSoft
import IP.RV32.CSR.Sstatus
import IP.RV32.CSR.Funct3
import IP.RV32.CSR.PMPRange
import IP.RV32.CSR.AddrDecoder
import IP.RV32.CSR.MStatusBits
import IP.RV32.CSR.ReadMux
import IP.RV32.Pipeline.SuppressEXWB
import IP.RV32.Pipeline.AbortGuarantee
import IP.RV32.Pipeline.FlushSquash
import IP.RV32.Pipeline.BranchComp
import IP.RV32.Pipeline.Hazard
import IP.RV32.Pipeline.IdexLive
import IP.RV32.Pipeline.PCNext
import IP.RV32.Pipeline.Writeback
import IP.RV32.Pipeline.Forward
import IP.RV32.Pipeline.Regfile
import IP.RV32.Pipeline.Stall
import IP.RV32.Pipeline.IFID
import IP.RV32.Pipeline.IFetchSrc
import IP.RV32.Pipeline.AluSrc
import IP.RV32.Pipeline.AluResult
import IP.RV32.Pipeline.MMURedirectInv
import IP.RV32.Pipeline.StoreDuringTrap
import IP.RV32.Pipeline.RegfileTrapInv
import IP.RV32.Pipeline.SideEffectsTrapInv
import IP.RV32.Pipeline.StoreLoadFwd
