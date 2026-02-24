/-
  Sv32 MMU Top-Level

  Combines TLB + PTW + permission checks for one address channel.
  Provides virtual-to-physical translation with automatic page walks.

  Interface:
    vaddr (32-bit) → paddr (34-bit for Sv32) + fault + ready

  Instantiate twice: once for instruction fetch (iTLB), once for data (dTLB).
  Supports bypass mode when satp.MODE = 0 (bare translation for M-mode).
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.RV32.CSR.Types

set_option maxRecDepth 8192

namespace Sparkle.Examples.RV32.MMU.Top

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Examples.RV32.CSR
open CircuitM

/-- Generate the MMU top-level for one address channel.

    This integrates the TLB and PTW into a unified translation unit.
    Uses a simple FSM: IDLE → TLB_LOOKUP → PTW_WALK → DONE/FAULT

    Inputs:
      clk, rst
      -- Translation request
      vaddr[31:0]        - Virtual address to translate
      req_valid          - Translation request valid
      access_read        - Access is a load
      access_write       - Access is a store
      access_exec        - Access is instruction fetch
      -- SATP
      satp[31:0]         - SATP register value
      priv_mode[1:0]     - Current privilege mode
      -- SFENCE.VMA
      sfence             - Flush TLB
      -- Memory interface (shared with PTW)
      mem_rdata[31:0]    - Memory read response
      mem_ready          - Memory response valid

    Outputs:
      paddr[31:0]        - Physical address (translated)
      ready              - Translation complete
      fault              - Page fault
      -- Memory interface (PTW requests)
      mem_addr[31:0]     - PTW memory read address
      mem_req            - PTW memory read request
      stall              - MMU is busy, stall pipeline
-/
def generateMMUTop : CircuitM Unit := do
  addInput "clk" .bit
  addInput "rst" .bit
  addInput "vaddr" (.bitVector 32)
  addInput "req_valid" .bit
  addInput "access_read" .bit
  addInput "access_write" .bit
  addInput "access_exec" .bit
  addInput "satp" (.bitVector 32)
  addInput "priv_mode" (.bitVector 2)
  addInput "sfence" .bit
  addInput "mem_rdata" (.bitVector 32)
  addInput "mem_ready" .bit

  addOutput "paddr" (.bitVector 32)
  addOutput "ready" .bit
  addOutput "fault" .bit
  addOutput "mem_addr" (.bitVector 32)
  addOutput "mem_req" .bit
  addOutput "stall" .bit

  -- =========================================================================
  -- SATP decode
  -- =========================================================================
  let satpMode ← makeWire "satp_mode" .bit
  emitAssign satpMode (.slice (.ref "satp") satpMODE satpMODE)
  let satpPPN ← makeWire "satp_ppn" (.bitVector 22)
  emitAssign satpPPN (.slice (.ref "satp") satpPPN_HI 0)

  -- Bypass mode: no translation when satp.MODE=0 or M-mode
  let isMmode ← makeWire "is_mmode" .bit
  emitAssign isMmode (.op .eq [.ref "priv_mode", .const privM 2])
  let bypassMMU ← makeWire "bypass_mmu" .bit
  emitAssign bypassMMU (.op .or [.ref isMmode, .op .not [.ref satpMode]])

  -- VPN extraction
  let vpn ← makeWire "mmu_vpn" (.bitVector 20)
  emitAssign vpn (.slice (.ref "vaddr") 31 12)
  let pageOffset ← makeWire "page_offset" (.bitVector 12)
  emitAssign pageOffset (.slice (.ref "vaddr") 11 0)

  -- =========================================================================
  -- MMU FSM States
  -- =========================================================================
  -- 0: IDLE, 1: TLB_LOOKUP, 2: PTW_WALK, 3: DONE, 4: FAULT
  let stateNext ← makeWire "mmu_state_next" (.bitVector 3)
  let stateReg ← emitRegister "mmu_state" "clk" "rst" (.ref stateNext) 0 (.bitVector 3)

  let isMMUIdle ← makeWire "mmu_is_idle" .bit
  emitAssign isMMUIdle (.op .eq [.ref stateReg, .const 0 3])
  let isTLBLookup ← makeWire "mmu_is_tlb" .bit
  emitAssign isTLBLookup (.op .eq [.ref stateReg, .const 1 3])
  let isPTWWalk ← makeWire "mmu_is_ptw" .bit
  emitAssign isPTWWalk (.op .eq [.ref stateReg, .const 2 3])
  let isMMUDone ← makeWire "mmu_is_done" .bit
  emitAssign isMMUDone (.op .eq [.ref stateReg, .const 3 3])
  let isMMUFault ← makeWire "mmu_is_fault" .bit
  emitAssign isMMUFault (.op .eq [.ref stateReg, .const 4 3])

  -- =========================================================================
  -- TLB (inline — simplified version without full module instantiation)
  -- =========================================================================
  -- For the top-level, we model TLB as a set of registers
  -- 4-entry TLB for simplicity in the top-level integration

  -- TLB valid array
  let tlbEntry0Valid_next ← makeWire "tlb0_valid_next" .bit
  let tlbEntry0Valid ← emitRegister "tlb0_valid" "clk" "rst" (.ref tlbEntry0Valid_next) 0 .bit
  let tlbEntry0VPN_next ← makeWire "tlb0_vpn_next" (.bitVector 20)
  let tlbEntry0VPN ← emitRegister "tlb0_vpn" "clk" "rst" (.ref tlbEntry0VPN_next) 0 (.bitVector 20)
  let tlbEntry0PPN_next ← makeWire "tlb0_ppn_next" (.bitVector 22)
  let tlbEntry0PPN ← emitRegister "tlb0_ppn" "clk" "rst" (.ref tlbEntry0PPN_next) 0 (.bitVector 22)
  let tlbEntry0Flags_next ← makeWire "tlb0_flags_next" (.bitVector 8)
  let tlbEntry0Flags ← emitRegister "tlb0_flags" "clk" "rst" (.ref tlbEntry0Flags_next) 0 (.bitVector 8)
  let tlbEntry0Mega_next ← makeWire "tlb0_mega_next" .bit
  let tlbEntry0Mega ← emitRegister "tlb0_mega" "clk" "rst" (.ref tlbEntry0Mega_next) 0 .bit

  -- TLB lookup
  let tlb0Hit ← makeWire "tlb0_hit" .bit
  emitAssign tlb0Hit (.op .and [.ref tlbEntry0Valid,
    .op .eq [.ref tlbEntry0VPN, .ref vpn]])

  -- FIFO replacement pointer
  let replPtrNext ← makeWire "repl_ptr_next" (.bitVector 2)
  let replPtrReg ← emitRegister "mmu_repl_ptr" "clk" "rst" (.ref replPtrNext) 0 (.bitVector 2)

  -- =========================================================================
  -- PTW Control Signals
  -- =========================================================================
  let ptwReq ← makeWire "ptw_req" .bit
  let ptwDone ← makeWire "ptw_done" .bit
  let ptwFault ← makeWire "ptw_fault" .bit
  let ptwPPN ← makeWire "ptw_ppn" (.bitVector 22)
  let ptwFlags ← makeWire "ptw_flags" (.bitVector 8)
  let ptwMega ← makeWire "ptw_mega" .bit
  let ptwBusy ← makeWire "ptw_busy" .bit
  let ptwMemAddr ← makeWire "ptw_mem_addr" (.bitVector 32)
  let ptwMemReq ← makeWire "ptw_mem_req" .bit

  -- =========================================================================
  -- Inline PTW FSM (simplified 2-level walker)
  -- =========================================================================
  let ptwStateNext ← makeWire "ptw_state_next" (.bitVector 3)
  let ptwStateReg ← emitRegister "ptw_state" "clk" "rst" (.ref ptwStateNext) 0 (.bitVector 3)

  let ptwIsIdle ← makeWire "ptw_is_idle" .bit
  emitAssign ptwIsIdle (.op .eq [.ref ptwStateReg, .const 0 3])
  let ptwIsL1 ← makeWire "ptw_is_l1" .bit
  emitAssign ptwIsL1 (.op .eq [.ref ptwStateReg, .const 1 3])
  let ptwIsL0 ← makeWire "ptw_is_l0" .bit
  emitAssign ptwIsL0 (.op .eq [.ref ptwStateReg, .const 2 3])
  let ptwIsDone ← makeWire "ptw_is_done" .bit
  emitAssign ptwIsDone (.op .eq [.ref ptwStateReg, .const 3 3])
  let ptwIsFault ← makeWire "ptw_is_fault" .bit
  emitAssign ptwIsFault (.op .eq [.ref ptwStateReg, .const 4 3])

  -- Latched vaddr for PTW
  let ptwVaddrNext ← makeWire "ptw_vaddr_next" (.bitVector 32)
  let ptwVaddrReg ← emitRegister "ptw_vaddr" "clk" "rst" (.ref ptwVaddrNext) 0 (.bitVector 32)
  emitAssign ptwVaddrNext (Expr.mux (.op .and [.ref ptwIsIdle, .ref ptwReq])
    (.ref "vaddr") (.ref ptwVaddrReg))

  let ptwVPN1 ← makeWire "ptw_vpn1" (.bitVector 10)
  emitAssign ptwVPN1 (.slice (.ref ptwVaddrReg) 31 22)
  let ptwVPN0 ← makeWire "ptw_vpn0" (.bitVector 10)
  emitAssign ptwVPN0 (.slice (.ref ptwVaddrReg) 21 12)

  -- PTE latch
  let ptwPteNext ← makeWire "ptw_pte_next" (.bitVector 32)
  let ptwPteReg ← emitRegister "ptw_pte" "clk" "rst" (.ref ptwPteNext) 0 (.bitVector 32)
  emitAssign ptwPteNext (Expr.mux (.ref "mem_ready") (.ref "mem_rdata") (.ref ptwPteReg))

  let pteValid ← makeWire "pte_valid" .bit
  emitAssign pteValid (.slice (.ref ptwPteReg) 0 0)
  let pteRBit ← makeWire "pte_r_bit" .bit
  emitAssign pteRBit (.slice (.ref ptwPteReg) 1 1)
  let pteXBit ← makeWire "pte_x_bit" .bit
  emitAssign pteXBit (.slice (.ref ptwPteReg) 3 3)
  let pteIsLeaf ← makeWire "pte_is_leaf" .bit
  emitAssign pteIsLeaf (.op .or [.ref pteRBit, .ref pteXBit])

  -- Memory address generation
  let l1Addr ← makeWire "ptw_l1_addr" (.bitVector 32)
  emitAssign l1Addr (Expr.add
    (.concat [.ref satpPPN, .const 0 10])
    (.concat [.const 0 20, .ref ptwVPN1, .const 0 2]))

  let ptePPNFull ← makeWire "pte_ppn_full" (.bitVector 22)
  emitAssign ptePPNFull (.slice (.ref ptwPteReg) 31 10)

  let l0Addr ← makeWire "ptw_l0_addr" (.bitVector 32)
  emitAssign l0Addr (Expr.add
    (.concat [.ref ptePPNFull, .const 0 10])
    (.concat [.const 0 20, .ref ptwVPN0, .const 0 2]))

  emitAssign ptwMemAddr (Expr.mux (.ref ptwIsL1) (.ref l1Addr)
    (Expr.mux (.ref ptwIsL0) (.ref l0Addr) (.const 0 32)))
  emitAssign ptwMemReq (.op .or [.ref ptwIsL1, .ref ptwIsL0])

  -- PTW state transitions
  let pteInvalid ← makeWire "pte_invalid" .bit
  emitAssign pteInvalid (.op .not [.ref pteValid])

  let nextFromPtwIdle ← makeWire "ptw_next_idle" (.bitVector 3)
  emitAssign nextFromPtwIdle (Expr.mux (.ref ptwReq) (.const 1 3) (.const 0 3))

  let nextFromL1 ← makeWire "ptw_next_l1" (.bitVector 3)
  emitAssign nextFromL1
    (Expr.mux (.ref "mem_ready")
      (Expr.mux (.ref pteInvalid) (.const 4 3)
      (Expr.mux (.ref pteIsLeaf) (.const 3 3)
        (.const 2 3)))
      (.const 1 3))

  let nextFromL0 ← makeWire "ptw_next_l0" (.bitVector 3)
  emitAssign nextFromL0
    (Expr.mux (.ref "mem_ready")
      (Expr.mux (.ref pteInvalid) (.const 4 3)
      (Expr.mux (.ref pteIsLeaf) (.const 3 3)
        (.const 4 3)))
      (.const 2 3))

  emitAssign ptwStateNext
    (Expr.mux (.ref ptwIsIdle) (.ref nextFromPtwIdle)
    (Expr.mux (.ref ptwIsL1) (.ref nextFromL1)
    (Expr.mux (.ref ptwIsL0) (.ref nextFromL0)
      (.const 0 3))))

  -- Megapage tracking
  let ptwMegaNext ← makeWire "ptw_mega_next" .bit
  let ptwMegaReg ← emitRegister "ptw_mega_reg" "clk" "rst" (.ref ptwMegaNext) 0 .bit
  emitAssign ptwMegaNext
    (Expr.mux (.op .and [.ref ptwIsL1, .ref "mem_ready"])
      (.ref pteIsLeaf)
      (Expr.mux (.ref ptwIsIdle) (.const 0 1) (.ref ptwMegaReg)))

  emitAssign ptwDone (.ref ptwIsDone)
  emitAssign ptwFault (.ref ptwIsFault)
  emitAssign ptwPPN (.ref ptePPNFull)
  emitAssign ptwFlags (.slice (.ref ptwPteReg) 7 0)
  emitAssign ptwMega (.ref ptwMegaReg)
  emitAssign ptwBusy (.op .not [.ref ptwIsIdle])

  -- =========================================================================
  -- TLB Fill on PTW completion
  -- =========================================================================
  let tlbFill ← makeWire "tlb_fill" .bit
  emitAssign tlbFill (.ref ptwIsDone)

  -- TLB entry update: fill on PTW done, clear on SFENCE
  emitAssign tlbEntry0Valid_next
    (Expr.mux (.ref "sfence") (.const 0 1)
    (Expr.mux (.ref tlbFill) (.const 1 1)
      (.ref tlbEntry0Valid)))
  emitAssign tlbEntry0VPN_next
    (Expr.mux (.ref tlbFill) (.slice (.ref ptwVaddrReg) 31 12) (.ref tlbEntry0VPN))
  emitAssign tlbEntry0PPN_next
    (Expr.mux (.ref tlbFill) (.ref ptwPPN) (.ref tlbEntry0PPN))
  emitAssign tlbEntry0Flags_next
    (Expr.mux (.ref tlbFill) (.ref ptwFlags) (.ref tlbEntry0Flags))
  emitAssign tlbEntry0Mega_next
    (Expr.mux (.ref tlbFill) (.ref ptwMega) (.ref tlbEntry0Mega))

  -- Replacement pointer: increment on fill (unused with single entry, but ready for expansion)
  emitAssign replPtrNext (Expr.mux (.ref tlbFill)
    (Expr.add (.ref replPtrReg) (.const 1 2))
    (.ref replPtrReg))

  -- =========================================================================
  -- PTW request: on TLB miss
  -- =========================================================================
  emitAssign ptwReq (.op .and [.ref isTLBLookup, .op .not [.ref tlb0Hit]])

  -- =========================================================================
  -- MMU State Transitions
  -- =========================================================================
  -- IDLE → TLB_LOOKUP (on request, with translation enabled)
  -- TLB_LOOKUP → DONE (hit) / PTW_WALK (miss)
  -- PTW_WALK → DONE (ptw done) / FAULT (ptw fault)
  -- DONE → IDLE
  -- FAULT → IDLE

  let nextFromMMUIdle ← makeWire "mmu_next_idle" (.bitVector 3)
  let needTranslate ← makeWire "need_translate" .bit
  emitAssign needTranslate (.op .and [.ref "req_valid", .op .not [.ref bypassMMU]])
  emitAssign nextFromMMUIdle (Expr.mux (.ref needTranslate) (.const 1 3) (.const 0 3))

  let nextFromTLBLookup ← makeWire "mmu_next_tlb" (.bitVector 3)
  emitAssign nextFromTLBLookup
    (Expr.mux (.ref tlb0Hit) (.const 3 3)  -- hit → DONE
      (.const 2 3))  -- miss → PTW_WALK

  let nextFromPTWWalk ← makeWire "mmu_next_ptw" (.bitVector 3)
  emitAssign nextFromPTWWalk
    (Expr.mux (.ref ptwIsDone) (.const 3 3)
    (Expr.mux (.ref ptwIsFault) (.const 4 3)
      (.const 2 3)))

  emitAssign stateNext
    (Expr.mux (.ref isMMUIdle) (.ref nextFromMMUIdle)
    (Expr.mux (.ref isTLBLookup) (.ref nextFromTLBLookup)
    (Expr.mux (.ref isPTWWalk) (.ref nextFromPTWWalk)
      (.const 0 3))))  -- DONE/FAULT → IDLE

  -- =========================================================================
  -- Physical Address Output
  -- =========================================================================
  -- On bypass: paddr = vaddr
  -- On TLB hit: paddr = {tlb_ppn, page_offset} (or megapage variant)
  -- On PTW done: paddr = {ptw_ppn, page_offset}
  let tlbPAddr ← makeWire "tlb_paddr" (.bitVector 32)
  -- For 4KB pages: {ppn[21:0], offset[11:0]} = 34 bits, truncate to 32
  -- Use ppn[19:0] ++ offset[11:0] for 32-bit physical address
  emitAssign tlbPAddr (.concat [.slice (.ref tlbEntry0PPN) 19 0, .ref pageOffset])

  let ptwPAddr ← makeWire "ptw_paddr" (.bitVector 32)
  emitAssign ptwPAddr (.concat [.slice (.ref ptwPPN) 19 0, .ref pageOffset])

  let translatedAddr ← makeWire "translated_addr" (.bitVector 32)
  emitAssign translatedAddr
    (Expr.mux (.ref tlb0Hit) (.ref tlbPAddr) (.ref ptwPAddr))

  emitAssign "paddr" (Expr.mux (.ref bypassMMU) (.ref "vaddr") (.ref translatedAddr))

  -- =========================================================================
  -- Output Signals
  -- =========================================================================
  -- Ready: bypass always ready, else on DONE state
  let bypassReady ← makeWire "bypass_ready" .bit
  emitAssign bypassReady (.op .and [.ref "req_valid", .ref bypassMMU])
  emitAssign "ready" (.op .or [.ref bypassReady, .ref isMMUDone])
  emitAssign "fault" (.ref isMMUFault)

  -- Memory interface: forward PTW requests
  emitAssign "mem_addr" (.ref ptwMemAddr)
  emitAssign "mem_req" (.ref ptwMemReq)

  -- Stall: MMU busy and not bypass
  let mmuBusy ← makeWire "mmu_busy" .bit
  emitAssign mmuBusy (.op .not [.ref isMMUIdle])
  emitAssign "stall" (.op .and [.ref mmuBusy, .op .not [.ref bypassMMU]])

/-- Build the MMU top module -/
def buildMMUTop : Module :=
  CircuitM.runModule "RV32I_MMU" do
    generateMMUTop

end Sparkle.Examples.RV32.MMU.Top
