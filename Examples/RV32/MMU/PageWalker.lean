/-
  Sv32 Hardware Page Table Walker (PTW)

  Walks the 2-level Sv32 page table to translate virtual addresses.

  Sv32 Virtual Address: [VPN1(10) | VPN0(10) | offset(12)]
  Sv32 PTE format: [PPN1(12) | PPN0(10) | RSW(2) | D | A | G | U | X | W | R | V]

  FSM States:
    IDLE   - Waiting for TLB miss
    LEVEL1 - Reading level-1 PTE at satp.PPN*4096 + VPN[1]*4
    LEVEL0 - Reading level-0 PTE at PTE.PPN*4096 + VPN[0]*4
    DONE   - Translation complete, fill TLB
    FAULT  - Page fault (invalid PTE, permission violation)
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.RV32.CSR.Types

set_option maxRecDepth 8192

namespace Sparkle.Examples.RV32.MMU.PageWalker

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Examples.RV32.CSR
open CircuitM

/-- PTW state encoding -/
def stIDLE   : Nat := 0
def stLEVEL1 : Nat := 1
def stLEVEL0 : Nat := 2
def stDONE   : Nat := 3
def stFAULT  : Nat := 4

/-- Generate the hardware page table walker.

    Inputs:
      clk, rst
      -- Translation request
      ptw_req             - Start page walk request
      vaddr[31:0]         - Virtual address to translate
      -- SATP register
      satp_ppn[21:0]      - Page table root PPN from satp
      -- Memory interface (response)
      mem_rdata[31:0]     - Memory read data (PTE)
      mem_ready           - Memory response valid
      -- Access type for permission check
      access_read         - Load instruction
      access_write        - Store instruction
      access_exec         - Instruction fetch
      priv_mode[1:0]      - Current privilege mode

    Outputs:
      -- Translation result
      ptw_done            - Walk complete (hit DONE state)
      ptw_fault           - Page fault occurred
      ptw_ppn[21:0]       - Translated PPN
      ptw_flags[7:0]      - PTE flags
      ptw_megapage        - Result is a megapage (4MB)
      -- Memory interface (request)
      mem_addr[31:0]      - Memory read address (for PTE fetch)
      mem_req             - Memory read request
      -- Status
      ptw_busy            - PTW is busy (not idle)
-/
def generatePTW : CircuitM Unit := do
  addInput "clk" .bit
  addInput "rst" .bit
  addInput "ptw_req" .bit
  addInput "vaddr" (.bitVector 32)
  addInput "satp_ppn" (.bitVector 22)
  addInput "mem_rdata" (.bitVector 32)
  addInput "mem_ready" .bit
  addInput "access_read" .bit
  addInput "access_write" .bit
  addInput "access_exec" .bit
  addInput "priv_mode" (.bitVector 2)

  addOutput "ptw_done" .bit
  addOutput "ptw_fault" .bit
  addOutput "ptw_ppn" (.bitVector 22)
  addOutput "ptw_flags" (.bitVector 8)
  addOutput "ptw_megapage" .bit
  addOutput "mem_addr" (.bitVector 32)
  addOutput "mem_req" .bit
  addOutput "ptw_busy" .bit

  -- =========================================================================
  -- State Register (3-bit FSM)
  -- =========================================================================
  let stateNext ← makeWire "ptw_state_next" (.bitVector 3)
  let stateReg ← emitRegister "ptw_state" "clk" "rst" (.ref stateNext) stIDLE (.bitVector 3)

  -- State decode signals
  let isIdle ← makeWire "ptw_is_idle" .bit
  emitAssign isIdle (.op .eq [.ref stateReg, .const stIDLE 3])
  let isLevel1 ← makeWire "ptw_is_level1" .bit
  emitAssign isLevel1 (.op .eq [.ref stateReg, .const stLEVEL1 3])
  let isLevel0 ← makeWire "ptw_is_level0" .bit
  emitAssign isLevel0 (.op .eq [.ref stateReg, .const stLEVEL0 3])
  let isDone ← makeWire "ptw_is_done" .bit
  emitAssign isDone (.op .eq [.ref stateReg, .const stDONE 3])
  let isFault ← makeWire "ptw_is_fault" .bit
  emitAssign isFault (.op .eq [.ref stateReg, .const stFAULT 3])

  -- =========================================================================
  -- Latched Virtual Address
  -- =========================================================================
  let vaddrNext ← makeWire "ptw_vaddr_next" (.bitVector 32)
  let vaddrReg ← emitRegister "ptw_vaddr" "clk" "rst" (.ref vaddrNext) 0 (.bitVector 32)
  -- Latch on request
  emitAssign vaddrNext (Expr.mux (.op .and [.ref isIdle, .ref "ptw_req"])
    (.ref "vaddr") (.ref vaddrReg))

  -- Extract VPN fields from latched vaddr
  -- VPN[1] = vaddr[31:22], VPN[0] = vaddr[21:12]
  let vpn1 ← makeWire "ptw_vpn1" (.bitVector 10)
  emitAssign vpn1 (.slice (.ref vaddrReg) 31 22)
  let vpn0 ← makeWire "ptw_vpn0" (.bitVector 10)
  emitAssign vpn0 (.slice (.ref vaddrReg) 21 12)

  -- =========================================================================
  -- PTE Register (latched from memory response)
  -- =========================================================================
  let pteNext ← makeWire "ptw_pte_next" (.bitVector 32)
  let pteReg ← emitRegister "ptw_pte" "clk" "rst" (.ref pteNext) 0 (.bitVector 32)
  -- Latch PTE when memory responds
  emitAssign pteNext (Expr.mux (.ref "mem_ready") (.ref "mem_rdata") (.ref pteReg))

  -- PTE field extraction
  let pteFlags ← makeWire "pte_flags" (.bitVector 8)
  emitAssign pteFlags (.slice (.ref pteReg) 7 0)

  let pteV ← makeWire "pte_v" .bit
  emitAssign pteV (.slice (.ref pteReg) 0 0)
  let pteR ← makeWire "pte_r" .bit
  emitAssign pteR (.slice (.ref pteReg) 1 1)
  let pteW ← makeWire "pte_w" .bit
  emitAssign pteW (.slice (.ref pteReg) 2 2)
  let pteX ← makeWire "pte_x" .bit
  emitAssign pteX (.slice (.ref pteReg) 3 3)
  let pteU ← makeWire "pte_u" .bit
  emitAssign pteU (.slice (.ref pteReg) 4 4)
  let pteA ← makeWire "pte_a" .bit
  emitAssign pteA (.slice (.ref pteReg) 6 6)
  let pteD ← makeWire "pte_d" .bit
  emitAssign pteD (.slice (.ref pteReg) 7 7)

  -- PTE PPN: bits [31:10]
  let ptePPN ← makeWire "pte_ppn" (.bitVector 22)
  emitAssign ptePPN (.slice (.ref pteReg) 31 10)
  let ptePPN1 ← makeWire "pte_ppn1" (.bitVector 12)
  emitAssign ptePPN1 (.slice (.ref pteReg) 31 20)
  let ptePPN0 ← makeWire "pte_ppn0" (.bitVector 10)
  emitAssign ptePPN0 (.slice (.ref pteReg) 19 10)

  -- Is this a leaf PTE? (R or X set)
  let isLeaf ← makeWire "pte_is_leaf" .bit
  emitAssign isLeaf (.op .or [.ref pteR, .ref pteX])

  -- =========================================================================
  -- Permission Checks
  -- =========================================================================
  -- Check if access is permitted by PTE flags

  -- Read: need R=1 (or X=1 if MXR set, but we skip MXR for simplicity)
  let readOk ← makeWire "perm_read_ok" .bit
  emitAssign readOk (.ref pteR)

  -- Write: need W=1
  let writeOk ← makeWire "perm_write_ok" .bit
  emitAssign writeOk (.ref pteW)

  -- Execute: need X=1
  let execOk ← makeWire "perm_exec_ok" .bit
  emitAssign execOk (.ref pteX)

  -- Access check: does the requested access type match permissions?
  let readCheck ← makeWire "read_check" .bit
  emitAssign readCheck (Expr.mux (.ref "access_read") (.ref readOk) (.const 1 1))
  let writeCheck ← makeWire "write_check" .bit
  emitAssign writeCheck (Expr.mux (.ref "access_write") (.ref writeOk) (.const 1 1))
  let execCheck ← makeWire "exec_check" .bit
  emitAssign execCheck (Expr.mux (.ref "access_exec") (.ref execOk) (.const 1 1))

  let permOk ← makeWire "perm_ok" .bit
  emitAssign permOk (.op .and [.ref readCheck, .op .and [.ref writeCheck, .ref execCheck]])

  -- U-mode check: U-mode can only access U=1 pages
  let isUmode ← makeWire "is_umode" .bit
  emitAssign isUmode (.op .eq [.ref "priv_mode", .const privU 2])
  let umodeOk ← makeWire "umode_ok" .bit
  emitAssign umodeOk (Expr.mux (.ref isUmode) (.ref pteU) (.const 1 1))

  -- S-mode check: S-mode cannot access U=1 pages (without SUM)
  let isSmode ← makeWire "is_smode" .bit
  emitAssign isSmode (.op .eq [.ref "priv_mode", .const privS 2])
  let smodeOk ← makeWire "smode_ok" .bit
  emitAssign smodeOk (Expr.mux (.ref isSmode) (.op .not [.ref pteU]) (.const 1 1))

  -- A/D bit check: A must be set; D must be set if write
  let aOk ← makeWire "a_ok" .bit
  emitAssign aOk (.ref pteA)
  let dOk ← makeWire "d_ok" .bit
  emitAssign dOk (Expr.mux (.ref "access_write") (.ref pteD) (.const 1 1))

  -- Overall permission check
  let allPermsOk ← makeWire "all_perms_ok" .bit
  emitAssign allPermsOk (.op .and [.ref permOk,
    .op .and [.ref umodeOk,
    .op .and [.ref smodeOk,
    .op .and [.ref aOk, .ref dOk]]]])

  -- =========================================================================
  -- Memory Address Generation
  -- =========================================================================

  -- Level 1 address: satp.PPN * 4096 + VPN[1] * 4
  -- = {satp_ppn, 12'b0} + {20'b0, vpn1, 2'b0}
  let l1Base ← makeWire "l1_base" (.bitVector 32)
  emitAssign l1Base (.concat [.ref "satp_ppn", .const 0 10])
  let l1Offset ← makeWire "l1_offset" (.bitVector 32)
  emitAssign l1Offset (.concat [.const 0 20, .ref vpn1, .const 0 2])
  let l1Addr ← makeWire "l1_addr" (.bitVector 32)
  emitAssign l1Addr (Expr.add (.ref l1Base) (.ref l1Offset))

  -- Level 0 address: PTE.PPN * 4096 + VPN[0] * 4
  -- = {pte_ppn, 12'b0} + {20'b0, vpn0, 2'b0}
  let l0Base ← makeWire "l0_base" (.bitVector 32)
  emitAssign l0Base (.concat [.ref ptePPN, .const 0 10])
  let l0Offset ← makeWire "l0_offset" (.bitVector 32)
  emitAssign l0Offset (.concat [.const 0 20, .ref vpn0, .const 0 2])
  let l0Addr ← makeWire "l0_addr" (.bitVector 32)
  emitAssign l0Addr (Expr.add (.ref l0Base) (.ref l0Offset))

  -- Select memory address based on state
  emitAssign "mem_addr"
    (Expr.mux (.ref isLevel1) (.ref l1Addr)
    (Expr.mux (.ref isLevel0) (.ref l0Addr)
      (.const 0 32)))

  -- Memory request: active during LEVEL1 or LEVEL0 states
  emitAssign "mem_req" (.op .or [.ref isLevel1, .ref isLevel0])

  -- =========================================================================
  -- FSM State Transitions
  -- =========================================================================
  -- IDLE → LEVEL1 (on request)
  -- LEVEL1 → LEVEL0 (non-leaf, valid PTE) / DONE (leaf, valid) / FAULT (invalid)
  -- LEVEL0 → DONE (leaf, valid) / FAULT (invalid/non-leaf)
  -- DONE → IDLE
  -- FAULT → IDLE

  -- Transition from LEVEL1/LEVEL0 on memory response
  let pteInvalid ← makeWire "pte_invalid" .bit
  emitAssign pteInvalid (.op .not [.ref pteV])

  -- For LEVEL1: if leaf PTE with valid perms → DONE, if non-leaf → LEVEL0, else FAULT
  -- For megapages (leaf at level 1), PPN[0] must be 0 (alignment check)
  let megaAlignOk ← makeWire "mega_align_ok" .bit
  emitAssign megaAlignOk (.op .eq [.ref ptePPN0, .const 0 10])

  let l1LeafOk ← makeWire "l1_leaf_ok" .bit
  emitAssign l1LeafOk (.op .and [.ref isLeaf,
    .op .and [.ref allPermsOk, .ref megaAlignOk]])

  -- Next state logic
  let nextFromIdle ← makeWire "next_from_idle" (.bitVector 3)
  emitAssign nextFromIdle (Expr.mux (.ref "ptw_req")
    (.const stLEVEL1 3) (.const stIDLE 3))

  let nextFromL1 ← makeWire "next_from_l1" (.bitVector 3)
  emitAssign nextFromL1
    (Expr.mux (.ref "mem_ready")
      (Expr.mux (.ref pteInvalid) (.const stFAULT 3)
      (Expr.mux (.ref l1LeafOk) (.const stDONE 3)
      (Expr.mux (.ref isLeaf) (.const stFAULT 3)  -- leaf but bad perms or alignment
        (.const stLEVEL0 3))))  -- non-leaf, walk to level 0
      (.const stLEVEL1 3))  -- wait for memory

  let l0LeafOk ← makeWire "l0_leaf_ok" .bit
  emitAssign l0LeafOk (.op .and [.ref isLeaf, .ref allPermsOk])

  let nextFromL0 ← makeWire "next_from_l0" (.bitVector 3)
  emitAssign nextFromL0
    (Expr.mux (.ref "mem_ready")
      (Expr.mux (.ref pteInvalid) (.const stFAULT 3)
      (Expr.mux (.ref l0LeafOk) (.const stDONE 3)
        (.const stFAULT 3)))  -- non-leaf at level 0 is always fault
      (.const stLEVEL0 3))  -- wait for memory

  emitAssign stateNext
    (Expr.mux (.ref isIdle) (.ref nextFromIdle)
    (Expr.mux (.ref isLevel1) (.ref nextFromL1)
    (Expr.mux (.ref isLevel0) (.ref nextFromL0)
      (.const stIDLE 3))))  -- DONE and FAULT both return to IDLE

  -- =========================================================================
  -- Megapage Tracking
  -- =========================================================================
  let megapageNext ← makeWire "megapage_next" .bit
  let megapageReg ← emitRegister "ptw_megapage" "clk" "rst" (.ref megapageNext) 0 .bit
  -- Set megapage if we're at level1 and found a leaf PTE
  emitAssign megapageNext
    (Expr.mux (.op .and [.ref isLevel1, .ref "mem_ready"])
      (.ref isLeaf)
      (Expr.mux (.ref isIdle) (.const 0 1) (.ref megapageReg)))

  -- =========================================================================
  -- Output Signals
  -- =========================================================================
  emitAssign "ptw_done" (.ref isDone)
  emitAssign "ptw_fault" (.ref isFault)
  emitAssign "ptw_ppn" (.ref ptePPN)
  emitAssign "ptw_flags" (.ref pteFlags)
  emitAssign "ptw_megapage" (.ref megapageReg)
  emitAssign "ptw_busy" (.op .not [.ref isIdle])

/-- Build the PTW module -/
def buildPTW : Module :=
  CircuitM.runModule "RV32I_PTW" do
    generatePTW

end Sparkle.Examples.RV32.MMU.PageWalker
