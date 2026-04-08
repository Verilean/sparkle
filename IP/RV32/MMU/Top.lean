/-
  Sv32 MMU Top-Level — Signal DSL

  Combines TLB (4 entries) + PTW FSM in a single Signal.loop.
  26 registers total:
    - MMU FSM state (3-bit), PTW FSM state (3-bit)
    - Latched vaddr (32-bit), PTE latch (32-bit)
    - Megapage flag (1-bit), Replacement pointer (2-bit)
    - 4 TLB entries × 5 fields each: valid(1), vpn(20), ppn(22), flags(8), mega(1)

  Supports bypass mode when satp.MODE = 0 (bare translation for M-mode).
  FSM: IDLE → TLB_LOOKUP → PTW_WALK → DONE/FAULT
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.CSR.Types

set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

namespace Sparkle.IP.RV32.MMU

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.RV32.CSR

/-- MMU top-level — Signal DSL.

    Inputs:
      vaddr[31:0]        - Virtual address to translate
      reqValid           - Translation request valid
      accessRead         - Access is a load
      accessWrite        - Access is a store
      accessExec         - Access is instruction fetch
      satp[31:0]         - SATP register value
      privMode[1:0]      - Current privilege mode
      sfence             - Flush TLB
      memRdata[31:0]     - Memory read response
      memReady           - Memory response valid

    Output:
      (paddr[31:0] × ready × fault × mem_addr[31:0] × mem_req × stall) -/
def mmuTopSignal {dom : DomainConfig}
    (vaddr : Signal dom (BitVec 32))
    (reqValid : Signal dom Bool)
    (accessRead : Signal dom Bool)
    (accessWrite : Signal dom Bool)
    (accessExec : Signal dom Bool)
    (satp : Signal dom (BitVec 32))
    (privMode : Signal dom (BitVec 2))
    (sfence : Signal dom Bool)
    (memRdata : Signal dom (BitVec 32))
    (memReady : Signal dom Bool)
    : Signal dom (BitVec 32 × (Bool × (Bool × (BitVec 32 × (Bool × Bool))))) :=

  -- SATP decode
  let satpMode := (satp.map (BitVec.extractLsb' 31 1 ·)) === 1#1
  let satpPPN := satp.map (BitVec.extractLsb' 0 22 ·)

  -- Bypass mode: no translation when satp.MODE=0 or M-mode
  let isMmode := privMode === (BitVec.ofNat 2 privM)
  let bypassMMU := isMmode ||| (~~~satpMode)

  -- VPN and page offset extraction
  let vpn := vaddr.map (BitVec.extractLsb' 12 20 ·)
  let pageOffset := vaddr.map (BitVec.extractLsb' 0 12 ·)

  -- Register layout (26 total):
  --  0: mmuState (BitVec 3)      1: ptwState (BitVec 3)
  --  2: ptwVaddr (BitVec 32)     3: ptwPte (BitVec 32)
  --  4: ptwMega (Bool)           5: replPtr (BitVec 2)
  --  6-10: TLB entry 0 (valid, vpn, ppn, flags, mega)
  -- 11-15: TLB entry 1
  -- 16-20: TLB entry 2
  -- 21-25: TLB entry 3

  let mmu := Signal.loop fun state =>
    let mmuStateReg := projN! state 26 0   -- BitVec 3
    let ptwStateReg := projN! state 26 1   -- BitVec 3
    let ptwVaddrReg := projN! state 26 2   -- BitVec 32
    let ptwPteReg   := projN! state 26 3   -- BitVec 32
    let ptwMegaReg  := projN! state 26 4   -- Bool
    let replPtrReg  := projN! state 26 5   -- BitVec 2

    -- TLB entry 0
    let tlb0Valid := projN! state 26 6     -- Bool
    let tlb0VPN   := projN! state 26 7     -- BitVec 20
    let tlb0PPN   := projN! state 26 8     -- BitVec 22
    let tlb0Flags := projN! state 26 9     -- BitVec 8
    let tlb0Mega  := projN! state 26 10    -- Bool

    -- TLB entry 1
    let tlb1Valid := projN! state 26 11
    let tlb1VPN   := projN! state 26 12
    let tlb1PPN   := projN! state 26 13
    let tlb1Flags := projN! state 26 14
    let tlb1Mega  := projN! state 26 15

    -- TLB entry 2
    let tlb2Valid := projN! state 26 16
    let tlb2VPN   := projN! state 26 17
    let tlb2PPN   := projN! state 26 18
    let tlb2Flags := projN! state 26 19
    let tlb2Mega  := projN! state 26 20

    -- TLB entry 3
    let tlb3Valid := projN! state 26 21
    let tlb3VPN   := projN! state 26 22
    let tlb3PPN   := projN! state 26 23
    let tlb3Flags := projN! state 26 24
    let tlb3Mega  := projN! state 26 25

    -- =========================================================================
    -- MMU FSM states: 0=IDLE, 1=TLB_LOOKUP, 2=PTW_WALK, 3=DONE, 4=FAULT
    -- =========================================================================
    let isMMUIdle  := mmuStateReg === 0#3
    let isTLBLookup := mmuStateReg === 1#3
    let isPTWWalk  := mmuStateReg === 2#3
    let isMMUDone  := mmuStateReg === 3#3
    let isMMUFault := mmuStateReg === 4#3

    -- =========================================================================
    -- TLB Lookup (4-entry fully-associative)
    -- =========================================================================
    -- TLB hit for each entry: valid AND vpn match
    -- For megapages, only compare top 10 bits of VPN
    let tlb0FullMatch := tlb0VPN === vpn
    let tlb0MegaMatch := (tlb0VPN.map (BitVec.extractLsb' 10 10 ·)) === (vpn.map (BitVec.extractLsb' 10 10 ·))
    let tlb0VPNMatch := Signal.mux tlb0Mega tlb0MegaMatch tlb0FullMatch
    let tlb0Hit := tlb0Valid &&& tlb0VPNMatch

    let tlb1FullMatch := tlb1VPN === vpn
    let tlb1MegaMatch := (tlb1VPN.map (BitVec.extractLsb' 10 10 ·)) === (vpn.map (BitVec.extractLsb' 10 10 ·))
    let tlb1VPNMatch := Signal.mux tlb1Mega tlb1MegaMatch tlb1FullMatch
    let tlb1Hit := tlb1Valid &&& tlb1VPNMatch

    let tlb2FullMatch := tlb2VPN === vpn
    let tlb2MegaMatch := (tlb2VPN.map (BitVec.extractLsb' 10 10 ·)) === (vpn.map (BitVec.extractLsb' 10 10 ·))
    let tlb2VPNMatch := Signal.mux tlb2Mega tlb2MegaMatch tlb2FullMatch
    let tlb2Hit := tlb2Valid &&& tlb2VPNMatch

    let tlb3FullMatch := tlb3VPN === vpn
    let tlb3MegaMatch := (tlb3VPN.map (BitVec.extractLsb' 10 10 ·)) === (vpn.map (BitVec.extractLsb' 10 10 ·))
    let tlb3VPNMatch := Signal.mux tlb3Mega tlb3MegaMatch tlb3FullMatch
    let tlb3Hit := tlb3Valid &&& tlb3VPNMatch

    let anyTLBHit := (tlb0Hit ||| tlb1Hit) ||| (tlb2Hit ||| tlb3Hit)

    -- Priority mux for TLB output (entry 0 has highest priority)
    let tlbPPN := Signal.mux tlb0Hit tlb0PPN
      (Signal.mux tlb1Hit tlb1PPN
      (Signal.mux tlb2Hit tlb2PPN
      (Signal.mux tlb3Hit tlb3PPN
        (Signal.pure 0#22))))

    -- =========================================================================
    -- PTW FSM (inline): 0=IDLE, 1=LEVEL1, 2=LEVEL0, 3=DONE, 4=FAULT
    -- =========================================================================
    let ptwIsIdle := ptwStateReg === 0#3
    let ptwIsL1   := ptwStateReg === 1#3
    let ptwIsL0   := ptwStateReg === 2#3
    let ptwIsDone := ptwStateReg === 3#3
    let ptwIsFault := ptwStateReg === 4#3

    -- PTW request: on TLB miss during TLB_LOOKUP state
    let ptwReq := isTLBLookup &&& (~~~anyTLBHit)

    -- Latch vaddr on PTW start
    let ptwVaddrNext := Signal.mux (ptwIsIdle &&& ptwReq)
      vaddr ptwVaddrReg

    -- VPN extraction from latched vaddr
    let ptwVPN1 := ptwVaddrReg.map (BitVec.extractLsb' 22 10 ·)
    let ptwVPN0 := ptwVaddrReg.map (BitVec.extractLsb' 12 10 ·)

    -- PTE latch
    let ptwPteNext := Signal.mux memReady memRdata ptwPteReg

    -- PTE field decode
    let pteValid := (ptwPteReg.map (BitVec.extractLsb' 0 1 ·)) === 1#1
    let pteRBit := (ptwPteReg.map (BitVec.extractLsb' 1 1 ·)) === 1#1
    let pteXBit := (ptwPteReg.map (BitVec.extractLsb' 3 1 ·)) === 1#1
    let pteIsLeaf := pteRBit ||| pteXBit
    let pteInvalid := ~~~pteValid
    let ptePPNFull := ptwPteReg.map (BitVec.extractLsb' 10 22 ·)
    let pteFlags := ptwPteReg.map (BitVec.extractLsb' 0 8 ·)

    -- Memory address generation
    -- Level 1: satp.PPN * 4096 + VPN[1] * 4
    let satpPPNShifted := satpPPN ++ 0#10
    let ptwVPN1x4 := ptwVPN1 ++ 0#2
    let ptwVPN1Ext := 0#20 ++ ptwVPN1x4
    let l1Addr := satpPPNShifted + ptwVPN1Ext
    -- Level 0: PTE.PPN * 4096 + VPN[0] * 4
    let ptePPNShifted := ptePPNFull ++ 0#10
    let ptwVPN0x4 := ptwVPN0 ++ 0#2
    let ptwVPN0Ext := 0#20 ++ ptwVPN0x4
    let l0Addr := ptePPNShifted + ptwVPN0Ext

    let ptwMemAddr := Signal.mux ptwIsL1 l1Addr
      (Signal.mux ptwIsL0 l0Addr (Signal.pure 0#32))
    let ptwMemReq := ptwIsL1 ||| ptwIsL0

    -- PTW state transitions
    let nextFromPtwIdle := Signal.mux ptwReq (Signal.pure 1#3) (Signal.pure 0#3)
    let nextFromL1 := Signal.mux memReady
      (Signal.mux pteInvalid (Signal.pure 4#3)
      (Signal.mux pteIsLeaf (Signal.pure 3#3) (Signal.pure 2#3)))
      (Signal.pure 1#3)
    let nextFromL0 := Signal.mux memReady
      (Signal.mux pteInvalid (Signal.pure 4#3)
      (Signal.mux pteIsLeaf (Signal.pure 3#3) (Signal.pure 4#3)))
      (Signal.pure 2#3)
    let ptwStateNext := Signal.mux ptwIsIdle nextFromPtwIdle
      (Signal.mux ptwIsL1 nextFromL1
      (Signal.mux ptwIsL0 nextFromL0
        (Signal.pure 0#3)))

    -- Megapage tracking
    let ptwMegaNext := Signal.mux (ptwIsL1 &&& memReady)
      pteIsLeaf
      (Signal.mux ptwIsIdle (Signal.pure false) ptwMegaReg)

    -- =========================================================================
    -- TLB Fill on PTW completion
    -- =========================================================================
    let tlbFill := ptwIsDone
    let fillVPN := ptwVaddrReg.map (BitVec.extractLsb' 12 20 ·)

    -- Replacement pointer: which entry to fill
    let replIs0 := replPtrReg === 0#2
    let replIs1 := replPtrReg === 1#2
    let replIs2 := replPtrReg === 2#2
    let replIs3 := replPtrReg === 3#2
    let doFill0 := tlbFill &&& replIs0
    let doFill1 := tlbFill &&& replIs1
    let doFill2 := tlbFill &&& replIs2
    let doFill3 := tlbFill &&& replIs3

    -- TLB entry updates: sfence clears, fill sets, else hold
    let tlb0ValidNext := Signal.mux sfence (Signal.pure false)
      (Signal.mux doFill0 (Signal.pure true) tlb0Valid)
    let tlb0VPNNext := Signal.mux doFill0 fillVPN tlb0VPN
    let tlb0PPNNext := Signal.mux doFill0 ptePPNFull tlb0PPN
    let tlb0FlagsNext := Signal.mux doFill0 pteFlags tlb0Flags
    let tlb0MegaNext := Signal.mux doFill0 ptwMegaReg tlb0Mega

    let tlb1ValidNext := Signal.mux sfence (Signal.pure false)
      (Signal.mux doFill1 (Signal.pure true) tlb1Valid)
    let tlb1VPNNext := Signal.mux doFill1 fillVPN tlb1VPN
    let tlb1PPNNext := Signal.mux doFill1 ptePPNFull tlb1PPN
    let tlb1FlagsNext := Signal.mux doFill1 pteFlags tlb1Flags
    let tlb1MegaNext := Signal.mux doFill1 ptwMegaReg tlb1Mega

    let tlb2ValidNext := Signal.mux sfence (Signal.pure false)
      (Signal.mux doFill2 (Signal.pure true) tlb2Valid)
    let tlb2VPNNext := Signal.mux doFill2 fillVPN tlb2VPN
    let tlb2PPNNext := Signal.mux doFill2 ptePPNFull tlb2PPN
    let tlb2FlagsNext := Signal.mux doFill2 pteFlags tlb2Flags
    let tlb2MegaNext := Signal.mux doFill2 ptwMegaReg tlb2Mega

    let tlb3ValidNext := Signal.mux sfence (Signal.pure false)
      (Signal.mux doFill3 (Signal.pure true) tlb3Valid)
    let tlb3VPNNext := Signal.mux doFill3 fillVPN tlb3VPN
    let tlb3PPNNext := Signal.mux doFill3 ptePPNFull tlb3PPN
    let tlb3FlagsNext := Signal.mux doFill3 pteFlags tlb3Flags
    let tlb3MegaNext := Signal.mux doFill3 ptwMegaReg tlb3Mega

    -- Replacement pointer: increment on fill
    let replPtrNext := Signal.mux tlbFill
      (replPtrReg + 1#2) replPtrReg

    -- =========================================================================
    -- MMU State Transitions
    -- =========================================================================
    let needTranslate := reqValid &&& (~~~bypassMMU)
    let nextFromMMUIdle := Signal.mux needTranslate (Signal.pure 1#3) (Signal.pure 0#3)
    let nextFromTLBLookup := Signal.mux anyTLBHit (Signal.pure 3#3) (Signal.pure 2#3)
    let nextFromPTWWalk := Signal.mux ptwIsDone (Signal.pure 3#3)
      (Signal.mux ptwIsFault (Signal.pure 4#3) (Signal.pure 2#3))
    let mmuStateNext := Signal.mux isMMUIdle nextFromMMUIdle
      (Signal.mux isTLBLookup nextFromTLBLookup
      (Signal.mux isPTWWalk nextFromPTWWalk
        (Signal.pure 0#3)))

    -- Bundle all 26 registers
    bundleAll! [
      Signal.register 0#3 mmuStateNext,       -- 0
      Signal.register 0#3 ptwStateNext,        -- 1
      Signal.register 0#32 ptwVaddrNext,       -- 2
      Signal.register 0#32 ptwPteNext,         -- 3
      Signal.register false ptwMegaNext,       -- 4
      Signal.register 0#2 replPtrNext,         -- 5
      -- TLB entry 0
      Signal.register false tlb0ValidNext,     -- 6
      Signal.register 0#20 tlb0VPNNext,        -- 7
      Signal.register 0#22 tlb0PPNNext,        -- 8
      Signal.register 0#8 tlb0FlagsNext,       -- 9
      Signal.register false tlb0MegaNext,      -- 10
      -- TLB entry 1
      Signal.register false tlb1ValidNext,     -- 11
      Signal.register 0#20 tlb1VPNNext,        -- 12
      Signal.register 0#22 tlb1PPNNext,        -- 13
      Signal.register 0#8 tlb1FlagsNext,       -- 14
      Signal.register false tlb1MegaNext,      -- 15
      -- TLB entry 2
      Signal.register false tlb2ValidNext,     -- 16
      Signal.register 0#20 tlb2VPNNext,        -- 17
      Signal.register 0#22 tlb2PPNNext,        -- 18
      Signal.register 0#8 tlb2FlagsNext,       -- 19
      Signal.register false tlb2MegaNext,      -- 20
      -- TLB entry 3
      Signal.register false tlb3ValidNext,     -- 21
      Signal.register 0#20 tlb3VPNNext,        -- 22
      Signal.register 0#22 tlb3PPNNext,        -- 23
      Signal.register 0#8 tlb3FlagsNext,       -- 24
      Signal.register false tlb3MegaNext       -- 25
    ]

  -- Extract outputs from registered state
  let mmuStateReg := projN! mmu 26 0
  let isMMUIdle := mmuStateReg === 0#3
  let isMMUDone := mmuStateReg === 3#3
  let isMMUFault := mmuStateReg === 4#3

  let ptwStateReg := projN! mmu 26 1
  let ptwIsL1 := ptwStateReg === 1#3
  let ptwIsL0 := ptwStateReg === 2#3
  let ptwVaddrReg := projN! mmu 26 2
  let ptwPteReg := projN! mmu 26 3
  let ptePPNFull := ptwPteReg.map (BitVec.extractLsb' 10 22 ·)

  -- TLB hit recalc for output
  let tlb0Valid := projN! mmu 26 6
  let tlb0VPN := projN! mmu 26 7
  let tlb0PPN := projN! mmu 26 8
  let tlb0Mega := projN! mmu 26 10
  let tlb0FullMatch := tlb0VPN === vpn
  let tlb0MegaMatch := (tlb0VPN.map (BitVec.extractLsb' 10 10 ·)) === (vpn.map (BitVec.extractLsb' 10 10 ·))
  let tlb0VPNMatch := Signal.mux tlb0Mega tlb0MegaMatch tlb0FullMatch
  let tlb0Hit := tlb0Valid &&& tlb0VPNMatch

  -- Physical address output
  -- For 4KB pages: {ppn[19:0], offset[11:0]}
  let tlb0PPNLow := tlb0PPN.map (BitVec.extractLsb' 0 20 ·)
  let tlbPAddr := tlb0PPNLow ++ pageOffset
  let ptePPNLow := ptePPNFull.map (BitVec.extractLsb' 0 20 ·)
  let ptwPAddr := ptePPNLow ++ pageOffset
  let translatedAddr := Signal.mux tlb0Hit tlbPAddr ptwPAddr
  let paddr := Signal.mux bypassMMU vaddr translatedAddr

  -- Output signals
  let bypassReady := reqValid &&& bypassMMU
  let ready := bypassReady ||| isMMUDone
  let fault := isMMUFault

  -- Memory interface
  let satpPPN_out := satp.map (BitVec.extractLsb' 0 22 ·)
  let ptwVPN1_out := ptwVaddrReg.map (BitVec.extractLsb' 22 10 ·)
  let ptwVPN0_out := ptwVaddrReg.map (BitVec.extractLsb' 12 10 ·)
  let satpPPNShifted_out := satpPPN_out ++ 0#10
  let ptwVPN1x4_out := ptwVPN1_out ++ 0#2
  let ptwVPN1Ext_out := 0#20 ++ ptwVPN1x4_out
  let l1Addr := satpPPNShifted_out + ptwVPN1Ext_out
  let ptePPNShifted_out := ptePPNFull ++ 0#10
  let ptwVPN0x4_out := ptwVPN0_out ++ 0#2
  let ptwVPN0Ext_out := 0#20 ++ ptwVPN0x4_out
  let l0Addr := ptePPNShifted_out + ptwVPN0Ext_out
  let memAddr := Signal.mux ptwIsL1 l1Addr
    (Signal.mux ptwIsL0 l0Addr (Signal.pure 0#32))
  let memReq := ptwIsL1 ||| ptwIsL0

  -- Stall: MMU busy and not bypass
  let mmuBusy := ~~~isMMUIdle
  let stall := mmuBusy &&& (~~~bypassMMU)

  bundleAll! [paddr, ready, fault, memAddr, memReq, stall]

#synthesizeVerilog mmuTopSignal

end Sparkle.IP.RV32.MMU
