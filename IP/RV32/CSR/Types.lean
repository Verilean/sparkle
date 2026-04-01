/-
  RV32I CSR Types and Constants

  Defines CSR addresses, field layouts, exception/interrupt cause codes,
  and CLINT memory map for M-mode and S-mode operation.
-/

namespace Sparkle.IP.RV32.CSR

-- ============================================================================
-- M-mode CSR Addresses (12-bit)
-- ============================================================================

def csrMSTATUS   : Nat := 0x300
def csrMISA      : Nat := 0x301
def csrMEDELEG   : Nat := 0x302
def csrMIDELEG   : Nat := 0x303
def csrMIE       : Nat := 0x304
def csrMTVEC     : Nat := 0x305
def csrMCOUNTEREN : Nat := 0x306
def csrMSCRATCH  : Nat := 0x340
def csrMEPC      : Nat := 0x341
def csrMCAUSE    : Nat := 0x342
def csrMTVAL     : Nat := 0x343
def csrMIP       : Nat := 0x344

-- M-mode read-only CSRs
def csrMHARTID   : Nat := 0xF14

-- ============================================================================
-- S-mode CSR Addresses (12-bit)
-- ============================================================================

def csrSSTATUS   : Nat := 0x100
def csrSIE       : Nat := 0x104
def csrSTVEC     : Nat := 0x105
def csrSCOUNTEREN : Nat := 0x106
def csrSSCRATCH  : Nat := 0x140
def csrSEPC      : Nat := 0x141
def csrSCAUSE    : Nat := 0x142
def csrSTVAL     : Nat := 0x143
def csrSIP       : Nat := 0x144
def csrSATP      : Nat := 0x180

-- ============================================================================
-- MSTATUS Field Bit Positions
-- ============================================================================

/-- Machine Interrupt Enable -/
def mstatusMIE   : Nat := 3
/-- Machine Previous Interrupt Enable -/
def mstatusMPIE  : Nat := 7
/-- Supervisor Previous Privilege (1 bit at position 8) -/
def mstatusSPP   : Nat := 8
/-- Machine Previous Privilege (2 bits at positions 12:11) -/
def mstatusMPP_LO : Nat := 11
def mstatusMPP_HI : Nat := 12
/-- Supervisor Interrupt Enable -/
def mstatusSIE   : Nat := 1
/-- Supervisor Previous Interrupt Enable -/
def mstatusSPIE  : Nat := 5
/-- Modify Privilege (Make eXecutable Readable) -/
def mstatusMXR   : Nat := 19
/-- Supervisor User Memory access -/
def mstatusSUM   : Nat := 18
/-- Trap Virtual Memory -/
def mstatusTVM   : Nat := 20
/-- Timeout Wait (for WFI in S-mode) -/
def mstatusTW    : Nat := 21
/-- Trap SRET -/
def mstatusTSR   : Nat := 22

-- ============================================================================
-- MISA value: RV32I
-- ============================================================================

/-- MISA value: MXL=1 (RV32), I extension bit set -/
def misaValue : Nat := 0x40000100

-- ============================================================================
-- Exception Cause Codes (synchronous, bit 31 = 0)
-- ============================================================================

def causeINSTR_MISALIGN : Nat := 0
def causeINSTR_FAULT    : Nat := 1
def causeILLEGAL        : Nat := 2
def causeEBREAK         : Nat := 3
def causeLOAD_MISALIGN  : Nat := 4
def causeLOAD_FAULT     : Nat := 5
def causeSTORE_MISALIGN : Nat := 6
def causeSTORE_FAULT    : Nat := 7
def causeECALL_U        : Nat := 8
def causeECALL_S        : Nat := 9
def causeECALL_M        : Nat := 11
def causeINSTR_PAGE_FAULT : Nat := 12
def causeLOAD_PAGE_FAULT  : Nat := 13
def causeSTORE_PAGE_FAULT : Nat := 15

-- ============================================================================
-- Interrupt Cause Codes (asynchronous, bit 31 = 1)
-- ============================================================================

def causeS_SW_INT    : Nat := 0x80000001
def causeM_SW_INT    : Nat := 0x80000003
def causeS_TIMER_INT : Nat := 0x80000005
def causeM_TIMER_INT : Nat := 0x80000007
def causeS_EXT_INT   : Nat := 0x80000009
def causeM_EXT_INT   : Nat := 0x8000000B

-- ============================================================================
-- MIE / MIP Bit Positions
-- ============================================================================

/-- Supervisor Software Interrupt -/
def mieSSIE : Nat := 1
/-- Machine Software Interrupt -/
def mieMSIE : Nat := 3
/-- Supervisor Timer Interrupt -/
def mieSTIE : Nat := 5
/-- Machine Timer Interrupt -/
def mieMTIE : Nat := 7
/-- Supervisor External Interrupt -/
def mieSEIE : Nat := 9
/-- Machine External Interrupt -/
def mieMEIE : Nat := 11

-- ============================================================================
-- Privilege Levels
-- ============================================================================

def privU : Nat := 0  -- User
def privS : Nat := 1  -- Supervisor
def privM : Nat := 3  -- Machine

-- ============================================================================
-- CLINT Memory Map (Base: 0x02000000)
-- ============================================================================

def clintBase     : Nat := 0x02000000
def clintMSIP     : Nat := 0x0000     -- Software interrupt pending (bit 0)
def clintMTIMECMP_LO : Nat := 0x4000  -- Timer compare low 32 bits
def clintMTIMECMP_HI : Nat := 0x4004  -- Timer compare high 32 bits
def clintMTIME_LO : Nat := 0xBFF8     -- Timer counter low 32 bits
def clintMTIME_HI : Nat := 0xBFFC     -- Timer counter high 32 bits

-- ============================================================================
-- SATP Fields (Sv32)
-- ============================================================================

/-- SATP MODE bit (bit 31): 0 = bare, 1 = Sv32 -/
def satpMODE : Nat := 31
/-- SATP ASID field: bits [30:22] -/
def satpASID_LO : Nat := 22
def satpASID_HI : Nat := 30
/-- SATP PPN field: bits [21:0] -/
def satpPPN_HI : Nat := 21

-- ============================================================================
-- Sv32 Page Table Entry Fields
-- ============================================================================

/-- PTE Valid bit -/
def pteV : Nat := 0
/-- PTE Read permission -/
def pteR : Nat := 1
/-- PTE Write permission -/
def pteW : Nat := 2
/-- PTE Execute permission -/
def pteX : Nat := 3
/-- PTE User-accessible -/
def pteU : Nat := 4
/-- PTE Global mapping -/
def pteG : Nat := 5
/-- PTE Accessed -/
def pteA : Nat := 6
/-- PTE Dirty -/
def pteD : Nat := 7

-- ============================================================================
-- CSR Wire Structures (for circuit integration)
-- ============================================================================

/-- Wires connecting the CSR file to the pipeline -/
structure CSRWires where
  -- Read port
  csrReadData  : String  -- CSR read data output (32-bit)
  -- Interrupt signals
  mipMTIP      : String  -- Timer interrupt pending
  mipMSIP      : String  -- Software interrupt pending
  mieMTIE      : String  -- Timer interrupt enable
  mieMSIE      : String  -- Software interrupt enable
  mstatusMIE   : String  -- Global interrupt enable
  -- Trap vector
  mtvecBase    : String  -- Trap vector base address
  -- EPC for MRET
  mepc         : String  -- Exception PC (for MRET)
  deriving Repr

/-- Wires connecting the CLINT to the core -/
structure CLINTWires where
  timerIrq : String  -- Timer interrupt signal
  swIrq    : String  -- Software interrupt signal
  readData : String  -- Bus read data
  deriving Repr

/-- Page table walker state -/
inductive PTWState where
  | idle   : PTWState
  | level1 : PTWState
  | level0 : PTWState
  | done   : PTWState
  | fault  : PTWState
  deriving Repr, BEq, DecidableEq

/-- PTW state encoding to 3-bit value -/
def PTWState.toBitVec3 : PTWState → BitVec 3
  | .idle   => 0b000#3
  | .level1 => 0b001#3
  | .level0 => 0b010#3
  | .done   => 0b011#3
  | .fault  => 0b100#3

end Sparkle.IP.RV32.CSR
