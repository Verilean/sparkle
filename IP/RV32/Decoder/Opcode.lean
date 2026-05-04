/-
  RV32 bare opcode predicates — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 1127..1135). Each
  RV32I instruction class is identified by its 7-bit opcode:

    isALUrr   0b0110011  R-type
    isALUimm  0b0010011  I-type ALU
    isLoad    0b0000011  LB/LH/LW/LBU/LHU
    isStore   0b0100011  SB/SH/SW
    isBranch  0b1100011  BEQ/BNE/BLT/BGE/BLTU/BGEU
    isLUI     0b0110111
    isAUIPC   0b0010111
    isJAL     0b1101111
    isJALR    0b1100111

  Each predicate is a single 7-bit equality; pairwise mutex
  follows from the generic `csrAddrEq_mutex` pattern (cf.
  `CSR/AddrDecoder.lean`).

  Companion to:
    * `Decoder/Control.lean` — derived control signals (aluSrcB,
      regWrite, etc.) that are unions/intersections of these.
    * `Decoder/System.lean` — SYSTEM-opcode sub-decoders.
    * `AMO/Decode.lean` — A-extension opcode (0b0101111).
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Decoder

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure opcode predicates -/

@[inline] def isALUrrPure (opcode : BitVec 7) : Bool :=
  opcode == 0b0110011#7

@[inline] def isALUimmPure (opcode : BitVec 7) : Bool :=
  opcode == 0b0010011#7

@[inline] def isLoadPure (opcode : BitVec 7) : Bool :=
  opcode == 0b0000011#7

@[inline] def isStorePure (opcode : BitVec 7) : Bool :=
  opcode == 0b0100011#7

@[inline] def isBranchPure (opcode : BitVec 7) : Bool :=
  opcode == 0b1100011#7

@[inline] def isLUIPure (opcode : BitVec 7) : Bool :=
  opcode == 0b0110111#7

@[inline] def isAUIPCPure (opcode : BitVec 7) : Bool :=
  opcode == 0b0010111#7

@[inline] def isJALPure (opcode : BitVec 7) : Bool :=
  opcode == 0b1101111#7

@[inline] def isJALRPure (opcode : BitVec 7) : Bool :=
  opcode == 0b1100111#7

/-! ## Pairwise mutex — closed by `bv_decide` -/

theorem isALUrr_isLoad_mutex (opcode : BitVec 7) :
    !(isALUrrPure opcode && isLoadPure opcode) = true := by
  unfold isALUrrPure isLoadPure
  revert opcode; bv_decide

theorem isLoad_isStore_mutex (opcode : BitVec 7) :
    !(isLoadPure opcode && isStorePure opcode) = true := by
  unfold isLoadPure isStorePure
  revert opcode; bv_decide

theorem isJAL_isJALR_mutex (opcode : BitVec 7) :
    !(isJALPure opcode && isJALRPure opcode) = true := by
  unfold isJALPure isJALRPure
  revert opcode; bv_decide

theorem isLUI_isAUIPC_mutex (opcode : BitVec 7) :
    !(isLUIPure opcode && isAUIPCPure opcode) = true := by
  unfold isLUIPure isAUIPCPure
  revert opcode; bv_decide

theorem isBranch_isJAL_mutex (opcode : BitVec 7) :
    !(isBranchPure opcode && isJALPure opcode) = true := by
  unfold isBranchPure isJALPure
  revert opcode; bv_decide

/-! ## Composite specs -/

theorem isALUrrPure_spec (opcode : BitVec 7) :
    isALUrrPure opcode = (opcode == 0b0110011#7) := by rfl

theorem isLoadPure_spec (opcode : BitVec 7) :
    isLoadPure opcode = (opcode == 0b0000011#7) := by rfl

/-! ## Signal-level wrappers -/

def isALUrrSignal {dom : DomainConfig}
    (opcode : Signal dom (BitVec 7)) : Signal dom Bool :=
  opcode === 0b0110011#7

def isALUimmSignal {dom : DomainConfig}
    (opcode : Signal dom (BitVec 7)) : Signal dom Bool :=
  opcode === 0b0010011#7

def isLoadSignal {dom : DomainConfig}
    (opcode : Signal dom (BitVec 7)) : Signal dom Bool :=
  opcode === 0b0000011#7

def isStoreSignal {dom : DomainConfig}
    (opcode : Signal dom (BitVec 7)) : Signal dom Bool :=
  opcode === 0b0100011#7

def isBranchSignal {dom : DomainConfig}
    (opcode : Signal dom (BitVec 7)) : Signal dom Bool :=
  opcode === 0b1100011#7

def isLUISignal {dom : DomainConfig}
    (opcode : Signal dom (BitVec 7)) : Signal dom Bool :=
  opcode === 0b0110111#7

def isAUIPCSignal {dom : DomainConfig}
    (opcode : Signal dom (BitVec 7)) : Signal dom Bool :=
  opcode === 0b0010111#7

def isJALSignal {dom : DomainConfig}
    (opcode : Signal dom (BitVec 7)) : Signal dom Bool :=
  opcode === 0b1101111#7

def isJALRSignal {dom : DomainConfig}
    (opcode : Signal dom (BitVec 7)) : Signal dom Bool :=
  opcode === 0b1100111#7

end Sparkle.IP.RV32.Decoder
