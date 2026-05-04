/-
  RV32 CLINT register decode — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 733..749 read side; lines
  1323..1343 write/state-update side). The CLINT (Core-Local
  INTerruptor) is a memory-mapped peripheral at PA 0x02000000 with
  five visible registers:

      offset  | register   | width | purpose
      --------|------------|-------|------------------------
      0x0000  | msip       | 32    | M-mode software-interrupt
      0x4000  | mtimecmpLo | 32    | timer compare low
      0x4004  | mtimecmpHi | 32    | timer compare high
      0xBFF8  | mtimeLo    | 32    | mtime low
      0xBFFC  | mtimeHi    | 32    | mtime high

  This file extracts:
    1. The five address-match predicates (each a 16-bit offset
       comparison against the constant).
    2. The 5-way read mux producing `clintRdata`.

  Spec invariants:
    - Pairwise disjointness: the five offset constants are distinct
      (per the SiFive CLINT spec, §1).
    - Read mux is exhaustive in the five matches (default = 0, for
      out-of-range CLINT accesses).

  Reference: SiFive CLINT spec / RISC-V priv §3.1.10 (mtimecmp) and
  §3.1.6 (msip via ACLINT).
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.CLINT

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure offset-match predicates -/

/-- msip register: PA = 0x0200_0000. -/
@[inline] def msipMatchPure (offset : BitVec 16) : Bool :=
  offset == 0x0000#16

/-- mtimecmp[31:0]: PA = 0x0200_4000. -/
@[inline] def mtimecmpLoMatchPure (offset : BitVec 16) : Bool :=
  offset == 0x4000#16

/-- mtimecmp[63:32]: PA = 0x0200_4004. -/
@[inline] def mtimecmpHiMatchPure (offset : BitVec 16) : Bool :=
  offset == 0x4004#16

/-- mtime[31:0]: PA = 0x0200_BFF8. -/
@[inline] def mtimeLoMatchPure (offset : BitVec 16) : Bool :=
  offset == 0xBFF8#16

/-- mtime[63:32]: PA = 0x0200_BFFC. -/
@[inline] def mtimeHiMatchPure (offset : BitVec 16) : Bool :=
  offset == 0xBFFC#16

/-! ## Pairwise disjointness — closed by `bv_decide` -/

theorem msip_mtimecmpLo_disjoint (offset : BitVec 16) :
    !(msipMatchPure offset && mtimecmpLoMatchPure offset) = true := by
  unfold msipMatchPure mtimecmpLoMatchPure
  revert offset; bv_decide

theorem msip_mtimecmpHi_disjoint (offset : BitVec 16) :
    !(msipMatchPure offset && mtimecmpHiMatchPure offset) = true := by
  unfold msipMatchPure mtimecmpHiMatchPure
  revert offset; bv_decide

theorem msip_mtimeLo_disjoint (offset : BitVec 16) :
    !(msipMatchPure offset && mtimeLoMatchPure offset) = true := by
  unfold msipMatchPure mtimeLoMatchPure
  revert offset; bv_decide

theorem msip_mtimeHi_disjoint (offset : BitVec 16) :
    !(msipMatchPure offset && mtimeHiMatchPure offset) = true := by
  unfold msipMatchPure mtimeHiMatchPure
  revert offset; bv_decide

theorem mtimecmpLo_mtimecmpHi_disjoint (offset : BitVec 16) :
    !(mtimecmpLoMatchPure offset && mtimecmpHiMatchPure offset) = true := by
  unfold mtimecmpLoMatchPure mtimecmpHiMatchPure
  revert offset; bv_decide

theorem mtimecmpLo_mtimeLo_disjoint (offset : BitVec 16) :
    !(mtimecmpLoMatchPure offset && mtimeLoMatchPure offset) = true := by
  unfold mtimecmpLoMatchPure mtimeLoMatchPure
  revert offset; bv_decide

theorem mtimecmpLo_mtimeHi_disjoint (offset : BitVec 16) :
    !(mtimecmpLoMatchPure offset && mtimeHiMatchPure offset) = true := by
  unfold mtimecmpLoMatchPure mtimeHiMatchPure
  revert offset; bv_decide

theorem mtimecmpHi_mtimeLo_disjoint (offset : BitVec 16) :
    !(mtimecmpHiMatchPure offset && mtimeLoMatchPure offset) = true := by
  unfold mtimecmpHiMatchPure mtimeLoMatchPure
  revert offset; bv_decide

theorem mtimecmpHi_mtimeHi_disjoint (offset : BitVec 16) :
    !(mtimecmpHiMatchPure offset && mtimeHiMatchPure offset) = true := by
  unfold mtimecmpHiMatchPure mtimeHiMatchPure
  revert offset; bv_decide

theorem mtimeLo_mtimeHi_disjoint (offset : BitVec 16) :
    !(mtimeLoMatchPure offset && mtimeHiMatchPure offset) = true := by
  unfold mtimeLoMatchPure mtimeHiMatchPure
  revert offset; bv_decide

/-! ## Pure read-mux -/

/-- 5-way priority read mux. Order matches `SoC.lean` (msip > mtimecmpLo
    > mtimecmpHi > mtimeLo > mtimeHi). Out-of-range offsets return 0. -/
@[inline] def clintRdataPure
    (msipMatch mtimecmpLoMatch mtimecmpHiMatch mtimeLoMatch mtimeHiMatch : Bool)
    (msipReg mtimecmpLoReg mtimecmpHiReg mtimeLoReg mtimeHiReg : BitVec 32)
    : BitVec 32 :=
  if msipMatch then msipReg
  else if mtimecmpLoMatch then mtimecmpLoReg
  else if mtimecmpHiMatch then mtimecmpHiReg
  else if mtimeLoMatch then mtimeLoReg
  else if mtimeHiMatch then mtimeHiReg
  else 0#32

/-! ## Spec invariants — closed by `decide` / `rfl` -/

@[simp] theorem clintRdata_default
    (msipReg mtimecmpLoReg mtimecmpHiReg mtimeLoReg mtimeHiReg : BitVec 32) :
    clintRdataPure false false false false false
      msipReg mtimecmpLoReg mtimecmpHiReg mtimeLoReg mtimeHiReg = 0#32 := by
  rfl

@[simp] theorem clintRdata_msip
    (mtimecmpLoMatch mtimecmpHiMatch mtimeLoMatch mtimeHiMatch : Bool)
    (msipReg mtimecmpLoReg mtimecmpHiReg mtimeLoReg mtimeHiReg : BitVec 32) :
    clintRdataPure true mtimecmpLoMatch mtimecmpHiMatch mtimeLoMatch mtimeHiMatch
      msipReg mtimecmpLoReg mtimecmpHiReg mtimeLoReg mtimeHiReg = msipReg := by
  rfl

@[simp] theorem clintRdata_mtimecmpLo
    (mtimecmpHiMatch mtimeLoMatch mtimeHiMatch : Bool)
    (msipReg mtimecmpLoReg mtimecmpHiReg mtimeLoReg mtimeHiReg : BitVec 32) :
    clintRdataPure false true mtimecmpHiMatch mtimeLoMatch mtimeHiMatch
      msipReg mtimecmpLoReg mtimecmpHiReg mtimeLoReg mtimeHiReg = mtimecmpLoReg := by
  rfl

@[simp] theorem clintRdata_mtimecmpHi
    (mtimeLoMatch mtimeHiMatch : Bool)
    (msipReg mtimecmpLoReg mtimecmpHiReg mtimeLoReg mtimeHiReg : BitVec 32) :
    clintRdataPure false false true mtimeLoMatch mtimeHiMatch
      msipReg mtimecmpLoReg mtimecmpHiReg mtimeLoReg mtimeHiReg = mtimecmpHiReg := by
  rfl

@[simp] theorem clintRdata_mtimeLo
    (mtimeHiMatch : Bool)
    (msipReg mtimecmpLoReg mtimecmpHiReg mtimeLoReg mtimeHiReg : BitVec 32) :
    clintRdataPure false false false true mtimeHiMatch
      msipReg mtimecmpLoReg mtimecmpHiReg mtimeLoReg mtimeHiReg = mtimeLoReg := by
  rfl

@[simp] theorem clintRdata_mtimeHi
    (msipReg mtimecmpLoReg mtimecmpHiReg mtimeLoReg mtimeHiReg : BitVec 32) :
    clintRdataPure false false false false true
      msipReg mtimecmpLoReg mtimecmpHiReg mtimeLoReg mtimeHiReg = mtimeHiReg := by
  rfl

/-! ## Signal-level wrappers -/

def msipMatchSignal {dom : DomainConfig}
    (offset : Signal dom (BitVec 16)) : Signal dom Bool :=
  offset === 0x0000#16

def mtimecmpLoMatchSignal {dom : DomainConfig}
    (offset : Signal dom (BitVec 16)) : Signal dom Bool :=
  offset === 0x4000#16

def mtimecmpHiMatchSignal {dom : DomainConfig}
    (offset : Signal dom (BitVec 16)) : Signal dom Bool :=
  offset === 0x4004#16

def mtimeLoMatchSignal {dom : DomainConfig}
    (offset : Signal dom (BitVec 16)) : Signal dom Bool :=
  offset === 0xBFF8#16

def mtimeHiMatchSignal {dom : DomainConfig}
    (offset : Signal dom (BitVec 16)) : Signal dom Bool :=
  offset === 0xBFFC#16

def clintRdataSignal {dom : DomainConfig}
    (msipMatch mtimecmpLoMatch mtimecmpHiMatch mtimeLoMatch mtimeHiMatch : Signal dom Bool)
    (msipReg mtimecmpLoReg mtimecmpHiReg mtimeLoReg mtimeHiReg : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  Signal.mux msipMatch msipReg
    (Signal.mux mtimecmpLoMatch mtimecmpLoReg
    (Signal.mux mtimecmpHiMatch mtimecmpHiReg
    (Signal.mux mtimeLoMatch mtimeLoReg
    (Signal.mux mtimeHiMatch mtimeHiReg
      (Signal.pure 0#32)))))

end Sparkle.IP.RV32.CLINT
