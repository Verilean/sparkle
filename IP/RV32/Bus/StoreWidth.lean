/-
  RV32 store byte-enable masks — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (~lines 535..546). Computes
  the per-byte write-enable mask given the store width (funct3) and
  the low two bits of the effective address.

  Spec (RISC-V unprivileged spec, §2.6 Loads and Stores):

  | funct3[1:0] | width | addr[1:0]=0 | addr[1:0]=1 | addr[1:0]=2 | addr[1:0]=3 |
  |-------------|-------|-------------|-------------|-------------|-------------|
  | 00 (SB)     | byte  | b0          | b1          | b2          | b3          |
  | 01 (SH)     | half  | b0,b1       | (UB)        | b2,b3       | (UB)        |
  | 10 (SW)     | word  | b0,b1,b2,b3 | (UB)        | (UB)        | (UB)        |

  "(UB)" = misaligned access, not modeled here; we don't define
  trap-on-misalignment. The hardware just produces whatever the
  formulas below evaluate to and the kernel is expected to align.

  The encoding in `SoC.lean` simplifies to:

      b0we = SW ∨ (SH ∧ low) ∨ (SB ∧ off=0)
      b1we = SW ∨ (SH ∧ low) ∨ (SB ∧ off=1)
      b2we = SW ∨ (SH ∧ high) ∨ (SB ∧ off=2)
      b3we = SW ∨ (SH ∧ high) ∨ (SB ∧ off=3)

  where `low = (addr[1] = 0)` and `high = ¬low`. We capture the same
  formulas here as pure Booleans and prove the spec-table.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Bus

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure byte-enable predicates

  Inputs:
    * `isSB`, `isSH`, `isSW` — width predicates (mutually exclusive
      assuming a well-formed store; we don't enforce mutex here).
    * `storeByteOff0..3` — `addr[1:0] = i` (mutually exclusive).
    * `storeHalfLow` — `addr[1] = 0`.

  Output: per-byte write-enable.
-/

/-- Byte-0 write enable. -/
@[inline] def b0wePure
    (isSB isSH isSW storeHalfLow storeByteOff0 : Bool) : Bool :=
  isSW || (isSH && storeHalfLow) || (isSB && storeByteOff0)

/-- Byte-1 write enable. -/
@[inline] def b1wePure
    (isSB isSH isSW storeHalfLow storeByteOff1 : Bool) : Bool :=
  isSW || (isSH && storeHalfLow) || (isSB && storeByteOff1)

/-- Byte-2 write enable. `storeHalfHigh = !storeHalfLow`. -/
@[inline] def b2wePure
    (isSB isSH isSW storeHalfHigh storeByteOff2 : Bool) : Bool :=
  isSW || (isSH && storeHalfHigh) || (isSB && storeByteOff2)

/-- Byte-3 write enable. -/
@[inline] def b3wePure
    (isSB isSH isSW storeHalfHigh storeByteOff3 : Bool) : Bool :=
  isSW || (isSH && storeHalfHigh) || (isSB && storeByteOff3)

/-! ## Spec invariants — closed by `decide` -/

/-- SW asserts every byte enable. -/
@[simp] theorem b0we_SW
    (isSB isSH storeHalfLow storeByteOff0 : Bool) :
    b0wePure isSB isSH true storeHalfLow storeByteOff0 = true := by
  revert isSB isSH storeHalfLow storeByteOff0; decide

@[simp] theorem b1we_SW
    (isSB isSH storeHalfLow storeByteOff1 : Bool) :
    b1wePure isSB isSH true storeHalfLow storeByteOff1 = true := by
  revert isSB isSH storeHalfLow storeByteOff1; decide

@[simp] theorem b2we_SW
    (isSB isSH storeHalfHigh storeByteOff2 : Bool) :
    b2wePure isSB isSH true storeHalfHigh storeByteOff2 = true := by
  revert isSB isSH storeHalfHigh storeByteOff2; decide

@[simp] theorem b3we_SW
    (isSB isSH storeHalfHigh storeByteOff3 : Bool) :
    b3wePure isSB isSH true storeHalfHigh storeByteOff3 = true := by
  revert isSB isSH storeHalfHigh storeByteOff3; decide

/-- SH with `addr[1] = 0` asserts byte 0 and byte 1. -/
@[simp] theorem b0we_SH_low (storeByteOff0 : Bool) :
    b0wePure false true false true storeByteOff0 = true := by
  revert storeByteOff0; decide

@[simp] theorem b1we_SH_low (storeByteOff1 : Bool) :
    b1wePure false true false true storeByteOff1 = true := by
  revert storeByteOff1; decide

/-- SH with `addr[1] = 0` does NOT assert bytes 2 or 3. -/
@[simp] theorem b2we_SH_low_clear (storeByteOff2 : Bool) :
    b2wePure false true false false storeByteOff2 = false := by
  revert storeByteOff2; decide

@[simp] theorem b3we_SH_low_clear (storeByteOff3 : Bool) :
    b3wePure false true false false storeByteOff3 = false := by
  revert storeByteOff3; decide

/-- SH with `addr[1] = 1` asserts byte 2 and byte 3. -/
@[simp] theorem b2we_SH_high (storeByteOff2 : Bool) :
    b2wePure false true false true storeByteOff2 = true := by
  revert storeByteOff2; decide

@[simp] theorem b3we_SH_high (storeByteOff3 : Bool) :
    b3wePure false true false true storeByteOff3 = true := by
  revert storeByteOff3; decide

/-- SB with `addr[1:0] = 0` asserts only byte 0. -/
theorem sb_off0_only_byte0 :
    b0wePure true false false false true = true ∧
    b1wePure true false false false false = false ∧
    b2wePure true false false false false = false ∧
    b3wePure true false false false false = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- SB with `addr[1:0] = 1` asserts only byte 1. -/
theorem sb_off1_only_byte1 :
    b0wePure true false false false false = false ∧
    b1wePure true false false false true = true ∧
    b2wePure true false false false false = false ∧
    b3wePure true false false false false = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- SB with `addr[1:0] = 2` asserts only byte 2. -/
theorem sb_off2_only_byte2 :
    b0wePure true false false false false = false ∧
    b1wePure true false false false false = false ∧
    b2wePure true false false false true = true ∧
    b3wePure true false false false false = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- SB with `addr[1:0] = 3` asserts only byte 3. -/
theorem sb_off3_only_byte3 :
    b0wePure true false false false false = false ∧
    b1wePure true false false false false = false ∧
    b2wePure true false false false false = false ∧
    b3wePure true false false false true = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- No-op when no width predicate fires (decoder-error case). -/
@[simp] theorem b0we_nostore
    (storeHalfLow storeByteOff0 : Bool) :
    b0wePure false false false storeHalfLow storeByteOff0 = false := by
  revert storeHalfLow storeByteOff0; decide

/-! ## Composite spec — exhaustive over Bool^5 -/

theorem b0wePure_spec :
    ∀ (isSB isSH isSW storeHalfLow storeByteOff0 : Bool),
      b0wePure isSB isSH isSW storeHalfLow storeByteOff0 =
        (isSW || (isSH && storeHalfLow) || (isSB && storeByteOff0)) := by
  decide

theorem b1wePure_spec :
    ∀ (isSB isSH isSW storeHalfLow storeByteOff1 : Bool),
      b1wePure isSB isSH isSW storeHalfLow storeByteOff1 =
        (isSW || (isSH && storeHalfLow) || (isSB && storeByteOff1)) := by
  decide

theorem b2wePure_spec :
    ∀ (isSB isSH isSW storeHalfHigh storeByteOff2 : Bool),
      b2wePure isSB isSH isSW storeHalfHigh storeByteOff2 =
        (isSW || (isSH && storeHalfHigh) || (isSB && storeByteOff2)) := by
  decide

theorem b3wePure_spec :
    ∀ (isSB isSH isSW storeHalfHigh storeByteOff3 : Bool),
      b3wePure isSB isSH isSW storeHalfHigh storeByteOff3 =
        (isSW || (isSH && storeHalfHigh) || (isSB && storeByteOff3)) := by
  decide

/-! ## Signal-level wrappers -/

def b0weSignal {dom : DomainConfig}
    (isSB isSH isSW storeHalfLow storeByteOff0 : Signal dom Bool)
    : Signal dom Bool :=
  isSW ||| ((isSH &&& storeHalfLow) ||| (isSB &&& storeByteOff0))

def b1weSignal {dom : DomainConfig}
    (isSB isSH isSW storeHalfLow storeByteOff1 : Signal dom Bool)
    : Signal dom Bool :=
  isSW ||| ((isSH &&& storeHalfLow) ||| (isSB &&& storeByteOff1))

def b2weSignal {dom : DomainConfig}
    (isSB isSH isSW storeHalfHigh storeByteOff2 : Signal dom Bool)
    : Signal dom Bool :=
  isSW ||| ((isSH &&& storeHalfHigh) ||| (isSB &&& storeByteOff2))

def b3weSignal {dom : DomainConfig}
    (isSB isSH isSW storeHalfHigh storeByteOff3 : Signal dom Bool)
    : Signal dom Bool :=
  isSW ||| ((isSH &&& storeHalfHigh) ||| (isSB &&& storeByteOff3))

/-! ## Per-lane DRAM-write enable

  Each of the 4 byte lanes' actual WE is `dmem_we ∧ bNwe`:
    - `dmem_we` is the gating term (= memWrite + DMEM + ¬TLBmiss + ¬scExFails).
    - `bNwe` is the funct3+addr-derived per-lane enable from the
      width predicates above.

  Both are required for the byte to commit.
-/

@[inline] def byteWePure (dmem_we bNwe : Bool) : Bool :=
  dmem_we && bNwe

@[simp] theorem byteWe_no_dmem (bNwe : Bool) :
    byteWePure false bNwe = false := rfl

@[simp] theorem byteWe_no_lane (dmem_we : Bool) :
    byteWePure dmem_we false = false := by
  unfold byteWePure; cases dmem_we <;> rfl

@[simp] theorem byteWe_active : byteWePure true true = true := rfl

theorem byteWePure_spec (dmem_we bNwe : Bool) :
    byteWePure dmem_we bNwe = (dmem_we && bNwe) := rfl

def byteWeSignal {dom : DomainConfig}
    (dmem_we bNwe : Signal dom Bool) : Signal dom Bool :=
  dmem_we &&& bNwe

end Sparkle.IP.RV32.Bus
