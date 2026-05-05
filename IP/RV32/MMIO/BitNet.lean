/-
  RV32 BitNet MMIO peripheral decode — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 768..780, 1363..1366).
  The BitNet peripheral is a Level-1a (dim=4, 1 layer) MMIO
  device at address bit 30 = 1 (i.e. 0x40000000+) with 3
  registers:

    offset  register   width  semantics
    ------  ---------  -----  -----------------------------
    0x0     status     32     read/write, latches a status word
    0x4     input      32     write-only, drives the BitNet
    0x8     output     32     read-only, BitNet's combinational
                              output (settled same cycle as input
                              latches)

  Reads of unmapped offsets return 0; writes are silently
  ignored.

  Per `IP/RV32/BitNetPeripheral.lean`, the BitNet itself is a
  combinational function from input → output, so the latched
  input register's value drives a same-cycle output.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.MMIO

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure offset matchers -/

/-- offset == 0x0 (status register). -/
@[inline] def mmioIsStatusPure (offset : BitVec 4) : Bool :=
  offset == 0x0#4

/-- offset == 0x4 (input register). -/
@[inline] def mmioIsInputPure (offset : BitVec 4) : Bool :=
  offset == 0x4#4

/-- offset == 0x8 (output register). -/
@[inline] def mmioIsOutputPure (offset : BitVec 4) : Bool :=
  offset == 0x8#4

/-! ## Pure rdata mux -/

/-- 3-way priority read mux: status > output > 0 (default). -/
@[inline] def mmioRdataPure
    (mmioIsStatus mmioIsOutput : Bool)
    (aiStatusReg bitnetOut : BitVec 32) : BitVec 32 :=
  if mmioIsStatus then aiStatusReg
  else if mmioIsOutput then bitnetOut
  else 0#32

/-! ## Pure write commits -/

/-- aiStatusReg next: write-on-status-match else hold. -/
@[inline] def aiStatusNextPure
    (mmioWE mmioIsStatus : Bool)
    (newVal aiStatusReg : BitVec 32) : BitVec 32 :=
  if mmioWE && mmioIsStatus then newVal else aiStatusReg

/-- aiInputReg next: write-on-input-match else hold. -/
@[inline] def aiInputNextPure
    (mmioWE mmioIsInput : Bool)
    (newVal aiInputReg : BitVec 32) : BitVec 32 :=
  if mmioWE && mmioIsInput then newVal else aiInputReg

/-! ## Spec invariants -/

/-- offset 0 → status. -/
@[simp] theorem mmioRdata_status
    (mmioIsOutput : Bool) (aiStatusReg bitnetOut : BitVec 32) :
    mmioRdataPure true mmioIsOutput aiStatusReg bitnetOut = aiStatusReg := by rfl

/-- offset 8 (no status match) → output. -/
@[simp] theorem mmioRdata_output (aiStatusReg bitnetOut : BitVec 32) :
    mmioRdataPure false true aiStatusReg bitnetOut = bitnetOut := by rfl

/-- offset other → 0. -/
@[simp] theorem mmioRdata_default (aiStatusReg bitnetOut : BitVec 32) :
    mmioRdataPure false false aiStatusReg bitnetOut = 0#32 := by rfl

/-- status / input / output are pairwise distinct offsets. -/
theorem mmio_offsets_pairwise_distinct (offset : BitVec 4) :
    !(mmioIsStatusPure offset && mmioIsInputPure offset) = true ∧
    !(mmioIsStatusPure offset && mmioIsOutputPure offset) = true ∧
    !(mmioIsInputPure offset && mmioIsOutputPure offset) = true := by
  unfold mmioIsStatusPure mmioIsInputPure mmioIsOutputPure
  refine ⟨?_, ?_, ?_⟩ <;> (revert offset; bv_decide)

/-! ### Write-commit spec -/

/-- aiStatusReg holds when WE is clear. -/
@[simp] theorem aiStatusNext_no_we
    (mmioIsStatus : Bool) (newVal aiStatusReg : BitVec 32) :
    aiStatusNextPure false mmioIsStatus newVal aiStatusReg = aiStatusReg := by
  unfold aiStatusNextPure
  cases mmioIsStatus <;> rfl

/-- aiStatusReg holds on offset mismatch. -/
@[simp] theorem aiStatusNext_no_match
    (mmioWE : Bool) (newVal aiStatusReg : BitVec 32) :
    aiStatusNextPure mmioWE false newVal aiStatusReg = aiStatusReg := by
  unfold aiStatusNextPure
  cases mmioWE <;> rfl

/-- aiStatusReg writes when both WE and offset match. -/
theorem aiStatusNext_writes (newVal aiStatusReg : BitVec 32) :
    aiStatusNextPure true true newVal aiStatusReg = newVal := by rfl

/-! ## Composite specs -/

theorem mmioRdataPure_spec
    (mmioIsStatus mmioIsOutput : Bool)
    (aiStatusReg bitnetOut : BitVec 32) :
    mmioRdataPure mmioIsStatus mmioIsOutput aiStatusReg bitnetOut =
      (if mmioIsStatus then aiStatusReg
       else if mmioIsOutput then bitnetOut
       else 0#32) := by rfl

/-! ## Signal-level wrappers -/

def mmioIsStatusSignal {dom : DomainConfig}
    (offset : Signal dom (BitVec 4)) : Signal dom Bool :=
  offset === 0x0#4

def mmioIsInputSignal {dom : DomainConfig}
    (offset : Signal dom (BitVec 4)) : Signal dom Bool :=
  offset === 0x4#4

def mmioIsOutputSignal {dom : DomainConfig}
    (offset : Signal dom (BitVec 4)) : Signal dom Bool :=
  offset === 0x8#4

def mmioRdataSignal {dom : DomainConfig}
    (mmioIsStatus mmioIsOutput : Signal dom Bool)
    (aiStatusReg bitnetOut : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux mmioIsStatus aiStatusReg
    (Signal.mux mmioIsOutput bitnetOut (Signal.pure 0#32))

def aiStatusNextSignal {dom : DomainConfig}
    (mmioWE mmioIsStatus : Signal dom Bool)
    (newVal aiStatusReg : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux (mmioWE &&& mmioIsStatus) newVal aiStatusReg

def aiInputNextSignal {dom : DomainConfig}
    (mmioWE mmioIsInput : Signal dom Bool)
    (newVal aiInputReg : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux (mmioWE &&& mmioIsInput) newVal aiInputReg

end Sparkle.IP.RV32.MMIO
