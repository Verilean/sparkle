/-
  RV32 D-side miss tracking — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 1747..1749). Three
  state-bit latches that capture the faulting D-side load/store's
  metadata when a TLB miss fires:

    dMissPCNext       — captures `idex_pc`         (for mepc/sepc)
    dMissVaddrNext    — captures `alu_result_approx` (for mtval/stval)
    dMissIsStoreNext  — captures `idex_memWrite`   (for cause selection
                                                    13=load / 15=store)

  All three follow the same pattern:

      next = if dTLBMiss then captureValue else heldValue

  This is the *capture-on-event-else-hold* idiom. The
  combinational spec is trivial; what matters is that we never
  accidentally update these on a non-dTLBMiss cycle (which would
  corrupt the trap context for an in-flight fault).

  Note: These three latches must be updated in concert (same
  cycle's dTLBMiss latches all three), otherwise the trap
  context becomes inconsistent (e.g. dMissPC for one fault but
  dMissVaddr for another).

  Reference: docs/RV32_Architecture_Status.md §1.3 (D-side miss
  state) + commit 0e14494's dMMURedirect double-execution fix.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.MMU

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure capture-or-hold for BitVec 32 (PC / VAddr) -/

/-- Capture `newVal` on `dTLBMiss`, else hold `old`. -/
@[inline] def dMissCaptureBV32Pure
    (dTLBMiss : Bool) (newVal old : BitVec 32) : BitVec 32 :=
  if dTLBMiss then newVal else old

/-- Capture-Bool variant for `dMissIsStore`. -/
@[inline] def dMissCaptureBoolPure
    (dTLBMiss new old : Bool) : Bool :=
  if dTLBMiss then new else old

/-! ## Spec invariants — closed by `decide` / `rfl` -/

/-- No miss → hold the BitVec field. -/
@[simp] theorem dMissCaptureBV32_no_miss
    (newVal old : BitVec 32) :
    dMissCaptureBV32Pure false newVal old = old := by
  rfl

/-- Miss fires → capture the new value. -/
@[simp] theorem dMissCaptureBV32_miss
    (newVal old : BitVec 32) :
    dMissCaptureBV32Pure true newVal old = newVal := by
  rfl

/-- No miss → hold the Bool field. -/
@[simp] theorem dMissCaptureBool_no_miss
    (new old : Bool) :
    dMissCaptureBoolPure false new old = old := by
  rfl

/-- Miss fires → capture the new Bool. -/
@[simp] theorem dMissCaptureBool_miss
    (new old : Bool) :
    dMissCaptureBoolPure true new old = new := by
  rfl

/-! ## Joint capture spec

  All three capture functions agree on the same `dTLBMiss` event.
  This is what makes the trap context consistent — when we say "a
  fault was captured at cycle t with these PC/Vaddr/IsStore",
  it's because dTLBMiss fired at cycle t and all three latched
  together. -/

/-- Capture invariance: no miss → all three fields hold. -/
theorem dMiss_no_miss_holds_all
    (idex_pc alu_result old_pc old_vaddr : BitVec 32)
    (idex_memWrite old_isStore : Bool) :
    dMissCaptureBV32Pure false idex_pc old_pc = old_pc ∧
    dMissCaptureBV32Pure false alu_result old_vaddr = old_vaddr ∧
    dMissCaptureBoolPure false idex_memWrite old_isStore = old_isStore := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- Joint capture: miss → all three latch atomically. -/
theorem dMiss_miss_captures_all
    (idex_pc alu_result old_pc old_vaddr : BitVec 32)
    (idex_memWrite old_isStore : Bool) :
    dMissCaptureBV32Pure true idex_pc old_pc = idex_pc ∧
    dMissCaptureBV32Pure true alu_result old_vaddr = alu_result ∧
    dMissCaptureBoolPure true idex_memWrite old_isStore = idex_memWrite := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-! ## Composite specs -/

theorem dMissCaptureBV32Pure_spec :
    ∀ (dTLBMiss : Bool) (newVal old : BitVec 32),
      dMissCaptureBV32Pure dTLBMiss newVal old =
        (if dTLBMiss then newVal else old) := by
  intros; rfl

theorem dMissCaptureBoolPure_spec :
    ∀ (dTLBMiss new old : Bool),
      dMissCaptureBoolPure dTLBMiss new old =
        (if dTLBMiss then new else old) := by
  intros; rfl

/-! ## Signal-level wrappers -/

def dMissCaptureBV32Signal {dom : DomainConfig}
    (dTLBMiss : Signal dom Bool)
    (newVal old : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux dTLBMiss newVal old

def dMissCaptureBoolSignal {dom : DomainConfig}
    (dTLBMiss new old : Signal dom Bool) : Signal dom Bool :=
  Signal.mux dTLBMiss new old

end Sparkle.IP.RV32.MMU
