/-
  RV32 CLINT commit trap invariant — multi-cycle composite

  Combines two prior building blocks into the multi-cycle
  theorem "trap at cycle t → CLINT register unchanged at
  cycle t+1":

    1. `Pipeline/SuppressEXWB.lean::validEX_trap` (combinational):
         trap → validEX at t = false.

    2. `Bus/PeripheralWE.lean::peripheralWESignal_false_when_validEX_false`
       (combinational):
         validEX=false at t → peripheralWE at t = false.

    3. `CLINT/Decode.lean::clintRegWeSignal` (def):
         clintRegWe = clintWE ∧ regMatch.

    4. `CSR/Commit.lean::csrPlainReg_hold_when_we_false`
       (sequential):
         WE=false at t → CSR-reg at t+1 = old.val t.

  Together: trap at cycle t → CLINT-WE at t = false → CLINT
  register at t+1 = old.val t.

  Applies to all 5 CLINT registers in SoC.lean:
  msip/mtimecmpLo/mtimecmpHi/mtimeLo/mtimeHi.

  The mtimeLo/Hi case is interesting: their `old` is actually the
  incremented value `mtimeLoInc`/`mtimeHiInc`, so under "no CSR
  write" the time advances every cycle. The trap-suppression
  guarantee here is that the CSR *write* doesn't fire — the
  mtime increment continues normally.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.CSR.Commit
import IP.RV32.CLINT.Decode
import IP.RV32.Bus.PeripheralWE
import IP.RV32.Pipeline.SuppressEXWB

namespace Sparkle.IP.RV32.CLINT

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.RV32.Bus
open Sparkle.IP.RV32.CSR
open Sparkle.IP.RV32.Pipeline

/-! ## Multi-cycle composite -/

/-- **trap at cycle t → CLINT register at t+1 = old.val t.**

    The CLINT-WE is `clintWE ∧ regMatch`, where `clintWE =
    peripheralWESignal idex_memWrite isCLINT_ex validEX`. A trap
    clears validEX same-cycle, so peripheralWE is false, so the
    register WE is false, so the register holds. -/
theorem trap_holds_clintReg {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_memWrite isCLINT_ex regMatch : Signal dom Bool)
    (init : BitVec 32) (newVal old : Signal dom (BitVec 32)) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    -- Wire the WE the same way SoC.lean does:
    let clintWE :=
      peripheralWESignal idex_memWrite isCLINT_ex
        (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
    let regWE := clintRegWeSignal clintWE regMatch
    (csrPlainRegSignal init regWE newVal old).val (t + 1) = old.val t := by
  -- Step 1: validEX at t = false on trap.
  have h_validEX :
    (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect).val t = false := by
    rw [validEXSignal_eq_pure]
    rw [show trap_taken.val t = true from h_trap]
    exact validEX_trap (dTLBMiss.val t) (pendingWriteEn.val t)
      (mmuBusy.val t) (dMMURedirect.val t)
  -- Step 2: clintWE = peripheralWE is false (validEX=false).
  have h_clintWE :
    (peripheralWESignal idex_memWrite isCLINT_ex
      (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)).val t = false :=
    peripheralWESignal_false_when_validEX_false _ _ _ t h_validEX
  -- Step 3: clintRegWe = clintWE ∧ regMatch is false (clintWE=false).
  have h_regWE :
    (clintRegWeSignal
      (peripheralWESignal idex_memWrite isCLINT_ex
        (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect))
      regMatch).val t = false := by
    -- clintRegWeSignal is `&&&` over Signal Bool; reduce to Bool-and.
    show (Signal.ap (Signal.map (· && ·)
      (peripheralWESignal idex_memWrite isCLINT_ex
        (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)))
      regMatch).val t = false
    show ((peripheralWESignal idex_memWrite isCLINT_ex
      (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)).val t
      && regMatch.val t) = false
    rw [h_clintWE]
    rfl
  -- Step 4: register holds when WE=false.
  exact csrPlainReg_hold_when_we_false init _ newVal old t h_regWE

end Sparkle.IP.RV32.CLINT
