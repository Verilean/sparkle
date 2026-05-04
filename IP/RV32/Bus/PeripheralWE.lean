/-
  RV32 peripheral write-enable — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 1332, 1361, 1369). The
  three peripheral write-enables (CLINT, MMIO, UART) all share
  the same shape:

      peripheralWE = idex_memWrite ∧ targetMatch ∧ validEX

  This is the "side-effect-bearing peripheral write" pattern —
  for each peripheral target, the write fires when:
    1. The IDEX stage has a store instruction (`memWrite`).
    2. The bus decoder maps the address to this peripheral.
    3. The instruction commits successfully (`validEX = ¬suppressEXWB`).

  Per Sparkle commit 91a3278: the DRAM `dmem_we` was historically
  the *only* side-effect-bearing write that wasn't gated on
  validEX, leading to a double-commit bug under timer interrupts.
  After the fix, DRAM also goes through this same gating pattern
  (modulo the AMO-writeback exclusion).

  This file proves the per-source spec and a "no write without
  memWrite" invariant.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Bus

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure peripheral WE -/

/-- Generic 3-way AND for peripheral writes:
    `idex_memWrite ∧ targetMatch ∧ validEX`. -/
@[inline] def peripheralWEPure
    (idex_memWrite targetMatch validEX : Bool) : Bool :=
  idex_memWrite && targetMatch && validEX

/-! ## Spec invariants — closed by `decide` -/

/-- No memWrite → no peripheral write (regardless of target/validEX). -/
@[simp] theorem peripheralWE_no_memWrite (targetMatch validEX : Bool) :
    peripheralWEPure false targetMatch validEX = false := by rfl

/-- Different target → no peripheral write. -/
@[simp] theorem peripheralWE_no_target (idex_memWrite validEX : Bool) :
    peripheralWEPure idex_memWrite false validEX = false := by
  unfold peripheralWEPure
  cases idex_memWrite <;> rfl

/-- !validEX (= suppressEXWB fires) → no peripheral write. -/
@[simp] theorem peripheralWE_suppressed (idex_memWrite targetMatch : Bool) :
    peripheralWEPure idex_memWrite targetMatch false = false := by
  unfold peripheralWEPure
  cases idex_memWrite <;> cases targetMatch <;> rfl

/-- All three gates open → write fires. -/
theorem peripheralWE_fires :
    peripheralWEPure true true true = true := by rfl

/-! ## Composite spec -/

theorem peripheralWEPure_spec :
    ∀ (idex_memWrite targetMatch validEX : Bool),
      peripheralWEPure idex_memWrite targetMatch validEX =
        (idex_memWrite && targetMatch && validEX) := by
  decide

/-! ## Cross-target mutual exclusion

  Combined with `Bus/Decoder.lean`'s mutex (`bus_decoder_*_disjoint`),
  the per-target WE predicates are also mutex: at most one peripheral
  fires its WE per cycle, since at most one of {isCLINT, isMmio,
  isUART, isDMEM} is true for any given address. -/

/-- Two distinct targets cannot both fire WE (assuming the targets are
    address-disjoint per the bus decoder). -/
theorem peripheralWE_target_mutex
    (idex_memWrite validEX : Bool)
    (targetA targetB : Bool)
    (hAB : !(targetA && targetB) = true) :
    !(peripheralWEPure idex_memWrite targetA validEX
       && peripheralWEPure idex_memWrite targetB validEX) = true := by
  unfold peripheralWEPure
  -- The `targetA ∧ targetB = false` precondition collapses both
  -- WE predicates to false on any cycle where the addresses differ.
  cases idex_memWrite <;> cases validEX <;> cases targetA <;>
    cases targetB <;> simp_all

/-! ## Signal-level wrapper -/

def peripheralWESignal {dom : DomainConfig}
    (idex_memWrite targetMatch validEX : Signal dom Bool) : Signal dom Bool :=
  idex_memWrite &&& (targetMatch &&& validEX)

end Sparkle.IP.RV32.Bus
