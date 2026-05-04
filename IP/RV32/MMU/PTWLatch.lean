/-
  RV32 MMU PTW PTE-latching + megapage-tracking next-state — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (~lines 1637..1651). The page-
  table walker (PTW) holds two stateful signals beyond the FSM:

    1. `ptwPteReg` — the most recently fetched PTE word from DRAM.
       In the WAIT states (L1_WAIT or L0_WAIT) we sample
       `dmem_rdata` (the data returned for the previous REQ
       address); otherwise we hold.

    2. `ptwMegaReg` — sticky "leaf-found-at-level-1" flag, used
       later when forming the megapage PA (concat hi-10 of
       ptePPN with VA-low-22 instead of ptePPN || VA-low-12).

       Set to `true` when L1_WAIT sees a valid leaf;
       cleared to `false` on PTW restart (`ptwIsIdle` cycle);
       held otherwise.

  Spec invariants:
    * PTE-latch in WAIT states; hold elsewhere.
    * Megapage flag: set on (L1_WAIT ∧ leaf ∧ valid); clear on Idle;
      hold otherwise. `Idle` clears regardless, so the flag is fresh
      each PTW.

  Reference: Sparkle SoC megapage bugfix (commit bf6d873): "Sv32:
  fix megapage PA formation in iTLB / dTLB / d-side MMU."
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.MMU

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure next-state functions -/

/-- PTE-register next: in WAIT states latch dmem_rdata; else hold. -/
@[inline] def ptwPteNextPure
    (isDataReady : Bool) (dmem_rdata ptwPte : BitVec 32) : BitVec 32 :=
  if isDataReady then dmem_rdata else ptwPte

/-- Megapage-flag next: set on L1_WAIT-leaf-and-valid; clear on Idle;
    hold otherwise. The hold arm matters because the flag must
    survive the L0_REQ/L0_WAIT phase (between L1_WAIT setting it and
    the eventual TLB fill at PTW Done). -/
@[inline] def ptwMegaNextPure
    (megaSet ptwIsIdle ptwMega : Bool) : Bool :=
  if megaSet then true
  else if ptwIsIdle then false
  else ptwMega

/-! ## Spec invariants — closed by `decide` / `rfl` -/

@[simp] theorem ptwPteNext_latch
    (dmem_rdata ptwPte : BitVec 32) :
    ptwPteNextPure true dmem_rdata ptwPte = dmem_rdata := by rfl

@[simp] theorem ptwPteNext_hold
    (dmem_rdata ptwPte : BitVec 32) :
    ptwPteNextPure false dmem_rdata ptwPte = ptwPte := by rfl

@[simp] theorem ptwMegaNext_set
    (ptwIsIdle ptwMega : Bool) :
    ptwMegaNextPure true ptwIsIdle ptwMega = true := by rfl

@[simp] theorem ptwMegaNext_idle_clear
    (ptwMega : Bool) :
    ptwMegaNextPure false true ptwMega = false := by rfl

@[simp] theorem ptwMegaNext_hold
    (ptwMega : Bool) :
    ptwMegaNextPure false false ptwMega = ptwMega := by rfl

/-- Megapage flag is monotonic within a single PTW: once set, stays
    set until Idle (which is the boundary between PTWs). -/
theorem ptwMegaNext_monotonic_in_ptw
    (megaSet : Bool) (ptwMega : Bool) :
    -- Not Idle: if megaSet, we get true; if ¬megaSet, we hold ptwMega.
    -- In particular, ptwMega = true → ptwMegaNext = true (stays).
    ptwMega = true → ptwMegaNextPure megaSet false ptwMega = true := by
  intro h
  cases megaSet <;> simp [ptwMegaNextPure, h]

/-! ## Composite specs -/

theorem ptwPteNextPure_spec (isDataReady : Bool) (dmem_rdata ptwPte : BitVec 32) :
    ptwPteNextPure isDataReady dmem_rdata ptwPte =
      (if isDataReady then dmem_rdata else ptwPte) := by rfl

theorem ptwMegaNextPure_spec (megaSet ptwIsIdle ptwMega : Bool) :
    ptwMegaNextPure megaSet ptwIsIdle ptwMega =
      (if megaSet then true
       else if ptwIsIdle then false else ptwMega) := by rfl

/-! ## Signal-level wrappers -/

/-- Helper: combine `ptwIsL1Wait || ptwIsL0Wait` into a single
    "data ready" signal (matches SoC.lean's local). -/
def isDataReadySignal {dom : DomainConfig}
    (ptwIsL1Wait ptwIsL0Wait : Signal dom Bool) : Signal dom Bool :=
  ptwIsL1Wait ||| ptwIsL0Wait

/-- Helper: `megaSet = ptwIsL1Wait ∧ pteIsLeaf ∧ ¬pteInvalid`. -/
def megaSetSignal {dom : DomainConfig}
    (ptwIsL1Wait pteIsLeaf pteInvalid : Signal dom Bool) : Signal dom Bool :=
  ptwIsL1Wait &&& (pteIsLeaf &&& (~~~pteInvalid))

def ptwPteNextSignal {dom : DomainConfig}
    (isDataReady : Signal dom Bool)
    (dmem_rdata ptwPte : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux isDataReady dmem_rdata ptwPte

def ptwMegaNextSignal {dom : DomainConfig}
    (megaSet ptwIsIdle ptwMega : Signal dom Bool) : Signal dom Bool :=
  Signal.mux megaSet (Signal.pure true)
    (Signal.mux ptwIsIdle (Signal.pure false) ptwMega)

end Sparkle.IP.RV32.MMU
