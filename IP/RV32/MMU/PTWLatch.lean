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

/-! ## Sequential ptwPteReg

  ptwPteReg latches `dmem_rdata` whenever `isDataReady` (= L1_WAIT
  ∨ L0_WAIT) fires; otherwise holds. -/

/-- ptwPteReg signal wrapper. -/
def ptwPteRegSignal {dom : DomainConfig}
    (init : BitVec 32) (isDataReady : Signal dom Bool)
    (dmem_rdata ptwPte : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.register init (ptwPteNextSignal isDataReady dmem_rdata ptwPte)

/-- **isDataReady at t → ptwPteReg at t+1 = dmem_rdata.val t.** -/
theorem ptwPteReg_latch_when_ready {dom : DomainConfig}
    (init : BitVec 32) (isDataReady : Signal dom Bool)
    (dmem_rdata ptwPte : Signal dom (BitVec 32)) (t : Nat)
    (h_ready : isDataReady.val t = true) :
    (ptwPteRegSignal init isDataReady dmem_rdata ptwPte).val (t + 1) = dmem_rdata.val t := by
  unfold ptwPteRegSignal
  show (Signal.register init _).val (t + 1) = _
  show (ptwPteNextSignal isDataReady dmem_rdata ptwPte).val t = _
  unfold ptwPteNextSignal Signal.mux
  show (if isDataReady.val t then _ else _) = _
  rw [h_ready]
  rfl

/-- **¬isDataReady at t → ptwPteReg at t+1 = ptwPte.val t.** -/
theorem ptwPteReg_hold_when_not_ready {dom : DomainConfig}
    (init : BitVec 32) (isDataReady : Signal dom Bool)
    (dmem_rdata ptwPte : Signal dom (BitVec 32)) (t : Nat)
    (h_no_ready : isDataReady.val t = false) :
    (ptwPteRegSignal init isDataReady dmem_rdata ptwPte).val (t + 1) = ptwPte.val t := by
  unfold ptwPteRegSignal
  show (Signal.register init _).val (t + 1) = _
  show (ptwPteNextSignal isDataReady dmem_rdata ptwPte).val t = _
  unfold ptwPteNextSignal Signal.mux
  show (if isDataReady.val t then _ else _) = _
  rw [h_no_ready]
  rfl

/-! ## Sequential ptwMegaReg

  ptwMegaReg is a sticky flag: set on (L1_WAIT ∧ leaf ∧ valid),
  cleared on Idle (PTW restart), held otherwise. -/

/-- ptwMegaReg signal wrapper. -/
def ptwMegaRegSignal {dom : DomainConfig}
    (init : Bool) (megaSet ptwIsIdle ptwMega : Signal dom Bool) : Signal dom Bool :=
  Signal.register init (ptwMegaNextSignal megaSet ptwIsIdle ptwMega)

/-- **megaSet at t → ptwMegaReg at t+1 = true.** -/
theorem ptwMegaReg_set_on_megaSet {dom : DomainConfig}
    (init : Bool) (megaSet ptwIsIdle ptwMega : Signal dom Bool) (t : Nat)
    (h_set : megaSet.val t = true) :
    (ptwMegaRegSignal init megaSet ptwIsIdle ptwMega).val (t + 1) = true := by
  unfold ptwMegaRegSignal
  show (Signal.register init _).val (t + 1) = true
  show (ptwMegaNextSignal megaSet ptwIsIdle ptwMega).val t = true
  unfold ptwMegaNextSignal Signal.mux
  show (if megaSet.val t then _ else _) = true
  rw [h_set]
  rfl

/-- **¬megaSet ∧ ptwIsIdle at t → ptwMegaReg at t+1 = false.** -/
theorem ptwMegaReg_clears_on_idle {dom : DomainConfig}
    (init : Bool) (megaSet ptwIsIdle ptwMega : Signal dom Bool) (t : Nat)
    (h_no_set : megaSet.val t = false)
    (h_idle : ptwIsIdle.val t = true) :
    (ptwMegaRegSignal init megaSet ptwIsIdle ptwMega).val (t + 1) = false := by
  unfold ptwMegaRegSignal
  show (Signal.register init _).val (t + 1) = false
  show (ptwMegaNextSignal megaSet ptwIsIdle ptwMega).val t = false
  unfold ptwMegaNextSignal Signal.mux
  show (if megaSet.val t then _ else
    (if ptwIsIdle.val t then _ else _)) = false
  rw [h_no_set, h_idle]
  rfl

/-- **¬megaSet ∧ ¬ptwIsIdle at t → ptwMegaReg at t+1 = ptwMega.val t.** -/
theorem ptwMegaReg_hold_otherwise {dom : DomainConfig}
    (init : Bool) (megaSet ptwIsIdle ptwMega : Signal dom Bool) (t : Nat)
    (h_no_set : megaSet.val t = false)
    (h_no_idle : ptwIsIdle.val t = false) :
    (ptwMegaRegSignal init megaSet ptwIsIdle ptwMega).val (t + 1) = ptwMega.val t := by
  unfold ptwMegaRegSignal
  show (Signal.register init _).val (t + 1) = _
  show (ptwMegaNextSignal megaSet ptwIsIdle ptwMega).val t = _
  unfold ptwMegaNextSignal Signal.mux
  show (if megaSet.val t then _ else
    (if ptwIsIdle.val t then _ else _)) = _
  rw [h_no_set, h_no_idle]
  rfl

/-! ## LTL forms for PTWLatch cycle-N+1 lemmas -/

theorem ptwPteReg_latch_when_ready_LTL {dom : DomainConfig}
    (init : BitVec 32) (isDataReady : Signal dom Bool)
    (dmem_rdata ptwPte : Signal dom (BitVec 32)) :
    ∀ t, isDataReady.val t = true →
         (ptwPteRegSignal init isDataReady dmem_rdata ptwPte).val (t + 1) = dmem_rdata.val t :=
  fun t => ptwPteReg_latch_when_ready init isDataReady dmem_rdata ptwPte t

theorem ptwPteReg_hold_when_not_ready_LTL {dom : DomainConfig}
    (init : BitVec 32) (isDataReady : Signal dom Bool)
    (dmem_rdata ptwPte : Signal dom (BitVec 32)) :
    ∀ t, isDataReady.val t = false →
         (ptwPteRegSignal init isDataReady dmem_rdata ptwPte).val (t + 1) = ptwPte.val t :=
  fun t => ptwPteReg_hold_when_not_ready init isDataReady dmem_rdata ptwPte t

theorem ptwMegaReg_set_on_megaSet_LTL {dom : DomainConfig}
    (init : Bool) (megaSet ptwIsIdle ptwMega : Signal dom Bool) :
    ∀ t, megaSet.val t = true →
         (ptwMegaRegSignal init megaSet ptwIsIdle ptwMega).val (t + 1) = true :=
  fun t => ptwMegaReg_set_on_megaSet init megaSet ptwIsIdle ptwMega t

theorem ptwMegaReg_clears_on_idle_LTL {dom : DomainConfig}
    (init : Bool) (megaSet ptwIsIdle ptwMega : Signal dom Bool) :
    ∀ t, megaSet.val t = false → ptwIsIdle.val t = true →
         (ptwMegaRegSignal init megaSet ptwIsIdle ptwMega).val (t + 1) = false :=
  fun t => ptwMegaReg_clears_on_idle init megaSet ptwIsIdle ptwMega t

theorem ptwMegaReg_hold_otherwise_LTL {dom : DomainConfig}
    (init : Bool) (megaSet ptwIsIdle ptwMega : Signal dom Bool) :
    ∀ t, megaSet.val t = false → ptwIsIdle.val t = false →
         (ptwMegaRegSignal init megaSet ptwIsIdle ptwMega).val (t + 1) = ptwMega.val t :=
  fun t => ptwMegaReg_hold_otherwise init megaSet ptwIsIdle ptwMega t

end Sparkle.IP.RV32.MMU
