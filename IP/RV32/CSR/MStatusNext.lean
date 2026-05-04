/-
  RV32 mstatus next-state — selector chain over already-extracted
  pure transformers.

  This file is the *composition* layer that picks which mstatus
  transformer applies on a given cycle. The transformers themselves
  live in `IP/RV32/CSR/MStatus.lean`:

    mstatusMretValPure mstatus mpie  -- MRET: MIE←MPIE, MPIE←1, MPP←0
    mstatusSretValPure mstatus spie  -- SRET: SIE←SPIE, SPIE←1, SPP←0
    mstatusTrapMValPure m mie  priv  -- M-trap: MIE←0, MPIE←old MIE, MPP←priv
    mstatusTrapSValPure m sie  priv  -- S-trap: SIE←0, SPIE←old SIE, SPP←priv[0]

  The selector encodes the priority order seen in `SoC.lean` (~line
  1421):

    1. trap_taken (trap delegation picks M vs S transformer first)
    2. mret
    3. sret
    4. sstatus CSR write (preserve M-bits, overwrite S-bits)
    5. mstatus CSR write (overwrite, modulo WPRI)
    6. otherwise: hold

  The CSR writes (sstatus / mstatus) are gated by `idex_isCsr_valid`,
  which itself depends on `validEX`. We model that as an
  `mstatusCsrActive` boolean rolled into `sstatusWriteActive` and
  `mstatusWriteActive`.

  The mret/sret arms also need an "instruction valid" gate, but in
  the live SoC they are masked through the IDEX instruction's decode
  bits being clear when the inst is squashed; so this layer takes
  `idex_isMret` / `idex_isSret` directly without an extra gate.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.CSR.MStatus

namespace Sparkle.IP.RV32.CSR

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure selector

  Given the Bool selectors and the four candidate next-values, plus
  the impl-side composite `mstatusTrapVal` (= `mstatusTrapSVal` if
  `trapToS`, else `mstatusTrapMVal`), and the two write-paths'
  payloads, return the chosen mstatus next-state. -/

/--
  Five-way priority mux for `mstatus`'s next-state.

  Inputs:
    * `trapTaken`         — async/sync trap fires this cycle
    * `trapVal`           — pre-selected (M-vs-S) trap-entry mstatus
    * `isMret`            — IDEX instruction is MRET
    * `mretVal`           — `mstatusMretValPure mstatus mpie`
    * `isSret`            — IDEX instruction is SRET
    * `sretVal`           — `mstatusSretValPure mstatus spie`
    * `sstatusWrite`      — sstatus CSR write commits this cycle
    * `sstatusWdata`      — payload (M-bits preserved, S-bits new)
    * `mstatusWrite`      — mstatus CSR write commits this cycle
    * `mstatusWdata`      — payload (full new mstatus)
    * `mstatus`           — current value (held when nothing fires)
-/
@[inline] def mstatusNextPure
    (trapTaken : Bool) (trapVal : BitVec 32)
    (isMret : Bool) (mretVal : BitVec 32)
    (isSret : Bool) (sretVal : BitVec 32)
    (sstatusWrite : Bool) (sstatusWdata : BitVec 32)
    (mstatusWrite : Bool) (mstatusWdata : BitVec 32)
    (mstatus : BitVec 32) : BitVec 32 :=
  if trapTaken then trapVal
  else if isMret then mretVal
  else if isSret then sretVal
  else if sstatusWrite then sstatusWdata
  else if mstatusWrite then mstatusWdata
  else mstatus

/-! ## Spec invariants — priority + invariance -/

/-- A non-event cycle holds `mstatus` unchanged. -/
@[simp] theorem mstatusNext_hold
    (trapVal mretVal sretVal sstatusWdata mstatusWdata mstatus : BitVec 32) :
    mstatusNextPure
      false trapVal false mretVal false sretVal
      false sstatusWdata false mstatusWdata mstatus = mstatus := by
  rfl

/-- Trap takes priority over every other selector. -/
@[simp] theorem mstatusNext_trap_priority
    (trapVal : BitVec 32) (isMret : Bool) (mretVal : BitVec 32)
    (isSret : Bool) (sretVal : BitVec 32)
    (sstatusWrite : Bool) (sstatusWdata : BitVec 32)
    (mstatusWrite : Bool) (mstatusWdata : BitVec 32)
    (mstatus : BitVec 32) :
    mstatusNextPure
      true trapVal isMret mretVal isSret sretVal
      sstatusWrite sstatusWdata mstatusWrite mstatusWdata mstatus = trapVal := by
  rfl

/-- MRET takes priority over SRET / sstatus / mstatus writes. -/
@[simp] theorem mstatusNext_mret_priority
    (trapVal mretVal : BitVec 32) (isSret : Bool) (sretVal : BitVec 32)
    (sstatusWrite : Bool) (sstatusWdata : BitVec 32)
    (mstatusWrite : Bool) (mstatusWdata : BitVec 32)
    (mstatus : BitVec 32) :
    mstatusNextPure
      false trapVal true mretVal isSret sretVal
      sstatusWrite sstatusWdata mstatusWrite mstatusWdata mstatus = mretVal := by
  rfl

/-- SRET takes priority over the CSR-write paths. -/
@[simp] theorem mstatusNext_sret_priority
    (trapVal mretVal sretVal : BitVec 32)
    (sstatusWrite : Bool) (sstatusWdata : BitVec 32)
    (mstatusWrite : Bool) (mstatusWdata : BitVec 32)
    (mstatus : BitVec 32) :
    mstatusNextPure
      false trapVal false mretVal true sretVal
      sstatusWrite sstatusWdata mstatusWrite mstatusWdata mstatus = sretVal := by
  rfl

/-- sstatus CSR write takes priority over mstatus CSR write. -/
@[simp] theorem mstatusNext_sstatus_priority
    (trapVal mretVal sretVal sstatusWdata : BitVec 32)
    (mstatusWrite : Bool) (mstatusWdata : BitVec 32)
    (mstatus : BitVec 32) :
    mstatusNextPure
      false trapVal false mretVal false sretVal
      true sstatusWdata mstatusWrite mstatusWdata mstatus = sstatusWdata := by
  rfl

/-- mstatus CSR write applies when nothing higher-priority fires. -/
@[simp] theorem mstatusNext_mstatus_write
    (trapVal mretVal sretVal sstatusWdata mstatusWdata mstatus : BitVec 32) :
    mstatusNextPure
      false trapVal false mretVal false sretVal
      false sstatusWdata true mstatusWdata mstatus = mstatusWdata := by
  rfl

/-! ## Signal-level wrappers -/

/-- Signal-level `mstatusNext`. -/
def mstatusNextSignal {dom : DomainConfig}
    (trapTaken : Signal dom Bool) (trapVal : Signal dom (BitVec 32))
    (isMret : Signal dom Bool) (mretVal : Signal dom (BitVec 32))
    (isSret : Signal dom Bool) (sretVal : Signal dom (BitVec 32))
    (sstatusWrite : Signal dom Bool) (sstatusWdata : Signal dom (BitVec 32))
    (mstatusWrite : Signal dom Bool) (mstatusWdata : Signal dom (BitVec 32))
    (mstatus : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux trapTaken trapVal
    (Signal.mux isMret mretVal
    (Signal.mux isSret sretVal
    (Signal.mux sstatusWrite sstatusWdata
    (Signal.mux mstatusWrite mstatusWdata
      mstatus))))

/-- Cycle-wise: `mstatusNextSignal = mstatusNextPure`. -/
theorem mstatusNextSignal_eq_pure {dom : DomainConfig}
    (trapTaken : Signal dom Bool) (trapVal : Signal dom (BitVec 32))
    (isMret : Signal dom Bool) (mretVal : Signal dom (BitVec 32))
    (isSret : Signal dom Bool) (sretVal : Signal dom (BitVec 32))
    (sstatusWrite : Signal dom Bool) (sstatusWdata : Signal dom (BitVec 32))
    (mstatusWrite : Signal dom Bool) (mstatusWdata : Signal dom (BitVec 32))
    (mstatus : Signal dom (BitVec 32)) (t : Nat) :
    (mstatusNextSignal trapTaken trapVal isMret mretVal isSret sretVal
       sstatusWrite sstatusWdata mstatusWrite mstatusWdata mstatus).val t =
      mstatusNextPure (trapTaken.val t) (trapVal.val t)
        (isMret.val t) (mretVal.val t)
        (isSret.val t) (sretVal.val t)
        (sstatusWrite.val t) (sstatusWdata.val t)
        (mstatusWrite.val t) (mstatusWdata.val t)
        (mstatus.val t) := by
  unfold mstatusNextSignal mstatusNextPure
  show (Signal.mux _ _ _).val t = _
  unfold Signal.mux
  -- Each Signal.mux unfolds to `if cond.val t then ...`. Repeated
  -- applications collapse the chain.
  cases h_trap : trapTaken.val t <;>
  cases h_mret : isMret.val t <;>
  cases h_sret : isSret.val t <;>
  cases h_sw : sstatusWrite.val t <;>
  cases h_mw : mstatusWrite.val t <;>
  simp [h_trap, h_mret, h_sret, h_sw, h_mw]

/-! ## Sequential mstatus register

  `mstatus` is held in a `Signal.register init mstatusNextSignal` —
  next-state via the 5-way priority mux above. This file packages
  the cycle-wise sequential statements:
    * trap fires at t → mstatus at t+1 = trapVal.val t
    * (no event)      → mstatus at t+1 = mstatus.val t
-/

/-- mstatus register wrapper. -/
def mstatusRegSignal {dom : DomainConfig}
    (init : BitVec 32) (trapTaken : Signal dom Bool) (trapVal : Signal dom (BitVec 32))
    (isMret : Signal dom Bool) (mretVal : Signal dom (BitVec 32))
    (isSret : Signal dom Bool) (sretVal : Signal dom (BitVec 32))
    (sstatusWrite : Signal dom Bool) (sstatusWdata : Signal dom (BitVec 32))
    (mstatusWrite : Signal dom Bool) (mstatusWdata : Signal dom (BitVec 32))
    (mstatus : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.register init
    (mstatusNextSignal trapTaken trapVal isMret mretVal isSret sretVal
      sstatusWrite sstatusWdata mstatusWrite mstatusWdata mstatus)

/-- **trap at cycle t → mstatus at t+1 = trapVal.val t.**

    The trap-entry path takes priority over every other arm of
    the 5-way mux. -/
theorem mstatusReg_latches_trapVal_on_trap {dom : DomainConfig}
    (init : BitVec 32) (trapTaken : Signal dom Bool) (trapVal : Signal dom (BitVec 32))
    (isMret : Signal dom Bool) (mretVal : Signal dom (BitVec 32))
    (isSret : Signal dom Bool) (sretVal : Signal dom (BitVec 32))
    (sstatusWrite : Signal dom Bool) (sstatusWdata : Signal dom (BitVec 32))
    (mstatusWrite : Signal dom Bool) (mstatusWdata : Signal dom (BitVec 32))
    (mstatus : Signal dom (BitVec 32)) (t : Nat)
    (h_trap : trapTaken.val t = true) :
    (mstatusRegSignal init trapTaken trapVal isMret mretVal isSret sretVal
      sstatusWrite sstatusWdata mstatusWrite mstatusWdata mstatus).val (t + 1) =
      trapVal.val t := by
  unfold mstatusRegSignal
  show (Signal.register init _).val (t + 1) = _
  show (mstatusNextSignal trapTaken trapVal isMret mretVal isSret sretVal
    sstatusWrite sstatusWdata mstatusWrite mstatusWdata mstatus).val t = _
  rw [mstatusNextSignal_eq_pure]
  rw [h_trap]
  rfl

/-- **No event at cycle t → mstatus at t+1 = mstatus.val t.** -/
theorem mstatusReg_hold_when_no_event {dom : DomainConfig}
    (init : BitVec 32) (trapTaken : Signal dom Bool) (trapVal : Signal dom (BitVec 32))
    (isMret : Signal dom Bool) (mretVal : Signal dom (BitVec 32))
    (isSret : Signal dom Bool) (sretVal : Signal dom (BitVec 32))
    (sstatusWrite : Signal dom Bool) (sstatusWdata : Signal dom (BitVec 32))
    (mstatusWrite : Signal dom Bool) (mstatusWdata : Signal dom (BitVec 32))
    (mstatus : Signal dom (BitVec 32)) (t : Nat)
    (h_no_trap : trapTaken.val t = false)
    (h_no_mret : isMret.val t = false)
    (h_no_sret : isSret.val t = false)
    (h_no_sw : sstatusWrite.val t = false)
    (h_no_mw : mstatusWrite.val t = false) :
    (mstatusRegSignal init trapTaken trapVal isMret mretVal isSret sretVal
      sstatusWrite sstatusWdata mstatusWrite mstatusWdata mstatus).val (t + 1) =
      mstatus.val t := by
  unfold mstatusRegSignal
  show (Signal.register init _).val (t + 1) = _
  show (mstatusNextSignal trapTaken trapVal isMret mretVal isSret sretVal
    sstatusWrite sstatusWdata mstatusWrite mstatusWdata mstatus).val t = _
  rw [mstatusNextSignal_eq_pure]
  rw [h_no_trap, h_no_mret, h_no_sret, h_no_sw, h_no_mw]
  rfl

/-! ## Cycle-N+2 mstatus stays at trap-latched value

  Combine `mstatusReg_latches_trapVal_on_trap` (cycle N → N+1)
  with `mstatusReg_hold_when_no_event` (cycle N+1 → N+2): when
  trap fires at N and no events fire at N+1, mstatus at N+2
  equals trapVal.val N.

  Note: the "no event at N+1" hypotheses for trapTaken/isMret/
  isSret are discharged via IDEX-squash reasoning (the IDEX
  control bits idex_isMret, idex_isSret, idex_isCsr are all
  cleared after the squash). The sstatusWrite/mstatusWrite
  hypotheses also follow from idex_isCsr=false at N+1.
-/

/-- **trap at N + no events at N+1 → mstatusReg at N+2 = trapVal.val N.** -/
theorem mstatusReg_stays_trapVal_at_N_plus_2 {dom : DomainConfig}
    (init : BitVec 32) (trapTaken : Signal dom Bool) (trapVal : Signal dom (BitVec 32))
    (isMret : Signal dom Bool) (mretVal : Signal dom (BitVec 32))
    (isSret : Signal dom Bool) (sretVal : Signal dom (BitVec 32))
    (sstatusWrite : Signal dom Bool) (sstatusWdata : Signal dom (BitVec 32))
    (mstatusWrite : Signal dom Bool) (mstatusWdata : Signal dom (BitVec 32))
    (n : Nat)
    (h_trap_n : trapTaken.val n = true)
    (h_no_trap_n1 : trapTaken.val (n + 1) = false)
    (h_no_mret_n1 : isMret.val (n + 1) = false)
    (h_no_sret_n1 : isSret.val (n + 1) = false)
    (h_no_sw_n1 : sstatusWrite.val (n + 1) = false)
    (h_no_mw_n1 : mstatusWrite.val (n + 1) = false) :
    -- The "mstatus" signal here is the register output recursively.
    -- We use Signal.register init mstatusNextSignal as the target.
    let regSig :=
      mstatusRegSignal init trapTaken trapVal isMret mretVal isSret sretVal
        sstatusWrite sstatusWdata mstatusWrite mstatusWdata
        (mstatusRegSignal init trapTaken trapVal isMret mretVal isSret sretVal
          sstatusWrite sstatusWdata mstatusWrite mstatusWdata (Signal.pure 0#32))
    regSig.val (n + 2) = trapVal.val n := by
  -- Step 1: At cycle N, trap fires → inner reg at N+1 = trapVal.val N.
  have h_inner_n1 :
    (mstatusRegSignal init trapTaken trapVal isMret mretVal isSret sretVal
      sstatusWrite sstatusWdata mstatusWrite mstatusWdata (Signal.pure 0#32)).val (n + 1) =
      trapVal.val n :=
    mstatusReg_latches_trapVal_on_trap init trapTaken trapVal isMret mretVal isSret
      sretVal sstatusWrite sstatusWdata mstatusWrite mstatusWdata _ n h_trap_n
  -- Step 2: At cycle N+1, no events → outer reg at N+2 = inner reg at N+1.
  have h_outer := mstatusReg_hold_when_no_event init trapTaken trapVal isMret mretVal
    isSret sretVal sstatusWrite sstatusWdata mstatusWrite mstatusWdata
    (mstatusRegSignal init trapTaken trapVal isMret mretVal isSret sretVal
      sstatusWrite sstatusWdata mstatusWrite mstatusWdata (Signal.pure 0#32))
    (n + 1) h_no_trap_n1 h_no_mret_n1 h_no_sret_n1 h_no_sw_n1 h_no_mw_n1
  show (mstatusRegSignal _ _ _ _ _ _ _ _ _ _ _ _).val (n + 2) = _
  rw [h_outer]
  exact h_inner_n1

end Sparkle.IP.RV32.CSR
