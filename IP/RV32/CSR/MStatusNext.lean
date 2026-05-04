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

end Sparkle.IP.RV32.CSR
