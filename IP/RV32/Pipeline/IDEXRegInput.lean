/-
  RV32 IDEX-stage register-input next-state — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (~lines 1777..1800). The IDEX
  stage holds the decoded fields of an instruction passing from
  ID into EX. Each control bit / data field has a 3-way priority
  next-state:

      freezeIDEX → hold (replay the same instruction; load-use
                  stall, AMO writeback bubble)
      squash    → zero/false/NOP (flush a control hazard;
                  branch mispredict, JAL/JALR/trap)
      else      → take the new ID-stage value

  Two flavors:

    * **Squashable**: control bits and `aluOp`/`rd` — flush
      replaces with zero/false (NOP). 17 fields use this shape.
    * **Non-squashable**: data fields like rs1Val/rs2Val/imm/
      rs1Idx/rs2Idx/funct3/pc/pc4/csrAddr/csrFunct3 — flush
      doesn't need to clear them; the squashed control bits
      already make them harmless. 11 fields use this shape.

  Spec invariants:
    * freezeIDEX wins over squash (same as flush winning over
      stall in IFID).
    * On squash without freeze, squashable fields → 0/false.
    * On no-event, all fields take the ID-stage input.

  Reference: `docs/RV32_Architecture_Status.md` §1.2 (pipeline
  policy: "freezeIDEX hold during load-use stall + AMO writeback
  bubble; squash on branch/JAL/JALR/trap").
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure next-state functions -/

/-- Squashable IDEX field: 3-way priority freeze > squash > new.
    On squash, the field is replaced by `zero` (typically 0#n or
    false, i.e., the NOP control encoding). -/
@[inline] def idexSquashableNextPure {α}
    (freezeIDEX squash : Bool) (held zero new : α) : α :=
  if freezeIDEX then held
  else if squash then zero
  else new

/-- Non-squashable IDEX field: 2-way priority freeze > new. -/
@[inline] def idexHoldableNextPure {α}
    (freezeIDEX : Bool) (held new : α) : α :=
  if freezeIDEX then held else new

/-! ## Spec invariants — closed by `rfl` -/

/-- Freeze wins over squash. -/
@[simp] theorem idexSquashable_freeze_wins {α}
    (squash : Bool) (held zero new : α) :
    idexSquashableNextPure true squash held zero new = held := by rfl

/-- Squash on no-freeze → zero. -/
@[simp] theorem idexSquashable_squash {α} (held zero new : α) :
    idexSquashableNextPure false true held zero new = zero := by rfl

/-- No event → take the new ID-stage value. -/
@[simp] theorem idexSquashable_advance {α} (held zero new : α) :
    idexSquashableNextPure false false held zero new = new := by rfl

/-- Holdable freeze → held. -/
@[simp] theorem idexHoldable_freeze {α} (held new : α) :
    idexHoldableNextPure true held new = held := by rfl

/-- Holdable advance → new. -/
@[simp] theorem idexHoldable_advance {α} (held new : α) :
    idexHoldableNextPure false held new = new := by rfl

/-! ## Composite specs -/

theorem idexSquashableNextPure_spec {α}
    (freezeIDEX squash : Bool) (held zero new : α) :
    idexSquashableNextPure freezeIDEX squash held zero new =
      (if freezeIDEX then held
       else if squash then zero else new) := by rfl

theorem idexHoldableNextPure_spec {α}
    (freezeIDEX : Bool) (held new : α) :
    idexHoldableNextPure freezeIDEX held new =
      (if freezeIDEX then held else new) := by rfl

/-! ## Bridge: holdable agrees with squashable when squash=false -/

theorem idexHoldable_eq_squashable_no_squash {α}
    (freezeIDEX : Bool) (held zero new : α) :
    idexHoldableNextPure freezeIDEX held new =
      idexSquashableNextPure freezeIDEX false held zero new := by
  unfold idexHoldableNextPure idexSquashableNextPure
  cases freezeIDEX <;> rfl

/-! ## Signal-level wrappers (type-specialized) -/

/-- Squashable BitVec field. -/
def idexSquashableBVSignal {dom : DomainConfig} {n : Nat}
    (freezeIDEX squash : Signal dom Bool)
    (held : Signal dom (BitVec n))
    (zero : BitVec n)
    (new : Signal dom (BitVec n)) : Signal dom (BitVec n) :=
  Signal.mux freezeIDEX held
    (Signal.mux squash (Signal.pure zero) new)

/-- Squashable Bool field. -/
def idexSquashableBoolSignal {dom : DomainConfig}
    (freezeIDEX squash : Signal dom Bool)
    (held new : Signal dom Bool) : Signal dom Bool :=
  Signal.mux freezeIDEX held
    (Signal.mux squash (Signal.pure false) new)

/-- Holdable BitVec field. -/
def idexHoldableBVSignal {dom : DomainConfig} {n : Nat}
    (freezeIDEX : Signal dom Bool)
    (held new : Signal dom (BitVec n)) : Signal dom (BitVec n) :=
  Signal.mux freezeIDEX held new

/-! ## EX/WB-stage suppress pattern

  Several EX/WB control bits use a different pattern from the
  IDEX freeze+squash logic. They have a single "suppress" gate
  that forces 0/false during suppression (e.g., on dTLBMiss or
  during a load-result-not-yet-ready hold), with the new value
  otherwise:

      next = if suppressEXWB then zero else new

  This is the trap-suppression pattern (see
  Pipeline/SuppressEXWB.lean for the gate's spec). The new
  value here is the IDEX-stage value, since the EX/WB register
  latches it for the WB stage one cycle later.

  Unlike `idexSquashableNextPure`, there's no "held"/freeze
  arm: when freezeIDEX is true, the upstream IDEX-stage value
  is held *as the held value*, so the EX/WB just sees a steady
  IDEX input across the freeze cycles.
-/

@[inline] def exwbSuppressNextPure {α}
    (suppressEXWB : Bool) (zero new : α) : α :=
  if suppressEXWB then zero else new

/-- Suppress → zero. -/
@[simp] theorem exwbSuppress_suppress {α} (zero new : α) :
    exwbSuppressNextPure true zero new = zero := by rfl

/-- ¬Suppress → new. -/
@[simp] theorem exwbSuppress_advance {α} (zero new : α) :
    exwbSuppressNextPure false zero new = new := by rfl

theorem exwbSuppressNextPure_spec {α}
    (suppressEXWB : Bool) (zero new : α) :
    exwbSuppressNextPure suppressEXWB zero new =
      (if suppressEXWB then zero else new) := by rfl

/-- Suppress-pattern BitVec wrapper. -/
def exwbSuppressBVSignal {dom : DomainConfig} {n : Nat}
    (suppressEXWB : Signal dom Bool) (zero : BitVec n)
    (new : Signal dom (BitVec n)) : Signal dom (BitVec n) :=
  Signal.mux suppressEXWB (Signal.pure zero) new

/-- Suppress-pattern Bool wrapper. -/
def exwbSuppressBoolSignal {dom : DomainConfig}
    (suppressEXWB new : Signal dom Bool) : Signal dom Bool :=
  Signal.mux suppressEXWB (Signal.pure false) new

/-! ## Sequential register lemmas for idexHoldable / exwbSuppress

  These are register-level wrappers + cycle-wise sequential
  lemmas, mirroring the FlushSquash idex-squashable register
  semantics for the simpler "holdable" and "suppress" patterns. -/

/-- Holdable BV register: register init (idexHoldableBVSignal). -/
def idexHoldableBVRegSignal {dom : DomainConfig} {n : Nat}
    (init : BitVec n) (freezeIDEX : Signal dom Bool)
    (held new : Signal dom (BitVec n)) : Signal dom (BitVec n) :=
  Signal.register init (idexHoldableBVSignal freezeIDEX held new)

/-- **freeze at t → idexHoldableBVReg at t+1 = held.val t.** -/
theorem idexHoldableBVReg_freeze {dom : DomainConfig} {n : Nat}
    (init : BitVec n) (freezeIDEX : Signal dom Bool)
    (held new : Signal dom (BitVec n)) (t : Nat)
    (h_freeze : freezeIDEX.val t = true) :
    (idexHoldableBVRegSignal init freezeIDEX held new).val (t + 1) = held.val t := by
  unfold idexHoldableBVRegSignal idexHoldableBVSignal
  show (Signal.register init _).val (t + 1) = _
  show (Signal.mux freezeIDEX held new).val t = _
  unfold Signal.mux
  show (if freezeIDEX.val t then _ else _) = _
  rw [h_freeze]
  rfl

/-- **¬freeze at t → idexHoldableBVReg at t+1 = new.val t.** -/
theorem idexHoldableBVReg_advance {dom : DomainConfig} {n : Nat}
    (init : BitVec n) (freezeIDEX : Signal dom Bool)
    (held new : Signal dom (BitVec n)) (t : Nat)
    (h_no_freeze : freezeIDEX.val t = false) :
    (idexHoldableBVRegSignal init freezeIDEX held new).val (t + 1) = new.val t := by
  unfold idexHoldableBVRegSignal idexHoldableBVSignal
  show (Signal.register init _).val (t + 1) = _
  show (Signal.mux freezeIDEX held new).val t = _
  unfold Signal.mux
  show (if freezeIDEX.val t then _ else _) = _
  rw [h_no_freeze]
  rfl

/-- ExwbSuppress BV register. -/
def exwbSuppressBVRegSignal {dom : DomainConfig} {n : Nat}
    (init : BitVec n) (suppressEXWB : Signal dom Bool) (zero : BitVec n)
    (new : Signal dom (BitVec n)) : Signal dom (BitVec n) :=
  Signal.register init (exwbSuppressBVSignal suppressEXWB zero new)

/-- **suppress at t → exwbSuppressBVReg at t+1 = zero.** -/
theorem exwbSuppressBVReg_suppress {dom : DomainConfig} {n : Nat}
    (init : BitVec n) (suppressEXWB : Signal dom Bool) (zero : BitVec n)
    (new : Signal dom (BitVec n)) (t : Nat)
    (h_suppress : suppressEXWB.val t = true) :
    (exwbSuppressBVRegSignal init suppressEXWB zero new).val (t + 1) = zero := by
  unfold exwbSuppressBVRegSignal exwbSuppressBVSignal
  show (Signal.register init _).val (t + 1) = _
  show (Signal.mux suppressEXWB (Signal.pure zero) new).val t = _
  unfold Signal.mux
  show (if suppressEXWB.val t then _ else _) = _
  rw [h_suppress]
  rfl

/-- **¬suppress at t → exwbSuppressBVReg at t+1 = new.val t.** -/
theorem exwbSuppressBVReg_advance {dom : DomainConfig} {n : Nat}
    (init : BitVec n) (suppressEXWB : Signal dom Bool) (zero : BitVec n)
    (new : Signal dom (BitVec n)) (t : Nat)
    (h_no_suppress : suppressEXWB.val t = false) :
    (exwbSuppressBVRegSignal init suppressEXWB zero new).val (t + 1) = new.val t := by
  unfold exwbSuppressBVRegSignal exwbSuppressBVSignal
  show (Signal.register init _).val (t + 1) = _
  show (Signal.mux suppressEXWB (Signal.pure zero) new).val t = _
  unfold Signal.mux
  show (if suppressEXWB.val t then _ else _) = _
  rw [h_no_suppress]
  rfl

/-- ExwbSuppress Bool register. -/
def exwbSuppressBoolRegSignal {dom : DomainConfig}
    (init : Bool) (suppressEXWB new : Signal dom Bool) : Signal dom Bool :=
  Signal.register init (exwbSuppressBoolSignal suppressEXWB new)

/-- **suppress at t → exwbSuppressBoolReg at t+1 = false.** -/
theorem exwbSuppressBoolReg_suppress {dom : DomainConfig}
    (init : Bool) (suppressEXWB new : Signal dom Bool) (t : Nat)
    (h_suppress : suppressEXWB.val t = true) :
    (exwbSuppressBoolRegSignal init suppressEXWB new).val (t + 1) = false := by
  unfold exwbSuppressBoolRegSignal exwbSuppressBoolSignal
  show (Signal.register init _).val (t + 1) = _
  show (Signal.mux suppressEXWB (Signal.pure false) new).val t = _
  unfold Signal.mux
  show (if suppressEXWB.val t then _ else _) = _
  rw [h_suppress]
  rfl

/-- **¬suppress at t → exwbSuppressBoolReg at t+1 = new.val t.** -/
theorem exwbSuppressBoolReg_advance {dom : DomainConfig}
    (init : Bool) (suppressEXWB new : Signal dom Bool) (t : Nat)
    (h_no_suppress : suppressEXWB.val t = false) :
    (exwbSuppressBoolRegSignal init suppressEXWB new).val (t + 1) = new.val t := by
  unfold exwbSuppressBoolRegSignal exwbSuppressBoolSignal
  show (Signal.register init _).val (t + 1) = _
  show (Signal.mux suppressEXWB (Signal.pure false) new).val t = _
  unfold Signal.mux
  show (if suppressEXWB.val t then _ else _) = _
  rw [h_no_suppress]
  rfl

end Sparkle.IP.RV32.Pipeline
