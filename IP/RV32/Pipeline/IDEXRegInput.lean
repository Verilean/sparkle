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

end Sparkle.IP.RV32.Pipeline
