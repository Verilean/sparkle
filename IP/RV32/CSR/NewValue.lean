/-
  RV32 CSR new-value selector — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (~lines 1361..1365). Computes
  the CSR's new value given the current value, the write data,
  and the three op flags from funct3[1:0]:

      csrrw / csrrwi:  RW → newVal = wdata        (overwrite)
      csrrs / csrrsi:  RS → newVal = old ∨ wdata  (set)
      csrrc / csrrci:  RC → newVal = old ∧ ¬wdata (clear)
      otherwise:           newVal = old           (no-op / read-only)

  The `csrWdata` and `wdata` flow are decided upstream:
    csrWdata = csrIsImm ? zext(rs1Idx) : ex_rs1

  This file does not capture the immediate-vs-register selection
  (it's a single mux orthogonal to the RW/RS/RC choice). It only
  captures the three op semantics.

  Reference: RISC-V unprivileged spec, §6 (Zicsr extension).
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.CSR

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure selector -/

/-- CSR new-value computation. Priority: RW > RS > RC > hold. -/
@[inline] def csrNewValPure
    (old wdata : BitVec 32) (isRW isRS isRC : Bool) : BitVec 32 :=
  if isRW then wdata
  else if isRS then old ||| wdata
  else if isRC then old &&& (~~~wdata)
  else old

/-! ## Spec invariants — closed by `decide` over Bool^3 -/

/-- All-clear ops hold the old value. -/
@[simp] theorem csrNewVal_hold
    (old wdata : BitVec 32) :
    csrNewValPure old wdata false false false = old := by
  rfl

/-- RW takes priority over RS / RC. -/
@[simp] theorem csrNewVal_rw
    (old wdata : BitVec 32) (isRS isRC : Bool) :
    csrNewValPure old wdata true isRS isRC = wdata := by
  rfl

/-- RS without RW yields old ∨ wdata. -/
@[simp] theorem csrNewVal_rs
    (old wdata : BitVec 32) (isRC : Bool) :
    csrNewValPure old wdata false true isRC = old ||| wdata := by
  rfl

/-- RC alone yields old ∧ ¬wdata. -/
@[simp] theorem csrNewVal_rc
    (old wdata : BitVec 32) :
    csrNewValPure old wdata false false true = old &&& (~~~wdata) := by
  rfl

/-! ## Bit-level invariants

  RS only sets bits; RC only clears bits. These are the two
  most-cited invariants when reasoning about CSR-write side
  effects (e.g., `csrrs zero, mip, x0` is a no-op no matter what
  bits are pending).

  The whole-vector versions follow directly from the unfolds
  (RS = old ||| wdata; RC = old &&& ~~~wdata). -/

/-- RS never clears a set bit: `old &&& (RS-result) = old` (whole-vector). -/
theorem csrNewVal_rs_preserves_set_bits
    (old wdata : BitVec 32) :
    old &&& csrNewValPure old wdata false true false = old := by
  unfold csrNewValPure
  show old &&& (old ||| wdata) = old
  bv_decide

/-- RC never sets a clear bit: `(RC-result) &&& ~~~old = 0` (whole-vector:
    every bit RC-result has set must already be set in `old`). Equivalently:
    `RC-result | old = old` since RC only clears. -/
theorem csrNewVal_rc_preserves_clear_bits
    (old wdata : BitVec 32) :
    csrNewValPure old wdata false false true ||| old = old := by
  unfold csrNewValPure
  show (old &&& (~~~wdata)) ||| old = old
  bv_decide

/-! ## Composite spec — exhaustive over Bool^3 -/

/-- Truth table for `csrNewValPure`'s op-flag dimension. -/
theorem csrNewValPure_op_spec :
    ∀ (isRW isRS isRC : Bool) (old wdata : BitVec 32),
      csrNewValPure old wdata isRW isRS isRC =
        (if isRW then wdata
         else if isRS then old ||| wdata
         else if isRC then old &&& (~~~wdata)
         else old) := by
  intros; rfl

/-! ## Signal-level wrapper -/

/-- Signal-level `csrNewVal`. -/
def csrNewValSignal {dom : DomainConfig}
    (old wdata : Signal dom (BitVec 32))
    (isRW isRS isRC : Signal dom Bool) : Signal dom (BitVec 32) :=
  Signal.mux isRW wdata
    (Signal.mux isRS (old ||| wdata)
      (Signal.mux isRC (old &&& (~~~wdata)) old))

/-! ## Cycle-wise equivalence -/

private theorem signal_pure_val {dom : DomainConfig} {α : Type}
    (x : α) (t : Nat) : (Signal.pure (dom := dom) x).val t = x := rfl

/-- Helper: `(a ||| b).val t = a.val t ||| b.val t` for `BitVec 32`. -/
private theorem signal_bv_or_val {dom : DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (t : Nat) :
    (a ||| b).val t = (a.val t ||| b.val t) := by
  show (Signal.ap (Signal.map (· ||| ·) a) b).val t = _
  rfl

/-- Helper: `(a &&& b).val t = a.val t &&& b.val t` for `BitVec 32`. -/
private theorem signal_bv_and_val {dom : DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (t : Nat) :
    (a &&& b).val t = (a.val t &&& b.val t) := by
  show (Signal.ap (Signal.map (· &&& ·) a) b).val t = _
  rfl

/-- Helper: `(~~~a).val t = ~~~(a.val t)` for `BitVec 32`. -/
private theorem signal_bv_not_val {dom : DomainConfig} {n : Nat}
    (a : Signal dom (BitVec n)) (t : Nat) :
    (~~~a).val t = ~~~(a.val t) := by
  show (Signal.map (fun x => ~~~x) a).val t = _
  rfl

/-- `csrNewValSignal = csrNewValPure` cycle-by-cycle. -/
theorem csrNewValSignal_eq_pure {dom : DomainConfig}
    (old wdata : Signal dom (BitVec 32))
    (isRW isRS isRC : Signal dom Bool) (t : Nat) :
    (csrNewValSignal old wdata isRW isRS isRC).val t =
      csrNewValPure (old.val t) (wdata.val t)
        (isRW.val t) (isRS.val t) (isRC.val t) := by
  unfold csrNewValSignal csrNewValPure
  show (Signal.mux _ _ _).val t = _
  unfold Signal.mux
  cases h_rw : isRW.val t <;>
  cases h_rs : isRS.val t <;>
  cases h_rc : isRC.val t <;>
    simp [h_rw, h_rs, h_rc, signal_bv_or_val, signal_bv_and_val, signal_bv_not_val]

end Sparkle.IP.RV32.CSR
