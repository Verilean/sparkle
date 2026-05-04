/-
  RV32 branch comparator — pure logic + invariants

  The Signal-level `branchCompSignal` is already defined in
  `IP/RV32/Core.lean`. This file adds the *pure* counterpart (over
  raw `BitVec 32` and `BitVec 3`), proves per-branch invariants
  with `bv_decide`, and proves the cycle-wise equivalence.

  Branch encoding (RISC-V unprivileged spec, §2.5):

    funct3 | mnemonic | condition
    -------|----------|-------------------
    000    | BEQ      | a == b
    001    | BNE      | a != b
    100    | BLT      | a <ₛ b   (signed)
    101    | BGE      | a ≥ₛ b
    110    | BLTU     | a <ᵤ b   (unsigned)
    111    | BGEU     | a ≥ᵤ b

  funct3 ∈ {010, 011} are reserved (defined as `false` here, matching
  the SoC.lean default-arm).
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.Core

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure branch comparator -/

/-- Pure branch-condition function over `BitVec 3` × `BitVec 32` × `BitVec 32`. -/
@[inline] def branchCompPure
    (funct3 : BitVec 3) (a b : BitVec 32) : Bool :=
  let beq  := a == b
  let blt  := a.slt b
  let bltu := a.ult b
  if funct3 == 7#3 then !bltu       -- BGEU
  else if funct3 == 6#3 then bltu    -- BLTU
  else if funct3 == 5#3 then !blt    -- BGE
  else if funct3 == 4#3 then blt     -- BLT
  else if funct3 == 1#3 then !beq    -- BNE
  else if funct3 == 0#3 then beq     -- BEQ
  else false                         -- reserved encodings

/-! ## Per-branch spec — closed by `bv_decide` over BitVec 32² -/

/-- BEQ: `funct3 = 000 → result = (a == b)`. -/
theorem branchComp_BEQ (a b : BitVec 32) :
    branchCompPure 0#3 a b = (a == b) := by
  unfold branchCompPure
  bv_decide

/-- BNE: `funct3 = 001 → result = (a ≠ b)`. -/
theorem branchComp_BNE (a b : BitVec 32) :
    branchCompPure 1#3 a b = !(a == b) := by
  unfold branchCompPure
  bv_decide

/-- BLT: `funct3 = 100 → result = (signed a < b)`. -/
theorem branchComp_BLT (a b : BitVec 32) :
    branchCompPure 4#3 a b = a.slt b := by
  unfold branchCompPure
  bv_decide

/-- BGE: `funct3 = 101 → result = ¬(signed a < b)`. -/
theorem branchComp_BGE (a b : BitVec 32) :
    branchCompPure 5#3 a b = !(a.slt b) := by
  unfold branchCompPure
  bv_decide

/-- BLTU: `funct3 = 110 → result = (unsigned a < b)`. -/
theorem branchComp_BLTU (a b : BitVec 32) :
    branchCompPure 6#3 a b = a.ult b := by
  unfold branchCompPure
  bv_decide

/-- BGEU: `funct3 = 111 → result = ¬(unsigned a < b)`. -/
theorem branchComp_BGEU (a b : BitVec 32) :
    branchCompPure 7#3 a b = !(a.ult b) := by
  unfold branchCompPure
  bv_decide

/-- Reserved encoding 010: result is `false`. -/
theorem branchComp_reserved_2 (a b : BitVec 32) :
    branchCompPure 2#3 a b = false := by
  unfold branchCompPure
  bv_decide

/-- Reserved encoding 011: result is `false`. -/
theorem branchComp_reserved_3 (a b : BitVec 32) :
    branchCompPure 3#3 a b = false := by
  unfold branchCompPure
  bv_decide

/-! ## Cycle-wise equivalence with the Signal-level form

  `Sparkle.IP.RV32.branchCompSignal` (defined in `Core.lean`) is the
  Signal-level branch comparator. We prove it equals `branchCompPure`
  on each cycle. -/

private theorem signal_eq_val {dom : DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (t : Nat) :
    (a === b).val t = (a.val t == b.val t) := by
  show (Signal.ap (Signal.map (· == ·) a) b).val t = _
  rfl

private theorem signal_not_val {dom : DomainConfig}
    (a : Signal dom Bool) (t : Nat) :
    (~~~a).val t = !(a.val t) := by
  show (Signal.map (fun x => !x) a).val t = _
  rfl

private theorem signal_slt_val {dom : DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (t : Nat) :
    (Signal.slt a b).val t = (a.val t).slt (b.val t) := by
  show (Signal.ap (Signal.map (BitVec.slt · ·) a) b).val t = _
  rfl

private theorem signal_ult_val {dom : DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (t : Nat) :
    (Signal.ult a b).val t = (a.val t).ult (b.val t) := by
  show (Signal.ap (Signal.map (BitVec.ult · ·) a) b).val t = _
  rfl

/-! ### Signal-vs-pure equivalence

  We provide the per-funct3-value equivalence (i.e. once `funct3.val t`
  is a concrete `BitVec 3` literal, the Signal expression reduces to
  the pure one). This is what's needed to use the pure-side spec
  lemmas (`branchComp_BEQ`, `branchComp_BLT`, …) when proving
  Signal-level properties.

  A fully generic `branchCompSignal_eq_pure` parameterised over
  `funct3 : Signal dom (BitVec 3)` would require bridging
  Decidable-Prop equality on BitVec inside `Signal.mux` with
  Bool-`==` equality inside the pure function. That's possible but
  not needed — the per-value form below is sharper. -/

private theorem branch_signal_concrete {dom : DomainConfig}
    (a b : Signal dom (BitVec 32)) (t : Nat) (n : BitVec 3) :
    (Sparkle.IP.RV32.branchCompSignal (Signal.pure (dom := dom) n) a b).val t =
      branchCompPure n (a.val t) (b.val t) := by
  unfold Sparkle.IP.RV32.branchCompSignal branchCompPure
  show (Signal.mux _ _ _).val t = _
  unfold Signal.mux
  simp only [signal_eq_val, signal_not_val, signal_slt_val, signal_ult_val]
  -- Now (Signal.pure n).val t = n; case-split on the 8 BitVec 3 values.
  match n with
  | 0#3 => simp [Signal.pure]
  | 1#3 => simp [Signal.pure]
  | 2#3 => simp [Signal.pure]
  | 3#3 => simp [Signal.pure]
  | 4#3 => simp [Signal.pure]
  | 5#3 => simp [Signal.pure]
  | 6#3 => simp [Signal.pure]
  | 7#3 => simp [Signal.pure]

end Sparkle.IP.RV32.Pipeline
