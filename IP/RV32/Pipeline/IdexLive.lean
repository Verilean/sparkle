/-
  RV32 IDEX-live predicate — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 1484..1487). The
  `idexLive` predicate is the key input to the asynchronous-trap
  PC selector (see `Trap/TrapPC.lean`):

      idexLive  = idex_regWrite ∨ idex_memRead ∨ idex_memWrite
                ∨ idex_jump     ∨ idex_branch  ∨ idex_isCsr
                ∨ idex_isEcall  ∨ idex_isMret  ∨ idex_isSret
                ∨ idex_isAMO    ∨ idex_isMext  ∨ idex_isSFenceVMA

  Spec: `idexLive` fires iff the IDEX-stage instruction has any
  side-effect-bearing control bit set. When all are clear, IDEX
  holds a squashed NOP and the trap should save `pcReg` (not
  `idex_pc`) into mepc.

  This is consequential for trap-PC correctness: if `idexLive`
  is wrong, async traps may save the *previous* committed
  instruction's PC into mepc, causing replay-loops on `sret`.
  Commit 01c7177 (the trapPC-for-async fix) hinges on this
  predicate being correct.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure idexLive -/

/-- 12-way OR over IDEX control bits. -/
@[inline] def idexLivePure
    (idex_regWrite idex_memRead idex_memWrite : Bool)
    (idex_jump idex_branch idex_isCsr : Bool)
    (idex_isEcall idex_isMret idex_isSret : Bool)
    (idex_isAMO idex_isMext idex_isSFenceVMA : Bool) : Bool :=
  idex_regWrite || idex_memRead || idex_memWrite
    || idex_jump || idex_branch || idex_isCsr
    || idex_isEcall || idex_isMret || idex_isSret
    || idex_isAMO || idex_isMext || idex_isSFenceVMA

/-! ## Spec invariants — closed by `decide` -/

/-- All-clear inputs → idexLive = false (squashed NOP). -/
@[simp] theorem idexLive_all_clear :
    idexLivePure false false false false false false
      false false false false false false = false := by
  rfl

/-- A regWrite always makes idexLive fire. -/
@[simp] theorem idexLive_regWrite
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool) :
    idexLivePure true b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 = true := by
  unfold idexLivePure
  revert b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  decide

/-- A memRead always makes idexLive fire. -/
@[simp] theorem idexLive_memRead
    (b0 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool) :
    idexLivePure b0 true b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 = true := by
  unfold idexLivePure
  revert b0 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  decide

/-- A memWrite always makes idexLive fire. -/
@[simp] theorem idexLive_memWrite
    (b0 b1 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool) :
    idexLivePure b0 b1 true b3 b4 b5 b6 b7 b8 b9 b10 b11 = true := by
  unfold idexLivePure
  revert b0 b1 b3 b4 b5 b6 b7 b8 b9 b10 b11
  decide

/-- A jump always makes idexLive fire. -/
@[simp] theorem idexLive_jump
    (b0 b1 b2 b4 b5 b6 b7 b8 b9 b10 b11 : Bool) :
    idexLivePure b0 b1 b2 true b4 b5 b6 b7 b8 b9 b10 b11 = true := by
  unfold idexLivePure
  revert b0 b1 b2 b4 b5 b6 b7 b8 b9 b10 b11
  decide

/-- A branch always makes idexLive fire. -/
@[simp] theorem idexLive_branch
    (b0 b1 b2 b3 b5 b6 b7 b8 b9 b10 b11 : Bool) :
    idexLivePure b0 b1 b2 b3 true b5 b6 b7 b8 b9 b10 b11 = true := by
  unfold idexLivePure
  revert b0 b1 b2 b3 b5 b6 b7 b8 b9 b10 b11
  decide

/-- A CSR access always makes idexLive fire. -/
@[simp] theorem idexLive_isCsr
    (b0 b1 b2 b3 b4 b6 b7 b8 b9 b10 b11 : Bool) :
    idexLivePure b0 b1 b2 b3 b4 true b6 b7 b8 b9 b10 b11 = true := by
  unfold idexLivePure
  revert b0 b1 b2 b3 b4 b6 b7 b8 b9 b10 b11
  decide

/-- An ECALL always makes idexLive fire. -/
@[simp] theorem idexLive_isEcall
    (b0 b1 b2 b3 b4 b5 b7 b8 b9 b10 b11 : Bool) :
    idexLivePure b0 b1 b2 b3 b4 b5 true b7 b8 b9 b10 b11 = true := by
  unfold idexLivePure
  revert b0 b1 b2 b3 b4 b5 b7 b8 b9 b10 b11
  decide

/-- MRET always makes idexLive fire. -/
@[simp] theorem idexLive_isMret
    (b0 b1 b2 b3 b4 b5 b6 b8 b9 b10 b11 : Bool) :
    idexLivePure b0 b1 b2 b3 b4 b5 b6 true b8 b9 b10 b11 = true := by
  unfold idexLivePure
  revert b0 b1 b2 b3 b4 b5 b6 b8 b9 b10 b11
  decide

/-- SRET always makes idexLive fire. -/
@[simp] theorem idexLive_isSret
    (b0 b1 b2 b3 b4 b5 b6 b7 b9 b10 b11 : Bool) :
    idexLivePure b0 b1 b2 b3 b4 b5 b6 b7 true b9 b10 b11 = true := by
  unfold idexLivePure
  revert b0 b1 b2 b3 b4 b5 b6 b7 b9 b10 b11
  decide

/-- AMO always makes idexLive fire. -/
@[simp] theorem idexLive_isAMO
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b10 b11 : Bool) :
    idexLivePure b0 b1 b2 b3 b4 b5 b6 b7 b8 true b10 b11 = true := by
  unfold idexLivePure
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b10 b11
  decide

/-- M-extension (MUL/DIV) always makes idexLive fire. -/
@[simp] theorem idexLive_isMext
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b11 : Bool) :
    idexLivePure b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 true b11 = true := by
  unfold idexLivePure
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b11
  decide

/-- SFENCE.VMA always makes idexLive fire. -/
@[simp] theorem idexLive_isSFenceVMA
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool) :
    idexLivePure b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 true = true := by
  unfold idexLivePure
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  decide

/-! ## Composite spec -/

theorem idexLivePure_spec :
    ∀ (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool),
      idexLivePure b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 =
        (b0 || b1 || b2 || b3 || b4 || b5 || b6 || b7 || b8 || b9 || b10 || b11) := by
  decide

/-! ## Signal-level wrapper -/

def idexLiveSignal {dom : DomainConfig}
    (idex_regWrite idex_memRead idex_memWrite : Signal dom Bool)
    (idex_jump idex_branch idex_isCsr : Signal dom Bool)
    (idex_isEcall idex_isMret idex_isSret : Signal dom Bool)
    (idex_isAMO idex_isMext idex_isSFenceVMA : Signal dom Bool)
    : Signal dom Bool :=
  idex_regWrite ||| idex_memRead ||| idex_memWrite
    ||| idex_jump ||| idex_branch ||| idex_isCsr
    ||| idex_isEcall ||| idex_isMret ||| idex_isSret
    ||| idex_isAMO ||| idex_isMext ||| idex_isSFenceVMA

/-! ## All-clear → idexLive = false

  When every control bit is `false` (the squashed-NOP state),
  `idexLive` is also `false`. This is the form needed when
  combining with `idex_squash_clears_next_cycle` (in
  Pipeline/FlushSquash.lean) to show "squash at N → idexLive
  at N+1 = false". -/

theorem idexLive_false_of_all_clear
    (idex_regWrite idex_memRead idex_memWrite
     idex_jump idex_branch idex_isCsr
     idex_isEcall idex_isMret idex_isSret
     idex_isAMO idex_isMext idex_isSFenceVMA : Bool)
    (h0 : idex_regWrite = false) (h1 : idex_memRead = false)
    (h2 : idex_memWrite = false) (h3 : idex_jump = false)
    (h4 : idex_branch = false) (h5 : idex_isCsr = false)
    (h6 : idex_isEcall = false) (h7 : idex_isMret = false)
    (h8 : idex_isSret = false) (h9 : idex_isAMO = false)
    (h10 : idex_isMext = false) (h11 : idex_isSFenceVMA = false) :
    idexLivePure idex_regWrite idex_memRead idex_memWrite
      idex_jump idex_branch idex_isCsr
      idex_isEcall idex_isMret idex_isSret
      idex_isAMO idex_isMext idex_isSFenceVMA = false := by
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  rfl

end Sparkle.IP.RV32.Pipeline
