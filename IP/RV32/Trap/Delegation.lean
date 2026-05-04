/-
  RV32 trap delegation — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean`. Trap delegation routes a trap to
  S-mode (instead of the default M-mode) when:
    1. The trap's cause bit is set in mideleg (interrupts) or medeleg
       (synchronous exceptions).
    2. Current privilege is ≤ S (i.e., U or S, not M).

  This file isolates the *destination decision* (S or M) given the
  delegation lookup result and the current privilege. The lookup
  itself (medeleg/mideleg shift+test) is also captured but as a
  combinational op, not a separate decision point.

  Per RISC-V priv spec, Vol II §3.1.8 (medeleg/mideleg):
  - delegation bit set + priv < M  ⇒  trap to S-mode
  - else  ⇒  trap to M-mode

  In our hardware, M cannot trap to S regardless of delegation, which
  the `priv ≤ S` clause encodes.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Trap

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure decision functions -/

/--
  Given the lookup result `delegated` (= medeleg-or-mideleg bit for
  this trap's cause) and `privLeS` (= current priv ≤ S), decide where
  the trap goes if `trap_taken` is asserted.

  Returns `(trapToS, trapToM)` as a pair. Mutually exclusive: at most
  one is `true`, and if `trap_taken` is `false`, both are `false`.
-/
@[inline] def trapDestPure
    (trapTaken delegated privLeS : Bool) : Bool × Bool :=
  let trapToS := trapTaken && delegated && privLeS
  let trapToM := trapTaken && !trapToS
  (trapToS, trapToM)

/-- `trapToS` projection of `trapDestPure`. -/
@[inline] def trapToSPure (trapTaken delegated privLeS : Bool) : Bool :=
  (trapDestPure trapTaken delegated privLeS).1

/-- `trapToM` projection of `trapDestPure`. -/
@[inline] def trapToMPure (trapTaken delegated privLeS : Bool) : Bool :=
  (trapDestPure trapTaken delegated privLeS).2

/-! ## Spec invariants — closed by `decide` over Bool³ -/

/-- A non-trap cycle goes nowhere. -/
@[simp] theorem trapDest_no_trap
    (delegated privLeS : Bool) :
    trapDestPure false delegated privLeS = (false, false) := by
  revert delegated privLeS; decide

/-- A trap with delegation set, while priv ≤ S, goes to S-mode. -/
@[simp] theorem trapDest_to_S :
    trapDestPure true true true = (true, false) := by
  decide

/-- A trap that's not delegated goes to M-mode. -/
@[simp] theorem trapDest_no_deleg
    (privLeS : Bool) :
    trapDestPure true false privLeS = (false, true) := by
  revert privLeS; decide

/-- A trap delegated to S but taken in M-mode (priv > S) still goes
    to M (we can't drop privilege in a trap). -/
@[simp] theorem trapDest_M_overrides
    (delegated : Bool) :
    trapDestPure true delegated false = (false, true) := by
  revert delegated; decide

/-- Mutual exclusion: trapToS and trapToM are never both true. -/
theorem trapDest_mutex
    (trapTaken delegated privLeS : Bool) :
    let (s, m) := trapDestPure trapTaken delegated privLeS
    !(s && m) := by
  revert trapTaken delegated privLeS; decide

/-- Disjunction with trap_taken: if a trap is taken it goes somewhere. -/
theorem trapDest_total
    (trapTaken delegated privLeS : Bool) :
    let (s, m) := trapDestPure trapTaken delegated privLeS
    trapTaken = (s || m) := by
  revert trapTaken delegated privLeS; decide

/-! ## Composite spec -/

/--
  Exhaustive spec on Bool³ — every (trapTaken, delegated, privLeS)
  combination produces the correct (trapToS, trapToM) pair.

  This is the single statement we want CI to depend on. -/
theorem trapDestPure_spec :
    ∀ (trapTaken delegated privLeS : Bool),
      trapDestPure trapTaken delegated privLeS =
        ( trapTaken && delegated && privLeS
        , trapTaken && !(trapTaken && delegated && privLeS) ) := by
  decide

/-! ## Signal-level wrappers (split into two so the synth backend can
    accept them — it does not handle Prod return types). -/

/-- Signal-level `trapToS` (cycle-wise lift of `trapToSPure`). -/
def trapToSSignal {dom : DomainConfig}
    (trapTaken delegated privLeS : Signal dom Bool)
    : Signal dom Bool :=
  trapTaken &&& (delegated &&& privLeS)

/-- Signal-level `trapToM` (cycle-wise lift of `trapToMPure`). -/
def trapToMSignal {dom : DomainConfig}
    (trapTaken delegated privLeS : Signal dom Bool)
    : Signal dom Bool :=
  trapTaken &&& (~~~(trapToSSignal trapTaken delegated privLeS))

/-- Helper: `(a &&& b).val t = a.val t && b.val t` for `Signal Bool`. -/
private theorem signal_and_val {dom : DomainConfig}
    (a b : Signal dom Bool) (t : Nat) :
    (a &&& b).val t = (a.val t && b.val t) := by
  show (Signal.ap (Signal.map (· && ·) a) b).val t = _
  rfl

/-- Helper: `(~~~a).val t = !(a.val t)` for `Signal Bool`. -/
private theorem signal_not_val {dom : DomainConfig}
    (a : Signal dom Bool) (t : Nat) :
    (~~~a).val t = !(a.val t) := by
  show (Signal.map (fun x => !x) a).val t = _
  rfl

/-- Cycle-wise equivalence: `trapToSSignal = trapToSPure`. -/
theorem trapToSSignal_eq_pure {dom : DomainConfig}
    (trapTaken delegated privLeS : Signal dom Bool) (t : Nat) :
    (trapToSSignal trapTaken delegated privLeS).val t =
      trapToSPure (trapTaken.val t) (delegated.val t)
        (privLeS.val t) := by
  unfold trapToSSignal trapToSPure trapDestPure
  simp [signal_and_val, Bool.and_assoc]

/-- Cycle-wise equivalence: `trapToMSignal = trapToMPure`. -/
theorem trapToMSignal_eq_pure {dom : DomainConfig}
    (trapTaken delegated privLeS : Signal dom Bool) (t : Nat) :
    (trapToMSignal trapTaken delegated privLeS).val t =
      trapToMPure (trapTaken.val t) (delegated.val t)
        (privLeS.val t) := by
  unfold trapToMSignal trapToSSignal trapToMPure trapDestPure
  simp [signal_and_val, signal_not_val, Bool.and_assoc]

/-! ## Cause-bit decoders (used as inputs to the delegation lookup) -/

/-- isInterrupt: bit 31 of trap cause. -/
@[inline] def isInterruptPure (trapCause : BitVec 32) : Bool :=
  trapCause.extractLsb' 31 1 == 1#1

/-- causeIdx: low 5 bits of trap cause (the cause index for medeleg/mideleg). -/
@[inline] def causeIdxPure (trapCause : BitVec 32) : BitVec 5 :=
  trapCause.extractLsb' 0 5

/-- causeIdxExt: cause-idx zero-extended to 32 bits (for use as a shift amount). -/
@[inline] def causeIdxExtPure (trapCause : BitVec 32) : BitVec 32 :=
  (0#27 : BitVec 27) ++ causeIdxPure trapCause

/-! ## Delegation-bit lookup -/

/-- Test whether bit `idx` of `delegReg` is set.
    `delegReg >>> idxExt` shifts the relevant bit to position 0,
    where we extract it. -/
@[inline] def delegBitPure (delegReg : BitVec 32) (idxExt : BitVec 32) : Bool :=
  ((delegReg >>> idxExt).extractLsb' 0 1) == 1#1

/-- Combined delegation: pick mideleg if interrupt, medeleg otherwise. -/
@[inline] def delegatedPure
    (isInterrupt : Bool) (medelegReg midelegReg : BitVec 32)
    (idxExt : BitVec 32) : Bool :=
  if isInterrupt then delegBitPure midelegReg idxExt
  else delegBitPure medelegReg idxExt

/-! ## Spec invariants — closed by `bv_decide` -/

/-- isInterrupt is set iff cause's MSB is 1. -/
theorem isInterrupt_msb (trapCause : BitVec 32) :
    isInterruptPure trapCause = (trapCause.extractLsb' 31 1 == 1#1) := by rfl

/-- causeIdxExt has zero high bits. -/
theorem causeIdxExt_high_zero (trapCause : BitVec 32) :
    (causeIdxExtPure trapCause).extractLsb' 5 27 = 0#27 := by
  unfold causeIdxExtPure causeIdxPure
  bv_decide

/-- causeIdxExt's low 5 bits = causeIdx. -/
theorem causeIdxExt_low_eq (trapCause : BitVec 32) :
    (causeIdxExtPure trapCause).extractLsb' 0 5 = causeIdxPure trapCause := by
  unfold causeIdxExtPure
  bv_decide

/-! ## Signal-level wrappers -/

def isInterruptSignal {dom : DomainConfig}
    (trapCause : Signal dom (BitVec 32)) : Signal dom Bool :=
  (trapCause.map (BitVec.extractLsb' 31 1 ·)) === 1#1

def causeIdxSignal {dom : DomainConfig}
    (trapCause : Signal dom (BitVec 32)) : Signal dom (BitVec 5) :=
  trapCause.map (BitVec.extractLsb' 0 5 ·)

def causeIdxExtSignal {dom : DomainConfig}
    (trapCause : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let zero27 : Signal dom (BitVec 27) := Signal.pure 0#27
  zero27 ++ causeIdxSignal trapCause

def delegBitSignal {dom : DomainConfig}
    (delegReg idxExt : Signal dom (BitVec 32)) : Signal dom Bool :=
  ((delegReg >>> idxExt).map (BitVec.extractLsb' 0 1 ·)) === 1#1

def delegatedSignal {dom : DomainConfig}
    (isInterrupt : Signal dom Bool)
    (medelegReg midelegReg idxExt : Signal dom (BitVec 32)) : Signal dom Bool :=
  Signal.mux isInterrupt (delegBitSignal midelegReg idxExt) (delegBitSignal medelegReg idxExt)

end Sparkle.IP.RV32.Trap
