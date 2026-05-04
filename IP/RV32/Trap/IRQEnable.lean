/-
  RV32 interrupt-enable predicates — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (~lines 870..976). Computes
  whether each kind of interrupt fires this cycle, given the
  current privilege, mstatus.{MIE,SIE} flags, mie.{MTIE,MSIE}
  bits, mideleg.{MTI,MSI} bits, sie.{STIE,SSIE,SEIE} bits, the
  software-pending bits in mipSoftReg.{STIP,SSIP,SEIP}, and the
  hardware-derived `timerIrq` / `swIrq`.

  Three M-mode interrupts modeled: timer (MTI), software (MSI).
  External (MEI) is omitted because Sparkle has no external
  interrupt controller wired in.

  Three S-mode interrupts modeled: timer (STI), software (SSI),
  external (SEI). All are delivered through `mipSoftReg` since
  S-mode pending bits are software-writable in our SoC.

  Spec (per RISC-V priv spec, Vol II §3.1.6 + §4.1.3):

      M-mode timer fires iff
        ( (priv=M ∧ mstatus.MIE) ∨ priv<M ) ∧ mie.MTIE ∧ timerIrq
        ∧ ¬mideleg.MTI

      S-mode timer fires iff
        ( (priv=S ∧ mstatus.SIE) ∨ priv=U )
        ∧ sie.STIE ∧ mip.STIP

  (Symmetric for software/external.)

  Note that the S-mode predicate does NOT mention the mideleg
  bit: in our hardware, the S-mode handler only runs after the
  trap is delegated (handled separately in `Trap/Delegation.lean`).
  Whether a *given* pending S-bit is enabled here is the local
  question; whether it routes to S vs M is the delegation
  question.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Trap

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure boolean predicates -/

/-- M-mode interrupt enable mask.

    True iff the architectural condition for M-mode interrupts to
    be unmasked at this privilege level is met:
      - in M-mode: requires `mstatus.MIE = 1`
      - in S/U-mode: always unmasked (interrupts to higher priv
        are always enabled per the priv spec). -/
@[inline] def mModeIntEnablePure
    (privIsM mstatusMIE : Bool) : Bool :=
  (privIsM && mstatusMIE) || !privIsM

/-- M-mode timer interrupt fires this cycle. -/
@[inline] def mTimerIntEnabledPure
    (privIsM mstatusMIE mieMTIE timerIrq mTimerNotDelegated : Bool) : Bool :=
  mModeIntEnablePure privIsM mstatusMIE
    && mieMTIE && timerIrq && mTimerNotDelegated

/-- M-mode software interrupt fires this cycle. -/
@[inline] def mSwIntEnabledPure
    (privIsM mstatusMIE mieMSIE swIrq mSwNotDelegated : Bool) : Bool :=
  mModeIntEnablePure privIsM mstatusMIE
    && mieMSIE && swIrq && mSwNotDelegated

/-- S-mode interrupt enable mask. True iff the S-mode unmask
    condition is met for the current privilege. -/
@[inline] def sModeIntEnablePure
    (privIsS privIsU mstatusSIE : Bool) : Bool :=
  (privIsS && mstatusSIE) || privIsU

/-- S-mode timer interrupt fires this cycle. -/
@[inline] def sTimerIntEnabledPure
    (privIsS privIsU mstatusSIE sieSTIE stipPending : Bool) : Bool :=
  sModeIntEnablePure privIsS privIsU mstatusSIE
    && sieSTIE && stipPending

/-- S-mode software interrupt fires this cycle. -/
@[inline] def sSwIntEnabledPure
    (privIsS privIsU mstatusSIE sieSSIE ssipPending : Bool) : Bool :=
  sModeIntEnablePure privIsS privIsU mstatusSIE
    && sieSSIE && ssipPending

/-- S-mode external interrupt fires this cycle. -/
@[inline] def sExtIntEnabledPure
    (privIsS privIsU mstatusSIE sieSEIE seipPending : Bool) : Bool :=
  sModeIntEnablePure privIsS privIsU mstatusSIE
    && sieSEIE && seipPending

/-! ## Spec invariants — closed by `decide` over Bool^n -/

/-- In M-mode with MIE clear, M-mode interrupts are masked. -/
@[simp] theorem mTimer_M_no_MIE
    (mieMTIE timerIrq mTimerNotDeleg : Bool) :
    mTimerIntEnabledPure true false mieMTIE timerIrq mTimerNotDeleg = false := by
  revert mieMTIE timerIrq mTimerNotDeleg; decide

/-- In M-mode with MIE set and MTIE+pending+notDeleg, M-timer fires. -/
@[simp] theorem mTimer_M_MIE_set :
    mTimerIntEnabledPure true true true true true = true := by
  decide

/-- In a non-M mode, the MIE bit is irrelevant for M-mode interrupts. -/
theorem mTimer_nonM_ignores_MIE
    (mstatusMIE mieMTIE timerIrq mTimerNotDeleg : Bool) :
    mTimerIntEnabledPure false mstatusMIE mieMTIE timerIrq mTimerNotDeleg
      = (mieMTIE && timerIrq && mTimerNotDeleg) := by
  revert mstatusMIE mieMTIE timerIrq mTimerNotDeleg; decide

/-- A delegated M-mode timer interrupt does NOT fire on the M-mode path. -/
@[simp] theorem mTimer_delegated_drops
    (privIsM mstatusMIE mieMTIE timerIrq : Bool) :
    mTimerIntEnabledPure privIsM mstatusMIE mieMTIE timerIrq false = false := by
  revert privIsM mstatusMIE mieMTIE timerIrq; decide

/-- An M-mode timer with no pending IRQ does not fire. -/
@[simp] theorem mTimer_no_irq_drops
    (privIsM mstatusMIE mieMTIE mTimerNotDeleg : Bool) :
    mTimerIntEnabledPure privIsM mstatusMIE mieMTIE false mTimerNotDeleg = false := by
  revert privIsM mstatusMIE mieMTIE mTimerNotDeleg; decide

/-- In M-mode (priv=M), S-mode interrupts are masked. -/
@[simp] theorem sTimer_M_masked
    (mstatusSIE sieSTIE stipPending : Bool) :
    sTimerIntEnabledPure false false mstatusSIE sieSTIE stipPending = false := by
  revert mstatusSIE sieSTIE stipPending; decide

/-- In U-mode, S-mode interrupts ignore mstatus.SIE. -/
theorem sTimer_U_ignores_SIE
    (mstatusSIE sieSTIE stipPending : Bool) :
    sTimerIntEnabledPure false true mstatusSIE sieSTIE stipPending
      = (sieSTIE && stipPending) := by
  revert mstatusSIE sieSTIE stipPending; decide

/-- In S-mode, S-mode interrupts require mstatus.SIE. -/
theorem sTimer_S_requires_SIE
    (sieSTIE stipPending : Bool) :
    sTimerIntEnabledPure true false false sieSTIE stipPending = false := by
  revert sieSTIE stipPending; decide

/-- In S-mode with SIE+STIE+pending, S-timer fires. -/
@[simp] theorem sTimer_S_SIE_set :
    sTimerIntEnabledPure true false true true true = true := by
  decide

/-! ## Composite spec — exhaustive truth tables -/

/-- M-timer's spec. Closed by `decide` over Bool^5 (32 cases). -/
theorem mTimerIntEnabledPure_spec :
    ∀ (privIsM mstatusMIE mieMTIE timerIrq mTimerNotDeleg : Bool),
      mTimerIntEnabledPure privIsM mstatusMIE mieMTIE timerIrq mTimerNotDeleg
        = (((privIsM && mstatusMIE) || !privIsM)
            && mieMTIE && timerIrq && mTimerNotDeleg) := by
  decide

/-- S-timer's spec. Closed by `decide` over Bool^5. -/
theorem sTimerIntEnabledPure_spec :
    ∀ (privIsS privIsU mstatusSIE sieSTIE stipPending : Bool),
      sTimerIntEnabledPure privIsS privIsU mstatusSIE sieSTIE stipPending
        = (((privIsS && mstatusSIE) || privIsU) && sieSTIE && stipPending) := by
  decide

/-! ## Signal-level wrappers -/

/-- Signal-level `mModeIntEnable`. -/
def mModeIntEnableSignal {dom : DomainConfig}
    (privIsM mstatusMIE : Signal dom Bool) : Signal dom Bool :=
  (privIsM &&& mstatusMIE) ||| (~~~privIsM)

/-- Signal-level `sModeIntEnable`. -/
def sModeIntEnableSignal {dom : DomainConfig}
    (privIsS privIsU mstatusSIE : Signal dom Bool) : Signal dom Bool :=
  (privIsS &&& mstatusSIE) ||| privIsU

/-- Signal-level `mTimerIntEnabled`. -/
def mTimerIntEnabledSignal {dom : DomainConfig}
    (privIsM mstatusMIE mieMTIE timerIrq mTimerNotDeleg : Signal dom Bool)
    : Signal dom Bool :=
  mModeIntEnableSignal privIsM mstatusMIE
    &&& (mieMTIE &&& timerIrq) &&& mTimerNotDeleg

/-- Signal-level `mSwIntEnabled`. -/
def mSwIntEnabledSignal {dom : DomainConfig}
    (privIsM mstatusMIE mieMSIE swIrq mSwNotDeleg : Signal dom Bool)
    : Signal dom Bool :=
  mModeIntEnableSignal privIsM mstatusMIE
    &&& (mieMSIE &&& swIrq) &&& mSwNotDeleg

/-- Signal-level `sTimerIntEnabled`. -/
def sTimerIntEnabledSignal {dom : DomainConfig}
    (privIsS privIsU mstatusSIE sieSTIE stipPending : Signal dom Bool)
    : Signal dom Bool :=
  sModeIntEnableSignal privIsS privIsU mstatusSIE
    &&& sieSTIE &&& stipPending

/-- Signal-level `sSwIntEnabled`. -/
def sSwIntEnabledSignal {dom : DomainConfig}
    (privIsS privIsU mstatusSIE sieSSIE ssipPending : Signal dom Bool)
    : Signal dom Bool :=
  sModeIntEnableSignal privIsS privIsU mstatusSIE
    &&& sieSSIE &&& ssipPending

/-- Signal-level `sExtIntEnabled`. -/
def sExtIntEnabledSignal {dom : DomainConfig}
    (privIsS privIsU mstatusSIE sieSEIE seipPending : Signal dom Bool)
    : Signal dom Bool :=
  sModeIntEnableSignal privIsS privIsU mstatusSIE
    &&& sieSEIE &&& seipPending

/-! ## Signal-vs-pure equivalence -/

/-- Helper: `(a &&& b).val t = a.val t && b.val t`. -/
private theorem signal_and_val {dom : DomainConfig}
    (a b : Signal dom Bool) (t : Nat) :
    (a &&& b).val t = (a.val t && b.val t) := by
  show (Signal.ap (Signal.map (· && ·) a) b).val t = _
  rfl

/-- Helper: `(a ||| b).val t = a.val t || b.val t`. -/
private theorem signal_or_val {dom : DomainConfig}
    (a b : Signal dom Bool) (t : Nat) :
    (a ||| b).val t = (a.val t || b.val t) := by
  show (Signal.ap (Signal.map (· || ·) a) b).val t = _
  rfl

/-- Helper: `(~~~a).val t = !(a.val t)`. -/
private theorem signal_not_val {dom : DomainConfig}
    (a : Signal dom Bool) (t : Nat) :
    (~~~a).val t = !(a.val t) := by
  show (Signal.map (fun x => !x) a).val t = _
  rfl

/-- Cycle-wise: `mTimerIntEnabledSignal = mTimerIntEnabledPure`. -/
theorem mTimerIntEnabledSignal_eq_pure {dom : DomainConfig}
    (privIsM mstatusMIE mieMTIE timerIrq mTimerNotDeleg : Signal dom Bool) (t : Nat) :
    (mTimerIntEnabledSignal privIsM mstatusMIE mieMTIE timerIrq mTimerNotDeleg).val t =
      mTimerIntEnabledPure (privIsM.val t) (mstatusMIE.val t)
        (mieMTIE.val t) (timerIrq.val t) (mTimerNotDeleg.val t) := by
  unfold mTimerIntEnabledSignal mModeIntEnableSignal
    mTimerIntEnabledPure mModeIntEnablePure
  simp [signal_and_val, signal_or_val, signal_not_val, Bool.and_assoc]

/-- Cycle-wise: `sTimerIntEnabledSignal = sTimerIntEnabledPure`. -/
theorem sTimerIntEnabledSignal_eq_pure {dom : DomainConfig}
    (privIsS privIsU mstatusSIE sieSTIE stipPending : Signal dom Bool) (t : Nat) :
    (sTimerIntEnabledSignal privIsS privIsU mstatusSIE sieSTIE stipPending).val t =
      sTimerIntEnabledPure (privIsS.val t) (privIsU.val t)
        (mstatusSIE.val t) (sieSTIE.val t) (stipPending.val t) := by
  unfold sTimerIntEnabledSignal sModeIntEnableSignal
    sTimerIntEnabledPure sModeIntEnablePure
  simp [signal_and_val, signal_or_val, Bool.and_assoc]

end Sparkle.IP.RV32.Trap
