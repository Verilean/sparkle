/-
  RV32 PTW request gating + vaddr-latch — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 1607..1616). The PTW
  starts a walk when EITHER side has a TLB miss; D-side has
  priority. The vaddr to walk is latched on the start cycle.

  Spec:

    ifetchPTWReq = ifetchTLBMiss
                 ∧ ptwIdle ∧ !dTLBMiss
                 ∧ MMU-idle ∧ !trap_taken

    ptwReq        = dTLBMiss ∨ ifetchPTWReq

    ptwVaddrOnStart = dTLBMiss ? alu_result : fetchPC
                                          (D priority)

    ptwVaddrNext  = (ptwIdle ∧ ptwReq) ? ptwVaddrOnStart
                                       : ptwVaddr  (hold)

  The "no PTW during trap" gating on `ifetchPTWReq` prevents the
  PTW from starting on a stale fetchPC — when a trap fires, the
  fetchPC is about to be redirected to mtvec, and starting a
  PTW with the old fetchPC would walk a wrong address.

  The "D-side priority" rule prevents two simultaneous walks: if
  both sides miss in the same cycle, D wins (the D-side walk
  completes first; the I-side will retry on the next idle cycle).
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.MMU

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure PTW request gating -/

/-- I-side PTW request: only fire when D-side isn't asking and the
    MMU+PTW are quiescent and no trap is firing. -/
@[inline] def ifetchPTWReqPure
    (ifetchTLBMiss ptwIsIdle dTLBMiss isMMUIdle trap_taken : Bool) : Bool :=
  ifetchTLBMiss && ptwIsIdle && !dTLBMiss && isMMUIdle && !trap_taken

/-- PTW request: D-side OR (gated) I-side. -/
@[inline] def ptwReqPure (dTLBMiss ifetchPTWReq : Bool) : Bool :=
  dTLBMiss || ifetchPTWReq

/-- PTW vaddr-on-start: D-side wins on tie. -/
@[inline] def ptwVaddrOnStartPure
    (dTLBMiss : Bool) (alu_result fetchPC : BitVec 32) : BitVec 32 :=
  if dTLBMiss then alu_result else fetchPC

/-- PTW vaddr next: latch on idle+req start, hold otherwise. -/
@[inline] def ptwVaddrNextPure
    (ptwIsIdle ptwReq : Bool)
    (ptwVaddrOnStart ptwVaddr : BitVec 32) : BitVec 32 :=
  if ptwIsIdle && ptwReq then ptwVaddrOnStart else ptwVaddr

/-! ## Spec invariants — closed by `decide` / `rfl` -/

/-- D-side miss without I-side miss → ptwReq fires from D. -/
theorem ptwReq_d_only (ifetchPTWReq : Bool) :
    ptwReqPure true ifetchPTWReq = true := by
  unfold ptwReqPure
  cases ifetchPTWReq <;> rfl

/-- No miss on either side → no ptwReq. -/
@[simp] theorem ptwReq_none : ptwReqPure false false = false := by rfl

/-- ifetchPTWReq excludes D-priority (D-side miss inhibits I-walk start). -/
@[simp] theorem ifetchPTWReq_d_priority
    (ifetchTLBMiss ptwIsIdle isMMUIdle trap_taken : Bool) :
    ifetchPTWReqPure ifetchTLBMiss ptwIsIdle true isMMUIdle trap_taken = false := by
  unfold ifetchPTWReqPure
  cases ifetchTLBMiss <;> cases ptwIsIdle <;> cases isMMUIdle <;>
    cases trap_taken <;> rfl

/-- ifetchPTWReq is gated by trap_taken (no walk during trap). -/
@[simp] theorem ifetchPTWReq_trap_gates
    (ifetchTLBMiss ptwIsIdle dTLBMiss isMMUIdle : Bool) :
    ifetchPTWReqPure ifetchTLBMiss ptwIsIdle dTLBMiss isMMUIdle true = false := by
  unfold ifetchPTWReqPure
  cases ifetchTLBMiss <;> cases ptwIsIdle <;> cases dTLBMiss <;>
    cases isMMUIdle <;> rfl

/-- ifetchPTWReq requires the MMU to be idle. -/
@[simp] theorem ifetchPTWReq_mmu_busy
    (ifetchTLBMiss ptwIsIdle dTLBMiss trap_taken : Bool) :
    ifetchPTWReqPure ifetchTLBMiss ptwIsIdle dTLBMiss false trap_taken = false := by
  unfold ifetchPTWReqPure
  cases ifetchTLBMiss <;> cases ptwIsIdle <;> cases dTLBMiss <;>
    cases trap_taken <;> rfl

/-- ifetchPTWReq requires PTW to be idle. -/
@[simp] theorem ifetchPTWReq_ptw_busy
    (ifetchTLBMiss dTLBMiss isMMUIdle trap_taken : Bool) :
    ifetchPTWReqPure ifetchTLBMiss false dTLBMiss isMMUIdle trap_taken = false := by
  unfold ifetchPTWReqPure
  cases ifetchTLBMiss <;> cases dTLBMiss <;> cases isMMUIdle <;>
    cases trap_taken <;> rfl

/-- All gates clear + I-side miss → fire. -/
theorem ifetchPTWReq_fires :
    ifetchPTWReqPure true true false true false = true := by rfl

/-! ### vaddr-on-start spec -/

/-- D-side miss → use alu_result (D-side priority). -/
@[simp] theorem ptwVaddrOnStart_d (alu_result fetchPC : BitVec 32) :
    ptwVaddrOnStartPure true alu_result fetchPC = alu_result := by rfl

/-- No D-side miss → use fetchPC. -/
@[simp] theorem ptwVaddrOnStart_i (alu_result fetchPC : BitVec 32) :
    ptwVaddrOnStartPure false alu_result fetchPC = fetchPC := by rfl

/-! ### vaddr-latch spec -/

/-- Idle + req → latch new vaddr. -/
@[simp] theorem ptwVaddrNext_latch (ptwVaddrOnStart ptwVaddr : BitVec 32) :
    ptwVaddrNextPure true true ptwVaddrOnStart ptwVaddr = ptwVaddrOnStart := by rfl

/-- Non-idle PTW → hold (the FSM is already walking). -/
theorem ptwVaddrNext_hold_busy
    (ptwReq : Bool) (ptwVaddrOnStart ptwVaddr : BitVec 32) :
    ptwVaddrNextPure false ptwReq ptwVaddrOnStart ptwVaddr = ptwVaddr := by
  unfold ptwVaddrNextPure
  cases ptwReq <;> rfl

/-- No req on idle → hold. -/
theorem ptwVaddrNext_hold_no_req (ptwVaddrOnStart ptwVaddr : BitVec 32) :
    ptwVaddrNextPure true false ptwVaddrOnStart ptwVaddr = ptwVaddr := by rfl

/-! ## Composite specs -/

theorem ifetchPTWReqPure_spec
    (ifetchTLBMiss ptwIsIdle dTLBMiss isMMUIdle trap_taken : Bool) :
    ifetchPTWReqPure ifetchTLBMiss ptwIsIdle dTLBMiss isMMUIdle trap_taken =
      (ifetchTLBMiss && ptwIsIdle && !dTLBMiss && isMMUIdle && !trap_taken) := by rfl

theorem ptwReqPure_spec (dTLBMiss ifetchPTWReq : Bool) :
    ptwReqPure dTLBMiss ifetchPTWReq = (dTLBMiss || ifetchPTWReq) := by rfl

/-! ## Signal-level wrappers -/

def ifetchPTWReqSignal {dom : DomainConfig}
    (ifetchTLBMiss ptwIsIdle dTLBMiss isMMUIdle trap_taken : Signal dom Bool)
    : Signal dom Bool :=
  ifetchTLBMiss &&&
    (ptwIsIdle &&& ((~~~dTLBMiss) &&& (isMMUIdle &&& (~~~trap_taken))))

def ptwReqSignal {dom : DomainConfig}
    (dTLBMiss ifetchPTWReq : Signal dom Bool) : Signal dom Bool :=
  dTLBMiss ||| ifetchPTWReq

def ptwVaddrOnStartSignal {dom : DomainConfig}
    (dTLBMiss : Signal dom Bool)
    (alu_result fetchPC : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux dTLBMiss alu_result fetchPC

def ptwVaddrNextSignal {dom : DomainConfig}
    (ptwIsIdle ptwReq : Signal dom Bool)
    (ptwVaddrOnStart ptwVaddr : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux (ptwIsIdle &&& ptwReq) ptwVaddrOnStart ptwVaddr

end Sparkle.IP.RV32.MMU
