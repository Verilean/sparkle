/-
  RV32 UART 8250 register decode — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (~lines 1356..1379). The
  Sparkle SoC includes an 8250-compatible UART at PA 0x10000000,
  with 8 register offsets (3 bits) and DLAB-aware register
  selection.

  Per 8250 UART spec:

    offset  DLAB=0          DLAB=1
    ------  --------------  ----------------
    0       RBR (read)      DLL (divisor low)
    0       THR (write)     DLL (divisor low)
    1       IER             DLM (divisor high)
    2       IIR (read)      —
    2       FCR (write)     —
    3       LCR             LCR  (DLAB lives here, bit 7)
    4       MCR             MCR
    5       LSR             —
    6       MSR             —
    7       SCR             SCR

  Register write-commits follow the standard `csrPlainNextSignal`
  shape but with offset+DLAB gating.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.UART

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure offset matchers -/

@[inline] def uartOffPure (offset : BitVec 3) (n : BitVec 3) : Bool :=
  offset == n

@[inline] def uartDLABBitPure (lcr : BitVec 8) : Bool :=
  lcr.extractLsb' 7 1 == 1#1

/-! ## Pure write-commit predicates

  Each UART register's write fires when:
    1. uartWE (peripheralWE for UART target)
    2. The offset matches
    3. (For DLL/DLM/IER) the DLAB bit selects the alt register
-/

/-- LCR write: offset 3 (no DLAB gating). -/
@[inline] def uartWriteLCRPure (uartWE : Bool) (offset : BitVec 3) : Bool :=
  uartWE && uartOffPure offset 3#3

/-- IER write: offset 1, DLAB=0. -/
@[inline] def uartWriteIERPure
    (uartWE : Bool) (offset : BitVec 3) (uartDLAB : Bool) : Bool :=
  uartWE && uartOffPure offset 1#3 && !uartDLAB

/-- MCR write: offset 4. -/
@[inline] def uartWriteMCRPure (uartWE : Bool) (offset : BitVec 3) : Bool :=
  uartWE && uartOffPure offset 4#3

/-- SCR write: offset 7. -/
@[inline] def uartWriteSCRPure (uartWE : Bool) (offset : BitVec 3) : Bool :=
  uartWE && uartOffPure offset 7#3

/-- DLL write: offset 0, DLAB=1. -/
@[inline] def uartWriteDLLPure
    (uartWE : Bool) (offset : BitVec 3) (uartDLAB : Bool) : Bool :=
  uartWE && uartOffPure offset 0#3 && uartDLAB

/-- DLM write: offset 1, DLAB=1. -/
@[inline] def uartWriteDLMPure
    (uartWE : Bool) (offset : BitVec 3) (uartDLAB : Bool) : Bool :=
  uartWE && uartOffPure offset 1#3 && uartDLAB

/-! ## Spec invariants — closed by `decide` / `bv_decide` -/

/-- Offset 0..7 are pairwise distinct: at most one offN matches. -/
theorem offsetMatch_unique
    (offset : BitVec 3) (n m : BitVec 3) (h : n ≠ m) :
    !(uartOffPure offset n && uartOffPure offset m) = true := by
  unfold uartOffPure
  cases h1 : offset == n
  · simp [h1]
  · cases h2 : offset == m
    · simp [h2]
    · -- both true → offset = n ∧ offset = m → n = m, contradiction
      exfalso
      have e1 : offset = n := by
        revert h1; cases h1' : offset == n
        · intro hh; cases hh
        · intro _; bv_decide
      have e2 : offset = m := by
        revert h2; cases h2' : offset == m
        · intro hh; cases hh
        · intro _; bv_decide
      exact h (e1.symm.trans e2)

/-- IER and DLM both target offset 1 — they are DLAB-disjoint. -/
theorem ier_dlm_dlab_mutex
    (uartWE : Bool) (offset : BitVec 3) (uartDLAB : Bool) :
    !(uartWriteIERPure uartWE offset uartDLAB
       && uartWriteDLMPure uartWE offset uartDLAB) = true := by
  unfold uartWriteIERPure uartWriteDLMPure
  cases uartDLAB <;> simp

/-- LCR write fires iff WE + offset 3. -/
theorem lcrWrite_fires (uartWE : Bool) :
    uartWriteLCRPure uartWE 3#3 = uartWE := by
  unfold uartWriteLCRPure uartOffPure
  cases uartWE <;> rfl

/-- DLL needs DLAB=1. -/
theorem dllWrite_needs_dlab (uartWE : Bool) :
    uartWriteDLLPure uartWE 0#3 false = false := by
  unfold uartWriteDLLPure uartOffPure
  cases uartWE <;> rfl

/-- IER needs DLAB=0. -/
theorem ierWrite_needs_no_dlab (uartWE : Bool) :
    uartWriteIERPure uartWE 1#3 true = false := by
  unfold uartWriteIERPure uartOffPure
  cases uartWE <;> rfl

/-! ## Composite specs -/

theorem uartWriteLCRPure_spec (uartWE : Bool) (offset : BitVec 3) :
    uartWriteLCRPure uartWE offset =
      (uartWE && (offset == 3#3)) := by rfl

theorem uartWriteIERPure_spec
    (uartWE : Bool) (offset : BitVec 3) (uartDLAB : Bool) :
    uartWriteIERPure uartWE offset uartDLAB =
      (uartWE && (offset == 1#3) && !uartDLAB) := by rfl

/-! ## Signal-level wrappers -/

def uartOffSignal {dom : DomainConfig}
    (offset : Signal dom (BitVec 3)) (n : BitVec 3) : Signal dom Bool :=
  offset === n

def uartDLABBitSignal {dom : DomainConfig}
    (lcr : Signal dom (BitVec 8)) : Signal dom Bool :=
  (lcr.map (BitVec.extractLsb' 7 1 ·)) === 1#1

def uartWriteLCRSignal {dom : DomainConfig}
    (uartWE : Signal dom Bool) (offset : Signal dom (BitVec 3))
    : Signal dom Bool :=
  uartWE &&& uartOffSignal offset 3#3

def uartWriteIERSignal {dom : DomainConfig}
    (uartWE : Signal dom Bool) (offset : Signal dom (BitVec 3))
    (uartDLAB : Signal dom Bool) : Signal dom Bool :=
  uartWE &&& (uartOffSignal offset 1#3 &&& (~~~uartDLAB))

def uartWriteMCRSignal {dom : DomainConfig}
    (uartWE : Signal dom Bool) (offset : Signal dom (BitVec 3))
    : Signal dom Bool :=
  uartWE &&& uartOffSignal offset 4#3

def uartWriteSCRSignal {dom : DomainConfig}
    (uartWE : Signal dom Bool) (offset : Signal dom (BitVec 3))
    : Signal dom Bool :=
  uartWE &&& uartOffSignal offset 7#3

def uartWriteDLLSignal {dom : DomainConfig}
    (uartWE : Signal dom Bool) (offset : Signal dom (BitVec 3))
    (uartDLAB : Signal dom Bool) : Signal dom Bool :=
  uartWE &&& (uartOffSignal offset 0#3 &&& uartDLAB)

def uartWriteDLMSignal {dom : DomainConfig}
    (uartWE : Signal dom Bool) (offset : Signal dom (BitVec 3))
    (uartDLAB : Signal dom Bool) : Signal dom Bool :=
  uartWE &&& (uartOffSignal offset 1#3 &&& uartDLAB)

end Sparkle.IP.RV32.UART
