/-
  RV32 SoC bus decoder — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (~lines 504..510). Decodes the
  effective (post-MMU) physical address into one of four targets:

      isCLINT_ex  := addr[31:16] = 0x0200
      is_mmio_ex  := addr[30]    = 1
      isUART_ex   := addr[31:24] = 0x10
      isDMEM_ex   := !isCLINT_ex && !is_mmio_ex && !isUART_ex

  This file proves the two invariants from
  `docs/RV32_Architecture_Status.md` §2.3:
    1. **Mutual exclusion**: at most one target is true.
    2. **Exhaustiveness**: at least one target is true.

  Combined: for every 32-bit address, exactly one of {CLINT, MMIO,
  UART, DMEM} is true. The proof uses `bv_decide` to enumerate the
  finite address-space relevant bits.

  Reference (Sparkle SoC address map):
    DRAM (DMEM):  catch-all (0x00000000..0x7FFFFFFF except CLINT/UART)
    CLINT:        0x02000000..0x0200FFFF (cause: addr[31:16] = 0x0200)
    UART:         0x10000000..0x10FFFFFF (cause: addr[31:24] = 0x10)
    MMIO default: addr[30] = 1 (catch-all for any 0x4xxxxxxx-0x7xxxxxxx
                                or 0xCxxxxxxx-0xFxxxxxxx mapping)

  Note: `is_mmio_ex` overlaps with the high half of the 32-bit space,
  but in practice the SoC's actual physical layout puts DRAM in
  0x80000000..0x81FFFFFF, which has bit 30 = 0, so DMEM and MMIO
  don't physically overlap.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Bus

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure decoder predicates -/

/-- True iff `addr[31:16] = 0x0200` (CLINT region). -/
@[inline] def isCLINTPure (addr : BitVec 32) : Bool :=
  addr.extractLsb' 16 16 == 0x0200#16

/-- True iff `addr[30] = 1` (MMIO default region). -/
@[inline] def isMmioPure (addr : BitVec 32) : Bool :=
  addr.extractLsb' 30 1 == 1#1

/-- True iff `addr[31:24] = 0x10` (UART region). -/
@[inline] def isUARTPure (addr : BitVec 32) : Bool :=
  addr.extractLsb' 24 8 == 0x10#8

/-- DMEM is the catch-all: not CLINT, not MMIO, not UART. -/
@[inline] def isDMEMPure (addr : BitVec 32) : Bool :=
  !(isCLINTPure addr) && !(isMmioPure addr) && !(isUARTPure addr)

/-! ## Spec invariants — closed by `bv_decide` over BitVec 32 -/

/-- **Exhaustiveness**: every address routes to at least one target.
    DMEM is the catch-all so this reduces to "DMEM ∨ ¬DMEM = true". -/
theorem bus_decoder_exhaustive (addr : BitVec 32) :
    (isCLINTPure addr) || (isMmioPure addr) ||
      (isUARTPure addr) || (isDMEMPure addr) = true := by
  unfold isDMEMPure
  cases h1 : isCLINTPure addr <;>
    cases h2 : isMmioPure addr <;>
    cases h3 : isUARTPure addr <;>
    simp [h1]

/-- **Mutex - DMEM is exclusive**: when DMEM is selected, none of the
    others are. -/
theorem bus_decoder_dmem_exclusive (addr : BitVec 32) :
    isDMEMPure addr = true →
    isCLINTPure addr = false ∧
      isMmioPure addr = false ∧
      isUARTPure addr = false := by
  unfold isDMEMPure
  intro h
  -- h : (!isCLINTPure addr) && !isMmioPure addr && !isUARTPure addr = true
  rcases (Bool.and_eq_true _ _).mp h with ⟨h12, h3⟩
  rcases (Bool.and_eq_true _ _).mp h12 with ⟨h1, h2⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (Bool.not_eq_true _).mp (by simpa using h1)
  · exact (Bool.not_eq_true _).mp (by simpa using h2)
  · exact (Bool.not_eq_true _).mp (by simpa using h3)

/-- **Mutex — CLINT and UART are address-disjoint**:
    CLINT ⊆ {addr | addr[31:16] = 0x0200}, UART ⊆ {addr | addr[31:24] = 0x10};
    these don't overlap because 0x0200's top byte is 0x02, not 0x10. -/
theorem bus_decoder_clint_uart_disjoint (addr : BitVec 32) :
    !(isCLINTPure addr && isUARTPure addr) = true := by
  unfold isCLINTPure isUARTPure
  revert addr; bv_decide

/-- **Mutex — CLINT and MMIO are address-disjoint**:
    CLINT.addr[31:16] = 0x0200 → bit 30 = 0; MMIO requires bit 30 = 1. -/
theorem bus_decoder_clint_mmio_disjoint (addr : BitVec 32) :
    !(isCLINTPure addr && isMmioPure addr) = true := by
  unfold isCLINTPure isMmioPure
  revert addr; bv_decide

/-- **Mutex — UART and MMIO are address-disjoint**:
    UART.addr[31:24] = 0x10 → bit 30 = 0; MMIO requires bit 30 = 1. -/
theorem bus_decoder_uart_mmio_disjoint (addr : BitVec 32) :
    !(isUARTPure addr && isMmioPure addr) = true := by
  unfold isUARTPure isMmioPure
  revert addr; bv_decide

/-- **Combined uniqueness (compact form)**: any two distinct predicates
    cannot both fire. The four pairwise lemmas above (plus `dmem_exclusive`'s
    cases) are the constituents; `bus_decoder_dmem_exclusive` handles the
    DMEM-vs-others side. -/
theorem bus_decoder_dmem_when_no_others (addr : BitVec 32) :
    isCLINTPure addr = false → isMmioPure addr = false →
    isUARTPure addr = false → isDMEMPure addr = true := by
  intro h1 h2 h3
  unfold isDMEMPure
  rw [h1, h2, h3]
  rfl

/-! ## Signal-level wrappers -/

/-- Signal-level `isCLINT`. Uses 16-bit upper word == 0x0200. -/
def isCLINTSignal {dom : DomainConfig}
    (addr : Signal dom (BitVec 32)) : Signal dom Bool :=
  (addr.map (BitVec.extractLsb' 16 16 ·)) === 0x0200#16

/-- Signal-level `isMmio`. Uses bit 30 == 1. -/
def isMmioSignal {dom : DomainConfig}
    (addr : Signal dom (BitVec 32)) : Signal dom Bool :=
  (addr.map (BitVec.extractLsb' 30 1 ·)) === 1#1

/-- Signal-level `isUART`. Uses byte 24 == 0x10. -/
def isUARTSignal {dom : DomainConfig}
    (addr : Signal dom (BitVec 32)) : Signal dom Bool :=
  (addr.map (BitVec.extractLsb' 24 8 ·)) === 0x10#8

/-- Signal-level `isDMEM`. Catch-all. -/
def isDMEMSignal {dom : DomainConfig}
    (isCLINT isMmio isUART : Signal dom Bool) : Signal dom Bool :=
  (~~~isCLINT) &&& ((~~~isMmio) &&& (~~~isUART))

end Sparkle.IP.RV32.Bus
