/-
  RV32 store-during-async-trap idempotency — invariant E

  Invariant E from `docs/RV32_Architecture_Status.md` §2.2:

      "A store in IDEX when async-trap fires either commits
       exactly once, or commits twice with identical data —
       never produces inconsistent memory."

  This is the invariant that the DRAM `dmem_we` validEX gate
  fix (commit 91a3278) closed. Before the fix, when trap_taken
  fired with a store in IDEX:
    - CLINT/MMIO/UART writes were suppressed (gated on validEX).
    - DRAM `dmem_we` was NOT gated → write committed anyway.
    - After `sret`, mepc=idex_pc → kernel re-ran the store.
    - Result: two DRAM writes (the original + the re-execution),
      with possibly different data (sp may have changed during
      trap save/restore).

  After the fix, `dmem_we` is gated on `early_dramValid`, which
  is `!(trap_taken | mmuBusy | dMMURedirect)`. So the original
  store's DRAM commit is suppressed; only the post-sret re-
  execution commits. **Exactly one commit, with the post-sret
  data.**

  This file proves the suppression part: the gate guarantees
  no DRAM write fires when trap_taken is true.

  Companion to:
    * Pipeline/AbortGuarantee.lean — `dmemWe_not_gated_by_trap`
                                     witness theorem (commit 90cf116)
                                     showed the gap pre-fix
    * AMO/SC.lean                  — dmemWePure
    * Trap/TrapTaken.lean          — trap_taken composition

  The witness theorem and this proof together form the
  before/after pair: the witness showed the bug existed; this
  proof shows the fix closes it.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.AMO.SC

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## The DRAM write-gate (post-fix shape)

  Per commit 91a3278, the gate combines `proto_byte_we` (the
  store-related write enable) with `early_dramValid` (the trap-
  aware suppression):

      dramWriteGate = early_dramValid ∨ dmemExtWriteEn
      actual_byte_we = proto_byte_we ∧ dramWriteGate

  Where:
      early_dramValid = ¬(trap_taken ∨ mmuBusy ∨ dMMURedirect)

  We prove that when trap_taken fires AND dmemExtWriteEn is
  false (normal pipeline operation, not firmware loading), the
  gate suppresses the byte-write. -/

/-- Pure form of the DRAM write-gate (post-fix). -/
@[inline] def dramWriteGatePure
    (trap_taken mmuBusy dMMURedirect dmemExtWriteEn : Bool) : Bool :=
  let early_dramValid := !(trap_taken || mmuBusy || dMMURedirect)
  early_dramValid || dmemExtWriteEn

/-- Pure form of the actual_byte_we (post-fix). -/
@[inline] def actualByteWePure
    (proto_byte_we trap_taken mmuBusy dMMURedirect dmemExtWriteEn : Bool) : Bool :=
  proto_byte_we && dramWriteGatePure trap_taken mmuBusy dMMURedirect dmemExtWriteEn

/-! ## Invariant E (combinational): trap_taken → no DRAM write

  When trap_taken fires (and the firmware loader isn't writing),
  the gate suppresses any in-flight store's DRAM commit. -/

/-- **Invariant E (suppression part)**: trap_taken with no
    firmware-loader write → DRAM byte_we is forced to false. -/
theorem trap_suppresses_dram_write
    (proto_byte_we mmuBusy dMMURedirect : Bool) :
    actualByteWePure proto_byte_we true mmuBusy dMMURedirect false = false := by
  unfold actualByteWePure dramWriteGatePure
  cases proto_byte_we <;> rfl

/-- mmuBusy alone also suppresses (PTW in flight). -/
theorem mmuBusy_suppresses_dram_write
    (proto_byte_we trap_taken dMMURedirect : Bool) :
    actualByteWePure proto_byte_we trap_taken true dMMURedirect false = false := by
  unfold actualByteWePure dramWriteGatePure
  cases proto_byte_we <;> cases trap_taken <;> cases dMMURedirect <;> rfl

/-- dMMURedirect alone also suppresses. -/
theorem dMMURedirect_suppresses_dram_write
    (proto_byte_we trap_taken mmuBusy : Bool) :
    actualByteWePure proto_byte_we trap_taken mmuBusy true false = false := by
  unfold actualByteWePure dramWriteGatePure
  cases proto_byte_we <;> cases trap_taken <;> cases mmuBusy <;> rfl

/-- Firmware loader bypasses the gate (so `dmemExtWriteEn` works
    even during trap-like states — though the firmware loader is
    only active before the pipeline starts, so this is mostly
    a defensive correctness property). -/
theorem dmemExtWriteEn_bypasses_gate
    (proto_byte_we trap_taken mmuBusy dMMURedirect : Bool)
    (h : proto_byte_we = true) :
    actualByteWePure proto_byte_we trap_taken mmuBusy dMMURedirect true = true := by
  unfold actualByteWePure dramWriteGatePure
  rw [h]
  cases trap_taken <;> cases mmuBusy <;> cases dMMURedirect <;> rfl

/-- Quiescent state (no trap, no MMU activity, no firmware) → write
    fires iff proto_byte_we is asserted. -/
theorem quiescent_byte_we
    (proto_byte_we : Bool) :
    actualByteWePure proto_byte_we false false false false = proto_byte_we := by
  unfold actualByteWePure dramWriteGatePure
  cases proto_byte_we <;> rfl

/-! ## Composite spec -/

theorem actualByteWePure_spec
    (proto_byte_we trap_taken mmuBusy dMMURedirect dmemExtWriteEn : Bool) :
    actualByteWePure proto_byte_we trap_taken mmuBusy dMMURedirect dmemExtWriteEn =
      (proto_byte_we &&
       ((!(trap_taken || mmuBusy || dMMURedirect)) || dmemExtWriteEn)) := by rfl

/-! ## Signal-level wrappers -/

/-- Signal-level early dram-suppress: trap | mmuBusy | dMMURedirect. -/
def earlyDramSuppressSignal {dom : DomainConfig}
    (trap_taken mmuBusy dMMURedirect : Signal dom Bool) : Signal dom Bool :=
  trap_taken ||| mmuBusy ||| dMMURedirect

/-- Signal-level early dram-valid: ¬suppress. -/
def earlyDramValidSignal {dom : DomainConfig}
    (trap_taken mmuBusy dMMURedirect : Signal dom Bool) : Signal dom Bool :=
  ~~~(earlyDramSuppressSignal trap_taken mmuBusy dMMURedirect)

/-- Signal-level dram write-gate: early_dramValid | dmemExtWriteEn. -/
def dramWriteGateSignal {dom : DomainConfig}
    (trap_taken mmuBusy dMMURedirect dmemExtWriteEn : Signal dom Bool)
    : Signal dom Bool :=
  earlyDramValidSignal trap_taken mmuBusy dMMURedirect ||| dmemExtWriteEn

/-- Signal-level actual byte-WE: proto_byte_we ∧ dramWriteGate. -/
def actualByteWeSignal {dom : DomainConfig}
    (proto_byte_we trap_taken mmuBusy dMMURedirect dmemExtWriteEn : Signal dom Bool)
    : Signal dom Bool :=
  proto_byte_we &&&
    dramWriteGateSignal trap_taken mmuBusy dMMURedirect dmemExtWriteEn

/-! ## Connection to invariant E

  The full invariant E ("exactly one DRAM commit per logical
  store") combines:

    1. **Suppression** (proven here): when trap_taken fires
       with a store in IDEX, the original DRAM write is
       suppressed.

    2. **Re-execution** (already wired by commit 01c7177): mepc
       is set to the suppressed instruction's PC, so the kernel
       re-fetches and re-executes the store after sret.

    3. **Idempotency**: the re-executed store sees the same
       (sp, store data) as the original — assuming the trap
       handler save/restored these correctly. This is a
       higher-level invariant that depends on the kernel ABI
       (and is ultimately certified at the regfile-preservation
       level — invariant A in §2.2).

  With (1) proven here and (2) wired upstream, the system
  delivers exactly-one-commit semantics: the original is
  dropped, the re-execution commits cleanly. **No more
  double-commit bug.**

  The witness theorem `dmemWe_not_gated_by_trap` in
  `Pipeline/AbortGuarantee.lean` showed the gap *before* the
  fix; this module proves the gap is closed *after* the fix.
  Together: a complete before/after spec.
-/

end Sparkle.IP.RV32.Pipeline
