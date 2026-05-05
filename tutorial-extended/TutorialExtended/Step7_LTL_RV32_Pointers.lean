/-
  Tutorial Step 7: LTL in production — pointer to the RV32 SoC proofs.

  Steps 5-6 introduced LTL with toy examples. This file is a
  *guided tour* of where the same patterns appear at production
  scale in the RV32 SoC verification stack. We don't redefine
  anything; we import a few key theorems and demonstrate that
  they are accessible from user code.

  Reference: `docs/Tutorial_LTL.md` for the full walkthrough,
  and `docs/RV32_Architecture_Status.md` §2.2 for the broader
  invariant catalog.
-/

import Sparkle
-- The 4-premise BitNet sw→lw timing framework:
import IP.RV32.Verification.BitNetTimingLTL
-- The N-step register preservation scaffold:
import IP.RV32.Verification.InductionScaffold
-- The Linux-boot regression-pinning theorems:
import IP.RV32.Verification.LinuxBootRegression
-- A few representative cycle-N+1 LTL theorems from the SoC body:
import IP.RV32.Pipeline.SideEffectsTrapInv
-- The bf6d873 megapage PA-formation regression theorems:
import IP.RV32.MMU.PA

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace TutorialExtended.Step7

/-! ## Pattern 1: cycle-N+1 LTL form

  The simplest temporal property — "if X at cycle t, then Y at
  cycle t+1." Sparkle's RV32 SoC has 100+ such lemmas, all
  proved by `unfold + cases + rfl` from the `Signal.register` /
  `Signal.mux` semantics.

  Example: `trap_clears_exwb_regW_LTL` says that whenever a
  trap fires at cycle t, the EXWB-stage `regW` flag is forced
  to false at cycle t+1. -/

#check @Sparkle.IP.RV32.Pipeline.trap_clears_exwb_regW_LTL
-- Type signature (paraphrased):
-- ∀ {dom : DomainConfig} (trap_taken dTLBMiss pendingWriteEn mmuBusy
--   dMMURedirect idex_regWrite : Signal dom Bool),
--   ∀ t, trap_taken.atTime t = true →
--        (Signal.register false
--          (Signal.mux suppressEXWBSignal ...) idex_regWrite).val (t + 1) = false

/-! ## Pattern 2: N-step register preservation (induction scaffold)

  When you need "no event for K cycles → register unchanged for
  K cycles," the N-step preservation theorem from
  `IP/RV32/Verification/InductionScaffold.lean` lifts a per-cycle
  recurrence to a K-step trace invariant. Proof: induction on K. -/

#check @Sparkle.IP.RV32.Verification.nstep_preserve_when_no_event
-- Type:
-- ∀ {α : Type} (r : Nat → α) (we : Nat → Bool) (update : Nat → α),
--   (∀ s, r (s + 1) = if we s then update s else r s) →  -- recurrence
--   ∀ t k, (∀ i, i < k → we (t + i) = false) →            -- no event in window
--          r (t + k) = r t                                 -- preserved

/-! ## Pattern 3: 4-premise sw→lw bug-localization framework

  This is the actual `BitNetTimingLTL.lean` framework. P1 (cycle-N+1
  update), P2 (K-cycle preservation), P3 (combinational FFN), P4
  (lw decode). The composite theorem derives correctness; the
  contrapositive localizes runtime bugs to a specific layer. -/

#check @Sparkle.IP.RV32.Verification.sw_then_lw_observes_ffn_input
-- Composite (paraphrased):
-- ∀ premises P1..P4, ∀ T_sw K X,
--   sw at T_sw with input X ∧ no events in [T_sw+1, T_sw+1+K) ∧
--   lw at T_sw+1+K → mmioRdata observes ffn(X)

#check @Sparkle.IP.RV32.Verification.bug_localization_via_LTL
-- Contrapositive (paraphrased):
-- observed Y ≠ ffn(X) ⇒ ¬(P1 ∧ P2 ∧ P3 ∧ P4)

/-! ## Pattern 4: regression-pinning concrete vectors

  These are not LTL — just concrete-vector machine-checks that
  serve as regression alarms. They use `decide` / `bv_decide` to
  verify that specific PA-formation, PTE-decoding, or bus-routing
  cases produce the correct value.

  Example: the kernel's first instruction fetch (vaddr 0xc0000098,
  trampoline_pg_dir megapage) translates to PA 0x80400098. If a
  future Verilog-gen refactor breaks the megapage formula, this
  theorem fails to typecheck. -/

#check @Sparkle.IP.RV32.MMU.dPhysAddrMega_kernel_first_fetch_concrete
-- dPhysAddrPure true 0x080400#22 0xc0000098#32 = 0x80400098#32

/-! ## How these compose

  The verification stack layers from "concrete vectors" upward:

    decide-closed concrete vectors (LinuxBootRegression / MMU/PA)
        ↓
    cycle-N+1 LTL forms (per-register, ~100 theorems)
        ↓
    N-step preservation scaffold (InductionScaffold)
        ↓
    composite contracts (BitNetTimingLTL: 4-premise sw→lw)
        ↓
    contrapositive bug localization (each Pi → SoC layer)

  Each layer takes the theorems below it as discharged premises.
  The user only ever has to write the TOP layer (the property
  they want about the system); everything below is reusable. -/

/-! ## Demo: print which RV32 LTL theorems are accessible. -/

def runDemo : IO Unit := do
  IO.println "Step 7 — RV32 LTL theorem catalog (compile-time accessible)"
  IO.println "  cycle-N+1 LTL form (one of ~100):"
  IO.println "    trap_clears_exwb_regW_LTL"
  IO.println "  N-step preservation:"
  IO.println "    nstep_preserve_when_no_event"
  IO.println "  4-premise composite:"
  IO.println "    sw_then_lw_observes_ffn_input"
  IO.println "  Contrapositive bug localization:"
  IO.println "    bug_localization_via_LTL"
  IO.println "  Regression-pinning concrete vectors:"
  IO.println "    dPhysAddrMega_kernel_first_fetch_concrete"
  IO.println ""
  IO.println "See docs/Tutorial_LTL.md for the walkthrough,"
  IO.println "and docs/BitNet_LTL_Investigation.md for the worked example."

end TutorialExtended.Step7
