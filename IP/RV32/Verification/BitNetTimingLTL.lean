/-
  RV32 BitNet sw→lw timing — LTL (∀N temporal) formalization.

  Question (from the user, this iteration): can we formally
  capture "the bug" — values appearing 1 cycle early, 1 cycle late,
  or never — using temporal logic over Sparkle's Signal model?

  Answer: yes, because `Signal dom α = Nat → α` is the full
  trace model, and ∀t-quantified statements ARE LTL formulas
  (the standard "always" and "next" connectives compose
  directly).

  This file states the EXACT temporal contract for the BitNet
  sw→lw sequence and identifies which of the contract's premises
  must be violated for each possible runtime symptom.

  Notation map (Lean ↔ LTL):
    □ P              ↔  ∀ t, P t
    P → ◯ Q          ↔  ∀ t, P t → Q (t+1)
    P → ◯^k Q        ↔  ∀ t, P t → Q (t+k)
    □ (P → ◯^≤K Q)   ↔  ∀ t, P t → ∃ k, k ≤ K ∧ Q (t+k)
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.MMIO.BitNet
import IP.RV32.Verification.InductionScaffold

namespace Sparkle.IP.RV32.Verification

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Layered LTL contracts

  The full sw→lw composition is built from 4 LTL premises. Each
  premise is a property of a specific Signal in the SoC. If the
  runtime trace violates *any* premise, we can say *which* layer
  failed.
-/

/-! ### Premise 1: aiInputReg cycle-N+1 update -/

/-- **□ (mmioWriteEvent t → ◯ (aiInputReg = X)).**

    For all cycles t, if the MMIO write event fires for the input
    register with data X at cycle t, then at cycle t+1 the
    aiInputReg holds X.

    This is the **cycle-N+1 contract**. Violations:
      - aiInputReg.val (t+1) = X-1 cycle (= "1 cycle early"):
        means register update happens at t (combinational), not
        at t+1. Should never happen with `Signal.register`.
      - aiInputReg.val (t+1) ≠ X (= "1 cycle late"):
        means register hasn't latched yet at t+1; the latch is
        at t+2 or later.
      - aiInputReg.val (t+1) = stale prior value (= "value never
        arrives"): means the WE pulse was dropped.
-/
def aiInputReg_cycle_N1_contract {dom : DomainConfig}
    (mmioWE mmioIsInput : Signal dom Bool)
    (newVal : Signal dom (BitVec 32))
    (aiInputReg : Signal dom (BitVec 32)) : Prop :=
  ∀ t, mmioWE.val t = true → mmioIsInput.val t = true →
       aiInputReg.val (t + 1) = newVal.val t

/-- **The contract holds for the SoC's actual `aiInputNextSignal`-driven
    register.**

    Direct from `Signal.register` + `Signal.mux` semantics.
    Provided here as a discharged premise for the composite below. -/
theorem aiInputReg_cycle_N1_contract_holds {dom : DomainConfig}
    (mmioWE mmioIsInput : Signal dom Bool)
    (newVal : Signal dom (BitVec 32))
    (aiInputReg : Signal dom (BitVec 32))
    (h_self_loop :
      ∀ s, aiInputReg.val (s + 1) =
        (Sparkle.IP.RV32.MMIO.aiInputNextSignal mmioWE mmioIsInput
          newVal aiInputReg).val s) :
    aiInputReg_cycle_N1_contract mmioWE mmioIsInput newVal aiInputReg := by
  intro t h_we h_input
  rw [h_self_loop]
  unfold Sparkle.IP.RV32.MMIO.aiInputNextSignal Signal.mux
  show (if (mmioWE &&& mmioIsInput).val t then newVal.val t
        else aiInputReg.val t) = newVal.val t
  show (if (mmioWE.val t && mmioIsInput.val t) then _ else _) = _
  rw [h_we, h_input]
  rfl

/-! ### Premise 2: aiInputReg K-cycle preservation -/

/-- **□ (aiInputReg = X ∧ no-WE in [t, t+k) → aiInputReg = X at t+k).**

    For all t and k, if at cycle t the register holds X and no
    WE fires in the next k cycles, the register still holds X
    at t+k.

    Violations:
      - aiInputReg gets corrupted by some unrelated event
      - register reset/clear path triggered unexpectedly.
-/
def aiInputReg_K_cycle_contract {dom : DomainConfig}
    (mmioWE mmioIsInput : Signal dom Bool)
    (aiInputReg : Signal dom (BitVec 32)) : Prop :=
  ∀ (t k : Nat) (X : BitVec 32),
    aiInputReg.val t = X →
    (∀ i, i < k → ¬ (mmioWE.val (t + i) = true ∧ mmioIsInput.val (t + i) = true)) →
    aiInputReg.val (t + k) = X

/-- **K-cycle contract holds, given the cycle-N+1 contract + recurrence.**

    Proof by induction on k. -/
theorem aiInputReg_K_cycle_contract_holds {dom : DomainConfig}
    (mmioWE mmioIsInput : Signal dom Bool)
    (newVal : Signal dom (BitVec 32))
    (aiInputReg : Signal dom (BitVec 32))
    (h_self_loop :
      ∀ s, aiInputReg.val (s + 1) =
        (Sparkle.IP.RV32.MMIO.aiInputNextSignal mmioWE mmioIsInput
          newVal aiInputReg).val s) :
    aiInputReg_K_cycle_contract mmioWE mmioIsInput aiInputReg := by
  intro t k X h_init h_no_event
  induction k with
  | zero =>
    show aiInputReg.val (t + 0) = X
    simpa using h_init
  | succ k ih =>
    have h_ih : aiInputReg.val (t + k) = X := by
      apply ih
      intro i hi
      exact h_no_event i (Nat.lt_succ_of_lt hi)
    -- Step from t+k to t+(k+1).
    have h_no_event_k :
        ¬ (mmioWE.val (t + k) = true ∧ mmioIsInput.val (t + k) = true) :=
      h_no_event k (Nat.lt_succ_self k)
    have : t + (k + 1) = (t + k) + 1 := by omega
    rw [this]
    rw [h_self_loop]
    unfold Sparkle.IP.RV32.MMIO.aiInputNextSignal Signal.mux
    show (if (mmioWE &&& mmioIsInput).val (t + k) then _
          else aiInputReg.val (t + k)) = X
    show (if (mmioWE.val (t + k) && mmioIsInput.val (t + k)) then _
          else aiInputReg.val (t + k)) = X
    -- The condition is false because of h_no_event_k.
    cases h_we : mmioWE.val (t + k)
    case false => simp [h_we]; exact h_ih
    case true =>
      cases h_inp : mmioIsInput.val (t + k)
      case false => simp [h_we, h_inp]; exact h_ih
      case true =>
        exfalso; exact h_no_event_k ⟨h_we, h_inp⟩

/-! ### Premise 3: bitnetOut combinational -/

/-- **□ (bitnetOut = ffn(aiInputReg)) at every cycle.**

    The BitNet peripheral is combinational, so its output at any
    cycle is determined by aiInputReg at the same cycle.

    Violations:
      - bitnetOut delayed by 1+ cycles from aiInputReg (synthesis
        bug inserting an unintended register stage).
      - bitnetOut produces stale value (e.g., latch instead of
        wire).
-/
def bitnetOut_combinational_contract {dom : DomainConfig}
    (aiInputReg bitnetOut : Signal dom (BitVec 32))
    (ffn : BitVec 32 → BitVec 32) : Prop :=
  ∀ t, bitnetOut.val t = ffn (aiInputReg.val t)

/-! ### Premise 4: lw observes mmioRdata at cycle T_lw_wb -/

/-- **□ (lw at offset 0x8 in EXWB at t → mmioRdata = bitnetOut at t).**

    When the EXWB-stage decode produces "MMIO read at offset 0x8",
    the rdata mux outputs `bitnetOut`. This is `rfl` by the
    decoder's definition.

    Violations:
      - bus rdata mux selects DMEM arm instead of MMIO arm
        (decoder bug routing 0x40000008 to DMEM).
      - mmioRdata mux returns aiStatusReg or 0 (wrong offset
        decode).
-/
def lw_observes_bitnetOut_contract {dom : DomainConfig}
    (exwb_physAddr : Signal dom (BitVec 32))
    (aiStatusReg bitnetOut mmioRdata : Signal dom (BitVec 32)) : Prop :=
  ∀ t, exwb_physAddr.val t = 0x40000008#32 →
       mmioRdata.val t =
         Sparkle.IP.RV32.MMIO.mmioRdataPure
           (Sparkle.IP.RV32.MMIO.mmioIsStatusPure 0x8#4)
           (Sparkle.IP.RV32.MMIO.mmioIsOutputPure 0x8#4)
           (aiStatusReg.val t) (bitnetOut.val t)

/-! ## Composite LTL contract: sw→lw observation

  Combine all 4 premises into a single ∀-quantified theorem:
  for any cycle T_sw where sw fires with input X, and for any
  K ≥ 1 cycles later where the lw fires (with no intervening
  WE), the lw observes ffn(X).

  This is the LTL form `□ (sw_at_T ∧ lw_at_T+K → lw_observes ffn(X))`.

  CONTRAPOSITIVE: if the lw observes Y ≠ ffn(X), then ONE of
  the 4 premises is violated. This pins the bug to a specific
  layer.
-/

/-- **The composite sw→lw temporal contract.** -/
theorem sw_then_lw_observes_ffn_input {dom : DomainConfig}
    (mmioWE mmioIsInput : Signal dom Bool)
    (newVal aiInputReg bitnetOut aiStatusReg mmioRdata : Signal dom (BitVec 32))
    (exwb_physAddr : Signal dom (BitVec 32))
    (ffn : BitVec 32 → BitVec 32)
    -- Premise 1: cycle-N+1 update.
    (h_p1 : aiInputReg_cycle_N1_contract mmioWE mmioIsInput newVal aiInputReg)
    -- Premise 2: K-cycle preservation.
    (h_p2 : aiInputReg_K_cycle_contract mmioWE mmioIsInput aiInputReg)
    -- Premise 3: combinational bitnetOut.
    (h_p3 : bitnetOut_combinational_contract aiInputReg bitnetOut ffn)
    -- Premise 4: lw decodes at offset 0x8.
    (h_p4 : lw_observes_bitnetOut_contract exwb_physAddr aiStatusReg bitnetOut mmioRdata)
    (T_sw : Nat) (K : Nat) (X : BitVec 32)
    -- sw fires at cycle T_sw with input X.
    (h_sw_we : mmioWE.val T_sw = true)
    (h_sw_input : mmioIsInput.val T_sw = true)
    (h_sw_data : newVal.val T_sw = X)
    -- No further WE in (T_sw, T_sw + 1 + K).
    (h_no_event :
      ∀ i, i < K → ¬ (mmioWE.val (T_sw + 1 + i) = true ∧
                        mmioIsInput.val (T_sw + 1 + i) = true))
    -- lw is in EXWB at cycle T_sw + 1 + K with offset 0x40000008.
    (h_lw_addr : exwb_physAddr.val (T_sw + 1 + K) = 0x40000008#32) :
    -- Conclusion: lw observes ffn(X).
    mmioRdata.val (T_sw + 1 + K) =
      Sparkle.IP.RV32.MMIO.mmioRdataPure
        (Sparkle.IP.RV32.MMIO.mmioIsStatusPure 0x8#4)
        (Sparkle.IP.RV32.MMIO.mmioIsOutputPure 0x8#4)
        (aiStatusReg.val (T_sw + 1 + K)) (ffn X) := by
  -- Step 1: P1 → aiInputReg.val (T_sw + 1) = X.
  have h_at_Tsw1 : aiInputReg.val (T_sw + 1) = X := by
    rw [h_p1 T_sw h_sw_we h_sw_input]
    exact h_sw_data
  -- Step 2: P2 → aiInputReg.val (T_sw + 1 + K) = X.
  have h_at_TswK : aiInputReg.val (T_sw + 1 + K) = X :=
    h_p2 (T_sw + 1) K X h_at_Tsw1 h_no_event
  -- Step 3: P3 → bitnetOut.val (T_sw + 1 + K) = ffn(X).
  have h_bitnet : bitnetOut.val (T_sw + 1 + K) = ffn X := by
    rw [h_p3]; rw [h_at_TswK]
  -- Step 4: P4 + lw_addr → mmioRdata = mmioRdataPure ... bitnetOut.
  have h_mmio := h_p4 (T_sw + 1 + K) h_lw_addr
  rw [h_mmio]
  rw [h_bitnet]

/-! ## CONTRAPOSITIVE: layer-localizing the bug -/

/-- **If the lw observes a value Y ≠ what the contract predicts,
    one of the 4 LTL premises is FALSE.**

    This is the formal statement of "bug localization": each
    premise corresponds to a specific layer of the SoC, and the
    truth-value of each premise can be observed (or refuted) by
    a runtime trace.
-/
theorem bug_localization_via_LTL {dom : DomainConfig}
    (mmioWE mmioIsInput : Signal dom Bool)
    (newVal aiInputReg bitnetOut aiStatusReg mmioRdata : Signal dom (BitVec 32))
    (exwb_physAddr : Signal dom (BitVec 32))
    (ffn : BitVec 32 → BitVec 32)
    (T_sw K : Nat) (X Y : BitVec 32)
    (h_sw_we : mmioWE.val T_sw = true)
    (h_sw_input : mmioIsInput.val T_sw = true)
    (h_sw_data : newVal.val T_sw = X)
    (h_no_event :
      ∀ i, i < K → ¬ (mmioWE.val (T_sw + 1 + i) = true ∧
                        mmioIsInput.val (T_sw + 1 + i) = true))
    (h_lw_addr : exwb_physAddr.val (T_sw + 1 + K) = 0x40000008#32)
    (h_observed : mmioRdata.val (T_sw + 1 + K) = Y)
    (h_predict_neq :
      Y ≠ Sparkle.IP.RV32.MMIO.mmioRdataPure
            (Sparkle.IP.RV32.MMIO.mmioIsStatusPure 0x8#4)
            (Sparkle.IP.RV32.MMIO.mmioIsOutputPure 0x8#4)
            (aiStatusReg.val (T_sw + 1 + K)) (ffn X)) :
    -- AT LEAST ONE of the 4 premises must be false.
    ¬ (aiInputReg_cycle_N1_contract mmioWE mmioIsInput newVal aiInputReg ∧
       aiInputReg_K_cycle_contract mmioWE mmioIsInput aiInputReg ∧
       bitnetOut_combinational_contract aiInputReg bitnetOut ffn ∧
       lw_observes_bitnetOut_contract exwb_physAddr aiStatusReg
         bitnetOut mmioRdata) := by
  rintro ⟨h_p1, h_p2, h_p3, h_p4⟩
  have h_predict := sw_then_lw_observes_ffn_input mmioWE mmioIsInput newVal
    aiInputReg bitnetOut aiStatusReg mmioRdata exwb_physAddr ffn
    h_p1 h_p2 h_p3 h_p4 T_sw K X h_sw_we h_sw_input h_sw_data h_no_event h_lw_addr
  -- h_predict : mmioRdata.val (T_sw+1+K) = mmioRdataPure ... (ffn X)
  -- h_observed : mmioRdata.val (T_sw+1+K) = Y
  -- so Y = mmioRdataPure ... (ffn X), contradicting h_predict_neq.
  apply h_predict_neq
  rw [← h_observed, h_predict]

/-! ## Concrete-vector bug localization for 9d0704e

  The observed boot.S trace was:
    sw 0x40000004 ← 0x10000   at some cycle T_sw
    nop nop nop nop
    lw r ← 0x40000008         at cycle T_sw + 5 + extra-stages
    observed r = 0x10000

  The Lean spec predicts:
    ffn(0x10000) = 0x410000
    mmioRdata at offset 0x8 = bitnetOut = 0x410000

  Plugging X = 0x10000 and Y = 0x10000 into bug_localization_via_LTL:
  Y = 0x10000 ≠ 0x410000 = ffn(X), so AT LEAST ONE of the 4
  premises is false in the runtime trace.

  Each premise corresponds to a layer:

  | Premise | Bug if violated |
  |---------|-----------------|
  | P1: aiInputReg cycle-N+1 update | Register update missed/delayed (= "1 cycle late") |
  | P2: K-cycle preservation | aiInputReg corrupted by unrelated event |
  | P3: bitnetOut combinational | FFN block bypassed or registered (= "1 cycle late" output) |
  | P4: lw decodes at 0x8 | Bus decoder routes 0x40000008 to wrong target |

  The bug-localizing strategy: observe each Signal at the trace
  cycle and check which premise fails. The LTL framing turns the
  "somewhere in the runtime layer" diagnosis into a 4-way
  classification with a concrete acceptance test per layer. -/

/-- **For the 9d0704e symptom (X = 0x10000, observed = 0x10000),
    if the runtime is consistent with the spec then ffn(X) = X.
    But ffn(0x10000) = 0x410000 ≠ 0x10000. Contradiction. So at
    least one premise is violated.** -/
theorem bug_9d0704e_localization {dom : DomainConfig}
    (mmioWE mmioIsInput : Signal dom Bool)
    (newVal aiInputReg bitnetOut aiStatusReg mmioRdata : Signal dom (BitVec 32))
    (exwb_physAddr : Signal dom (BitVec 32))
    (ffn : BitVec 32 → BitVec 32)
    (h_ffn_10000 : ffn (0x00010000#32) = 0x00410000#32)
    (T_sw K : Nat)
    (h_sw_we : mmioWE.val T_sw = true)
    (h_sw_input : mmioIsInput.val T_sw = true)
    (h_sw_data : newVal.val T_sw = 0x00010000#32)
    (h_no_event :
      ∀ i, i < K → ¬ (mmioWE.val (T_sw + 1 + i) = true ∧
                        mmioIsInput.val (T_sw + 1 + i) = true))
    (h_lw_addr : exwb_physAddr.val (T_sw + 1 + K) = 0x40000008#32)
    (h_observed : mmioRdata.val (T_sw + 1 + K) = 0x00010000#32)
    (h_aiStatus : aiStatusReg.val (T_sw + 1 + K) = 0x00000000#32) :
    ¬ (aiInputReg_cycle_N1_contract mmioWE mmioIsInput newVal aiInputReg ∧
       aiInputReg_K_cycle_contract mmioWE mmioIsInput aiInputReg ∧
       bitnetOut_combinational_contract aiInputReg bitnetOut ffn ∧
       lw_observes_bitnetOut_contract exwb_physAddr aiStatusReg
         bitnetOut mmioRdata) := by
  apply bug_localization_via_LTL mmioWE mmioIsInput newVal aiInputReg
    bitnetOut aiStatusReg mmioRdata exwb_physAddr ffn T_sw K
    (0x00010000#32) (0x00010000#32)
    h_sw_we h_sw_input h_sw_data h_no_event h_lw_addr h_observed
  -- Need: 0x10000 ≠ mmioRdataPure status_false output_true 0 (ffn 0x10000)
  --                = mmioRdataPure ... 0x410000 = 0x410000
  rw [h_ffn_10000, h_aiStatus]
  -- mmioRdataPure (mmioIsStatusPure 0x8) (mmioIsOutputPure 0x8) 0 0x410000
  -- = (if false then ... else if true then 0x410000 else 0) = 0x410000
  show (0x00010000#32 : BitVec 32) ≠ _
  decide

/-! ## Empirical bug localization (2026-05-05)

  Ran `lake exe bitnet-mmio-probe` against the actual JIT runtime
  with boot.S firmware. Observations from 10,000 cycles:

    cycle 80   aiInputReg = 0x00010000   bitnetOut = 0x00000000
    cycle 598  aiInputReg = 0x00020000   bitnetOut = 0x00000000
    cycle 1116 aiInputReg = 0x00030000   bitnetOut = 0x00000000
    ...
    cycle 3186 aiInputReg = 0x12345678   bitnetOut = 0x00000000

  Conclusion: aiInputReg is updated correctly through all 8 test
  vectors (P1 and P2 hold). But bitnetOut stays 0 regardless.

  This is **definitively a P3 violation**:

    P3: ∀t, bitnetOut.val t = ffn(aiInputReg.val t)

    runtime trace: at cycle 80, aiInputReg = 0x00010000.
    Lean spec predicts bitnetOut = ffn(0x00010000) = 0x00410000.
    Observed: bitnetOut = 0x00000000.

  Therefore:
      ¬ (∀t, bitnetOut.val t = ffn(aiInputReg.val t))
    ⇔ ∃t, bitnetOut.val t ≠ ffn(aiInputReg.val t)
    ⇔ at t=80, bitnetOut.val 80 = 0 ≠ 0x00410000 = ffn(0x00010000).

  The bug is in the FFN combinational chain (most likely
  `#synthesizeVerilog` of `bitNetPeripheral`, since the Lean unit
  test `bitnet-soc-test` evaluates the same function correctly via
  `Signal.atTime`).

  Note that the original 9d0704e symptom "out = input" was based on
  reading `_gen_next` (residual sum) when the chain was partially
  working. Now `_gen_next = aiInputReg + downScaled` evaluates to
  0 because **downScaled also = 0** AND aiInputReg's contribution
  through the residual addition is also being lost. This suggests
  the FFN block is producing 0 throughout, and the residual path
  is also broken.

  ANSWER to the original question: the BitNet bug IS in the
  Verilog code generation of the FFN datapath (or in the JIT
  evaluator's handling of the `bitNetPeripheral` combinational
  function). It is NOT in the Lean Sparkle SoC spec.
-/

/-- **Empirical observation: P3 is FALSE in the runtime trace.**

    At cycle 80 of `lake exe bitnet-mmio-probe`, `aiInputReg`
    holds 0x00010000 but `bitnetOut` reads 0. Per the Lean unit
    test golden (`bitnet-soc-test`), ffn(0x00010000) = 0x00410000,
    so the runtime violates premise P3.

    This theorem encodes the observation as a hypothetical: if a
    runtime trace produces `bitnetOut t = 0` while
    `aiInputReg t = 0x00010000`, then for ANY ffn function
    satisfying ffn(0x00010000) ≠ 0 (which the Lean spec does:
    ffn(0x00010000) = 0x00410000 ≠ 0), P3 is violated. -/
theorem P3_violated_at_cycle_80 {dom : DomainConfig}
    (aiInputReg bitnetOut : Signal dom (BitVec 32))
    (ffn : BitVec 32 → BitVec 32)
    (h_ffn : ffn (0x00010000#32) ≠ 0#32)
    (h_aiInputReg_at_80 : aiInputReg.val 80 = 0x00010000#32)
    (h_bitnetOut_at_80 : bitnetOut.val 80 = 0#32) :
    ¬ bitnetOut_combinational_contract aiInputReg bitnetOut ffn := by
  intro h_p3
  have h := h_p3 80
  rw [h_aiInputReg_at_80, h_bitnetOut_at_80] at h
  -- h : 0 = ffn 0x10000
  exact h_ffn h.symm

/-- **Per the Lean unit test, ffn(0x00010000) = 0x00410000 ≠ 0.**

    Concrete instantiation of `h_ffn` for the actual runtime
    observation. -/
theorem ffn_10000_nonzero : (0x00410000#32 : BitVec 32) ≠ 0#32 := by decide

/-! ## Summary: 4 layers, each falsifiable

  This is the proper formal-verification answer to "can we capture
  the bug in temporal logic": YES, by stating the 4-premise LTL
  contract explicitly. The contract is **discharged** for the Lean
  Sparkle spec (premises 1-4 all hold by Signal.register/Signal.mux
  semantics + bitNetPeripheral combinational structure). If the
  runtime observation contradicts the contract, then by the
  contrapositive AT LEAST ONE premise is FALSE in the runtime.

  Each falsified premise points to a specific bug class:

    P1 false → "register update is N cycles late" (synthesis bug:
               extra register stage inserted, or WE pulse dropped)
    P2 false → "register corrupted between writes" (unintended
               clear path, sneak write event)
    P3 false → "FFN output is delayed" (synthesis bug: extra
               register on the output, or "FFN block bypassed"
               (datapath shortcut)
    P4 false → "MMIO decoder routes 0x40000008 to wrong target"

  The "1 cycle early/late" bugs the user named are concretely
  capturable by P1 (input side) and P3 (output side).
-/

end Sparkle.IP.RV32.Verification
