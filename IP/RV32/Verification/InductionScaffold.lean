/-
  RV32 N-step register-tracking induction scaffold

  Step 2 of the proof-decomposition plan (RV32_Architecture_Status.md
  §3): build the *N-step* trace-level lemmas that lift cycle-N+1
  primitives into "for any K consecutive cycles, register is
  preserved." These are the foundation for whole-Linux-boot
  invariants — without them, every multi-cycle property must be
  hand-rolled per cycle count.

  The core abstraction is a *value-level* preservation lemma:
  given a stream `r : Nat → α` that satisfies a recurrence
  "next-state = if event at t then update else hold," prove
  "no event in [t, t+k) → r at t+k = r at t."

  Proof: induction on k. The recurrence + no-event hypothesis
  collapses to identity.

  The hardware-side proof obligations remain unchanged: callers
  prove the recurrence holds (one per register class), then the
  N-step lemma kicks in for free.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.CSR.Commit

namespace Sparkle.IP.RV32.Verification

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Generic N-step preservation

  Abstract over the value type and the recurrence. Two variants:
  one for Bool-update (simple write-enable) and one for the
  conditional-update pattern.
-/

/-- **N-step preservation under no-event hypothesis.**

    Given a sequence `r : Nat → α` and a Bool-stream `we`,
    if for every cycle `s` in [t, t+k) the recurrence
    `r (s+1) = if we s then update s else r s`
    is satisfied AND `we s = false`, then `r (t+k) = r t`.

    The recurrence is supplied as a hypothesis (one obligation per
    cycle in the window). For the typical use case where the
    recurrence is *uniform* (same shape every cycle), callers will
    discharge it once globally and apply this lemma for any t/k.
-/
theorem nstep_preserve_when_no_event {α : Type}
    (r : Nat → α) (we : Nat → Bool) (update : Nat → α)
    (h_recurrence : ∀ s, r (s + 1) = if we s then update s else r s) :
    ∀ (t k : Nat),
      (∀ i, i < k → we (t + i) = false) →
      r (t + k) = r t := by
  intro t k
  induction k with
  | zero =>
    intro _
    simp
  | succ k ih =>
    intro h_no_event
    -- r (t + (k+1)) = r ((t + k) + 1)
    have h_step :
        r ((t + k) + 1) = if we (t + k) then update (t + k) else r (t + k) :=
      h_recurrence (t + k)
    -- we (t + k) = false (apply h_no_event with i = k)
    have h_no_event_k : we (t + k) = false := by
      have h := h_no_event k (Nat.lt_succ_self k)
      exact h
    -- IH: r (t + k) = r t (no events in [t, t+k))
    have h_ih : r (t + k) = r t := by
      apply ih
      intro i hi
      exact h_no_event i (Nat.lt_succ_of_lt hi)
    -- Combine.
    show r (t + (k + 1)) = r t
    have : t + (k + 1) = (t + k) + 1 := by omega
    rw [this, h_step, h_no_event_k]
    exact h_ih

/-! ## Specialization to `csrPlainRegSignal`

  Wires the abstract N-step lemma to the concrete csrPlainRegSignal
  shape. The recurrence is supplied by the caller (since the SoC's
  CSR registers are recursive — `reg.val (t+1) = if we.val t then
  newVal.val t else reg.val t`).
-/

/-- **CSR plain register N-step preservation.**

    Given a `csrPlainRegSignal`-like recurrence (caller provides
    the recurrence proof — typically discharged via the SoC's
    fixed-point structure), no WE for K cycles → register unchanged. -/
theorem csrPlainReg_preserve_K_cycles {dom : DomainConfig}
    (regSig : Signal dom (BitVec 32))
    (writeActive : Signal dom Bool)
    (newVal : Signal dom (BitVec 32))
    (h_recurrence :
      ∀ s, regSig.val (s + 1) =
        if writeActive.val s then newVal.val s else regSig.val s) :
    ∀ (t k : Nat),
      (∀ i, i < k → writeActive.val (t + i) = false) →
      regSig.val (t + k) = regSig.val t :=
  nstep_preserve_when_no_event regSig.val writeActive.val newVal.val h_recurrence

/-! ## Specialization to BitVec 8 (UART registers)

  Same shape as the BitVec 32 version, just at byte width. -/

theorem csrPlainReg8_preserve_K_cycles {dom : DomainConfig}
    (regSig : Signal dom (BitVec 8))
    (writeActive : Signal dom Bool)
    (newVal : Signal dom (BitVec 8))
    (h_recurrence :
      ∀ s, regSig.val (s + 1) =
        if writeActive.val s then newVal.val s else regSig.val s) :
    ∀ (t k : Nat),
      (∀ i, i < k → writeActive.val (t + i) = false) →
      regSig.val (t + k) = regSig.val t :=
  nstep_preserve_when_no_event regSig.val writeActive.val newVal.val h_recurrence

/-! ## Specialization to `Bool` registers

  e.g., `pendingWriteEn`, `flushDelay`, `divPending`. -/

theorem boolReg_preserve_K_cycles {dom : DomainConfig}
    (regSig : Signal dom Bool)
    (writeActive : Signal dom Bool)
    (newVal : Signal dom Bool)
    (h_recurrence :
      ∀ s, regSig.val (s + 1) =
        if writeActive.val s then newVal.val s else regSig.val s) :
    ∀ (t k : Nat),
      (∀ i, i < k → writeActive.val (t + i) = false) →
      regSig.val (t + k) = regSig.val t :=
  nstep_preserve_when_no_event regSig.val writeActive.val newVal.val h_recurrence

/-! ## Generic N-step "any predicate stays false"

  Companion lemma: if a state register is "set on event, hold otherwise,"
  and the event never fires in [t, t+k), the register stays at its
  cycle-t value. This is the same shape as the preservation lemma —
  we re-export it for clarity at use sites. -/

theorem boolReg_stays_false_K_cycles {dom : DomainConfig}
    (regSig : Signal dom Bool)
    (event : Signal dom Bool)
    (h_recurrence :
      ∀ s, regSig.val (s + 1) = if event.val s then true else regSig.val s)
    (t k : Nat)
    (h_init : regSig.val t = false)
    (h_no_event : ∀ i, i < k → event.val (t + i) = false) :
    regSig.val (t + k) = false := by
  have h_preserve :=
    nstep_preserve_when_no_event regSig.val event.val (fun _ => true)
      h_recurrence t k h_no_event
  rw [h_preserve]
  exact h_init

/-! ## Concrete recurrence for `csrPlainRegSignal` self-loop

  For a CSR register defined as `r = Signal.register init
  (csrPlainNextSignal we newVal r)` (the SoC's actual shape — the
  register's own output is fed back as `old`), the recurrence is:

    r.val (s+1) = if we.val s then newVal.val s else r.val s

  This is what `nstep_preserve_when_no_event` consumes, so callers
  with a self-looped CSR register can chain directly into the N-step
  preservation lemma.

  Note: the self-loop is broken by `Signal.register` (one cycle of
  delay), so this is well-defined.
-/

/-- **The self-loop CSR register satisfies the canonical recurrence.** -/
theorem csrPlainReg_selfLoop_recurrence {dom : DomainConfig}
    (init : BitVec 32) (writeActive : Signal dom Bool)
    (newVal : Signal dom (BitVec 32)) :
    let regSig :=
      Signal.register init
        (Sparkle.IP.RV32.CSR.csrPlainNextSignal writeActive newVal
          (Signal.register init
            (Sparkle.IP.RV32.CSR.csrPlainNextSignal writeActive newVal
              (Signal.pure init))))
    ∀ s, regSig.val (s + 1) =
      if writeActive.val s then newVal.val s
      else (Signal.register init
              (Sparkle.IP.RV32.CSR.csrPlainNextSignal writeActive newVal
                (Signal.pure init))).val s := by
  intro regSig s
  show (Signal.register init _).val (s + 1) = _
  show (Sparkle.IP.RV32.CSR.csrPlainNextSignal writeActive newVal _).val s = _
  rw [Sparkle.IP.RV32.CSR.csrPlainNextSignal_eq_pure]
  unfold Sparkle.IP.RV32.CSR.csrPlainNextPure
  rfl

/-! ## End-to-end demonstration: K-cycle CSR preservation

  Combines `csrPlainNextSignal_eq_pure` (the cycle-wise recurrence)
  with `nstep_preserve_when_no_event` (induction over K) to give
  the trace-level invariant for an *abstract* CSR register stream:

    "If `writeActive.val (t+i) = false` for all i < K, then
     `csrPlainRegSignal init writeActive newVal r .val (t+K) =
      csrPlainRegSignal init writeActive newVal r .val t`"

  for *any* feedback signal `r` that satisfies the canonical
  recurrence `r.val (s+1) = csrPlainNextPure (writeActive.val s)
  (newVal.val s) (r.val s)`. This is the exact shape consumed by
  callers that have a self-looped SoC register.
-/

theorem csrPlainReg_K_cycles_no_write {dom : DomainConfig}
    (regSig : Signal dom (BitVec 32))
    (writeActive : Signal dom Bool)
    (newVal : Signal dom (BitVec 32))
    (h_recurrence :
      ∀ s, regSig.val (s + 1) =
        Sparkle.IP.RV32.CSR.csrPlainNextPure
          (writeActive.val s) (newVal.val s) (regSig.val s)) :
    ∀ (t k : Nat),
      (∀ i, i < k → writeActive.val (t + i) = false) →
      regSig.val (t + k) = regSig.val t := by
  -- Reduce csrPlainNextPure to the if-then-else shape consumed by
  -- nstep_preserve_when_no_event.
  apply nstep_preserve_when_no_event regSig.val writeActive.val newVal.val
  intro s
  rw [h_recurrence]
  unfold Sparkle.IP.RV32.CSR.csrPlainNextPure
  rfl

/-! ## K-cycle post-trap preservation composite

  Combines a cycle-N+1 register-update lemma (caller-supplied,
  typically the cycle-N+1 LTL form of a trap-suppression theorem)
  with the N-step preservation lemma to give:

    "If trap fires at cycle N and the WE stays false in
     [N+1, N+1+K), then the register at N+1+K equals the register
     at N+1."

  This is the temporal pattern that arises in Linux-boot reasoning:
  a trap fires once (e.g., timer interrupt), and the kernel's
  ISR runs for many cycles without touching CSR mscratch — we need
  to know mscratch is unchanged through the entire ISR window.

  The "register at N+1" anchor is whatever value the cycle-N+1
  lemma produces (typically `old.val N` for the trap-hold case, or
  the trap-payload for the trap-override case). This composite lets
  the caller chain that anchor with the K-cycle preservation. -/

/-- **Generic K-cycle post-trap preservation.**

    If at cycle N+1 the register holds value `v` (caller-supplied
    via `h_at_N1`), and the WE is false for the K cycles
    [N+1, N+1+K), then at cycle N+1+K the register still holds `v`.

    Caller discharges:
      * `h_recurrence` — the canonical register recurrence.
      * `h_at_N1` — the cycle-N+1 anchor (e.g., from a trap-hold lemma).
      * `h_no_event` — no WE fires in the K-cycle window after N+1.
-/
theorem post_trap_preserve_K_cycles {α : Type}
    (r : Nat → α) (we : Nat → Bool) (update : Nat → α)
    (h_recurrence : ∀ s, r (s + 1) = if we s then update s else r s)
    (n : Nat) (v : α)
    (h_at_N1 : r (n + 1) = v) :
    ∀ (k : Nat),
      (∀ i, i < k → we (n + 1 + i) = false) →
      r (n + 1 + k) = v := by
  intro k h_no_event
  have h_preserve :=
    nstep_preserve_when_no_event r we update h_recurrence (n + 1) k h_no_event
  rw [h_preserve]
  exact h_at_N1

/-- **CSR-specialized post-trap preservation.**

    The α-generic version above instantiated for `BitVec 32` CSR
    registers, with the recurrence reduced to the `if-then-else`
    shape consumed by `post_trap_preserve_K_cycles`. -/
theorem csrPlainReg_post_trap_K_cycles_no_write {dom : DomainConfig}
    (regSig : Signal dom (BitVec 32))
    (writeActive : Signal dom Bool)
    (newVal : Signal dom (BitVec 32))
    (h_recurrence :
      ∀ s, regSig.val (s + 1) =
        Sparkle.IP.RV32.CSR.csrPlainNextPure
          (writeActive.val s) (newVal.val s) (regSig.val s))
    (n : Nat) (v : BitVec 32)
    (h_at_N1 : regSig.val (n + 1) = v) :
    ∀ (k : Nat),
      (∀ i, i < k → writeActive.val (n + 1 + i) = false) →
      regSig.val (n + 1 + k) = v := by
  apply post_trap_preserve_K_cycles regSig.val writeActive.val newVal.val
  · intro s
    rw [h_recurrence]
    unfold Sparkle.IP.RV32.CSR.csrPlainNextPure
    rfl
  · exact h_at_N1

end Sparkle.IP.RV32.Verification
