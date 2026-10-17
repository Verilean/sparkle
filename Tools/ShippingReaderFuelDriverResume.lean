import Tools.ShippingReaderFuelDriverComplete

/-! # A resumable driver for the fuel wrapper `machineShapeF`

BUILT on poc 25f877f8 (run `l1`: `cgrun -n l1 -m 3G -j 1 -- lake build Tools.ShippingReaderFuelDriverResume`, exit 0) (worker L, branch `par/r-16`, base poc 20304f50; reviewer
2026-10-17 item 3). No `sorry`, no axiom, no `native_decide`. Imports only the
BUILT `Tools.ShippingReaderFuelDriverComplete`. NOT used by the compiler:
production still calls the `partial` reader `machineShape?`; nothing under
`Sparkle/` changed.

## Design choice: option (ii), a RESUMABLE driver (no `partial def`)

* `resumeStep step s : ResumeState ⊕ (Option α × Nat)` is ONE total attempt:
  it calls the three-valued `step` at `s.fuel`; on OUT it returns the next
  state (`fuel := 2 * s.fuel`), on FAIL / OK it returns the answer TOGETHER
  WITH ITS FUEL WITNESS `(o, s.fuel)`. `o = none` is the ordinary refusal,
  `o = some sh` the success.
* `resumeRun step k s` runs at most `k` attempts. When the `k` attempts are
  used up it returns `Sum.inl s'` — the RESUMABLE STATE, a value of a
  different type summand than any answer. A budget / cancellation outcome is
  therefore never a refusal: it carries no verdict and can be continued
  (`resumeRun_add`: running `j` then `k` attempts = running `j + k`).
* No `partial def` is provided: a caller (IO loop, experiment with a time
  limit, cancellation token) iterates `resumeRun` / `resumeStep` as long as it
  wants; every theorem is about the total functions. Chosen over option (i)
  because the theorems then hold of the very function that is executed, not
  of a separate specification of an unreasoned `partial def`.

## What is proved

Generic (any three-valued `step`; completion needs `StepStable` and a positive
start fuel), and instantiated for `machineShapeF` (`runShapeFor`,
`resumeInit start = ⟨max start 1, 0⟩`):

* RETURN SOUNDNESS: `resumeRun_sound` / `runShapeFor_sound` — every returned
  `(o, n)` has `step n = some o`, `n = 2 ^ j * s.fuel` with `j < k`; hence
  every larger fuel gives `o` (`runShapeFor_stable`) and no fuel gives a
  different non-OUT answer (`runShapeFor_genuine`). In particular a returned
  FAIL is a genuine refusal of the wrapper, never produced for OUT.
* BUDGET OUTCOME: `resumeRun_inl` / `runShapeFor_budget` — a resumable state
  after `k` attempts has `fuel = 2 ^ k * s.fuel`, `tries = s.tries + k`, and
  the `k` attempted fuels were all OUT. `resumeRun_inl_of_out`: if every fuel
  is OUT the driver never answers (never refuses).
* ANSWER STABILITY: `resumeRun_inr_mono` (more attempts never change an
  answer), `resumeAnswers_unique`.
* EVENTUAL COMPLETION: `resumeRun_complete_le` (`N ≤ 2 ^ k * s.fuel` ⟹ an
  answer within `k + 1` attempts), `resumeRun_complete`, and for the wrapper
  `runShapeFor_complete_le` (`machineShapeF N … = some r` ⟹ answer `r` after
  at most `N + 1` attempts from any positive state), `runShapeFor_complete_init`,
  `runShapeFor_resume_complete` (completion also from ANY state an earlier
  budget-limited run stopped in), `shapeRuns_resume` (from a finite derivation
  `ShapeRuns`), `driveShape_resume` (whatever the bounded driver answers, the
  resumable driver answers too), `runShapeFor_out_forever_iff`,
  `resumeAnswers_iff` (total specification: the resumable driver eventually
  answers `o` ⟺ some fuel answers `o`).
* RETRY AUDIT: `machineShapeF` is a pure total function; the only state
  carried between attempts is `ResumeState` (`fuel` and the bookkeeping
  counter `tries`). Proved: `resumeShape_inr_iff` / `resumeShape_inl_iff` (an
  attempt's outcome is exactly a FRESH call `machineShapeF s.fuel …`; nothing
  of earlier attempts enters), `resumeRun_view` (runs from two states with the
  same fuel give the same answers and the same next fuels — `tries` never
  influences anything).

## What is NOT proved (kept apart)

* O1 / O2 (the MetaM execution bridge between the compiled `partial`
  `machineShape?` and the wrapper): no axiom, no statement here.
* Termination: the resumable driver need not answer at all (when every fuel is
  OUT); that is the intended behaviour — it then keeps returning resumable
  states, never a verdict. -/
namespace Tools.ShippingReaderFuel
open Lean
open Sparkle.Compiler.Elab

/-! ## The resumable state and the total step -/

/-- The only state carried between attempts: the next fuel and a counter. -/
structure ResumeState where
  fuel : Nat
  tries : Nat

/-- The initial state: fuel `max start 1` (fuel `0` is always OUT once the
prefix passes), no attempt yet. -/
def resumeInit (start : Nat) : ResumeState :=
  { fuel := max start 1, tries := 0 }

/-- **One attempt.** OUT ⟹ the next state (fuel doubled); FAIL / OK ⟹ the
answer with its fuel witness. -/
def resumeStep {α : Type} (step : Nat → Option (Option α)) (s : ResumeState) :
    ResumeState ⊕ (Option α × Nat) :=
  match step s.fuel with
  | none => Sum.inl { fuel := 2 * s.fuel, tries := s.tries + 1 }
  | some o => Sum.inr (o, s.fuel)

/-- **At most `k` attempts.** `Sum.inl s'`: budget used up, resumable from
`s'` (NOT a verdict); `Sum.inr (o, n)`: the answer `o` at fuel `n`. -/
def resumeRun {α : Type} (step : Nat → Option (Option α)) :
    Nat → ResumeState → ResumeState ⊕ (Option α × Nat)
  | 0, s => Sum.inl s
  | k + 1, s =>
    match resumeStep step s with
    | Sum.inl s' => resumeRun step k s'
    | Sum.inr a => Sum.inr a

/-- Continue a run for `k` more attempts (an answer is kept as it is). -/
def resumeCont {α : Type} (step : Nat → Option (Option α)) (k : Nat) :
    ResumeState ⊕ (Option α × Nat) → ResumeState ⊕ (Option α × Nat)
  | Sum.inl s => resumeRun step k s
  | Sum.inr a => Sum.inr a

/-- What a run shows when the counter `tries` is forgotten. -/
def resumeView {β : Type} : ResumeState ⊕ β → Nat ⊕ β
  | Sum.inl s => Sum.inl s.fuel
  | Sum.inr a => Sum.inr a

/-- **Total specification**: run long enough, the resumable driver returns
`a`. -/
def ResumeAnswers {α : Type} (step : Nat → Option (Option α)) (s : ResumeState)
    (a : Option α × Nat) : Prop :=
  ∃ k, resumeRun step k s = Sum.inr a

section Generic
variable {α : Type} (step : Nat → Option (Option α))

theorem resumeStep_out {s : ResumeState} (h : step s.fuel = none) :
    resumeStep step s = Sum.inl ({ fuel := 2 * s.fuel, tries := s.tries + 1 } : ResumeState) := by
  first
    | (simp only [resumeStep, h]; done)
    | (unfold resumeStep; rw [h])

theorem resumeStep_some {s : ResumeState} {o : Option α} (h : step s.fuel = some o) :
    resumeStep step s = Sum.inr (o, s.fuel) := by
  first
    | (simp only [resumeStep, h]; done)
    | (unfold resumeStep; rw [h])

theorem resumeStep_inl {s s' : ResumeState} (h : resumeStep step s = Sum.inl s') :
    step s.fuel = none ∧ s'.fuel = 2 * s.fuel ∧ s'.tries = s.tries + 1 := by
  cases hs : step s.fuel with
  | none =>
    rw [resumeStep_out step hs] at h
    cases h
    refine ⟨?_, rfl, rfl⟩
    first | rfl | exact hs
  | some o =>
    rw [resumeStep_some step hs] at h
    cases h

theorem resumeStep_inr {s : ResumeState} {o : Option α} {n : Nat}
    (h : resumeStep step s = Sum.inr (o, n)) : step s.fuel = some o ∧ n = s.fuel := by
  cases hs : step s.fuel with
  | none =>
    rw [resumeStep_out step hs] at h
    cases h
  | some o' =>
    rw [resumeStep_some step hs] at h
    cases h
    refine ⟨?_, rfl⟩
    first | rfl | exact hs

/-- **Retry audit (one attempt)**: an attempt answers exactly what a fresh call
of `step` at the state's fuel answers. -/
theorem resumeStep_inr_iff (s : ResumeState) (o : Option α) (n : Nat) :
    resumeStep step s = Sum.inr (o, n) ↔ step s.fuel = some o ∧ n = s.fuel := by
  constructor
  · exact resumeStep_inr step
  · intro h
    obtain ⟨h1, h2⟩ := h
    rw [h2]
    exact resumeStep_some step h1

theorem resumeStep_inl_iff (s s' : ResumeState) :
    resumeStep step s = Sum.inl s' ↔
      step s.fuel = none ∧ s'.fuel = 2 * s.fuel ∧ s'.tries = s.tries + 1 := by
  constructor
  · exact resumeStep_inl step
  · intro h
    obtain ⟨h1, h2, h3⟩ := h
    rw [resumeStep_out step h1]
    cases s' with
    | mk f t =>
      have h2' : f = 2 * s.fuel := h2
      have h3' : t = s.tries + 1 := h3
      rw [h2', h3']

theorem resumeRun_succ_inl {k : Nat} {s s' : ResumeState}
    (h : resumeStep step s = Sum.inl s') :
    resumeRun step (k + 1) s = resumeRun step k s' := by
  simp only [resumeRun, h]

theorem resumeRun_succ_inr {k : Nat} {s : ResumeState} {a : Option α × Nat}
    (h : resumeStep step s = Sum.inr a) :
    resumeRun step (k + 1) s = Sum.inr a := by
  simp only [resumeRun, h]

/-- **Resumption**: `j` attempts, then `k` more from where it stopped, is the
same as `j + k` attempts. -/
theorem resumeRun_add : ∀ (j k : Nat) (s : ResumeState),
    resumeRun step (j + k) s = resumeCont step k (resumeRun step j s)
  | 0, k, s => by
    rw [Nat.zero_add]
    all_goals rfl
  | j + 1, k, s => by
    rw [Nat.add_right_comm j 1 k]
    cases h : resumeStep step s with
    | inl s' =>
      rw [resumeRun_succ_inl step h, resumeRun_succ_inl step h]
      exact resumeRun_add j k s'
    | inr a =>
      rw [resumeRun_succ_inr step h, resumeRun_succ_inr step h]
      all_goals rfl

/-- **Return soundness**: a returned `(o, n)` is the step's answer at the
witness fuel `n`, one of the attempted fuels `2 ^ j * s.fuel`, `j < k`. -/
theorem resumeRun_sound : ∀ {k : Nat} {s : ResumeState} {o : Option α} {n : Nat},
    resumeRun step k s = Sum.inr (o, n) →
      step n = some o ∧ ∃ j, j < k ∧ n = 2 ^ j * s.fuel
  | 0, s, o, n, h => by
    have h' : (Sum.inl s : ResumeState ⊕ (Option α × Nat)) = Sum.inr (o, n) := h
    cases h'
  | k + 1, s, o, n, h => by
    cases hr : resumeStep step s with
    | inl s1 =>
      obtain ⟨_, hf1, _⟩ := resumeStep_inl step hr
      rw [resumeRun_succ_inl step hr] at h
      obtain ⟨h1, j, hj, hn⟩ := resumeRun_sound h
      refine ⟨h1, j + 1, Nat.succ_lt_succ hj, ?_⟩
      rw [hn, hf1, drv_two_pow_succ_mul]
    | inr a =>
      rw [resumeRun_succ_inr step hr] at h
      have ha : a = (o, n) := Sum.inr.inj h
      rw [ha] at hr
      obtain ⟨h1, h2⟩ := resumeStep_inr step hr
      refine ⟨?_, 0, Nat.zero_lt_succ k, ?_⟩
      · rw [h2]
        exact h1
      · rw [Nat.pow_zero, Nat.one_mul]
        exact h2

/-- **Budget outcome**: a resumable state after `k` attempts has fuel
`2 ^ k * s.fuel`, counter `s.tries + k`, and every attempted fuel was OUT. -/
theorem resumeRun_inl : ∀ {k : Nat} {s s' : ResumeState},
    resumeRun step k s = Sum.inl s' →
      s'.fuel = 2 ^ k * s.fuel ∧ s'.tries = s.tries + k ∧
        ∀ j, j < k → step (2 ^ j * s.fuel) = none
  | 0, s, s', h => by
    have h' : (Sum.inl s : ResumeState ⊕ (Option α × Nat)) = Sum.inl s' := h
    cases h'
    refine ⟨?_, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    rw [Nat.pow_zero, Nat.one_mul]
  | k + 1, s, s', h => by
    cases hr : resumeStep step s with
    | inl s1 =>
      obtain ⟨hout, hf1, ht1⟩ := resumeStep_inl step hr
      rw [resumeRun_succ_inl step hr] at h
      obtain ⟨hf, ht, hall⟩ := resumeRun_inl h
      refine ⟨?_, ?_, ?_⟩
      · rw [hf, hf1, drv_two_pow_succ_mul]
      · rw [ht, ht1]
        all_goals omega
      · intro j hj
        cases j with
        | zero =>
          rw [Nat.pow_zero, Nat.one_mul]
          exact hout
        | succ j =>
          have h2 := hall j (by omega)
          rw [hf1, ← drv_two_pow_succ_mul] at h2
          exact h2
    | inr a =>
      rw [resumeRun_succ_inr step hr] at h
      cases h

/-- If every fuel is OUT, the driver never answers — in particular it never
refuses. -/
theorem resumeRun_inl_of_out (hout : ∀ N, step N = none) (k : Nat) (s : ResumeState) :
    ∃ s', resumeRun step k s = Sum.inl s' := by
  cases hk : resumeRun step k s with
  | inl s' => exact ⟨s', rfl⟩
  | inr a =>
    rcases a with ⟨o, n⟩
    have h1 := (resumeRun_sound step hk).1
    rw [hout n] at h1
    cases h1

/-- More attempts never change an answer. -/
theorem resumeRun_inr_mono {k k' : Nat} {s : ResumeState} {a : Option α × Nat}
    (h : resumeRun step k s = Sum.inr a) (hk : k ≤ k') :
    resumeRun step k' s = Sum.inr a := by
  obtain ⟨d, rfl⟩ : ∃ d, k' = k + d := ⟨k' - k, by omega⟩
  rw [resumeRun_add step k d s, h]
  all_goals rfl

/-- **Retry audit (runs)**: the counter `tries` never influences a run; two
states with the same fuel give the same answers and the same next fuels. -/
theorem resumeRun_view : ∀ (k : Nat) (s t : ResumeState), s.fuel = t.fuel →
    resumeView (resumeRun step k s) = resumeView (resumeRun step k t)
  | 0, s, t, hf => by
    show (Sum.inl s.fuel : Nat ⊕ (Option α × Nat)) = Sum.inl t.fuel
    rw [hf]
  | k + 1, s, t, hf => by
    cases h1 : step s.fuel with
    | none =>
      have h2 : step t.fuel = none := by
        rw [← hf]
        exact h1
      rw [resumeRun_succ_inl step (resumeStep_out step h1),
        resumeRun_succ_inl step (resumeStep_out step h2)]
      exact resumeRun_view k _ _ (by show 2 * s.fuel = 2 * t.fuel; rw [hf])
    | some o =>
      have h2 : step t.fuel = some o := by
        rw [← hf]
        exact h1
      rw [resumeRun_succ_inr step (resumeStep_some step h1),
        resumeRun_succ_inr step (resumeStep_some step h2), hf]

/-- **Completion with an explicit attempt bound.** -/
theorem resumeRun_complete_le (hs : StepStable step) {N : Nat} {o : Option α}
    (hN : step N = some o) :
    ∀ (k : Nat) (s : ResumeState), N ≤ 2 ^ k * s.fuel →
      ∃ n, resumeRun step (k + 1) s = Sum.inr (o, n)
  | 0, s, hle => by
    rw [Nat.pow_zero, Nat.one_mul] at hle
    have h1 := hs hN hle
    exact ⟨s.fuel, resumeRun_succ_inr step (resumeStep_some step h1)⟩
  | k + 1, s, hle => by
    cases h : step s.fuel with
    | none =>
      rw [resumeRun_succ_inl step (resumeStep_out step h)]
      rw [drv_two_pow_succ_mul k s.fuel] at hle
      exact resumeRun_complete_le hs hN k { fuel := 2 * s.fuel, tries := s.tries + 1 } hle
    | some o' =>
      have h1 := hs h (drv_le_two_pow_mul (k + 1) s.fuel)
      have h2 := hs hN hle
      rw [h1] at h2
      have ho : o' = o := Option.some.inj h2
      rw [ho] at h
      exact ⟨s.fuel, resumeRun_succ_inr step (resumeStep_some step h)⟩

/-- **Eventual completion** from a positive fuel. -/
theorem resumeRun_complete (hs : StepStable step) {N : Nat} {o : Option α}
    (hN : step N = some o) {s : ResumeState} (hn : 0 < s.fuel) :
    ∃ k n, resumeRun step k s = Sum.inr (o, n) := by
  obtain ⟨n, h⟩ := resumeRun_complete_le step hs hN N s
    (drv_le_two_pow_mul_pos hn N (drv_self_le_two_pow N))
  exact ⟨N + 1, n, h⟩

/-- A state reached by a budget-limited run from a positive fuel is positive. -/
theorem resumeRun_inl_pos {k : Nat} {s s' : ResumeState} (hn : 0 < s.fuel)
    (h : resumeRun step k s = Sum.inl s') : 0 < s'.fuel := by
  obtain ⟨hf, _, _⟩ := resumeRun_inl step h
  rw [hf]
  exact Nat.lt_of_lt_of_le hn (drv_le_two_pow_mul k s.fuel)

theorem resumeRun_out_forever_iff (hs : StepStable step) {s : ResumeState}
    (hn : 0 < s.fuel) :
    (∀ k, ∃ s', resumeRun step k s = Sum.inl s') ↔ ∀ N, step N = none := by
  constructor
  · intro h N
    cases hN : step N with
    | none => rfl
    | some o =>
      obtain ⟨k, n, hk⟩ := resumeRun_complete step hs hN hn
      obtain ⟨s', hs'⟩ := h k
      rw [hs'] at hk
      cases hk
  · intro h k
    exact resumeRun_inl_of_out step h k s

theorem resumeAnswers_sound {s : ResumeState} {o : Option α} {n : Nat}
    (h : ResumeAnswers step s (o, n)) : step n = some o := by
  obtain ⟨k, hk⟩ := h
  exact (resumeRun_sound step hk).1

theorem resumeAnswers_unique {s : ResumeState} {a a' : Option α × Nat}
    (h : ResumeAnswers step s a) (h' : ResumeAnswers step s a') : a = a' := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨k', hk'⟩ := h'
  rcases Nat.le_total k k' with hle | hle
  · have h2 := resumeRun_inr_mono step hk hle
    rw [hk'] at h2
    exact (Sum.inr.inj h2).symm
  · have h2 := resumeRun_inr_mono step hk' hle
    rw [hk] at h2
    exact Sum.inr.inj h2

/-- **The total specification, both ways**: the resumable driver eventually
answers `o` ⟺ some fuel answers `o`. -/
theorem resumeAnswers_iff (hs : StepStable step) {s : ResumeState} (hn : 0 < s.fuel)
    (o : Option α) :
    (∃ n, ResumeAnswers step s (o, n)) ↔ ∃ N, step N = some o := by
  constructor
  · intro h
    obtain ⟨n, hn'⟩ := h
    exact ⟨n, resumeAnswers_sound step hn'⟩
  · intro h
    obtain ⟨N, hN⟩ := h
    obtain ⟨k, n, hk⟩ := resumeRun_complete step hs hN hn
    exact ⟨n, (⟨k, hk⟩ : ∃ k, resumeRun step k s = Sum.inr (o, n))⟩

end Generic

/-! ## The wrapper instance -/

/-- One attempt of the wrapper at the state's fuel. -/
def resumeShape (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo) (senv : StructEnv)
    (ai : Bool) (s : ResumeState) : ResumeState ⊕ (Option MachineShape × Nat) :=
  resumeStep (fun n => machineShapeF n sm ps ci senv ai) s

/-- At most `budget` attempts of the wrapper from `s`; `Sum.inl` = resumable,
undecided (never a refusal). -/
def runShapeFor (budget : Nat) (s : ResumeState) (sm : Bool) (ps : List (String × Nat))
    (ci : ConstantInfo) (senv : StructEnv) (ai : Bool := true) :
    ResumeState ⊕ (Option MachineShape × Nat) :=
  resumeRun (fun n => machineShapeF n sm ps ci senv ai) budget s

section Shape
variable {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo} {senv : StructEnv}
  {ai : Bool}

theorem resumeInit_pos (start : Nat) : 0 < (resumeInit start).fuel :=
  drv_max_pos start

/-- **Retry audit**: an attempt's answer is the answer of a fresh call of the
wrapper at the state's fuel. -/
theorem resumeShape_inr_iff (s : ResumeState) (o : Option MachineShape) (n : Nat) :
    resumeShape sm ps ci senv ai s = Sum.inr (o, n) ↔
      machineShapeF s.fuel sm ps ci senv ai = some o ∧ n = s.fuel :=
  resumeStep_inr_iff (fun n => machineShapeF n sm ps ci senv ai) s o n

theorem resumeShape_inl_iff (s s' : ResumeState) :
    resumeShape sm ps ci senv ai s = Sum.inl s' ↔
      machineShapeF s.fuel sm ps ci senv ai = none ∧ s'.fuel = 2 * s.fuel ∧
        s'.tries = s.tries + 1 :=
  resumeStep_inl_iff (fun n => machineShapeF n sm ps ci senv ai) s s'

/-- The counter never influences a wrapper run. -/
theorem runShapeFor_view (k : Nat) (s t : ResumeState) (hf : s.fuel = t.fuel) :
    resumeView (runShapeFor k s sm ps ci senv ai) =
      resumeView (runShapeFor k t sm ps ci senv ai) :=
  resumeRun_view (fun n => machineShapeF n sm ps ci senv ai) k s t hf

/-- **Return soundness**: a returned `(r, n)` is the wrapper's answer at the
witness fuel `n`. -/
theorem runShapeFor_sound {k : Nat} {s : ResumeState} {r : Option MachineShape} {n : Nat}
    (h : runShapeFor k s sm ps ci senv ai = Sum.inr (r, n)) :
    machineShapeF n sm ps ci senv ai = some r ∧ ∃ j, j < k ∧ n = 2 ^ j * s.fuel :=
  resumeRun_sound (fun n => machineShapeF n sm ps ci senv ai) h

/-- ... and at every larger fuel. -/
theorem runShapeFor_stable {k : Nat} {s : ResumeState} {r : Option MachineShape} {n : Nat}
    (h : runShapeFor k s sm ps ci senv ai = Sum.inr (r, n)) {m : Nat} (hm : n ≤ m) :
    machineShapeF m sm ps ci senv ai = some r :=
  machineShapeF_stable (runShapeFor_sound h).1 hm

/-- **A returned answer is genuine**: no fuel gives a different non-OUT
answer (a returned FAIL: no fuel gives OK; a returned OK: no fuel FAILs). -/
theorem runShapeFor_genuine {k : Nat} {s : ResumeState} {r : Option MachineShape} {n : Nat}
    (h : runShapeFor k s sm ps ci senv ai = Sum.inr (r, n)) (m : Nat) :
    machineShapeF m sm ps ci senv ai = none ∨ machineShapeF m sm ps ci senv ai = some r := by
  have h1 := (runShapeFor_sound h).1
  cases hm : machineShapeF m sm ps ci senv ai with
  | none => exact Or.inl rfl
  | some o =>
    right
    rw [machineShapeF_det hm h1]

/-- **Budget outcome**: a resumable state, every attempted fuel OUT. -/
theorem runShapeFor_budget {k : Nat} {s s' : ResumeState}
    (h : runShapeFor k s sm ps ci senv ai = Sum.inl s') :
    s'.fuel = 2 ^ k * s.fuel ∧ s'.tries = s.tries + k ∧
      ∀ j, j < k → machineShapeF (2 ^ j * s.fuel) sm ps ci senv ai = none :=
  resumeRun_inl (fun n => machineShapeF n sm ps ci senv ai) h

theorem runShapeFor_inr_mono {k k' : Nat} {s : ResumeState} {a : Option MachineShape × Nat}
    (h : runShapeFor k s sm ps ci senv ai = Sum.inr a) (hk : k ≤ k') :
    runShapeFor k' s sm ps ci senv ai = Sum.inr a :=
  resumeRun_inr_mono (fun n => machineShapeF n sm ps ci senv ai) h hk

/-- **Completion, explicit bound**: fuel `N` answers `r` ⟹ from any positive
state the resumable driver answers `r` within `N + 1` attempts. -/
theorem runShapeFor_complete_le {N : Nat} {r : Option MachineShape}
    (hN : machineShapeF N sm ps ci senv ai = some r) {s : ResumeState} (hn : 0 < s.fuel) :
    ∃ n, runShapeFor (N + 1) s sm ps ci senv ai = Sum.inr (r, n) :=
  resumeRun_complete_le (fun n => machineShapeF n sm ps ci senv ai)
    (machineShapeF_stepStable sm ps ci senv ai) hN N s
    (drv_le_two_pow_mul_pos hn N (drv_self_le_two_pow N))

theorem runShapeFor_complete_init {N : Nat} {r : Option MachineShape}
    (hN : machineShapeF N sm ps ci senv ai = some r) (start : Nat) :
    ∃ n, runShapeFor (N + 1) (resumeInit start) sm ps ci senv ai = Sum.inr (r, n) :=
  runShapeFor_complete_le hN (resumeInit_pos start)

/-- **Resumption never loses the answer**: from ANY state a budget-limited run
stopped in, continuing reaches the answer of any fuel that answers. -/
theorem runShapeFor_resume_complete {N : Nat} {r : Option MachineShape}
    (hN : machineShapeF N sm ps ci senv ai = some r) {start j : Nat} {s' : ResumeState}
    (hj : runShapeFor j (resumeInit start) sm ps ci senv ai = Sum.inl s') :
    ∃ n, runShapeFor (N + 1) s' sm ps ci senv ai = Sum.inr (r, n) :=
  runShapeFor_complete_le hN
    (resumeRun_inl_pos (fun n => machineShapeF n sm ps ci senv ai) (resumeInit_pos start) hj)

/-- **A finite derivation of the wrapper ⟹ the resumable driver answers the
same.** -/
theorem shapeRuns_resume {r : Option MachineShape} (h : ShapeRuns sm ps ci senv ai r)
    (start : Nat) :
    ∃ k n, runShapeFor k (resumeInit start) sm ps ci senv ai = Sum.inr (r, n) := by
  obtain ⟨N, hN⟩ := shapeRuns_fuel h
  obtain ⟨n, hn⟩ := runShapeFor_complete_init hN start
  exact ⟨N + 1, n, hn⟩

/-- Whatever the bounded driver answers, the resumable driver answers too. -/
theorem driveShape_resume {rounds start : Nat} {r : Option MachineShape}
    (h : (driveShape rounds start sm ps ci senv ai).res = some r) :
    ∃ k n, runShapeFor k (resumeInit start) sm ps ci senv ai = Sum.inr (r, n) := by
  have hN := (driveShape_res rounds start sm ps ci senv ai).symm.trans h
  obtain ⟨n, hn⟩ := runShapeFor_complete_init hN start
  exact ⟨_, n, hn⟩

/-- Never answering ⟺ OUT at every fuel. -/
theorem runShapeFor_out_forever_iff (start : Nat) :
    (∀ k, ∃ s', runShapeFor k (resumeInit start) sm ps ci senv ai = Sum.inl s') ↔
      ∀ N, machineShapeF N sm ps ci senv ai = none :=
  resumeRun_out_forever_iff (fun n => machineShapeF n sm ps ci senv ai)
    (machineShapeF_stepStable sm ps ci senv ai) (resumeInit_pos start)

/-- The total specification for the wrapper. -/
theorem resumeShape_answers_iff (start : Nat) (r : Option MachineShape) :
    (∃ n, ResumeAnswers (fun n => machineShapeF n sm ps ci senv ai) (resumeInit start) (r, n)) ↔
      ∃ N, machineShapeF N sm ps ci senv ai = some r :=
  resumeAnswers_iff (fun n => machineShapeF n sm ps ci senv ai)
    (machineShapeF_stepStable sm ps ci senv ai) (resumeInit_pos start) r

end Shape

end Tools.ShippingReaderFuel
