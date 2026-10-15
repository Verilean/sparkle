import Tools.ShippingReaderFuelDriver
import Tools.ShippingReaderFuelEval

/-! # Eventual completion of the doubling driver

WRITTEN, NOT BUILT (worker G, branch `par/r-11`, base poc a3a1d2d4; record
`docs/parallel/R-reader-fuel.md` §"Driver completion"). No `sorry`, no
axiom, no `native_decide`. Imports only BUILT files (`…FuelDriver`,
`…FuelEval`). NOT used by the compiler: production still calls the `partial`
reader `machineShape?`; nothing under `Sparkle/` changed.

## What is proved

The bounded driver `driveLoop step rounds n k` / `driveShape rounds start …`
(`Tools/ShippingReaderFuelDriver.lean`) is a TEST tool: a final OUT means ONLY
"undecided within this trial budget". This file proves that the budget is the
only reason for an OUT — for a fuel-stable step, every answer that SOME fuel
reaches is reached by the driver after finitely many rounds, and it is the SAME
answer:

* generic, any stable `step` (`StepStable`):
  `driveLoop_complete_le` (every round bound `r` with `N ≤ 2 ^ r * n`),
  `driveLoop_complete` (`∃ rounds`, start `n > 0`),
  `driveLoop_complete_iff` (the driver eventually answers `o` ⟺ some fuel
  answers `o`), `driveLoop_out_forever_iff` (OUT for every round bound ⟺ OUT
  at every fuel);
* the wrapper: `machineShapeF_stepStable`, `driveShape_complete_le`
  (`N ≤ 2 ^ rounds`), `driveShape_complete_ge` (`N ≤ rounds`),
  `driveShape_complete` (`∃ rounds`), `driveShape_complete_ok` /
  `driveShape_complete_fail` (success `some s` / ordinary refusal `none`),
  `driveShape_complete_iff`, `driveShape_out_forever_iff`. No hypothesis on
  `start`: the driver starts at `max start 1 > 0`.
* the block-level / wrapper-level link with the finite-execution relation of
  `Tools/ShippingReaderFuelEval.lean`: `WEval` (a `machNorm` call by `EvalN`, a
  block call by `Eval`), `ShapeRuns` (the wrapper `shapeW` returns `r` against
  every table answering a FINITE list of calls, each with a finite derivation),
  `shapeRuns_fuel` (`ShapeRuns → ∃ N, machineShapeF N … = some r`) and
  `shapeRuns_drive` / `shapeRuns_drive_le`: **a finite derivation of the
  wrapper ⟹ the driver eventually returns the same answer** (success or
  ordinary refusal).

## What is NOT proved (kept apart)

* The converse `machineShapeF N … = some r → ShapeRuns …` needs compactness of
  the wrapper (`Compact (shapeW …)`, as `compact_step` / `compact_normStep` for
  the block and `machNorm`); not written. The fuel-level converse IS available:
  a driver answer is the wrapper's answer at the driver's fuel (`driveShape_res`).
* O1 (outside the kernel): that a RETURNING run of the compiled `partial`
  `machineShape?` yields such a finite derivation. Hence nothing here says the
  driver answers whenever the old reader answers; it says the driver answers
  whenever a finite derivation (equivalently, some fuel) exists.
* **Production rule**: a production switch must NEVER map a final OUT of the
  bounded driver to a refusal or to the legacy route; OUT is "undecided within
  this budget" only (`driveShape_out_sound`, `driveShape_out_forever_iff`). -/
namespace Tools.ShippingReaderFuel
open Lean
open Sparkle.Compiler.Elab

/-! ## Arithmetic -/

theorem drv_le_two_pow_mul : ∀ (j n : Nat), n ≤ 2 ^ j * n
  | 0, n => Nat.le_of_eq (by rw [Nat.pow_zero, Nat.one_mul])
  | j + 1, n => by
    have ih := drv_le_two_pow_mul j n
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc, Nat.two_mul]
    exact Nat.le_trans ih (Nat.le_add_right _ _)

theorem drv_one_le_two_pow (N : Nat) : 1 ≤ 2 ^ N := by
  have h := drv_le_two_pow_mul N 1
  rw [Nat.mul_one] at h
  exact h

theorem drv_self_le_two_pow : ∀ N : Nat, N ≤ 2 ^ N
  | 0 => Nat.zero_le _
  | N + 1 => by
    have ih := drv_self_le_two_pow N
    have h1 := drv_one_le_two_pow N
    rw [Nat.pow_succ, Nat.mul_two]
    exact Nat.add_le_add ih h1

theorem drv_le_two_pow_mul_pos {N n : Nat} (hn : 0 < n) (r : Nat) (hr : N ≤ 2 ^ r) :
    N ≤ 2 ^ r * n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.mul_add, Nat.mul_one]
  exact Nat.le_trans hr (Nat.le_add_left _ _)

theorem drv_two_pow_succ_mul (r n : Nat) : 2 ^ (r + 1) * n = 2 ^ r * (2 * n) := by
  rw [Nat.pow_succ, Nat.mul_assoc]

/-! ## The generic loop -/

/-- A three-valued step whose non-OUT answers are stable under more fuel. -/
def StepStable {α : Type} (step : Nat → Option (Option α)) : Prop :=
  ∀ {n m : Nat} {o : Option α}, step n = some o → n ≤ m → step m = some o

section Loop
variable {α : Type} (step : Nat → Option (Option α))

/-- **Completion with an explicit round bound**: if fuel `N` answers `o` and
`N ≤ 2 ^ r * n`, the driver with `r` rounds from `n` answers `o`. -/
theorem driveLoop_complete_le (hs : StepStable step) {N : Nat} {o : Option α}
    (hN : step N = some o) :
    ∀ r n k, N ≤ 2 ^ r * n → (driveLoop step r n k).1 = some o
  | 0, n, k, hle => by
    rw [Nat.pow_zero, Nat.one_mul] at hle
    show step n = some o
    exact hs hN hle
  | r + 1, n, k, hle => by
    cases h : step n with
    | none =>
      rw [driveLoop_succ_out step h]
      rw [drv_two_pow_succ_mul r n] at hle
      exact driveLoop_complete_le hs hN r (2 * n) (k + 1) hle
    | some o' =>
      rw [driveLoop_succ_some step h]
      have h1 := hs h (drv_le_two_pow_mul (r + 1) n)
      have h2 := hs hN hle
      rw [h1] at h2
      exact h2

/-- **Eventual completion**: from a start fuel `n > 0`, some round bound gives
the answer of any fuel that answers. -/
theorem driveLoop_complete (hs : StepStable step) {N : Nat} {o : Option α}
    (hN : step N = some o) {n : Nat} (hn : 0 < n) (k : Nat) :
    ∃ r, (driveLoop step r n k).1 = some o :=
  ⟨N, driveLoop_complete_le step hs hN N n k
    (drv_le_two_pow_mul_pos hn N (drv_self_le_two_pow N))⟩

/-- A driver answer is an answer of the step at some fuel. -/
theorem driveLoop_sound_some {r n k : Nat} {o : Option α}
    (h : (driveLoop step r n k).1 = some o) : ∃ N, step N = some o :=
  ⟨(driveLoop step r n k).2.1, (driveLoop_res step r n k).symm.trans h⟩

theorem driveLoop_complete_iff (hs : StepStable step) {n : Nat} (hn : 0 < n) (k : Nat)
    (o : Option α) :
    (∃ r, (driveLoop step r n k).1 = some o) ↔ ∃ N, step N = some o := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := h
    exact driveLoop_sound_some step hr
  · intro h
    obtain ⟨N, hN⟩ := h
    exact driveLoop_complete step hs hN hn k

/-- OUT for every round bound ⟺ OUT at every fuel. -/
theorem driveLoop_out_forever_iff (hs : StepStable step) {n : Nat} (hn : 0 < n) (k : Nat) :
    (∀ r, (driveLoop step r n k).1 = none) ↔ ∀ N, step N = none := by
  constructor
  · intro h N
    cases hN : step N with
    | none => rfl
    | some o =>
      obtain ⟨r, hr⟩ := driveLoop_complete step hs hN hn k
      rw [h r] at hr
      cases hr
  · intro h r
    exact (driveLoop_res step r n k).trans (h _)

end Loop

/-! ## The wrapper driver -/

section Drive
variable (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo) (senv : StructEnv)
  (ai : Bool)

theorem machineShapeF_stepStable :
    StepStable (fun n => machineShapeF n sm ps ci senv ai) := by
  intro n m o h hnm
  have h' : machineShapeF n sm ps ci senv ai = some o := h
  show machineShapeF m sm ps ci senv ai = some o
  exact machineShapeF_stable (sm := sm) (ps := ps) (ci := ci) (senv := senv) (ai := ai) h' hnm

theorem drv_max_pos (start : Nat) : 0 < max start 1 := by
  first
    | exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right start 1)
    | omega

/-- **Completion of `driveShape`, explicit bound**: if fuel `N` gives `r` and
`N ≤ 2 ^ rounds`, the driver with `rounds` rounds returns `r` (any `start`). -/
theorem driveShape_complete_le {N : Nat} {r : Option MachineShape}
    (h : machineShapeF N sm ps ci senv ai = some r) (rounds start : Nat)
    (hr : N ≤ 2 ^ rounds) :
    (driveShape rounds start sm ps ci senv ai).res = some r :=
  driveLoop_complete_le (fun n => machineShapeF n sm ps ci senv ai)
    (machineShapeF_stepStable sm ps ci senv ai) h rounds (max start 1) 0
    (drv_le_two_pow_mul_pos (drv_max_pos start) rounds hr)

/-- Every round bound `rounds ≥ N` suffices. -/
theorem driveShape_complete_ge {N : Nat} {r : Option MachineShape}
    (h : machineShapeF N sm ps ci senv ai = some r) (rounds start : Nat)
    (hr : N ≤ rounds) :
    (driveShape rounds start sm ps ci senv ai).res = some r :=
  driveShape_complete_le sm ps ci senv ai h rounds start
    (Nat.le_trans hr (drv_self_le_two_pow rounds))

/-- **Eventual completion of `driveShape`**: an answer reached at some fuel
(`some s` success or `none` ordinary refusal) is the driver's answer for some
round bound — the SAME answer. -/
theorem driveShape_complete {N : Nat} {r : Option MachineShape}
    (h : machineShapeF N sm ps ci senv ai = some r) (start : Nat) :
    ∃ rounds, (driveShape rounds start sm ps ci senv ai).res = some r :=
  ⟨N, driveShape_complete_ge sm ps ci senv ai h N start (Nat.le_refl N)⟩

theorem driveShape_complete_ok {N : Nat} {s : MachineShape}
    (h : machineShapeF N sm ps ci senv ai = some (some s)) (start : Nat) :
    ∃ rounds, (driveShape rounds start sm ps ci senv ai).res = some (some s) :=
  driveShape_complete sm ps ci senv ai h start

theorem driveShape_complete_fail {N : Nat}
    (h : machineShapeF N sm ps ci senv ai = some none) (start : Nat) :
    ∃ rounds, (driveShape rounds start sm ps ci senv ai).res = some none :=
  driveShape_complete sm ps ci senv ai h start

/-- The driver eventually answers `r` ⟺ some fuel answers `r`. -/
theorem driveShape_complete_iff (start : Nat) (r : Option MachineShape) :
    (∃ rounds, (driveShape rounds start sm ps ci senv ai).res = some r) ↔
      ∃ N, machineShapeF N sm ps ci senv ai = some r := by
  constructor
  · intro h
    obtain ⟨rounds, hr⟩ := h
    exact ⟨(driveShape rounds start sm ps ci senv ai).finalFuel,
      (driveShape_res rounds start sm ps ci senv ai).symm.trans hr⟩
  · intro h
    obtain ⟨N, hN⟩ := h
    exact driveShape_complete sm ps ci senv ai hN start

/-- OUT for every round bound ⟺ OUT at every fuel: an OUT of a bounded run is
never evidence of a refusal. -/
theorem driveShape_out_forever_iff (start : Nat) :
    (∀ rounds, (driveShape rounds start sm ps ci senv ai).res = none) ↔
      ∀ N, machineShapeF N sm ps ci senv ai = none := by
  constructor
  · intro h N
    cases hN : machineShapeF N sm ps ci senv ai with
    | none => rfl
    | some o =>
      obtain ⟨rounds, hr⟩ := driveShape_complete sm ps ci senv ai hN start
      rw [h rounds] at hr
      cases hr
  · intro h rounds
    exact (driveShape_res rounds start sm ps ci senv ai).trans (h _)

end Drive

/-! ## Finite derivations of the wrapper (link with `…FuelEval`) -/

/-- Finite execution of one wrapper call: `machNorm` by `EvalN`, a block call
by `Eval`. -/
def WEval (senv : StructEnv) : (c : WCall) → WCall.Res c → Prop
  | .norm e, r => EvalN senv e r
  | .blk c, r => Eval senv c r

theorem wEval_fuel {senv : StructEnv} (c : WCall) (r : WCall.Res c) (h : WEval senv c r) :
    ∃ n, wtab senv n c = some r := by
  cases c with
  | norm e =>
    have h' : EvalN senv e r := h
    obtain ⟨n, hn⟩ := evalN_fuel h'
    exact ⟨n, hn⟩
  | blk c =>
    have h' : Eval senv c r := h
    obtain ⟨n, hn⟩ := eval_fuel h'
    exact ⟨n, hn⟩

/-- Finitely many executed wrapper calls are all answered at one fuel. -/
theorem wext_fuel_of (senv : StructEnv) :
    ∀ L : List (Sigma WCall.Res), (∀ p, p ∈ L → WEval senv p.1 p.2) →
      ∃ N, Ext (wtab senv N) L := by
  intro L
  induction L with
  | nil => intro _; exact ⟨0, ext_nil _⟩
  | cons q L ih =>
    intro hL
    obtain ⟨n, hn⟩ := wEval_fuel q.1 q.2 (hL q (List.mem_cons.mpr (Or.inl rfl)))
    obtain ⟨N, hN⟩ := ih (fun p hp => hL p (List.mem_cons.mpr (Or.inr hp)))
    refine ⟨n + N, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact wtab_mono senv (Nat.le_add_right n N) _ _ hn
    · exact wtab_mono senv (Nat.le_add_left N n) _ _ (hN p hp)

/-- **A finite execution of the wrapper**: finitely many calls (`machNorm` or
block), each with a finite derivation, and the wrapper `shapeW` returns `r`
against every table answering at least those. `r = some s`: success;
`r = none`: ordinary refusal. -/
def ShapeRuns (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo) (senv : StructEnv)
    (ai : Bool) (r : Option MachineShape) : Prop :=
  ∃ L : List (Sigma WCall.Res), (∀ p, p ∈ L → WEval senv p.1 p.2) ∧
    ∀ h : (c : WCall) → Option (WCall.Res c), Ext h L → (shapeW sm ps ci senv ai).run h = some r

section Runs
variable {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo} {senv : StructEnv}
  {ai : Bool}

/-- A finite execution of the wrapper is reached at some fuel. -/
theorem shapeRuns_fuel {r : Option MachineShape} (h : ShapeRuns sm ps ci senv ai r) :
    ∃ N, machineShapeF N sm ps ci senv ai = some r := by
  obtain ⟨L, s, k⟩ := h
  obtain ⟨N, hN⟩ := wext_fuel_of senv L s
  exact ⟨N, k (wtab senv N) hN⟩

/-- **Finite derivation ⟹ the driver eventually returns the same answer.** -/
theorem shapeRuns_drive {r : Option MachineShape} (h : ShapeRuns sm ps ci senv ai r)
    (start : Nat) : ∃ rounds, (driveShape rounds start sm ps ci senv ai).res = some r := by
  obtain ⟨N, hN⟩ := shapeRuns_fuel h
  exact driveShape_complete sm ps ci senv ai hN start

/-- The same, for every sufficiently large round bound. -/
theorem shapeRuns_drive_le {r : Option MachineShape} (h : ShapeRuns sm ps ci senv ai r) :
    ∃ N, ∀ rounds start, N ≤ rounds →
      (driveShape rounds start sm ps ci senv ai).res = some r := by
  obtain ⟨N, hN⟩ := shapeRuns_fuel h
  exact ⟨N, fun rounds start hr => driveShape_complete_ge sm ps ci senv ai hN rounds start hr⟩

end Runs

end Tools.ShippingReaderFuel
