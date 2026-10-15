import Tools.ShippingReaderFuelShape

/-! # The doubling driver of the fuel wrapper `machineShapeF`

WRITTEN, NOT BUILT (worker F, branch `par/r-9`; record
`docs/parallel/R-reader-fuel-driver.md`). No `sorry`, no axiom, no
`native_decide`. NOT used by the compiler: production still calls the
`partial` reader `machineShape?` (nothing under `Sparkle/` changed).

## Which driver, and why it never returns FAIL for OUT

`driveLoop` is a **fuel-bounded total `def`** (structural on the number of
rounds), not a `partial def`: it can carry theorems. From a start fuel
`max start 1 > 0` (fuel `0` is always OUT once the prefix passes,
`machineShapeF_zero`) it runs the wrapper; on OUT, and ONLY on OUT, it doubles
the fuel and retries; FAIL and OK stop at once. When its own round bound is
used up it returns the last answer AS IT IS — OUT stays OUT
(`driveShape_out_sound`), never FAIL, never "legacy".

The returned answer is BY CONSTRUCTION the wrapper's answer at the returned
fuel (`driveShape_res`): there is no line of the driver that produces
`some none` itself. Hence FAIL from the driver is a genuine refusal —
stable for every larger fuel, and no fuel at all gives OK
(`driveShape_fail_sound`); OK is stable for every larger fuel
(`driveShape_ok_stable`) and no fuel FAILs (`driveShape_ok_sound`).

`Nat` is unbounded: `2 * n` never overflows. With `defaultRounds = 64` a
final OUT means the readers did not finish within recursion depth
`2^64 · start`, i.e. the real `partial` reader would not have returned either
(modulo the open coverage question O1 of `R-reader-fuel.md`). -/
namespace Tools.ShippingReaderFuel
open Lean
open Sparkle.Compiler.Elab

/-- `OUT` / `FAIL` / `OK`. -/
def resClass {α : Type} : Option (Option α) → String
  | none => "OUT"
  | some none => "FAIL"
  | some (some _) => "OK"

/-- The doubling loop over any three-valued `step`: `(answer, final fuel,
doublings)`. Retries (fuel `2 * n`) on OUT only. -/
def driveLoop {α : Type} (step : Nat → Option (Option α)) :
    (rounds : Nat) → (n : Nat) → (k : Nat) → Option (Option α) × Nat × Nat
  | 0, n, k => (step n, n, k)
  | r + 1, n, k =>
    match step n with
    | none => driveLoop step r (2 * n) (k + 1)
    | some o => (some o, n, k)

section Loop
variable {α : Type} (step : Nat → Option (Option α))

theorem driveLoop_succ_out {r n k : Nat} (h : step n = none) :
    driveLoop step (r + 1) n k = driveLoop step r (2 * n) (k + 1) := by
  simp only [driveLoop, h]

theorem driveLoop_succ_some {r n k : Nat} {o : Option α} (h : step n = some o) :
    driveLoop step (r + 1) n k = (some o, n, k) := by
  simp only [driveLoop, h]

/-- **The answer is the step's answer at the returned fuel.** -/
theorem driveLoop_res : ∀ r n k,
    (driveLoop step r n k).1 = step (driveLoop step r n k).2.1
  | 0, n, k => rfl
  | r + 1, n, k => by
    cases h : step n with
    | none =>
      rw [driveLoop_succ_out step h]
      exact driveLoop_res r (2 * n) (k + 1)
    | some o =>
      rw [driveLoop_succ_some step h]
      exact h.symm

/-- The returned fuel is the start fuel doubled `j` times, `j` the number of
doublings, at most the round bound. -/
theorem driveLoop_fuel : ∀ r n k, ∃ j, j ≤ r ∧
    (driveLoop step r n k).2.1 = 2 ^ j * n ∧ (driveLoop step r n k).2.2 = k + j
  | 0, n, k => ⟨0, Nat.le_refl 0, by simp [driveLoop], rfl⟩
  | r + 1, n, k => by
    cases h : step n with
    | none =>
      obtain ⟨j, hj, hf, hd⟩ := driveLoop_fuel r (2 * n) (k + 1)
      refine ⟨j + 1, Nat.succ_le_succ hj, ?_, ?_⟩
      · rw [driveLoop_succ_out step h, hf]
        first
          | (rw [Nat.pow_succ, Nat.mul_assoc]; done)
          | simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      · rw [driveLoop_succ_out step h, hd]
        all_goals omega
    | some o =>
      refine ⟨0, Nat.zero_le _, ?_, ?_⟩
      · simp [driveLoop_succ_some step h]
      · simp [driveLoop_succ_some step h]

/-- An OUT answer used up every round. -/
theorem driveLoop_out_rounds : ∀ r n k,
    (driveLoop step r n k).1 = none → (driveLoop step r n k).2.2 = k + r
  | 0, n, k, _ => rfl
  | r + 1, n, k, hres => by
    cases h : step n with
    | none =>
      rw [driveLoop_succ_out step h] at hres ⊢
      have := driveLoop_out_rounds r (2 * n) (k + 1) hres
      omega
    | some o =>
      rw [driveLoop_succ_some step h] at hres
      simp at hres

end Loop

/-- What the driver returns. -/
structure DriveResult where
  res : Option (Option MachineShape)
  finalFuel : Nat
  doublings : Nat

/-- The default round bound. -/
def defaultRounds : Nat := 64

/-- **The doubling driver**: start at `max start 1`, double on OUT only, at
most `rounds` times. -/
def driveShape (rounds start : Nat) (symbolicMode : Bool) (parameters : List (String × Nat))
    (ci : ConstantInfo) (senv : StructEnv) (allowInsts : Bool := true) : DriveResult :=
  let r := driveLoop (fun n => machineShapeF n symbolicMode parameters ci senv allowInsts)
    rounds (max start 1) 0
  { res := r.1, finalFuel := r.2.1, doublings := r.2.2 }

section Drive
variable (rounds start : Nat) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo)
  (senv : StructEnv) (ai : Bool)

/-- **The driver's answer is the wrapper's answer at the driver's fuel** —
the driver never makes up an answer (in particular never FAIL for OUT). -/
theorem driveShape_res :
    (driveShape rounds start sm ps ci senv ai).res =
      machineShapeF (driveShape rounds start sm ps ci senv ai).finalFuel sm ps ci senv ai :=
  driveLoop_res (fun n => machineShapeF n sm ps ci senv ai) rounds (max start 1) 0

/-- The driver's fuel: `2 ^ doublings * max start 1`, at most `rounds`
doublings. -/
theorem driveShape_fuel :
    (driveShape rounds start sm ps ci senv ai).finalFuel =
        2 ^ (driveShape rounds start sm ps ci senv ai).doublings * max start 1 ∧
      (driveShape rounds start sm ps ci senv ai).doublings ≤ rounds := by
  obtain ⟨j, hj, hf, hd⟩ :=
    driveLoop_fuel (fun n => machineShapeF n sm ps ci senv ai) rounds (max start 1) 0
  have hd' : (driveShape rounds start sm ps ci senv ai).doublings = j := by
    show (driveLoop (fun n => machineShapeF n sm ps ci senv ai) rounds (max start 1) 0).2.2 = j
    rw [hd]
    all_goals omega
  refine ⟨?_, ?_⟩
  · rw [hd']
    exact hf
  · rw [hd']
    exact hj

/-- OK is stable for every larger fuel. -/
theorem driveShape_ok_stable {s : MachineShape}
    (h : (driveShape rounds start sm ps ci senv ai).res = some (some s)) {m : Nat}
    (hm : (driveShape rounds start sm ps ci senv ai).finalFuel ≤ m) :
    machineShapeF m sm ps ci senv ai = some (some s) := by
  rw [driveShape_res rounds start sm ps ci senv ai] at h
  exact machineShapeF_stable h hm

/-- OK: no fuel FAILs (every non-OUT answer is this one). -/
theorem driveShape_ok_sound {s : MachineShape}
    (h : (driveShape rounds start sm ps ci senv ai).res = some (some s)) (m : Nat) :
    machineShapeF m sm ps ci senv ai = none ∨
      machineShapeF m sm ps ci senv ai = some (some s) := by
  rw [driveShape_res rounds start sm ps ci senv ai] at h
  cases hm : machineShapeF m sm ps ci senv ai with
  | none => exact Or.inl rfl
  | some o =>
    right
    rw [machineShapeF_det hm h]

/-- FAIL is a genuine refusal: no fuel gives OK, and every larger fuel FAILs. -/
theorem driveShape_fail_sound
    (h : (driveShape rounds start sm ps ci senv ai).res = some none) (m : Nat) :
    machineShapeF m sm ps ci senv ai = none ∨ machineShapeF m sm ps ci senv ai = some none := by
  rw [driveShape_res rounds start sm ps ci senv ai] at h
  cases hm : machineShapeF m sm ps ci senv ai with
  | none => exact Or.inl rfl
  | some o =>
    right
    rw [machineShapeF_det hm h]

theorem driveShape_fail_stable
    (h : (driveShape rounds start sm ps ci senv ai).res = some none) {m : Nat}
    (hm : (driveShape rounds start sm ps ci senv ai).finalFuel ≤ m) :
    machineShapeF m sm ps ci senv ai = some none := by
  rw [driveShape_res rounds start sm ps ci senv ai] at h
  exact machineShapeF_stable h hm

/-- **OUT stays OUT**: every fuel up to the driver's last one is OUT, and the
driver used up all its rounds (it did not stop early on a bound by turning
OUT into FAIL). -/
theorem driveShape_out_sound
    (h : (driveShape rounds start sm ps ci senv ai).res = none) :
    (driveShape rounds start sm ps ci senv ai).doublings = rounds ∧
      ∀ m, m ≤ (driveShape rounds start sm ps ci senv ai).finalFuel →
        machineShapeF m sm ps ci senv ai = none := by
  refine ⟨?_, ?_⟩
  · have := driveLoop_out_rounds (fun n => machineShapeF n sm ps ci senv ai) rounds
      (max start 1) 0 h
    show (driveLoop (fun n => machineShapeF n sm ps ci senv ai) rounds (max start 1) 0).2.2 =
      rounds
    rw [this]
    all_goals omega
  · intro m hm
    rw [driveShape_res rounds start sm ps ci senv ai] at h
    exact machineShapeF_out_le h hm

end Drive

end Tools.ShippingReaderFuel
