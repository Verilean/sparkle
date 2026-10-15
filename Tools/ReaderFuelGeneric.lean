/-! # Fuel semantics of a recursive reader — the generic part (worker B, R-4)

UNVERIFIED: written without running `lean` / `lake` (worker rule). Core only
(no import), no `sorry`, no axiom, no `native_decide`. Not registered in
`lakefile.lean`; the integrator builds it on its own.

Context: `docs/parallel/R-reader-coverage.md`. The compiler's machine reader
(`machNorm`, and the seven-function `mutual` block `machConv` … `machLoopRoot`
of `Sparkle/Compiler/Elab.lean`) is `partial`: seven/eight `opaque` constants
with no equation in the kernel. A total candidate is the fuel iteration of the
SAME body, `iter B n`, with a three-valued result:

* `.ok r`  — the old reader's `some r`;
* `.fail`  — the old reader's `none` (a refusal: legacy route as today);
* `.out`   — fuel exhausted. NEVER a refusal: the driver retries with more
  fuel (or stops with a hard error); it never maps `.out` to `none`/legacy.

This file proves, for ANY body `B` that is monotone (`Mono`, "`.out` is
absorbing and a probe's `.out` is not read as a failure"):

1. `iter_mono` / `iter_det`  — the answer does not depend on the fuel once it
   is not `.out` (the certificate is just the number `n`);
2. `iter_le_fix`, `agree_ok`, `agree_fail` — SOUNDNESS against the old
   reader, under the hypothesis that the old reader is a fixpoint of `B`
   (its own source equation). That hypothesis is about `opaque` constants:
   it stays OUTSIDE the kernel (a `Prop`, never an axiom);
3. `fixpoint_not_complete` — the converse (old `some r` ⟹ some fuel gives
   `.ok r`) does NOT follow from the source equation: a fixpoint need not be
   the least one. Coverage is a separate obligation;
4. `iter_total` — the converse DOES hold for every input when a measure `μ`
   guards `B` (option (i) of the ruling): fuel `μ x + 1` never runs out.
-/

namespace Tools.ReaderFuelGeneric

/-- The result of a fuel-bounded reader call. -/
inductive Fu (α : Type) where
  | ok (a : α)
  | fail
  | out

/-- The information order: `.out` below everything, otherwise equality. -/
inductive Fu.Le {α : Type} : Fu α → Fu α → Prop
  | out (b : Fu α) : Fu.Le .out b
  | refl (a : Fu α) : Fu.Le a a

theorem Fu.Le.eq_of_ne {α : Type} {a b : Fu α} (h : Fu.Le a b) (ha : a ≠ .out) : a = b := by
  cases h with
  | out => exact absurd rfl ha
  | refl => rfl

/-- The old reader's `Option` result as a `Fu` (never `.out`). -/
def ofOpt {α : Type} : Option α → Fu α
  | some a => .ok a
  | none => .fail

theorem ofOpt_eq_ok {α : Type} {o : Option α} {a : α} (h : ofOpt o = .ok a) : o = some a := by
  cases o with
  | none => change Fu.fail = Fu.ok a at h; cases h
  | some b => change Fu.ok b = Fu.ok a at h; cases h; rfl

theorem ofOpt_eq_fail {α : Type} {o : Option α} (h : ofOpt o = .fail) : o = none := by
  cases o with
  | none => rfl
  | some b => change Fu.ok b = Fu.fail at h; cases h

/-- Sequencing with `.fail` and `.out` absorbing (the `Option` bind of the old
reader, with `.out` passed through unchanged). -/
def Fu.bind {α β : Type} : Fu α → (α → Fu β) → Fu β
  | .ok a, k => k a
  | .fail, _ => .fail
  | .out, _ => .out

/-- The building block of `Mono` for a body written with `Fu.bind`: every arm
that only binds recursive results is monotone. (A probe that reads `.fail` of
a recursive call as "try the next candidate" is monotone too, provided it
passes `.out` through; reading `.out` as `.fail` is NOT.) -/
theorem Fu.bind_le {α β : Type} {x x' : Fu α} {k k' : α → Fu β}
    (hx : Fu.Le x x') (hk : ∀ a, Fu.Le (k a) (k' a)) : Fu.Le (x.bind k) (x'.bind k') := by
  cases hx with
  | out => exact Fu.Le.out _
  | refl =>
    cases x with
    | ok a => exact hk a
    | fail => exact Fu.Le.refl _
    | out => exact Fu.Le.out _

/-- A body: one unfolding of the reader, its recursive calls through `g`.
The mutual block is one body over the sum `ι` of the seven argument tuples. -/
abbrev Body (ι : Type) (R : ι → Type) : Type :=
  ((x : ι) → Fu (R x)) → (x : ι) → Fu (R x)

section
variable {ι : Type} {R : ι → Type}

/-- The fuel iteration: `n` nested unfoldings, `.out` below the last. -/
def iter (B : Body ι R) : Nat → (x : ι) → Fu (R x)
  | 0 => fun _ => .out
  | n + 1 => B (iter B n)

theorem iter_zero (B : Body ι R) (x : ι) : iter B 0 x = .out := rfl

theorem iter_succ (B : Body ι R) (n : Nat) (x : ι) : iter B (n + 1) x = B (iter B n) x := rfl

/-- Monotone body: more defined recursive answers give a more defined answer.
This is the kernel-checkable form of "`.out` is absorbing everywhere and no
`.out` of a recursive call (a sharing probe included) is treated as a
refusal". -/
def Mono (B : Body ι R) : Prop :=
  ∀ g h : (x : ι) → Fu (R x), (∀ x, Fu.Le (g x) (h x)) → ∀ x, Fu.Le (B g x) (B h x)

theorem iter_le_add (B : Body ι R) (hB : Mono B) :
    ∀ (n k : Nat) (x : ι), Fu.Le (iter B n x) (iter B (n + k) x)
  | 0, _, x => by rw [iter_zero]; exact Fu.Le.out _
  | n + 1, k, x => by
    have e : n + 1 + k = (n + k) + 1 := by omega
    rw [e, iter_succ, iter_succ]
    exact hB _ _ (fun y => iter_le_add B hB n k y) x

theorem iter_mono (B : Body ι R) (hB : Mono B) {n m : Nat} (h : n ≤ m) (x : ι) :
    Fu.Le (iter B n x) (iter B m x) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact iter_le_add B hB n k x

/-- Fuel independence: two fuels that both finish give the same answer. -/
theorem iter_det (B : Body ι R) (hB : Mono B) {n m : Nat} {x : ι}
    (hn : iter B n x ≠ .out) (hm : iter B m x ≠ .out) : iter B n x = iter B m x := by
  rcases Nat.le_total n m with h | h
  · exact (iter_mono B hB h x).eq_of_ne hn
  · exact ((iter_mono B hB h x).eq_of_ne hm).symm

/-- The old reader `f` satisfies its own source equation (written through `B`).
For the compiler's `partial def`s this is a statement about `opaque`
constants: neither provable nor refutable in the kernel. A DEFINITION, used
only as a hypothesis. -/
def IsFix (B : Body ι R) (f : (x : ι) → Option (R x)) : Prop :=
  ∀ x, ofOpt (f x) = B (fun y => ofOpt (f y)) x

/-- Every fuel iteration is below every fixpoint. -/
theorem iter_le_fix (B : Body ι R) (hB : Mono B) (f : (x : ι) → Option (R x))
    (hfix : IsFix B f) : ∀ (n : Nat) (x : ι), Fu.Le (iter B n x) (ofOpt (f x))
  | 0, x => by rw [iter_zero]; exact Fu.Le.out _
  | n + 1, x => by
    rw [iter_succ, hfix x]
    exact hB _ _ (fun y => iter_le_fix B hB f hfix n y) x

/-- Soundness, success: a finished fuel run agrees with the old reader. -/
theorem agree_ok (B : Body ι R) (hB : Mono B) (f : (x : ι) → Option (R x))
    (hfix : IsFix B f) {n : Nat} {x : ι} {r : R x} (h : iter B n x = .ok r) :
    f x = some r := by
  have hle := iter_le_fix B hB f hfix n x
  rw [h] at hle
  have e := hle.eq_of_ne (by intro h'; cases h')
  exact ofOpt_eq_ok e.symm

/-- Soundness, refusal. -/
theorem agree_fail (B : Body ι R) (hB : Mono B) (f : (x : ι) → Option (R x))
    (hfix : IsFix B f) {n : Nat} {x : ι} (h : iter B n x = .fail) : f x = none := by
  have hle := iter_le_fix B hB f hfix n x
  rw [h] at hle
  have e := hle.eq_of_ne (by intro h'; cases h')
  exact ofOpt_eq_fail e.symm

/-- Option (i): `μ` guards `B` — whenever every call at a smaller measure has
finished, the body finishes. -/
def Guarded (μ : ι → Nat) (B : Body ι R) : Prop :=
  ∀ (g : (x : ι) → Fu (R x)) (x : ι), (∀ y, μ y < μ x → g y ≠ .out) → B g x ≠ .out

/-- Under a guarding measure the fuel `μ x + 1` always finishes, so with
`agree_ok`/`agree_fail` the total version decides EVERY input exactly as any
fixpoint (the old reader included) does. -/
theorem iter_total (B : Body ι R) (hB : Mono B) (μ : ι → Nat) (hg : Guarded μ B) :
    ∀ x, iter B (μ x + 1) x ≠ .out := by
  have key : ∀ (k : Nat) (x : ι), μ x < k → iter B (μ x + 1) x ≠ .out := by
    intro k
    induction k with
    | zero => intro x hx; exact absurd hx (Nat.not_lt_zero _)
    | succ k ih =>
      intro x hx
      rw [iter_succ]
      refine hg _ x ?_
      intro y hy
      have h1 : iter B (μ y + 1) y ≠ .out := ih y (by omega)
      have h2 : Fu.Le (iter B (μ y + 1) y) (iter B (μ x) y) := iter_mono B hB (by omega) y
      intro h
      exact h1 ((h2.eq_of_ne h1).trans h)
  intro x
  exact key (μ x + 1) x (Nat.lt_succ_self _)

end

/-- The source equation alone does not give coverage: the body "call yourself"
is monotone, `fun _ => some ()` is a fixpoint of it, yet no fuel finishes.
(The compiled `partial` code computes the LEAST fixpoint on the inputs where
it terminates; that fact is about the compiled code, not the kernel.) -/
theorem fixpoint_not_complete :
    ∃ (B : Body Unit (fun _ => Unit)) (f : (x : Unit) → Option Unit),
      Mono B ∧ IsFix B f ∧ f () = some () ∧ ∀ n, iter B n () ≠ .ok () := by
  refine ⟨fun g => g, fun _ => some (), ?_, ?_, rfl, ?_⟩
  · unfold Mono
    intro g h hgh x
    exact hgh x
  · unfold IsFix
    intro x
    rfl
  · intro n
    induction n with
    | zero => intro h; rw [iter_zero] at h; cases h
    | succ n ih => rw [iter_succ]; exact ih

end Tools.ReaderFuelGeneric
