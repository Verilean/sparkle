/-!
# Bool-fold decision of `∀ x < n, P x` for the input-domain enumeration

`Nat.decidableBallLT` builds a proof-carrying instance whose kernel evaluation holds every
step in memory: `decide +kernel` on a 16-bit input domain exceeds 14 GB (R90 `MIL1553HWTest`,
R108, R148).  `chkAll` folds a Bool predicate with an accumulator index instead; the scoped
instance `ballLtDec` is `decidable_of_iff` of that fold, proved sound AND complete below, so the
kernel still evaluates the original proposition's decision and no new axiom is involved.
Untrusted like the script: the kernel checks every use.
-/
namespace Tools.VedInvocationDom

def chkAll (P : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => P i && chkAll P n (i+1)

theorem chkAll_sound (P : Nat → Bool) :
    ∀ (n i : Nat), chkAll P n i = true → ∀ x, i ≤ x → x < i + n → P x = true
  | 0, i, _, x, h1, h2 => by omega
  | n+1, i, h, x, h1, h2 => by
    simp only [chkAll, Bool.and_eq_true] at h
    by_cases hx : x = i
    · subst hx; exact h.1
    · exact chkAll_sound P n (i+1) h.2 x (by omega) (by omega)

theorem chkAll_complete (P : Nat → Bool) :
    ∀ (n i : Nat), (∀ x, i ≤ x → x < i + n → P x = true) → chkAll P n i = true
  | 0, i, _ => rfl
  | n+1, i, h => by
    simp only [chkAll, Bool.and_eq_true]
    exact ⟨h i (Nat.le_refl _) (by omega),
      chkAll_complete P n (i+1) (fun x h1 h2 => h x (by omega) (by omega))⟩

/-- `∀ x < n, P x`, decided by the Bool fold (scoped: only where this namespace is opened). -/
scoped instance (priority := high) ballLtDec (n : Nat) (P : Nat → Prop) [DecidablePred P] :
    Decidable (∀ x, x < n → P x) :=
  decidable_of_iff (chkAll (fun x => decide (P x)) n 0 = true)
    ⟨fun h x hx => of_decide_eq_true (chkAll_sound _ n 0 h x (Nat.zero_le _) (by omega)),
     fun h => chkAll_complete _ n 0 (fun x _ hx => decide_eq_true (h x (by omega)))⟩

/-- the domain `[0, K*S)` as `K` chunks of `S` (each chunk closed by its own `decide +kernel`,
so the kernel's per-declaration caches stay small). -/
theorem chunks (S K : Nat) (P : Nat → Prop) (h : ∀ c, c < K → ∀ x, x < S → P (c * S + x)) :
    ∀ x, x < K * S → P x := by
  intro x hx
  have hS : 0 < S := by
    cases S with
    | zero => simp at hx
    | succ _ => omega
  have hc : x / S < K := (Nat.div_lt_iff_lt_mul hS).2 hx
  have := h (x / S) hc (x % S) (Nat.mod_lt _ hS)
  rwa [Nat.mul_comm, Nat.div_add_mod] at this

theorem allLt_zero (Q : Nat → Prop) : ∀ c, c < 0 → Q c := fun _ h => absurd h (Nat.not_lt_zero _)

theorem allLt_succ (Q : Nat → Prop) (n : Nat) (h : ∀ c, c < n → Q c) (hn : Q n) :
    ∀ c, c < n + 1 → Q c := fun c hc => by
  by_cases e : c = n
  · subst e; exact hn
  · exact h c (by omega)

end Tools.VedInvocationDom
