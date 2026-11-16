import Tools.VedU1Contract

/-!
# Kernel-cheap name tests for the statement's decidable parts (`sparkle-ved-packed-seq4`)

The kernel compares two `String` literals by unfolding `String.decEq` (both literals become `String.mk` lists of
`Char.ofNat n`): measured on R23 (323 statements) about 1.6·10^3 heartbeats (0.7 ms) PER COMPARE.  `OrderOk` (`woCheck`,
`isPermOf`, the `contains` tests) and the `Nodup` of the wire names compare every name with every other: 519 M heartbeats
(236 s) for the `OrderOk` of R23 alone.

`skey s` is a natural number computed from the characters (equal strings have equal keys: no injectivity is needed), and
`containsK l n` tests `skey x == skey n` (a literal comparison the kernel does by GMP) before the string comparison:
`containsK l n = l.contains n` for every `l`, `n`.  `woCheckK`, `isPermOfK`, `nodupK`, `OrderOkK` are the definitions of
`Sparkle.IR.woCheck`, `isPermOf`, `List.Nodup` (as a `Bool`), `Tools.VedU1Contract.OrderOk` with every membership test
replaced by that one, and are proved equal to them; the statement is unchanged (the entry proves `OrderOk m b = true` by
`OrderOk_eq_K` and a kernel evaluation of `OrderOkK m b`).
-/

namespace Tools.VedU1PackedSeq4

open Sparkle.IR.AST Sparkle.IR.Reorder Tools.VedU1Contract

/-- a natural number computed from the characters of a string (equal strings, equal keys) -/
def skey (s : String) : Nat :=
  s.data.foldl (fun h c => (h * 1000003 + c.val.toNat + 1) % 2305843009213693951) 7

/-- `l.contains n` with the key test before the string comparison -/
def containsK (l : List String) (n : String) : Bool :=
  l.any fun x => skey x == skey n && x == n

theorem containsK_eq (l : List String) (n : String) : containsK l n = l.contains n := by
  unfold containsK
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.any_cons, List.contains_cons, ih]
    cases hx : (x == n) with
    | true =>
      have e : x = n := eq_of_beq hx
      subst e
      simp
    | false =>
      have e : (n == x) = false := by
        cases h2 : (n == x)
        · rfl
        · have := eq_of_beq h2
          subst this
          simp at hx
      simp [hx, e]

/-- `List.Nodup` as a `Bool` -/
def nodupK : List String → Bool
  | [] => true
  | x :: xs => !containsK xs x && nodupK xs

theorem nodupK_iff (l : List String) : nodupK l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [nodupK]
  | cons x xs ih =>
    simp only [nodupK, Bool.and_eq_true, Bool.not_eq_true', containsK_eq, List.nodup_cons, ih]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun hm => by simp [List.contains_iff_mem] at h1; exact h1 hm, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by simpa [List.contains_iff_mem] using h1, h2⟩

theorem decide_nodup_eq (l : List String) : decide l.Nodup = nodupK l := by
  by_cases h : l.Nodup
  · simp [h, (nodupK_iff l).2 h]
  · have : nodupK l ≠ true := fun h' => h ((nodupK_iff l).1 h')
    simp [h, this]

/-- `woCheck` (`Sparkle.IR.ReorderInvariance`) with `containsK` -/
def woCheckK (done : List String) : List Stmt → Bool
  | [] => true
  | s :: rest =>
    (stmtReads s).all (fun n => !containsK (writesOf rest) n)
    && (stmtWrites s).all (fun n => !containsK done n && !containsK (writesOf rest) n)
    && woCheckK (done ++ stmtWrites s) rest

theorem woCheckK_eq (done : List String) (body : List Stmt) : woCheckK done body = woCheck done body := by
  induction body generalizing done with
  | nil => rfl
  | cons s rest ih => simp only [woCheckK, woCheck, containsK_eq, ih]

section Perm
variable {α : Type} [DecidableEq α]

/-- `a ∈ l` with a key test before the comparison -/
def memKg (key : α → Nat) (a : α) (l : List α) : Bool := l.any fun x => key x == key a && decide (x = a)

def eraseKg (key : α → Nat) : List α → α → List α
  | [], _ => []
  | x :: xs, a => if key x == key a && decide (x = a) then xs else x :: eraseKg key xs a

theorem memKg_eq (key : α → Nat) (a : α) (l : List α) : memKg key a l = decide (a ∈ l) := by
  unfold memKg
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.any_cons, ih]
    by_cases h : x = a
    · subst h; simp
    · have h' : ¬ a = x := fun e => h e.symm
      simp [h, h']

theorem eraseKg_eq (key : α → Nat) (l : List α) (a : α) : eraseKg key l a = l.erase a := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    unfold eraseKg
    rw [List.erase_cons]
    by_cases h : x = a
    · subst h; simp
    · simp [h, ih]

def isPermOfKg (key : α → Nat) : List α → List α → Bool
  | [], [] => true
  | [], _ :: _ => false
  | a :: rest, l => if memKg key a l then isPermOfKg key rest (eraseKg key l a) else false

theorem isPermOfKg_eq (key : α → Nat) (l₁ l₂ : List α) : isPermOfKg key l₁ l₂ = isPermOf l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> rfl
  | cons a rest ih => simp [isPermOfKg, isPermOf, memKg_eq, eraseKg_eq, ih]

end Perm

/-- a key of a statement (equal statements, equal keys) -/
def stmtKey : Stmt → Nat
  | .assign l _ => skey l
  | .register o .. => skey o
  | _ => 0

/-- `OrderOk` with the key-tested name lookups -/
def OrderOkK (m : Module) (b : List Stmt) : Bool :=
  isPermOfKg stmtKey b m.body && woCheckK [] b &&
  nodupK (nextKeys b) && decide (b.filterMap stmtMemName).Nodup &&
  b.all (fun s => (stmtReads s).all (fun n => !containsK (stmtWrites s) n)) &&
  b.all (fun s => (allReads s).all (fun n =>
    containsK (m.inputs.map (·.name)) n || containsK ((regsOf b).map (·.1)) n ||
      containsK (writesOf b) n)) &&
  m.outputs.all (fun p => containsK ((regsOf b).map (·.1)) p.name || containsK (writesOf b) p.name) &&
  (writesOf b).all (fun n => !containsK (m.inputs.map (·.name)) n && !containsK ((regsOf b).map (·.1)) n) &&
  ((regsOf b).map (·.1)).all (fun n => !containsK (m.inputs.map (·.name)) n)

theorem OrderOk_eq_K (m : Module) (b : List Stmt) : OrderOkK m b = OrderOk m b := by
  simp only [OrderOkK, OrderOk, isPermOfKg_eq, woCheckK_eq, containsK_eq, decide_nodup_eq]

end Tools.VedU1PackedSeq4
