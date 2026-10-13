import Sparkle.IR.RefineCheck
import Std.Data.HashMap.Lemmas

/-! # The merge keeps a non-assignment statement — the pure part (round par/a-30)

`Sparkle.IR.RegDedup.mergeDuplicatesParts` (`Sparkle/IR/RegDedup.lean`
234–293) rewrites a statement that defines a node `n` with
`subst.get? n = some r` into `assign n (ref r)` — WHATEVER its kind (287–290).
So `m.body.all isAssign = false → (merge m).body.all isAssign = false` is
false in general (`mergeCex`, `docs/parallel/A-leaf-entry-2.md` §1).

The true statement, with the hypothesis this file names:

    LastNonAssign body :=
      ∃ pre st post, body = pre ++ st :: post ∧ isAssign st = false ∧
        ∀ l r, Stmt.assign l r ∈ post → definedNode st ≠ some l

"some non-assignment statement is not FOLLOWED by an assignment to the name
it defines". It is weaker than distinct defined names
(`lastNonAssign_of_nodup`).

Why it is the right one — the merge, as read:

* classes are keyed by NAME (`cls : HashMap String Nat`); a refinement round
  ends with `next.insert n k` per node (257), so for a name defined more than
  once the LAST statement decides the class;
* `k` is the id of the statement's signature (`sigOf`, 79–88), and the
  signature starts with `{self}|A|`, `{self}|R|`, `{self}|M|` or `{self}|?`:
  the character after the first `|` is `A` exactly for an assignment
  (`isA_sig`; `self` is a number, it has no `|`);
* the loop over `[0:nodes.length + 1]` runs at least once and each pass
  ends with `cls := next` (259, before the `break`): the final `cls` is the
  result of ONE round over some previous class map (`IsRound`);
* `rep[k]` is the first node of class `k` in body order (273–275), and a
  name is put into `subst` only when its class's representative is another
  name (281–283): a representative is never in `subst`.

So: let `n` be the name `st` defines. The last statement defining `n` is a
non-assignment (it is `st` or a later one, and no later one is an
assignment). Its class's representative `n'` has the same signature id, so
the last statement defining `n'` is a non-assignment too; `n'` is not in
`subst`; that statement is kept (`mapStmtExprs` keeps the kind).
A non-assignment that defines no node (an instance, a multi-port memory) is
kept by 291–292 without any of this.

THIS FILE is the part that does not look at the `do` block: the loops as
structural recursions (`innerRec`, `outerRec`, `repRec`, `substRec`), their
invariants, and `partsRec_keeps`. That `mergeDuplicatesParts` IS these
recursions is `Tools/ShippingMergeKeepsBridge.lean`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingMergeKeeps
open Sparkle.IR.AST Std
open Sparkle.IR.RegDedup (definedNode sigOf isAssign)

/-! ## 1. Signatures: the character after the first `|` -/

/-- What follows the first `|`. -/
def afterBar : List Char → List Char
  | [] => []
  | c :: cs => if c = '|' then cs else afterBar cs

theorem afterBar_append : ∀ (l : List Char), (∀ c ∈ l, c ≠ '|') → ∀ r : List Char,
    afterBar (l ++ '|' :: r) = r
  | [], _, r => by
    show (if ('|' : Char) = '|' then r else afterBar r) = r
    exact if_pos rfl
  | c :: cs, h, r => by
    have hc : ¬ (c = '|') := h c (List.mem_cons_self ..)
    show (if c = '|' then cs ++ '|' :: r else afterBar (cs ++ '|' :: r)) = r
    rw [if_neg hc]
    exact afterBar_append cs (fun x hx => h x (List.mem_cons_of_mem _ hx)) r

/-- The signature is an assignment's: the character after the first `|` is `A`. -/
def isA (s : String) : Bool := (afterBar s.toList).head? == some 'A'

/-- A number's decimal form has no `|` (the proof of
`Sparkle.IR.NameHints.digits`). -/
theorem no_bar_nat (n : Nat) : ∀ c ∈ (toString n).toList, c ≠ '|' := by
  intro c hc he
  simp only [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at hc
  have hd := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) hc
  rw [he] at hd
  first
    | exact absurd hd (by decide)
    | simp at hd

theorem isA_form (self : Nat) (t : String) (c : Char) (rest : List Char)
    (ht : t.toList = '|' :: c :: rest) : isA (toString self ++ t) = (c == 'A') := by
  unfold isA
  rw [String.toList_append, ht, afterBar_append _ (no_bar_nat self)]
  first
    | done
    | rfl
    | simp

theorem isA_of_form {s : String} {self : Nat} {lit X : String} {c : Char} {rest : List Char}
    (hs : s = toString self ++ (lit ++ X)) (hl : lit.toList = '|' :: c :: rest) :
    isA s = (c == 'A') := by
  have ht : (lit ++ X).toList = '|' :: c :: (rest ++ X.toList) := by
    simp only [String.toList_append, hl, List.cons_append]
  rw [hs]
  exact isA_form self (lit ++ X) c (rest ++ X.toList) ht

theorem litA : ("|A|" : String).toList = '|' :: 'A' :: ['|'] := by
  first
    | simp
    | rfl
    | decide

theorem litR : ("|R|" : String).toList = '|' :: 'R' :: ['|'] := by
  first
    | simp
    | rfl
    | decide

theorem litM : ("|M|" : String).toList = '|' :: 'M' :: ['|'] := by
  first
    | simp
    | rfl
    | decide

theorem litQ : ("|?" : String).toList = '|' :: '?' :: [] := by
  first
    | simp
    | rfl
    | decide

/-- **The kind marker of a signature**: `isA` of a statement's signature is
`isAssign` of the statement, whatever the class maps and the own class. -/
theorem isA_sig (alias : HashMap String String) (cls : HashMap String Nat) (self : Nat)
    (st : Stmt) : isA (sigOf alias cls self st) = isAssign st := by
  cases st with
  | assign l r =>
    have hX : ∃ X : String,
        sigOf alias cls self (Stmt.assign l r) = toString self ++ ("|A|" ++ X) := by
      first
        | exact ⟨_, String.append_assoc⟩
        | (simp only [sigOf, String.append_assoc]; exact ⟨_, rfl⟩)
        | (unfold sigOf; simp only [String.append_assoc]; exact ⟨_, rfl⟩)
    obtain ⟨X, hX⟩ := hX
    refine (isA_of_form hX litA).trans ?_
    first
      | (simp [isAssign]; done)
      | rfl
      | decide
  | register o clk rst input init =>
    obtain ⟨rstN, rk⟩ := rst
    have hX : ∃ X : String,
        sigOf alias cls self (Stmt.register o clk (rstN, rk) input init) =
          toString self ++ ("|R|" ++ X) := by
      first
        | (simp only [sigOf, String.append_assoc]; exact ⟨_, rfl⟩)
        | (unfold sigOf; simp only [String.append_assoc]; exact ⟨_, rfl⟩)
    obtain ⟨X, hX⟩ := hX
    refine (isA_of_form hX litR).trans ?_
    first
      | (simp [isAssign]; done)
      | rfl
      | decide
  | memory name aw dw clk wa wd we ra rd cr ew er =>
    have hX : ∃ X : String,
        sigOf alias cls self (Stmt.memory name aw dw clk wa wd we ra rd cr ew er) =
          toString self ++ ("|M|" ++ X) := by
      first
        | (simp only [sigOf, String.append_assoc]; exact ⟨_, rfl⟩)
        | (unfold sigOf; simp only [String.append_assoc]; exact ⟨_, rfl⟩)
    obtain ⟨X, hX⟩ := hX
    refine (isA_of_form hX litM).trans ?_
    first
      | (simp [isAssign]; done)
      | rfl
      | decide
  | inst mn inm conns =>
    have hs : sigOf alias cls self (Stmt.inst mn inm conns) = toString self ++ "|?" := by
      first
        | rfl
        | (simp only [sigOf]; rfl)
    refine ((congrArg isA hs).trans (isA_form self "|?" '?' [] litQ)).trans ?_
    first
      | (simp [isAssign]; done)
      | rfl
      | decide

/-! ## 2. The hash-map facts used, in `get?` form -/

theorem hm_get?_insert {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] [DecidableEq α]
    {m : HashMap α β} {k a : α} {v : β} :
    (m.insert k v).get? a = if k = a then some v else m.get? a := by
  rw [Std.HashMap.get?_insert]
  by_cases h : k = a
  · have hb : (k == a) = true := by simp [h]
    rw [if_pos h, if_pos hb]
  · have hb : ¬ ((k == a) = true) := by simpa using h
    rw [if_neg h, if_neg hb]

theorem hm_get?_insert_self {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] [DecidableEq α]
    {m : HashMap α β} {k : α} {v : β} : (m.insert k v).get? k = some v :=
  hm_get?_insert.trans (if_pos rfl)

theorem hm_get?_insert_ne {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] [DecidableEq α]
    {m : HashMap α β} {k a : α} {v : β} (h : ¬ (k = a)) : (m.insert k v).get? a = m.get? a :=
  hm_get?_insert.trans (if_neg h)

theorem hm_contains {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {m : HashMap α β} {a : α} : m.contains a = (m.get? a).isSome :=
  Std.HashMap.contains_eq_isSome_getElem?

theorem hm_getD {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {m : HashMap α β} {a : α} {fb : β} : m.getD a fb = (m.get? a).getD fb :=
  Std.HashMap.getD_eq_getD_getElem?

theorem hm_get?_empty {α β : Type} [BEq α] [Hashable α] {a : α} :
    ({} : HashMap α β).get? a = none := by
  first
    | exact Std.HashMap.getElem?_empty
    | simp
    | rfl

theorem hm_size_insert_new {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {m : HashMap α β} {k : α} {v : β} (h : m.get? k = none) :
    (m.insert k v).size = m.size + 1 := by
  have hn : ¬ (k ∈ m) := by
    intro hm
    have hc : m.contains k = true := Std.HashMap.mem_iff_contains.mp hm
    rw [hm_contains, h] at hc
    simp at hc
  rw [Std.HashMap.size_insert, if_neg hn]

/-! ## 3. One refinement round -/

/-- The id of a signature: its id if it has one, else the next free one. -/
def idOf (ids : HashMap String Nat) (s : String) : Nat :=
  match ids.get? s with
  | some k => k
  | none => ids.size

theorem idOf_spec (ids : HashMap String Nat) (s : String) :
    ids.get? s = some (idOf ids s) ∨ (ids.get? s = none ∧ idOf ids s = ids.size) := by
  cases h : ids.get? s with
  | some k =>
    left
    simp only [idOf, h]
  | none =>
    right
    refine ⟨rfl, ?_⟩
    simp only [idOf, h]

/-- The inner loop of `mergeDuplicatesParts` (251–257), as a recursion. -/
def innerRec (alias : HashMap String String) (cls : HashMap String Nat) :
    List (String × Stmt) → HashMap String Nat → HashMap String Nat →
      HashMap String Nat × HashMap String Nat
  | [], ids, next => (ids, next)
  | (n, st) :: l, ids, next =>
    innerRec alias cls l
      (ids.insert (sigOf alias cls (cls.getD n 0) st)
        (idOf ids (sigOf alias cls (cls.getD n 0) st)))
      (next.insert n (idOf ids (sigOf alias cls (cls.getD n 0) st)))

/-- The kind (`isAssign`) of the statement that last defined each name. -/
def updKind (kd : String → Bool) (n : String) (b : Bool) : String → Bool :=
  fun x => if x = n then b else kd x

def lastKind : List (String × Stmt) → (String → Bool) → String → Bool
  | [], kd => kd
  | (n, st) :: l, kd => lastKind l (updKind kd n (isAssign st))

theorem lastKind_append : ∀ (a b : List (String × Stmt)) (kd : String → Bool),
    lastKind (a ++ b) kd = lastKind b (lastKind a kd)
  | [], _, _ => rfl
  | (n, st) :: a, b, kd => lastKind_append a b (updKind kd n (isAssign st))

theorem lastKind_stable : ∀ (l : List (String × Stmt)) (kd : String → Bool) (n : String),
    kd n = false → (∀ s, (n, s) ∈ l → isAssign s = false) → lastKind l kd n = false
  | [], _, _, h, _ => h
  | (y, s) :: l, kd, n, h, hl => by
    show lastKind l (updKind kd y (isAssign s)) n = false
    apply lastKind_stable l _ n
    · show (if n = y then isAssign s else kd n) = false
      by_cases e : n = y
      · rw [if_pos e]
        exact hl s (by rw [e]; exact List.mem_cons_self ..)
      · rw [if_neg e]
        exact h
    · intro s' hs'
      exact hl s' (List.mem_cons_of_mem _ hs')

theorem lastKind_false : ∀ (l : List (String × Stmt)) (kd : String → Bool) (n : String),
    kd n = true → lastKind l kd n = false → ∃ st, (n, st) ∈ l ∧ isAssign st = false
  | [], kd, n, h, hf => by
    have hf' : kd n = false := hf
    rw [h] at hf'
    cases hf'
  | (y, s) :: l, kd, n, h, hf => by
    have hf' : lastKind l (updKind kd y (isAssign s)) n = false := hf
    by_cases hk : updKind kd y (isAssign s) n = true
    · obtain ⟨st, hst, hs⟩ := lastKind_false l _ n hk hf'
      exact ⟨st, List.mem_cons_of_mem _ hst, hs⟩
    · have hk' : ¬ ((if n = y then isAssign s else kd n) = true) := hk
      by_cases e : n = y
      · rw [if_pos e] at hk'
        refine ⟨s, ?_, ?_⟩
        · rw [e]
          exact List.mem_cons_self ..
        · cases hs : isAssign s with
          | true => exact absurd hs hk'
          | false => rfl
      · rw [if_neg e] at hk'
        exact absurd h hk'

/-- The invariant of a round: ids are below the size and distinct per
signature, and a name's class is the id of a signature whose kind is the
kind of the statement that last defined the name. -/
structure RoundInv (ids next : HashMap String Nat) (kd : String → Bool) : Prop where
  bound : ∀ s k, ids.get? s = some k → k < ids.size
  inj : ∀ s s' k, ids.get? s = some k → ids.get? s' = some k → s = s'
  kind : ∀ n k, next.get? n = some k → ∃ s, ids.get? s = some k ∧ isA s = kd n

theorem RoundInv.step {ids next : HashMap String Nat} {kd : String → Bool}
    (h : RoundInv ids next kd) (s n : String) (b : Bool) (v : Nat) (hs : isA s = b)
    (hv : ids.get? s = some v ∨ (ids.get? s = none ∧ v = ids.size)) :
    RoundInv (ids.insert s v) (next.insert n v) (updKind kd n b) := by
  have hsz : ids.size ≤ (ids.insert s v).size := Std.HashMap.size_le_size_insert
  have keep : ∀ x j, ids.get? x = some j → (ids.insert s v).get? x = some j := by
    intro x j hx
    by_cases e : s = x
    · rw [← e] at hx
      rw [← e, hm_get?_insert_self]
      rcases hv with hv | ⟨hv, -⟩
      · exact hv.symm.trans hx
      · exact absurd (hv.symm.trans hx) (by simp)
    · rw [hm_get?_insert_ne e]
      exact hx
  have selfB : v < (ids.insert s v).size := by
    rcases hv with hv | ⟨hv, hvs⟩
    · exact Nat.lt_of_lt_of_le (h.bound s v hv) hsz
    · rw [hm_size_insert_new hv]
      omega
  refine ⟨?_, ?_, ?_⟩
  · intro x k hx
    by_cases e : s = x
    · rw [← e, hm_get?_insert_self] at hx
      have hk : v = k := Option.some.inj hx
      rw [← hk]
      exact selfB
    · rw [hm_get?_insert_ne e] at hx
      exact Nat.lt_of_lt_of_le (h.bound x k hx) hsz
  · intro x x' k hx hx'
    by_cases e : s = x
    · by_cases e' : s = x'
      · exact e.symm.trans e'
      · rw [← e, hm_get?_insert_self] at hx
        rw [hm_get?_insert_ne e'] at hx'
        have hk : v = k := Option.some.inj hx
        rw [← hk] at hx'
        rw [← e]
        rcases hv with hv | ⟨hv, hvs⟩
        · exact h.inj s x' v hv hx'
        · have hlt := h.bound x' v hx'
          omega
    · by_cases e' : s = x'
      · rw [hm_get?_insert_ne e] at hx
        rw [← e', hm_get?_insert_self] at hx'
        have hk : v = k := Option.some.inj hx'
        rw [← hk] at hx
        rw [← e']
        rcases hv with hv | ⟨hv, hvs⟩
        · exact h.inj x s v hx hv
        · have hlt := h.bound x v hx
          omega
      · rw [hm_get?_insert_ne e] at hx
        rw [hm_get?_insert_ne e'] at hx'
        exact h.inj x x' k hx hx'
  · intro x k hx
    by_cases e : n = x
    · rw [← e, hm_get?_insert_self] at hx
      have hk : v = k := Option.some.inj hx
      refine ⟨s, ?_, ?_⟩
      · rw [← hk]
        exact hm_get?_insert_self
      · rw [hs, ← e]
        show b = (if n = n then b else kd n)
        exact (if_pos rfl).symm
    · rw [hm_get?_insert_ne e] at hx
      obtain ⟨s0, hs0, hk0⟩ := h.kind x k hx
      refine ⟨s0, keep s0 k hs0, ?_⟩
      rw [hk0]
      have e2 : ¬ (x = n) := fun q => e q.symm
      show kd x = (if x = n then b else kd x)
      exact (if_neg e2).symm

theorem innerRec_inv (alias : HashMap String String) (cls : HashMap String Nat) :
    ∀ (l : List (String × Stmt)) (ids next : HashMap String Nat) (kd : String → Bool),
      RoundInv ids next kd →
      RoundInv (innerRec alias cls l ids next).1 (innerRec alias cls l ids next).2 (lastKind l kd)
  | [], _, _, _, h => h
  | (n, st) :: l, ids, next, kd, h =>
    innerRec_inv alias cls l _ _ _
      (h.step (sigOf alias cls (cls.getD n 0) st) n (isAssign st)
        (idOf ids (sigOf alias cls (cls.getD n 0) st))
        (isA_sig alias cls (cls.getD n 0) st)
        (idOf_spec ids (sigOf alias cls (cls.getD n 0) st)))

theorem innerRec_dom (alias : HashMap String String) (cls : HashMap String Nat) :
    ∀ (l : List (String × Stmt)) (ids next : HashMap String Nat) (x : String),
      ((next.get? x).isSome = true ∨ x ∈ l.map (·.1)) →
      ((innerRec alias cls l ids next).2.get? x).isSome = true
  | [], _, _, _, h => by
    rcases h with h | h
    · exact h
    · simp at h
  | (n, st) :: l, ids, next, x, h => by
    show ((innerRec alias cls l _ (next.insert n _)).2.get? x).isSome = true
    apply innerRec_dom alias cls l
    by_cases e : n = x
    · left
      rw [← e]
      simp only [hm_get?_insert_self, Option.isSome_some]
    · rcases h with h | h
      · left
        rw [hm_get?_insert_ne e]
        exact h
      · right
        have h' : x ∈ n :: l.map (·.1) := h
        rcases List.mem_cons.mp h' with q | q
        · exact absurd q.symm e
        · exact q

/-- A class map that is the result of one round over the nodes. -/
def IsRound (nodes : List (String × Stmt)) (c : HashMap String Nat) : Prop :=
  ∃ (alias : HashMap String String) (cls0 : HashMap String Nat),
    c = (innerRec alias cls0 nodes {} {}).2

/-- **After a round, two names in one class were last defined by statements
of the same kind.** -/
theorem round_sep {nodes : List (String × Stmt)} {c : HashMap String Nat}
    (hc : IsRound nodes c) (kd0 : String → Bool) {n1 n2 : String}
    (h1 : n1 ∈ nodes.map (·.1)) (h2 : n2 ∈ nodes.map (·.1))
    (he : c.getD n1 0 = c.getD n2 0) :
    lastKind nodes kd0 n1 = lastKind nodes kd0 n2 := by
  obtain ⟨alias, cls0, hceq⟩ := hc
  rw [hceq] at he
  have e0 : RoundInv ({} : HashMap String Nat) ({} : HashMap String Nat) kd0 := by
    refine ⟨?_, ?_, ?_⟩
    · intro s k h
      rw [hm_get?_empty] at h
      cases h
    · intro s s' k h
      rw [hm_get?_empty] at h
      cases h
    · intro n k h
      rw [hm_get?_empty] at h
      cases h
  have inv := innerRec_inv alias cls0 nodes {} {} kd0 e0
  have d1 := innerRec_dom alias cls0 nodes {} {} n1 (Or.inr h1)
  have d2 := innerRec_dom alias cls0 nodes {} {} n2 (Or.inr h2)
  cases g1 : (innerRec alias cls0 nodes {} {}).2.get? n1 with
  | none =>
    rw [g1] at d1
    simp at d1
  | some k1 =>
    cases g2 : (innerRec alias cls0 nodes {} {}).2.get? n2 with
    | none =>
      rw [g2] at d2
      simp at d2
    | some k2 =>
      have hk : k1 = k2 := by
        have e1 : (innerRec alias cls0 nodes {} {}).2.getD n1 0 = k1 := by
          simp only [hm_getD, g1, Option.getD_some]
        have e2 : (innerRec alias cls0 nodes {} {}).2.getD n2 0 = k2 := by
          simp only [hm_getD, g2, Option.getD_some]
        exact e1.symm.trans (he.trans e2)
      obtain ⟨s1, hs1, q1⟩ := inv.kind n1 k1 g1
      obtain ⟨s2, hs2, q2⟩ := inv.kind n2 k2 g2
      rw [hk] at hs1
      have hss := inv.inj s1 s2 k2 hs1 hs2
      rw [← q1, ← q2, hss]

/-- The outer loop (248–261), as a recursion over its index list: a round,
then stop if the number of classes did not change. -/
def outerRec (alias : HashMap String String) (nodes : List (String × Stmt)) :
    List Nat → HashMap String Nat → Nat → HashMap String Nat × Nat
  | [], c, k => (c, k)
  | _ :: idx, c, k =>
    if (innerRec alias c nodes {} {}).1.size == k then ((innerRec alias c nodes {} {}).2, k)
    else outerRec alias nodes idx (innerRec alias c nodes {} {}).2
      (innerRec alias c nodes {} {}).1.size

/-- **After at least one pass the class map is a round's result.** -/
theorem outerRec_round (alias : HashMap String String) (nodes : List (String × Stmt))
    (idx : List Nat) : ∀ (c : HashMap String Nat) (k : Nat), idx ≠ [] →
      IsRound nodes (outerRec alias nodes idx c k).1 := by
  induction idx with
  | nil =>
    intro c k h
    exact absurd rfl h
  | cons i idx ih =>
    intro c k _
    show IsRound nodes
      (if (innerRec alias c nodes {} {}).1.size == k then ((innerRec alias c nodes {} {}).2, k)
        else outerRec alias nodes idx (innerRec alias c nodes {} {}).2
          (innerRec alias c nodes {} {}).1.size).1
    split
    · exact ⟨alias, c, rfl⟩
    · by_cases hn : idx = []
      · rw [hn]
        exact ⟨alias, c, rfl⟩
      · exact ih _ _ hn

/-! ## 4. Representatives and the substitution -/

/-- The representative loop (273–275). -/
def repRec (cls : HashMap String Nat) :
    List (String × Stmt) → HashMap Nat String → HashMap Nat String
  | [], rep => rep
  | (n, _) :: l, rep =>
    repRec cls l (if !rep.contains (cls.getD n 0) then rep.insert (cls.getD n 0) n else rep)

/-- The substitution loop (281–283). -/
def substRec (cls : HashMap String Nat) (rep : HashMap Nat String) :
    List (String × Stmt) → HashMap String String → HashMap String String
  | [], s => s
  | (n, _) :: l, s =>
    substRec cls rep l
      (if rep.getD (cls.getD n 0) n != n then s.insert n (rep.getD (cls.getD n 0) n) else s)

theorem repRec_keep (cls : HashMap String Nat) :
    ∀ (l : List (String × Stmt)) (rep : HashMap Nat String) (k : Nat) (n : String),
      rep.get? k = some n → (repRec cls l rep).get? k = some n
  | [], _, _, _, h => h
  | (x, _) :: l, rep, k, n, h => by
    show (repRec cls l
      (if !rep.contains (cls.getD x 0) then rep.insert (cls.getD x 0) x else rep)).get? k = some n
    apply repRec_keep cls l
    split
    · rename_i hc
      by_cases e : cls.getD x 0 = k
      · exfalso
        rw [e, hm_contains, h] at hc
        simp at hc
      · rw [hm_get?_insert_ne e]
        exact h
    · exact h

/-- Every entry of the representative map is a node name of its class. -/
def RepOk (cls : HashMap String Nat) (names : List String) (rep : HashMap Nat String) : Prop :=
  ∀ k n, rep.get? k = some n → n ∈ names ∧ cls.getD n 0 = k

theorem repRec_ok (cls : HashMap String Nat) (names : List String) :
    ∀ (l : List (String × Stmt)) (rep : HashMap Nat String), (∀ p ∈ l, p.1 ∈ names) →
      RepOk cls names rep → RepOk cls names (repRec cls l rep)
  | [], _, _, h => h
  | (x, st) :: l, rep, hl, h => by
    show RepOk cls names (repRec cls l
      (if !rep.contains (cls.getD x 0) then rep.insert (cls.getD x 0) x else rep))
    apply repRec_ok cls names l _ (fun p hp => hl p (List.mem_cons_of_mem _ hp))
    split
    · intro k n hg
      by_cases e : cls.getD x 0 = k
      · rw [← e, hm_get?_insert_self] at hg
        have hx : x = n := Option.some.inj hg
        rw [← hx]
        exact ⟨hl (x, st) (List.mem_cons_self ..), e⟩
      · rw [hm_get?_insert_ne e] at hg
        exact h k n hg
    · exact h

theorem repRec_cover (cls : HashMap String Nat) :
    ∀ (l : List (String × Stmt)) (rep : HashMap Nat String) (x : String), x ∈ l.map (·.1) →
      ∃ n, (repRec cls l rep).get? (cls.getD x 0) = some n
  | [], _, _, h => by simp at h
  | (y, _) :: l, rep, x, h => by
    show ∃ n, (repRec cls l
      (if !rep.contains (cls.getD y 0) then rep.insert (cls.getD y 0) y else rep)).get?
        (cls.getD x 0) = some n
    have h' : x ∈ y :: l.map (·.1) := h
    rcases List.mem_cons.mp h' with e | e
    · rw [e]
      have hstep : ∃ n,
          (if !rep.contains (cls.getD y 0) then rep.insert (cls.getD y 0) y else rep).get?
            (cls.getD y 0) = some n := by
        split
        · exact ⟨y, hm_get?_insert_self⟩
        · rename_i hc
          cases hg : rep.get? (cls.getD y 0) with
          | some n => exact ⟨n, rfl⟩
          | none =>
            exfalso
            apply hc
            simp only [hm_contains, hg, Option.isSome_none, Bool.not_false]
      obtain ⟨n, hn⟩ := hstep
      exact ⟨n, repRec_keep cls l _ _ _ hn⟩
    · exact repRec_cover cls l _ x e

/-- **A name that is its own representative is never put into `subst`.** -/
theorem substRec_none (cls : HashMap String Nat) (rep : HashMap Nat String) :
    ∀ (l : List (String × Stmt)) (s : HashMap String String) (x : String),
      rep.getD (cls.getD x 0) x = x → s.get? x = none → (substRec cls rep l s).get? x = none
  | [], _, _, _, h => h
  | (y, _) :: l, s, x, hx, h => by
    show (substRec cls rep l
      (if rep.getD (cls.getD y 0) y != y then s.insert y (rep.getD (cls.getD y 0) y)
        else s)).get? x = none
    apply substRec_none cls rep l _ x hx
    split
    · rename_i hc
      by_cases e : y = x
      · exfalso
        rw [e, hx] at hc
        simp at hc
      · rw [hm_get?_insert_ne e]
        exact h
    · exact h

/-! ## 5. The rewrite of the body -/

/-- A statement as a node: its name and itself (235–236). -/
def nodeOf (st : Stmt) : Option (String × Stmt) := (definedNode st).map fun n => (n, st)

def nodesOfBody (body : List Stmt) : List (String × Stmt) := body.filterMap nodeOf

def nodesOf (m : Module) : List (String × Stmt) := nodesOfBody m.body

theorem nodeOf_some {st : Stmt} {n : String} (h : definedNode st = some n) :
    nodeOf st = some (n, st) := by
  simp only [nodeOf, h, Option.map_some]

theorem node_eq {a : Stmt} {n : String} {s : Stmt} (h : nodeOf a = some (n, s)) :
    definedNode a = some n ∧ a = s := by
  unfold nodeOf at h
  cases hd : definedNode a with
  | none =>
    rw [hd] at h
    simp at h
  | some x =>
    rw [hd] at h
    have h' : some (x, a) = some (n, s) := h
    have h2 := Option.some.inj h'
    exact ⟨congrArg some (congrArg Prod.fst h2), congrArg Prod.snd h2⟩

/-- The statement a node becomes (289–291). -/
def rewriteNode (subst : HashMap String String) (st : Stmt) (n : String) : Option String → Stmt
  | some r => .assign n (.ref r)
  | none => Sparkle.IR.Optimize.mapStmtExprs (Sparkle.IR.Optimize.renameRefs subst) st

/-- The body rewrite (286–292). -/
def rewriteStmt (subst : HashMap String String) (st : Stmt) : Stmt :=
  match definedNode st with
  | some n => rewriteNode subst st n (subst.get? n)
  | none => Sparkle.IR.Optimize.mapStmtExprs (Sparkle.IR.Optimize.renameRefs subst) st

theorem isAssign_mapStmtExprs (f : Expr → Expr) (st : Stmt) :
    isAssign (Sparkle.IR.Optimize.mapStmtExprs f st) = isAssign st := by
  cases st <;> rfl

theorem rewriteStmt_keeps {subst : HashMap String String} {st : Stmt}
    (h : ∀ n, definedNode st = some n → subst.get? n = none) :
    isAssign (rewriteStmt subst st) = isAssign st := by
  unfold rewriteStmt
  cases hd : definedNode st with
  | none => exact isAssign_mapStmtExprs _ _
  | some n =>
    have hn := h n hd
    show isAssign (rewriteNode subst st n (subst.get? n)) = isAssign st
    rw [hn]
    exact isAssign_mapStmtExprs _ _

/-- The end of `mergeDuplicatesParts` (284–293). -/
def finish (m : Module) (subst : HashMap String String) : List Stmt × List (String × Expr) :=
  if subst.isEmpty then (m.body, m.assertions)
  else (m.body.map (rewriteStmt subst),
    m.assertions.map fun (n, e) => (n, Sparkle.IR.Optimize.renameRefs subst e))

theorem finish_keeps {m : Module} {subst : HashMap String String} (st : Stmt)
    (hm : st ∈ m.body) (hs : isAssign st = false)
    (h : ∀ n, definedNode st = some n → subst.get? n = none) :
    (finish m subst).1.all isAssign = false := by
  unfold finish
  split
  · show m.body.all isAssign = false
    rw [List.all_eq_false]
    exact ⟨st, hm, (by simp [hs])⟩
  · show (m.body.map (rewriteStmt subst)).all isAssign = false
    rw [List.all_eq_false]
    refine ⟨rewriteStmt subst st, List.mem_map.mpr ⟨st, hm, rfl⟩, ?_⟩
    simp [rewriteStmt_keeps h, hs]

/-! ## 6. The hypothesis and the theorem -/

/-- **Some non-assignment statement is not followed by an assignment to the
name it defines.** -/
def LastNonAssign (body : List Stmt) : Prop :=
  ∃ (pre : List Stmt) (st : Stmt) (post : List Stmt), body = pre ++ st :: post ∧
    isAssign st = false ∧ ∀ l r, Stmt.assign l r ∈ post → definedNode st ≠ some l

theorem LastNonAssign.nonAssign {body : List Stmt} (h : LastNonAssign body) :
    body.all isAssign = false := by
  obtain ⟨pre, st, post, hb, hs, -⟩ := h
  have hm : st ∈ body := by
    rw [hb]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  rw [List.all_eq_false]
  exact ⟨st, hm, (by simp [hs])⟩

/-- **With a round's class map, the rewritten body keeps a non-assignment.** -/
theorem classes_keep (m : Module) (c : HashMap String Nat) (hround : IsRound (nodesOf m) c)
    (hL : LastNonAssign m.body) :
    (finish m (substRec c (repRec c (nodesOf m) {}) (nodesOf m) {})).1.all isAssign = false := by
  obtain ⟨pre, st, post, hb, hs, hpost⟩ := hL
  have hm : st ∈ m.body := by
    rw [hb]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  cases hd : definedNode st with
  | none =>
    refine finish_keeps st hm hs ?_
    intro n hn
    exact absurd (hd.symm.trans hn) (by simp)
  | some n =>
    -- `n` is a node name
    have hnode : (n, st) ∈ nodesOf m :=
      List.mem_filterMap.mpr ⟨st, hm, nodeOf_some hd⟩
    have hname : n ∈ (nodesOf m).map (·.1) := List.mem_map.mpr ⟨(n, st), hnode, rfl⟩
    -- the statement that last defines `n` is not an assignment
    have hsplit : nodesOf m = nodesOfBody pre ++ (n, st) :: nodesOfBody post := by
      show List.filterMap nodeOf m.body =
        List.filterMap nodeOf pre ++ (n, st) :: List.filterMap nodeOf post
      rw [hb, List.filterMap_append, List.filterMap_cons_some (nodeOf_some hd)]
    have hpostK : ∀ s, (n, s) ∈ nodesOfBody post → isAssign s = false := by
      intro s hsm
      obtain ⟨a, ha, hna⟩ := List.mem_filterMap.mp hsm
      obtain ⟨hdn, has⟩ := node_eq hna
      rw [← has]
      cases a with
      | assign l r =>
        exfalso
        have hl : l = n := Option.some.inj hdn
        refine hpost l r ha ?_
        rw [hd, hl]
      | _ => rfl
    have hK : lastKind (nodesOf m) (fun _ => true) n = false := by
      rw [hsplit, lastKind_append]
      show lastKind (nodesOfBody post)
        (updKind (lastKind (nodesOfBody pre) (fun _ => true)) n (isAssign st)) n = false
      have h0 : updKind (lastKind (nodesOfBody pre) (fun _ => true)) n (isAssign st) n = false := by
        simp [updKind, hs]
      exact lastKind_stable _ _ n h0 hpostK
    -- the representative of the class of `n`
    obtain ⟨n', hn'⟩ := repRec_cover c (nodesOf m) {} n hname
    have hok : RepOk c ((nodesOf m).map (·.1)) (repRec c (nodesOf m) {}) := by
      refine repRec_ok c ((nodesOf m).map (·.1)) (nodesOf m) {} ?_ ?_
      · intro p hp
        exact List.mem_map.mpr ⟨p, hp, rfl⟩
      · intro k x hx
        rw [hm_get?_empty] at hx
        cases hx
    obtain ⟨hn'mem, hn'cls⟩ := hok _ _ hn'
    have hself0 : (repRec c (nodesOf m) {}).getD (c.getD n 0) n' = n' :=
      (hm_getD (m := repRec c (nodesOf m) {}) (a := c.getD n 0) (fb := n')).trans
        (by rw [hn']; first | done | rfl)
    have hself : (repRec c (nodesOf m) {}).getD (c.getD n' 0) n' = n' := by
      rw [hn'cls]
      exact hself0
    -- it was last defined by a non-assignment too
    have hK' : lastKind (nodesOf m) (fun _ => true) n' = false :=
      (round_sep hround (fun _ => true) hn'mem hname hn'cls).trans hK
    obtain ⟨st', hst', hs'⟩ := lastKind_false (nodesOf m) (fun _ => true) n' rfl hK'
    obtain ⟨a, ha, hna⟩ := List.mem_filterMap.mp hst'
    obtain ⟨hdn, has⟩ := node_eq hna
    have hsa : isAssign a = false := by
      rw [has]
      exact hs'
    refine finish_keeps a ha hsa ?_
    intro x hx
    have hx' : n' = x := Option.some.inj (hdn.symm.trans hx)
    rw [← hx']
    exact substRec_none c _ (nodesOf m) {} n' hself hm_get?_empty

/-- What follows the class refinement (262, 272–293). -/
def afterClasses (m : Module) (cn : HashMap String Nat × Nat) :
    List Stmt × List (String × Expr) :=
  if cn.2 == (nodesOf m).length then (m.body, m.assertions)
  else finish m (substRec cn.1 (repRec cn.1 (nodesOf m) {}) (nodesOf m) {})

/-- `mergeDuplicatesParts` with its loops as recursions; `alias`, the first
class map and the index list of the outer loop are parameters. -/
def partsRec (m : Module) (alias : HashMap String String) (c0 : HashMap String Nat)
    (idx : List Nat) : List Stmt × List (String × Expr) :=
  if (nodesOf m).length < 2 then (m.body, m.assertions)
  else afterClasses m (outerRec alias (nodesOf m) idx c0 1)

/-- **The merge, as recursions, keeps a non-assignment statement.** -/
theorem partsRec_keeps (m : Module) (alias : HashMap String String) (c0 : HashMap String Nat)
    (idx : List Nat) (hidx : idx ≠ []) (hL : LastNonAssign m.body) :
    (partsRec m alias c0 idx).1.all isAssign = false := by
  unfold partsRec
  split
  · exact hL.nonAssign
  · unfold afterClasses
    split
    · exact hL.nonAssign
    · exact classes_keep m _ (outerRec_round alias (nodesOf m) idx c0 1 hidx) hL

/-! ## 7. Distinct defined names give the hypothesis -/

/-- With distinct defined names, a body that is not assignments only has a
non-assignment statement no later assignment redefines. -/
theorem lastNonAssign_of_nodup {body : List Stmt}
    (hnd : (body.filterMap definedNode).Nodup) (h : body.all isAssign = false) :
    LastNonAssign body := by
  rw [List.all_eq_false] at h
  obtain ⟨st, hm, hs⟩ := h
  obtain ⟨pre, post, hb⟩ := List.append_of_mem hm
  have hs' : isAssign st = false := by
    cases hq : isAssign st with
    | true => exact absurd hq hs
    | false => rfl
  refine ⟨pre, st, post, hb, hs', ?_⟩
  intro l r hmem hdn
  rw [hb, List.filterMap_append, List.filterMap_cons_some hdn] at hnd
  have h2 := (List.nodup_append.mp hnd).2.1
  have h3 := (List.nodup_cons.mp h2).1
  exact h3 (List.mem_filterMap.mpr ⟨Stmt.assign l r, hmem, rfl⟩)

end Tools.ShippingMergeKeeps
