import Lean

/-! # Name separation (obligation N1): what `Name.toString` can be, for every name

The closed machine endpoints carry premises about printed names
(`c.toString ≠ parent.toString`, `c.toString = c'.toString → c = c'`,
`o.name ≠ s!"inst{k}_{c.toString}"`) because `Lean.Name.toString` with
escaping does not evaluate in the kernel.

## The definition chain (toolchain v4.32.1, `src/lean/Init/Data/ToString/Name.lean`)

    Name.toString n (escape := true)                       line 123
      = Name.toStringWithToken n escape (fun _ => false)   line 100
      = Name.toStringWithSep "."
          (escape && !n.isInaccessibleUserName && !n.hasMacroScopes && !maybePseudoSyntax)
          n (fun _ => false)                               line 73
    toStringWithSep, per component `s`: maybeEscape s force
      = if escape then (escapePart s force).getD s else s  line 85
    escapePart s force                                     line 55
      = if h : s.utf8ByteSize > 0 then
          if !force && needsNoEscape s h then some s
          else if s.any isIdEndEscape then none
          else some (escape s)
        else some (escape s)
    needsNoEscape s h   (private, line 41)
      = needsNoEscapeAscii s h || isIdFirst s.front && (s.toRawSubstring.drop 1).all isIdRest
    needsNoEscapeAscii s h   (private, line 36)
      = isIdFirstAscii (s.getUTF8Byte 0 h) && needsNoEscapeAsciiRest s 1
    needsNoEscapeAsciiRest   (line 28)  — `private partial def`

What blocks evaluation:
* `needsNoEscapeAsciiRest` is a `partial def`: an OPAQUE constant in the
  logic. For every component that starts with an ASCII identifier character
  — every ordinary name — the escape test is `opaque || …`, which does not
  reduce, and whose value NO proof can determine. So "this component is not
  escaped" cannot be obtained from the first disjunct at all;
* the second disjunct (`String.front`, `Substring.Raw.drop`,
  `Substring.Raw.all` = `(s.toSlice?.get!).all p`, the pattern-searcher
  machinery) is defined and in principle provable (`String.Slice.all_bool_eq`
  gives the character list), but it does not evaluate in the kernel and core
  has no lemma taking `Substring.Raw.drop` / `String.front` to the character
  list. A bridge "plain component ⟹ not escaped" needs those lemmas first;
  it is NOT proved here;
* the escape switch itself scans strings (`isInaccessibleUserName`:
  `s.contains '✝'`; `maybePseudoSyntax`: `isPrefixOf`).

## What is proved instead — for EVERY name, no "plain" predicate

The opaque test only chooses, per component, between `s` and `«s»`. So the
printed name is one of finitely many strings, all of them built by string
appends the kernel does evaluate:

* `cands n`: the candidate renderings of `n` (each string component escaped
  or not), a structural function;
* `toString_mem : n.toString ∈ cands n`, for every `n` — by case analysis on
  the opaque test's outcome, never evaluating it;
* `toString_elim`: a property of all candidates holds of the printed name;
* `toString_ne` (`sepB a b = true → a.toString ≠ b.toString`): two names
  print differently when no candidate of one is a candidate of the other —
  a Boolean check on concrete names;
* the endpoints' shapes: `hparent_of`, `hnames_of`, `fresh_of`.

`toString` is NOT injective on all names, and the candidate check is what
tells: with reading the definition only (not evaluated), `"a».b"` as ONE
component and `"a»"`, `"b"` as two can print as the same string (a component
containing `»` is never escaped), and names containing `✝` switch escaping
off altogether. `sepB` is `false` on such a pair; it is the criterion, not a
syntactic notion of "plain".

What is NOT proved here
* `n.toString = n.toString (escape := false)` for any class of names (the
  bridge above).
* That `decide` evaluates `sepB` on the endpoints' names in acceptable time:
  a name of `k` string components has `2^k` candidates, so a pair costs
  `2^k · 2^k'` string comparisons in the kernel. UNMEASURED.
* Nothing about names with numeric components beyond the candidate list
  (`Nat.repr` is used as written).

UNVERIFIED at the time of writing: this file was not built. It relies on the
bodies of `Name.escapePart` (and of the private `escape`) being unfoldable
from a non-`module` file. -/
namespace Tools.ShippingNameSep

/-- `«s»`, as `Name.escapePart` writes it. -/
def esc (s : String) : String :=
  Lean.idBeginEscape.toString ++ s ++ Lean.idEndEscape.toString

/-- The three outcomes of `escapePart`; which one is not decided here. -/
theorem escapePart_cases (s : String) (force : Bool) :
    Lean.Name.escapePart s force = some s ∨ Lean.Name.escapePart s force = none ∨
      Lean.Name.escapePart s force = some (esc s) := by
  unfold Lean.Name.escapePart
  split
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inr rfl)

/-- A component is printed as itself or escaped. -/
theorem maybe_cases (e : Bool) (s : String) (force : Bool) :
    (if e = true then (Lean.Name.escapePart s force).getD s else s) = s ∨
      (if e = true then (Lean.Name.escapePart s force).getD s else s) = esc s := by
  cases e
  · exact Or.inl (if_neg (fun h => by cases h))
  · rcases escapePart_cases s force with h | h | h
    · exact Or.inl ((if_pos rfl).trans (congrArg (fun (o : Option String) => o.getD s) h))
    · exact Or.inl ((if_pos rfl).trans (congrArg (fun (o : Option String) => o.getD s) h))
    · exact Or.inr ((if_pos rfl).trans (congrArg (fun (o : Option String) => o.getD s) h))

/-- The candidate renderings of a name: every string component as itself or
escaped. -/
def cands : Lean.Name → List String
  | .anonymous => ["[anonymous]"]
  | .str .anonymous s => [s, esc s]
  | .num .anonymous v => [toString v]
  | .str p s => (cands p).flatMap fun r => [r ++ "." ++ s, r ++ "." ++ esc s]
  | .num p v => (cands p).map fun r => r ++ "." ++ Nat.repr v

theorem mem_str {r : String} {l : List String} (hr : r ∈ l) {s x : String}
    (hx : x = s ∨ x = esc s) :
    r ++ "." ++ x ∈ l.flatMap (fun r => [r ++ "." ++ s, r ++ "." ++ esc s]) := by
  refine List.mem_flatMap.mpr ⟨r, hr, ?_⟩
  rcases hx with h | h
  · subst h
    exact List.Mem.head _
  · subst h
    exact List.Mem.tail _ (List.Mem.head _)

/-- The separator renderer with the trivial token test is one of the
candidates, whatever the escape switch. -/
theorem sep_mem (e : Bool) :
    ∀ n : Lean.Name, Lean.Name.toStringWithSep "." e n (fun _ => false) ∈ cands n
  | .anonymous => List.Mem.head _
  | .str .anonymous s => by
    have h0 : Lean.Name.toStringWithSep "." e (.str .anonymous s) (fun _ => false) =
        (if e = true then (Lean.Name.escapePart s false).getD s else s) := rfl
    rw [h0]
    rcases maybe_cases e s false with h | h
    · rw [h]
      exact List.Mem.head _
    · rw [h]
      exact List.Mem.tail _ (List.Mem.head _)
  | .num .anonymous _ => List.Mem.head _
  | .str (.str q t) s => by
    have ih := sep_mem e (.str q t)
    cases e
    · exact mem_str ih (maybe_cases false s false)
    · exact mem_str ih (maybe_cases true s false)
  | .str (.num q w) s => by
    have ih := sep_mem e (.num q w)
    cases e
    · exact mem_str ih (maybe_cases false s false)
    · exact mem_str ih (maybe_cases true s false)
  | .num (.str q t) _ => List.mem_map.mpr ⟨_, sep_mem e (.str q t), rfl⟩
  | .num (.num q w) _ => List.mem_map.mpr ⟨_, sep_mem e (.num q w), rfl⟩

/-- **The printed name is one of the candidates**, for every name. -/
theorem toString_mem (n : Lean.Name) : n.toString ∈ cands n :=
  sep_mem _ n

/-- A property of every candidate holds of the printed name. -/
theorem toString_elim (n : Lean.Name) (P : String → Prop) (h : ∀ x, x ∈ cands n → P x) :
    P n.toString :=
  h _ (toString_mem n)

/-- No candidate of `a` is a candidate of `b`. -/
def sepB (a b : Lean.Name) : Bool :=
  (cands a).all fun x => (cands b).all fun y => decide (x ≠ y)

/-- **Separation of two names.** -/
theorem toString_ne {a b : Lean.Name} (h : sepB a b = true) : a.toString ≠ b.toString := by
  intro heq
  have h1 := List.all_eq_true.mp h _ (toString_mem a)
  have h2 := List.all_eq_true.mp h1 _ (toString_mem b)
  have h3 : a.toString ≠ b.toString := of_decide_eq_true h2
  exact h3 heq

/-! ## The endpoints' premises -/

/-- `hparent`: no callee prints as the parent. -/
theorem hparent_of {α : Type} (insts : List (Lean.Name × α)) (parent : Lean.Name)
    (h : (insts.all fun c => sepB c.1 parent) = true) :
    ∀ c ∈ insts, c.1.toString ≠ parent.toString := by
  intro c hc
  have h1 : sepB c.1 parent = true := List.all_eq_true.mp h c hc
  exact toString_ne h1

/-- `hnames`: different called declarations print differently. -/
theorem hnames_of (L : List Lean.Name)
    (h : (L.all fun c => L.all fun c' => decide (c = c') || sepB c c') = true) :
    ∀ c ∈ L, ∀ c' ∈ L, c.toString = c'.toString → c = c' := by
  intro c hc c' hc' heq
  have h1 := List.all_eq_true.mp h c hc
  have h2 : (decide (c = c') || sepB c c') = true := List.all_eq_true.mp h1 c' hc'
  cases hd : decide (c = c') with
  | true => exact of_decide_eq_true hd
  | false =>
    rw [hd] at h2
    have h3 : sepB c c' = true := h2
    exact absurd heq (toString_ne h3)

/-- `hfresh`, one call: a string is not `f` of the printed name when it is
`f` of no candidate (`f` is the instance-name format, e.g.
`fun x => s!"inst{k}_{x}"`). -/
theorem fresh_of (c : Lean.Name) (f : String → String) (o : String)
    (h : ((cands c).all fun x => decide (o ≠ f x)) = true) : o ≠ f c.toString := by
  have h1 := List.all_eq_true.mp h _ (toString_mem c)
  exact of_decide_eq_true h1

/-- `c.toString ∉ names`. -/
theorem not_mem_of (c : Lean.Name) (names : List String)
    (h : ((cands c).all fun x => decide (x ∉ names)) = true) : c.toString ∉ names := by
  have h1 := List.all_eq_true.mp h _ (toString_mem c)
  exact of_decide_eq_true h1

/-! ## Lists of declarations (the deep closings' name lists)

The printed names of a list of declarations are written
`L.map (fun n => n.toString)` — `Lean.Name.toString` has an optional
argument, so `L.map Lean.Name.toString` does not typecheck. -/

/-- `c` prints differently from every declaration of `L`. -/
theorem not_mem_map_of (c : Lean.Name) (L : List Lean.Name)
    (h : (L.all fun c' => sepB c c') = true) : c.toString ∉ L.map (fun n => n.toString) := by
  intro hm
  obtain ⟨c', hc', heq⟩ := List.mem_map.mp hm
  have h1 : sepB c c' = true := List.all_eq_true.mp h c' hc'
  have h2 : c.toString = c'.toString := heq.symm
  exact toString_ne h1 h2

/-- No declaration of `L` prints as a declaration of `L'`. -/
theorem disjoint_map_of (L L' : List Lean.Name)
    (h : (L.all fun c => L'.all fun c' => sepB c c') = true) :
    ∀ x ∈ L.map (fun n => n.toString), x ∉ L'.map (fun n => n.toString) := by
  intro x hx hx'
  obtain ⟨c, hc, e1⟩ := List.mem_map.mp hx
  obtain ⟨c', hc', e2⟩ := List.mem_map.mp hx'
  have h0 := List.all_eq_true.mp h c hc
  have h1 : sepB c c' = true := List.all_eq_true.mp h0 c' hc'
  have h2 : c.toString = c'.toString := e1.trans e2.symm
  exact toString_ne h1 h2

/-- The printed names of a duplicate-free list are duplicate-free when
printing is injective on it. -/
theorem nodup_map_of_inj : ∀ (L : List Lean.Name), L.Nodup →
    (∀ a ∈ L, ∀ b ∈ L, a.toString = b.toString → a = b) →
    (L.map (fun n => n.toString)).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hnd, hinj => by
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hnd
    refine List.nodup_cons.mpr ⟨?_, nodup_map_of_inj l hl
      (fun x hx y hy e => hinj x (List.Mem.tail _ hx) y (List.Mem.tail _ hy) e)⟩
    intro hm
    obtain ⟨b, hb, e⟩ := List.mem_map.mp hm
    have e' : a.toString = b.toString := e.symm
    have hab : a = b := hinj a (List.Mem.head _) b (List.Mem.tail _ hb) e'
    exact ha (by rw [hab]; exact hb)

/-- The printed names of `L` are pairwise distinct when its declarations
are distinct and print differently pairwise (the check of `hnames_of`). -/
theorem nodup_map_of (L : List Lean.Name) (hnd : L.Nodup)
    (h : (L.all fun c => L.all fun c' => decide (c = c') || sepB c c') = true) :
    (L.map (fun n => n.toString)).Nodup :=
  nodup_map_of_inj L hnd (hnames_of L h)

end Tools.ShippingNameSep
