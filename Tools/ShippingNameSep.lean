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
* `sepB` is costly in the kernel: a name of `k` string components has `2^k`
  candidates, so a pair costs `2^k · 2^k'` string comparisons (measured by
  the integrator: one test module peaks at 2.44 GiB). The structural test at
  the end of this file (`sepC` / `sepFast`, `inj_of`) avoids both the
  enumeration and the strings, for names with plain string components.
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

/-! ## A cheaper, structural test (round 12)

`sepB` enumerates `2^k` candidates per name and compares STRINGS in the
kernel (appends and equality on UTF-8 byte arrays): one test module peaked
at 2.44 GiB. The test below never builds a string and never enumerates.

A name is given by the CHARACTERS of its components, last component first
(`CN`); `nameOf` rebuilds the name with `String.ofList`, which a string
literal unfolds to (so `nameOf [['c','n','t'], ['M']]` and `` `M.cnt `` are
expected to be definitionally equal at the cost of expanding the literals —
NOT measured). A component is PLAIN (`plainC`) when it contains none of

    '.'   the separator `toStringWithSep "."` writes between components
    '«'   `idBeginEscape`, written by `escapePart` in front of an escaped part
    '»'   `idEndEscape`, written behind it

Those three are the only characters the proof needs to know about: whatever
`escapePart` decides (its test looks at `isIdFirst` / `isIdRest` /
`isIdEndEscape` and the opaque ASCII scan), the result is the component or
the component between `«` `»`, so deleting `«` `»` from ANY candidate of a
name with plain components leaves the components joined by dots, and a list
of dot-free components is recovered from that. Hence:

* `inj_of`: on names with plain string components, printing is INJECTIVE —
  no comparison of candidates at all;
* `sepC A B = okC A && okC B && decide (A ≠ B)`: linear in the characters;
* the list forms `hnames_of'` (the check is `L.all okC`, linear — no
  pairwise test), `hparent_of'`, `not_mem_map_of'`, `disjoint_map_of'`,
  `nodup_map_of'`;
* `sepFast a b` on `Lean.Name`s (through `String.toList`, whose kernel cost
  on a literal is NOT measured; the `CN` forms avoid it).

What `sepFast` / `sepC` cannot separate and `sepB` can: names with a
numeric component (private names, macro scopes), the anonymous name, names
with a component containing `.`, `«` or `»` (e.g. `` `«a.b».c `` against
`` `d ``), and — for `fresh_of` / `not_mem_of` — a printed name against an
arbitrary string (`s!"inst{k}_{c}"`): those two keep the candidate lists. -/

/-- A name by the characters of its string components, last component
first. -/
abbrev CN := List (List Char)

/-- The name of a component list. -/
def nameOf : CN → Lean.Name
  | [] => .anonymous
  | cs :: rest => .str (nameOf rest) (String.ofList cs)

/-- An escape bracket. -/
def bra (c : Char) : Bool :=
  decide (c = Lean.idBeginEscape) || decide (c = Lean.idEndEscape)

/-- A character list without the escape brackets. -/
def stripL (l : List Char) : List Char := l.filter fun c => !bra c

/-- A component with no separator and no escape bracket. -/
def plainC (cs : List Char) : Bool := cs.all fun c => !bra c && !decide (c = '.')

/-- A non-anonymous name whose components are all plain. -/
def okC (A : CN) : Bool := !A.isEmpty && A.all plainC

/-- The printed form after deleting the brackets: the components joined by
dots. -/
def key : CN → List Char
  | [] => []
  | [cs] => cs
  | cs :: rest => key rest ++ '.' :: cs

theorem and_tt {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | (have h' : false = true := h; cases h')

theorem not_tt {a : Bool} (h : (!a) = true) : a = false := by
  cases a <;> first | rfl | (have h' : false = true := h; cases h')

theorem not_ff {a : Bool} (h : a = false) : (!a) = true := by
  subst h
  rfl

theorem or_l {a b : Bool} (h : a = true) : (a || b) = true := by
  subst h
  rfl

theorem or_r {a b : Bool} (h : b = true) : (a || b) = true := by
  subst h
  cases a <;> rfl

theorem bra_b : bra Lean.idBeginEscape = true := by
  unfold bra
  exact or_l (decide_eq_true rfl)

theorem bra_e : bra Lean.idEndEscape = true := by
  unfold bra
  exact or_r (decide_eq_true rfl)

theorem bra_dot : bra '.' = false := by decide

theorem plain_mem {cs : List Char} (h : plainC cs = true) {c : Char} (hc : c ∈ cs) :
    bra c = false ∧ c ≠ '.' := by
  have h1 : (!bra c && !decide (c = '.')) = true := List.all_eq_true.mp h c hc
  obtain ⟨ha, hb⟩ := and_tt h1
  exact ⟨not_tt ha, of_decide_eq_false (not_tt hb)⟩

theorem dot_not_mem {cs : List Char} (h : plainC cs = true) : '.' ∉ cs :=
  fun hm => (plain_mem h hm).2 rfl

theorem strip_plain {cs : List Char} (h : plainC cs = true) : stripL cs = cs := by
  unfold stripL
  exact List.filter_eq_self.mpr fun a ha => not_ff (plain_mem h ha).1

theorem strip_append (a b : List Char) : stripL (a ++ b) = stripL a ++ stripL b := by
  unfold stripL
  exact List.filter_append a b

theorem strip_single {c : Char} (h : bra c = true) : stripL [c] = [] := by
  unfold stripL
  exact List.filter_cons_of_neg fun hh => absurd (h.symm.trans (not_tt hh)) (by decide)

theorem strip_dot : stripL ['.'] = ['.'] := by
  unfold stripL
  exact List.filter_cons_of_pos (not_ff bra_dot)

theorem dot_toList : (".": String).toList = ['.'] :=
  (congrArg String.toList (rfl : (".": String) = String.ofList ['.'])).trans String.toList_ofList

theorem esc_toList (s : String) :
    (esc s).toList = [Lean.idBeginEscape] ++ s.toList ++ [Lean.idEndEscape] := by
  unfold esc
  rw [String.toList_append, String.toList_append, Char.toString_eq_singleton,
    Char.toString_eq_singleton, String.toList_singleton, String.toList_singleton]

theorem strip_esc (s : String) : stripL (esc s).toList = stripL s.toList := by
  have h1 : stripL (esc s).toList = [] ++ stripL s.toList ++ [] := by
    rw [esc_toList, strip_append, strip_append, strip_single bra_b, strip_single bra_e]
  exact h1.trans (List.append_nil _)

/-- A plain component, as itself or escaped, strips to itself. -/
theorem strip_part {cs : List Char} (h : plainC cs = true) {y : String}
    (hy : y = String.ofList cs ∨ y = esc (String.ofList cs)) : stripL y.toList = cs := by
  have h0 : stripL (String.ofList cs).toList = cs :=
    (congrArg stripL String.toList_ofList).trans (strip_plain h)
  rcases hy with e | e
  · exact (congrArg (fun (z : String) => stripL z.toList) e).trans h0
  · exact (congrArg (fun (z : String) => stripL z.toList) e).trans ((strip_esc _).trans h0)

theorem strip_join (r y : String) (k cs : List Char) (hr : stripL r.toList = k)
    (hy : stripL y.toList = cs) : stripL (r ++ "." ++ y).toList = k ++ '.' :: cs := by
  have h1 : stripL (r ++ "." ++ y).toList = k ++ ['.'] ++ cs := by
    rw [String.toList_append, String.toList_append, strip_append, strip_append, hr, hy,
      dot_toList, strip_dot]
  exact h1.trans (List.append_assoc k ['.'] cs)

theorem all_tail {α : Type} {p : α → Bool} {a : α} {l : List α}
    (h : (a :: l).all p = true) : l.all p = true :=
  List.all_eq_true.mpr fun y hy => List.all_eq_true.mp h y (List.Mem.tail _ hy)

/-- **Every candidate rendering of a name with plain components strips to
the dotted components.** -/
theorem cand_strip : ∀ (A : CN), A ≠ [] → A.all plainC = true →
    ∀ x, x ∈ cands (nameOf A) → stripL x.toList = key A
  | [], h, _, _, _ => absurd rfl h
  | [cs], _, hp, x, hx => by
    have hcs : plainC cs = true := List.all_eq_true.mp hp cs (List.Mem.head _)
    have hx' : x ∈ [String.ofList cs, esc (String.ofList cs)] := hx
    show stripL x.toList = cs
    rcases List.mem_cons.mp hx' with e | hx''
    · exact strip_part hcs (Or.inl e)
    · exact strip_part hcs (Or.inr (List.mem_singleton.mp hx''))
  | cs :: c2 :: rest, _, hp, x, hx => by
    have hcs : plainC cs = true := List.all_eq_true.mp hp cs (List.Mem.head _)
    have hx' : x ∈ (cands (nameOf (c2 :: rest))).flatMap
        (fun r => [r ++ "." ++ String.ofList cs, r ++ "." ++ esc (String.ofList cs)]) := hx
    obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.mp hx'
    have ih := cand_strip (c2 :: rest) (List.cons_ne_nil _ _) (all_tail hp) r hr
    show stripL x.toList = key (c2 :: rest) ++ '.' :: cs
    have hxr' : x ∈ [r ++ "." ++ String.ofList cs, r ++ "." ++ esc (String.ofList cs)] := hxr
    rcases List.mem_cons.mp hxr' with e | hx''
    · exact (congrArg (fun (z : String) => stripL z.toList) e).trans
        (strip_join r (String.ofList cs) _ cs ih (strip_part hcs (Or.inl rfl)))
    · have e : x = r ++ "." ++ esc (String.ofList cs) := List.mem_singleton.mp hx''
      exact (congrArg (fun (z : String) => stripL z.toList) e).trans
        (strip_join r (esc (String.ofList cs)) _ cs ih (strip_part hcs (Or.inr rfl)))

/-- Two lists split at a separator that occurs in neither tail agree part
by part. -/
theorem append_sep_inj {α : Type} {d : α} : ∀ (X Y a b : List α), d ∉ a → d ∉ b →
    X ++ d :: a = Y ++ d :: b → X = Y ∧ a = b
  | [], [], a, b, _, _, h => by
    have h1 : d :: a = d :: b := h
    exact ⟨rfl, (List.cons.inj h1).2⟩
  | [], y :: Y, a, b, ha, _, h => by
    have h1 : d :: a = y :: (Y ++ d :: b) := h
    have h2 : a = Y ++ d :: b := (List.cons.inj h1).2
    have h3 : d ∈ Y ++ d :: b := List.mem_append_right Y (List.Mem.head _)
    exact absurd (Eq.mpr (congrArg (fun (l : List α) => d ∈ l) h2) h3) ha
  | x :: X, [], a, b, _, hb, h => by
    have h1 : x :: (X ++ d :: a) = d :: b := h
    have h2 : X ++ d :: a = b := (List.cons.inj h1).2
    have h3 : d ∈ X ++ d :: a := List.mem_append_right X (List.Mem.head _)
    exact absurd (Eq.mp (congrArg (fun (l : List α) => d ∈ l) h2) h3) hb
  | x :: X, y :: Y, a, b, ha, hb, h => by
    have h1 : x :: (X ++ d :: a) = y :: (Y ++ d :: b) := h
    obtain ⟨hxy, ht⟩ := List.cons.inj h1
    obtain ⟨e1, e2⟩ := append_sep_inj X Y a b ha hb ht
    exact ⟨(congrArg (fun (z : α) => z :: X) hxy).trans (congrArg (fun (Z : List α) => y :: Z) e1), e2⟩

/-- The dotted form determines the plain components. -/
theorem key_inj : ∀ (A B : CN), A ≠ [] → B ≠ [] → A.all plainC = true → B.all plainC = true →
    key A = key B → A = B
  | [], _, h, _, _, _, _ => absurd rfl h
  | _ :: _, [], _, h, _, _, _ => absurd rfl h
  | [a], [b], _, _, _, _, h => by
    have h1 : a = b := h
    exact congrArg (fun (z : List Char) => [z]) h1
  | [a], b :: b2 :: rb, _, _, hpa, _, h => by
    have h1 : a = key (b2 :: rb) ++ '.' :: b := h
    have ha : '.' ∉ a := dot_not_mem (List.all_eq_true.mp hpa a (List.Mem.head _))
    have h3 : '.' ∈ key (b2 :: rb) ++ '.' :: b := List.mem_append_right _ (List.Mem.head _)
    exact absurd (Eq.mpr (congrArg (fun (l : List Char) => '.' ∈ l) h1) h3) ha
  | a :: a2 :: ra, [b], _, _, _, hpb, h => by
    have h1 : key (a2 :: ra) ++ '.' :: a = b := h
    have hb : '.' ∉ b := dot_not_mem (List.all_eq_true.mp hpb b (List.Mem.head _))
    have h3 : '.' ∈ key (a2 :: ra) ++ '.' :: a := List.mem_append_right _ (List.Mem.head _)
    exact absurd (Eq.mp (congrArg (fun (l : List Char) => '.' ∈ l) h1) h3) hb
  | a :: a2 :: ra, b :: b2 :: rb, _, _, hpa, hpb, h => by
    have h1 : key (a2 :: ra) ++ '.' :: a = key (b2 :: rb) ++ '.' :: b := h
    have ha : '.' ∉ a := dot_not_mem (List.all_eq_true.mp hpa a (List.Mem.head _))
    have hb : '.' ∉ b := dot_not_mem (List.all_eq_true.mp hpb b (List.Mem.head _))
    obtain ⟨e1, e2⟩ := append_sep_inj _ _ a b ha hb h1
    have ih : a2 :: ra = b2 :: rb :=
      key_inj (a2 :: ra) (b2 :: rb) (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
        (all_tail hpa) (all_tail hpb) e1
    exact (congrArg (fun (z : List Char) => z :: a2 :: ra) e2).trans
      (congrArg (fun (z : CN) => b :: z) ih)

theorem okC_spec {A : CN} (h : okC A = true) : A ≠ [] ∧ A.all plainC = true := by
  have h' : (!A.isEmpty && A.all plainC) = true := h
  obtain ⟨h1, h2⟩ := and_tt h'
  refine ⟨?_, h2⟩
  intro e
  have h3 : A.isEmpty = false := not_tt h1
  have h4 : A.isEmpty = true := congrArg List.isEmpty e
  exact absurd (h4.symm.trans h3) (by decide)

/-- **Printing is injective on names with plain string components.** -/
theorem inj_of {A B : CN} (hA : okC A = true) (hB : okC B = true)
    (h : (nameOf A).toString = (nameOf B).toString) : A = B := by
  obtain ⟨a1, a2⟩ := okC_spec hA
  obtain ⟨b1, b2⟩ := okC_spec hB
  have k1 : stripL (nameOf A).toString.toList = key A :=
    cand_strip A a1 a2 _ (toString_mem (nameOf A))
  have k2 : stripL (nameOf B).toString.toList = key B :=
    cand_strip B b1 b2 _ (toString_mem (nameOf B))
  have k3 : stripL (nameOf A).toString.toList = stripL (nameOf B).toString.toList :=
    congrArg (fun (z : String) => stripL z.toList) h
  exact key_inj A B a1 b1 a2 b2 (k1.symm.trans (k3.trans k2))

/-- The structural test: both plain, and different. -/
def sepC (A B : CN) : Bool := okC A && okC B && decide (A ≠ B)

/-- **Separation by the structural test.** -/
theorem sepC_ne {A B : CN} (h : sepC A B = true) :
    (nameOf A).toString ≠ (nameOf B).toString := by
  have h' : (okC A && okC B && decide (A ≠ B)) = true := h
  obtain ⟨h12, h3⟩ := and_tt h'
  obtain ⟨h1, h2⟩ := and_tt h12
  exact fun heq => of_decide_eq_true h3 (inj_of h1 h2 heq)

/-- `hnames`, structurally: printing is injective on a list of plain names.
The check is linear in the list. -/
theorem hnames_of' (L : List CN) (h : (L.all okC) = true) :
    ∀ c ∈ L.map nameOf, ∀ c' ∈ L.map nameOf, c.toString = c'.toString → c = c' := by
  intro c hc c' hc' heq
  obtain ⟨A, hA, eA⟩ := List.mem_map.mp hc
  obtain ⟨B, hB, eB⟩ := List.mem_map.mp hc'
  have h0 : (nameOf A).toString = (nameOf B).toString :=
    (congrArg (fun (n : Lean.Name) => n.toString) eA).trans
      (heq.trans (congrArg (fun (n : Lean.Name) => n.toString) eB).symm)
  have e : A = B := inj_of (List.all_eq_true.mp h A hA) (List.all_eq_true.mp h B hB) h0
  exact eA.symm.trans ((congrArg nameOf e).trans eB)

/-- `hparent`, structurally. -/
theorem hparent_of' {α : Type} (insts : List (CN × α)) (parent : CN)
    (h : (insts.all fun c => sepC c.1 parent) = true) :
    ∀ c ∈ insts.map (fun c => (nameOf c.1, c.2)), c.1.toString ≠ (nameOf parent).toString := by
  intro c hc heq
  obtain ⟨d, hd, e⟩ := List.mem_map.mp hc
  have h1 : sepC d.1 parent = true := List.all_eq_true.mp h d hd
  have e1 : nameOf d.1 = c.1 := congrArg Prod.fst e
  have h2 : (nameOf d.1).toString = (nameOf parent).toString :=
    (congrArg (fun (n : Lean.Name) => n.toString) e1).trans heq
  exact sepC_ne h1 h2

/-- `c` prints differently from every declaration of `L`, structurally. -/
theorem not_mem_map_of' (c : CN) (L : List CN) (h : (L.all fun c' => sepC c c') = true) :
    (nameOf c).toString ∉ (L.map nameOf).map (fun n => n.toString) := by
  intro hm
  obtain ⟨n, hn, e1⟩ := List.mem_map.mp hm
  obtain ⟨B, hB, e2⟩ := List.mem_map.mp hn
  have h1 : sepC c B = true := List.all_eq_true.mp h B hB
  have e1' : n.toString = (nameOf c).toString := e1
  have h2 : (nameOf c).toString = (nameOf B).toString :=
    e1'.symm.trans (congrArg (fun (n : Lean.Name) => n.toString) e2).symm
  exact sepC_ne h1 h2

/-- No declaration of `L` prints as a declaration of `L'`, structurally. -/
theorem disjoint_map_of' (L L' : List CN)
    (h : (L.all fun c => L'.all fun c' => sepC c c') = true) :
    ∀ x ∈ (L.map nameOf).map (fun n => n.toString),
      x ∉ (L'.map nameOf).map (fun n => n.toString) := by
  intro x hx hx'
  obtain ⟨n, hn, e1⟩ := List.mem_map.mp hx
  obtain ⟨A, hA, e2⟩ := List.mem_map.mp hn
  have e1' : n.toString = x := e1
  have e3 : (nameOf A).toString = x :=
    (congrArg (fun (n : Lean.Name) => n.toString) e2).trans e1'
  have h0 : (L'.all fun c' => sepC A c') = true := List.all_eq_true.mp h A hA
  exact not_mem_map_of' A L' h0
    (Eq.mpr (congrArg (fun (z : String) => z ∈ (L'.map nameOf).map (fun n => n.toString)) e3) hx')

/-- The printed names of a list of plain names are pairwise distinct when
the names are. -/
theorem nodup_map_of' (L : List CN) (hnd : (L.map nameOf).Nodup) (h : (L.all okC) = true) :
    ((L.map nameOf).map (fun n => n.toString)).Nodup :=
  nodup_map_of_inj _ hnd (hnames_of' L h)

/-! ### On `Lean.Name`s directly -/

/-- The components of a name without numeric parts, last first. -/
def compsOf : Lean.Name → Option CN
  | .anonymous => some []
  | .str p s => (compsOf p).map fun r => s.toList :: r
  | .num _ _ => none

theorem nameOf_compsOf : ∀ (n : Lean.Name) (A : CN), compsOf n = some A → nameOf A = n
  | .anonymous, A, h => by
    have h1 : some ([] : CN) = some A := h
    cases h1
    rfl
  | .str p s, A, h => by
    have h1 : (compsOf p).map (fun r => s.toList :: r) = some A := h
    obtain ⟨R, hp, hR⟩ := Option.map_eq_some_iff.mp h1
    have ih : nameOf R = p := nameOf_compsOf p R hp
    have e1 : nameOf (s.toList :: R) = Lean.Name.str p s :=
      (congrArg (fun (q : Lean.Name) => Lean.Name.str q (String.ofList s.toList)) ih).trans
        (congrArg (fun (t : String) => Lean.Name.str p t) String.ofList_toList)
    exact (congrArg nameOf hR).symm.trans e1
  | .num _ _, A, h => by
    have h1 : (none : Option CN) = some A := h
    cases h1

/-- The test on two optional component lists. -/
def sepFastO : Option CN → Option CN → Bool
  | some A, some B => sepC A B
  | some _, none => false
  | none, some _ => false
  | none, none => false

theorem sepFastO_spec : ∀ (x y : Option CN), sepFastO x y = true →
    ∃ A B, x = some A ∧ y = some B ∧ sepC A B = true
  | some A, some B, h => ⟨A, B, rfl, rfl, h⟩
  | some _, none, h => by
    have h1 : false = true := h
    cases h1
  | none, some _, h => by
    have h1 : false = true := h
    cases h1
  | none, none, h => by
    have h1 : false = true := h
    cases h1

/-- The structural test on names: no numeric component, every component
plain, and the component lists differ. -/
def sepFast (a b : Lean.Name) : Bool := sepFastO (compsOf a) (compsOf b)

/-- **Separation of two names by the structural test.** -/
theorem sepFast_ne {a b : Lean.Name} (h : sepFast a b = true) : a.toString ≠ b.toString := by
  obtain ⟨A, B, ha, hb, hs⟩ := sepFastO_spec _ _ h
  have ea : nameOf A = a := nameOf_compsOf a A ha
  have eb : nameOf B = b := nameOf_compsOf b B hb
  intro heq
  have h2 : (nameOf A).toString = (nameOf B).toString :=
    (congrArg (fun (n : Lean.Name) => n.toString) ea).trans
      (heq.trans (congrArg (fun (n : Lean.Name) => n.toString) eb).symm)
  exact sepC_ne hs h2

end Tools.ShippingNameSep
