import Sparkle.IR.ModuleName
import Sparkle.Backend.Verilog

/-! # The module-name encoding is injective and survives the emitter

For `Sparkle.IR.ModuleName` (Finding H, ruling of 2026-10-13):

* `decode_encode : decode (encode k) = some k`, for every key;
* `encode_injective`, and its instances: `ofDecl_injective` (two
  declarations, whatever their names: `.anonymous`, `.str` / `.num`
  components, any character), `ofMem_injective`, `ofDecl_ne_ofMem`,
  `ofDecl_ne_aux`;
* the fast path: `plain_no_dollar` / `tagged_has_dollar` (the plain image
  and the tagged image are disjoint), `safe_ne_unsafe`, `safe_injective`;
* `sanitizeName_encode : sanitizeName (encode k) = encode k` — the
  emitter's normalisation is the identity on the image, so the composed map
  is injective too (`sanitized_injective`).

NOT here: legality of the image as a SystemVerilog identifier (first
character, keyword) is tested, not proved; that `encode (.decl n)` equals
what `sanitizeName n.toString` printed for a safe `n` is tested on the
corpus, not proved (`Name.toString` does not evaluate in the kernel); cache
coherence does NOT follow from name injectivity alone. -/
namespace Tools.ShippingModuleName
open Lean (Name)
open Sparkle.IR.ModuleName

/-! ## Split / join -/

theorem splitOn_ne_nil (d : Char) : ∀ (x : List Char), splitOn d x ≠ []
  | [] => List.cons_ne_nil _ _
  | c :: r => by
    show (if c = d then [] :: splitOn d r else consHead c (splitOn d r)) ≠ []
    by_cases hc : c = d
    · rw [if_pos hc]
      exact List.cons_ne_nil _ _
    · rw [if_neg hc]
      cases hs : splitOn d r with
      | nil => exact absurd hs (splitOn_ne_nil d r)
      | cons h t => exact List.cons_ne_nil (c :: h) t

theorem split_none (d : Char) : ∀ (a : List Char), d ∉ a → splitOn d a = [a]
  | [], _ => rfl
  | c :: a, h => by
    have hc : c ≠ d := fun e => h (List.mem_cons.mpr (Or.inl e.symm))
    have ha : d ∉ a := fun e => h (List.mem_cons.mpr (Or.inr e))
    show (if c = d then [] :: splitOn d a else consHead c (splitOn d a)) = [c :: a]
    rw [if_neg hc, split_none d a ha]
    all_goals rfl

theorem split_append (d : Char) : ∀ (a r : List Char), d ∉ a →
    splitOn d (a ++ d :: r) = a :: splitOn d r
  | [], r, _ => by
    show (if d = d then [] :: splitOn d r else consHead d (splitOn d r)) = [] :: splitOn d r
    rw [if_pos rfl]
  | c :: a, r, h => by
    have hc : c ≠ d := fun e => h (List.mem_cons.mpr (Or.inl e.symm))
    have ha : d ∉ a := fun e => h (List.mem_cons.mpr (Or.inr e))
    show (if c = d then [] :: splitOn d (a ++ d :: r)
      else consHead c (splitOn d (a ++ d :: r))) = (c :: a) :: splitOn d r
    rw [if_neg hc, split_append d a r ha]
    all_goals rfl

theorem split_cons_ne (d c : Char) (r : List Char) (hc : c ≠ d) :
    ∃ h t, splitOn d (c :: r) = (c :: h) :: t := by
  cases hs : splitOn d r with
  | nil => exact absurd hs (splitOn_ne_nil d r)
  | cons h t =>
    refine ⟨h, t, ?_⟩
    show (if c = d then [] :: splitOn d r else consHead c (splitOn d r)) = (c :: h) :: t
    rw [if_neg hc, hs]
    all_goals rfl

theorem join_consHead (d c : Char) : ∀ (ps : List (List Char)), ps ≠ [] →
    join d (consHead c ps) = c :: join d ps
  | [], h => absurd rfl h
  | [_], _ => rfl
  | _ :: _ :: _, _ => rfl

theorem join_split (d : Char) : ∀ (x : List Char), join d (splitOn d x) = x
  | [] => rfl
  | c :: r => by
    have ih := join_split d r
    show join d (if c = d then [] :: splitOn d r else consHead c (splitOn d r)) = c :: r
    by_cases hc : c = d
    · rw [if_pos hc]
      cases hs : splitOn d r with
      | nil => exact absurd hs (splitOn_ne_nil d r)
      | cons h t =>
        rw [hs] at ih
        show d :: join d (h :: t) = c :: r
        rw [ih, hc]
    · rw [if_neg hc, join_consHead d c _ (splitOn_ne_nil d r), ih]

theorem split_join (d : Char) (segs : List (List Char)) (hne : segs ≠ [])
    (hm : ∀ s, s ∈ segs → d ∉ s) : splitOn d (join d segs) = segs := by
  induction segs with
  | nil => exact absurd rfl hne
  | cons a t ih =>
    cases t with
    | nil => exact split_none d a (hm a (List.mem_cons.mpr (Or.inl rfl)))
    | cons b r =>
      have ih' := ih (List.cons_ne_nil b r) (fun s hs => hm s (List.mem_cons.mpr (Or.inr hs)))
      show splitOn d (a ++ d :: join d (b :: r)) = a :: b :: r
      rw [split_append d a _ (hm a (List.mem_cons.mpr (Or.inl rfl))), ih']

/-- The pieces of a joined list whose LAST element may contain `d`. -/
theorem split_join_last (d : Char) (last : List Char) (ns : List (List Char))
    (hm : ∀ s, s ∈ ns → d ∉ s) :
    splitOn d (join d (ns ++ [last])) = ns ++ splitOn d last := by
  induction ns with
  | nil => rfl
  | cons a t ih =>
    have ih' := ih (fun s hs => hm s (List.mem_cons.mpr (Or.inr hs)))
    have hj : join d ((a :: t) ++ [last]) = a ++ d :: join d (t ++ [last]) := by
      cases t <;> rfl
    rw [hj, split_append d a _ (hm a (List.mem_cons.mpr (Or.inl rfl))), ih']
    all_goals rfl

theorem mem_join {d x : Char} (segs : List (List Char)) (h : x ∈ join d segs) :
    x = d ∨ ∃ s, s ∈ segs ∧ x ∈ s := by
  induction segs with
  | nil =>
    have h' : x ∈ ([] : List Char) := h
    cases h'
  | cons a t ih =>
    cases t with
    | nil => exact Or.inr ⟨a, List.mem_cons.mpr (Or.inl rfl), h⟩
    | cons b r =>
      have h' : x ∈ a ++ d :: join d (b :: r) := h
      rcases List.mem_append.mp h' with ha | hb
      · exact Or.inr ⟨a, List.mem_cons.mpr (Or.inl rfl), ha⟩
      · rcases List.mem_cons.mp hb with hd | hr
        · exact Or.inl hd
        · rcases ih hr with h1 | ⟨s, hs, hx⟩
          · exact Or.inl h1
          · exact Or.inr ⟨s, List.mem_cons.mpr (Or.inr hs), hx⟩

/-! ## Characters -/

theorem alnum_ne_us {c : Char} (h : c.isAlphanum = true) : c ≠ '_' := by
  intro e
  subst e
  exact absurd h (by decide)

theorem alnum_ne_dollar {c : Char} (h : c.isAlphanum = true) : c ≠ '$' := by
  intro e
  subst e
  exact absurd h (by decide)

theorem last_char {x : Char} (h : (x.isAlphanum || x == '_') = true) :
    x.isAlphanum = true ∨ x = '_' := by
  cases ha : x.isAlphanum with
  | true => exact Or.inl rfl
  | false =>
    rw [ha] at h
    have h1 : (x == '_') = true := h
    exact Or.inr (eq_of_beq h1)

theorem low_not_up {c : Char} (h : isLow c = true) : isUp c = false := by
  have h1 : 97 ≤ c.toNat ∧ c.toNat ≤ 122 := of_decide_eq_true h
  have h2 : ¬ (65 ≤ c.toNat ∧ c.toNat ≤ 90) := fun h3 => by omega
  exact decide_eq_false h2

/-! ## Decimal numbers -/

theorem digit_val : ∀ (d : Nat), d < 10 → digitVal (digitChar d) = d
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | 8, _ => by decide
  | 9, _ => by decide
  | d + 10, h => absurd h (by omega)

theorem digit_alnum : ∀ (d : Nat), d < 10 → (digitChar d).isAlphanum = true
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | 8, _ => by decide
  | 9, _ => by decide
  | d + 10, h => absurd h (by omega)

theorem undigs_append : ∀ (a b : List Nat) (acc : Nat),
    undigs acc (a ++ b) = undigs (undigs acc a) b
  | [], _, _ => rfl
  | d :: a, b, acc => undigs_append a b (acc * 10 + d)

theorem undigs_digsF : ∀ (f n : Nat), n < f → undigs 0 (digsF f n) = n
  | 0, n, h => absurd h (Nat.not_lt_zero n)
  | f + 1, n, h => by
    show undigs 0 (if n < 10 then [n] else digsF f (n / 10) ++ [n % 10]) = n
    by_cases hn : n < 10
    · rw [if_pos hn]
      show 0 * 10 + n = n
      omega
    · rw [if_neg hn, undigs_append, undigs_digsF f (n / 10) (by omega)]
      show n / 10 * 10 + n % 10 = n
      omega

theorem digsF_lt : ∀ (f n d : Nat), d ∈ digsF f n → d < 10
  | 0, _, d, h => by
    have h' : d ∈ [0] := h
    rcases List.mem_cons.mp h' with e | e
    · omega
    · cases e
  | f + 1, n, d, h => by
    have h' : d ∈ (if n < 10 then [n] else digsF f (n / 10) ++ [n % 10]) := h
    by_cases hn : n < 10
    · rw [if_pos hn] at h'
      rcases List.mem_cons.mp h' with e | e
      · omega
      · cases e
    · rw [if_neg hn] at h'
      rcases List.mem_append.mp h' with e | e
      · exact digsF_lt f (n / 10) d e
      · rcases List.mem_cons.mp e with e | e
        · omega
        · cases e

theorem digsF_ne_nil : ∀ (f n : Nat), digsF f n ≠ []
  | 0, _ => List.cons_ne_nil 0 []
  | f + 1, n => by
    show (if n < 10 then [n] else digsF f (n / 10) ++ [n % 10]) ≠ []
    by_cases hn : n < 10
    · rw [if_pos hn]
      exact List.cons_ne_nil _ _
    · rw [if_neg hn]
      intro e
      have h1 := congrArg List.length e
      rw [List.length_append] at h1
      have h2 : (digsF f (n / 10)).length + 1 = 0 := h1
      omega

theorem map_val_chr : ∀ (l : List Nat), (∀ d, d ∈ l → d < 10) →
    (l.map digitChar).map digitVal = l
  | [], _ => rfl
  | d :: l, h => by
    show digitVal (digitChar d) :: (l.map digitChar).map digitVal = d :: l
    rw [digit_val d (h d (List.mem_cons.mpr (Or.inl rfl))),
      map_val_chr l (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))]

theorem natOfChars_natChars (n : Nat) : natOfChars (natChars n) = n := by
  show undigs 0 (((digsF (n + 1) n).map digitChar).map digitVal) = n
  rw [map_val_chr (digsF (n + 1) n) (fun d hd => digsF_lt (n + 1) n d hd)]
  exact undigs_digsF (n + 1) n (Nat.lt_succ_self n)

theorem natChars_alnum (n : Nat) (x : Char) (hx : x ∈ natChars n) : x.isAlphanum = true := by
  have hx' : x ∈ (digsF (n + 1) n).map digitChar := hx
  obtain ⟨d, hd, e⟩ := List.mem_map.mp hx'
  rw [← e]
  exact digit_alnum d (digsF_lt _ _ d hd)

theorem natChars_ne_nil (n : Nat) : natChars n ≠ [] := by
  intro e
  have e' : (digsF (n + 1) n).map digitChar = [] := e
  have h1 := congrArg List.length e'
  rw [List.length_map] at h1
  exact digsF_ne_nil (n + 1) n (List.eq_nil_of_length_eq_zero h1)

/-! ## One string component -/

theorem charOf_codeOf (c : Char) : charOf (codeOf c) = c := by
  unfold charOf codeOf
  by_cases hc : c = '_'
  · rw [if_pos hc, if_pos rfl]
    exact hc.symm
  · rw [if_neg hc, if_neg (natChars_ne_nil c.toNat), natOfChars_natChars, Char.ofNat_toNat]

theorem codeOf_alnum (c x : Char) (h : x ∈ codeOf c) : x.isAlphanum = true := by
  unfold codeOf at h
  by_cases hc : c = '_'
  · rw [if_pos hc] at h
    cases h
  · rw [if_neg hc] at h
    exact natChars_alnum _ x h

theorem length_consHead (c : Char) : ∀ (ps : List (List Char)),
    (consHead c ps).length = ps.length
  | [] => rfl
  | _ :: _ => rfl

theorem mem_consHead {c : Char} {p : List Char} : ∀ (ps : List (List Char)),
    p ∈ consHead c ps → (∃ h, h ∈ ps ∧ p = c :: h) ∨ p ∈ ps
  | [], h => by
    have h' : p ∈ ([] : List (List Char)) := h
    cases h'
  | h0 :: t, h => by
    have h' : p ∈ (c :: h0) :: t := h
    rcases List.mem_cons.mp h' with e | e
    · exact Or.inl ⟨h0, List.mem_cons.mpr (Or.inl rfl), e⟩
    · exact Or.inr (List.mem_cons.mpr (Or.inr e))

theorem unpieces_consHead (c : Char) : ∀ (ps : List (List Char)),
    unpieces (consHead c ps) = (unpieces ps).map (fun r => c :: r)
  | [] => rfl
  | [_] => rfl
  | h :: code :: rest => by
    show (unpieces rest).map (fun r => (c :: h) ++ charOf code :: r) =
      ((unpieces rest).map (fun r => h ++ charOf code :: r)).map (fun r => c :: r)
    cases unpieces rest <;> rfl

theorem pieces_ne_nil : ∀ (s : List Char), pieces s ≠ []
  | [] => List.cons_ne_nil _ _
  | c :: s => by
    show (if c.isAlphanum = true then consHead c (pieces s)
      else [] :: codeOf c :: pieces s) ≠ []
    by_cases hc : c.isAlphanum = true
    · rw [if_pos hc]
      cases hp : pieces s with
      | nil => exact absurd hp (pieces_ne_nil s)
      | cons h t => exact List.cons_ne_nil (c :: h) t
    · rw [if_neg hc]
      exact List.cons_ne_nil _ _

theorem pieces_odd : ∀ (s : List Char), (pieces s).length % 2 = 1
  | [] => rfl
  | c :: s => by
    have ih := pieces_odd s
    show (if c.isAlphanum = true then consHead c (pieces s)
      else [] :: codeOf c :: pieces s).length % 2 = 1
    by_cases hc : c.isAlphanum = true
    · rw [if_pos hc, length_consHead]
      exact ih
    · rw [if_neg hc]
      show ((pieces s).length + 1 + 1) % 2 = 1
      omega

theorem pieces_alnum : ∀ (s p : List Char), p ∈ pieces s → ∀ (x : Char), x ∈ p →
    x.isAlphanum = true
  | [], p, hp, x, hx => by
    have hp' : p ∈ [([] : List Char)] := hp
    rcases List.mem_cons.mp hp' with e | e
    · rw [e] at hx
      cases hx
    · cases e
  | c :: s, p, hp, x, hx => by
    have hp' : p ∈ (if c.isAlphanum = true then consHead c (pieces s)
      else [] :: codeOf c :: pieces s) := hp
    by_cases hc : c.isAlphanum = true
    · rw [if_pos hc] at hp'
      rcases mem_consHead (pieces s) hp' with ⟨h, hh, e⟩ | hin
      · rw [e] at hx
        rcases List.mem_cons.mp hx with e1 | e1
        · rw [e1]
          exact hc
        · exact pieces_alnum s h hh x e1
      · exact pieces_alnum s p hin x hx
    · rw [if_neg hc] at hp'
      rcases List.mem_cons.mp hp' with e | hp2
      · rw [e] at hx
        cases hx
      · rcases List.mem_cons.mp hp2 with e | hin
        · rw [e] at hx
          exact codeOf_alnum c x hx
        · exact pieces_alnum s p hin x hx

theorem unpieces_pieces : ∀ (s : List Char), unpieces (pieces s) = some s
  | [] => rfl
  | c :: s => by
    have ih := unpieces_pieces s
    show unpieces (if c.isAlphanum = true then consHead c (pieces s)
      else [] :: codeOf c :: pieces s) = some (c :: s)
    by_cases hc : c.isAlphanum = true
    · rw [if_pos hc, unpieces_consHead, ih]
      all_goals rfl
    · rw [if_neg hc]
      show (unpieces (pieces s)).map (fun r => [] ++ charOf (codeOf c) :: r) = some (c :: s)
      rw [ih, charOf_codeOf]
      all_goals rfl

theorem split_encStr (s : List Char) : splitOn '_' (encStr s) = pieces s :=
  split_join '_' (pieces s) (pieces_ne_nil s)
    (fun p hp hu => alnum_ne_us (pieces_alnum s p hp '_' hu) rfl)

/-- Every character of an encoded string component: a letter, a digit or `_`. -/
theorem encStr_chars (s : List Char) (x : Char) (h : x ∈ encStr s) :
    x.isAlphanum = true ∨ x = '_' := by
  rcases mem_join (pieces s) h with e | ⟨p, hp, hx⟩
  · exact Or.inr e
  · exact Or.inl (pieces_alnum s p hp x hx)

/-! ## Components and fields -/

theorem encComp_chars (c : Comp) (x : Char) (h : x ∈ encComp c) :
    x.isAlphanum = true ∨ x = '_' := by
  cases c with
  | str s => exact encStr_chars s x h
  | num n =>
    have h' : x ∈ '_' :: natChars n := h
    rcases List.mem_cons.mp h' with e | e
    · exact Or.inr e
    · exact Or.inl (natChars_alnum n x e)

theorem encComp_no_dollar (c : Comp) : '$' ∉ encComp c := by
  intro h
  rcases encComp_chars c '$' h with e | e
  · exact absurd e (by decide)
  · exact absurd e (by decide)

theorem decPs_odd : ∀ (ps : List (List Char)), ps.length % 2 = 1 →
    decPs ps = (unpieces ps).map Comp.str
  | [], h => by
    have h' : 0 % 2 = 1 := h
    omega
  | [_], _ => rfl
  | [_, _], h => by
    have h' : 2 % 2 = 1 := h
    omega
  | _ :: _ :: _ :: _, _ => rfl

theorem decComp_enc : ∀ (c : Comp), decComp (encComp c) = some c
  | .str s => by
    show decPs (splitOn '_' (encStr s)) = some (Comp.str s)
    rw [split_encStr, decPs_odd _ (pieces_odd s), unpieces_pieces]
    all_goals rfl
  | .num n => by
    have h : splitOn '_' ('_' :: natChars n) = [[], natChars n] := by
      have h1 : splitOn '_' ([] ++ '_' :: natChars n) = [] :: splitOn '_' (natChars n) :=
        split_append '_' [] (natChars n) (fun e => by cases e)
      have h2 : splitOn '_' (natChars n) = [natChars n] :=
        split_none '_' (natChars n) (fun e => alnum_ne_us (natChars_alnum n '_' e) rfl)
      rw [h2] at h1
      exact h1
    show decPs (splitOn '_' ('_' :: natChars n)) = some (Comp.num n)
    rw [h]
    show some (Comp.num (natOfChars (natChars n))) = some (Comp.num n)
    rw [natOfChars_natChars]

theorem decAll_enc : ∀ (cs : List Comp), decAll (cs.map encComp) = some cs
  | [] => rfl
  | c :: cs => by
    show (decComp (encComp c)).bind
      (fun x => (decAll (cs.map encComp)).map (fun r => x :: r)) = some (c :: cs)
    rw [decComp_enc, decAll_enc cs]
    all_goals rfl

theorem nameOfRev_compsRev : ∀ (n : Name), nameOfRev (compsRev n) = n
  | .anonymous => rfl
  | .str p s => by
    show Name.str (nameOfRev (compsRev p)) (String.ofList s.toList) = Name.str p s
    rw [nameOfRev_compsRev p, String.ofList_toList]
  | .num p k => by
    show Name.num (nameOfRev (compsRev p)) k = Name.num p k
    rw [nameOfRev_compsRev p]

theorem compsRev_of_strComps : ∀ (n : Name) (l : List (List Char)), strComps n = some l →
    compsRev n = l.map Comp.str
  | .anonymous, l, h => by
    have h' : some ([] : List (List Char)) = some l := h
    cases h'
    rfl
  | .str p s, l, h => by
    have h' : (strComps p).map (fun r => s.toList :: r) = some l := h
    cases hp : strComps p with
    | none =>
      rw [hp] at h'
      have h2 : (none : Option (List (List Char))) = some l := h'
      cases h2
    | some l' =>
      rw [hp] at h'
      have h2 : some (s.toList :: l') = some l := h'
      cases h2
      show Comp.str s.toList :: compsRev p = Comp.str s.toList :: l'.map Comp.str
      rw [compsRev_of_strComps p l' hp]
  | .num _ _, l, h => by
    have h' : (none : Option (List (List Char))) = some l := h
    cases h'

/-! ## The tagged form -/

theorem split_tagged (k : Char) (hk : k ≠ '$') (cs : List Comp) :
    splitOn '$' (tagged k cs) = spHead :: [k] :: cs.map encComp :=
  split_join '$' (spHead :: [k] :: cs.map encComp) (List.cons_ne_nil _ _) (by
    intro s hs hd
    rcases List.mem_cons.mp hs with e | hs1
    · rw [e] at hd
      exact absurd hd (by decide)
    · rcases List.mem_cons.mp hs1 with e | hs2
      · rw [e] at hd
        rcases List.mem_cons.mp hd with e1 | e1
        · exact hk e1.symm
        · cases e1
      · obtain ⟨c, _, e⟩ := List.mem_map.mp hs2
        rw [← e] at hd
        exact encComp_no_dollar c hd)

theorem tagged_has_dollar (k : Char) (cs : List Comp) : '$' ∈ tagged k cs := by
  show '$' ∈ spHead ++ '$' :: join '$' ([k] :: cs.map encComp)
  exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

theorem decTop_tagged_D (n : Name) :
    decTop (splitOn '$' (tagged 'D' (compsRev n).reverse)) = some (Key.decl n) := by
  rw [split_tagged 'D' (by decide) _]
  show (decAll ((compsRev n).reverse.map encComp)).bind (decKey ['D']) = some (Key.decl n)
  rw [decAll_enc]
  show decKey ['D'] (compsRev n).reverse = some (Key.decl n)
  unfold decKey
  rw [if_pos rfl, List.reverse_reverse, nameOfRev_compsRev]

theorem decTop_tagged_X (n : Name) :
    decTop (splitOn '$' (tagged 'X' (compsRev n).reverse)) = some (Key.aux n) := by
  rw [split_tagged 'X' (by decide) _]
  show (decAll ((compsRev n).reverse.map encComp)).bind (decKey ['X']) = some (Key.aux n)
  rw [decAll_enc]
  show decKey ['X'] (compsRev n).reverse = some (Key.aux n)
  unfold decKey
  rw [if_neg (show ¬ (['X'] = ['D']) by decide), if_pos rfl, List.reverse_reverse,
    nameOfRev_compsRev]

/-! ## The plain form -/

/-- What "safe" means, as facts about the components. -/
structure Plain (ns : List (List Char)) (last : List Char) : Prop where
  upper : ∀ s, s ∈ ns → startsUpper s = true
  alnum : ∀ s, s ∈ ns → ∀ (x : Char), x ∈ s → x.isAlphanum = true
  notMem : ∀ s, s ∈ ns → s ≠ memHead
  lower : startsLower last = true
  lastChars : ∀ (x : Char), x ∈ last → x.isAlphanum = true ∨ x = '_'

theorem nsOk_spec {s : List Char} (h : nsOk s = true) :
    startsUpper s = true ∧ (∀ (x : Char), x ∈ s → x.isAlphanum = true) ∧ s ≠ memHead := by
  simp only [nsOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, List.all_eq_true.mp h.1.2, h.2⟩

theorem lastOk_spec {s : List Char} (h : lastOk s = true) :
    startsLower s = true ∧ ∀ (x : Char), x ∈ s → x.isAlphanum = true ∨ x = '_' := by
  simp only [lastOk, Bool.and_eq_true] at h
  exact ⟨h.1, fun x hx => last_char (List.all_eq_true.mp h.2 x hx)⟩

theorem safeOk_spec {nsRev : List (List Char)} {last : List Char}
    (h : safeOk nsRev last = true) : Plain nsRev.reverse last := by
  simp only [safeOk, Bool.and_eq_true] at h
  have hl := lastOk_spec h.1.1
  have hn : ∀ s, s ∈ nsRev.reverse → nsOk s = true :=
    fun s hs => List.all_eq_true.mp h.1.2 s (List.mem_reverse.mp hs)
  exact ⟨(fun s hs => (nsOk_spec (hn s hs)).1), (fun s hs => (nsOk_spec (hn s hs)).2.1),
    (fun s hs => (nsOk_spec (hn s hs)).2.2), (hl.1), (hl.2)⟩

theorem safeOf_spec : ∀ (o : Option (List (List Char))) (ns : List (List Char))
    (last : List Char), safeOf o = some (ns, last) →
    o = some (last :: ns.reverse) ∧ Plain ns last
  | none, ns, last, h => by
    have h' : (none : Option (List (List Char) × List Char)) = some (ns, last) := h
    cases h'
  | some [], ns, last, h => by
    have h' : (none : Option (List (List Char) × List Char)) = some (ns, last) := h
    cases h'
  | some (last' :: nsRev), ns, last, h => by
    have h' : (if safeOk nsRev last' = true then some (nsRev.reverse, last') else none) =
        some (ns, last) := h
    by_cases hk : safeOk nsRev last' = true
    · rw [if_pos hk] at h'
      cases h'
      exact ⟨by rw [List.reverse_reverse], safeOk_spec hk⟩
    · rw [if_neg hk] at h'
      cases h'

/-- A safe name: its string components, and the facts. -/
theorem safeName_spec {n : Name} {ns : List (List Char)} {last : List Char}
    (h : safeName n = some (ns, last)) :
    compsRev n = (last :: ns.reverse).map Comp.str ∧ Plain ns last :=
  have h1 := safeOf_spec (strComps n) ns last h
  ⟨compsRev_of_strComps n _ h1.1, h1.2⟩

/-- **The plain image has no `$`.** -/
theorem plain_no_dollar {ns : List (List Char)} {last : List Char} (hp : Plain ns last) :
    '$' ∉ plainL ns last := by
  intro h
  rcases mem_join (ns ++ [last]) h with e | ⟨s, hs, hx⟩
  · exact absurd e (by decide)
  · rcases List.mem_append.mp hs with hs1 | hs1
    · exact alnum_ne_dollar (hp.alnum s hs1 '$' hx) rfl
    · rcases List.mem_cons.mp hs1 with e | e
      · rw [e] at hx
        rcases hp.lastChars '$' hx with e1 | e1
        · exact absurd e1 (by decide)
        · exact absurd e1 (by decide)
      · cases e

theorem regroup_append (toks : List (List Char)) (ns : List (List Char))
    (hu : ∀ s, s ∈ ns → startsUpper s = true) : regroup (ns ++ toks) = ns ++ regroup toks := by
  induction ns with
  | nil => rfl
  | cons a t ih =>
    show (if startsUpper a = true then a :: regroup (t ++ toks)
      else [join '_' (a :: (t ++ toks))]) = (a :: t) ++ regroup toks
    rw [if_pos (hu a (List.mem_cons.mpr (Or.inl rfl))),
      ih (fun s hs => hu s (List.mem_cons.mpr (Or.inr hs)))]
    all_goals rfl

/-- The pieces of a lower-case-initial component: the first is not
upper-case-initial, and regrouping gives the component back. -/
theorem regroup_last {last : List Char} (hl : startsLower last = true) :
    regroup (splitOn '_' last) = [last] ∧
    ∃ h t, splitOn '_' last = h :: t ∧ startsUpper h = false := by
  cases last with
  | nil =>
    have h' : false = true := hl
    cases h'
  | cons c rest =>
    have hlow : isLow c = true := hl
    have hc : c ≠ '_' := by
      intro e
      rw [e] at hlow
      exact absurd hlow (by decide)
    obtain ⟨h, t, e⟩ := split_cons_ne '_' c rest hc
    have hup : startsUpper (c :: h) = false := low_not_up hlow
    refine ⟨?_, (c :: h), t, e, hup⟩
    have hj := join_split '_' (c :: rest)
    rw [e] at hj
    rw [e]
    show (if startsUpper (c :: h) = true then (c :: h) :: regroup t
      else [join '_' ((c :: h) :: t)]) = [c :: rest]
    have hnu : ¬ (startsUpper (c :: h) = true) := by
      rw [hup]
      exact Bool.false_ne_true
    rw [if_neg hnu, hj]

theorem memHead_upper : startsUpper memHead = true := by decide

/-- The `_`-pieces of a plain name: not headed by `SparkleMem`, and
regrouping gives the components back. -/
theorem plain_pieces {ns : List (List Char)} {last : List Char} (hp : Plain ns last) :
    regroup (splitOn '_' (plainL ns last)) = ns ++ [last] ∧
    ∃ h t, splitOn '_' (plainL ns last) = h :: t ∧ h ≠ memHead := by
  have hs : splitOn '_' (plainL ns last) = ns ++ splitOn '_' last :=
    split_join_last '_' last ns (fun s hs hu => alnum_ne_us (hp.alnum s hs '_' hu) rfl)
  obtain ⟨hr, h, t, e, hup⟩ := regroup_last hp.lower
  refine ⟨?_, ?_⟩
  · rw [hs, regroup_append _ ns hp.upper, hr]
  · cases ns with
    | nil =>
      refine ⟨h, t, ?_, ?_⟩
      · rw [hs]
        exact e
      · intro e1
        rw [e1, memHead_upper] at hup
        exact absurd hup (by decide)
    | cons a r =>
      refine ⟨a, r ++ splitOn '_' last, hs, ?_⟩
      exact hp.notMem a (List.mem_cons.mpr (Or.inl rfl))

theorem decTop_plain {ns : List (List Char)} {last : List Char} (hp : Plain ns last) :
    decTop (splitOn '$' (plainL ns last)) =
      some (Key.decl (nameOfRev ((last :: ns.reverse).map Comp.str))) := by
  rw [split_none '$' _ (plain_no_dollar hp)]
  show decPlain (splitOn '_' (plainL ns last)) = _
  obtain ⟨hr, h, t, e, hne⟩ := plain_pieces hp
  have hrev : (ns ++ [last]).reverse = last :: ns.reverse := by
    rw [List.reverse_append]
    all_goals rfl
  rw [e] at hr
  rw [e]
  show (if h = memHead then decMem (h :: t)
    else some (Key.decl (nameOfRev ((regroup (h :: t)).reverse.map Comp.str)))) = _
  rw [if_neg hne, hr, hrev]

/-! ## The memory form -/

theorem memHead_alnum : memHead.all Char.isAlphanum = true := by decide
theorem comboL_alnum : comboL.all Char.isAlphanum = true := by decide
theorem syncL_alnum : syncL.all Char.isAlphanum = true := by decide

theorem kindOf_memKind : ∀ (c : Bool), kindOf (memKind c) = some c
  | true => by decide
  | false => by decide

theorem mem_segs_alnum (c : Bool) (a d : Nat) : ∀ s,
    s ∈ [memHead, memKind c, natChars a, natChars d] → ∀ (x : Char), x ∈ s →
    x.isAlphanum = true := by
  intro s hs x hx
  rcases List.mem_cons.mp hs with e | hs1
  · rw [e] at hx
    exact List.all_eq_true.mp memHead_alnum x hx
  · rcases List.mem_cons.mp hs1 with e | hs2
    · rw [e] at hx
      cases c with
      | true => exact List.all_eq_true.mp comboL_alnum x hx
      | false => exact List.all_eq_true.mp syncL_alnum x hx
    · rcases List.mem_cons.mp hs2 with e | hs3
      · rw [e] at hx
        exact natChars_alnum a x hx
      · rcases List.mem_cons.mp hs3 with e | hs4
        · rw [e] at hx
          exact natChars_alnum d x hx
        · cases hs4

theorem memL_no_dollar (c : Bool) (a d : Nat) : '$' ∉ memL c a d := by
  intro h
  rcases mem_join [memHead, memKind c, natChars a, natChars d] h with e | ⟨s, hs, hx⟩
  · exact absurd e (by decide)
  · exact alnum_ne_dollar (mem_segs_alnum c a d s hs '$' hx) rfl

theorem decTop_mem (c : Bool) (a d : Nat) :
    decTop (splitOn '$' (memL c a d)) = some (Key.mem c a d) := by
  rw [split_none '$' _ (memL_no_dollar c a d)]
  show decPlain (splitOn '_' (join '_' [memHead, memKind c, natChars a, natChars d])) = _
  rw [split_join '_' [memHead, memKind c, natChars a, natChars d] (List.cons_ne_nil _ _)
    (fun s hs hu => alnum_ne_us (mem_segs_alnum c a d s hs '_' hu) rfl)]
  have hP : decPlain [memHead, memKind c, natChars a, natChars d] =
      decMem [memHead, memKind c, natChars a, natChars d] := by
    show (if memHead = memHead then decMem [memHead, memKind c, natChars a, natChars d]
      else some (Key.decl (nameOfRev
        ((regroup [memHead, memKind c, natChars a, natChars d]).reverse.map Comp.str)))) = _
    rw [if_pos rfl]
  rw [hP]
  show (kindOf (memKind c)).map
    (fun c' => Key.mem c' (natOfChars (natChars a)) (natOfChars (natChars d))) =
      some (Key.mem c a d)
  rw [kindOf_memKind, natOfChars_natChars, natOfChars_natChars]
  all_goals rfl

/-! ## The theorems -/

theorem encDeclL_safe {n : Name} {ns : List (List Char)} {last : List Char}
    (h : safeName n = some (ns, last)) : encodeL (Key.decl n) = plainL ns last := by
  show encDeclL n = plainL ns last
  unfold encDeclL
  rw [h]
  all_goals rfl

theorem encDeclL_unsafe {n : Name} (h : safeName n = none) :
    encodeL (Key.decl n) = tagged 'D' (compsRev n).reverse := by
  show encDeclL n = tagged 'D' (compsRev n).reverse
  unfold encDeclL
  rw [h]
  all_goals rfl

theorem decTop_encodeL : ∀ (k : Key), decTop (splitOn '$' (encodeL k)) = some k
  | .decl n => by
    cases hs : safeName n with
    | none =>
      rw [encDeclL_unsafe hs]
      exact decTop_tagged_D n
    | some p =>
      obtain ⟨ns, last⟩ := p
      obtain ⟨hc, hp⟩ := safeName_spec hs
      rw [encDeclL_safe hs, decTop_plain hp, ← hc, nameOfRev_compsRev]
  | .mem c a d => decTop_mem c a d
  | .aux n => decTop_tagged_X n

/-- **Reading back.** -/
theorem decode_encode (k : Key) : decode (encode k) = some k := by
  show decTop (splitOn '$' (String.ofList (encodeL k)).toList) = some k
  rw [String.toList_ofList]
  exact decTop_encodeL k

/-- **The encoding is injective**: across the tags, and within each. -/
theorem encode_injective {a b : Key} (h : encode a = encode b) : a = b := by
  have h1 : decode (encode a) = decode (encode b) := congrArg decode h
  rw [decode_encode, decode_encode] at h1
  exact Option.some.inj h1

/-- Two declarations have one module name only if they are one declaration
(any `Lean.Name`: anonymous, numeric components, any character). -/
theorem ofDecl_injective {a b : Name} (h : ofDecl a = ofDecl b) : a = b :=
  Key.decl.inj (encode_injective h)

theorem ofDecl_ne {a b : Name} (h : a ≠ b) : ofDecl a ≠ ofDecl b :=
  fun e => h (ofDecl_injective e)

theorem ofMem_injective {c c' : Bool} {a d a' d' : Nat} (h : ofMem c a d = ofMem c' a' d') :
    c = c' ∧ a = a' ∧ d = d' :=
  Key.mem.inj (encode_injective h)

/-- No declaration — whatever its name, `SparkleMem_combo_4_8` included —
has the name of a memory module. -/
theorem ofDecl_ne_ofMem (n : Name) (c : Bool) (a d : Nat) : ofDecl n ≠ ofMem c a d := by
  intro e
  have h : Key.decl n = Key.mem c a d := encode_injective e
  cases h

theorem ofDecl_ne_aux (n n' : Name) : ofDecl n ≠ encode (Key.aux n') := by
  intro e
  have h : Key.decl n = Key.aux n' := encode_injective e
  cases h

theorem ofMem_ne_aux (c : Bool) (a d : Nat) (n : Name) :
    ofMem c a d ≠ encode (Key.aux n) := by
  intro e
  have h : Key.mem c a d = Key.aux n := encode_injective e
  cases h

/-! ## The fast path, explicitly -/

/-- **The safe image and the tagged image are disjoint**: a safe
declaration and an unsafe one never share a module name. -/
theorem safe_ne_unsafe {a b : Name} (ha : isSafe a = true) (hb : isSafe b = false) :
    ofDecl a ≠ ofDecl b := by
  intro e
  have hab : a = b := ofDecl_injective e
  rw [hab, hb] at ha
  exact absurd ha (by decide)

/-- The same by the characters: the name of a safe declaration has no `$`,
the name of an unsafe one has. -/
theorem safe_no_dollar {n : Name} (h : isSafe n = true) : '$' ∉ encodeL (Key.decl n) := by
  cases hs : safeName n with
  | none =>
    have h' : (safeName n).isSome = true := h
    rw [hs] at h'
    have h2 : false = true := h'
    cases h2
  | some p =>
    obtain ⟨ns, last⟩ := p
    rw [encDeclL_safe hs]
    exact plain_no_dollar (safeName_spec hs).2

theorem unsafe_has_dollar {n : Name} (h : isSafe n = false) : '$' ∈ encodeL (Key.decl n) := by
  cases hs : safeName n with
  | none =>
    rw [encDeclL_unsafe hs]
    exact tagged_has_dollar _ _
  | some p =>
    have h' : (safeName n).isSome = false := h
    rw [hs] at h'
    have h2 : true = false := h'
    cases h2

/-- **The fast path is injective on safe names** (an instance of
`ofDecl_injective`, stated for the record). -/
theorem safe_injective {a b : Name} (_ha : isSafe a = true) (_hb : isSafe b = true)
    (h : ofDecl a = ofDecl b) : a = b :=
  ofDecl_injective h

/-! ## The emitter -/

/-- Every character of an encoded name is one `sanitizeName` keeps. -/
theorem ok_of {x : Char} (h : x.isAlphanum = true ∨ x = '_' ∨ x = '$') :
    Sparkle.IR.NameHints.charOk x = true := by
  rcases h with h | h | h
  · show (x.isAlphanum || x == '_' || x == '$') = true
    rw [h]
    all_goals rfl
  · rw [h]
    decide
  · rw [h]
    decide

theorem tagged_chars (k : Char) (hk : k.isAlphanum = true) (cs : List Comp) (x : Char)
    (h : x ∈ tagged k cs) : x.isAlphanum = true ∨ x = '_' ∨ x = '$' := by
  rcases mem_join (spHead :: [k] :: cs.map encComp) h with e | ⟨s, hs, hx⟩
  · exact Or.inr (Or.inr e)
  · rcases List.mem_cons.mp hs with e | hs1
    · rw [e] at hx
      exact Or.inl (List.all_eq_true.mp (by decide : spHead.all Char.isAlphanum = true) x hx)
    · rcases List.mem_cons.mp hs1 with e | hs2
      · rw [e] at hx
        rcases List.mem_cons.mp hx with e1 | e1
        · rw [e1]
          exact Or.inl hk
        · cases e1
      · obtain ⟨c, _, e⟩ := List.mem_map.mp hs2
        rw [← e] at hx
        rcases encComp_chars c x hx with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)

theorem encodeL_chars : ∀ (k : Key) (x : Char), x ∈ encodeL k →
    x.isAlphanum = true ∨ x = '_' ∨ x = '$'
  | .decl n, x, h => by
    cases hs : safeName n with
    | none =>
      rw [encDeclL_unsafe hs] at h
      exact tagged_chars 'D' (by decide) _ x h
    | some p =>
      obtain ⟨ns, last⟩ := p
      rw [encDeclL_safe hs] at h
      have hp := (safeName_spec hs).2
      rcases mem_join (ns ++ [last]) h with e | ⟨s, hs1, hx⟩
      · exact Or.inr (Or.inl e)
      · rcases List.mem_append.mp hs1 with hs2 | hs2
        · exact Or.inl (hp.alnum s hs2 x hx)
        · rcases List.mem_cons.mp hs2 with e | e
          · rw [e] at hx
            rcases hp.lastChars x hx with h1 | h1
            · exact Or.inl h1
            · exact Or.inr (Or.inl h1)
          · cases e
  | .mem c a d, x, h => by
    rcases mem_join [memHead, memKind c, natChars a, natChars d] h with e | ⟨s, hs, hx⟩
    · exact Or.inr (Or.inl e)
    · exact Or.inl (mem_segs_alnum c a d s hs x hx)
  | .aux n, x, h => tagged_chars 'X' (by decide) _ x h

theorem encode_clean (k : Key) : Sparkle.IR.NameHints.Clean (encode k) := by
  intro c hc
  have hc' : c ∈ (String.ofList (encodeL k)).toList := hc
  rw [String.toList_ofList] at hc'
  exact ok_of (encodeL_chars k c hc')

/-- **The emitter's normalisation is the identity on the image.** (The proof
is `Tools.ShippingSVBridge.sanitizeName_of_clean`'s, repeated here so that
this file imports only the encoding and the emitter.) -/
theorem sanitizeName_encode (k : Key) :
    Sparkle.Backend.Verilog.sanitizeName (encode k) = encode k := by
  have ha : (encode k).all Sparkle.IR.NameHints.charOk = true := by
    simpa [Sparkle.IR.NameHints.Clean, String.all_bool_eq] using encode_clean k
  simpa [Sparkle.Backend.Verilog.sanitizeName, Sparkle.IR.NameHints.charOk] using
    (if_pos ha : (if (encode k).all Sparkle.IR.NameHints.charOk = true then encode k else
      (encode k).replace "." "_" |>.replace "-" "_" |>.replace " " "_"
        |>.replace "'" "_prime" |>.replace "#" "") = encode k)

/-- **Injectivity survives the emitter**: the names the emitter prints for
two keys are equal only if the keys are. -/
theorem sanitized_injective {a b : Key}
    (h : Sparkle.Backend.Verilog.sanitizeName (encode a) =
      Sparkle.Backend.Verilog.sanitizeName (encode b)) : a = b := by
  rw [sanitizeName_encode, sanitizeName_encode] at h
  exact encode_injective h

theorem sanitizeName_ofDecl (n : Name) :
    Sparkle.Backend.Verilog.sanitizeName (ofDecl n) = ofDecl n :=
  sanitizeName_encode (Key.decl n)

theorem sanitizeName_ofMem (c : Bool) (a d : Nat) :
    Sparkle.Backend.Verilog.sanitizeName (ofMem c a d) = ofMem c a d :=
  sanitizeName_encode (Key.mem c a d)

end Tools.ShippingModuleName
