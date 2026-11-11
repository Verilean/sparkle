import Tools.VedU1Table

/-!
# Constant-table leaves for U1: position-indexed straight-line bodies

The compiler shares equal constants (by value and width) and refers to the first wire that holds
one, so the body of a `kLut!` table is not always the textbook shape: an entry equal to an index
constant (the S-box: an 8-bit index and 8-bit entries) is an alias, and a mux operand names the
root wire.  What is fixed is the wire naming: position `p` of the body defines `W p`, with `W`
injective, and every statement reads earlier positions only.  A `Form` is a statement given by the
POSITIONS it reads; the kernel checks (once, linearly) that the synthesized body IS the body of the
forms read from it, and the lemmas here evaluate such a body in one induction (`eval_bodyN`), prove
it a well-ordered netlist (`orderOk_bodyN`) and its wire names distinct (`nodup_wires`) without any
quadratic scan over names.

Untrusted like the script: the kernel checks everything.
-/

namespace Tools.VedU1TableGen

open Sparkle.IR.AST Sparkle.IR.Semantics Tools.VedU1Table

inductive Form
  | const (c w : Nat)
  | alias (j : Nat)
  | eqIn (j : Nat)
  | mux (c t f : Nat)
  deriving DecidableEq

/-- the positions a form reads -/
def Form.reads : Form → List Nat
  | .const _ _ => []
  | .alias j => [j]
  | .eqIn j => [j]
  | .mux c t f => [c, t, f]

def Form.denote (inp : String) (W : Nat → String) : Form → Expr
  | .const c w => .const (Int.ofNat c) w
  | .alias j => .ref (W j)
  | .eqIn j => .op .eq [.ref inp, .ref (W j)]
  | .mux c t f => .op .mux [.ref (W c), .ref (W t), .ref (W f)]

/-- the value of a form from the input value `x` and the values `g` of the positions -/
def Form.ev (x : Nat) (g : Nat → Nat) : Form → Nat
  | .const c w => c % 2 ^ w
  | .alias j => g j
  | .eqIn j => if x = g j then 1 else 0
  | .mux c t f => if g c ≠ 0 then g t else g f

theorem Form.ev_congr (x : Nat) (g g' : Nat → Nat) (f : Form) (h : ∀ j ∈ f.reads, g j = g' j) :
    f.ev x g = f.ev x g' := by
  cases f with
  | const c w => rfl
  | alias j => exact h j (by simp [Form.reads])
  | eqIn j => simp only [Form.ev, h j (by simp [Form.reads])]
  | mux c t f' =>
    simp only [Form.ev, h c (by simp [Form.reads]), h t (by simp [Form.reads]),
      h f' (by simp [Form.reads])]

/-- the values at positions `0 … n-1` -/
def valsN (x : Nat) (Fn : Nat → Form) : Nat → List Nat
  | 0 => []
  | n + 1 => valsN x Fn n ++ [(Fn n).ev x (fun j => (valsN x Fn n).getD j 0)]

theorem valsN_length (x : Nat) (Fn : Nat → Form) : ∀ n, (valsN x Fn n).length = n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih => simp [valsN, ih]

theorem valsN_prefix (x : Nat) (Fn : Nat → Form) (j : Nat) :
    ∀ n, j < n → (valsN x Fn n).getD j 0 = (valsN x Fn (j + 1)).getD j 0 := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro h
    by_cases hj : j = n
    · subst hj; rfl
    · rw [valsN, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [valsN_length]; omega),
        ← List.getD_eq_getElem?_getD]
      exact ih (by omega)

/-- the value at position `p` -/
def V (x : Nat) (Fn : Nat → Form) (p : Nat) : Nat := (valsN x Fn (p + 1)).getD p 0

/-- the recursion of the values: a form's value from the values of the positions it reads -/
theorem V_eq (x : Nat) (Fn : Nat → Form) (p : Nat) (hr : ∀ j ∈ (Fn p).reads, j < p) :
    V x Fn p = (Fn p).ev x (V x Fn) := by
  have h1 : V x Fn p = (Fn p).ev x (fun j => (valsN x Fn p).getD j 0) := by
    simp only [V, valsN]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [valsN_length]; exact Nat.le_refl _), valsN_length]
    simp
  rw [h1]
  apply Form.ev_congr
  intro j hj
  have := hr j hj
  exact (valsN_prefix x Fn j p this)

/-! ## evaluating the body -/

/-- the body: statement `p` (for `p = i, …, i+n-1`) defines `W p` by form `p` -/
def bodyN (inp : String) (W : Nat → String) (Fn : Nat → Form) : Nat → Nat → List Stmt
  | _, 0 => []
  | i, n + 1 => .assign (W i) ((Fn i).denote inp W) :: bodyN inp W Fn (i + 1) n

/-- every form reads earlier positions only (positions `< N`) -/
def ValidN (Fn : Nat → Form) (N : Nat) : Prop := ∀ p, p < N → ∀ j ∈ (Fn p).reads, j < p

theorem eval_bodyN (we : WEnv) (mems : MEnv) (inp : String) (W : Nat → String) (Fn : Nat → Form)
    (x N : Nat) (hv : ValidN Fn N)
    (hW : ∀ a b, a < N → b < N → W a = W b → a = b) (hI : ∀ a, a < N → W a ≠ inp) :
    ∀ (n i : Nat) (env : Env), i + n ≤ N → env inp = x → (∀ j, j < i → env (W j) = V x Fn j) →
    ∃ env', evalAssigns we mems (bodyN inp W Fn i n) env = some env' ∧ env' inp = x ∧
      ∀ j, j < i + n → env' (W j) = V x Fn j := by
  intro n
  induction n with
  | zero =>
    intro i env _ hx hj
    exact ⟨env, rfl, hx, fun j hjl => hj j (by omega)⟩
  | succ n ih =>
    intro i env hM hx hj
    have hWi : W i ≠ inp := hI i (by omega)
    have hr : ∀ j ∈ (Fn i).reads, j < i := hv i (by omega)
    have hev : evalExpr we env ((Fn i).denote inp W) = some (V x Fn i) := by
      rw [V_eq x Fn i hr]
      cases hf : Fn i with
      | const c w => rw [hf] at hr; exact eval_constN we env c w
      | alias j =>
        rw [hf] at hr
        have := hj j (hr j (by simp [Form.reads]))
        simp only [Form.denote, Form.ev, eval_ref, this]
      | eqIn j =>
        rw [hf] at hr
        have := hj j (hr j (by simp [Form.reads]))
        simp only [Form.denote, Form.ev, eval_eq, this, hx]
      | mux c t f' =>
        rw [hf] at hr
        have h1 := hj c (hr c (by simp [Form.reads]))
        have h2 := hj t (hr t (by simp [Form.reads]))
        have h3 := hj f' (hr f' (by simp [Form.reads]))
        simp only [Form.denote, Form.ev, eval_mux, h1, h2, h3]
    obtain ⟨env', hrun, hx', hfin⟩ := ih (i + 1) (upd env (W i) (V x Fn i)) (by omega)
      (by rw [upd_ne _ _ _ hWi.symm]; exact hx)
      (by
        intro j hjl
        by_cases hji : j = i
        · subst hji; rw [upd_same]
        · rw [upd_ne _ _ _ (fun h => hji (hW j i (by omega) (by omega) h)), hj j (by omega)])
    refine ⟨env', ?_, hx', fun j hjl => hfin j (by omega)⟩
    simp only [bodyN, evalAssigns, hev, Option.bind_eq_bind, Option.bind_some]
    exact hrun

/-! ## the body is a well-ordered netlist -/

open Sparkle.IR.Reorder Tools.VedU1Contract

theorem writesOf_bodyN (inp : String) (W : Nat → String) (Fn : Nat → Form) :
    ∀ (n i : Nat), writesOf (bodyN inp W Fn i n) = (List.range' i n).map W := by
  intro n
  induction n with
  | zero => intro i; simp [bodyN, writesOf]
  | succ n ih =>
    intro i
    have := ih (i + 1)
    simp only [bodyN, writesOf, List.flatMap_cons, stmtWrites, List.range'_succ, List.map_cons] at this ⊢
    rw [this]; rfl

theorem refs_denote (inp : String) (W : Nat → String) (f : Form) :
    ∀ n ∈ refsOf (f.denote inp W), n = inp ∨ ∃ j ∈ f.reads, n = W j := by
  intro n hn
  cases f <;> simp_all [Form.denote, Form.reads, refsOf, refsOf.refsList]

theorem contains_false_of_not_mem {l : List String} {n : String} (h : n ∉ l) : l.contains n = false := by
  cases hc : l.contains n
  · rfl
  · exact absurd (List.contains_iff_mem.1 hc) h

theorem bnot_contains {l : List String} {n : String} : ((!l.contains n) = true) ↔ n ∉ l := by
  rw [Bool.not_eq_true']
  constructor
  · intro h hm
    rw [List.contains_iff_mem.2 hm] at h
    cases h
  · exact contains_false_of_not_mem

theorem mem_range'_map {W : Nat → String} {i len : Nat} {n : String} :
    n ∈ (List.range' i len).map W ↔ ∃ q, i ≤ q ∧ q < i + len ∧ W q = n := by
  simp only [List.mem_map, List.mem_range']
  constructor
  · rintro ⟨q, ⟨k, hk, rfl⟩, rfl⟩; exact ⟨i + 1 * k, by omega, by omega, rfl⟩
  · rintro ⟨q, h1, h2, rfl⟩; exact ⟨q, ⟨q - i, by omega, by omega⟩, rfl⟩

theorem woCheck_bodyN (inp : String) (W : Nat → String) (Fn : Nat → Form) (N : Nat) (hv : ValidN Fn N)
    (hW : ∀ a b, a < N → b < N → W a = W b → a = b) (hI : ∀ a, a < N → W a ≠ inp) :
    ∀ (n i : Nat), i + n ≤ N → woCheck ((List.range i).map W) (bodyN inp W Fn i n) = true := by
  intro n
  induction n with
  | zero => intro i _; simp [bodyN, woCheck]
  | succ n ih =>
    intro i hM
    have hr : ∀ j ∈ (Fn i).reads, j < i := hv i (by omega)
    simp only [bodyN, woCheck, stmtReads, stmtWrites, writesOf_bodyN, Bool.and_eq_true, List.all_eq_true,
      Bool.not_eq_true', List.mem_singleton, forall_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro m hm
      have hm' := refs_denote inp W (Fn i) m hm
      apply contains_false_of_not_mem
      intro hmem
      obtain ⟨q, hq1, hq2, hq⟩ := mem_range'_map.1 hmem
      rcases hm' with rfl | ⟨j, hj, rfl⟩
      · exact hI q (by omega) hq
      · have := hW q j (by omega) (by have := hr j hj; omega) hq
        have := hr j hj
        omega
    · refine ⟨contains_false_of_not_mem ?_, contains_false_of_not_mem ?_⟩
      · intro hmem
        obtain ⟨q, hq1, hq2⟩ := List.mem_map.1 hmem
        have hq1' := List.mem_range.1 hq1
        have := hW q i (by omega) (by omega) hq2
        omega
      · intro hmem
        obtain ⟨q, hq1, hq2, hq⟩ := mem_range'_map.1 hmem
        have := hW q i (by omega) (by omega) hq
        omega
    · have := ih (i + 1) (by omega)
      have e : (List.range i).map W ++ [W i] = (List.range (i + 1)).map W := by
        rw [List.range_succ, List.map_append]; rfl
      rw [e]; exact this

theorem mem_bodyN (inp : String) (W : Nat → String) (Fn : Nat → Form) :
    ∀ (n i : Nat) (s : Stmt), s ∈ bodyN inp W Fn i n →
      ∃ p, i ≤ p ∧ p < i + n ∧ s = .assign (W p) ((Fn p).denote inp W) := by
  intro n
  induction n with
  | zero => intro i s hs; simp [bodyN] at hs
  | succ n ih =>
    intro i s hs
    simp only [bodyN, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact ⟨i, Nat.le_refl _, by omega, rfl⟩
    · obtain ⟨p, h1, h2, h3⟩ := ih (i + 1) s hs
      exact ⟨p, by omega, by omega, h3⟩

theorem isPermOf_refl_aux {α : Type} [DecidableEq α] : ∀ (l : List α), isPermOf l l = true := by
  intro l
  induction l with
  | nil => rfl
  | cons a rest ih => simp [isPermOf, ih]

theorem regsOf_bodyN (inp : String) (W : Nat → String) (Fn : Nat → Form) :
    ∀ (n i : Nat), regsOf (bodyN inp W Fn i n) = [] := by
  intro n
  induction n with
  | zero => intro i; rfl
  | succ n ih => intro i; simp [bodyN, regsOf, ih]

theorem nextKeys_bodyN (inp : String) (W : Nat → String) (Fn : Nat → Form) :
    ∀ (n i : Nat), nextKeys (bodyN inp W Fn i n) = [] := by
  intro n
  induction n with
  | zero => intro i; rfl
  | succ n ih => intro i; simp [bodyN, nextKeys, List.flatMap_cons] at ih ⊢; exact ih _

theorem memNames_bodyN (inp : String) (W : Nat → String) (Fn : Nat → Form) :
    ∀ (n i : Nat), (bodyN inp W Fn i n).filterMap stmtMemName = [] := by
  intro n
  induction n with
  | zero => intro i; rfl
  | succ n ih => intro i; simp [bodyN, stmtMemName, ih]

/-- A position-indexed body is a well-ordered netlist (`OrderOk`): no `O(n²)` string scan. -/
theorem orderOk_bodyN (m : Sparkle.IR.AST.Module) (inp : String) (W : Nat → String) (Fn : Nat → Form)
    (N : Nat) (hv : ValidN Fn N) (hW : ∀ a b, a < N → b < N → W a = W b → a = b)
    (hI : ∀ a, a < N → W a ≠ inp) (hbody : m.body = bodyN inp W Fn 0 N)
    (hin : m.inputs.map (·.name) = [inp]) (hout : ∀ p ∈ m.outputs, ∃ q, q < N ∧ p.name = W q) :
    OrderOk m (bodyN inp W Fn 0 N) = true := by
  have hw := writesOf_bodyN inp W Fn N 0
  have hall := mem_bodyN inp W Fn N 0
  unfold OrderOk
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, bnot_contains, List.contains_iff_mem,
    Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [← hbody]; exact isPermOf_refl_aux _
  · exact woCheck_bodyN inp W Fn N hv hW hI N 0 (by omega)
  · rw [nextKeys_bodyN]; exact List.nodup_nil
  · rw [memNames_bodyN]; exact List.nodup_nil
  · intro s hs n hn
    obtain ⟨p, h1, h2, rfl⟩ := hall s hs
    have h4 := hv p (by omega)
    simp only [stmtReads, stmtWrites, List.mem_singleton] at hn ⊢
    rcases refs_denote inp W (Fn p) n hn with rfl | ⟨j, hj, rfl⟩
    · exact fun h => hI p (by omega) h.symm
    · exact fun h => by
        have := hW j p (by have := h4 j hj; omega) (by omega) h
        have := h4 j hj; omega
  · intro s hs n hn
    obtain ⟨p, h1, h2, rfl⟩ := hall s hs
    have h4 := hv p (by omega)
    simp only [allReads, stmtReads] at hn ⊢
    rw [hw, regsOf_bodyN]
    rcases refs_denote inp W (Fn p) n hn with rfl | ⟨j, hj, rfl⟩
    · left; left; rw [hin]; simp
    · right; exact mem_range'_map.2 ⟨j, by omega, by have := h4 j hj; omega, rfl⟩
  · intro p hp
    obtain ⟨q, hq, hn⟩ := hout p hp
    rw [hw, regsOf_bodyN]
    right
    exact mem_range'_map.2 ⟨q, by omega, by omega, hn.symm⟩
  · intro n hn
    rw [hw] at hn
    obtain ⟨q, _, hq, rfl⟩ := mem_range'_map.1 hn
    rw [regsOf_bodyN]
    refine ⟨?_, by simp⟩
    rw [hin]
    simp only [List.mem_singleton]
    exact fun h => hI q (by omega) h
  · intro n hn
    rw [regsOf_bodyN] at hn
    simp at hn

/-- the wire names of a position-indexed body are distinct (`WidthStmt`'s `Nodup`) -/
theorem nodup_wires (inp : String) (W : Nat → String) (N : Nat)
    (hW : ∀ a b, a < N → b < N → W a = W b → a = b) (hI : ∀ a, a < N → W a ≠ inp) :
    (inp :: (List.range N).map W).Nodup := by
  refine List.nodup_cons.2 ⟨?_, ?_⟩
  · intro h
    obtain ⟨q, hq, hqe⟩ := List.mem_map.1 h
    exact hI q (List.mem_range.1 hq) hqe
  · unfold List.Nodup
    rw [List.pairwise_map]
    exact (List.nodup_range (n := N)).imp_of_mem (fun {a b} ha hb hne hab =>
      hne (hW a b (List.mem_range.1 ha) (List.mem_range.1 hb) hab))

end Tools.VedU1TableGen
