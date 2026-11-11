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

/-! ## the value of the table skeleton -/

/-- positions whose value does not depend on the input: constants and aliases of such -/
inductive PureAt (Fn : Nat → Form) : Nat → Prop
  | const {p c w} : Fn p = .const c w → PureAt Fn p
  | alias {p j} : Fn p = .alias j → j < p → PureAt Fn j → PureAt Fn p

theorem V_pure (Fn : Nat → Form) {p : Nat} (h : PureAt Fn p) (x y : Nat) : V x Fn p = V y Fn p := by
  induction h with
  | const hf =>
    rename_i p c w
    rw [V_eq x Fn p (by rw [hf]; simp [Form.reads]), V_eq y Fn p (by rw [hf]; simp [Form.reads]), hf]
    rfl
  | alias hf hj hp ih =>
    rename_i p j
    rw [V_eq x Fn p (by rw [hf]; intro k hk; simp [Form.reads] at hk; omega),
      V_eq y Fn p (by rw [hf]; intro k hk; simp [Form.reads] at hk; omega), hf]
    simp only [Form.ev]
    exact ih

/-- decidable purity with the value (fuel: the alias depth) -/
def kv (Fn : Nat → Form) : Nat → Nat → Option Nat
  | 0, _ => none
  | f + 1, p => match Fn p with
    | .const c w => some (c % 2 ^ w)
    | .alias j => if j < p then kv Fn f j else none
    | _ => none

theorem kv_sound (Fn : Nat → Form) : ∀ (f p v : Nat), kv Fn f p = some v →
    PureAt Fn p ∧ ∀ x, V x Fn p = v := by
  intro f
  induction f with
  | zero => intro p v h; simp [kv] at h
  | succ f ih =>
    intro p v h
    simp only [kv] at h
    cases hf : Fn p with
    | const c w =>
      rw [hf] at h
      simp only [Option.some.injEq] at h
      refine ⟨PureAt.const hf, fun x => ?_⟩
      rw [V_eq x Fn p (by rw [hf]; simp [Form.reads]), hf]
      simp [Form.ev, h]
    | alias j =>
      rw [hf] at h
      by_cases hj : j < p
      · simp only [hj, if_true] at h
        obtain ⟨hp, hv⟩ := ih j v h
        refine ⟨PureAt.alias hf hj hp, fun x => ?_⟩
        rw [V_eq x Fn p (by rw [hf]; intro k hk; simp [Form.reads] at hk; omega), hf]
        simp only [Form.ev]
        exact hv x
      · simp [hj] at h
    | eqIn j => rw [hf] at h; simp at h
    | mux c t f' => rw [hf] at h; simp at h

/-- The value of a table skeleton: wires `3k+1` compare the input with `bp k`, the chain
`3t+j` (`j = 1…t`) muxes them from the top, position `4t+1` aliases the result. -/
theorem skeleton_val (Fn : Nat → Form) (t : Nat) (ht : 1 ≤ t) (hv : ValidN Fn (4 * t + 2))
    (bp rt : Nat → Nat) (rl : Nat) (tbl : List Nat) (last w : Nat) (htl : tbl.length = t)
    (h1 : ∀ k, k < t → Fn (3 * k + 1) = .eqIn (bp k))
    (h2 : ∀ j, 1 ≤ j → j ≤ t → Fn (3 * t + j) = .mux (3 * (t - j) + 1) (rt (t - j))
      (if j = 1 then rl else 3 * t + j - 1))
    (h3 : Fn (4 * t + 1) = .alias (4 * t))
    (hb : ∀ k, k < t → ∀ x, V x Fn (bp k) = k)
    (hd : ∀ k, k < t → ∀ x, V x Fn (rt k) = tbl.getD k 0 % 2 ^ w)
    (hl : ∀ x, V x Fn rl = last % 2 ^ w) (x : Nat) :
    V x Fn (4 * t + 1) = pick x 0 tbl last % 2 ^ w := by
  -- the conditions
  have hc : ∀ k, k < t → V x Fn (3 * k + 1) = if x = k then 1 else 0 := by
    intro k hk
    have hr := hv (3 * k + 1) (by omega)
    rw [h1 k hk] at hr
    rw [V_eq x Fn _ (by rw [h1 k hk]; exact hr), h1 k hk]
    simp only [Form.ev, hb k hk x]
  -- the chain
  let E : Nat → Nat := fun j => if j = 0 then V x Fn rl else V x Fn (3 * t + j)
  have hE : ∀ j, j < t → E (j + 1) = if V x Fn (3 * (t - (j + 1)) + 1) ≠ 0 then V x Fn (rt (t - (j + 1))) else E j := by
    intro j hj
    have hr := hv (3 * t + (j + 1)) (by omega)
    rw [h2 (j + 1) (by omega) (by omega)] at hr
    simp only [E, if_neg (Nat.succ_ne_zero j)]
    rw [V_eq x Fn _ (by rw [h2 (j + 1) (by omega) (by omega)]; exact hr), h2 (j + 1) (by omega) (by omega)]
    simp only [Form.ev]
    by_cases hj0 : j = 0
    · subst hj0; simp
    · have : ¬ (j + 1 = 1) := by omega
      simp only [this, if_false, hj0, if_false]
      have e : 3 * t + (j + 1) - 1 = 3 * t + j := by omega
      rw [e]
  have hcv : ∀ j, j ≤ t → E j = cv (fun i => if x = i then 1 else 0) (fun i => tbl.getD i 0 % 2 ^ w) t (last % 2 ^ w) j := by
    intro j
    induction j with
    | zero => intro _; simp [E, cv, hl x]
    | succ j ih =>
      intro hj
      rw [hE j (by omega), ih (by omega)]
      simp only [cv]
      have hk : t - (j + 1) < t := by omega
      rw [hc _ hk, hd _ hk x]
  have hfin : V x Fn (4 * t) = E t := by
    have : 4 * t = 3 * t + t := by omega
    simp only [E, if_neg (by omega : t ≠ 0)]
    rw [this]
  have hr3 := hv (4 * t + 1) (by omega)
  rw [h3] at hr3
  rw [V_eq x Fn _ (by rw [h3]; exact hr3), h3]
  simp only [Form.ev]
  rw [hfin, hcv t (Nat.le_refl _)]
  have := cv_eq tbl last x w t (by omega)
  rw [htl] at this
  simpa using this

/-! ## the wire names of a table body -/

/-- the compiler's wire names: the pre-region `3t` wires `nm (p % 3) p`, the else chain `nm 3 p`
up to `4t - 1`, then `_gen_out` and `out` -/
def Wt (t p : Nat) : String :=
  if p < 3 * t then nm (p % 3) p else if p < 4 * t then nm 3 p
  else if p = 4 * t then "_gen_out" else "out"

theorem nm_ne_of_ne_t {s : String} (h : s.toList[1]? ≠ some 't') (a j : Nat) : nm a j ≠ s := by
  intro e
  exact h (e ▸ nm_get1 a j)

theorem Wt_lt (t p : Nat) (h : p < 4 * t) : Wt t p = nm (if p < 3 * t then p % 3 else 3) p := by
  unfold Wt
  by_cases h1 : p < 3 * t
  · simp [h1]
  · simp [h1, h]

theorem Wt_ge (t p : Nat) (h : 4 * t ≤ p) : Wt t p = if p = 4 * t then "_gen_out" else "out" := by
  unfold Wt
  have h1 : ¬ p < 3 * t := by omega
  have h2 : ¬ p < 4 * t := by omega
  simp [h1, h2]

theorem Wt_inj (t : Nat) : ∀ a b, a < 4 * t + 2 → b < 4 * t + 2 → Wt t a = Wt t b → a = b := by
  intro a b ha hb h
  have g1 : "_gen_out".toList[1]? ≠ some 't' := by decide
  have g2 : "out".toList[1]? ≠ some 't' := by decide
  have ne_go : "_gen_out" ≠ "out" := by decide
  have kind : ∀ p, (if p < 3 * t then p % 3 else 3) ≤ 3 := by
    intro p; split <;> omega
  by_cases ha' : a < 4 * t <;> by_cases hb' : b < 4 * t
  · rw [Wt_lt t a ha', Wt_lt t b hb'] at h
    exact (nm_inj (kind a) (kind b) h).2
  · rw [Wt_lt t a ha', Wt_ge t b (by omega)] at h
    by_cases hb4 : b = 4 * t
    · simp only [hb4, if_true] at h; exact absurd h (nm_ne_of_ne_t g1 _ _)
    · simp only [hb4, if_false] at h; exact absurd h (nm_ne_of_ne_t g2 _ _)
  · rw [Wt_ge t a (by omega), Wt_lt t b hb'] at h
    by_cases ha4 : a = 4 * t
    · simp only [ha4, if_true] at h; exact absurd h.symm (nm_ne_of_ne_t g1 _ _)
    · simp only [ha4, if_false] at h; exact absurd h.symm (nm_ne_of_ne_t g2 _ _)
  · rw [Wt_ge t a (by omega), Wt_ge t b (by omega)] at h
    by_cases h1 : a = 4 * t <;> by_cases h2 : b = 4 * t
    · omega
    · simp only [h1, h2, if_true, if_false] at h; exact absurd h ne_go
    · simp only [h1, h2, if_true, if_false] at h; exact absurd h.symm ne_go
    · omega

theorem Wt_ne_inp (t : Nat) (inp : String) (h1 : inp.toList[1]? ≠ some 't') (h2 : inp ≠ "_gen_out")
    (h3 : inp ≠ "out") : ∀ a, a < 4 * t + 2 → Wt t a ≠ inp := by
  intro a ha
  by_cases ha' : a < 4 * t
  · rw [Wt_lt t a ha']; exact nm_ne_of_ne_t h1 _ _
  · rw [Wt_ge t a (by omega)]
    split
    · exact fun h => h2 h.symm
    · exact fun h => h3 h.symm

/-! ## a table, as data the kernel checks -/

structure TblData where
  Fl : List Form
  t : Nat
  bpL : List Nat
  rtL : List Nat
  rl : Nat
  tbl : List Nat
  last : Nat
  iw : Nat
  w : Nat
  inp : String

def TblData.Fn (D : TblData) : Nat → Form := fun p => D.Fl.getD p (.const 0 0)

/-- the body the data stands for -/
def TblData.body (D : TblData) : List Stmt := bodyN D.inp (Wt D.t) D.Fn 0 (4 * D.t + 2)

/-- the checks, all on small numbers and the form list: the shape of the skeleton, validity (every
form reads earlier positions), the constants behind the compared / selected positions, and the
names. -/
def TblData.ok (D : TblData) : Bool :=
  decide (1 ≤ D.t) && (D.Fl.length == 4 * D.t + 2) && (D.tbl.length == D.t) && decide (D.t ≤ 2 ^ D.iw) &&
  (List.range (4 * D.t + 2)).all (fun p => (D.Fn p).reads.all (fun j => decide (j < p))) &&
  (List.range D.t).all (fun k => D.Fn (3 * k + 1) == .eqIn (D.bpL.getD k 0)) &&
  (List.range' 1 D.t).all (fun j => D.Fn (3 * D.t + j) ==
    .mux (3 * (D.t - j) + 1) (D.rtL.getD (D.t - j) 0) (if j = 1 then D.rl else 3 * D.t + j - 1)) &&
  (D.Fn (4 * D.t + 1) == .alias (4 * D.t)) &&
  (List.range D.t).all (fun k =>
    (kv D.Fn (D.bpL.getD k 0 + 1) (D.bpL.getD k 0) == some k) &&
    (kv D.Fn (D.rtL.getD k 0 + 1) (D.rtL.getD k 0) == some (D.tbl.getD k 0 % 2 ^ D.w))) &&
  (kv D.Fn (D.rl + 1) D.rl == some (D.last % 2 ^ D.w)) &&
  decide (D.inp.toList[1]? ≠ some 't') && decide (D.inp ≠ "_gen_out") && decide (D.inp ≠ "out")

theorem TblData.ok_sound (D : TblData) (h : D.ok = true) :
    1 ≤ D.t ∧ D.Fl.length = 4 * D.t + 2 ∧ D.tbl.length = D.t ∧ D.t ≤ 2 ^ D.iw ∧
    ValidN D.Fn (4 * D.t + 2) ∧
    (∀ k, k < D.t → D.Fn (3 * k + 1) = .eqIn (D.bpL.getD k 0)) ∧
    (∀ j, 1 ≤ j → j ≤ D.t → D.Fn (3 * D.t + j) =
      .mux (3 * (D.t - j) + 1) (D.rtL.getD (D.t - j) 0) (if j = 1 then D.rl else 3 * D.t + j - 1)) ∧
    D.Fn (4 * D.t + 1) = .alias (4 * D.t) ∧
    (∀ k, k < D.t → ∀ x, V x D.Fn (D.bpL.getD k 0) = k) ∧
    (∀ k, k < D.t → ∀ x, V x D.Fn (D.rtL.getD k 0) = D.tbl.getD k 0 % 2 ^ D.w) ∧
    (∀ x, V x D.Fn D.rl = D.last % 2 ^ D.w) ∧
    D.inp.toList[1]? ≠ some 't' ∧ D.inp ≠ "_gen_out" ∧ D.inp ≠ "out" := by
  simp only [TblData.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.mem_range, List.mem_range'_1] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_, h8, ?_, ?_, ?_, h11, h12, h13⟩
  · intro p hp j hj
    exact h5 p hp j hj
  · intro k hk; exact h6 k hk
  · intro j hj1 hj2; exact h7 j ⟨hj1, by omega⟩
  · intro k hk x
    have := (h9 k hk).1
    exact (kv_sound _ _ _ _ this).2 x
  · intro k hk x
    have := (h9 k hk).2
    exact (kv_sound _ _ _ _ this).2 x
  · intro x
    exact (kv_sound _ _ _ _ h10).2 x

theorem all_bodyN (inp : String) (W : Nat → String) (Fn : Nat → Form) :
    ∀ (n i : Nat), (bodyN inp W Fn i n).all isAsg = true := by
  intro n
  induction n with
  | zero => intro i; rfl
  | succ n ih => intro i; simp [bodyN, isAsg, ih]

/-- One cycle of a table body: no register update, memories unchanged, `out` the table lookup. -/
theorem step_table (D : TblData) (hok : D.ok = true) (we : WEnv) (mems : MEnv) (env0 : Env) :
    ∃ envF, stepModule we D.body env0 mems = some (envF, [], mems) ∧
      envF "out" = pick (env0 D.inp) 0 D.tbl D.last % 2 ^ D.w := by
  obtain ⟨ht, hlen, htl, hti, hv, h1, h2, h3, hb, hd, hl, hi1, hi2, hi3⟩ := D.ok_sound hok
  have hW := Wt_inj D.t
  have hI := Wt_ne_inp D.t D.inp hi1 hi2 hi3
  obtain ⟨env', hrun, _, hval⟩ := eval_bodyN we mems D.inp (Wt D.t) D.Fn (env0 D.inp) (4 * D.t + 2) hv hW hI
    (4 * D.t + 2) 0 env0 (by omega) rfl (fun j hj => absurd hj (Nat.not_lt_zero _))
  have hout : env' "out" = V (env0 D.inp) D.Fn (4 * D.t + 1) := by
    have := hval (4 * D.t + 1) (by omega)
    rw [Wt_ge D.t _ (by omega)] at this
    simpa using this
  refine ⟨env', ?_, ?_⟩
  · unfold TblData.body
    simp only [stepModule, hrun, regNexts_asg we mems _ _ (all_bodyN _ _ _ _ _),
      memNexts_asg we _ mems _ (all_bodyN _ _ _ _ _), Option.bind_eq_bind, Option.bind_some]
  · rw [hout]
    exact skeleton_val D.Fn D.t ht hv (fun k => D.bpL.getD k 0) (fun k => D.rtL.getD k 0) D.rl D.tbl D.last D.w
      htl h1 h2 h3 hb hd hl _

/-- the table body is a well-ordered netlist -/
theorem orderOk_table (D : TblData) (hok : D.ok = true) (m : Sparkle.IR.AST.Module)
    (hbody : m.body = D.body) (hin : m.inputs.map (·.name) = [D.inp])
    (hout : ∀ p ∈ m.outputs, p.name = "out") : OrderOk m D.body = true := by
  obtain ⟨ht, hlen, htl, hti, hv, h1, h2, h3, hb, hd, hl, hi1, hi2, hi3⟩ := D.ok_sound hok
  exact orderOk_bodyN m D.inp (Wt D.t) D.Fn (4 * D.t + 2) hv (Wt_inj D.t)
    (Wt_ne_inp D.t D.inp hi1 hi2 hi3) hbody hin
    (fun p hp => ⟨4 * D.t + 1, by omega, by rw [hout p hp, Wt_ge D.t _ (by omega)]; simp⟩)

/-- the wire names of the table body are distinct (`WidthStmt`) -/
theorem nodup_table (D : TblData) (hok : D.ok = true) :
    (D.inp :: (List.range (4 * D.t + 1)).map (Wt D.t)).Nodup := by
  obtain ⟨ht, hlen, htl, hti, hv, h1, h2, h3, hb, hd, hl, hi1, hi2, hi3⟩ := D.ok_sound hok
  exact nodup_wires D.inp (Wt D.t) (4 * D.t + 1) (fun a b ha hb h => Wt_inj D.t a b (by omega) (by omega) h)
    (fun a ha => Wt_ne_inp D.t D.inp hi1 hi2 hi3 a (by omega))

end Tools.VedU1TableGen
