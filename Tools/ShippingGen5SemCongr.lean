import Tools.ShippingGen5SemCall
import Tools.ShippingQuadCalls
set_option autoImplicit false
-- Built in g5sm-u4 at c28de8a1a7e26247d4b3082731cbcf6a820b640c (Pod kjob lake build, exit 0). Clean build is the coder's. No sorry/axiom/native_decide.
/-! # DG-SEM U4E (scripts/gen5/DG_SEM_FREEZE_P4.md rev1 §5.2): stage preservation through the `let`s

`lsrcAt_congr` is proved as frozen. `typedVal_let_congr` is NOT proved: as stated in the freeze its conclusion also compares the
*off-sort* component of a `let` position (the `v` component of a `bool` `let`, the `b` component of a `bits` `let`); that component is the
value of the input Signal at that very position, which `hb`/`hv` (positions `< kDOf d + k`) do not constrain. See
`scripts/gen5/DG_SEM_FREEZE_P4_U4E_ADDENDUM.md`. The sort-aware statement `typedVal_let_agree` (new, internal) is what `lsrcAt_congr` is
derived from. -/
namespace Tools.ShippingGen5Sem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingMachineRef (reads)
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge Sparkle.Compiler.MachInstOrigin

/-- sort-aware agreement of two typed valuations at a position: the component of the position's declared sort -/
def AgrAt (d : MachineData) (T T' : TVal) (p : Nat) : Prop :=
  (d.K p = some .bool → T.b p = T'.b p) ∧ ∀ w, d.K p = some (.bits w) → T.v p w = T'.v p w

theorem ok_Kfacts (d : MachineData) (h : d.ok = true) :
    (∀ j, j < d.kb → d.K (d.bpos j) = some .bool ∧ d.bpos j < d.nIn + d.ss.length + d.ls.length) ∧
    (∀ j, j < d.kv → d.K (d.vpos j) = some (.bits (d.vw j)) ∧ d.vpos j < d.nIn + d.ss.length + d.ls.length) ∧
    (∀ i, i < d.ss.length → d.K (d.nIn + i) = d.ss[i]?) := by
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, hslots, fb, fv, fslots, flets, nextsWF, houts, hne⟩ := h
  exact ⟨fb, fv, fslots⟩

theorem LetsTyped.get3 {bpos vpos : Nat → Nat} {kb kv : Nat} {vw : Nat → Nat} {K : Nat → Option SType} :
    ∀ {p : Nat} {ls : List (Σ s : SType, Term s)}, LetsTyped bpos vpos kb kv vw K p ls →
      ∀ (q : Nat) (l : Σ s : SType, Term s), ls[q]? = some l →
        l.2.WF kb kv vw ∧
        reads (fun j => decide (bpos j < p + q)) (fun j => decide (vpos j < p + q)) l.2 = true ∧
        K (p + q) = some l.1
  | _, [], _, q, l, h => by simp at h
  | p, _ :: _, h, 0, l, hl => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
    subst hl; exact ⟨h.1, by simpa using h.2.1, by simpa using h.2.2.1⟩
  | p, _ :: _, h, q + 1, l, hl => by
    have := LetsTyped.get3 h.2.2.2 q l (by simpa using hl)
    rw [show p + (q + 1) = p + 1 + q by omega]; exact this

/-! ## the accumulator of `cleanLets` -/

def cleanStep (d : MachineData) (k : Nat) (clean : List Bool) (l : Σ s : SType, Term s) : List Bool :=
  clean ++ [reads (fun j => posOk d k clean (d.bpos j)) (fun j => posOk d k clean (d.vpos j)) l.2]

theorem cleanLets_eq (d : MachineData) (k : Nat) : cleanLets d k = d.ls.foldl (cleanStep d k) [] := rfl

def cleanUpTo (d : MachineData) (k m : Nat) : List Bool := (d.ls.take m).foldl (cleanStep d k) []

theorem foldl_cleanStep_length (d : MachineData) (k : Nat) :
    ∀ (xs : List (Σ s : SType, Term s)) (c : List Bool), (xs.foldl (cleanStep d k) c).length = c.length + xs.length
  | [], c => by simp
  | x :: xs, c => by
    simp only [List.foldl_cons, foldl_cleanStep_length d k xs, cleanStep, List.length_append, List.length_cons,
      List.length_nil]
    omega

theorem cleanUpTo_length (d : MachineData) (k m : Nat) (hm : m ≤ d.ls.length) : (cleanUpTo d k m).length = m := by
  unfold cleanUpTo
  rw [foldl_cleanStep_length]
  simp only [List.length_nil, List.length_take]
  omega

theorem cleanUpTo_succ (d : MachineData) (k m : Nat) (hm : m < d.ls.length) :
    cleanUpTo d k (m + 1) = cleanUpTo d k m ++
      [reads (fun j => posOk d k (cleanUpTo d k m) (d.bpos j)) (fun j => posOk d k (cleanUpTo d k m) (d.vpos j))
        (d.ls[m]).2] := by
  unfold cleanUpTo
  rw [List.take_succ_eq_append_getElem hm, List.foldl_append]
  rfl

theorem cleanUpTo_full (d : MachineData) (k : Nat) : cleanUpTo d k d.ls.length = cleanLets d k := by
  unfold cleanUpTo
  rw [List.take_length]
  rfl

theorem cleanUpTo_stable (d : MachineData) (k l : Nat) (r : Nat) (hr : r < l) :
    ∀ j, l + j ≤ d.ls.length → (cleanUpTo d k (l + j))[r]? = (cleanUpTo d k l)[r]?
  | 0, _ => rfl
  | j + 1, h => by
    rw [← Nat.add_assoc, cleanUpTo_succ d k (l + j) (by omega)]
    have hlen := cleanUpTo_length d k (l + j) (by omega)
    rw [List.getElem?_append_left (by omega)]
    exact cleanUpTo_stable d k l r hr j (by omega)

theorem getD_true_lt (c : List Bool) (r : Nat) (h : c.getD r false = true) : r < c.length := by
  rcases Nat.lt_or_ge r c.length with hr | hr
  · exact hr
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hr] at h
    simp at h

theorem cleanUpTo_mono (d : MachineData) (k l m : Nat) (hlm : l ≤ m) (hm : m ≤ d.ls.length) (r : Nat)
    (h : (cleanUpTo d k l).getD r false = true) : (cleanUpTo d k m).getD r false = true := by
  have hr := getD_true_lt _ _ h
  rw [cleanUpTo_length d k l (by omega)] at hr
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hlm
  have := cleanUpTo_stable d k l r hr j hm
  rw [List.getD_eq_getElem?_getD] at h ⊢
  rw [this]; exact h

theorem getD_append_ne (c : List Bool) (f : Bool) (r : Nat) (h : r ≠ c.length) :
    (c ++ [f]).getD r false = c.getD r false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_gt_of_ne h with hr | hr
  · rw [List.getElem?_append_left hr]
  · have h1 : [f][r - c.length]? = none := List.getElem?_eq_none (by simp; omega)
    have h2 : c[r]? = none := List.getElem?_eq_none (by omega)
    rw [List.getElem?_append_right (by omega), h1, h2]

theorem posOk_step (d : MachineData) (k : Nat) (c : List Bool) (f : Bool) (p : Nat)
    (hp : p ≠ d.nIn + d.ss.length + c.length) : posOk d k (c ++ [f]) p = posOk d k c p := by
  unfold posOk
  by_cases h : d.nIn + d.ss.length ≤ p
  · rw [getD_append_ne c f (p - (d.nIn + d.ss.length)) (by omega)]
  · have : decide (d.nIn + d.ss.length ≤ p) = false := by simpa using h
    simp [this]

theorem posOk_self (d : MachineData) (k : Nat) (c : List Bool) (f : Bool)
    (h : posOk d k (c ++ [f]) (d.nIn + d.ss.length + c.length) = true) :
    d.nIn + d.ss.length + c.length < kDOf d + k ∨ f = true := by
  unfold posOk at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | ⟨_, h⟩
  · exact Or.inl h
  · omega
  · right
    rw [show d.nIn + d.ss.length + c.length - (d.nIn + d.ss.length) = c.length by omega,
      List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)] at h
    simpa using h

theorem encodeBool_inj' {a b : Bool} (h : Tools.ShippingMuxLoweringSoundness.encodeBool a =
    Tools.ShippingMuxLoweringSoundness.encodeBool b) : a = b := by
  cases a <;> cases b <;> simp_all [Tools.ShippingMuxLoweringSoundness.encodeBool]

theorem posOk_mono (d : MachineData) (k l m : Nat) (hlm : l ≤ m) (hm : m ≤ d.ls.length) (p : Nat)
    (h : posOk d k (cleanUpTo d k l) p = true) : posOk d k (cleanUpTo d k m) p = true := by
  unfold posOk at h ⊢
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
  rcases h with (h | h) | ⟨h1, h2⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr ⟨h1, cleanUpTo_mono d k l m hlm hm _ h2⟩

/-! ## the partial typed valuation (the first `m` lets) -/

theorem letVal_append (bpos vpos : Nat → Nat) :
    ∀ (xs ys : List (Σ s : SType, Term s)) (p : Nat) (V : TVal),
      letVal bpos vpos (xs ++ ys) p V = letVal bpos vpos ys (p + xs.length) (letVal bpos vpos xs p V)
  | [], ys, p, V => rfl
  | x :: xs, ys, p, V => by
    simp only [List.cons_append, letVal, List.length_cons]
    rw [letVal_append bpos vpos xs ys (p + 1), show p + 1 + xs.length = p + (xs.length + 1) by omega]

def partialVal (d : MachineData) {D : DomainConfig} (bs : Nat → Signal D Bool)
    (vs : (j n : Nat) → Signal D (BitVec n)) (t : Nat) (x : HList (tys d.ss)) (m : Nat) : TVal :=
  letVal d.bpos d.vpos (d.ls.take m) (d.nIn + d.ss.length)
    (slotVal d.nIn d.ss x 0 ⟨fun p => (bs p).val t, fun p w => (vs p w).val t⟩)

theorem typedVal_eq_partial (d : MachineData) {D : DomainConfig} (bs : Nat → Signal D Bool)
    (vs : (j n : Nat) → Signal D (BitVec n)) (t : Nat) (x : HList (tys d.ss)) :
    typedVal d.nIn d.bpos d.vpos d.ss d.ls bs vs t x = partialVal d bs vs t x d.ls.length := by
  unfold typedVal partialVal
  rw [List.take_length]

theorem partialVal_succ (d : MachineData) {D : DomainConfig} (bs : Nat → Signal D Bool)
    (vs : (j n : Nat) → Signal D (BitVec n)) (t : Nat) (x : HList (tys d.ss)) (m : Nat) (hm : m < d.ls.length) :
    partialVal d bs vs t x (m + 1) =
      (partialVal d bs vs t x m).set (d.nIn + d.ss.length + m) (d.ls[m]).1
        (eval (fun j => (partialVal d bs vs t x m).b (d.bpos j))
          (fun j w => (partialVal d bs vs t x m).v (d.vpos j) w) (d.ls[m]).2) := by
  unfold partialVal
  rw [List.take_succ_eq_append_getElem hm, letVal_append]
  have : (d.ls.take m).length = m := by simp; omega
  rw [this]
  rfl

theorem slotVal_ge (kIn : Nat) : ∀ (ss : List SType) (x : HList (tys ss)) (i0 : Nat) (V : TVal)
    (q : Nat), kIn + i0 + ss.length ≤ q →
    (slotVal kIn ss x i0 V).b q = V.b q ∧ ∀ n, (slotVal kIn ss x i0 V).v q n = V.v q n
  | [], _, _, _, _, _ => ⟨rfl, fun _ => rfl⟩
  | s :: ss, x, i0, V, q, h => by
    obtain ⟨hb, hv⟩ := slotVal_ge kIn ss x.2 (i0 + 1) (V.set (kIn + i0) s x.1) q (by simp at h; omega)
    exact ⟨hb.trans (set_b_ne (by simp at h; omega)), fun n => (hv n).trans (set_v_ne (by simp at h; omega) n)⟩

/-! ## the sort-aware invariant -/

theorem partial_agr (d : MachineData) (hok : d.ok = true) (k : Nat) {D : DomainConfig}
    (bs bs' : Nat → Signal D Bool) (vs vs' : (j n : Nat) → Signal D (BitVec n)) (t : Nat) (x : HList (tys d.ss))
    (hb : ∀ p, p < kDOf d + k → (bs p).val t = (bs' p).val t)
    (hv : ∀ p w, p < kDOf d + k → (vs p w).val t = (vs' p w).val t) :
    ∀ m, m ≤ d.ls.length → ∀ p, posOk d k (cleanUpTo d k m) p = true →
      AgrAt d (partialVal d bs vs t x m) (partialVal d bs' vs' t x m) p := by
  obtain ⟨fb, fv, fslots⟩ := ok_Kfacts d hok
  have hLT := Tools.ShippingQuadCalls.ok_letsTyped d hok
  intro m
  induction m with
  | zero =>
    intro _ p hp
    have h0 : ∀ V : TVal, partialVal d bs vs t x 0 = slotVal d.nIn d.ss x 0 ⟨fun p => (bs p).val t, fun p w => (vs p w).val t⟩ →
      True := fun _ _ => trivial
    have e0 : partialVal d bs vs t x 0 =
        slotVal d.nIn d.ss x 0 ⟨fun p => (bs p).val t, fun p w => (vs p w).val t⟩ := rfl
    have e0' : partialVal d bs' vs' t x 0 =
        slotVal d.nIn d.ss x 0 ⟨fun p => (bs' p).val t, fun p w => (vs' p w).val t⟩ := rfl
    rw [e0, e0']
    have hp' : posOk d k [] p = true := hp
    rcases Nat.lt_or_ge p d.nIn with h1 | h1
    · have hk : p < kDOf d + k := by
        unfold posOk at hp'
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp'
        rcases hp' with (h | h) | h
        · exact h
        · omega
        · omega
      have s1 := slotVal_lt d.nIn d.ss x 0 ⟨fun p => (bs p).val t, fun p w => (vs p w).val t⟩ p (by omega)
      have s2 := slotVal_lt d.nIn d.ss x 0 ⟨fun p => (bs' p).val t, fun p w => (vs' p w).val t⟩ p (by omega)
      refine ⟨fun _ => ?_, fun w _ => ?_⟩
      · rw [s1.1, s2.1]; exact hb p hk
      · rw [(s1.2 w), (s2.2 w)]; exact hv p w hk
    · rcases Nat.lt_or_ge p (d.nIn + d.ss.length) with h2 | h2
      · -- a slot position
        have hi : p - d.nIn < d.ss.length := by omega
        have hK := fslots (p - d.nIn) hi
        rw [show d.nIn + (p - d.nIn) = p by omega] at hK
        refine ⟨fun hKb => ?_, fun w hKw => ?_⟩
        · rw [hK] at hKb
          have a1 := (slotVal_at d.nIn d.ss x 0 ⟨fun p => (bs p).val t, fun p w => (vs p w).val t⟩ (p - d.nIn) .bool hKb).1 rfl
          have a2 := (slotVal_at d.nIn d.ss x 0 ⟨fun p => (bs' p).val t, fun p w => (vs' p w).val t⟩ (p - d.nIn) .bool hKb).1 rfl
          rw [show d.nIn + 0 + (p - d.nIn) = p by omega] at a1 a2
          exact encodeBool_inj' (a1.trans a2.symm)
        · rw [hK] at hKw
          have a1 := (slotVal_at d.nIn d.ss x 0 ⟨fun p => (bs p).val t, fun p w => (vs p w).val t⟩ (p - d.nIn) (.bits w) hKw).2 w rfl
          have a2 := (slotVal_at d.nIn d.ss x 0 ⟨fun p => (bs' p).val t, fun p w => (vs' p w).val t⟩ (p - d.nIn) (.bits w) hKw).2 w rfl
          rw [show d.nIn + 0 + (p - d.nIn) = p by omega] at a1 a2
          exact BitVec.eq_of_toNat_eq (a1.trans a2.symm)
      · have hk : p < kDOf d + k := by
          unfold posOk at hp'
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp'
          rcases hp' with (h | h) | h
          · exact h
          · omega
          · simp at h
        have s1 := slotVal_ge d.nIn d.ss x 0 ⟨fun p => (bs p).val t, fun p w => (vs p w).val t⟩ p (by omega)
        have s2 := slotVal_ge d.nIn d.ss x 0 ⟨fun p => (bs' p).val t, fun p w => (vs' p w).val t⟩ p (by omega)
        refine ⟨fun _ => ?_, fun w _ => ?_⟩
        · rw [s1.1, s2.1]; exact hb p hk
        · rw [(s1.2 w), (s2.2 w)]; exact hv p w hk
  | succ m ih =>
    intro hm p hp
    have hm' : m < d.ls.length := hm
    have ihm := ih (by omega)
    obtain ⟨hwf, hrd, hKP⟩ := LetsTyped.get3 hLT m (d.ls[m]) (List.getElem?_eq_getElem hm')
    have hlenc := cleanUpTo_length d k m (by omega)
    rw [partialVal_succ d bs vs t x m hm', partialVal_succ d bs' vs' t x m hm']
    rw [cleanUpTo_succ d k m hm'] at hp
    by_cases hpP : p = d.nIn + d.ss.length + m
    · subst hpP
      have hev : eval (fun j => (partialVal d bs vs t x m).b (d.bpos j))
            (fun j w => (partialVal d bs vs t x m).v (d.vpos j) w) (d.ls[m]).2 =
          eval (fun j => (partialVal d bs' vs' t x m).b (d.bpos j))
            (fun j w => (partialVal d bs' vs' t x m).v (d.vpos j) w) (d.ls[m]).2 := by
        -- the position is ok: either below `kDOf d + k`, or the flag of this `let` is true
        have hok' : d.nIn + d.ss.length + m < kDOf d + k ∨
            reads (fun j => posOk d k (cleanUpTo d k m) (d.bpos j)) (fun j => posOk d k (cleanUpTo d k m) (d.vpos j))
              (d.ls[m]).2 = true := by
          rcases posOk_self d k (cleanUpTo d k m) _ (by rw [hlenc]; exact hp) with h | h
          · exact Or.inl (by rw [hlenc] at h; exact h)
          · exact Or.inr h
        rcases hok' with hlt | hflag
        · refine eval_congr_wf (okB := fun j => decide (d.bpos j < d.nIn + d.ss.length + m))
            (okV := fun j => decide (d.vpos j < d.nIn + d.ss.length + m)) (kb := d.kb) (kv := d.kv) (vw := d.vw)
            (fun j hj hokj => ?_) (fun j hj hokj => ?_) _ hwf hrd
          · have hlt' : d.bpos j < d.nIn + d.ss.length + m := by simpa using hokj
            have hpo : posOk d k (cleanUpTo d k m) (d.bpos j) = true := by
              unfold posOk; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
              exact Or.inl (Or.inl (by omega))
            exact (ihm _ hpo).1 (fb j hj).1
          · have hlt' : d.vpos j < d.nIn + d.ss.length + m := by simpa using hokj
            have hpo : posOk d k (cleanUpTo d k m) (d.vpos j) = true := by
              unfold posOk; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
              exact Or.inl (Or.inl (by omega))
            exact (ihm _ hpo).2 (d.vw j) (fv j hj).1
        · refine eval_congr_wf (okB := fun j => posOk d k (cleanUpTo d k m) (d.bpos j))
            (okV := fun j => posOk d k (cleanUpTo d k m) (d.vpos j)) (kb := d.kb) (kv := d.kv) (vw := d.vw)
            (fun j hj hokj => ?_) (fun j hj hokj => ?_) _ hwf hflag
          · exact (ihm _ hokj).1 (fb j hj).1
          · exact (ihm _ hokj).2 (d.vw j) (fv j hj).1
      generalize d.ls[m] = lm at hev hKP
      obtain ⟨s, e⟩ := lm
      simp only at hev hKP
      cases s with
      | bool =>
        refine ⟨fun _ => ?_, fun w hw => ?_⟩
        · rw [set_b_eq, set_b_eq]; exact hev
        · rw [hKP] at hw; cases hw
      | bits w0 =>
        refine ⟨fun hw => ?_, fun w hw => ?_⟩
        · rw [hKP] at hw; cases hw
        · rw [hKP] at hw
          have : w0 = w := by injection hw with h; injection h
          subst this
          rw [set_v_eq, set_v_eq]; exact hev
    · have hp2 : posOk d k (cleanUpTo d k m) p = true := by
        rw [← posOk_step d k (cleanUpTo d k m) _ p (by omega)]; exact hp
      have a := ihm p hp2
      exact ⟨fun h => by rw [set_b_ne hpP, set_b_ne hpP]; exact a.1 h,
        fun w h => by rw [set_v_ne hpP, set_v_ne hpP]; exact a.2 w h⟩

/-- sort-aware stage preservation of the full typed valuation (internal; `typedVal_let_congr` of the freeze is stronger and not provable, see the addendum) -/
theorem typedVal_let_agree (d : MachineData) (hok : d.ok = true) (k : Nat) {D : DomainConfig}
    (bs bs' : Nat → Signal D Bool) (vs vs' : (j n : Nat) → Signal D (BitVec n)) (t : Nat) (x : HList (tys d.ss))
    (hb : ∀ p, p < kDOf d + k → (bs p).val t = (bs' p).val t)
    (hv : ∀ p w, p < kDOf d + k → (vs p w).val t = (vs' p w).val t) :
    ∀ p, posOk d k (cleanLets d k) p = true →
      AgrAt d (typedVal d.nIn d.bpos d.vpos d.ss d.ls bs vs t x)
        (typedVal d.nIn d.bpos d.vpos d.ss d.ls bs' vs' t x) p := by
  intro p hp
  rw [typedVal_eq_partial, typedVal_eq_partial]
  exact partial_agr d hok k bs bs' vs vs' t x hb hv d.ls.length (Nat.le_refl _) p (by rw [cleanUpTo_full]; exact hp)

theorem lsrcAt_congr (d : MachineData) (hok : d.ok = true) (k : Nat) {D : DomainConfig}
    (bs bs' : Nat → Signal D Bool) (vs vs' : (j n : Nat) → Signal D (BitVec n))
    (S : Signal D (HList (tys d.ss))) (t : Nat)
    (hb : ∀ p, p < kDOf d + k → (bs p).val t = (bs' p).val t)
    (hv : ∀ p w, p < kDOf d + k → (vs p w).val t = (vs' p w).val t) :
    ∀ l, (cleanLets d k)[l]? = some true → lsrcGet (lsrcAt d bs vs S) l t = lsrcGet (lsrcAt d bs' vs' S) l t := by
  intro l hl
  obtain ⟨fb, fv, fslots⟩ := ok_Kfacts d hok
  have hLT := Tools.ShippingQuadCalls.ok_letsTyped d hok
  unfold lsrcGet lsrcAt
  simp only [List.getElem?_map]
  cases hls : d.ls[l]? with
  | none => rfl
  | some lt =>
    have hl' : l < d.ls.length := by
      rcases Nat.lt_or_ge l d.ls.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hls; cases hls
    have hwf := LetsTyped.get hLT l lt hls
    -- the flag of let `l`
    have hflag : reads (fun j => posOk d k (cleanUpTo d k l) (d.bpos j)) (fun j => posOk d k (cleanUpTo d k l) (d.vpos j))
        lt.2 = true := by
      have h1 := cleanUpTo_stable d k (l + 1) l (by omega) (d.ls.length - (l + 1)) (by omega)
      rw [show l + 1 + (d.ls.length - (l + 1)) = d.ls.length by omega, cleanUpTo_full, hl,
        cleanUpTo_succ d k l hl'] at h1
      have hlenc := cleanUpTo_length d k l (by omega)
      rw [List.getElem?_append_right (by omega), hlenc] at h1
      have hlt : d.ls[l] = lt := Option.some.inj ((List.getElem?_eq_getElem hl').symm.trans hls)
      rw [hlt] at h1
      simpa using h1.symm
    simp only [Option.map_some, Option.getD_some]
    congr 1
    refine eval_congr_wf (okB := fun j => posOk d k (cleanUpTo d k l) (d.bpos j))
      (okV := fun j => posOk d k (cleanUpTo d k l) (d.vpos j)) (kb := d.kb) (kv := d.kv) (vw := d.vw)
      (fun j hj hokj => ?_) (fun j hj hokj => ?_) _ hwf hflag
    · have hpo := posOk_mono d k l d.ls.length (by omega) (Nat.le_refl _) _ hokj
      rw [cleanUpTo_full] at hpo
      exact (typedVal_let_agree d hok k bs bs' vs vs' t (S.val t) hb hv _ hpo).1 (fb j hj).1
    · have hpo := posOk_mono d k l d.ls.length (by omega) (Nat.le_refl _) _ hokj
      rw [cleanUpTo_full] at hpo
      exact (typedVal_let_agree d hok k bs bs' vs vs' t (S.val t) hb hv _ hpo).2 (d.vw j) (fv j hj).1

end Tools.ShippingGen5Sem
