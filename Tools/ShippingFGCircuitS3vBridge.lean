import Tools.ShippingFGCircuitS3tCombRun
set_option autoImplicit false
-- FG circuit pilot S3v, step 1: the bridge from the source terms `ofData` reads off a `MachineData` (`CTerm`) to the typed semantics (`Term.eval` on `typedVal`).  A GENERAL lemma under explicit side conditions that are decidable facts about the data (`d.ss.length = 0`, and `Frag`: every term of the lets and outputs is in the fragment `tC` covers with a positive slice length and a `bitsInput` that reads a bits-sorted position); nothing is assumed as a hypothesis for the pilot: they are proved for `httpGetByte` by the kernel in `Tools.ShippingFGCircuitS3vChild`.  docs/FG-CIRCUIT-PILOT.md §71.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3vBridge
open Tools.ShippingFGCircuitS3tComb Tools.ShippingFGCircuitS3tCombRun Tools.ShippingUnifiedSource
open Tools.ShippingMachineAuto Tools.ShippingMachineDenote
open Tools.ShippingMuxLoweringSoundness (encodeBool)
open Sparkle.Core (HList)

/-- the bit width of a sort's encoding -/
def sortW : SType → Nat
  | .bool => 1
  | .bits w => w

/-- a typed value `x` of sort `s` and a source term `c` correspond under the position valuation `V`: the term's value is the value's encoding and its width is the sort's -/
def Rel (V : Nat → Nat) (s : SType) (x : s.Type) (c : CTerm) : Prop :=
  c.den V = enc s x ∧ c.width = sortW s

/-- the same for the value a typed valuation holds at position `p` -/
def PosRel (V : Nat → Nat) (T : TVal) (p : Nat) : SType → CTerm → Prop
  | .bool, c => Rel V .bool (T.b p) c
  | .bits w, c => Rel V (.bits w) (T.v p w) c

/-- the translated `let`s `acc` (one per earlier `let`, in order) correspond to the typed values the valuation `T` holds at their positions; `pre` lists their sorts -/
def LetInv (d : MachineData) (V : Nat → Nat) (T : TVal) (pre : List (Σ s : SType, Term s)) (acc : List CTerm) : Prop :=
  ∀ (k : Nat) (c : CTerm), acc[k]? = some c → ∃ l, pre[k]? = some l ∧ PosRel V T (d.nIn + d.ss.length + k) l.1 c

/-- the fragment: the terms `tC` covers, with a positive slice length, no Bool input, and a `bitsInput` that is an input position or reads a `let` of bits sort of that width -/
def Frag (d : MachineData) : {s : SType} → Term s → Bool
  | _, .boolInput _ => false
  | _, .bitsInput w j =>
    decide (d.vpos j < d.nIn) ||
      decide ((d.ls[d.vpos j - d.nIn - d.ss.length]?).map (·.1) = some (.bits w))
  | _, .boolLit _ => true
  | _, .bitsLit _ _ => true
  | _, .compare .eq a b => Frag d a && Frag d b
  | _, .mux c a b => Frag d c && Frag d a && Frag d b
  | _, .slice _ _ len a => decide (0 < len) && Frag d a
  | _, .concat a b => Frag d a && Frag d b
  | _, _ => true

theorem enc_bool (x : Bool) : enc .bool x = encodeBool x := rfl
theorem enc_bits (w : Nat) (x : BitVec w) : enc (.bits w) x = x.toNat := rfl

theorem tC_sound (d : MachineData) (hss : d.ss.length = 0) (V : Nat → Nat) (T : TVal)
    (pre : List (Σ s : SType, Term s)) (acc : List CTerm)
    (hpre : ∀ (k : Nat) l, pre[k]? = some l → d.ls[k]? = some l)
    (hin : ∀ p w, p < d.nIn → (T.v p w).toNat = V p % 2 ^ w)
    (hlet : LetInv d V T pre acc) :
    ∀ {s : SType} (t : Term s) (c : CTerm), Frag d t = true → tC d (fun l => acc[l]?) t = some c →
      Rel V s (eval (fun j => T.b (d.bpos j)) (fun j w => T.v (d.vpos j) w) t) c
  | _, .boolInput j, c, hf, h => by simp [Frag] at hf
  | _, .bitsInput w j, c, hf, h => by
    simp only [tC] at h
    split at h
    · rename_i hlt
      cases h
      refine ⟨?_, rfl⟩
      simp only [CTerm.den, eval, enc_bits]
      exact (hin _ _ hlt).symm
    · rename_i hlt
      split at h
      · rename_i c' hc'
        split at h
        · rename_i hw
          cases h
          obtain ⟨l0, hl0, hrel⟩ := hlet _ _ hc'
          have hls := hpre _ _ hl0
          simp only [Frag, Bool.or_eq_true, decide_eq_true_eq] at hf
          rcases hf with hf | hf
          · exact absurd hf hlt
          · rw [hls] at hf
            obtain ⟨s0, t0⟩ := l0
            simp only [Option.map_some, Option.some.injEq] at hf
            subst hf
            have hp : d.nIn + d.ss.length + (d.vpos j - d.nIn - d.ss.length) = d.vpos j := by omega
            rw [hp] at hrel
            exact hrel
        · cases h
      · cases h
  | _, .boolLit b, c, hf, h => by
    simp only [tC] at h
    cases h
    refine ⟨?_, rfl⟩
    cases b <;> simp [CTerm.den, eval, enc_bool, encodeBool]
  | _, .bitsLit w v, c, hf, h => by
    simp only [tC] at h
    cases h
    refine ⟨?_, rfl⟩
    simp [CTerm.den, eval, enc_bits]
  | _, .compare op (w := w) a b, c, hf, h => by
    cases op
    case eq =>
      simp only [tC] at h
      split at h
      · rename_i ca cb ha hb
        cases h
        simp only [Frag, Bool.and_eq_true] at hf
        have ra := tC_sound d hss V T pre acc hpre hin hlet a ca hf.1 ha
        have rb := tC_sound d hss V T pre acc hpre hin hlet b cb hf.2 hb
        obtain ⟨e1, -⟩ := ra
        obtain ⟨e2, -⟩ := rb
        rw [enc_bits] at e1 e2
        refine ⟨?_, rfl⟩
        simp only [eval, Tools.ShippingBoolSourceSoundness.compareValue]
        generalize eval (fun j => T.b (d.bpos j)) (fun j w => T.v (d.vpos j) w) a = x at e1 ⊢
        generalize eval (fun j => T.b (d.bpos j)) (fun j w => T.v (d.vpos j) w) b = y at e2 ⊢
        simp only [CTerm.den, e1, e2, enc_bool]
        by_cases hxy : x = y
        · subst hxy; simp [encodeBool]
        · have : x.toNat ≠ y.toNat := fun h => hxy (BitVec.eq_of_toNat_eq h)
          simp [this, encodeBool, hxy]
      · cases h
    all_goals simp [tC] at h
  | _, .mux (s := s') cc a b, c, hf, h => by
    simp only [tC] at h
    split at h
    · rename_i ccc ca cb hc ha hb
      cases h
      simp only [Frag, Bool.and_eq_true] at hf
      have rc := tC_sound d hss V T pre acc hpre hin hlet cc ccc hf.1.1 hc
      have ra := tC_sound d hss V T pre acc hpre hin hlet a ca hf.1.2 ha
      have rb := tC_sound d hss V T pre acc hpre hin hlet b cb hf.2 hb
      obtain ⟨rc1, -⟩ := rc
      refine ⟨?_, ?_⟩
      · simp only [eval]
        generalize eval (fun j => T.b (d.bpos j)) (fun j w => T.v (d.vpos j) w) cc = xc at rc1 ⊢
        cases xc <;> simp [CTerm.den, rc1, encodeBool, enc_bool, ra.1, rb.1]
      · simp [CTerm.width, ra.2]
    · cases h
  | _, .slice _ start len (w := w) a, c, hf, h => by
    simp only [tC] at h
    split at h
    · rename_i ca ha
      cases h
      simp only [Frag, Bool.and_eq_true, decide_eq_true_eq] at hf
      have ra := tC_sound d hss V T pre acc hpre hin hlet a ca hf.2 ha
      obtain ⟨e1, e2⟩ := ra
      rw [enc_bits] at e1
      have hl : start + len - 1 - start + 1 = len := by omega
      refine ⟨?_, ?_⟩
      · simp only [CTerm.den, eval, enc_bits, BitVec.extractLsb'_toNat, e1, hl]
      · simp only [CTerm.width, sortW, hl]
    · cases h
  | _, .concat (m := m) (n := n) a b, c, hf, h => by
    simp only [tC] at h
    split at h
    · rename_i ca cb ha hb
      cases h
      simp only [Frag, Bool.and_eq_true] at hf
      have ra := tC_sound d hss V T pre acc hpre hin hlet a ca hf.1 ha
      have rb := tC_sound d hss V T pre acc hpre hin hlet b cb hf.2 hb
      obtain ⟨e1, f1⟩ := ra
      obtain ⟨e2, f2⟩ := rb
      rw [enc_bits] at e1 e2
      simp only [sortW] at f1 f2
      refine ⟨?_, ?_⟩
      · simp only [CTerm.den, eval, enc_bits, BitVec.toNat_append, e1, e2, f2]
      · simp only [CTerm.width, sortW, f1, f2]
    · cases h
  | _, .bitsNum .., c, hf, h => by simp [tC] at h
  | _, .binary .., c, hf, h => by simp [tC] at h
  | _, .boolBinary .., c, hf, h => by simp [tC] at h
  | _, .boolNot .., c, hf, h => by simp [tC] at h
  | _, .boolEq .., c, hf, h => by simp [tC] at h
  | _, .setw .., c, hf, h => by simp [tC] at h
  | _, .appCompare .., c, hf, h => by simp [tC] at h
  | _, .appBool .., c, hf, h => by simp [tC] at h
  | _, .appBool2 .., c, hf, h => by simp [tC] at h
  | _, .concatLitHi .., c, hf, h => by simp [tC] at h
  | _, .concatLitLo .., c, hf, h => by simp [tC] at h
  | _, .zextMap .., c, hf, h => by simp [tC] at h
  | _, .sliceF .., c, hf, h => by simp [tC] at h


theorem letVal_lt (bpos vpos : Nat → Nat) : ∀ (rest : List (Σ s : SType, Term s)) (p : Nat) (T : TVal) (q : Nat),
    q < p → (letVal bpos vpos rest p T).b q = T.b q ∧ ∀ n, (letVal bpos vpos rest p T).v q n = T.v q n
  | [], _, _, _, _ => ⟨rfl, fun _ => rfl⟩
  | l :: rest, p, T, q, h => by
    obtain ⟨hb, hv⟩ := letVal_lt bpos vpos rest (p + 1)
      (T.set p l.1 (eval (fun j => T.b (bpos j)) (fun j w => T.v (vpos j) w) l.2)) q (by omega)
    exact ⟨hb.trans (set_b_ne (by omega)), fun n => (hv n).trans (set_v_ne (by omega) n)⟩

theorem posRel_set (V : Nat → Nat) (T : TVal) (p : Nat) (s : SType) (x : s.Type) (c : CTerm)
    (h : Rel V s x c) : PosRel V (T.set p s x) p s c := by
  cases s with
  | bool => simp only [PosRel]; rw [set_b_eq]; exact h
  | bits w => simp only [PosRel]; rw [set_v_eq]; exact h

theorem posRel_set_ne (V : Nat → Nat) (T : TVal) (p q : Nat) (s : SType) (x : s.Type) (s0 : SType) (c : CTerm)
    (hq : q ≠ p) (h : PosRel V T q s0 c) : PosRel V (T.set p s x) q s0 c := by
  cases s0 with
  | bool => simp only [PosRel] at h ⊢; rw [set_b_ne hq]; exact h
  | bits w => simp only [PosRel] at h ⊢; rw [set_v_ne hq]; exact h

theorem letsC_sound (d : MachineData) (hss : d.ss.length = 0) (V : Nat → Nat) :
    ∀ (rest pre : List (Σ s : SType, Term s)) (acc lc : List CTerm) (T : TVal),
      pre ++ rest = d.ls → pre.length = acc.length →
      (∀ p w, p < d.nIn → (T.v p w).toNat = V p % 2 ^ w) → LetInv d V T pre acc →
      (∀ l ∈ rest, Frag d l.2 = true) → letsC d rest acc = some lc →
      (∀ p w, p < d.nIn →
        ((letVal d.bpos d.vpos rest (d.nIn + d.ss.length + acc.length) T).v p w).toNat = V p % 2 ^ w) ∧
      LetInv d V (letVal d.bpos d.vpos rest (d.nIn + d.ss.length + acc.length) T) (pre ++ rest) lc
  | [], pre, acc, lc, T, hd, hl, hin, hlet, hF, h => by
    simp only [letsC, Option.some.injEq] at h
    subst h
    simpa [letVal] using ⟨hin, hlet⟩
  | l :: rest, pre, acc, lc, T, hd, hl, hin, hlet, hF, h => by
    simp only [letsC] at h
    split at h
    · rename_i c hc
      have hfl : Frag d l.2 = true := hF l (by simp)
      have hpre : ∀ (k : Nat) l', pre[k]? = some l' → d.ls[k]? = some l' := by
        intro k l' hk
        rw [← hd]
        have hkl : k < pre.length := (List.getElem?_eq_some_iff.mp hk).1
        rw [List.getElem?_append_left hkl]; exact hk
      have rel := tC_sound d hss V T pre acc hpre hin hlet l.2 c hfl hc
      have hT1 : ∀ p w, p < d.nIn →
          (((T.set (d.nIn + d.ss.length + acc.length) l.1
            (eval (fun j => T.b (d.bpos j)) (fun j w => T.v (d.vpos j) w) l.2)).v p w).toNat = V p % 2 ^ w) := by
        intro p w hp
        rw [set_v_ne (by omega)]
        exact hin p w hp
      have hlet1 : LetInv d V (T.set (d.nIn + d.ss.length + acc.length) l.1
          (eval (fun j => T.b (d.bpos j)) (fun j w => T.v (d.vpos j) w) l.2)) (pre ++ [l]) (acc ++ [c]) := by
        intro k c' hk
        by_cases hka : k < acc.length
        · rw [List.getElem?_append_left hka] at hk
          obtain ⟨l', hl', hrel⟩ := hlet k c' hk
          refine ⟨l', ?_, posRel_set_ne V T _ _ _ _ _ _ (by omega) hrel⟩
          rw [List.getElem?_append_left (by omega)]; exact hl'
        · have hke : k = acc.length := by
            have := (List.getElem?_eq_some_iff.mp hk).1
            simp at this; omega
          subst hke
          have hc' : c' = c := by simpa using hk.symm
          subst hc'
          refine ⟨l, ?_, posRel_set V T _ _ _ _ rel⟩
          simp [hl]
      have ih := letsC_sound d hss V rest (pre ++ [l]) (acc ++ [c]) lc _
        (by simpa using hd) (by simp [hl]) hT1 hlet1 (fun l' hl' => hF l' (by simp [hl'])) h
      have e : d.nIn + d.ss.length + (acc ++ [c]).length = d.nIn + d.ss.length + acc.length + 1 := by
        simp; omega
      rw [e] at ih
      simpa [letVal] using ih
    · cases h

theorem mapM_some {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β), l.mapM f = some r →
    r.length = l.length ∧ ∀ (k : Nat) a c, l[k]? = some a → r[k]? = some c → f a = some c
  | [], r, h => by simp [List.mapM_nil] at h; subst h; simp
  | a :: l, r, h => by
    simp only [List.mapM_cons] at h
    cases hb : f a with
    | none => simp [hb] at h
    | some b =>
      cases hr : List.mapM f l with
      | none => simp [hb, hr] at h
      | some bs =>
        simp [hb, hr] at h
        subst h
        obtain ⟨h1, h2⟩ := mapM_some f l bs hr
        refine ⟨by simp [h1], ?_⟩
        intro k a' c ha hc
        cases k with
        | zero => simp at ha hc; subst ha; subst hc; exact hb
        | succ k => exact h2 k a' c (by simpa using ha) (by simpa using hc)

/-- the typed valuation of a cycle of the data's terms, at the input values `B`/`W` and state `x` (what `typedVal` is, at a time) -/
def letTV (d : MachineData) (x : HList (tys d.ss)) (B : Nat → Bool) (W : (p w : Nat) → BitVec w) : TVal :=
  letVal d.bpos d.vpos d.ls (d.nIn + d.ss.length) (slotVal d.nIn d.ss x 0 ⟨B, W⟩)

theorem typedVal_eq {D : Sparkle.Core.Domain.DomainConfig} (d : MachineData)
    (bools : Nat → Sparkle.Core.Signal.Signal D Bool)
    (bits : (j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal D (BitVec n)) (t : Nat) (x : HList (tys d.ss)) :
    typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t x =
      letTV d x (fun p => (bools p).val t) (fun p w => (bits p w).val t) := rfl

/-- **the bridge** (for data with no state, whose lets and outputs are in `Frag`): if `ofData d = some s`, then at any position valuation `V` that the input values `W` realise (`(W p w).toNat = V p % 2 ^ w` below `nIn`), every output's source term denotes the encoding of the value `Term.eval` gives the data's output term under the typed valuation (`typedVal`), with the sort's width -/
theorem ofData_sound (d : MachineData) (hss : d.ss.length = 0) (V : Nat → Nat)
    (x : HList (tys d.ss)) (B : Nat → Bool) (W : (p w : Nat) → BitVec w)
    (hW : ∀ p w, p < d.nIn → (W p w).toNat = V p % 2 ^ w)
    (hfl : ∀ l ∈ d.ls, Frag d l.2 = true) (hfo : ∀ o ∈ d.outs, Frag d o.2 = true)
    (s : CSrc) (h : ofData d = some s) :
    s.inPos = inputPositions d ∧ s.outs.length = d.outs.length ∧
    ∀ (k : Nat) (o : Σ s : SType, Term s) (c : CTerm), d.outs[k]? = some o → s.outs[k]? = some c →
      Rel V o.1 (eval (fun j => (letTV d x B W).b (d.bpos j)) (fun j w => (letTV d x B W).v (d.vpos j) w) o.2) c := by
  simp only [ofData] at h
  split at h
  · rename_i lc hlc
    cases hm : d.outs.mapM (fun o => tC d (fun l => lc[l]?) o.2) with
    | none => rw [hm] at h; cases h
    | some os =>
      rw [hm] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨hl1, hl2⟩ := mapM_some _ _ _ hm
      have hin0 : ∀ p w, p < d.nIn →
          ((slotVal d.nIn d.ss x 0 ⟨B, W⟩).v p w).toNat = V p % 2 ^ w := by
        intro p w hp
        rw [(slotVal_lt d.nIn d.ss x 0 ⟨B, W⟩ p (by omega)).2 w]
        exact hW p w hp
      obtain ⟨hin1, hlet1⟩ := letsC_sound d hss V d.ls [] [] lc _ (by simp) rfl hin0
        (by intro k c hk; simp at hk) hfl hlc
      refine ⟨rfl, hl1, ?_⟩
      intro k o c ho hc
      have hf := hfo o (List.mem_of_getElem? ho)
      exact tC_sound d hss V (letTV d x B W) ([] ++ d.ls) lc (fun k l h => by simpa using h) hin1 hlet1 o.2 c hf
        (hl2 k o c ho hc)
  · cases h

end Tools.ShippingFGCircuitS3vBridge
