import Tools.ShippingFGCircuitS3vBridge
set_option autoImplicit false
-- FG circuit pilot S3w, step 2 (bridge extension): `FragW`, the fragment of S3v's `Frag` plus a `boolInput` that reads a `let` of sort `bool` (not an input position).  `tlpCplByte`'s output reads fifteen such Bool lets (`compare .eq`).  The soundness lemmas are S3v's `tC_sound`/`letsC_sound`/`ofData_sound` with the one added case; S3v's files are not changed.   docs/FG-CIRCUIT-PILOT.md §72.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3wBridge
open Tools.ShippingFGCircuitS3tComb Tools.ShippingFGCircuitS3tCombRun Tools.ShippingUnifiedSource
open Tools.ShippingMachineAuto Tools.ShippingMachineDenote
open Tools.ShippingFGCircuitS3vBridge (sortW Rel PosRel LetInv enc_bool enc_bits letVal_lt posRel_set posRel_set_ne mapM_some letTV)
open Tools.ShippingMuxLoweringSoundness (encodeBool)
open Sparkle.Core (HList)

/-- the fragment: S3v's `Frag`, plus a `boolInput` that is not an input position and reads a `let` of sort `bool` -/
def FragW (d : MachineData) : {s : SType} → Term s → Bool
  | _, .boolInput j =>
    decide (d.nIn ≤ d.bpos j) && decide ((d.ls[d.bpos j - d.nIn - d.ss.length]?).map (·.1) = some .bool)
  | _, .bitsInput w j =>
    decide (d.vpos j < d.nIn) ||
      decide ((d.ls[d.vpos j - d.nIn - d.ss.length]?).map (·.1) = some (.bits w))
  | _, .boolLit _ => true
  | _, .bitsLit _ _ => true
  | _, .compare .eq a b => FragW d a && FragW d b
  | _, .mux c a b => FragW d c && FragW d a && FragW d b
  | _, .slice _ _ len a => decide (0 < len) && FragW d a
  | _, .concat a b => FragW d a && FragW d b
  | _, _ => true

theorem tC_soundW (d : MachineData) (hss : d.ss.length = 0) (V : Nat → Nat) (T : TVal)
    (pre : List (Σ s : SType, Term s)) (acc : List CTerm)
    (hpre : ∀ (k : Nat) l, pre[k]? = some l → d.ls[k]? = some l)
    (hin : ∀ p w, p < d.nIn → (T.v p w).toNat = V p % 2 ^ w)
    (hlet : LetInv d V T pre acc) :
    ∀ {s : SType} (t : Term s) (c : CTerm), FragW d t = true → tC d (fun l => acc[l]?) t = some c →
      Rel V s (eval (fun j => T.b (d.bpos j)) (fun j w => T.v (d.vpos j) w) t) c
  | _, .boolInput j, c, hf, h => by
    simp only [FragW, Bool.and_eq_true, decide_eq_true_eq] at hf
    obtain ⟨hnin, hf⟩ := hf
    simp only [tC] at h
    have hlt : ¬ d.bpos j < d.nIn := by omega
    rw [if_neg hlt] at h
    obtain ⟨l0, hl0, hrel⟩ := hlet _ _ h
    have hls := hpre _ _ hl0
    rw [hls] at hf
    obtain ⟨s0, t0⟩ := l0
    simp only [Option.map_some, Option.some.injEq] at hf
    subst hf
    have hp : d.nIn + d.ss.length + (d.bpos j - d.nIn - d.ss.length) = d.bpos j := by omega
    rw [hp] at hrel
    exact hrel
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
          simp only [FragW, Bool.or_eq_true, decide_eq_true_eq] at hf
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
        simp only [FragW, Bool.and_eq_true] at hf
        have ra := tC_soundW d hss V T pre acc hpre hin hlet a ca hf.1 ha
        have rb := tC_soundW d hss V T pre acc hpre hin hlet b cb hf.2 hb
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
      simp only [FragW, Bool.and_eq_true] at hf
      have rc := tC_soundW d hss V T pre acc hpre hin hlet cc ccc hf.1.1 hc
      have ra := tC_soundW d hss V T pre acc hpre hin hlet a ca hf.1.2 ha
      have rb := tC_soundW d hss V T pre acc hpre hin hlet b cb hf.2 hb
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
      simp only [FragW, Bool.and_eq_true, decide_eq_true_eq] at hf
      have ra := tC_soundW d hss V T pre acc hpre hin hlet a ca hf.2 ha
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
      simp only [FragW, Bool.and_eq_true] at hf
      have ra := tC_soundW d hss V T pre acc hpre hin hlet a ca hf.1 ha
      have rb := tC_soundW d hss V T pre acc hpre hin hlet b cb hf.2 hb
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


theorem letsC_soundW (d : MachineData) (hss : d.ss.length = 0) (V : Nat → Nat) :
    ∀ (rest pre : List (Σ s : SType, Term s)) (acc lc : List CTerm) (T : TVal),
      pre ++ rest = d.ls → pre.length = acc.length →
      (∀ p w, p < d.nIn → (T.v p w).toNat = V p % 2 ^ w) → LetInv d V T pre acc →
      (∀ l ∈ rest, FragW d l.2 = true) → letsC d rest acc = some lc →
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
      have hfl : FragW d l.2 = true := hF l (by simp)
      have hpre : ∀ (k : Nat) l', pre[k]? = some l' → d.ls[k]? = some l' := by
        intro k l' hk
        rw [← hd]
        have hkl : k < pre.length := (List.getElem?_eq_some_iff.mp hk).1
        rw [List.getElem?_append_left hkl]; exact hk
      have rel := tC_soundW d hss V T pre acc hpre hin hlet l.2 c hfl hc
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
      have ih := letsC_soundW d hss V rest (pre ++ [l]) (acc ++ [c]) lc _
        (by simpa using hd) (by simp [hl]) hT1 hlet1 (fun l' hl' => hF l' (by simp [hl'])) h
      have e : d.nIn + d.ss.length + (acc ++ [c]).length = d.nIn + d.ss.length + acc.length + 1 := by
        simp; omega
      rw [e] at ih
      simpa [letVal] using ih
    · cases h

/-- **the bridge** (for data with no state, whose lets and outputs are in `FragW`): if `ofData d = some s`, then at any position valuation `V` that the input values `W` realise (`(W p w).toNat = V p % 2 ^ w` below `nIn`), every output's source term denotes the encoding of the value `Term.eval` gives the data's output term under the typed valuation (`typedVal`), with the sort's width -/
theorem ofData_soundW (d : MachineData) (hss : d.ss.length = 0) (V : Nat → Nat)
    (x : HList (tys d.ss)) (B : Nat → Bool) (W : (p w : Nat) → BitVec w)
    (hW : ∀ p w, p < d.nIn → (W p w).toNat = V p % 2 ^ w)
    (hfl : ∀ l ∈ d.ls, FragW d l.2 = true) (hfo : ∀ o ∈ d.outs, FragW d o.2 = true)
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
      obtain ⟨hin1, hlet1⟩ := letsC_soundW d hss V d.ls [] [] lc _ (by simp) rfl hin0
        (by intro k c hk; simp at hk) hfl hlc
      refine ⟨rfl, hl1, ?_⟩
      intro k o c ho hc
      have hf := hfo o (List.mem_of_getElem? ho)
      exact tC_soundW d hss V (letTV d x B W) ([] ++ d.ls) lc (fun k l h => by simpa using h) hin1 hlet1 o.2 c hf
        (hl2 k o c ho hc)
  · cases h

end Tools.ShippingFGCircuitS3wBridge
