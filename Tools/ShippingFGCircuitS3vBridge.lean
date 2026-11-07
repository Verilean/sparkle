import Tools.ShippingFGCircuitS3tCombRun
set_option autoImplicit false
-- FG circuit pilot S3v, step 1: the bridge from the source terms `ofData` reads off a `MachineData` (`CTerm`) to the typed semantics (`Term.eval` on `typedVal`).  A GENERAL lemma under explicit side conditions that are decidable facts about the data (`d.ss.length = 0`, and `Frag`: every term of the lets and outputs is in the fragment `tC` covers with a positive slice length and a `bitsInput` that reads a bits-sorted position); nothing is assumed as a hypothesis for the pilot: they are proved for `httpGetByte` by the kernel in `Tools.ShippingFGCircuitS3vChild`.  docs/FG-CIRCUIT-PILOT.md §71.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3vBridge
open Tools.ShippingFGCircuitS3tComb Tools.ShippingFGCircuitS3tCombRun Tools.ShippingUnifiedSource
open Tools.ShippingMachineAuto Tools.ShippingMachineDenote
open Tools.ShippingMuxLoweringSoundness (encodeBool)

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

end Tools.ShippingFGCircuitS3vBridge
