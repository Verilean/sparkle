import Sparkle.Core.Signal
import Tools.VedU1Packed

/-!
# Value lemmas for the `Signal op BitVec` instances

`Tools/VedU1Lemmas.lean` states the scalar-operand lemmas over `a op Signal.pure b` (the instance the
elaborator picks when the expected type is known).  Inside a `Signal.loop fun state => …` the
literal operand of `busyCntReg - 1#5` elaborates to the other instance (`HSub (Signal _) (BitVec n)`,
`instHSubSignalBitVec_1`), whose `val` the simp set could not unfold.  These lemmas are the same
equations for the mixed instances; every one is `rfl` (no axiom).
-/

namespace Tools.VedU1MultiSeqLemmas

open Sparkle.Core.Domain Sparkle.Core.Signal

variable {dom : DomainConfig} {n : Nat}

theorem add_val_scI (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HAdd.hAdd (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s + b := rfl
theorem add_val_csI (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HAdd.hAdd (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a + b.val s := rfl
theorem sub_val_scI (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HSub.hSub (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s - b := rfl
theorem sub_val_csI (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HSub.hSub (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a - b.val s := rfl
theorem mul_val_scI (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HMul.hMul (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s * b := rfl
theorem mul_val_csI (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HMul.hMul (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a * b.val s := rfl
theorem and_val_scI (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HAnd.hAnd (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s &&& b := rfl
theorem and_val_csI (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HAnd.hAnd (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a &&& b.val s := rfl
theorem or_val_scI (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HOr.hOr (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s ||| b := rfl
theorem or_val_csI (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HOr.hOr (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a ||| b.val s := rfl
theorem xor_val_scI (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HXor.hXor (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s ^^^ b := rfl
theorem xor_val_csI (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HXor.hXor (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a ^^^ b.val s := rfl
theorem shl_val_scI (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HShiftLeft.hShiftLeft (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s <<< b := rfl
theorem shl_val_csI (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HShiftLeft.hShiftLeft (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a <<< b.val s := rfl
theorem shr_val_scI (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HShiftRight.hShiftRight (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s >>> b := rfl
theorem shr_val_csI (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HShiftRight.hShiftRight (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a >>> b.val s := rfl
theorem append_val_scI {m : Nat} (a : Signal dom (BitVec m)) (b : BitVec n) (s : Nat) :
    (@HAppend.hAppend (Signal dom (BitVec m)) (BitVec n) (Signal dom (BitVec (m + n))) _ a b).val s = a.val s ++ b := rfl
theorem append_val_csI {m : Nat} (a : BitVec m) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HAppend.hAppend (BitVec m) (Signal dom (BitVec n)) (Signal dom (BitVec (m + n))) _ a b).val s = a ++ b.val s := rfl

/-! ## The packed value as a sum

`OTy.packNat` ORs the leaves, shifted by the widths after them; every leaf is below its own power
of two, so the OR is a sum.  The generated proofs use the additive form (omega does not know
`|||`). -/

open Tools.VedU1Contract Tools.VedU1Packed

theorem PTy_obs_lt (p : PTy) (v : p.val) : p.obs v < 2 ^ p.width := by
  cases p with
  | bit =>
    cases (show Bool from v) <;> simp [PTy.obs, PTy.width]
  | bv w => exact (show BitVec w from v).isLt

theorem OTy_packNat_lt (o : OTy) (v : o.val) : o.packNat v < 2 ^ o.width := by
  induction o with
  | leaf p => exact PTy_obs_lt p v
  | pair a b iha ihb =>
    have ha := iha v.1
    have hb := ihb v.2
    show (a.packNat v.1 <<< b.width ||| b.packNat v.2) < 2 ^ (a.width + b.width)
    rw [cat_eq _ _ _ hb, Nat.pow_add]
    have h1 : (a.packNat v.1 + 1) * 2 ^ b.width ≤ 2 ^ a.width * 2 ^ b.width :=
      Nat.mul_le_mul_right _ ha
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega

theorem OTy_packNat_pair (a b : OTy) (v : (OTy.pair a b).val) :
    (OTy.pair a b).packNat v = a.packNat v.1 * 2 ^ b.width + b.packNat v.2 := by
  show a.packNat v.1 <<< b.width ||| b.packNat v.2 = _
  exact cat_eq _ _ _ (OTy_packNat_lt b v.2)

theorem OTy_packNat_leaf (p : PTy) (v : (OTy.leaf p).val) : (OTy.leaf p).packNat v = p.obs v := rfl

/-- `x ^^^ (2^k - 1)` is the complement of `x` in `k` bits. -/
theorem xor_ones (x c k : Nat) (hc : c + 1 = 2 ^ k) (h : x < 2 ^ k) : x ^^^ c = c - x := by
  have h1 : (BitVec.ofNat k x).toNat = x := by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  have h2 := congrArg BitVec.toNat (BitVec.xor_allOnes (x := BitVec.ofNat k x))
  rw [BitVec.toNat_xor, BitVec.toNat_allOnes, BitVec.toNat_not, h1] at h2
  have hc' : c = 2 ^ k - 1 := by omega
  subst hc'
  exact h2

end Tools.VedU1MultiSeqLemmas
