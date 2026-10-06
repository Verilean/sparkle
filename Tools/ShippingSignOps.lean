import Sparkle.Core.Signal

/-! # Sign extension and arithmetic right shift as derived Signal operators

`BitVec.signExtend` and `BitVec.sshiftRight` go through `toInt`/`ofInt`,
which are stuck on a symbolic value: no kernel `rfl` relates them to the
certified operators. They ARE equal to a combination of those operators,
as theorems:

* `signExtend (k + w) x = fill k (msb x) ++ x`,
* `x.sshiftRight y = ((x ^^^ M) >>> y) ^^^ M` with `M = fill w (msb x)`,

where the sign bit is a 1-bit slice compared with `1#1` and `fill` is a mux
of two literals. The machine route reads the operators in this derived form
(`Sparkle.Compiler.MachSignOps`), and the endpoint generator rewrites the
declaration's value with the Signal-level equations below (`simp`), proves
the endpoint for the rewritten value by the usual kernel `rfl`s, and
transports it back to the declaration along the equation. -/
namespace Tools.ShippingSignOps
open Sparkle.Core.Domain Sparkle.Core.Signal

/-! ## Values -/

/-- The sign bit as the certified route reads it: a 1-bit slice compared with `1#1`. -/
theorem msbSlice_eq {w : Nat} (_hw : 0 < w) (x : BitVec w) :
    (BitVec.extractLsb' (w - 1) 1 x == 1#1) = x.msb := by
  rw [BitVec.msb_eq_getLsbD_last]
  cases h : x.getLsbD (w - 1)
  · have : BitVec.extractLsb' (w - 1) 1 x = 0#1 := by
      apply BitVec.eq_of_getElem_eq; intro i hi
      have : i = 0 := by omega
      subst this; simpa [BitVec.getElem_extractLsb'] using h
    simp [this]
  · have : BitVec.extractLsb' (w - 1) 1 x = 1#1 := by
      apply BitVec.eq_of_getElem_eq; intro i hi
      have : i = 0 := by omega
      subst this; simpa [BitVec.getElem_extractLsb'] using h
    simp [this]

/-- All ones when the condition holds, zero otherwise (a mux of two literals). -/
def fill (k : Nat) (c : Bool) : BitVec k :=
  if c then BitVec.ofNat k (2 ^ k - 1) else BitVec.ofNat k 0

theorem fill_eq (k : Nat) (c : Bool) :
    fill k c = if c then BitVec.allOnes k else 0#k := by
  cases c <;> simp [fill, BitVec.allOnes, BitVec.toNat_eq]

theorem signExtend_derived {w : Nat} (hw : 0 < w) (k : Nat) (x : BitVec w) :
    BitVec.signExtend (k + w) x =
      fill k (BitVec.extractLsb' (w - 1) 1 x == 1#1) ++ x := by
  rw [msbSlice_eq hw, fill_eq]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_signExtend, BitVec.getElem_append]
  by_cases h : i < w
  · simp [h]
  · cases hm : x.msb <;> simp [h, BitVec.getElem_allOnes]

theorem sshiftRight_derived {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    x.sshiftRight y.toNat =
      BitVec.xor (BitVec.ushiftRight (BitVec.xor x (fill w (BitVec.extractLsb' (w - 1) 1 x == 1#1)))
        y.toNat) (fill w (BitVec.extractLsb' (w - 1) 1 x == 1#1)) := by
  rw [msbSlice_eq hw, fill_eq]
  cases hm : x.msb
  · rw [BitVec.sshiftRight_eq_of_msb_false hm]
    simp only [if_false, Bool.false_eq_true]
    apply BitVec.eq_of_getElem_eq; intro i hi
    simp [BitVec.getElem_ushiftRight]
  · rw [BitVec.sshiftRight_eq_of_msb_true hm]
    simp only [if_true]
    apply BitVec.eq_of_getElem_eq; intro i hi
    simp [BitVec.getElem_ushiftRight, BitVec.getElem_not]

/-! ## Signals -/

variable {dom : DomainConfig}

/-- The sign bit of a Signal, as a Bool Signal. -/
def msbS {w : Nat} (x : Signal dom (BitVec w)) : Signal dom Bool :=
  x.map (fun v => BitVec.extractLsb' (w - 1) 1 v) === Signal.pure (BitVec.ofNat 1 1)

/-- All ones when the condition holds, zero otherwise. -/
def fillS (k : Nat) (c : Signal dom Bool) : Signal dom (BitVec k) :=
  Signal.mux c (Signal.pure (BitVec.ofNat k (2 ^ k - 1))) (Signal.pure (BitVec.ofNat k 0))

/-- Sign extension, derived. -/
def sextS (k : Nat) {w : Nat} (x : Signal dom (BitVec w)) : Signal dom (BitVec (k + w)) :=
  fillS k (msbS x) ++ x

/-- Arithmetic right shift by a Signal amount, derived. -/
def ashrS {w : Nat} (x y : Signal dom (BitVec w)) : Signal dom (BitVec w) :=
  ((x ^^^ fillS w (msbS x)) >>> y) ^^^ fillS w (msbS x)

theorem map_signExtend (k : Nat) {w : Nat} (hw : 0 < w) (x : Signal dom (BitVec w)) :
    Signal.map (fun v => BitVec.signExtend (k + w) v) x = sextS k x := by
  cases x with
  | mk xv =>
  show (⟨fun t => BitVec.signExtend (k + w) (xv t)⟩ : Signal dom (BitVec (k + w))) =
    ⟨fun t => _⟩
  congr 1
  funext t
  rw [signExtend_derived hw]
  rfl

theorem ashr_eq {w : Nat} (hw : 0 < w) (x y : Signal dom (BitVec w)) :
    Signal.ashr x y = ashrS x y := by
  cases x with
  | mk xv =>
  cases y with
  | mk yv =>
  show (⟨fun t => (xv t).sshiftRight (yv t).toNat⟩ : Signal dom (BitVec w)) = ⟨fun t => _⟩
  congr 1
  funext t
  rw [sshiftRight_derived hw]
  rfl

theorem lift_sshiftRight {w : Nat} (hw : 0 < w) (x y : Signal dom (BitVec w)) :
    ((fun a b => BitVec.sshiftRight a (BitVec.toNat b)) <$> x <*> y) = ashrS x y :=
  ashr_eq hw x y

theorem ap_sshiftRight {w : Nat} (hw : 0 < w) (x y : Signal dom (BitVec w)) :
    Signal.ap (Signal.map (fun a b => BitVec.sshiftRight a (BitVec.toNat b)) x) y = ashrS x y :=
  ashr_eq hw x y

/-- `Sparkle.Core.Signal.ashr` (the DSL's `sshiftRight` by a `BitVec`
amount) lifted over two Signals. -/
theorem ap_ashrBV {w : Nat} (hw : 0 < w) (x y : Signal dom (BitVec w)) :
    Signal.ap (Signal.map (fun a b => Sparkle.Core.Signal.ashr a b) x) y = ashrS x y :=
  ashr_eq hw x y

theorem map_sshiftRight (k : Nat) {w : Nat} (hw : 0 < w) (hk : k < 2 ^ w)
    (x : Signal dom (BitVec w)) :
    Signal.map (fun v => BitVec.sshiftRight v k) x = ashrS x (Signal.pure (BitVec.ofNat w k)) := by
  cases x with
  | mk xv =>
  show (⟨fun t => (xv t).sshiftRight k⟩ : Signal dom (BitVec w)) = ⟨fun t => _⟩
  congr 1
  funext t
  have hk' : (BitVec.ofNat w k).toNat = k := by simp [Nat.mod_eq_of_lt hk]
  conv => lhs; rw [← hk', sshiftRight_derived hw]
  rfl

/-! ## Zero extension written as a slice

`extractLsb' 0 (k + w) x` of a `w`-bit `x` reads `k` bits past its top: the
zero extension `0#k ++ x`. -/

theorem extractLsb'_zext {w : Nat} (k : Nat) (x : BitVec w) :
    BitVec.extractLsb' 0 (k + w) x = BitVec.ofNat k 0 ++ x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_extractLsb', BitVec.getElem_append]
  by_cases h : i < w
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge x i (by omega)]

theorem map_extractLsb'_zext (k : Nat) {w : Nat} (x : Signal dom (BitVec w)) :
    Signal.map (fun v => BitVec.extractLsb' 0 (k + w) v) x =
      (Signal.pure (BitVec.ofNat k 0) : Signal dom (BitVec k)) ++ x := by
  cases x with
  | mk xv =>
  show (⟨fun t => BitVec.extractLsb' 0 (k + w) (xv t)⟩ : Signal dom (BitVec (k + w))) =
    ⟨fun t => _⟩
  congr 1
  funext t
  rw [extractLsb'_zext]
  rfl

end Tools.ShippingSignOps
