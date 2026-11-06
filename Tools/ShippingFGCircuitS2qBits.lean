import Tools.ShippingFGCircuitS2iDT
set_option autoImplicit false
-- FG circuit pilot S2q: the per-time equations that are the BASIS of the three narrow bit rules of `DT` (`mapExtract`, `sigShlBV`, `sigAppendCL`), docs/FG-CIRCUIT-PILOT.md §43.
-- No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.

/-! # The bit operations of `Signal`

Each rule's VALUE is Lean's own term (`Signal.map (fun x => BitVec.extractLsb' lo len x) s`, the `HShiftLeft`/`HAppend` instance of `Sparkle.Core.Signal`, whose implementation is
`pure`/`map`/`ap`). The theorems below prove, in the kernel and for EVERY time `t`, the equation that those definitions satisfy, with `BitVec`'s original meaning:
* extract: `(…).val t = BitVec.extractLsb' lo len (s.val t)` (parameters: width `W`, `lo`, `len` and the domain are arbitrary: a family of one fixed-width operation);
* shift: `(s <<< k).val t = s.val t <<< k` (`BitVec`'s `<<<` truncates to the width `W`; an amount `≥ W` gives `0`: `shl_at_big`);
* append: `(c ++ s).val t = c ++ s.val t` (the constant on the LEFT, the output width `m + n`, order preserved: the high bits are `c`). -/
namespace Tools.ShippingFGCircuitS2qBits
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

theorem extract_at {D : DomainConfig} {W : Nat} (lo len : Nat) (sv : Signal D (BitVec W)) (t : Nat) :
    (Signal.map (fun x : BitVec W => BitVec.extractLsb' lo len x) sv).val t = BitVec.extractLsb' lo len (sv.val t) := rfl

theorem shl_at {D : DomainConfig} {W : Nat} (av : Signal D (BitVec W)) (k : BitVec W) (t : Nat) :
    (@HShiftLeft.hShiftLeft _ _ _ (@Sparkle.Core.Signal.instHShiftLeftSignalBitVec D W) av k).val t = av.val t <<< k := rfl

theorem shl_at_toNat {D : DomainConfig} {W : Nat} (av : Signal D (BitVec W)) (k : BitVec W) (t : Nat) :
    ((@HShiftLeft.hShiftLeft _ _ _ (@Sparkle.Core.Signal.instHShiftLeftSignalBitVec D W) av k).val t).toNat
      = ((av.val t).toNat <<< k.toNat) % 2 ^ W := by
  rw [shl_at]; exact BitVec.toNat_shiftLeft ..

theorem shl_at_big {D : DomainConfig} {W : Nat} (av : Signal D (BitVec W)) (k : BitVec W) (t : Nat) (hk : W ≤ k.toNat) :
    (@HShiftLeft.hShiftLeft _ _ _ (@Sparkle.Core.Signal.instHShiftLeftSignalBitVec D W) av k).val t = 0#W := by
  apply BitVec.eq_of_toNat_eq
  rw [shl_at_toNat, Nat.shiftLeft_eq]
  have : 2 ^ W ∣ (av.val t).toNat * 2 ^ k.toNat := Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 hk) _
  simpa using Nat.mod_eq_zero_of_dvd this

theorem append_at {D : DomainConfig} {M N : Nat} (c : BitVec M) (bv : Signal D (BitVec N)) (t : Nat) :
    (@HAppend.hAppend _ _ _ (@Sparkle.Core.Signal.instHAppendBitVecSignalHAddNat M D N) c bv).val t = c ++ bv.val t := rfl

theorem append_at_toNat {D : DomainConfig} {M N : Nat} (c : BitVec M) (bv : Signal D (BitVec N)) (t : Nat) :
    ((@HAppend.hAppend _ _ _ (@Sparkle.Core.Signal.instHAppendBitVecSignalHAddNat M D N) c bv).val t).toNat
      = c.toNat * 2 ^ N + (bv.val t).toNat := by
  rw [append_at, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (bv.val t).isLt, Nat.shiftLeft_eq]

/-- NEW (S2t): bitwise OR of two `Signal D (BitVec W)`: at every time `t` the output is `av.val t ||| bv.val t` (the instance is `(· ||| ·) <$> a <*> b`). Separate from the `Bool` OR and the mixed-constant instances. -/
theorem or_at {D : DomainConfig} {W : Nat} (av bv : Signal D (BitVec W)) (t : Nat) :
    (@HOr.hOr _ _ _ (@Sparkle.Core.Signal.instHOrSignalBitVec D W) av bv).val t = (av.val t ||| bv.val t) := rfl

end Tools.ShippingFGCircuitS2qBits

#print axioms Tools.ShippingFGCircuitS2qBits.extract_at
#print axioms Tools.ShippingFGCircuitS2qBits.shl_at
#print axioms Tools.ShippingFGCircuitS2qBits.shl_at_toNat
#print axioms Tools.ShippingFGCircuitS2qBits.shl_at_big
#print axioms Tools.ShippingFGCircuitS2qBits.append_at
#print axioms Tools.ShippingFGCircuitS2qBits.append_at_toNat
#print axioms Tools.ShippingFGCircuitS2qBits.or_at
