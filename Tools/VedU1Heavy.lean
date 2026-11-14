import Lean
import Tools.VedU1Lemmas
import Tools.VedU1ScriptSeqGen

/-!
# Closing tactics for signed arithmetic over wide inputs (`Tools.VedU1Heavy`)

The wide path of `Tools/VedU1Entry.lean` (data inputs wider than 16 bits in total) rewrites with
`BitVec.toInt_eq_toNat_cond` and `toSigned`, which opens every signed value into a case split on its
sign bit (`x < 128`, `2 * x < 256`), and does so once per case of the narrow selector inputs.  Two
shapes then run out of budget:

* a tree of signed selects (`max`-like muxes over `slt`): the closing `repeat' split` is exponential
  in the number of distinct conditions, which the unfolding multiplies (`maxPool2x2`: 7
  comparisons over 4 inputs);
* a signed product followed by an arithmetic shift by a narrow selector and a clamp
  (`requantize`): the whole normalisation is repeated for every value of the selector.

The heavy script (`scriptFor … (heavy := true)`) keeps a signed value whole:

1. `ved_heavy_norm` brings both sides to ONE form: `BitVec.toInt x` is `toSigned w x.toNat`,
   `toSigned` / `toNat` are pushed into `ite`s, `(toSigned a * toSigned b).bmod 2^w` is
   `toSigned (a * b % 2^w)` (`mul_bmod_toSigned`), `a < b` is `¬ b ≤ a` and `ite (¬ c)` swaps the
   branches; the side conditions (`0 < w`, `a < 2 ^ w`) are discharged by `omega` from the input
   range facts;
2. `ved_gen_atoms` names each `toSigned` argument that is a wrap-around of a product
   (`x0 * e % 2 ^ 32`) by a variable with its range;
3. after the selectors are case-split, `ved_heavy_close` splits once per distinct condition
   (`split` rewrites every `ite` on the same condition) and closes the leaves by `omega` /
   `simp_all`, unfolding `toSigned` only at a leaf.

The script is UNTRUSTED: the kernel checks the proof term it produces.
-/

namespace Tools.VedU1Heavy

open Sparkle.IR.Semantics

theorem toSigned_emod (w n m : Nat) (hm : 2 ^ w = m) :
    toSigned w n % (m : Int) = (n : Int) % (m : Int) := by
  unfold toSigned
  subst hm
  split
  · rfl
  · rw [Int.sub_emod]; simp

theorem bmod_eq_of_emod (x y : Int) (m : Nat) (h : x % (m : Int) = y % (m : Int)) :
    x.bmod m = y.bmod m := by
  rw [Int.bmod_def, Int.bmod_def, h]

theorem bmod_toSigned (w n m : Nat) (hw : 0 < w) (hm : 2 ^ w = m) :
    (n : Int).bmod m = toSigned w (n % m) := by
  have hh : 2 ^ (w - 1) * 2 = 2 ^ w := by
    obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
    simp [Nat.pow_succ]
  have hr : n % m < m := Nat.mod_lt _ (by rw [← hm]; exact Nat.two_pow_pos w)
  have e1 : ((n % m : Nat) : Int) = (n : Int) % (m : Int) := by push_cast; rfl
  rw [Int.bmod_def, ← e1]
  unfold toSigned
  subst hm
  split <;> split <;> omega

/-- the wrap-around product of two signed values (the left side is what `BitVec.toInt_mul` leaves) -/
theorem mul_bmod_toSigned (w a b m : Nat) (hw : 0 < w) (hm : 2 ^ w = m) :
    (toSigned w a * toSigned w b).bmod m = toSigned w (a * b % m) := by
  have h1 : (toSigned w a * toSigned w b) % (m : Int) = ((a * b : Nat) : Int) % (m : Int) := by
    rw [Int.mul_emod, toSigned_emod w a m hm, toSigned_emod w b m hm, ← Int.mul_emod]; push_cast; rfl
  rw [bmod_eq_of_emod _ _ m h1]
  exact bmod_toSigned w (a * b) m hw hm

theorem toInt_eq_toSigned {w : Nat} (hw : 0 < w) (x : BitVec w) : x.toInt = toSigned w x.toNat :=
  (Tools.VedU1Lemmas.toSigned_toInt w hw x).symm

theorem toSigned_ite (w : Nat) (c : Prop) [Decidable c] (a b : Nat) :
    toSigned w (if c then a else b) = if c then toSigned w a else toSigned w b := by
  split <;> rfl

/-- step 1 of the heavy script (see the module docstring) -/
syntax (name := vedHeavyNorm) "ved_heavy_norm" : tactic

macro_rules
  | `(tactic| ved_heavy_norm) =>
    `(tactic| (simp (disch := omega) only [apply_ite BitVec.toNat,
          Tools.VedU1Heavy.toInt_eq_toSigned, Tools.VedU1Heavy.mul_bmod_toSigned,
          BitVec.toNat_ofNat, Tools.VedU1Lemmas.toNat_sshiftRight', BitVec.toNat_mul, BitVec.extractLsb'_toNat,
          Tools.VedU1ScriptSeq.vedToNatAppend, Tools.VedU1Lemmas.bit1_eq, Tools.VedU1Lemmas.or_hi_16,
          Tools.VedU1Lemmas.or_hi_8, Tools.VedU1Lemmas.or_hi_24, Tools.VedU1Lemmas.or_hi_32,
          Nat.mod_eq_of_lt, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Nat.zero_mul, Nat.shiftRight_eq_div_pow, Nat.zero_add, Nat.div_one,
          Int.shiftRight_eq_div_pow, Int.not_le.symm, ite_not]))

open Lean Meta Elab Tactic in
/-- step 2: every maximal argument `X` of a `toSigned w X` that is a wrap-around `_ % m` and mentions a
variable is replaced by a fresh variable with `X < m` (an argument without a nested `toSigned` only) -/
elab "ved_gen_atoms" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let st ← IO.mkRef (#[] : Array Expr)
  let rec go (e : Expr) : MetaM Unit := do
    if e.isAppOfArity ``Sparkle.IR.Semantics.toSigned 2 then
      let x := e.getArg! 1
      if x.hasFVar && !x.hasLooseBVars && x.isAppOfArity ``HMod.hMod 6 && (x.find? (·.isConstOf ``Sparkle.IR.Semantics.toSigned)).isNone then
        if !(← st.get).contains x then st.modify (·.push x)
    match e with
    | .app f a => go f; go a
    | .lam _ t b _ => go t; go b
    | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()
  go tgt
  let xs ← st.get
  for i in [0:xs.size] do
    let x := xs[i]!
    let stx ← Term.exprToSyntax x
    let p := mkIdent (Name.mkSimple s!"ved_p{i}")
    let hp := mkIdent (Name.mkSimple s!"ved_hp{i}")
    evalTactic (← `(tactic| generalize $hp:ident : $stx = $p:ident))
    evalTactic (← `(tactic| have : $p:ident < $(← Term.exprToSyntax ((x.getArg! 5))) := by omega))

/-- step 3: the closing tactic, after the selectors are case-split -/
syntax (name := vedHeavyClose) "ved_heavy_close" : tactic

macro_rules
  | `(tactic| ved_heavy_close) =>
    `(tactic| ((repeat' split)
        <;> (first | omega | (simp_all; done) | (simp only [Sparkle.IR.Semantics.toSigned, Int.shiftRight_eq_div_pow] at *
                                                    <;> (repeat' split) <;> omega))))

end Tools.VedU1Heavy
