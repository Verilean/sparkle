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


theorem shr_bounds (A : Int) (y : Nat) :
    (0 ≤ A → 0 ≤ A >>> y ∧ A >>> y ≤ A) ∧ (A < 0 → A ≤ A >>> y ∧ A >>> y < 0) := by
  rw [Int.shiftRight_eq_div_pow]
  have ht : (0 : Int) < ((2 ^ y : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos y
  have ht1 : (1 : Int) ≤ ((2 ^ y : Nat) : Int) := by omega
  generalize ((2 ^ y : Nat) : Int) = t at *
  refine ⟨fun h => ⟨Int.ediv_nonneg h (by omega), Int.ediv_le_self _ h⟩, fun h => ⟨?_, ?_⟩⟩
  · apply Int.le_ediv_of_mul_le ht
    have := Int.mul_le_mul_of_nonpos_left (by omega : A ≤ 0) ht1
    omega
  · exact Int.ediv_neg_of_neg_of_pos h ht

theorem toSigned_range (w X : Nat) (hw : 0 < w) (hX : X < 2 ^ w) :
    -((2 ^ (w - 1) : Nat) : Int) ≤ toSigned w X ∧ toSigned w X < ((2 ^ (w - 1) : Nat) : Int) := by
  have hh : 2 ^ (w - 1) * 2 = 2 ^ w := by
    obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
    simp [Nat.pow_succ]
  unfold toSigned
  split <;> omega


open Lean Meta Simp in
/-- `c ||| x` for a numeral `c` whose low `k` bits are zero and `x < 2 ^ k` (`k` the number of trailing zero
bits of `c`, `x < 2 ^ k` by the configured discharger): the sum `c + x` (`Tools.VedU1Lemmas.or_hi`).  The
extension of a short operand by a constant (`0x3F ++ scale` read as `1008 ||| scale`) at any width. -/
simproc_decl vedOrAdd (_ ||| _) := fun e => do
  unless e.isAppOfArity ``HOr.hOr 6 do return .continue
  let some c := (e.getArg! 4).nat? | return .continue
  if c == 0 then return .continue
  let x := e.getArg! 5
  if (x.nat?).isSome then return .continue
  let mut k := 0
  let mut r := c
  while r % 2 == 0 do
    r := r / 2
    k := k + 1
  let lt ← mkAppM ``LT.lt #[x, ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit k]]
  let some h1 ← (← getMethods).discharge? lt | return .continue
  let h2 ← mkAppM ``Eq.refl #[mkNatLit 0]
  let pf ← mkAppM ``Tools.VedU1Lemmas.or_hi #[mkNatLit c, x, mkNatLit k, h1, h2]
  let rhs := (← inferType pf).appArg!
  return .visit { expr := rhs, proof? := some pf }

/-- step 1 of the heavy script (see the module docstring) -/
syntax (name := vedHeavyNorm) "ved_heavy_norm" : tactic

macro_rules
  | `(tactic| ved_heavy_norm) =>
    `(tactic| (simp (disch := omega) only [apply_ite BitVec.toNat,
          Tools.VedU1Heavy.toInt_eq_toSigned, Tools.VedU1Heavy.mul_bmod_toSigned,
          BitVec.toNat_ofNat, Tools.VedU1Lemmas.toNat_sshiftRight', BitVec.toNat_mul, BitVec.extractLsb'_toNat,
          Tools.VedU1ScriptSeq.vedToNatAppend, Tools.VedU1Lemmas.bit1_eq, Tools.VedU1Heavy.vedOrAdd,
          Nat.mod_eq_of_lt, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Nat.zero_mul, Nat.shiftRight_eq_div_pow, Nat.zero_add, Nat.div_one,
          Int.not_le.symm, ite_not]))

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


open Lean Meta Elab Tactic in
/-- step 2b: a shift `toSigned w X >>> y` by a variable amount is named by a variable `Q` whose range is
that of a `w`-bit signed value (`shr_bounds`, `toSigned_range`): the goal no longer depends on `y`, so the
selector need not be case-split -/
elab "ved_gen_shifts" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let st ← IO.mkRef (#[] : Array Expr)
  let rec go (e : Expr) : MetaM Unit := do
    if e.isAppOfArity ``HShiftRight.hShiftRight 6 && (e.getArg! 0).isConstOf ``Int then
      let a := e.getArg! 4
      if a.isAppOfArity ``Sparkle.IR.Semantics.toSigned 2 && !e.hasLooseBVars then
        if !(← st.get).contains e then st.modify (·.push e)
    match e with
    | .app f a => go f; go a
    | .lam _ t b _ => go t; go b
    | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()
  go tgt
  let ts ← st.get
  if ts.isEmpty then throwError "ved_gen_shifts: no signed shift"
  for i in [0:ts.size] do
    let t := ts[i]!
    let a := t.getArg! 4
    let y := t.getArg! 5
    let some w := (a.getArg! 0).nat? | throwError "ved_gen_shifts: width is not a literal"
    let x := a.getArg! 1
    let tS ← Term.exprToSyntax t
    let aS ← Term.exprToSyntax a
    let yS ← Term.exprToSyntax y
    let xS ← Term.exprToSyntax x
    let wS := Syntax.mkNumLit (toString w)
    let hb := mkIdent (Name.mkSimple s!"ved_hb{i}")
    let ha := mkIdent (Name.mkSimple s!"ved_ha{i}")
    let q := mkIdent (Name.mkSimple s!"ved_q{i}")
    let hq := mkIdent (Name.mkSimple s!"ved_hq{i}")
    let lit := Syntax.mkNumLit (toString (2 ^ (w - 1)))
    evalTactic (← `(tactic| have $hb:ident := Tools.VedU1Heavy.shr_bounds $aS $yS))
    evalTactic (← `(tactic| have $ha:ident := Tools.VedU1Heavy.toSigned_range $wS $xS (by omega) (by omega)))
    evalTactic (← `(tactic| simp only [Nat.reduceSub, Nat.reducePow] at $ha:ident))
    evalTactic (← `(tactic| generalize $tS = $q:ident at $hb:ident ⊢))
    evalTactic (← `(tactic| have $hq:ident : -($lit : Int) ≤ $q:ident ∧ $q:ident < $lit := by omega))
    evalTactic (← `(tactic| clear $hb:ident $ha:ident))

/-- step 3: the closing tactic, after the selectors are case-split -/
syntax (name := vedHeavyClose) "ved_heavy_close" : tactic

macro_rules
  | `(tactic| ved_heavy_close) =>
    `(tactic| ((repeat' split)
        <;> (first | omega | (simp_all; done) | (simp only [Sparkle.IR.Semantics.toSigned, Int.shiftRight_eq_div_pow] at *
                                                    <;> (repeat' split) <;> omega))))

end Tools.VedU1Heavy
