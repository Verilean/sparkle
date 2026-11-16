import Lean

/-!
# Reading a field out of a packed loop word without `omega` (`sparkle-ved-packed-seq4`)

A `Signal.loop` over several registers is packed by the synthesizer into ONE wire and every register is sliced back
out of it (`_tmp_s_{k+1} = slice(_tmp_s_k, hi, 0)`, `_gen_x = slice(_tmp_s_k, hi, lo)`).  Substituted into the
equation of a later statement, the word is a nest of `a % 2^w * 2^o + (rest) % 2^o`, wrapped by one more `% 2^(hi+1)`
for every slice of the chain.  `Tools.VedU1ScriptSeqGen.ved_seq_unpack` proves each read-back `t = x.toNat` by `omega`
over the whole word (162 .. 992 M heartbeats per field for 26 registers, R23).

`ved_pk4_unpack at h` rewrites the right-hand side of `h : lhs = rhs` bottom-up with three equations only, each proved
by a closed lemma (no search): with `r < m`

* `x % M = x`                       when an upper bound of `x` below `M` is read off the term (`ltBound`);
* `(a * m + r) % m = r`;
* `(a * m + r) / m = a`.

`ltBound` knows `c % M < M`, `x.toNat < 2^w` (`BitVec.isLt`), `b.toNat < 2` (`Bool`), numerals, and
`a * m + r < Na * m` from `a < Na`, `r < m`.  A term of another shape is left as it is (the equation is not
changed).  UNTRUSTED like every tactic of the script: the kernel checks the proof term.
-/

namespace Tools.VedU1PackedSeq4

theorem pk4_div (a r m : Nat) (hr : r < m) : (a * m + r) / m = a := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) hr
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hr, Nat.zero_add]

theorem pk4_mod (a r m : Nat) (hr : r < m) : (a * m + r) % m = r := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem pk4_lt (a r na m : Nat) (ha : a < na) (hr : r < m) : a * m + r < na * m := by
  calc a * m + r < a * m + m := Nat.add_lt_add_left hr _
    _ = (a + 1) * m := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ na * m := Nat.mul_le_mul_right _ ha

theorem pk4_bool_lt (b : Bool) : b.toNat < 2 := Nat.lt_succ_of_le (Bool.toNat_le b)

theorem pk4_lt_of_lt_le {x b m : Nat} (h : x < b) (hb : b ≤ m) : x < m := Nat.lt_of_lt_of_le h hb

section Meta
open Lean Meta

/-- `e` ascribed to the proposition `ty` (the kernel checks that its own type is defeq to `ty`, e.g. `2 * 256` against `512`) -/
def hint (e ty : Expr) : Expr := mkApp2 (mkConst ``id [Level.zero]) ty e

/-- value of a closed natural-number term: numerals, `+`, `*`, `^`, `-`, `/`, `%` -/
partial def closedNat? (e : Expr) : Option Nat :=
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do return (← closedNat? a) + (← closedNat? b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do return (← closedNat? a) * (← closedNat? b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => do return (← closedNat? a) - (← closedNat? b)
  | (``HPow.hPow, #[_, _, _, _, a, b]) => do
    let y ← closedNat? b
    if y > 4096 then none else return (← closedNat? a) ^ y
  | _ => e.nat?

/-- `Nat.ble n m = true` (the kernel checks it by literal arithmetic) -/
private def leProof (n m : Nat) : MetaM Expr := do
  let ty ← mkAppM ``LE.le #[mkNatLit n, mkNatLit m]
  let b ← mkEqRefl (mkConst ``true)
  return hint (mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (mkNatLit n) (mkNatLit m) b) ty

/-- `(B, h : x < B)` for the shapes `ltBound` knows -/
partial def ltBound (x : Expr) : MetaM (Option (Nat × Expr)) := do
  if let some n := x.nat? then
    let ty ← mkAppM ``LT.lt #[x, mkNatLit (n + 1)]
    return some (n + 1, hint (mkApp (mkConst ``Nat.lt_succ_self) x) ty)
  match x.getAppFnArgs with
  | (``HMod.hMod, #[_, _, _, _, c, m]) =>
    let some M := closedNat? m | return none
    if M == 0 then return none
    let pos ← mkAppM ``LT.lt #[mkNatLit 0, m]
    let hpos := hint (← leProof 1 M) pos
    return some (M, mkApp3 (mkConst ``Nat.mod_lt) c m hpos)
  | (``BitVec.toNat, #[w, b]) =>
    let some W := closedNat? (← instantiateMVars w) | return none
    if W > 4096 then return none
    return some (2 ^ W, mkApp2 (mkConst ``BitVec.isLt) w b)
  | (``Bool.toNat, #[b]) => return some (2, mkApp (mkConst ``pk4_bool_lt) b)
  | (``HAdd.hAdd, #[_, _, _, _, p, r]) =>
    match p.getAppFnArgs with
    | (``HMul.hMul, #[_, _, _, _, a, m0]) =>
      let some M0 := closedNat? m0 | return none
      let some (Na, pa) ← ltBound a | return none
      let some prM ← ltProofTo r M0 | return none
      let ty ← mkAppM ``LT.lt #[x, mkNatLit (Na * M0)]
      return some (Na * M0, hint (mkApp6 (mkConst ``pk4_lt) a r (mkNatLit Na) m0 pa prM) ty)
    | _ => return none
  | _ => return none
where
  /-- `h : x < M` for a given bound `M` (the bound is weakened when it is smaller) -/
  ltProofTo (x : Expr) (M : Nat) : MetaM (Option Expr) := do
    let some (B, p) ← ltBound x | return none
    if B > M then return none
    if B == M then return some p
    return some (mkApp5 (mkConst ``pk4_lt_of_lt_le) x (mkNatLit B) (mkNatLit M) p (← leProof B M))

/-- `h : x < M` for a given bound `M` -/
def ltProofTo (x : Expr) (M : Nat) : MetaM (Option Expr) := do
  let some (B, p) ← ltBound x | return none
  if B > M then return none
  if B == M then return some p
  return some (mkApp5 (mkConst ``pk4_lt_of_lt_le) x (mkNatLit B) (mkNatLit M) p (← leProof B M))

/-- the normal form of `e` and a proof `e = e'` (`none`: `e' == e`) -/
partial def pkNorm (e : Expr) : MetaM (Expr × Option Expr) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => rebuildBin e a b
  | (``HMul.hMul, #[_, _, _, _, a, b]) => rebuildBin e a b
  | (``HMod.hMod, #[_, _, _, _, x, m]) =>
    let some M := closedNat? m | return (e, none)
    if M == 0 then return (e, none)
    let (x', px) ← pkNorm x
    let (e1, p1) ← rebuildL e x' px m
    -- rule 1: `x' < M` gives `x' % M = x'`
    if let some h ← ltProofTo x' M then
      return (x', ← chain p1 (some (mkApp3 (mkConst ``Nat.mod_eq_of_lt) x' m h)))
    -- rule 2: `(a * m0 + r) % m0 = r`
    if let some (a, m0, r) := asPack x' then
      if closedNat? m0 == some M then
        if let some h ← ltProofTo r M then
          let ty ← mkEq e1 r
          return (r, ← chain p1 (some (hint (mkApp4 (mkConst ``pk4_mod) a r m0 h) ty)))
    return (e1, p1)
  | (``HDiv.hDiv, #[_, _, _, _, x, d]) =>
    let some D := closedNat? d | return (e, none)
    if D == 0 then return (e, none)
    let (x', px) ← pkNorm x
    let (e1, p1) ← rebuildL e x' px d
    -- rule 3: `(a * m0 + r) / m0 = a`
    if let some (a, m0, r) := asPack x' then
      if closedNat? m0 == some D then
        if let some h ← ltProofTo r D then
          let ty ← mkEq e1 a
          return (a, ← chain p1 (some (hint (mkApp4 (mkConst ``pk4_div) a r m0 h) ty)))
    return (e1, p1)
  | _ => return (e, none)
where
  asPack (x : Expr) : Option (Expr × Expr × Expr) :=
    match x.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, p, r]) =>
      match p.getAppFnArgs with
      | (``HMul.hMul, #[_, _, _, _, a, m0]) => some (a, m0, r)
      | _ => none
    | _ => none
  /-- `e = op x c` with `x` replaced by `x'` -/
  rebuildL (e x' : Expr) (px : Option Expr) (c : Expr) : MetaM (Expr × Option Expr) := do
    let f := e.getAppFn
    let pre := #[e.getArg! 0, e.getArg! 1, e.getArg! 2, e.getArg! 3]
    let e1 := mkAppN f (pre ++ #[x', c])
    match px with
    | none => return (e1, none)
    | some p =>
      let motive := mkLambda `z .default (e.getArg! 0) (mkAppN f (pre ++ #[.bvar 0, c]))
      return (e1, some (← mkCongrArg motive p))
  rebuildBin (e a b : Expr) : MetaM (Expr × Option Expr) := do
    let (a', pa) ← pkNorm a
    let (b', pb) ← pkNorm b
    if pa.isNone && pb.isNone then return (e, none)
    let f := e.getAppFn
    let pre := #[e.getArg! 0, e.getArg! 1, e.getArg! 2, e.getArg! 3]
    let e' := mkAppN f (pre ++ #[a', b'])
    let fa := mkAppN f pre
    let pf ← match pa, pb with
      | some p1, some p2 => mkCongr (← mkCongrArg fa p1) p2
      | some p1, none => mkCongrFun (← mkCongrArg fa p1) b
      | none, some p2 => mkCongrArg (mkApp fa a) p2
      | none, none => unreachable!
    return (e', some pf)
  chain (p1 p2 : Option Expr) : MetaM (Option Expr) := do
    match p1, p2 with
    | none, p => return p
    | p, none => return p
    | some a, some b => return some (← mkEqTrans a b)

end Meta

section Tactic
open Lean Meta Elab Tactic

/-- `ved_pk4_unpack at h`: rewrite the right-hand side of `h : lhs = rhs` by `pkNorm`; no change when the
normal form is the same term. -/
elab "ved_pk4_unpack " "at " h:ident : tactic => withMainContext do
  let some d := (← getLCtx).findFromUserName? h.getId | return
  let ty ← instantiateMVars d.type
  let some (_, lhs, rhs) := ty.eq? | return
  let (rhs', pf?) ← pkNorm rhs
  let some pf := pf? | return
  let newTy ← mkEq lhs rhs'
  let newH ← mkEqTrans d.toExpr pf
  let g ← getMainGoal
  let g1 ← g.assert d.userName newTy (hint newH newTy)
  let (nv, g2) ← g1.intro1P
  let g3 ← g2.clear d.fvarId
  replaceMainGoal [g3]
  let _ := nv

end Tactic

end Tools.VedU1PackedSeq4

namespace Tools.VedU1PackedSeq4
open Lean Meta Elab Tactic

/-- `ved_pk4_split h as "pfx" at i, j, ..`: for a hypothesis `h : A₀ ∧ A₁ ∧ …` (right nested; the elements of a recursive
conjunction such as `AllP P B` are found by `whnf`) introduce `pfx_i : A_i` for the listed indices (increasing), each as a
projection built DIRECTLY (`And.left` of the `And.right` chain: linear; the elaborator on the same projections as
`.2.2.1` is quadratic, 30 s for 75 conjuncts and 120 s for 323). -/
syntax (name := vedPk4Split) "ved_pk4_split " ident " as " str " at " num,* : tactic

@[tactic vedPk4Split] def evalVedPk4Split : Tactic := fun stx => withMainContext do
  let h : Ident := ⟨stx[1]⟩
  let pfx := (stx[3]).isStrLit?.getD "h"
  let idxs : Array Nat := (stx[5].getSepArgs).map fun n => n.isNatLit?.getD 0
  let some d := (← getLCtx).findFromUserName? h.getId | throwError "ved_pk4_split: no hypothesis {h.getId}"
  let some last := idxs.back? | return
  let mut cur : Lean.Expr := d.toExpr
  let mut curTy ← instantiateMVars d.type
  let mut hyps : Array Hypothesis := #[]
  let mut j := 0
  for i in [0:last + 1] do
    unless curTy.isAppOfArity ``And 2 do
      let t' ← whnfD curTy
      if t'.isAppOfArity ``And 2 then curTy := t'
    let some (a, b) := (match curTy.getAppFnArgs with | (``And, #[a, b]) => some (a, b) | _ => none)
      | -- the last conjunct of the chain
        if j < idxs.size && idxs[j]! == i then
          hyps := hyps.push { userName := Name.mkSimple s!"{pfx}{i}", type := curTy, value := cur }
          break
        throwError "ved_pk4_split: the type of the conjunction ends at {i}"
    if j < idxs.size && idxs[j]! == i then
      hyps := hyps.push { userName := Name.mkSimple s!"{pfx}{i}", type := a, value := mkApp3 (mkConst ``And.left) a b cur }
      j := j + 1
    cur := mkApp3 (mkConst ``And.right) a b cur
    curTy := b
  let g ← getMainGoal
  let (_, g') ← g.assertHypotheses hyps
  replaceMainGoal [g']

end Tools.VedU1PackedSeq4
