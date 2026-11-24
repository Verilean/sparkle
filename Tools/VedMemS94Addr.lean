import Lean
import Tools.VedMemLoop

/-!
# Spellings of one value inside a memory read (`ved.mem.s94AddrNorm`, `ved.mem.s94ReadLift`; s94x)

Observed (s94w, R033 goals 33 34 and the same family 53 54 63): the two sides of a tail goal read ONE memory word, the address spelled two ways, and shift by one power, the exponent
spelled two ways:

* `ved_M0 (BitVec.ofNat 9 ((c.toNat * 68 + a.toNat * 4 + b.toNat) % 512))` against `ved_M0 (68#9 * (0#7 ++ c) + 4#9 * (0#4 ++ a) + (0#6 ++ b))` (`c : BitVec 2`, `a : BitVec 5`, `b : BitVec 3`),
* `2 ^ ((64 + (128 - x.toNat) + (128 - X / 65536 % 64 % 128)) % 128)` against `2 ^ ((128 - X / 65536 % 64 + (128 - x.toNat + 64)) % 128)`.

`omega` / `split` take each spelling for its own atom (`(ved_M0 a).toNat`, `2 ^ e`, and so the `|||` of them): cause (a), the local theorem "the two spellings are one number" is not supplied.
The theorem is supplied here once per pair (`ved_bv_addr_eq`: `BitVec.eq_of_toNat_eq`, the `toNat` lemmas of `+ * ++` on zero-extended fields, `omega`; the exponents by `omega`) and the second
spelling is replaced by the first in the target and the context (`rewriteAll`: DAG replace over the abstraction of the term + `congrArg`, no `simp`, no `rw`: those walk the tree).

`ved_read_lift`: a read of a variable memory function at an `if` address, `f (if c then a else b)`, is `if c then f a else f b` (`read_ite`), so that the `if`s of the addresses are the `if`s of the
values and the reads at the branches are plain atoms.
-/

namespace Tools.VedMemS94Addr

open Lean Meta Elab Tactic Tools.VedU1WireShare

register_option ved.mem.s94AddrNorm : Bool := {
  defValue := false
  descr := "ved_local_close_state / ved_local_close_mulshift: before the closers, two spellings of one memory address (`ofNat w (sum % 2^w)` against the BitVec sum of zero-extended fields) and two spellings of one exponent `2 ^ e` are made one (ved_spell_unify); default false"
}

register_option ved.mem.s94ReadLift : Bool := {
  defValue := false
  descr := "ved_local_close_state / ved_local_close_mulshift: a read of a variable memory function at an `if` address, f (if c then a else b), is lifted to if c then f a else f b in the target and the hypotheses (ved_read_lift); default false"
}

register_option ved.mem.s94OrDisj : Bool := {
  defValue := false
  descr := "ved_local_close_state / ved_local_close_mulshift: bounds `x ||| y < 2 ^ k` (`^^^` too) of the bit-field terms of the goal, the bound of each side proved by omega (ved_or_bounds); default false"
}

initialize orHits : IO.Ref Nat ← IO.mkRef 0
initialize orRefuse : IO.Ref Bool ← IO.mkRef false
initialize orFailLate : IO.Ref Bool ← IO.mkRef false
initialize unifyHits : IO.Ref Nat ← IO.mkRef 0
initialize unifyRefuse : IO.Ref Bool ← IO.mkRef false
initialize unifyFailLate : IO.Ref Bool ← IO.mkRef false
initialize liftHits : IO.Ref Nat ← IO.mkRef 0
initialize liftRefuse : IO.Ref Bool ← IO.mkRef false
initialize liftFailLate : IO.Ref Bool ← IO.mkRef false

/-- a zero-extension by `0#p ++` is the word of the same number (the root of the left side is the append, whose widths `p`, `n` are fixed by its first two arguments: the form `toNat (0#p ++ x)` does not match a
term whose width was normalised to a literal, `?p + ?n =?= 9`) -/
theorem zext_append_eq {p n : Nat} (x : BitVec n) : (0#p ++ x : BitVec (p + n)) = BitVec.ofNat (p + n) x.toNat := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hle : 2 ^ n ≤ 2 ^ (p + n) := Nat.pow_le_pow_right (by decide) (Nat.le_add_left n p)
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hx hle)]
  simp

/-- the lift of a read through an `if` address -/
theorem read_ite {α β : Type} (f : α → β) (c : Prop) [Decidable c] (a b : α) : f (if c then a else b) = if c then f a else f b := by
  split <;> rfl

/-- `toNat` of an `if` -/
theorem toNat_ite {n : Nat} (c : Prop) [Decidable c] (a b : BitVec n) : (if c then a else b).toNat = if c then a.toNat else b.toNat := by
  split <;> rfl

/-- the address equation of two spellings, in full: with `c : BitVec 2`, `a : BitVec 5`, `b : BitVec 3` (the R033 goals 33 34; the general normaliser is `ved_bv_addr_eq`, this is its instance) -/
theorem addr_spell_9 (c : BitVec 2) (a : BitVec 5) (b : BitVec 3) :
    BitVec.ofNat 9 ((c.toNat * 68 + a.toNat * 4 + b.toNat) % 512) = 68#9 * (0#7 ++ c) + 4#9 * (0#4 ++ a) + (0#6 ++ b) := by
  apply BitVec.eq_of_toNat_eq
  have hc := c.isLt
  have ha := a.isLt
  have hb := b.isLt
  simp only [zext_append_eq]
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceAdd]
  omega

/-- `h : a = b`: `a` is replaced by `b` in every proposition of the context and in the target (DAG replace over the abstraction of `a`, `congrArg`; no `simp` / `rw`, which walk the tree);
returns the new goal and the number of propositions changed -/
def rewriteAll (g : MVarId) (a b h : Expr) : MetaM (MVarId × Nat) := do
  let aTy ← g.withContext (inferType a)
  let rw (T : Expr) : MetaM (Option (Expr × Expr)) := do
    if (T.find? (· == a)).isNone then return none
    withLocalDeclD `ved_x aTy fun x => do
      let Tabs := T.replace fun e => if e == a then some x else none
      let motive ← mkLambdaFVars #[x] Tabs
      let T' := Tabs.replaceFVar x b
      let pf ← mkExpectedTypeHint (← mkAppM ``congrArg #[motive, h]) (← mkEq T T')
      return some (T', pf)
  let mut g := g
  let mut n := 0
  for d in ← g.withContext getLCtx do
    if d.isImplementationDetail || d.isLet then continue
    let t ← instantiateMVars d.type
    unless (← g.withContext (isProp t)) do continue
    if let some (t', pf) ← g.withContext (rw t) then
      let r ← g.replaceLocalDecl d.fvarId t' pf
      g := r.mvarId
      n := n + 1
  let tgt ← instantiateMVars (← g.getType)
  if let some (t', pf) ← g.withContext (rw tgt) then
    g ← g.replaceTargetEq t' pf
    n := n + 1
  return (g, n)

/-- `ved_zext_lift`: every `0#p ++ x` (`x : BitVec n`) of the target is `BitVec.ofNat (p + n) x.toNat` (`zext_append_eq`; `rewriteAll`, the term found by shape: the simp lemma does not match once the width of the
append was normalised to a literal, `BitVec (?p + ?n)` against `BitVec 9`); fails when there is none -/
elab "ved_zext_lift" : tactic => do
  let mut g ← getMainGoal
  let mut total := 0
  for _ in [0:4] do
    let tgt ← instantiateMVars (← g.getType)
    let isZ (x : Expr) : Bool :=
      x.isAppOfArity ``HAppend.hAppend 6 && (x.getArg! 4).isAppOfArity ``BitVec.ofNat 2 && (x.getArg! 4).appArg!.nat? == some 0 &&
      (x.getArg! 0).isAppOf ``BitVec && (x.getArg! 1).isAppOf ``BitVec
    let zs := collectDag isZ tgt
    if zs.isEmpty then break
    for z in zs do
      let p := (z.getArg! 0).appArg!
      let n := (z.getArg! 1).appArg!
      let h := mkAppN (mkConst ``zext_append_eq) #[p, n, z.getArg! 5]
      let some (_, _, r) := (← g.withContext (inferType h)).eq? | continue
      let (g', k) ← rewriteAll g z r h
      g := g'; total := total + k
  if total == 0 then throwError "ved_zext_lift: no zero extension"
  replaceMainGoal [g]

/-- `ved_bv_addr_eq`: the equation of two `BitVec` terms by their numbers (the bounds of the variables are in the context) -/
macro "ved_bv_addr_eq" : tactic =>
  `(tactic| ((try ved_zext_lift)
             apply BitVec.eq_of_toNat_eq
             simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.extractLsb'_toNat]
             simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceAdd]
             omega))


/-- the target and the propositions of the context, instantiated -/
def propsOf (g : MVarId) : MetaM (Array Expr) := g.withContext do
  let mut ps : Array Expr := #[← instantiateMVars (← g.getType)]
  for d in ← getLCtx do
    if d.isImplementationDetail || d.isLet then continue
    let t ← instantiateMVars d.type
    if (← isProp t) then ps := ps.push t
  return ps

/-- the reads `f a` of a variable function of one `BitVec` argument (the memories after `ved_cone_opaque`: `ved_M0 a`) -/
def readsOf (g : MVarId) (e : Expr) : MetaM (Array Expr) := g.withContext do
  let cands := collectDag (fun x => x.isApp && x.getAppNumArgs == 1 && x.getAppFn.isFVar && !x.appArg!.hasLooseBVars) e
  cands.filterM fun x => do return (← whnfR (← inferType x.appArg!)).isAppOf ``BitVec

/-- the addresses at the leaves of the `if`s of an address -/
partial def addrLeaves (a : Expr) : Array Expr :=
  if a.isAppOfArity ``ite 5 then addrLeaves (a.getArg! 3) ++ addrLeaves (a.getArg! 4) else #[a]

/-- the names of the variables of a term, sorted (the gate of a pair: two spellings of one value mention the same variables) -/
def fvKey (e : Expr) : Array Name :=
  ((collectDag (·.isFVar) e).map (·.fvarId!.name)).qsort Name.lt

/-- bounds `x.toNat < 2 ^ w` of the `BitVec` variables of `es` as hypotheses of the main goal of the TacticM, then `tac` -/
def withBounds (es : Array Expr) (tac : TacticM Unit) : TacticM Unit := do
  let mut seen : Array FVarId := #[]
  for e in es do
    for x in collectDag (·.isFVar) e do
      let f := x.fvarId!
      if seen.contains f then continue
      seen := seen.push f
      let g ← getMainGoal
      let isBv ← g.withContext do return (← whnfR (← instantiateMVars (← f.getType))).isAppOf ``BitVec
      unless isBv do continue
      let (pr, ty) ← g.withContext do
        let pr ← mkAppM ``BitVec.isLt #[x]
        pure (pr, ← inferType pr)
      let (_, g1) ← (← g.assert `ved_b ty pr).intro1P
      replaceMainGoal [g1]
  tac

/-! ### cheap gate: random evaluation

A pair of terms is worth a proof only if they agree on random values of their atoms (variables, memory reads, `if`s): two numbers that differ on one valuation are not two spellings of one value, the
proof (an `omega` call on a context of 30 hypotheses, up to the pair limit) is never started. The terms are evaluated by the arithmetic they are made of (`+ - * / % ^ ||| &&& ^^^ <<< >>>`,
`BitVec` `+ - * ++ extractLsb' ofNat`, literals); any other subterm is an atom whose value is a hash of the term and the valuation number. Equal terms agree on every valuation. -/

/-- the atom value of `e` under valuation `seed`, below `bound` -/
def atomVal (seed : Nat) (e : Expr) (bound : Nat) : Nat :=
  (hash e).toNat * 2654435761 + seed * 40503 + (hash e).toNat / 7 |>.mod (if bound == 0 then 1 else bound)

mutual
partial def evalNat (seed : Nat) (e : Expr) : MetaM Nat := do
  let bin (f : Nat → Nat → Nat) : MetaM Nat := do
    return f (← evalNat seed (e.getArg! 4)) (← evalNat seed (e.getArg! 5))
  if e.isAppOfArity ``OfNat.ofNat 3 then
    if let some n := e.nat? then return n
  if e.isRawNatLit then return e.rawNatLit?.getD 0
  if e.isAppOfArity ``HAdd.hAdd 6 then return ← bin (· + ·)
  if e.isAppOfArity ``HSub.hSub 6 then return ← bin (· - ·)
  if e.isAppOfArity ``HMul.hMul 6 then return ← bin (· * ·)
  if e.isAppOfArity ``HDiv.hDiv 6 then return ← bin (fun a b => a / b)
  if e.isAppOfArity ``HMod.hMod 6 then return ← bin (fun a b => a % b)
  if e.isAppOfArity ``HOr.hOr 6 then return ← bin (· ||| ·)
  if e.isAppOfArity ``HAnd.hAnd 6 then return ← bin (· &&& ·)
  if e.isAppOfArity ``HXor.hXor 6 then return ← bin (· ^^^ ·)
  if e.isAppOfArity ``HShiftLeft.hShiftLeft 6 then return ← bin (· <<< ·)
  if e.isAppOfArity ``HShiftRight.hShiftRight 6 then return ← bin (· >>> ·)
  if e.isAppOfArity ``HPow.hPow 6 then
    let b ← evalNat seed (e.getArg! 4)
    let x ← evalNat seed (e.getArg! 5)
    if x ≤ 4096 then return b ^ x
  if e.isAppOfArity ``BitVec.toNat 2 then return ← evalBV seed (e.getArg! 1)
  return atomVal seed e (2 ^ 16)

partial def evalBV (seed : Nat) (v : Expr) : MetaM Nat := do
  let ty ← whnfR (← inferType v)
  let w := if ty.isAppOf ``BitVec then ty.appArg!.nat?.getD 64 else 64
  let m := 2 ^ w
  let bin (f : Nat → Nat → Nat) : MetaM Nat := do
    return f (← evalBV seed (v.getArg! 4)) (← evalBV seed (v.getArg! 5)) % m
  if v.isAppOfArity ``BitVec.ofNat 2 then return (← evalNat seed (v.getArg! 1)) % m
  if v.isAppOfArity ``OfNat.ofNat 3 then
    if let some n := v.nat? then return n % m
  if v.isAppOfArity ``HAdd.hAdd 6 then return ← bin (· + ·)
  if v.isAppOfArity ``HSub.hSub 6 then return ← bin (fun a b => m + a - b)
  if v.isAppOfArity ``HMul.hMul 6 then return ← bin (· * ·)
  if v.isAppOfArity ``HAppend.hAppend 6 then
    let tb ← whnfR (← inferType (v.getArg! 5))
    let wb := if tb.isAppOf ``BitVec then tb.appArg!.nat?.getD 0 else 0
    return (((← evalBV seed (v.getArg! 4)) <<< wb) ||| (← evalBV seed (v.getArg! 5))) % m
  if v.isAppOfArity ``BitVec.extractLsb' 4 then
    let some s := (v.getArg! 1).nat? | return atomVal seed v m
    let some l := (v.getArg! 2).nat? | return atomVal seed v m
    return ((← evalBV seed (v.getArg! 3)) >>> s) % 2 ^ l
  return atomVal seed v m
end

/-- the two terms (`BitVec` words when `bv`, numbers otherwise) agree on `nSeeds` valuations -/
def agreeOnRandom (bv : Bool) (l r : Expr) : MetaM Bool := do
  for seed in [1:7] do
    let a ← if bv then evalBV seed l else evalNat seed l
    let b ← if bv then evalBV seed r else evalNat seed r
    if a != b then return false
  return true

/-- the heartbeat limit of one pair proof (thousands) -/
def pairCapK : Nat := 1500
/-- most pair proofs tried by one `ved_spell_unify` -/
def pairMax : Nat := 24

/-- a proof of the proposition `P` by `tac` (the bounds of the variables of `es` in the context) under the pair limit, or none -/
def proveProp (P : Expr) (es : Array Expr) (tac : TacticM Unit) : TacticM (Option Expr) := do
  let mv ← mkFreshExprMVar P
  let hb0 ← IO.getNumHeartbeats
  -- a heartbeat timeout of the pair limit is a failure of this pair (a runtime exception: `tryCatchRuntimeEx`), not of the caller
  tryCatchRuntimeEx
    (do
      let gs ← withTheReader Core.Context (fun c => { c with maxHeartbeats := (if c.maxHeartbeats == 0 then pairCapK * 1000 else min c.maxHeartbeats (pairCapK * 1000)), initHeartbeats := hb0 }) do
        Tactic.run mv.mvarId! (withoutRecover (withBounds es tac))
      if gs.isEmpty then return some (← instantiateMVars mv) else return none)
    (fun ex => do
      if (← IO.getEnv "VED_UNIFYDBG").isSome then IO.eprintln s!"unify: prove failed: {((← ex.toMessageData.toString).replace "\n" " | ").take 600}"
      return none)

/-- a proof of `l = r` by `tac` under the pair limit, or none -/
def prove (l r : Expr) (tac : TacticM Unit) : TacticM (Option Expr) := do
  proveProp (← mkEq l r) #[l, r] tac

/-- one pass over a family of terms: the pairs of `terms` that are two spellings of one value (same variables, same type, `tac` proves the equation) are unified, the later spelling replaced by the earlier
one in the whole goal; returns the goal and the number of pairs unified -/
def unifyPairs (g : MVarId) (terms : Array Expr) (bv : Bool) (tac : TacticM Unit) (budget : IO.Ref Nat) : TacticM (MVarId × Nat) := do
  let mut g := g
  let mut done : Array Expr := #[]
  let mut n := 0
  let dbg := (← IO.getEnv "VED_UNIFYDBG").isSome
  for i in [0:terms.size] do
    for j in [i+1:terms.size] do
      let r := terms[i]!
      let b := terms[j]!
      if done.contains b || done.contains r || r == b then continue
      unless fvKey r == fvKey b do continue
      unless (← g.withContext (do isDefEq (← inferType r) (← inferType b))) do
        if dbg then IO.eprintln s!"unify: pair {i},{j}: types differ"
        continue
      unless (← g.withContext (agreeOnRandom bv r b)) do continue
      if (← budget.get) == 0 then return (g, n)
      budget.modify (· - 1)
      let some h ← g.withContext (setGoals [g] *> prove b r tac) | do
        if dbg then IO.eprintln s!"unify: pair {i},{j}: proof failed"
        continue
      let (g', k) ← rewriteAll g b r h
      if k > 0 then
        g := g'
        done := done.push b
        n := n + 1
  return (g, n)

/-- `ved_spell_unify` (option `ved.mem.s94AddrNorm`): (1) the addresses of the reads of one variable memory function: leaves of the `if`s of the addresses that are two spellings of one `BitVec`
(`ved_bv_addr_eq`), (2) the exponents `2 ^ e` of the target and the context that are two spellings of one number (`omega`); the later spelling replaced by the first everywhere. Fails when nothing is unified. -/
elab "ved_spell_unify" : tactic => do
  unless ved.mem.s94AddrNorm.get (← getOptions) do throwError "ved_spell_unify: option ved.mem.s94AddrNorm is off"
  if ← unifyRefuse.get then throwError "ved_spell_unify: refused (test seam)"
  let mut g ← getMainGoal
  let budget ← IO.mkRef pairMax
  let mut total := 0
  -- the rounds: an address inside an address (`M0 (.. M1 a ..)`) is unified once the inner one is (3 rounds at most)
  for _ in [0:3] do
    let mut round := 0
    -- (1) addresses
    let ps ← propsOf g
    let mut byFn : Array (FVarId × Array Expr) := #[]
    for t in ps do
      for rd in ← readsOf g t do
        let f := rd.getAppFn.fvarId!
        let ls := (addrLeaves rd.appArg!).filter fun a => !(collectDag (·.isFVar) a).isEmpty && !a.isFVar
        match byFn.findIdx? (·.1 == f) with
        | some i => byFn := byFn.modify i fun (f, as) => (f, ls.foldl (fun as a => if as.contains a then as else as.push a) as)
        | none => byFn := byFn.push (f, ls.foldl (fun as a => if as.contains a then as else as.push a) #[])
    if (← IO.getEnv "VED_UNIFYDBG").isSome then
      IO.eprintln s!"unify: enter props={ps.size}"
      for (f, ls) in byFn do
        IO.eprintln s!"unify: fn {(← g.withContext f.getUserName)} leaves {ls.size}"
        for l in ls do IO.eprintln s!"unify:   leaf key={fvKey l} {((← g.withContext (ppExpr l)).pretty.replace "\n" " ").take 160}"
    for (_, ls) in byFn do
      if ls.size < 2 then continue
      let (g', n) ← unifyPairs g ls true (do evalTactic (← `(tactic| ved_bv_addr_eq))) budget
      g := g'; round := round + n
    -- (2) exponents
    let ps ← propsOf g
    let mut exps : Array Expr := #[]
    for t in ps do
      for x in collectDag (fun x => x.isAppOfArity ``HPow.hPow 6 && (x.getArg! 4).isAppOfArity ``OfNat.ofNat 3 && !(collectDag (·.isFVar) (x.getArg! 5)).isEmpty) t do
        let e := x.getArg! 5
        unless exps.contains e do exps := exps.push e
    let (g', n) ← unifyPairs g exps false (do evalTactic (← `(tactic| omega))) budget
    g := g'; round := round + n
    total := total + round
    if round == 0 then break
  if total == 0 then throwError "ved_spell_unify: no two spellings of one value"
  Tools.VedMemLoop.dbgLog s!"spell_unify: {total} pairs unified"
  replaceMainGoal [g]
  unifyHits.modify (· + total)
  if ← unifyFailLate.get then throwError "ved_spell_unify: failed after its work (test seam)"

/-- `x ||| y = 0` iff both are 0 (the conditions `a * 2 ||| b = 0` of the packed fields against `¬(a * 2 = 0 ∧ b = 0)`) -/
theorem or_eq_zero_iff' (x y : Nat) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have h1 : x ≤ x ||| y := Nat.left_le_or
    have h2 : y ≤ x ||| y := Nat.right_le_or
    omega
  · rintro ⟨rfl, rfl⟩
    rfl

/-- a bit mask is below a power of two when one side is -/
theorem and_lt_left {x y n : Nat} (h : x < 2 ^ n) : x &&& y < 2 ^ n := Nat.lt_of_le_of_lt Nat.and_le_left h
theorem and_lt_right {x y n : Nat} (h : y < 2 ^ n) : x &&& y < 2 ^ n := Nat.lt_of_le_of_lt Nat.and_le_right h

/-- `x ||| y` with `x < 2 ^ k` is `x + y * 2 ^ k` (the bit fields are disjoint: `x` is below the field of `y`) -/
theorem or_mul_pow_eq_add (x y k : Nat) (h : x < 2 ^ k) : x ||| y * 2 ^ k = x + y * 2 ^ k := by
  rw [Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt h y, Nat.add_comm]

/-- the powers of two `2 ^ k` (k >= 3) that occur as literals in the propositions -/
def pow2Lits (ps : Array Expr) : Array Nat := Id.run do
  let mut ks : Array Nat := #[]
  for t in ps do
    for x in collectDag (fun x => x.isAppOfArity ``OfNat.ofNat 3) t do
      if let some n := x.nat? then
        if n ≥ 8 && n &&& (n - 1) == 0 && !ks.contains (Nat.log2 n) then ks := ks.push (Nat.log2 n)
  return ks.qsort (· < ·)

/-- `ved_or_bounds` (option `ved.mem.s94OrDisj`): for every `x ||| y` and `x ^^^ y` of the target and the context (natural numbers) the bound `x ||| y < 2 ^ k` for the smallest power `2 ^ k` that occurs
as a literal and bounds both sides (each side by `omega` from the bounds of the variables), `Nat.or_lt_two_pow` / `Nat.xor_lt_two_pow`; `omega` takes `x ||| y` for an atom otherwise and so
cannot see that `(x ||| y) % 2 ^ 64 = x ||| y`. Fails when no bound is proved. -/
elab "ved_or_bounds" : tactic => do
  unless ved.mem.s94OrDisj.get (← getOptions) do throwError "ved_or_bounds: option ved.mem.s94OrDisj is off"
  if ← orRefuse.get then throwError "ved_or_bounds: refused (test seam)"
  let mut g ← getMainGoal
  let ps ← propsOf g
  let isOr (x : Expr) : Bool := (x.isAppOfArity ``HOr.hOr 6 || x.isAppOfArity ``HXor.hXor 6 || x.isAppOfArity ``HAnd.hAnd 6) && (x.getArg! 0).isConstOf ``Nat
  let mut ts : Array Expr := #[]
  for t in ps do
    for x in collectDag isOr t do
      unless ts.contains x do ts := ts.push x
  let ks := pow2Lits ps
  let budget ← IO.mkRef (2 * pairMax)
  let mut n := 0
  for t in ts do
    -- the value of the term on random valuations must be below `2 ^ k`
    let mx ← g.withContext do
      let mut mx := 0
      for seed in [1:7] do mx := max mx (← evalNat seed t)
      pure mx
    for k in ks do
      if mx ≥ 2 ^ k then continue
      if (← budget.get) == 0 then break
      budget.modify (· - 1)
      let isXor := t.isAppOfArity ``HXor.hXor 6
      let rhs ← g.withContext (mkNumeral (mkConst ``Nat) (2 ^ k))
      let P ← g.withContext (mkAppM ``LT.lt #[t, rhs])
      let kS := Syntax.mkNumLit (toString k)
      let isAnd := t.isAppOfArity ``HAnd.hAnd 6
      let tac : TacticM Unit := do
        if isXor then evalTactic (← `(tactic| exact Nat.xor_lt_two_pow (n := $kS) (by omega) (by omega)))
        else if isAnd then evalTactic (← `(tactic| first | exact and_lt_right (n := $kS) (by omega) | exact and_lt_left (n := $kS) (by omega)))
        else evalTactic (← `(tactic| exact Nat.or_lt_two_pow (n := $kS) (by omega) (by omega)))
      let some pr ← g.withContext (setGoals [g] *> proveProp P #[t] tac) | continue
      let (_, g1) ← (← g.assert `ved_orb P pr).intro1P
      g := g1
      n := n + 1
      break
  if n == 0 then throwError "ved_or_bounds: no bound"
  replaceMainGoal [g]
  orHits.modify (· + n)
  if ← orFailLate.get then throwError "ved_or_bounds: failed after its work (test seam)"

/-- `ved_read_lift` (option `ved.mem.s94ReadLift`): `f (if c then a else b)` becomes `if c then f a else f b` (`read_ite`) for the variable memory functions `f`, and `(if c then x else y).toNat` of the
lifted reads `if c then x.toNat else y.toNat` (`toNat_ite`), in the target and the context, until nothing is left (at most 6 rounds). Fails when nothing is lifted. -/
elab "ved_read_lift" : tactic => do
  unless ved.mem.s94ReadLift.get (← getOptions) do throwError "ved_read_lift: option ved.mem.s94ReadLift is off"
  if ← liftRefuse.get then throwError "ved_read_lift: refused (test seam)"
  let mut g ← getMainGoal
  let mut total := 0
  for _ in [0:6] do
    let ps ← propsOf g
    let mut changed := 0
    -- reads at an `if` address
    let mut items : Array (Expr × Expr × Expr) := #[]
    for t in ps do
      for rd in ← readsOf g t do
        let a := rd.appArg!
        if a.isAppOfArity ``ite 5 && !items.any (·.1 == rd) then
          let f := rd.appFn!
          let ty ← g.withContext (inferType rd)
          let α := a.getArg! 0
          let h := mkAppN (mkConst ``read_ite) #[α, ty, f, a.getArg! 1, a.getArg! 2, a.getArg! 3, a.getArg! 4]
          let rhs := mkAppN (mkConst ``ite [1]) #[ty, a.getArg! 1, a.getArg! 2, mkApp f (a.getArg! 3), mkApp f (a.getArg! 4)]
          items := items.push (rd, rhs, h)
    for (l, r, h) in items do
      let (g', k) ← rewriteAll g l r h
      g := g'; changed := changed + k
    -- the `toNat` of such an `if`
    let ps ← propsOf g
    let mut items2 : Array (Expr × Expr × Expr) := #[]
    for t in ps do
      for x in collectDag (fun x => x.isAppOfArity ``BitVec.toNat 2 && (x.getArg! 1).isAppOfArity ``ite 5) t do
        let i := x.getArg! 1
        let isRd (e : Expr) : Bool := e.isApp && e.getAppFn.isFVar
        if isRd (i.getArg! 3) && isRd (i.getArg! 4) && !items2.any (·.1 == x) then
          let n := x.getArg! 0
          let h := mkAppN (mkConst ``toNat_ite) #[n, i.getArg! 1, i.getArg! 2, i.getArg! 3, i.getArg! 4]
          let rhs := mkAppN (mkConst ``ite [1]) #[mkConst ``Nat, i.getArg! 1, i.getArg! 2, mkApp2 (mkConst ``BitVec.toNat) n (i.getArg! 3), mkApp2 (mkConst ``BitVec.toNat) n (i.getArg! 4)]
          items2 := items2.push (x, rhs, h)
    for (l, r, h) in items2 do
      let (g', k) ← rewriteAll g l r h
      g := g'; changed := changed + k
    total := total + changed
    if changed == 0 then break
  if total == 0 then throwError "ved_read_lift: no read at an if address"
  Tools.VedMemLoop.dbgLog s!"read_lift: {total} propositions rewritten"
  replaceMainGoal [g]
  liftHits.modify (· + total)
  if ← liftFailLate.get then throwError "ved_read_lift: failed after its work (test seam)"

end Tools.VedMemS94Addr
