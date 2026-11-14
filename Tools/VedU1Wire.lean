import Lean
import Tools.VedU1Loop

/-!
# `ved_wire`: closing a large `Nat` / `Int` goal wire by wire (U1 loop script)

The goal that `#ved_u1` has to close for a register of a loop is an equation between the arithmetic of the
module (`Nat`, wrap-around by `% 2^w`, signed tests through the top bit) and of the declaration (`Int`,
`Int.bmod`, `BitVec.toInt`) that repeats a large term in every arm of nested clamps.  `omega` reads such a goal as
a tree and, on the whole system, runs out of memory or time (and is incomplete on the nested `/` / `%`).

`ved_wire` (UNTRUSTED: the kernel checks the resulting proof, the numeric samples only propose equalities)
1. replaces every operation node of the goal by a variable `w_k` with the equation `e_k : op(..) = w_k`
   over the earlier wires (innermost first), so that every equation has one operation;
2. evaluates every wire on a few sample points (the free atoms are drawn from their ranges) and, for every wire
   whose value equals that of an earlier wire, proves the equality `w_j = w_i` by `omega` in a context that holds
   only the two equations and the equalities already proved for their operands;
3. closes the goal from the equalities.
-/

namespace Tools.VedU1Wire

open Lean Meta Elab Tactic

theorem ved_cast_ite (c : Prop) [Decidable c] (a b : Nat) :
    ((if c then a else b : Nat) : Int) = if c then (a : Int) else (b : Int) := by
  split <;> rfl

/-! ### bit operations with a numeral operand

`a &&& c`, `a ^^^ c`, `a ||| c` for a numeral `c` are rewritten, one bit at a time, to `/ 2` and `% 2` terms
(`c` halves at each step, so the rewriting stops at `0`), which `omega` reads. -/

theorem and_mod2 (a c : Nat) : (a &&& c) % 2 = (a % 2) * (c % 2) := by
  have h := Nat.testBit_and a c 0
  simp only [Nat.testBit_zero] at h
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hc : c % 2 = 0 ∨ c % 2 = 1 := by omega
  have hb : (a &&& c) % 2 = 0 ∨ (a &&& c) % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hc with hc | hc <;> rcases hb with hb | hb <;> simp_all
theorem and_step (a c : Nat) : a &&& c = 2 * ((a / 2) &&& (c / 2)) + (a % 2) * (c % 2) := by
  have h1 : (a &&& c) / 2 = (a / 2) &&& (c / 2) := by simpa using (Nat.and_div_two_pow (a := a) (b := c) (n := 1))
  have h2 := and_mod2 a c
  omega
theorem xor_mod2 (a c : Nat) : (a ^^^ c) % 2 = (a % 2 + c % 2) % 2 := by
  have h := Nat.testBit_xor a c 0
  simp only [Nat.testBit_zero] at h
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hc : c % 2 = 0 ∨ c % 2 = 1 := by omega
  have hb : (a ^^^ c) % 2 = 0 ∨ (a ^^^ c) % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hc with hc | hc <;> rcases hb with hb | hb <;> simp_all
theorem xor_step (a c : Nat) : a ^^^ c = 2 * ((a / 2) ^^^ (c / 2)) + (a % 2 + c % 2) % 2 := by
  have h1 : (a ^^^ c) / 2 = (a / 2) ^^^ (c / 2) := by simpa using (Nat.xor_div_two_pow (a := a) (b := c) (n := 1))
  have h2 := xor_mod2 a c
  omega
theorem or_mod2 (a c : Nat) : (a ||| c) % 2 = (a % 2 + c % 2 - (a % 2) * (c % 2)) := by
  have h := Nat.testBit_or a c 0
  simp only [Nat.testBit_zero] at h
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hc : c % 2 = 0 ∨ c % 2 = 1 := by omega
  have hb : (a ||| c) % 2 = 0 ∨ (a ||| c) % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hc with hc | hc <;> rcases hb with hb | hb <;> simp_all
theorem or_step (a c : Nat) : a ||| c = 2 * ((a / 2) ||| (c / 2)) + (a % 2 + c % 2 - (a % 2) * (c % 2)) := by
  have h1 : (a ||| c) / 2 = (a / 2) ||| (c / 2) := by simpa using (Nat.or_div_two_pow (a := a) (b := c) (n := 1))
  have h2 := or_mod2 a c
  omega
theorem and_step_r (a c : Nat) (_hc : c ≠ 0) : a &&& c = 2 * ((a / 2) &&& (c / 2)) + (a % 2) * (c % 2) := and_step a c
theorem and_step_l (a c : Nat) (_hc : c ≠ 0) : c &&& a = 2 * ((c / 2) &&& (a / 2)) + (c % 2) * (a % 2) := and_step c a
theorem xor_step_r (a c : Nat) (_hc : c ≠ 0) : a ^^^ c = 2 * ((a / 2) ^^^ (c / 2)) + (a % 2 + c % 2) % 2 := xor_step a c
theorem xor_step_l (a c : Nat) (_hc : c ≠ 0) : c ^^^ a = 2 * ((c / 2) ^^^ (a / 2)) + (c % 2 + a % 2) % 2 := xor_step c a
theorem or_step_r (a c : Nat) (_hc : c ≠ 0) : a ||| c = 2 * ((a / 2) ||| (c / 2)) + (a % 2 + c % 2 - (a % 2) * (c % 2)) := or_step a c
theorem or_step_l (a c : Nat) (_hc : c ≠ 0) : c ||| a = 2 * ((c / 2) ||| (a / 2)) + (c % 2 + a % 2 - (c % 2) * (a % 2)) := or_step c a

theorem and_step_r1 (a c : Nat) (_hc : c ≠ 0) (_h : c < 2) : a &&& c = 2 * ((a / 2) &&& (c / 2)) + (a % 2) * (c % 2) := and_step a c
theorem and_step_l1 (a c : Nat) (_hc : c ≠ 0) (_h : c < 2) : c &&& a = 2 * ((c / 2) &&& (a / 2)) + (c % 2) * (a % 2) := and_step c a
theorem xor_step_r1 (a c : Nat) (_hc : c ≠ 0) (_h : c < 2) : a ^^^ c = 2 * ((a / 2) ^^^ (c / 2)) + (a % 2 + c % 2) % 2 := xor_step a c
theorem xor_step_l1 (a c : Nat) (_hc : c ≠ 0) (_h : c < 2) : c ^^^ a = 2 * ((c / 2) ^^^ (a / 2)) + (c % 2 + a % 2) % 2 := xor_step c a
theorem or_step_r1 (a c : Nat) (_hc : c ≠ 0) (_h : c < 2) : a ||| c = 2 * ((a / 2) ||| (c / 2)) + (a % 2 + c % 2 - (a % 2) * (c % 2)) := or_step a c
theorem or_step_l1 (a c : Nat) (_hc : c ≠ 0) (_h : c < 2) : c ||| a = 2 * ((c / 2) ||| (a / 2)) + (c % 2 + a % 2 - (c % 2) * (a % 2)) := or_step c a

/-- the rewriting of the bit operations with the numeral operand `1` -/
macro "ved_bitlit1" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := decide) only [Tools.VedU1Wire.and_step_r1, Tools.VedU1Wire.and_step_l1,
     Tools.VedU1Wire.xor_step_r1, Tools.VedU1Wire.xor_step_l1, Tools.VedU1Wire.or_step_r1, Tools.VedU1Wire.or_step_l1,
     Nat.reduceDiv, Nat.reduceMod, Nat.reduceXor, Nat.reduceAnd, Nat.reduceOr, Nat.and_zero, Nat.zero_and,
     Nat.xor_zero, Nat.zero_xor, Nat.or_zero, Nat.zero_or, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] $[$loc]?)

/-- the rewriting of the bit operations with a numeral operand -/
macro "ved_bitlit" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := decide) only [Tools.VedU1Wire.and_step_r, Tools.VedU1Wire.and_step_l,
     Tools.VedU1Wire.xor_step_r, Tools.VedU1Wire.xor_step_l, Tools.VedU1Wire.or_step_r, Tools.VedU1Wire.or_step_l,
     Nat.reduceDiv, Nat.reduceMod, Nat.reduceXor, Nat.reduceAnd, Nat.reduceOr, Nat.and_zero, Nat.zero_and,
     Nat.xor_zero, Nat.zero_xor, Nat.or_zero, Nat.zero_or, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] $[$loc]?)

/-! ### operation nodes -/

/-- an arithmetic operation node of type `Nat` / `Int` that mentions a free variable -/
def isWireOp (e : Expr) : MetaM Bool := do
  if e.hasLooseBVars || e.hasMVar || !e.hasFVar then return false
  let f := e.getAppFn
  unless f.isConst do return false
  let n := f.constName!
  let ar := e.getAppNumArgs
  let ok :=
    ((n == ``HAdd.hAdd || n == ``HSub.hSub || n == ``HMul.hMul || n == ``HDiv.hDiv || n == ``HMod.hMod
        || n == ``HPow.hPow) && ar == 6)
    || (n == ``ite && ar == 5) || (n == ``Int.bmod && ar == 2) || (n == ``Nat.cast && ar == 3)
    || (n == ``Neg.neg && ar == 3)
    || ((n == ``HXor.hXor || n == ``HAnd.hAnd || n == ``HOr.hOr) && ar == 6 && (e.getArg! 0).isConstOf ``Nat)
  unless ok do return false
  let ty ← whnfR (← inferType e)
  return ty.isConstOf ``Nat || ty.isConstOf ``Int

def kids (e : Expr) : Array Expr :=
  match e with
  | .app f a => #[f, a]
  | .lam _ t b _ => #[t, b]
  | .forallE _ t b _ => #[t, b]
  | .letE _ t v b _ => #[t, v, b]
  | .mdata _ b => #[b]
  | .proj _ _ b => #[b]
  | _ => #[]

/-- the operation nodes of `es` none of whose proper subterms is an operation node (each once) -/
def readyOps (es : Array Expr) : MetaM (Array Expr) := do
  let mut memo : Std.HashMap Expr Bool := {}
  let mut out : Array Expr := #[]
  -- iterative post-order
  let mut stack : Array (Expr × Bool) := es.reverse.map (·, false)
  while !stack.isEmpty do
    let (e, done) := stack.back!
    stack := stack.pop
    if memo.contains e then continue
    if !done then
      stack := stack.push (e, true)
      for k in kids e do
        unless memo.contains k do stack := stack.push (k, false)
    else
      let mut any := false
      for k in kids e do
        if memo.getD k false then any := true
      let isop ← isWireOp e
      if isop && !any then out := out.push e
      memo := memo.insert e (any || isop)
  return out

/-! ### evaluation on sample points -/

/-- the value of a `Nat` / `Int` term (a proposition for `evalP`) under `env` (values of the wires and atoms);
`none` for a shape not understood -/
partial def evalI (env : Expr → Option Int) (e : Expr) : Option Int := do
  if let some v := env e then return v
  if let some n := e.nat? then return n
  if let some n := e.int? then return n
  let f := e.getAppFn
  guard f.isConst
  let n := f.constName!
  let ar := e.getAppNumArgs
  let isNat := (e.getArg! 0).isConstOf ``Nat
  if ar == 6 && (n == ``HAdd.hAdd || n == ``HSub.hSub || n == ``HMul.hMul || n == ``HDiv.hDiv || n == ``HMod.hMod) then
    let a ← evalI env (e.getArg! 4)
    let b ← evalI env (e.getArg! 5)
    if n == ``HAdd.hAdd then return a + b
    if n == ``HSub.hSub then return (if isNat then max 0 (a - b) else a - b)
    if n == ``HMul.hMul then return a * b
    if n == ``HDiv.hDiv then return a / b
    return a % b
  if ar == 6 && n == ``HPow.hPow then
    let a ← evalI env (e.getArg! 4)
    let b ← evalI env (e.getArg! 5)
    guard (b ≥ 0 && b ≤ 4096)
    return a ^ b.toNat
  if ar == 6 && isNat && (n == ``HXor.hXor || n == ``HAnd.hAnd || n == ``HOr.hOr) then
    let a ← evalI env (e.getArg! 4)
    let b ← evalI env (e.getArg! 5)
    guard (a ≥ 0 && b ≥ 0)
    if n == ``HXor.hXor then return Int.ofNat (a.toNat ^^^ b.toNat)
    if n == ``HAnd.hAnd then return Int.ofNat (a.toNat &&& b.toNat)
    return Int.ofNat (a.toNat ||| b.toNat)
  if ar == 3 && n == ``Nat.cast then return ← evalI env (e.getArg! 2)
  if ar == 3 && n == ``Neg.neg then return - (← evalI env (e.getArg! 2))
  if ar == 2 && n == ``Int.bmod then
    let x ← evalI env (e.getArg! 0)
    let m ← evalI env (e.getArg! 1)
    guard (m > 0)
    let r := x % m
    return (if r < (m + 1) / 2 then r else r - m)
  if ar == 5 && n == ``ite then
    let c ← evalP env (e.getArg! 1)
    return ← evalI env (if c then e.getArg! 3 else e.getArg! 4)
  none
where
  evalP (env : Expr → Option Int) (c : Expr) : Option Bool := do
    let f := c.getAppFn
    guard f.isConst
    let n := f.constName!
    let ar := c.getAppNumArgs
    if ar == 4 && (n == ``LT.lt || n == ``LE.le || n == ``GT.gt || n == ``GE.ge) then
      let a ← evalI env (c.getArg! 2)
      let b ← evalI env (c.getArg! 3)
      if n == ``LT.lt then return decide (a < b)
      if n == ``LE.le then return decide (a ≤ b)
      if n == ``GT.gt then return decide (a > b)
      return decide (a ≥ b)
    if ar == 3 && (n == ``Eq || n == ``Ne) then
      let a ← evalI env (c.getArg! 1)
      let b ← evalI env (c.getArg! 2)
      return (if n == ``Eq then decide (a = b) else decide (a ≠ b))
    if ar == 1 && n == ``Not then return !(← evalP env (c.getArg! 0))
    if ar == 2 && n == ``And then return (← evalP env (c.getArg! 0)) && (← evalP env (c.getArg! 1))
    if ar == 2 && n == ``Or then return (← evalP env (c.getArg! 0)) || (← evalP env (c.getArg! 1))
    if n == ``True then return true
    if n == ``False then return false
    none

/-- the atoms of `e`: `Nat` / `Int` subterms that are neither operation nodes, numerals, nor wires
(`isWire`), not descended into -/
partial def atomsOf (isWire : FVarId → Bool) (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  if e.hasLooseBVars then return acc
  if e.isFVar && isWire e.fvarId! then return acc
  if e.nat?.isSome || e.int?.isSome then return acc
  let ty? ← try some <$> whnfR (← inferType e) catch _ => pure none
  let isNI := match ty? with | some ty => ty.isConstOf ``Nat || ty.isConstOf ``Int | none => false
  if isNI then
    let f := e.getAppFn
    let n := if f.isConst then f.constName! else Name.anonymous
    let ar := e.getAppNumArgs
    let isOp :=
      ((n == ``HAdd.hAdd || n == ``HSub.hSub || n == ``HMul.hMul || n == ``HDiv.hDiv || n == ``HMod.hMod
          || n == ``HPow.hPow) && ar == 6)
      || (n == ``ite && ar == 5) || (n == ``Int.bmod && ar == 2) || (n == ``Nat.cast && ar == 3)
      || (n == ``Neg.neg && ar == 3) || (n == ``OfNat.ofNat && ar == 3)
      || ((n == ``HXor.hXor || n == ``HAnd.hAnd || n == ``HOr.hOr) && ar == 6)
    unless isOp do
      return (if acc.contains e then acc else acc.push e)
  let mut acc := acc
  for k in kids e do acc ← atomsOf isWire k acc
  return acc

/-- `atomsOf` over several terms, each shared subterm visited once (the goal is a DAG whose tree is huge) -/
partial def atomsOfDag (isWire : FVarId → Bool) (es : Array Expr) : MetaM (Array Expr) := do
  let mut seen : Std.HashSet Expr := {}
  let mut acc : Array Expr := #[]
  let mut todo : Array Expr := es.reverse
  while !todo.isEmpty do
    let e := todo.back!
    todo := todo.pop
    if seen.contains e then continue
    seen := seen.insert e
    if e.hasLooseBVars then
      for k in kids e do todo := todo.push k
      continue
    if e.isFVar && isWire e.fvarId! then continue
    if e.nat?.isSome || e.int?.isSome then continue
    let ty? ← try some <$> whnfR (← inferType e) catch _ => pure none
    let isNI := match ty? with | some ty => ty.isConstOf ``Nat || ty.isConstOf ``Int | none => false
    if isNI then
      let f := e.getAppFn
      let n := if f.isConst then f.constName! else Name.anonymous
      let ar := e.getAppNumArgs
      let isOp :=
        ((n == ``HAdd.hAdd || n == ``HSub.hSub || n == ``HMul.hMul || n == ``HDiv.hDiv || n == ``HMod.hMod
            || n == ``HPow.hPow) && ar == 6)
        || (n == ``ite && ar == 5) || (n == ``Int.bmod && ar == 2) || (n == ``Nat.cast && ar == 3)
        || (n == ``Neg.neg && ar == 3) || (n == ``OfNat.ofNat && ar == 3)
        || ((n == ``HXor.hXor || n == ``HAnd.hAnd || n == ``HOr.hOr) && ar == 6)
      unless isOp do
        unless acc.contains e do acc := acc.push e
        continue
    for k in (kids e).reverse do todo := todo.push k
  return acc

/-! ### the proof search state -/

/-- a deterministic pseudo-random stream -/
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

/-- sample values of an atom with range `[0, hi]` (the corners and a few pseudo-random points) -/
def sampleAtom (hi : Nat) (seed : Nat) (n : Nat) : Array Int := Id.run do
  let corners : Array Nat := #[0, hi, hi / 2, hi / 2 + 1, 1, hi - 1]
  let mut s := seed
  let mut out : Array Int := #[]
  for _ in [0:n] do
    s := lcg s
    let r := s / 65536
    let v := if r % 3 == 0 then corners[(r / 3) % corners.size]! else (r / 7) % (hi + 1)
    out := out.push (Int.ofNat v)
  return out

/-- the upper bound `hi` with `0 ≤ atom ≤ hi` that the context states for `a` (`a < n`, possibly inside `∧`), or
`2^w - 1` for `BitVec.toNat`, else `2^32 - 1` -/
partial def atomHi (a : Expr) : MetaM Nat := do
  let mut best : Option Nat := none
  let rec scan (t : Expr) : Option Nat :=
    if t.isAppOfArity ``And 2 then
      match scan (t.getArg! 0), scan (t.getArg! 1) with
      | some x, some y => some (min x y)
      | some x, none => some x
      | none, y => y
    else if t.isAppOfArity ``LT.lt 4 && (t.getArg! 2) == a then
      (t.getArg! 3).nat?.map (· - 1)
    else if t.isAppOfArity ``LE.le 4 && (t.getArg! 2) == a then
      (t.getArg! 3).nat?
    else none
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      if let some h := scan (← instantiateMVars d.type) then
        best := some (match best with | some b => min b h | none => h)
  if let some h := best then return h
  if a.isAppOfArity ``BitVec.toNat 2 then
    if let some w := (a.getArg! 0).nat? then return 2 ^ w - 1
  return 2 ^ 32 - 1

/-- the numbers of samples -/
def nSamples : Nat := 24

/-! ### `omega` in a small context -/

/-- an `omega` that splits the remaining `if`s of the (small) context by `by_cases` where `omega` alone fails -/
partial def dfsOmega (fuel : Nat) : TacticM Unit := do
  let st ← saveState
  try
    evalTactic (← `(tactic| omega))
    return
  catch _ => st.restore
  if fuel == 0 then throwError "ved_wire: dfsOmega out of fuel"
  let g ← getMainGoal
  let some c ← g.withContext do
      let isIte := fun (s : Expr) => s.isAppOfArity ``ite 5 && !s.hasLooseBVars
      let mut r : Option Expr := none
      let tgt ← instantiateMVars (← g.getType)
      if let some s := tgt.find? isIte then r := some (s.getArg! 1)
      if r.isNone then
        for d in ← getLCtx do
          if !d.isImplementationDetail && r.isNone then
            if let some s := (← instantiateMVars d.type).find? isIte then r := some (s.getArg! 1)
      pure r
    | throwError "ved_wire: no `if` left and omega fails"
  let cs ← Term.exprToSyntax c
  let hc := mkIdent `ved_c
  evalTactic (← `(tactic| by_cases $hc:ident : $cs))
  let gs ← getGoals
  let mut i := 0
  for g' in gs do
    setGoals [g']
    try
      if i == 0 then evalTactic (← `(tactic| simp only [if_pos $hc:ident] at *))
      else evalTactic (← `(tactic| simp only [if_neg $hc:ident] at *))
    catch _ => pure ()
    i := i + 1
    dfsOmega (fuel - 1)
  setGoals []

/-- clear every proposition of the context of `g` that is not in `keep` -/
def clearOthers (g : MVarId) (keep : Std.HashSet FVarId) : MetaM MVarId := do
  g.withContext do
    let ids := (← getLCtx).foldl (init := #[]) fun acc d =>
      if d.isImplementationDetail || keep.contains d.fvarId then acc else acc.push d
    let mut g := g
    for d in ids.reverse do
      if (← isProp d.type) then
        g ← (try g.clear d.fvarId catch _ => pure g)
    return g

/-- the free variables of `es` and, transitively, of their types, in context order -/
def fvarsClosure (es : Array Expr) : MetaM (Array FVarId) := do
  let mut st : CollectFVars.State := {}
  for e in es do st := collectFVars st e
  let mut todo := st.fvarIds
  let mut seen : Std.HashSet FVarId := {}
  while !todo.isEmpty do
    let f := todo.back!
    todo := todo.pop
    if seen.contains f then continue
    seen := seen.insert f
    let d ← f.getDecl
    let mut s2 : CollectFVars.State := {}
    s2 := collectFVars s2 (← instantiateMVars d.type)
    for g in s2.fvarIds do unless seen.contains g do todo := todo.push g
  let lctx ← getLCtx
  let arr := seen.toArray
  return arr.qsort fun a b => (lctx.get! a).index < (lctx.get! b).index

/-- `pf : prop` as an application of an auxiliary theorem (closed over the variables `pf` and `prop` use), so
that the proof term of the goal stays small -/
def auxProof (prop pf : Expr) : MetaM Expr := do
  let xs ← fvarsClosure #[prop, pf]
  let xsE := xs.map mkFVar
  let ty ← mkForallFVars xsE prop
  let val ← mkLambdaFVars xsE pf
  let c ← mkAuxTheorem ty val
  return mkAppN c xsE

def isWireName (n : Name) (pre : String) : Bool :=
  match n with
  | .str .anonymous s => s.startsWith pre
  | _ => false

/-- `subst` of the proved equalities `ved_p.. : a = b` between two wires (the operands of equal wires become
the same variable, so that operations over them are the same atom for `omega`) -/
def substWires : TacticM Unit := do
  let names ← withMainContext do
    let mut out : Array Name := #[]
    for d in ← getLCtx do
      if !d.isImplementationDetail && isWireName d.userName "ved_p" then
        if let some (_, a, b) := (← instantiateMVars d.type).eq? then
          if a.isFVar && b.isFVar then out := out.push d.userName
    pure out
  for n in names do
    let g ← getMainGoal
    let some d := (← g.withContext getLCtx).findFromUserName? n | continue
    try
      let g' ← Lean.Meta.subst g d.fvarId
      replaceMainGoal [g']
    catch _ => pure ()

/-- an upper bound `n` with `x < 2^n` read off the context (`x ≤ c` or `x < c` for a numeral `c`), else found by
`omega` among the widths 1, 2, 4, ..., 128 -/
def widthOf? (x : Expr) : TacticM (Option Nat) := do
  let bitlen := fun (c : Nat) => if c == 0 then 0 else Nat.log2 c + 1
  if let some c := x.nat? then return some (bitlen c)
  let types ← withMainContext do
    let mut ts : Array Expr := #[]
    for d in ← getLCtx do
      unless d.isImplementationDetail do ts := ts.push (← instantiateMVars d.type)
    pure ts
  let mut best : Option Nat := none
  for t in types do
    if t.isAppOfArity ``LE.le 4 && (t.getArg! 2) == x then
      if let some c := (t.getArg! 3).nat? then
        best := some (match best with | some b => min b (bitlen c) | none => bitlen c)
    else if t.isAppOfArity ``LT.lt 4 && (t.getArg! 2) == x then
      if let some c := (t.getArg! 3).nat? then
        best := some (match best with | some b => min b (bitlen (c - 1)) | none => bitlen (c - 1))
  if best.isSome then return best
  for n in [1, 2, 4, 8, 16, 32, 64, 128] do
    let bound ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit n]
    if (← withMainContext (Tools.VedU1Loop.omegaProof? (← mkAppM ``LT.lt #[x, bound]))).isSome then return some n
  return none

/-- the bit facts of the bit operations that stay in the context:
`a ^^^ b`, `a ||| b` below `2^n` when both operands are, `a &&& b` below each operand -/
def addBitFacts : TacticM Unit := do
  let props ← withMainContext do
    let mut ps : Array Expr := #[← instantiateMVars (← getMainTarget)]
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        if (← isProp d.type) then ps := ps.push (← instantiateMVars d.type)
    pure ps
  let mut ops : Array Expr := #[]
  for p in props do
    for o in Tools.VedU1Loop.natBitOps p do
      unless ops.contains o do ops := ops.push o
  for t in ops do
    let a := t.getArg! 4
    let b := t.getArg! 5
    if t.isAppOfArity ``HAnd.hAnd 6 then
      withMainContext do
        evalTactic (← `(tactic| have := @Nat.and_le_left $(← Term.exprToSyntax a) $(← Term.exprToSyntax b)))
        evalTactic (← `(tactic| have := @Nat.and_le_right $(← Term.exprToSyntax a) $(← Term.exprToSyntax b)))
    else
      let some na ← widthOf? a | continue
      let some nb ← widthOf? b | continue
      let n := max na nb
      let bound ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit n]
      let some ha ← withMainContext (Tools.VedU1Loop.omegaProof? (← mkAppM ``LT.lt #[a, bound])) | continue
      let some hb ← withMainContext (Tools.VedU1Loop.omegaProof? (← mkAppM ``LT.lt #[b, bound])) | continue
      let lem ← if t.isAppOfArity ``HXor.hXor 6
        then mkAppM ``Nat.xor_lt_two_pow #[ha, hb] else mkAppM ``Nat.or_lt_two_pow #[ha, hb]
      withMainContext do evalTactic (← `(tactic| have := $(← Term.exprToSyntax lem)))

/-- a proof of `prop` in the context of the main goal reduced to `keep`, by `dfsOmega` (after the `bmod` and
cast-of-`if` rewrites); `none` when it fails -/
def localProof? (prop : Expr) (keep : Std.HashSet FVarId) (fuel : Nat) (bits : Bool := false) : TacticM (Option Expr) := do
  let saved ← getGoals
  let hb ← IO.getNumHeartbeats
  -- `level`: 0 no rewriting of bit operations, 1 those with the numeral `1`, 2 those with any numeral (the
  -- rewritten terms are large for `omega`, so the cheaper contexts are tried first); without bit operations
  -- in the goal only level 0
  let levels : List Nat := if bits then [0, 1, 2] else [0]
  for level in levels do
    let m ← mkFreshExprMVar prop
    let m' ← clearOthers m.mvarId! keep
    setGoals [m']
    let ok ← tryCatchRuntimeEx
      (withTheReader Core.Context (fun c => { c with initHeartbeats := hb, maxHeartbeats := 400000 * 1000 })
        (do
          -- a step can close the goal (`subst` of the proved equality of the two wires makes it `w = w`)
          let step : TacticM Unit → TacticM Unit := fun t => do unless (← getGoals).isEmpty do t
          if bits then substWires
          step (evalTactic (← `(tactic| try simp only [Int.bmod_def, Tools.VedU1Wire.ved_cast_ite] at *)))
          if level == 1 then step (evalTactic (← `(tactic| try ved_bitlit1 at *)))
          if level == 2 then step (evalTactic (← `(tactic| try ved_bitlit at *)))
          if bits then step addBitFacts
          if (← getGoals).isEmpty then return true
          dfsOmega fuel
          pure (← getGoals).isEmpty))
      fun _ => pure false
    setGoals saved
    if ok then return some (← auxProof prop (← instantiateMVars m))
  return none

/-! ### intervals -/

/-- an interval `[lo, hi]` of the value of `e` from the intervals of its parts (`bnd` for the wires and atoms) -/
partial def interval (bnd : Expr → Option (Int × Int)) (e : Expr) : Option (Int × Int) := do
  if let some b := bnd e then return b
  if let some n := e.nat? then return (n, n)
  if let some n := e.int? then return (n, n)
  let f := e.getAppFn
  guard f.isConst
  let n := f.constName!
  let ar := e.getAppNumArgs
  let isNat := (e.getArg! 0).isConstOf ``Nat
  if ar == 6 && (n == ``HAdd.hAdd || n == ``HSub.hSub || n == ``HMul.hMul || n == ``HDiv.hDiv || n == ``HMod.hMod) then
    let (l1, h1) ← interval bnd (e.getArg! 4)
    let (l2, h2) ← interval bnd (e.getArg! 5)
    if n == ``HAdd.hAdd then return (l1 + l2, h1 + h2)
    if n == ``HSub.hSub then
      return (if isNat then (max 0 (l1 - h2), max 0 (h1 - l2)) else (l1 - h2, h1 - l2))
    if n == ``HMul.hMul then
      let cs := [l1 * l2, l1 * h2, h1 * l2, h1 * h2]
      return (cs.foldl min (l1 * l2), cs.foldl max (l1 * l2))
    if n == ``HDiv.hDiv then
      guard (l2 > 0)
      return (l1 / h2, h1 / l2)
    guard (l2 > 0)
    if 0 ≤ l1 && h1 < l2 then return (l1, h1)
    return (0, h2 - 1)
  if ar == 6 && isNat && (n == ``HXor.hXor || n == ``HAnd.hAnd || n == ``HOr.hOr) then
    let (l1, h1) ← interval bnd (e.getArg! 4)
    let (l2, h2) ← interval bnd (e.getArg! 5)
    guard (l1 ≥ 0 && l2 ≥ 0)
    if n == ``HAnd.hAnd then return (0, min h1 h2)
    let m := (max h1 h2).toNat
    return (0, Int.ofNat (2 ^ (if m == 0 then 0 else Nat.log2 m + 1)) - 1)
  if ar == 6 && n == ``HPow.hPow then
    let (l1, h1) ← interval bnd (e.getArg! 4)
    let k ← (e.getArg! 5).nat?
    guard (l1 ≥ 0 && k ≤ 4096)
    return (l1 ^ k, h1 ^ k)
  if ar == 3 && n == ``Nat.cast then return ← interval bnd (e.getArg! 2)
  if ar == 3 && n == ``Neg.neg then
    let (l, h) ← interval bnd (e.getArg! 2)
    return (-h, -l)
  if ar == 2 && n == ``Int.bmod then
    let m ← (e.getArg! 1).nat?
    return (-(m / 2 : Nat), (m + 1) / 2 - 1)
  if ar == 5 && n == ``ite then
    let (l1, h1) ← interval bnd (e.getArg! 3)
    let (l2, h2) ← interval bnd (e.getArg! 4)
    return (min l1 l2, max h1 h2)
  none

/-! ### wiring -/

/-- an instance argument (head constant `inst...`) -/
def isInstArg (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ => match n with
    | .str _ s => s.startsWith "inst"
    | _ => false
  | _ => false

/-- `a` and `b` agree up to their instance arguments (an `ite` can carry a `Decidable` instance built from a
different, definitionally equal, spelling of its condition) -/
partial def redProj (e : Expr) : Expr :=
  if e.isAppOfArity ``Prod.fst 3 then
    let p := redProj (e.getArg! 2)
    if p.isAppOfArity ``Prod.mk 4 then redProj (p.getArg! 2) else e
  else if e.isAppOfArity ``Prod.snd 3 then
    let p := redProj (e.getArg! 2)
    if p.isAppOfArity ``Prod.mk 4 then redProj (p.getArg! 3) else e
  else e

partial def eqMod (a b : Expr) : Bool :=
  if a == b then true else
  let a := redProj a
  let b := redProj b
  if a == b then true else
  match a, b with
  | .app .., .app .. =>
    let xs := a.getAppArgs
    let ys := b.getAppArgs
    a.getAppFn == b.getAppFn && xs.size == ys.size
      && (List.range xs.size).all fun i => (isInstArg xs[i]! && isInstArg ys[i]!) || eqMod xs[i]! ys[i]!
  | _, _ => false

/-- the main goal `G` (with the hypotheses that mention `e` put back into it) becomes `∀ x, e = x → G[e := x]`
applied to `e` and `rfl`; the new variable and equation are named `xn`, `hn` -/
def wireOne (e : Expr) (xn hn : Name) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let ty ← inferType e
    let mut rev : Array FVarId := #[]
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        if (← isProp d.type) && (d.type.find? (eqMod · e)).isSome then rev := rev.push d.fvarId
    let (fvs, g1) ← g.revert rev (preserveOrder := true)
    g1.withContext do
      let tgt ← instantiateMVars (← g1.getType)
      let newTy ← withLocalDeclD xn ty fun xv => do
        let body := tgt.replace fun t => if eqMod t e then some xv else none
        withLocalDeclD hn (← mkEq e xv) fun hv => mkForallFVars #[xv, hv] body
      let g2 ← mkFreshExprMVar newTy
      g1.assign (mkApp2 g2 e (← mkEqRefl e))
      let (_, g3) ← g2.mvarId!.introN 2 [xn, hn]
      let (_, g4) ← g3.introNP fvs.size
      replaceMainGoal [g4]

/-- the hypothesis of the main goal called `n` -/
def hypNamed (n : Name) : TacticM LocalDecl := withMainContext do
  let some d := (← getLCtx).findFromUserName? n | throwError "ved_wire: no hypothesis {n}"
  return d

/-- the wire variables (`ved_w..`) of the context that occur in `t` -/
def wiresIn (t : Expr) : MetaM (Array FVarId) := do
  let mut out : Array FVarId := #[]
  for d in ← getLCtx do
    if isWireName d.userName "ved_w" && (t.find? (· == d.toExpr)).isSome then out := out.push d.fvarId
  return out

/-- the numeral `n` of type `Int` -/
def intLit (n : Int) : MetaM Expr := do
  let pos ← mkAppOptM ``OfNat.ofNat #[mkConst ``Int, mkRawNatLit n.natAbs, none]
  if n < 0 then mkAppM ``Neg.neg #[pos] else pure pos

/-- the hypotheses `keep`s of a local proof about the wires `S` (names): the equations of those, the equalities
and ranges that mention them, the hypotheses that mention no wire -/
def keepFor (eqs : Array Name) (S : Array FVarId) : TacticM (Std.HashSet FVarId) := withMainContext do
  let mut keep : Std.HashSet FVarId := {}
  -- the wires reachable from `S` through the proved equalities
  let mut reach : Std.HashSet FVarId := {}
  for f in S do reach := reach.insert f
  let mut pHyps : Array (FVarId × Array FVarId) := #[]
  for d in ← getLCtx do
    if !d.isImplementationDetail && isWireName d.userName "ved_p" then
      pHyps := pHyps.push (d.fvarId, ← wiresIn (← instantiateMVars d.type))
  discard <| pure pHyps
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    unless (← isProp d.type) do continue
    let ty ← instantiateMVars d.type
    let ws ← wiresIn ty
    if isWireName d.userName "ved_e" then
      if eqs.contains d.userName then keep := keep.insert d.fvarId
    else if ws.isEmpty then keep := keep.insert d.fvarId
    else if ws.any (reach.contains ·) then keep := keep.insert d.fvarId
  return keep

/-- add the range facts of the wire `xn` (definition `e`, interval `(lo, hi)`) as hypotheses `ved_g..` when
`omega` proves them from the equation and the ranges of the operands -/
def addRange (k : Nat) (xn hn : Name) (isNat : Bool) (lo hi : Int) (bits : Bool := false) : TacticM Unit := do
  let d ← hypNamed xn
  let xe := d.toExpr
  let (eqTy, S) ← withMainContext do
    let h ← hypNamed hn
    pure (h.type, (← wiresIn h.type).push d.fvarId)
  let keep ← keepFor #[hn] S
  let props ← withMainContext do
    let mut props : Array Expr := #[]
    if isNat then
      if hi ≥ 0 then props := props.push (← mkAppM ``LE.le #[xe, mkNatLit hi.toNat])
    else
      props := props.push (← mkAppM ``LE.le #[xe, ← intLit hi])
      props := props.push (← mkAppM ``LE.le #[← intLit lo, xe])
    pure props
  for p in props do
    let some pf ← withMainContext (localProof? p keep 3 bits) | continue
    let g ← getMainGoal
    let (_, g') ← (← g.assert (Name.mkSimple s!"ved_g{k}") p pf).intro1P
    replaceMainGoal [g']
  discard <| pure eqTy

/-- the equality of the wires `xi` and `xj` (a cast on the `Nat` side if their types differ) -/
def wireEq (xi xj : Name) : TacticM (Expr × Bool) := withMainContext do
  let di ← hypNamed xi
  let dj ← hypNamed xj
  let ti ← whnfR di.type
  let tj ← whnfR dj.type
  let up (d : LocalDecl) (isNat : Bool) : MetaM Expr :=
    if isNat then mkAppOptM ``Nat.cast #[mkConst ``Int, none, d.toExpr] else pure d.toExpr
  let iNat := ti.isConstOf ``Nat
  let jNat := tj.isConstOf ``Nat
  let a ← up di (iNat && !jNat)
  let b ← up dj (jNat && !iNat)
  return (← mkEq a b, true)

/-- the wires of `es`: the proof state of `ved_wire` -/
structure St where
  k : Nat := 0
  vals : Std.HashMap Name (Array Int) := {}
  bnd : Std.HashMap Name (Int × Int) := {}
  atomVals : Std.HashMap Expr (Array Int) := {}
  atomBnd : Std.HashMap Expr (Int × Int) := {}
  classes : Std.HashMap (Array Int) (Array Name) := {}
  cclasses : Std.HashMap (Nat × Array Int) (Array Name) := {}
  mods : Array Nat := #[]
  nAtoms : Nat := 0
  proved : Nat := 0
  tried : Nat := 0
  bits : Bool := false

def tag {α} (t : String) (x : TacticM α) : TacticM α :=
  try x catch e => throwError "{t}: {e.toMessageData}"

/-- `(xi : Int) % m = (xj : Int) % m` -/
def wireCong (xi xj : Name) (m : Nat) : TacticM Expr := withMainContext do
  let di ← hypNamed xi
  let dj ← hypNamed xj
  let up (d : LocalDecl) : MetaM Expr := do
    if (← whnfR d.type).isConstOf ``Nat then mkAppOptM ``Nat.cast #[mkConst ``Int, none, d.toExpr] else pure d.toExpr
  let mi ← intLit m
  mkEq (← mkAppM ``HMod.hMod #[← up di, mi]) (← mkAppM ``HMod.hMod #[← up dj, mi])

/-- a proof of `prop` (an equality of the wires `xi`, `xj`) by `omega` with the equations of a cone around the two
wires that grows by one layer of operands (and of the wires already proved equal to them) at each of `maxDepth`
steps -/
def proveCone (prop : Expr) (starts : Array Name) (maxDepth : Nat) (bits : Bool := false) : TacticM (Option Expr) := do
  let mut pr : Option Expr := none
  let mut layer : Array Name := starts
  let mut cone : Array Name := starts
  for depth in [0:maxDepth] do
    if pr.isSome then break
    let (eqNames, S) ← withMainContext do
      let mut S : Array FVarId := #[]
      let mut eqNames : Array Name := #[]
      for w in cone do
        let d ← hypNamed w
        S := S.push d.fvarId
        let he ← hypNamed (Name.mkSimple s!"ved_e{(w.toString.drop 5).toNat!}")
        eqNames := eqNames.push he.userName
        for f in ← wiresIn he.type do
          unless S.contains f do S := S.push f
      pure (eqNames, S)
    let keep ← keepFor eqNames S
    pr ← withMainContext (localProof? prop keep 12 bits)
    if pr.isNone && depth + 1 < maxDepth then
      let next ← withMainContext do
        let mut out : Array Name := #[]
        for w in layer do
          let he ← hypNamed (Name.mkSimple s!"ved_e{(w.toString.drop 5).toNat!}")
          for f in ← wiresIn he.type do
            let n ← f.getUserName
            unless cone.contains n || out.contains n do out := out.push n
          for d in ← getLCtx do
            if !d.isImplementationDetail && isWireName d.userName "ved_p" then
              let ws ← wiresIn (← instantiateMVars d.type)
              let wn ← ws.mapM (·.getUserName)
              if wn.contains w then
                for n in wn do
                  unless cone.contains n || out.contains n do out := out.push n
        pure out
      if next.isEmpty then break
      layer := next
      cone := cone ++ next
  return pr

/-- one wire: the candidate `e` is replaced by a variable, with its range facts and, when its sample values
equal those of an earlier wire, the proved equality -/
def wireStep (st : IO.Ref St) (e : Expr) : TacticM Unit := do
  let s ← st.get
  let k := s.k
  let xn := Name.mkSimple s!"ved_w{k}"
  let hn := Name.mkSimple s!"ved_e{k}"
  let (vec, iv, isNat) ← withMainContext do
    let lctx ← getLCtx
    let isW := fun (f : FVarId) => match lctx.find? f with | some d => isWireName d.userName "ved_w" | none => false
    -- atoms of the definition and their samples
    let atoms ← atomsOf isW e #[]
    for a in atoms do
      unless (← st.get).atomVals.contains a do
        let hi ← atomHi a
        let n := (← st.get).nAtoms
        st.modify fun s => { s with
          atomVals := s.atomVals.insert a (sampleAtom hi (n * 7919 + 13) nSamples)
          atomBnd := s.atomBnd.insert a (0, hi)
          nAtoms := n + 1 }
    let s ← st.get
    let wireVal := fun (f : FVarId) => match lctx.find? f with
      | some d => s.vals[d.userName]?
      | none => none
    let mut vec : Option (Array Int) := some #[]
    for i in [0:nSamples] do
      let env := fun (x : Expr) =>
        if x.isFVar then (wireVal x.fvarId!).bind (·[i]?) else (s.atomVals[x]?).bind (·[i]?)
      match vec, evalI env e with
      | some v, some x => vec := some (v.push x)
      | _, _ => vec := none
    let wireBnd := fun (x : Expr) =>
      if x.isFVar then (match lctx.find? x.fvarId! with | some d => s.bnd[d.userName]? | none => none)
      else s.atomBnd[x]?
    let iv := interval wireBnd e
    let isNat := (← whnfR (← inferType e)).isConstOf ``Nat
    pure (vec, iv, isNat)
  tag "wireOne" (wireOne e xn hn)
  if let some v := vec then st.modify fun s => { s with vals := s.vals.insert xn v }
  if let some (lo, hi) := iv then
    st.modify fun s => { s with bnd := s.bnd.insert xn (if isNat then (max 0 lo, hi) else (lo, hi)) }
    tag "addRange" (addRange k xn hn isNat lo hi (← st.get).bits)
  -- the moduli seen so far (literal right operands of `%`)
  if e.isAppOfArity ``HMod.hMod 6 then
    if let some m := (e.getArg! 5).nat? then
      if m ≥ 65536 && !(← st.get).mods.contains m then st.modify fun s => { s with mods := s.mods.push m }
  if let some v := vec then
    -- pair with an earlier wire of the same values
    let cls := (← st.get).classes.getD v #[]
    let mut done := false
    for xi in cls.toList.take 3 do
      if done then break
      let (prop, _) ← tag "wireEq" (wireEq xi xn)
      st.modify fun s => { s with tried := s.tried + 1 }
      let pr ← proveCone prop #[xi, xn] 4 (← st.get).bits
      if let some pf := pr then
        tag "assert" do
          let g ← getMainGoal
          let (_, g') ← (← g.assert (Name.mkSimple s!"ved_p{k}") prop pf).intro1P
          replaceMainGoal [g']
        st.modify fun s => { s with proved := s.proved + 1 }
        done := true
    st.modify fun s => { s with classes := s.classes.insert v (cls.push xn) }
    -- congruent modulo a seen modulus (a wrapped sum and its unwrapped signed counterpart)
    if !done then
      for m in (← st.get).mods do
        if done then break
        let key := (m, v.map (· % (m : Int)))
        let ccls := (← st.get).cclasses.getD key #[]
        let mut n := 0
        for xi in ccls do
          if done || n ≥ 2 then break
          if (← st.get).vals[xi]? == some v then continue
          n := n + 1
          let prop ← tag "wireCong" (wireCong xi xn m)
          st.modify fun s => { s with tried := s.tried + 1 }
          let pr ← proveCone prop #[xi, xn] 3 (← st.get).bits
          if let some pf := pr then
            tag "assert" do
              let g ← getMainGoal
              let (_, g') ← (← g.assert (Name.mkSimple s!"ved_pc{k}") prop pf).intro1P
              replaceMainGoal [g']
            st.modify fun s => { s with proved := s.proved + 1 }
            done := true
    for m in (← st.get).mods do
      let key := (m, v.map (· % (m : Int)))
      st.modify fun s => { s with cclasses := s.cclasses.insert key ((s.cclasses.getD key #[]).push xn) }
  st.modify fun s => { s with k := s.k + 1 }

/-- `ved_wire`: see the module docstring -/
elab "ved_wire" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  if Tools.VedU1Loop.treeSizeVal tgt < Tools.VedU1Loop.shareMinTree then return
  let st ← IO.mkRef ({} : St)
  evalTactic (← `(tactic| try simp only [Nat.reduceAdd, Nat.reducePow, Int.reducePow, Int.reduceAdd] at *))
  let collectEs : TacticM (Array Expr) := withMainContext do
    let mut es : Array Expr := #[← instantiateMVars (← getMainTarget)]
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        let n := d.userName
        unless isWireName n "ved_e" || isWireName n "ved_g" || isWireName n "ved_p" do
          let t ← instantiateMVars d.type
          if (← isProp t) then es := es.push t
    pure es
  -- a goal with bit operations (`^^^`, `&&&`, `|||` on `Nat`): the atoms (the inputs of the module, the register
  -- values) become wires as well, so that `w0 = in % 256` and `in` are two wires of equal value and the operations
  -- over them can be compared (`substWires`)
  let bits := (← collectEs).any fun e => (Tools.VedU1Loop.natBitOps e).size > 0
  st.modify fun s => { s with bits := bits }
  if bits then
    let mut tried : Array Expr := #[]
    for _ in [0:200] do
      let es ← collectEs
      let lctx ← getLCtx
      let isW := fun (f : FVarId) => match lctx.find? f with | some d => isWireName d.userName "ved_w" | none => false
      let atoms ← atomsOfDag isW es
      let some a := atoms.find? (fun a => !tried.contains a && a.hasFVar) | break
      tried := tried.push a
      tag "wireAtom" (wireStep st a)
  for _ in [0:200] do
    let es ← collectEs
    let cands ← readyOps es
    if cands.isEmpty then break
    tag s!"wireStep" (wireStep st cands[0]!)
  let s ← st.get
  trace[Elab.tactic] "ved_wire: {s.k} wires, {s.proved}/{s.tried} equalities"
  -- the goal from the equalities
  tag "final" do
    let g ← getMainGoal
    let (tgt, starts) ← withMainContext do
      let t ← instantiateMVars (← getMainTarget)
      let ws ← wiresIn t
      pure (t, ← ws.mapM (·.getUserName))
    let some pf ← proveCone tgt starts 6 s.bits | throwError "ved_wire: the goal is not proved from the equalities"
    g.assign pf
    replaceMainGoal []

/-- `ved_pack_wire`: the packing step of the loop script (`ved_pack_simp`) on a goal of ordinary size; on a large goal
(`shareMinTree` nodes read as a tree) `ved_wire`, whose failure is the failure of the step -/
elab "ved_pack_wire" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  if Tools.VedU1Loop.treeSizeVal tgt < Tools.VedU1Loop.shareMinTree then
    evalTactic (← `(tactic| try ved_pack_simp))
  else
    evalTactic (← `(tactic| ved_wire))

/-- `ved_bmod_close`: the last resort of the closing step: `Int.bmod` (not known to `omega`) rewritten by its
definition, the `if`s of the goal split, then `omega` -/
macro "ved_bmod_close" : tactic =>
  `(tactic| ((try simp only [Int.bmod_def, Tools.VedU1Wire.ved_cast_ite]) <;> ((repeat' split) <;> omega)))

end Tools.VedU1Wire
