import Lean
import Sparkle.Core.Signal
import Tools.VedU1Lemmas

/-!
# Loop-state invariant support for the U1 entry (several registers)

A module with several registers built with `Signal.loop` (a `circuit do` block: one `Signal.loop`
over the tuple of register values) is proved by the invariant "register `n_i` of the module equals
the `toNat` of the `i`-th component of the loop's state at the same cycle", by induction on the
cycle.  This file holds the pieces of that proof that do not depend on the checker:

* `loop_val_unfold`: the fixpoint equation of `Signal.loop` at every cycle for a body `F` whose
  cycle 0 value is independent of its argument and whose value at `t+1` depends on its argument
  only through the value at `t` (checked by `rfl` / `simp` for the concrete body; the lemma is a
  theorem, no axiom: it unfolds `loopGo`);
* the tactic `ved_loop_R ins ["n₀", …]`: assigns the invariant `?R` of
  `Tools.VedU1Entry.outputs_of_step` from the `Signal.loop` it finds in the goal (UNTRUSTED: the
  kernel checks the resulting proof; a wrong choice leaves a goal that cannot be closed).
-/

namespace Tools.VedU1Loop

open Sparkle.Core.Domain Sparkle.Core.Signal

open Lean Elab Tactic in
/-- `omega` with a small heartbeat budget of its own (the rewrite rules below call it as a
side-condition discharger, many times, on goals that can be large): running out of the budget is an
ordinary failure of this tactic. -/
elab "ved_omega" : tactic => do
  let hb ← IO.getNumHeartbeats
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with initHeartbeats := hb, maxHeartbeats := 2000 * 1000 })
      (Tactic.withoutRecover (evalTactic (← `(tactic| omega)))))
    fun _ => throwError "ved_omega: no proof within the budget"

theorem loop_val_unfold {dom : DomainConfig} {α : Type} [Inhabited α]
    (F : Signal dom α → Signal dom α)
    (h0 : ∀ s₁ s₂ : Signal dom α, (F s₁).val 0 = (F s₂).val 0)
    (hS : ∀ (s₁ s₂ : Signal dom α) (t : Nat), s₁.val t = s₂.val t →
      (F s₁).val (t + 1) = (F s₂).val (t + 1)) (t : Nat) :
    (Signal.loop F).val t = (F (Signal.loop F)).val t := by
  show Signal.loopGo F t = _
  rw [Signal.loopGo_eq]
  cases t with
  | zero => exact h0 _ _
  | succ u =>
    apply hS
    show (if u < u + 1 then Signal.loopGo F u else default) = Signal.loopGo F u
    rw [if_pos (Nat.lt_succ_self u)]

/-! ### single-bit logic on `Nat` (gate-level `&&&`, `|||`, `^^^` of one-bit wires)

Stated with the range hypotheses the script discharges by `omega` (after `split` for the
`if 1 else 0` of a comparison); the right-hand sides are `if`s, which `split` + `omega` close. -/

theorem and_lt2_l (x y : Nat) (hx : x < 2) : x &&& y = if x = 0 then 0 else y % 2 := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl
  · simp
  · simp [Nat.one_and_eq_mod_two]

theorem and_lt2_r (x y : Nat) (hy : y < 2) : x &&& y = if y = 0 then 0 else x % 2 := by
  rw [Nat.and_comm]; exact and_lt2_l y x hy

theorem or_lt2 (x y : Nat) (hx : x < 2) (hy : y < 2) : x ||| y = if x = 0 then y else 1 := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;> rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> simp

theorem xor_lt2 (x y : Nat) (hx : x < 2) (hy : y < 2) : x ^^^ y = if x = y then 0 else 1 := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;> rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> simp

theorem bool_true_iff (b : Bool) : b = true ↔ b.toNat = 1 := Bool.toNat_eq_one.symm

theorem bool_false_iff (b : Bool) : b = false ↔ b.toNat = 0 := by cases b <;> simp

/-! ### unpacking the loop state

The module packs the registers of a loop into one wire (`a * 2^k + b`) and slices the fields back
out (`x / 2^k % 2^w`); `omega` alone is incomplete on these nested `/` and `%`.  These rewrite
rules (range side conditions closed by `omega`) read a field back directly. -/

theorem div_pack (a b m : Nat) (hm : 0 < m) : (a * m + b) / m = a + b / m := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.add_comm]

theorem mod_pack (a b m : Nat) : (a * m + b) % m = b % m := by
  rw [Nat.add_comm]; exact Nat.add_mul_mod_self_right _ _ _

macro "ved_pack_simp" : tactic =>
  `(tactic| simp (disch := first | ved_omega | fail) only
      [Nat.reducePow, Nat.reduceAdd, Nat.mod_eq_of_lt, Nat.div_eq_of_lt, Tools.VedU1Loop.div_pack, Tools.VedU1Loop.mod_pack, Nat.add_mod_left, Nat.add_zero])

/-- the one-bit logic rewrite, with the range side conditions closed by `omega` -/
macro "ved_bit_simp" : tactic =>
  `(tactic| simp (disch := first | ved_omega | (split <;> ved_omega) | fail) only
      [Tools.VedU1Loop.and_lt2_l, Tools.VedU1Loop.and_lt2_r, Tools.VedU1Loop.or_lt2, Tools.VedU1Loop.xor_lt2])

open Lean Meta Elab Tactic

/-- a numeral of `Nat` or a `BitVec` literal (`n#w`, `OfNat.ofNat`) -/
def isNumLit (e : Lean.Expr) : Bool :=
  e.nat?.isSome || e.isRawNatLit
    || (e.isAppOfArity ``BitVec.ofNat 2 && (e.getArg! 1).nat?.isSome)
    || (e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).isRawNatLit)

/-- `x * n` with `n` a literal and `x` not one: `n * x`, for `x : α` with `α` as chosen by `isTy`.
The kernel unfolds `x * n` (structural recursion on `n`) when it has to evaluate the `toNat` of the
product, which is not feasible for a 32-bit literal; with the literal first the recursion is on `x`
and gets stuck. -/
def mulLitComm (isTy : Lean.Expr → Bool) (e : Lean.Expr) : Simp.SimpM Simp.Step := do
  unless e.isAppOfArity ``HMul.hMul 6 do return .continue
  let x := e.getArg! 4
  let y := e.getArg! 5
  if !isNumLit y || isNumLit x then return .continue
  let ty ← inferType x
  unless isTy ty do return .continue
  let pf ← if ty.isConstOf ``Nat then mkAppM ``Nat.mul_comm #[x, y]
    else mkAppM ``BitVec.mul_comm #[x, y]
  let e' ← mkAppM ``HMul.hMul #[y, x]
  return .visit { expr := e', proof? := some pf }

/-- `ved_mul_lit_bv`: `x * n#w` to `n#w * x` on `BitVec` (used by name: `simp [ved_mul_lit_bv]`) -/
simproc_decl ved_mul_lit_bv (HMul.hMul _ _) := mulLitComm (·.isAppOf ``BitVec)

/-- `ved_mul_lit_nat`: `x * n` to `n * x` on `Nat` (used by name) -/
simproc_decl ved_mul_lit_nat (HMul.hMul _ _) := mulLitComm (·.isConstOf ``Nat)

/-- the `Signal.loop` applications of `e` with no loose bound variable, children before parents
(a loop inside another's body comes first: the order the synthesizer allocates their registers) -/
partial def collectLoops (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
  let acc := match e with
    | .app f a => collectLoops a (collectLoops f acc)
    | .lam _ t b _ => collectLoops b (collectLoops t acc)
    | .forallE _ t b _ => collectLoops b (collectLoops t acc)
    | .letE _ t v b _ => collectLoops b (collectLoops v (collectLoops t acc))
    | .mdata _ b => collectLoops b acc
    | .proj _ _ b => collectLoops b acc
    | _ => acc
  if e.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 && !e.hasLooseBVars && !acc.contains e then acc.push e else acc

def loopsOf (e : Lean.Expr) : Array Lean.Expr := collectLoops e #[]

/-- all `a ||| b` on `Nat` in `e` (each distinct term once) -/
def natOrs (e : Lean.Expr) : Array Lean.Expr := Id.run do
  let mut out : Array Lean.Expr := #[]
  let mut todo : Array Lean.Expr := #[e]
  while !todo.isEmpty do
    let x := todo.back!
    todo := todo.pop
    if x.isAppOfArity ``HOr.hOr 6 && (x.getArg! 0).isConstOf ``Nat then
      unless out.contains x do out := out.push x
    match x with
    | .app f a => todo := (todo.push a).push f
    | .lam _ t b _ => todo := (todo.push b).push t
    | .forallE _ t b _ => todo := (todo.push b).push t
    | .letE _ t v b _ => todo := ((todo.push b).push v).push t
    | .mdata _ b => todo := todo.push b
    | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return out

/-- a proof of `prop` by `omega` in the current context, or `none` (nothing is logged) -/
def omegaProof? (prop : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let saved ← getGoals
  let m ← mkFreshExprMVar prop
  setGoals [m.mvarId!]
  let r ← try
      Tactic.withoutRecover (evalTactic (← `(tactic| ved_omega)))
      pure (← getGoals).isEmpty
    catch _ => pure false
  setGoals saved
  if r then return some (← instantiateMVars m) else return none

/-- `ved_or_lit`: rewrite `c ||| x` (either order) as `c + x` when, for some `w`, `x < 2^w` and
`c % 2^w = 0` (both proved by `omega`; `w` is the least with `x < 2^w`).  The single-register
shape `(acc <<< 8) ||| byte`, and a numeral `c` with the small operand `x`. -/
elab "ved_or_lit" : tactic => withMainContext do
  let mut skip : Array Lean.Expr := #[]
  for _ in [0:64] do
    if (← getGoals).isEmpty then break  -- the last `rw` closed the goal (`rfl`)
    let tgt ← instantiateMVars (← getMainTarget)
    let cands := (natOrs tgt).filter (!skip.contains ·)
    let some t := cands[0]? | break
    let a := t.getArg! 4
    let b := t.getArg! 5
    let mut done := false
    for (c, x, swapped) in [(a, b, false), (b, a, true)] do
      if done then break
      -- least `w` with `x < 2^w`
      let mut found : Option (Nat × Lean.Expr) := none
      for w in [0:65] do
        let p ← mkAppM ``LT.lt #[x, ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit w]]
        if let some pf ← omegaProof? p then
          found := some (w, pf)
          break
      let some (w, hx) := found | continue
      let pc ← mkEq (← mkAppM ``HMod.hMod #[c, ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit w]]) (mkNatLit 0)
      let some hc ← omegaProof? pc | continue
      let lem ← mkAppM ``Tools.VedU1Lemmas.or_hi #[c, x, mkNatLit w, hx, hc]
      let lemS ← Term.exprToSyntax lem
      if swapped then
        let cs ← Term.exprToSyntax c
        let xs ← Term.exprToSyntax x
        evalTactic (← `(tactic| rw [Nat.or_comm $xs $cs, $lemS:term]))
      else
        evalTactic (← `(tactic| rw [$lemS:term]))
      done := true
    unless done do skip := skip.push t

/-- all `a ^^^ b`, `a ||| b`, `a &&& b` on `Nat` in `e` (each distinct term once) -/
def natBitOps (e : Lean.Expr) : Array Lean.Expr := Id.run do
  let mut out : Array Lean.Expr := #[]
  let mut todo : Array Lean.Expr := #[e]
  while !todo.isEmpty do
    let x := todo.back!
    todo := todo.pop
    if (x.isAppOfArity ``HXor.hXor 6 || x.isAppOfArity ``HOr.hOr 6 || x.isAppOfArity ``HAnd.hAnd 6)
        && (x.getArg! 0).isConstOf ``Nat then
      unless out.contains x do out := out.push x
    match x with
    | .app f a => todo := (todo.push a).push f
    | .lam _ t b _ => todo := (todo.push b).push t
    | .forallE _ t b _ => todo := (todo.push b).push t
    | .letE _ t v b _ => todo := ((todo.push b).push v).push t
    | .mdata _ b => todo := todo.push b
    | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return out

/-- all `a * b` on `Nat` in `e` with neither factor a numeral (each distinct term once) -/
def natMuls (e : Lean.Expr) : Array Lean.Expr := Id.run do
  let mut out : Array Lean.Expr := #[]
  let mut todo : Array Lean.Expr := #[e]
  while !todo.isEmpty do
    let x := todo.back!
    todo := todo.pop
    if x.isAppOfArity ``HMul.hMul 6 && (x.getArg! 0).isConstOf ``Nat
        && (x.getArg! 4).nat?.isNone && (x.getArg! 5).nat?.isNone then
      unless out.contains x do out := out.push x
    match x with
    | .app f a => todo := (todo.push a).push f
    | .lam _ t b _ => todo := (todo.push b).push t
    | .forallE _ t b _ => todo := (todo.push b).push t
    | .letE _ t v b _ => todo := ((todo.push b).push v).push t
    | .mdata _ b => todo := todo.push b
    | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return out

/-- `ved_mul_facts`: for a product `a * b` of two non-numeral factors, `a < 2^n` and `b < 2^m`
(least `n`, `m` found by `omega`) give `a * b < 2^n * 2^m`; `omega` treats the product as an
atom and needs this bound. -/
elab "ved_mul_facts" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let cands : List Nat := (List.range 130).tail! ++ (List.range 60).map (fun i => 136 + 8 * i)
  for t in natMuls tgt do
    let a := t.getArg! 4
    let b := t.getArg! 5
    let least (x : Lean.Expr) : TacticM (Option (Nat × Lean.Expr)) := do
      for n in cands do
        let bound ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit n]
        if let some h ← omegaProof? (← mkAppM ``LT.lt #[x, bound]) then return some (n, h)
      return none
    let some (_, ha) ← least a | continue
    let some (_, hb) ← least b | continue
    let lem ← mkAppM ``Nat.mul_lt_mul'' #[ha, hb]
    evalTactic (← `(tactic| have := $(← Term.exprToSyntax lem)))

/-- `ved_bits_facts`: for every `a ^^^ b` / `a ||| b` in the goal whose operands are below `2^n`
(least `n` found by `omega`), add `a ^^^ b < 2^n`; for every `a &&& b`, add `a &&& b ≤ a` and
`≤ b`.  `omega` treats the bitwise term as an atom and needs these bounds. -/
elab "ved_bits_facts" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let cands : List Nat := (List.range 130).tail! ++ (List.range 60).map (fun i => 136 + 8 * i)
  for t in natBitOps tgt do
    let a := t.getArg! 4
    let b := t.getArg! 5
    if t.isAppOfArity ``HAnd.hAnd 6 then
      evalTactic (← `(tactic| have := @Nat.and_le_left $(← Term.exprToSyntax a) $(← Term.exprToSyntax b)))
      evalTactic (← `(tactic| have := @Nat.and_le_right $(← Term.exprToSyntax a) $(← Term.exprToSyntax b)))
    else
      let mut done := false
      for n in cands do
        if done then break
        let two := mkNatLit 2
        let bound ← mkAppM ``HPow.hPow #[two, mkNatLit n]
        let some ha ← omegaProof? (← mkAppM ``LT.lt #[a, bound]) | continue
        let some hb ← omegaProof? (← mkAppM ``LT.lt #[b, bound]) | continue
        let lem ← if t.isAppOfArity ``HXor.hXor 6
          then mkAppM ``Nat.xor_lt_two_pow #[ha, hb] else mkAppM ``Nat.or_lt_two_pow #[ha, hb]
        evalTactic (← `(tactic| have := $(← Term.exprToSyntax lem)))
        done := true

/-- `i`-th component of a right-nested product value -/
partial def compProj (e : Lean.Expr) (i : Nat) : MetaM Lean.Expr := do
  -- a bare (non-tuple) state `Signal.loop (fun s : Signal d (BitVec w) => …)` is its own component
  if i == 0 && !(← whnfR (← inferType e)).isAppOf ``Prod then return e
  if i == 0 then mkAppM ``Prod.fst #[e] else compProj (← mkAppM ``Prod.snd #[e]) (i - 1)

/-- `toNat` of a `BitVec w` / `Bool` component -/
def compToNat (e : Lean.Expr) : MetaM Lean.Expr := do
  let ty ← whnfR (← inferType e)
  match ty.getAppFnArgs with
  | (``BitVec, _) => mkAppM ``BitVec.toNat #[e]
  | (``Bool, _) => mkAppM ``Bool.toNat #[e]
  | _ => throwError "ved_loop_R: unsupported state component type {ty}"

/-- the components of a right-nested state tuple (`α × β × … × Unit`): their types -/
partial def stateComps (ty : Lean.Expr) : MetaM (List Lean.Expr) := do
  let ty ← whnfR ty
  match ty.getAppFnArgs with
  | (``Prod, #[a, b]) => return (← whnfR a) :: (← stateComps b)
  | (``BitVec, _) | (``Bool, _) => return [ty]  -- a bare (non-tuple) state
  | _ => return []

/-- bit width of a state component (`Bool` is one bit) -/
def compWidth (ty : Lean.Expr) : MetaM (Option Nat) := do
  match (← whnfR ty).getAppFnArgs with
  | (``Bool, _) => return some 1
  | (``BitVec, #[w]) => return (← instantiateMVars w).nat?
  | _ => return none

/-- match the state's components to the module's registers `(name, width)`: position by position
when the widths agree (the synthesizer allocates a loop's registers in component order), else by
width in order (greedy); the kernel checks the choice -/
def matchRegs (widths : List (Option Nat)) (regs : List (String × Nat)) : Option (List String) := Id.run do
  if widths.length == regs.length && (widths.zip regs).all (fun (w, r) => w == some r.2) then
    return some (regs.map (·.1))
  let mut avail := regs
  let mut out : List String := []
  for w in widths do
    let some w := w | return none
    match avail.find? (·.2 == w) with
    | some r =>
      out := out ++ [r.1]
      avail := avail.erase r
    | none => return none
  return (if avail.isEmpty then some out else none)

elab "ved_loop_R " ins:ident " [" ns:str,* "]" ws:num,* : tactic => withMainContext do
  let insE ← elabTerm ins.raw none
  let g ← getMainGoal
  let mut tgt ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    unless d.isImplementationDetail do tgt := mkApp tgt (← instantiateMVars d.type)
  let loops := loopsOf tgt
  if loops.isEmpty then
    let shown := (← ppExpr tgt).pretty.take 3000
    throwError "ved_loop_R: no Signal.loop in the goal: {shown}"
  let ms ← getMVars tgt
  let mut rId? : Option MVarId := none
  for m in ms do
    if (← m.getTag).eraseMacroScopes == `R then rId? := some m
  let some rId := rId? | throwError "ved_loop_R: no invariant mvar ?R in the goal"
  let regs := (ns.getElems.map (·.getString)).toList.zip (ws.getElems.map (·.getNat)).toList
  -- the components of every loop, in loop order
  let mut compsOf : Array (List Lean.Expr) := #[]
  for L in loops do
    let some α := L.getAppArgs[1]? | throwError "ved_loop_R: malformed Signal.loop"
    compsOf := compsOf.push (← stateComps α)
  let widths ← (compsOf.toList.flatten).mapM fun c => compWidth c
  let some names := matchRegs widths regs
    | throwError "ved_loop_R: the state components {widths} of {loops.size} loop(s) {compsOf.map (·.length)} do not match the module registers {regs}"
  forallTelescope (← inferType (mkMVar rId)) fun xs _ => do
    unless xs.size == 3 do throwError "ved_loop_R: unexpected invariant type"
    let mut eqs : Array Lean.Expr := #[]
    let mut k := 0
    for j in [0:loops.size] do
      let L' := loops[j]!.replaceFVar insE xs[0]!
      let lv ← mkAppM ``Sparkle.Core.Signal.Signal.val #[L', xs[1]!]
      for i in [0:compsOf[j]!.length] do
        let c ← compToNat (← compProj lv i)
        eqs := eqs.push (← mkEq (mkApp xs[2]! (mkStrLit names[k]!)) c)
        k := k + 1
    let some last := eqs.back? | throwError "ved_loop_R: no registers"
    let body := (eqs.pop).foldr (fun e r => mkAnd e r) last
    rId.assign (← mkLambdaFVars xs body)

/-- `ved_loop_unfold t`: rewrite `(Signal.loop F).val t` by the fixpoint equation (every loop
whose value at `t` occurs in the goal) -/
macro "ved_loop_unfold " t:term : tactic =>
  `(tactic| repeat (rw [Tools.VedU1Loop.loop_val_unfold _ ?h0 ?hS $t]
                    case h0 => intro _ _; rfl
                    case hS => intro s1 s2 t h; simp only [h]))

/-- `ved_loop_gen s`: generalise the state `(Signal.loop F).val s` of every loop found in the goal
or hypotheses to variables, everywhere, and take the tuple apart (`Bool` components are split
into their two values) -/
elab "ved_loop_gen " s:ident : tactic => withMainContext do
  let sE ← elabTerm s.raw none
  let g ← getMainGoal
  let mut tgt ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    unless d.isImplementationDetail do tgt := mkApp tgt (← instantiateMVars d.type)
  let loops := loopsOf tgt
  if loops.isEmpty then throwError "ved_loop_gen: no Signal.loop in the goal"
  for j in [0:loops.size] do
    let v ← mkAppM ``Sparkle.Core.Signal.Signal.val #[loops[j]!, sE]
    let vs ← Term.exprToSyntax v
    let X := mkIdent (Name.mkSimple s!"ved_X{j}")
    let some α := loops[j]!.getAppArgs[1]? | throwError "ved_loop_gen: malformed Signal.loop"
    let bare := !(← whnfR α).isAppOf ``Prod
    if bare then
      evalTactic (← `(tactic| all_goals generalize $vs = $(mkIdent (Name.mkSimple s!"ved_x{j}_0")):ident at *))
    else
      evalTactic (← `(tactic| all_goals generalize $vs = $X at *))
    let n := (← stateComps α).length
    let xs := (List.range (if bare then 1 else n + 1)).toArray.map fun i => mkIdent (Name.mkSimple s!"ved_x{j}_{i}")
    let pats ← xs.mapM fun x => `(Lean.Parser.Tactic.rcasesPatLo| $x:ident)
    if bare then pure ()
    else evalTactic (← `(tactic| all_goals rcases $X:ident with ⟨$pats,*⟩))
    for x in xs do
      let some d := (← withMainContext getLCtx).findFromUserName? x.getId | continue
      if (← whnfR d.type).isConstOf ``Bool then
        evalTactic (← `(tactic| all_goals cases $x:ident))

end Tools.VedU1Loop
