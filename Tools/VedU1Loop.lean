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

/-- the one-bit logic rewrite, with the range side conditions closed by `omega` -/
macro "ved_bit_simp" : tactic =>
  `(tactic| simp (disch := first | omega | (split <;> omega) | fail) only
      [Tools.VedU1Loop.and_lt2_l, Tools.VedU1Loop.and_lt2_r, Tools.VedU1Loop.or_lt2, Tools.VedU1Loop.xor_lt2])

open Lean Meta Elab Tactic

/-- the `Signal.loop` applications of `e` with no loose bound variable (outermost first) -/
def loopsOf (e : Lean.Expr) : Array Lean.Expr :=
  (Id.run do
    let mut out : Array Lean.Expr := #[]
    let mut todo : Array Lean.Expr := #[e]
    while !todo.isEmpty do
      let x := todo.back!
      todo := todo.pop
      if x.isAppOf ``Sparkle.Core.Signal.Signal.loop && !x.hasLooseBVars then
        unless out.contains x do out := out.push x
      else
        match x with
        | .app f a => todo := (todo.push a).push f
        | .lam _ t b _ => todo := (todo.push b).push t
        | .forallE _ t b _ => todo := (todo.push b).push t
        | .letE _ t v b _ => todo := ((todo.push b).push v).push t
        | .mdata _ b => todo := todo.push b
        | .proj _ _ b => todo := todo.push b
        | _ => pure ()
    return out)

/-- the first `c ||| x` / `x ||| c` of `e` with `c` a nonzero numeral: `(c, x)` -/
partial def natVal? (e : Lean.Expr) : Option Nat :=
  match e.nat? with
  | some n => some n
  | none =>
    if e.isAppOfArity ``HAdd.hAdd 6 then (·+·) <$> natVal? (e.getArg! 4) <*> natVal? (e.getArg! 5)
    else if e.isAppOfArity ``HMul.hMul 6 then (·*·) <$> natVal? (e.getArg! 4) <*> natVal? (e.getArg! 5)
    else if e.isAppOfArity ``HPow.hPow 6 then (·^·) <$> natVal? (e.getArg! 4) <*> natVal? (e.getArg! 5)
    else none

def orLit? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Nat × Bool) :=
  let lit (a : Lean.Expr) := match natVal? a with | some n => n != 0 | none => false
  let hit := e.find? fun x => x.isAppOfArity ``HOr.hOr 6 && (lit (x.getArg! 4) || lit (x.getArg! 5))
  hit.bind fun x =>
    if lit (x.getArg! 4) then (natVal? (x.getArg! 4)).map (x.getArg! 4, x.getArg! 5, ·, false)
    else (natVal? (x.getArg! 5)).map (x.getArg! 5, x.getArg! 4, ·, true)

/-- `ved_or_lit`: rewrite `c ||| x` (`c` a numeral, `x` below `c`'s lowest set bit) as `c + x` -/
elab "ved_or_lit" : tactic => do
  let mut n := 0
  while n < 64 do
    n := n + 1
    let some (c, x, cv, swapped) := orLit? (← instantiateMVars (← getMainTarget)) | break
    let mut w := 0
    while cv % 2 ^ (w + 1) == 0 do w := w + 1
    let cs ← Term.exprToSyntax c
    let xs ← Term.exprToSyntax x
    let ws := Syntax.mkNumLit (toString w)
    try
      if swapped then
        evalTactic (← `(tactic| rw [Nat.or_comm $xs $cs, Tools.VedU1Lemmas.or_hi $cs $xs $ws (by omega) (by omega)]))
      else
        evalTactic (← `(tactic| rw [Tools.VedU1Lemmas.or_hi $cs $xs $ws (by omega) (by omega)]))
    catch _ => break

/-- `i`-th component of a right-nested product value -/
partial def compProj (e : Lean.Expr) (i : Nat) : MetaM Lean.Expr := do
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
  | _ => return []

/-- bit width of a state component (`Bool` is one bit) -/
def compWidth (ty : Lean.Expr) : MetaM (Option Nat) := do
  match (← whnfR ty).getAppFnArgs with
  | (``Bool, _) => return some 1
  | (``BitVec, #[w]) => return (← instantiateMVars w).nat?
  | _ => return none

/-- match the state's components to the module's registers `(name, width)` by width, in
order (greedy; the kernel checks the choice): the `i`-th component's register -/
def matchRegs (widths : List (Option Nat)) (regs : List (String × Nat)) : Option (List String) := Id.run do
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
  let some L := loops[0]? | throwError "ved_loop_R: no Signal.loop in the goal"
  let ms ← getMVars tgt
  let mut rId? : Option MVarId := none
  for m in ms do
    if (← m.getTag).eraseMacroScopes == `R then rId? := some m
  let some rId := rId? | throwError "ved_loop_R: no invariant mvar ?R in the goal"
  let regs := (ns.getElems.map (·.getString)).toList.zip (ws.getElems.map (·.getNat)).toList
  let some α := L.getAppArgs[1]? | throwError "ved_loop_R: malformed Signal.loop"
  let comps ← stateComps α
  let widths ← comps.mapM fun c => compWidth c
  let some names := matchRegs widths regs
    | throwError "ved_loop_R: the state components {widths} do not match the module registers {regs}"
  forallTelescope (← inferType (mkMVar rId)) fun xs _ => do
    unless xs.size == 3 do throwError "ved_loop_R: unexpected invariant type"
    let L' := L.replaceFVar insE xs[0]!
    let lv ← mkAppM ``Sparkle.Core.Signal.Signal.val #[L', xs[1]!]
    let mut conj : Option Lean.Expr := none
    for i in (List.range names.length).reverse do
      let c ← compToNat (← compProj lv i)
      let eq ← mkEq (mkApp xs[2]! (mkStrLit names[i]!)) c
      conj := some (match conj with | none => eq | some r => mkAnd eq r)
    let some body := conj | throwError "ved_loop_R: no registers"
    rId.assign (← mkLambdaFVars xs body)

/-- `ved_loop_unfold t`: rewrite `(Signal.loop F).val t` by the fixpoint equation -/
macro "ved_loop_unfold " t:term : tactic =>
  `(tactic| (rw [Tools.VedU1Loop.loop_val_unfold _ ?h0 ?hS $t]
             case h0 => intro _ _; rfl
             case hS => intro s1 s2 t h; simp only [h]))

/-- `ved_loop_gen ins s X`: generalise the loop state `(Signal.loop F).val s` (the loop found in
the goal or hypotheses) to the variable `X`, everywhere -/
elab "ved_loop_gen " s:ident " [" xs:ident,* "]" : tactic => withMainContext do
  let sE ← elabTerm s.raw none
  let g ← getMainGoal
  let mut tgt ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    unless d.isImplementationDetail do tgt := mkApp tgt (← instantiateMVars d.type)
  let some L := (loopsOf tgt)[0]? | throwError "ved_loop_gen: no Signal.loop in the goal"
  let v ← mkAppM ``Sparkle.Core.Signal.Signal.val #[L, sE]
  let vs ← Term.exprToSyntax v
  let X := mkIdent `ved_X
  evalTactic (← `(tactic| generalize $vs = $X at *))
  let pats ← xs.getElems.mapM fun x => `(Lean.Parser.Tactic.rcasesPatLo| $x:ident)
  evalTactic (← `(tactic| rcases $X:ident with ⟨$pats,*⟩))
  -- a `Bool` component is split into its two values
  for x in xs.getElems do
    let some d := (← withMainContext getLCtx).findFromUserName? x.getId | continue
    if (← whnfR d.type).isConstOf ``Bool then
      evalTactic (← `(tactic| all_goals cases $x:ident))

end Tools.VedU1Loop
