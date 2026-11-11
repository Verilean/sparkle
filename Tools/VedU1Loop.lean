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
      Tactic.withoutRecover (evalTactic (← `(tactic| omega)))
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
