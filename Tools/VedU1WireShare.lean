import Lean
import Tools.VedU1Loop
import Tools.VedU1Wire

/-!
# Sharing-preserving steps of the single-register loop script (U1)

`Tools/VedU1Loop.lean` / `Tools/VedU1Entry.lean` read the loop of a declaration whose body repeats its argument
(a chain of `crc8Step` / `crc32Step`: every step uses its argument several times, the unfolded term is a DAG
whose tree is exponential in the number of steps).  The tactics there (`rw`, `generalize`, `loopsOf`) visit a term as
a tree, or let `isDefEq` unfold a large candidate; on such a goal they do not finish.  The tactics here do the same
steps by walks that memoise on the shared subterms (UNTRUSTED: the kernel checks the proof that results).

The size threshold `shareMinTree` applies only to the bit / packing steps (`ved_bit_simp_share`, the choice between
`ved_wire` and `ved_pack_simp` in `ved_pack_wire_all`): there a goal whose tree has fewer nodes keeps the original
tactic.  `ved_loop_unfold_share` and `ved_loop_gen_share` replace `ved_loop_unfold` / `ved_loop_gen` for every goal
(`ved_loop_gen_share` falls back to the original only when it finds no loop).
-/

namespace Tools.VedU1WireShare

open Lean Meta Elab Tactic Sparkle.Core.Signal

/-- the distinct subterms of `e` (each once, shared subterms visited once) that satisfy `p` -/
partial def collectDag (p : Expr → Bool) (e : Expr) : Array Expr := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut out : Array Expr := #[]
  let mut todo : Array Expr := #[e]
  while !todo.isEmpty do
    let x := todo.back!
    todo := todo.pop
    if seen.contains x then continue
    seen := seen.insert x
    if !x.hasLooseBVars && p x then out := out.push x
    match x with
    | .app f a => todo := (todo.push a).push f
    | .lam _ t b _ => todo := (todo.push b).push t
    | .forallE _ t b _ => todo := (todo.push b).push t
    | .letE _ t v b _ => todo := ((todo.push b).push v).push t
    | .mdata _ b => todo := todo.push b
    | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return out

/-- the `Signal.loop` terms of `e`, each once, without reading `e` as a tree (`Tools.VedU1Loop.loopsOf` order is
that of a tree walk; the order here is the order of a walk that visits each shared subterm once) -/
def loopsDag (e : Expr) : Array Expr :=
  collectDag (·.isAppOfArity ``Signal.loop 4) e

/-- run `tac` on the goal `m` and require that it closes it -/
def runSub (m : MVarId) (tac : TSyntax `tactic) : TacticM Unit := do
  let saved ← getGoals
  setGoals [m]
  evalTactic tac
  unless (← getGoals).isEmpty do throwError "ved_loop_unfold_share: a side condition is left open"
  setGoals saved

/-- `ved_loop_unfold_share t`: `ved_loop_unfold t` (rewrite `(Signal.loop F).val t` by the fixpoint equation of
`Signal.loop`, for every loop whose value at `t` occurs in the goal) on a goal that is read as a DAG: the
occurrences are found and replaced by a walk over the shared subterms, with no unification against the
candidates (the original `rw` tries every `Signal.val _ (s+1)` node of the unfolded body against the pattern,
and that unification unfolds the node) -/
elab "ved_loop_unfold_share " t:term : tactic => withMainContext do
  let tgt0 ← instantiateMVars (← getMainTarget)
  let tE ← instantiateMVars (← Term.elabTerm t (some (mkConst ``Nat)))
  let tE ← instantiateMVars tE
  let _ := tE
  let isOcc0 := fun (x : Expr) =>
    x.isAppOfArity ``Signal.val 4 && (x.getArg! 2).isAppOfArity ``Signal.loop 4
  -- the loops whose value is read at the cycle `t` (the cycle terms are small: unified)
  let occs := fun (e : Expr) => do
    let mut out : Array Expr := #[]
    for x in collectDag isOcc0 e do
      if x.getArg! 3 == tE || (← withReducible <| isDefEq (x.getArg! 3) tE) then out := out.push x
    pure out
  if (← occs tgt0).isEmpty then
    evalTactic (← `(tactic| ved_loop_unfold $t))
    return
  for _ in [0:64] do
    let tgt ← instantiateMVars (← getMainTarget)
    let some lhs := (← occs tgt)[0]? | break
    let L := lhs.getArg! 2
    -- `loop_val_unfold F h0 hS t`, the side conditions proved about the body only
    let f4 := mkApp4 (mkConst ``Tools.VedU1Loop.loop_val_unfold) (L.getArg! 0) (L.getArg! 1) (L.getArg! 2) (L.getArg! 3)
    let ty ← whnf (← inferType f4)
    let h0T := ty.bindingDomain!
    let h0 ← mkFreshExprMVar h0T
    let ty ← whnf (ty.bindingBody!.instantiate1 h0)
    let hS ← mkFreshExprMVar ty.bindingDomain!
    runSub h0.mvarId! (← `(tactic| (intro _ _; rfl)))
    runSub hS.mvarId! (← `(tactic| (intro s1 s2 t h; simp only [h])))
    let lem ← instantiateMVars (mkApp3 f4 h0 hS (lhs.getArg! 3))
    let eqTy ← instantiateMVars (← inferType lem)
    let some (_, l, r) := eqTy.eq? | throwError "ved_loop_unfold_share: unexpected equation {eqTy}"
    unless l == lhs do throwError "ved_loop_unfold_share: the occurrence is not the left side of the equation"
    let xTy ← inferType lhs
    let motive ← withLocalDeclD `ved_x xTy fun xv =>
      mkLambdaFVars #[xv] (tgt.replace fun e => if e == lhs then some xv else none)
    let pf ← mkCongrArg motive lem
    let newTgt := tgt.replace fun e => if e == lhs then some r else none
    let g ← getMainGoal
    let g' ← g.replaceTargetEq newTgt pf
    replaceMainGoal [g']
/-- generalise the term `v` of the main goal (and of the hypotheses that mention it, put back into the goal and
introduced again with their names) to a new variable `x`, by replacement over the shared subterms -/
def generalizeDag (v : Expr) (x : Name) : TacticM Unit := do
  -- the occurrences of `v`: the same signal read at the same cycle (the type argument of `Signal.val` can be
  -- a different, definitionally equal, spelling of the state type: `HList [BitVec 8]` / `BitVec 8 × HList []`)
  let isV := fun (e : Expr) =>
    e == v || (e.isAppOfArity ``Signal.val 4 && e.getArg! 2 == v.getArg! 2 && e.getArg! 3 == v.getArg! 3)
  let g ← getMainGoal
  g.withContext do
    let mut rev : Array FVarId := #[]
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        if (← instantiateMVars d.type).find? isV |>.isSome then rev := rev.push d.fvarId
    let (fvs, g1) ← g.revert rev (preserveOrder := true)
    g1.withContext do
      let tgt ← instantiateMVars (← g1.getType)
      let ty ← inferType v
      let newTy ← withLocalDeclD x ty fun xv =>
        mkForallFVars #[xv] (tgt.replace fun e => if isV e then some xv else none)
      let g2 ← mkFreshExprMVar newTy
      g1.assign (mkApp g2 v)
      let (_, g3) ← g2.mvarId!.intro x
      let (_, g4) ← g3.introNP fvs.size
      replaceMainGoal [g4]

/-- `ved_loop_gen_share s`: `ved_loop_gen s` (generalise the state `(Signal.loop F).val s` of every loop of the goal
or hypotheses to variables, take the tuple apart, split the `Bool` components) with the loops found and the
generalisation done by walks over the shared subterms; the original tactic when no loop is found this way -/
elab "ved_loop_gen_share " s:ident : tactic => withMainContext do
  let sE ← elabTerm s.raw none
  let g ← getMainGoal
  let mut tgt ← instantiateMVars (← g.getType)
  let mut loops := loopsDag tgt
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      for l in loopsDag (← instantiateMVars d.type) do
        unless loops.contains l do loops := loops.push l
  if loops.isEmpty then
    evalTactic (← `(tactic| ved_loop_gen $s))
    return
  for j in [0:loops.size] do
    let v ← mkAppM ``Sparkle.Core.Signal.Signal.val #[loops[j]!, sE]
    let X := mkIdent (Name.mkSimple s!"ved_X{j}")
    let some α := loops[j]!.getAppArgs[1]? | throwError "ved_loop_gen_share: malformed Signal.loop"
    let bare := !(← whnfR α).isAppOf ``Prod
    -- in every goal (the `Bool` components of an earlier loop were split into goals)
    let gs ← getGoals
    let mut gsOut : List MVarId := []
    for g in gs do
      setGoals [g]
      generalizeDag v (if bare then Name.mkSimple s!"ved_x{j}_0" else X.getId)
      gsOut := gsOut ++ (← getGoals)
    setGoals gsOut
    let n := (← Tools.VedU1Loop.stateComps α).length
    let xs := (List.range (if bare then 1 else n + 1)).toArray.map fun i => mkIdent (Name.mkSimple s!"ved_x{j}_{i}")
    let pats ← xs.mapM fun x => `(Lean.Parser.Tactic.rcasesPatLo| $x:ident)
    if bare then pure ()
    else evalTactic (← `(tactic| all_goals rcases $X:ident with ⟨$pats,*⟩))
    for x in xs do
      let some d := (← withMainContext getLCtx).findFromUserName? x.getId | continue
      if (← whnfR d.type).isConstOf ``Bool then
        evalTactic (← `(tactic| all_goals cases $x:ident))

/-- `ved_bit_simp_share`: `try ved_bit_simp`, except on a goal that `ved_wire` takes (read as a tree it has at least
`shareMinTree` nodes) and that has bit operations: `ved_bit_simp` closes the side conditions of its rewrite rules by
`omega`, which reads such a goal as a tree, and `ved_wire` rewrites the bit operations of its wires itself -/
elab "ved_bit_simp_share" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  if Tools.VedU1Loop.treeSizeVal tgt ≥ Tools.VedU1Loop.shareMinTree
      && (Tools.VedU1Loop.natBitOps tgt).size ≥ Tools.VedU1Loop.bitsMinOps then
    return
  evalTactic (← `(tactic| try ved_bit_simp))

/-- `ved_pack_wire_all`: `all_goals ved_pack_wire`, where the failure of the step on a goal is the failure of the tactic
(`all_goals` recovers from the error of its argument and leaves the goal, and the closing steps that follow then run
`omega` on a goal that is read as an exponentially large tree) -/
elab "ved_pack_wire_all" : tactic => do
  let gs ← getGoals
  let mut rest : List MVarId := []
  for g in gs do
    setGoals [g]
    evalTactic (← `(tactic| ved_pack_wire))
    rest := rest ++ (← getGoals)
  setGoals rest

end Tools.VedU1WireShare
