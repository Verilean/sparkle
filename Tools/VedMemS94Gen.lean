import Lean
import Tools.VedMemLoop

/-!
# The loop generalisation once, before the goal split (`ved.mem.s94GenOnce`)

Observed (sparkle-ved-mem-s94, thirteenth unit): `ved_loop_gen_mem s` (Tools/VedMemLoop.lean), run after stamp 100 on the 177 goals of R033,
generalises each of the 7 loops' states `(Signal.loop F).val s` goal by goal (revert, `rcases` of the state tuple) and splits every
`Bool` component by `cases`: 1 goal becomes 512, the scan for loops that no longer occur costs most of the time.  At the stamps 94/95
the goal is ONE goal in which the loops are shared (the case split is `refine ⟨_, _, _, ⟨rfl, rfl, rfl⟩, ?_⟩` and `And.intro`, later the peel).

`ved_loop_gen_once s` (on the one goal): every loop whose value `(loop).val s` occurs in the target or a hypothesis is generalised
(`generalizeDag`) and the state tuple is taken apart (`rcases`), as `ved_loop_gen_mem` does, but the `Bool` components are NOT split.
`ved_loop_gen_resid s` (where `ved_loop_gen_mem s` stood): one scan, shared over the goals by the types, of the targets and hypotheses of all goals for
`(loop).val s`; if none is left, nothing is done, otherwise the old `ved_loop_gen_mem s` runs (the fallback).
-/

namespace Tools.VedMemS94Gen

open Lean Meta Elab Tactic Tools.VedMemLoop Tools.VedU1WireShare Sparkle.Core.Signal

register_option ved.mem.s94GenOnce : Bool := {
  defValue := false
  descr := "ved memory loop: generalise the loop states once on the shared goal (stamp 95), without Bool case splits; the per-goal ved_loop_gen_mem is the fallback (default false)"
}

/-- test seams / counters (CloseCheck) -/
initialize genOnceHits : IO.Ref Nat ← IO.mkRef 0
initialize genOnceRefuse : IO.Ref Bool ← IO.mkRef false
initialize genOnceFailLate : IO.Ref Bool ← IO.mkRef false
/-- number of times the residual scan found nothing left (the old tactic skipped) / something left (the old tactic ran) -/
initialize genResidClean : IO.Ref Nat ← IO.mkRef 0
initialize genResidLeft : IO.Ref Nat ← IO.mkRef 0

/-- the occurrences of the loop value of `v` (`Signal.val` of the same loop at the same cycle, the type argument may be spelled differently) -/
def isLoopVal (v : Expr) (e : Expr) : Bool :=
  e == v || (e.isAppOfArity ``Signal.val 4 && e.getArg! 2 == v.getArg! 2 && e.getArg! 3 == v.getArg! 3)

/-- the goal with `v` generalised to a new variable `X` KEEPING the equation `hX : v = X` (the hypotheses that mention `v` are put back into the goal and
introduced again with their names, as `generalizeDag` does); returns the new main goal -/
def generalizeKeep (g : MVarId) (v : Expr) (X hX : Name) : MetaM MVarId := g.withContext do
  let mut rev : Array FVarId := #[]
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      if (← instantiateMVars d.type).find? (isLoopVal v) |>.isSome then rev := rev.push d.fvarId
  let (fvs, g1) ← g.revert rev (preserveOrder := true)
  g1.withContext do
    let tgt ← instantiateMVars (← g1.getType)
    let ty ← inferType v
    let newTy ← withLocalDeclD X ty fun xv => do
      let eqT ← mkEq v xv
      withLocalDeclD hX eqT fun hv =>
        mkForallFVars #[xv, hv] (tgt.replace fun e => if isLoopVal v e then some xv else none)
    let g2 ← mkFreshExprMVar newTy
    g1.assign (mkApp2 g2 v (← mkEqRefl v))
    let (_, g3) ← g2.mvarId!.intro X
    let (_, g4) ← g3.intro hX
    let (_, g5) ← g4.introNP fvs.size
    return g5

/-- in `g`, every occurrence of `v` (target and the hypotheses other than `keep`) is replaced by `r` with the proof `h : v = r` (`congrArg` over the target; the hypotheses
that mention `v` are reverted and introduced again).  `has` is the (memoised) test for a type -/
def replaceByEq (g : MVarId) (v r h : Expr) (keep : Array FVarId) (has : Expr → MetaM Bool) : MetaM MVarId := g.withContext do
  let mut rev : Array FVarId := #[]
  for d in ← getLCtx do
    unless d.isImplementationDetail || keep.contains d.fvarId do
      if ← has d.type then rev := rev.push d.fvarId
  let (fvs, g1) ← g.revert rev (preserveOrder := true)
  g1.withContext do
    let tgt ← instantiateMVars (← g1.getType)
    unless ← has tgt do
      let (_, g2) ← g1.introNP fvs.size
      return g2
    let newTgt := tgt.replace fun e => if isLoopVal v e then some r else none
    let xTy ← inferType v
    let motive ← withLocalDeclD `ved_y xTy fun y => mkLambdaFVars #[y] (tgt.replace fun e => if isLoopVal v e then some y else none)
    let pf ← mkCongrArg motive h
    let g2 ← g1.replaceTargetEq newTgt pf
    let (_, g3) ← g2.introNP fvs.size
    return g3

/-- `ved_loop_gen_once s`: see the module comment.  Fails (the caller's `first` restores the state) unless there is exactly one goal and
at least one loop value is generalised.  Every generalisation keeps its equation `ved_hX<j> : (loop).val s = (tuple)`, which `ved_loop_gen_resid` uses for the
loop values that appear later (the stage-99 simp). -/
elab "ved_loop_gen_once " s:ident : tactic => withMainContext do
  let gs ← getGoals
  unless gs.length == 1 do throwError "ved_loop_gen_once: {gs.length} goals"
  if (← genOnceRefuse.get) then throwError "ved_loop_gen_once: refused (test seam)"
  let sE ← elabTerm s.raw none
  let loops ← goalLoops (← getMainGoal)
  let mut done := 0
  for j in [0:loops.size] do
    let g ← getMainGoal
    unless (← hasValAt g loops[j]! sE) do continue
    let some α := loops[j]!.getAppArgs[1]? | throwError "ved_loop_gen_once: malformed Signal.loop"
    let bare := !(← whnfR α).isAppOf ``Prod
    let n := (← Tools.VedU1Loop.stateComps α).length
    let X := mkIdent (Name.mkSimple s!"ved_X{j}")
    let xs := (List.range (if bare then 1 else n + 1)).toArray.map fun i => mkIdent (Name.mkSimple s!"ved_x{j}_{i}")
    let pats ← xs.mapM fun x => `(Lean.Parser.Tactic.rcasesPatLo| $x:ident)
    let v ← g.withContext <| mkAppM ``Sparkle.Core.Signal.Signal.val #[loops[j]!, sE]
    let g' ← generalizeKeep g v (if bare then Name.mkSimple s!"ved_x{j}_0" else X.getId) (Name.mkSimple s!"ved_hX{j}")
    replaceMainGoal [g']
    unless bare do evalTactic (← `(tactic| rcases $X:ident with ⟨$pats,*⟩))
    done := done + 1
  if done == 0 then throwError "ved_loop_gen_once: no loop value to generalise"
  if (← genOnceFailLate.get) then throwError "ved_loop_gen_once: late failure (test seam)"
  genOnceHits.modify (· + 1)
  dbgLog s!"gen_once: {done} of {loops.size} loops generalised"

/-- `ved_loop_gen_resid s`: the loop values `(loop).val s` that appeared after `ved_loop_gen_once` (the stage-99 simp) are replaced, in each goal that has one, by the tuple of the
equation `ved_hX<j>` of that loop (no `rcases`, no `Bool` split, no scan of absent loops: one memoised scan per distinct type).  A loop value without such an
equation: the old `ved_loop_gen_mem s` for the rest (the fallback). -/
elab "ved_loop_gen_resid " s:ident : tactic => withMainContext do
  let sE ← elabTerm s.raw none
  let isV := fun (e : Expr) => e.isAppOfArity ``Signal.val 4 && (e.getArg! 2).isAppOfArity ``Signal.loop 4 && e.getArg! 3 == sE
  -- the equations of the first goal's context (shared by all goals): (v, tuple, proof, fvarId)
  let some g0 := (← getGoals).head? | return
  let eqs : Array (Expr × Expr × Expr × FVarId) ← g0.withContext do
    let mut acc : Array (Expr × Expr × Expr × FVarId) := #[]
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        if d.userName.toString.startsWith "ved_hX" then
          if let some (_, l, r) := (← instantiateMVars d.type).eq? then
            if isV l then acc := acc.push (l, r, d.toExpr, d.fvarId)
    pure acc
  let memo ← IO.mkRef (({} : Std.HashMap (Expr × Expr) Bool))
  let hasV (v : Expr) (e : Expr) : MetaM Bool := do
    let e ← instantiateMVars e
    if let some r := (← memo.get)[(v, e)]? then return r
    let r := !(collectDag (isLoopVal v) e).isEmpty
    memo.modify (·.insert (v, e) r)
    return r
  let keep := eqs.map (·.2.2.2)
  let mut out : List MVarId := []
  let mut other := false
  let mut replaced := 0
  for g in ← getGoals do
    let mut cur := g
    for (v, r, h, _) in eqs do
      let tgt ← cur.withContext do instantiateMVars (← cur.getType)
      let any ← cur.withContext do
        if ← hasV v tgt then pure true else
        let mut f := false
        for d in ← getLCtx do
          unless d.isImplementationDetail || keep.contains d.fvarId do
            if !f && (← hasV v d.type) then f := true
        pure f
      if any then
        cur ← replaceByEq cur v r h keep (hasV v)
        replaced := replaced + 1
    -- a loop value of a loop without an equation
    let left ← cur.withContext do
      let mut f := false
      let t ← instantiateMVars (← cur.getType)
      if !(collectDag isV t).isEmpty then f := true
      for d in ← getLCtx do
        unless f || d.isImplementationDetail || keep.contains d.fvarId do
          if !(collectDag isV (← instantiateMVars d.type)).isEmpty then f := true
      pure f
    if left then other := true
    -- the kept equations are used up: the old path has none (the later stages, e.g. `ved_mem_addr`'s `omega`/`simp`, see every hypothesis)
    cur ← cur.tryClearMany keep
    out := out ++ [cur]
  setGoals out
  if other then
    genResidLeft.modify (· + 1)
    dbgLog s!"gen_resid: {replaced} replacements; loop values without an equation left, ved_loop_gen_mem"
    evalTactic (← `(tactic| ved_loop_gen_mem $s))
  else
    genResidClean.modify (· + 1)
    dbgLog s!"gen_resid: {replaced} replacements, no loop value left"

/-! ## Two spellings of one loop (`ved_loop_canon`, option `ved.mem.s94Local`)

Observed (s94r, `#ved_s95_loops` on the stage-95 checkpoint goal of R033): the goal has 8 distinct loop values `(loop).val s`, and 4 PAIRS of them are one loop
(`isDefEq` at reducible transparency for 3 pairs, at default transparency for the 4th); the second spelling occurs only in the target (the declared state) and in the
memory write ports, the hypotheses (wire facts) only mention the first.  `ved_loop_gen_once` / `ved_loop_gen_mem` generalise each spelling to its own state tuple, so
the relation "the second tuple is the first" is lost: the register-update goals then mention fields (s94r goal 0: `ck277 ck276 ck275`) that no hypothesis mentions.
`ved_loop_canon` replaces every loop (target and hypotheses) that is `isDefEq` to an earlier loop of the same state type by that loop (`replaceTargetDefEq` /
`replaceLocalDeclDefEq`, the replacement by `Expr.replace` with its pointer cache), before the generalisation. -/

/-- counters / test seams (CloseCheck) -/
initialize canonHits : IO.Ref Nat ← IO.mkRef 0
initialize canonRefuse : IO.Ref Bool ← IO.mkRef false
/-- the heartbeat limit (thousands) of one default-transparency comparison of two loops -/
def canonHbK : Nat := 4000

/-- the pairs (loop, earlier loop it is `isDefEq` to) among `loops`; the comparison is only made between loops of the same (reducibly defeq) state type -/
def loopCanonPairs (loops : Array Expr) : MetaM (Array (Expr × Expr)) := do
  let mut reps : Array Expr := #[]
  let mut out : Array (Expr × Expr) := #[]
  for l in loops do
    let mut found := false
    for r in reps do
      if found then break
      let some a := l.getAppArgs[1]? | continue
      let some b := r.getAppArgs[1]? | continue
      unless a == b || (← withReducible (isDefEq a b)) do continue
      if l == r then continue
      let same ← do
        if ← withReducible (isDefEq l r) then pure true
        else
          let st ← saveState
          let hb0 ← IO.getNumHeartbeats
          let ok ← tryCatchRuntimeEx
            (withTheReader Core.Context (fun c => { c with maxHeartbeats := canonHbK * 1000, initHeartbeats := hb0 }) (isDefEq l r))
            (fun _ => pure false)
          unless ok do st.restore
          pure ok
      if same then
        out := out.push (l, r)
        found := true
    unless found do reps := reps.push l
  return out

/-- `ved_loop_canon`: see the section comment.  Fails (so that `try` leaves the goal) when no loop is replaced. -/
elab "ved_loop_canon" : tactic => withMainContext do
  if (← canonRefuse.get) then throwError "ved_loop_canon: refused (test seam)"
  let g0 ← getMainGoal
  let loops ← goalLoops g0
  let pairs ← loopCanonPairs loops
  if pairs.isEmpty then throwError "ved_loop_canon: no two loops are the same loop"
  let map : Std.HashMap Expr Expr := pairs.foldl (fun m (l, r) => m.insert l r) {}
  let f := fun (e : Expr) => if e.isAppOfArity ``Signal.loop 4 then map[e]? else none
  let mut g := g0
  let tgt ← instantiateMVars (← g.getType)
  let tgt' := tgt.replace f
  if tgt' != tgt then g ← g.replaceTargetDefEq tgt'
  for d in ← g0.withContext getLCtx do
    unless d.isImplementationDetail do
      let t ← instantiateMVars d.type
      let t' := t.replace f
      if t' != t then g ← g.replaceLocalDeclDefEq d.fvarId t'
  canonHits.modify (· + pairs.size)
  dbgLog s!"loop_canon: {pairs.size} loops replaced by an earlier one"
  replaceMainGoal [g]

end Tools.VedMemS94Gen
