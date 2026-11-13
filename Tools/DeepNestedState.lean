/-
  The STATE meaning of the NESTED loops of a deep circuit (H2d).

  `#verify_elab_deep` exports, per port, the theorem `<port>_deep_state`:
  `∀ params u, (Signal.loop F).val u = pack u` for the circuit's top loop.  A circuit that calls a plain
  stateful function (a parser, say) has that function's `Signal.loop G` INSIDE `F`.  When `G` does not read
  the enclosing loop's state (a closed term over the parameters) its state is a fact of its own:
  `∀ params u, (Signal.loop G).val u = pack' u`, with `pack'` the readers of the IR registers the nested
  circuit was flattened to.  `exportNested` finds each such `G` in the top state theorem's statement and
  proves and adds that theorem (`<state>_n<j>`), by the proof script the caller supplies for each candidate
  register block.  Whichever candidate is proved first is kept; a loop no candidate proves is left alone (the
  checker that needs it refuses).  The theorems are added through `addDecl` (kernel-checked) and audited by
  the caller like every generated theorem.
-/
import Lean
import Sparkle.Core.Signal
import Sparkle.Core.CircuitMonad

open Lean Meta Elab Term

namespace Tools.DeepNested

/-- A candidate register block of a node: the IR registers (in pack order), the pack at the cycle `u` and the
proof of `(Signal.loop G).val u = pack` given the local `u`. -/
structure BlockCand where
  idx : Array Nat
  pack : Term
  tac : TSyntax `tactic

/-- A nested node: its slot signature and its candidate blocks. -/
structure NodeCand where
  widths : Array Nat
  isBool : Array Bool
  blocks : Array BlockCand

/-- The closed `Signal.loop` applications inside `e` (outermost first, also inside each other). -/
partial def collectLoops (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc := if e.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 && !e.hasLooseBVars && !acc.contains e
    then acc.push e else acc
  match e with
  | .app f a => collectLoops a (collectLoops f acc)
  | .lam _ t b _ => collectLoops b (collectLoops t acc)
  | .forallE _ t b _ => collectLoops b (collectLoops t acc)
  | .letE _ t v b _ => collectLoops b (collectLoops v (collectLoops t acc))
  | .mdata _ b => collectLoops b acc
  | .proj _ _ b => collectLoops b acc
  | _ => acc

/-- The closed `runCircuitH inits body` applications inside `e` (a nested circuit not yet unfolded). -/
partial def collectRC (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc := if e.isAppOfArity ``Sparkle.Core.runCircuitH 8 && !e.hasLooseBVars && !acc.contains e
    then acc.push e else acc
  match e with
  | .app f a => collectRC a (collectRC f acc)
  | .lam _ t b _ => collectRC b (collectRC t acc)
  | .forallE _ t b _ => collectRC b (collectRC t acc)
  | .letE _ t v b _ => collectRC b (collectRC v (collectRC t acc))
  | .mdata _ b => collectRC b acc
  | .proj _ _ b => collectRC b acc
  | _ => acc

/-- The loop of a `runCircuitH inits body`: `Signal.loop (loopFOf inits body)` (`runCircuitH_eq`). -/
def loopOfRC (rc : Expr) : MetaM Expr := do
  let F := mkAppN (mkConst `loopFOf rc.getAppFn.constLevels!) rc.getAppArgs
  mkAppOptM ``Sparkle.Core.Signal.Signal.loop #[none, none, some (rc.getArg! 5), some F]

/-- One slot type: `BitVec n` (width `n`) or `Bool` (width 1, Bool-ness). -/
def slotOf (a : Expr) : MetaM (Option (Nat × Bool)) := do
  if a.isConstOf ``Bool then return some (1, true)
  if a.isAppOfArity ``BitVec 1 then
    let n ← whnf (a.getArg! 0)
    let some n := n.nat? <|> n.rawNatLit? | return none
    return some (n, false)
  return none

/-- The slot signature of a loop state type, either `HList [a, b, ..]` or its unfolded product form
`a × (b × ..)`: widths (a `Bool` slot has width 1) and Bool-ness. -/
partial def stateSig (e : Expr) : MetaM (Option (Array Nat × Array Bool)) := do
  if e.isAppOfArity ``Sparkle.Core.HList 1 then
    let mut ws : Array Nat := #[]
    let mut bs : Array Bool := #[]
    let mut cur := e.getArg! 0
    repeat
      if cur.isAppOfArity ``List.cons 3 then
        let some (w, b) ← slotOf (cur.getArg! 1) | return none
        ws := ws.push w; bs := bs.push b
        cur := cur.getArg! 2
      else break
    return some (ws, bs)
  else if e.isAppOfArity ``Prod 2 then
    let some (w, b) ← slotOf (e.getArg! 0) | return none
    let some (ws, bs) ← stateSig (e.getArg! 1) | return none
    return some (#[w] ++ ws, #[b] ++ bs)
  else if e.isConstOf ``PUnit then return some (#[], #[])
  else return none

/-- The slot signature of the type `Signal dom S` of a loop. -/
def signatureOf (loopTy : Expr) : MetaM (Option (Array Nat × Array Bool)) := do
  let some st := (← whnfR loopTy).getAppArgs.back? | return none
  stateSig st

/-- Diagnostics to the file named by `SPARKLE_DEEP_TRACE` (as `#verify_elab_deep`'s own stage markers). -/
def traceTo (msg : Unit → MetaM String) : MetaM Unit := do
  if let some f ← IO.getEnv "SPARKLE_DEEP_TRACE" then
    let m ← msg ()
    IO.FS.withFile f .append fun h => h.putStrLn s!"[nested] {m}"

/-- Prove and add the nested-state theorems of `stateTh`; returns the names added. -/
def exportNested (stateTh : Name) (nodes : Array NodeCand) : TermElabM (Array Name) := do
  let env ← getEnv
  let some ci := env.find? stateTh | return #[]
  let some (.str pre last) := some stateTh | return #[]
  forallTelescope ci.type fun xs body => do
    let mut added : Array Name := #[]
    let some (_, lhs, _) := body.eq? | return added
    let some u := xs.back? | return added
    let tops := collectLoops lhs #[]
    let some top := tops[0]? | return added
    let mut loops := #[]
    for rc in collectRC lhs #[] do
      let l ← loopOfRC rc
      unless loops.contains l || l == top do loops := loops.push l
    for l in collectLoops lhs #[] do
      unless loops.contains l || l == top do loops := loops.push l
    traceTo fun _ => do pure s!"{stateTh}: {tops.size} closed loops, {loops.size} nested"
    if loops.isEmpty then traceTo fun _ => do pure ((toString (← ppExpr lhs)).take 3000).toString
    let mut j := 0
    for l in loops do
      let some (ws, bs) ← signatureOf (← inferType l)
        | do traceTo fun _ => do pure s!"loop of unreadable type {← inferType l}"
             continue
      traceTo fun _ => do pure s!"nested loop {ws} {bs}"
      let uName := (← u.fvarId!.getUserName)
      let uId : Ident := mkIdent uName
      -- every candidate block that PROVES is exported (two registers with the same recurrence both prove)
      for node in nodes do
        if node.widths != ws || node.isBool != bs then continue
        for blk in node.blocks do
          let nm := Name.str pre (last ++ s!"_n{j}")
          if (← getEnv).contains nm then
            j := j + 1
            continue
          let savedMsgs := (← getThe Core.State).messages
          try
            let L ← exprToSyntax l
            let stmt ← `(Sparkle.Core.Signal.Signal.val $L $uId = $(blk.pack))
            let tgt ← instantiateMVars (← Term.withSynthesize (Term.elabType stmt))
            let pf ← mkFreshExprMVar tgt MetavarKind.syntheticOpaque
            -- `first | _`: a failing step THROWS (the tactic framework's error recovery would log the
            -- error and close the goal with `sorry`)
            let byStx ← `(by first | $(blk.tac):tactic)
            Term.withoutErrToSorry <| Term.withSynthesize <|
              Term.runTactic pf.mvarId! byStx.raw (kind := .term)
            let pf ← instantiateMVars pf
            if pf.hasSorry then throwError "the nested state proof contains sorry"
            let ty ← mkForallFVars xs tgt
            let val ← mkLambdaFVars xs pf
            if ty.hasMVar || val.hasMVar then throwError "metavariables in the nested state theorem"
            addDecl (Declaration.thmDecl { name := nm, levelParams := [], type := ty, value := val })
            added := added.push nm
            j := j + 1
          catch e =>
            modifyThe Core.State fun st => { st with messages := savedMsgs }
            traceTo fun _ => do pure s!"block {blk.idx}: {(← e.toMessageData.toString).take 600}"
    return added

end Tools.DeepNested
