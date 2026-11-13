/-
  Bundle `unsolved` of the U1 coverage work: which generated script a module's registers call for.

  The single-register script (`scriptFor`, `some (r, w)`) unfolds `Signal.register`; a declaration
  built by `circuit do` (`Signal.reg`) is a `Signal.loop` even with ONE register, and needs the
  loop script (`loopScriptFor`).  Untrusted routing only: the kernel checks whatever script runs.
-/
import Lean
import Sparkle.IR.ReorderInvariance
import Tools.VedU1Loop
import Std.Data.HashSet

namespace Tools.VedU1Uns
open Lean

/-- Does the declaration `decl`, or one of the helper definitions its body mentions, mention
`Signal.loop`? -/
def usesLoop (decl : Name) (helpers : Array Name) : CoreM Bool := do
  let env ← getEnv
  for n in #[decl] ++ helpers do
    if let some (.defnInfo di) := env.find? n then
      if di.value.getUsedConstants.contains `Sparkle.Core.Signal.Signal.loop then return true
  return false


open Sparkle.IR.AST in
/-- the module INPUT names in the combinational cone of each register's next-state input (wires are
followed through their assignments; a register output ends the cone), sorted -/
def regSupports (m : Sparkle.IR.AST.Module) : List (String × List String) :=
  let assigns : List (String × List String) :=
    m.body.filterMap fun | .assign l r => some (l, Sparkle.IR.Reorder.refsOf r) | _ => none
  let inputs := m.inputs.map (·.name)
  let cone (start : List String) : List String := Id.run do
    let mut names : List String := start.eraseDups
    for _ in [0:m.body.length + 1] do
      let more := names.flatMap fun n => match assigns.lookup n with | some rs => rs | none => []
      let names' := (names ++ more).eraseDups
      if names'.length == names.length then break
      names := names'
    return names
  m.body.filterMap fun
    | .register o _ _ i _ =>
      let ins := (cone (Sparkle.IR.Reorder.refsOf i)).filter (inputs.contains ·)
      some (o, (ins.toArray.qsort (· < ·)).toList)
    | _ => none

/-- the names `n` with an application `ins _ "n"` in `e` (every distinct subterm once) -/
partial def insNamesOf (insE e : Expr) : Array String :=
  let rec go (e : Expr) : StateM (Std.HashSet Expr × Array String) Unit := do
    if (← get).1.contains e then return
    modify fun (v, a) => (v.insert e, a)
    -- another loop's own inputs are not this component's (the module's cone ends at register outputs)
    if e.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then return
    match e with
    | .app f a =>
      if e.getAppFn == insE then
        match e.getAppArgs.back? with
        | some (.lit (.strVal n)) => modify fun (v, a) => (v, if a.contains n then a else a.push n)
        | _ => pure ()
      go f; go a
    | .lam _ t b _ => go t; go b
    | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()
  ((go e).run (({} : Std.HashSet Expr), (#[] : Array String))).2.2


open Lean Elab Tactic Meta Tools.VedU1Loop

/-- the input names read by each component of the loop's next state (`none`: the body is not an
explicit tuple of components) -/
def loopCompSupports (insE L : Expr) : MetaM (Option (List (List String))) := do
  let some F := L.getAppArgs[3]? | return none
  let F ← instantiateMVars F
  unless F.isLambda do return none
  lambdaTelescope F fun xs B => do
    unless xs.size == 1 do return none
    withLocalDeclD `t (mkConst ``Nat) fun t => do
      let v ← if B.isAppOf ``Sparkle.Core.Signal.Signal.mk then pure (B.appArg!.headBeta.beta #[t])
        else whnfCore (← mkAppM ``Sparkle.Core.Signal.Signal.val #[B, t])
      let sup (e : Expr) : List String := ((insNamesOf insE e).qsort (· < ·)).toList
      let mut out : List (List String) := []
      let mut cur := v
      for _ in [0:64] do
        match cur.getAppFnArgs with
        | (``Prod.mk, #[_, _, a, b]) => out := out ++ [sup a]; cur ← whnfCore b
        | _ => break
      if out.isEmpty then
        -- a bare (non-tuple) state
        return some [sup v]
      return some out

/-- components to registers: the same width and the same input support, in order; none when some
component has no such register or a register is left over -/
def matchRegsSupp (comps : List (Option Nat × List String))
    (regs : List (String × Nat × List String)) : Option (List String) := Id.run do
  let mut avail := regs
  let mut out : List String := []
  for (w, sp) in comps do
    let some w := w | return none
    match avail.find? (fun r => r.2.1 == w && r.2.2 == sp) with
    | some r => out := out ++ [r.1]; avail := avail.erase r
    | none => return none
  return (if avail.isEmpty then some out else none)

/-- `ved_loop_R ins [names] widths ; supports`: as `ved_loop_R`, but the components are matched to
the registers by width AND input support first (a module with two counters of one width whose
registers the synthesizer numbered in another order than the loops' components); the position/width
matching of `ved_loop_R` is the fallback.  `supports` are the registers' input names, `,`-joined. -/
elab "ved_loop_R2 " ins:ident " [" ns:str,* "]" ws:num,* " ; " ss:str,* : tactic => withMainContext do
  let insE ← elabTerm ins.raw none
  let g ← getMainGoal
  let mut tgt ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    unless d.isImplementationDetail do tgt := mkApp tgt (← instantiateMVars d.type)
  let loops := loopsOf tgt
  if loops.isEmpty then throwError "ved_loop_R: no Signal.loop in the goal"
  let ms ← getMVars tgt
  let mut rId? : Option MVarId := none
  for m in ms do
    if (← m.getTag).eraseMacroScopes == `R then rId? := some m
  let some rId := rId? | throwError "ved_loop_R: no invariant mvar ?R in the goal"
  let regs := (ns.getElems.map (·.getString)).toList.zip (ws.getElems.map (·.getNat)).toList
  let sups := (ss.getElems.map fun x => (x.getString.splitOn ",").filter (· ≠ "")).toList
  let mut compsOf : Array (List Expr) := #[]
  let mut compSup : List (List String) := []
  let mut supOk := true
  for L in loops do
    let some α := L.getAppArgs[1]? | throwError "ved_loop_R: malformed Signal.loop"
    let cs ← stateComps α
    compsOf := compsOf.push cs
    match ← loopCompSupports insE L with
    | some sp => if sp.length == cs.length then compSup := compSup ++ sp else supOk := false
    | none => supOk := false
  let widths ← (compsOf.toList.flatten).mapM fun c => compWidth c
  let regsS := regs.zip sups |>.map fun ((n, w), sp) => (n, w, sp)
  let viaSupp := if supOk && sups.length == regs.length then matchRegsSupp (widths.zip compSup) regsS else none
  let some names := viaSupp <|> matchRegs widths regs
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

end Tools.VedU1Uns
