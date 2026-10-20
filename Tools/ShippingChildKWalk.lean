import Tools.ShippingChildTranslateA
-- BUILT by the integrator: kw1 exit 1 (names), kw2–kw6 (rule elaboration context, non-reducing telescope, syntax), used by FallbackA fb13 exit 0. Integrator-written (after fb1: the generic `repeat (first | exact … | kbase)` walk timed out —
-- each failed `exact` unified a lemma's program against a bind by unfolding).
-- No `sorry`, no `axiom`, no `native_decide`, no law: a TACTIC only; what it closes is a
-- kernel-checked proof from the lemmas it is given.

/-! # `kwalk`: a head-directed walk for `KeepsCP` goals

`kwalk [t₁, …, tₙ]` walks a goal `KeepsCP mctx mref cctx cref I prog` along the SYNTAX of
`prog`, choosing the rule by the head symbol of `prog` BEFORE any unification:

* `bind` → `KeepsCP.bind`; `ite`/`dite` → `KeepsCP.ite`/`dite`; `pure` → `KeepsCP.pure`;
  `throw` → `KeepsCP.throw` (the message by `okmsg`); a `match` → `split`;
  `let`/`have` and beta-redexes → reduced (`dsimp only`); `getCompilerState >>= f` →
  `KeepsCP.bindCtx`;
* a constant `c` that is the head of the conclusion's program of one of the given terms `tᵢ`
  (computed by `forallMetaTelescope` of the term's type) → `apply tᵢ`, the remaining
  goals by `assumption` (the section's `O`, `hA`, `hS`, …) or by the walk;
* a local function application (a recursive translator `rec …`, a continuation `k …`) → the
  first local hypothesis whose type ends in `KeepsCP … (rec …)`-shape, by `exact h _ …`;
* any other constant → `unfold` it once and continue (fails on recursive definitions: then
  the walk stops and leaves the goal, naming the constant).

Goals it cannot close are left to the caller. -/

namespace Tools.ShippingChildKWalk
open Lean Elab Tactic Meta

/-- The program of a `KeepsCP … I prog` (or `Keeps … I prog`) type: its last argument. -/
def progOf? (t : Lean.Expr) : Option Lean.Expr :=
  let t := t.consumeMData
  if t.isAppOf ``Tools.ShippingChildTranslateA.KeepsCP ||
      t.isAppOf ``Tools.ShippingChildInv.Keeps then
    some t.appArg!
  else none

/-- The head constant of a program (after `mdata`). -/
def headConst? (p : Lean.Expr) : Option Name :=
  p.consumeMData.getAppFn.constName?

/-- The head constant of the conclusion's program of a term's type. -/
def ruleHead (t : Lean.Expr) : MetaM (Option Name) := do
  let ty ← inferType t
  forallTelescope ty fun _ concl => do
    match progOf? concl with
    | some p => return headConst? p
    | none => return none

def runTac (stx : TSyntax `tactic) : TacticM Bool := do
  let s ← saveState
  try
    -- (no error-to-`sorry` recovery: a failed nested `by …` must fail the step; a nested
    -- `by` with unsolved goals only LOGS an error, so a new logged error also fails it)
    let n0 := (← Core.getMessageLog).toList.length
    Term.withoutErrToSorry (evalTactic stx)
    let msgs := (← Core.getMessageLog).toList.drop n0
    if msgs.any (·.severity == .error) then
      s.restore
      return false
    return true
  catch _ =>
    s.restore
    return false

/-- One step on the main goal. Returns `false` if nothing applied. -/
def kstep (rules : Array (Lean.Expr × Name × Syntax)) : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  if ty.isForall then
    return ← runTac (← `(tactic| intros))
  let some p := progOf? ty | do
    -- side goals left by a rule (`SideRef`, `LocalRefType`, a message class, a hypothesis)
    if ← runTac (← `(tactic| assumption)) then return true
    let h := ty.getAppFn.constName?.getD .anonymous
    if h == ``Tools.ShippingChildInv.SideRef || h == ``Tools.ShippingChildInv.LocalRefType then
      return ← runTac (← `(tactic| constructor))
    if h == ``Tools.ShippingChildInv.OkMsg || h == ``Tools.ShippingChildInv.OkExc then
      return ← runTac (← `(tactic| okmsg))
    return false
  let p := p.consumeMData
  if p.isLet || p.isHeadBetaTarget then
    -- reduce the head `let`/`have` (zeta) or beta-redex in place: definitionally equal, and
    -- cheap (a `dsimp only` here timed out on a large join point, fb10)
    let p' := if p.isLet then p.letBody!.instantiate1 p.letValue! else p.headBeta
    let ty' := mkApp ty.consumeMData.appFn! p'
    let g' ← g.replaceTargetDefEq ty'
    replaceMainGoal [g']
    return true
  let fn := p.getAppFn
  if (← IO.getEnv "KWALK_DEBUG").isSome then
    logInfo m!"kwalk step: head {fn}; rules {rules.map (·.2.1)}"
  match fn with
  | .const c _ =>
    if c == ``Bind.bind then
      -- `getCompilerState >>= f` (the read context carries provenance)
      if (p.getArg! 4).consumeMData.isConstOf ``Sparkle.Compiler.Elab.CompilerM.getCompilerState then
        if ← runTac (← `(tactic| refine Tools.ShippingChildTranslateA.KeepsCP.bindCtx (fun _ _ => ?_))) then
          return true
      if ty.isAppOf ``Tools.ShippingChildInv.Keeps then
        return ← runTac (← `(tactic| refine Tools.ShippingChildInv.Keeps.bind ?_ (fun _ => ?_)))
      return ← runTac (← `(tactic| refine Tools.ShippingChildTranslateA.KeepsCP.bind ?_ (fun _ => ?_)))
    if c == ``ite then
      return ← runTac (← `(tactic| refine Tools.ShippingChildTranslateA.KeepsCP.ite (fun _ => ?_) (fun _ => ?_)))
    if c == ``dite then
      return ← runTac (← `(tactic| refine Tools.ShippingChildTranslateA.KeepsCP.dite (fun _ => ?_) (fun _ => ?_)))
    if c == ``Pure.pure then
      return ← runTac (← `(tactic| exact Tools.ShippingChildTranslateA.KeepsCP.pure _))
    if c == ``MonadExcept.throw || c == ``throw then
      return ← runTac (← `(tactic| exact Tools.ShippingChildTranslateA.KeepsCP.throw _ (by okmsg)))
    if c == ``get || c == ``MonadState.get || c == ``MonadStateOf.get then
      return ← runTac (← `(tactic| exact Tools.ShippingChildTranslateA.KeepsCP.get))
    if c == ``set || c == ``MonadStateOf.set then
      return ← runTac (← `(tactic| exact Tools.ShippingChildTranslateA.KeepsCP.set _))
    if c == ``modify || c == ``MonadState.modifyGet then
      return ← runTac (← `(tactic| exact Tools.ShippingChildTranslateA.KeepsCP.modify _))
    if c == ``Sparkle.Compiler.Elab.CompilerM.getCompilerState then
      return ← runTac (← `(tactic| exact Tools.ShippingChildTranslateA.KeepsCP.getCompilerState))
    if (← Meta.isMatcher c) then
      return ← runTac (← `(tactic| split))
    -- a lifted MetaM primitive under `Keeps`: a framed or diagnostic operation of the
    -- section's witness `O` at `hA`, for the stable `hS` (names from the context)
    if ty.isAppOf ``Tools.ShippingChildInv.Keeps then
      let O := mkIdent `O; let hA := mkIdent `hA; let hS := mkIdent `hS
      if ← runTac (← `(tactic| exact Tools.ShippingChildVCA.keepsA_framed $O $hA $hS (by constructor))) then
        return true
      if ← runTac (← `(tactic| exact Tools.ShippingChildVCA.keepsA_framed $O $hA $hS (by constructor <;> first | constructor | assumption))) then
        return true
      if ← runTac (← `(tactic| exact Tools.ShippingChildVCA.keepsA_diag $O $hA $hS (by constructor))) then
        return true
    if c == ``Sparkle.Compiler.Elab.CompilerM.liftMetaM then
      return ← runTac (← `(tactic| refine Tools.ShippingChildTranslateA.KeepsCP.lift ?_))
    -- a given rule for this head
    for (_, h, stx) in rules do
      if h == c then
        if ← runTac ⟨← `(tactic| (apply $(⟨stx⟩) <;> first | assumption | skip))⟩ then
          return true
    -- unfold a definition once
    let id := mkIdent c
    runTac (← `(tactic| unfold $id:ident))
  | .fvar _ =>
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let dty ← instantiateMVars d.type
      let isRule ← forallTelescope dty fun _ concl => pure (progOf? concl).isSome
      if isRule then
        let id := mkIdent d.userName
        if ← runTac (← `(tactic| exact $id _ _ _ _)) then return true
        if ← runTac (← `(tactic| exact $id _)) then return true
        if ← runTac (← `(tactic| exact $id)) then return true
    return false
  | _ => return false

/-- Walk every open goal until no step applies (bounded). -/
partial def kloop (rules : Array (Lean.Expr × Name × Syntax)) (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then return
  let gs ← getUnsolvedGoals
  let mut rest : List MVarId := []
  let mut progress := false
  for g in gs do
    if ← g.isAssigned then continue
    setGoals [g]
    if ← kstep rules then
      progress := true
      rest := rest ++ (← getUnsolvedGoals)
    else
      rest := rest ++ [g]
  setGoals rest
  if progress then kloop rules (fuel - 1)

def runKWalk (ts : Array Syntax) : TacticM Unit := withMainContext do
  let mut rules : Array (Lean.Expr × Name × Syntax) := #[]
  for t in ts do
    let e ← Term.withoutErrToSorry <| Tactic.elabTerm t none (mayPostpone := true)
    if let some h ← ruleHead e then
      rules := rules.push (e, h, t)
  kloop rules 400

elab "kwalk" " [" ts:term,* "]" : tactic => runKWalk (ts.getElems.map (·.raw))
elab "kwalk" : tactic => runKWalk #[]

end Tools.ShippingChildKWalk
