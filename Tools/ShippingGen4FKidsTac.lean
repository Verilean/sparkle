import Tools.ShippingGen4FKidsPrims
import Tools.ShippingChildVC
-- F-kids StatePF walk, part 3: `swalkN`, the head-directed walker for `KCS`/`KeepsCS` goals. A copy of Tools/ShippingGen4KWalkTac2.lean
-- (`swalkN`) with the `KeepsCP` rules replaced by the `KCS` rules of Tools/ShippingGen4FKidsCalc.lean. A TACTIC only (no law, no premise);
-- what it closes is a kernel-checked proof from the lemmas it is given. No sorry / axiom / native_decide.
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

namespace Tools.ShippingGen4FKidsTac
open Lean Elab Tactic Meta

/-- The program of a `KeepsCP … I prog` (or `Keeps … I prog`) type: its last argument. -/
def progOf? (t : Lean.Expr) : Option Lean.Expr :=
  let t := t.consumeMData
  if t.isAppOf ``Tools.ShippingGen4FKidsCalc.KCS || t.isAppOf ``Tools.ShippingGen4FKidsCalc.KeepsCS ||
      t.isAppOf ``Tools.ShippingGen4FKidsCalc.NoRetS || t.isAppOf ``Tools.ShippingGen4FKidsCalc.NoRetSA ||
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

def runTac (stx : TSyntax `tactic) (sorryOk : Bool := false) : TacticM Bool := do
  let s ← saveState
  let hb00 ← IO.getNumHeartbeats
  try
    -- (no error-to-`sorry` recovery: a failed nested `by …` must fail the step; a nested
    -- `by` with unsolved goals only LOGS an error, so a new logged error also fails it)
    let n0 := (← Core.getMessageLog).toList.length
    let hb0 ← IO.getNumHeartbeats
    -- (rt180) let-bound join points are not unfolded by unification (`jp ?u =?= jp ()` must assign `?u`)
    withConfig (fun c => { c with zetaDelta := false }) <| if sorryOk then evalTactic stx else Term.withoutErrToSorry (evalTactic stx)
    if (← IO.getEnv "KWALK_DEBUG").isSome then
      let d := (← IO.getNumHeartbeats) - hb0
      if d > 300000 then logInfo m!"kwalk runTac hb {d}: {stx.raw.reprint.getD ""}"
    let msgs := (← Core.getMessageLog).toList.drop n0
    if msgs.any (·.severity == .error) then
      if (← IO.getEnv "KWALK_DEBUG").isSome then logInfo m!"kwalk runTac logged error: {← msgs.filter (·.severity == .error) |>.mapM (·.data.toString)}"
      s.restore
      return false
    return true
  catch ex =>
    s.restore
    if (← IO.getEnv "KWALK_DEBUG").isSome then
      let d := (← IO.getNumHeartbeats) - hb00
      let src := stx.raw.reprint.getD ""
      let em := (← ex.toMessageData.toString).take 300
      logInfo m!"kwalk runTac failed hb {d}: {src} :: {em}"
    return false

/-- (rt177) `runTac` with a heartbeat budget of its own (a runaway try is reported and the step goes on). -/
def runTacLim (stx : TSyntax `tactic) (lim : Nat) : TacticM Bool := do
  let s ← saveState
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := lim }) (runTac stx))
    (fun ex => do
      s.restore
      if (← IO.getEnv "KWALK_DEBUG").isSome then
        let em := (← ex.toMessageData.toString).take 100
        logInfo m!"kwalk runTacLim exceeded {lim}: {em}"
      return false)

/-- (rt176) `apply rule <;> first | assumption | skip`, except that `assumption` is not tried on a LARGE new goal
(`∀ …, KeepsCP (k x)` for a big continuation `k`): the defeq test of such a goal against a hypothesis such as `htr`
beta-reduces `k x` and runs `whnf` on the whole do-block (the H11 runaway at `CompilerM.withLocalDecl`). -/
def applyRule (stx : Syntax) : TacticM Bool := do
  unless ← runTac ⟨← `(tactic| apply $(⟨stx⟩))⟩ do return false
  let mut rest : List MVarId := []
  for g in ← getGoals do
    if ← g.isAssigned then continue
    let ty ← instantiateMVars (← g.getType)
    if ty.approxDepth.toNat < 14 then
      setGoals [g]
      if ← runTac (← `(tactic| assumption)) then continue
    rest := rest ++ [g]
  setGoals rest
  return true

/-- (fkids3) is a `PairPF` / `OptPFc` fact in the local context (a child pair is in scope)? Gates the rules that exist only for it, so that
every other module's walk is unchanged. -/
def hasPFHyp : MetaM Bool := do
  let mut r := false
  for d in ← getLCtx do
    let hd := (← instantiateMVars d.type).consumeMData.getAppFn.constName?
    if hd == some ``Tools.ShippingGen4FKidsCalc.OptPFc || hd == some ``Tools.ShippingGen4FKids.PairPF then r := true
  pure r

/-- (fkids3) is the child-synthesis hypothesis `hchild` in scope? Gates the child-pair rules (join-point premise, `bindTryChild`) to the modules that have it. -/
def hasChild : MetaM Bool := do
  return ((← getLCtx).findFromUserName? `hchild).isSome

/-- One step on the main goal. Returns `false` if nothing applied. -/
def kstep (rules : Array (Lean.Expr × Name × Syntax)) : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  if ty.isForall then
    return ← runTac (← `(tactic| intros))
  -- the unpointed statement: point it at a fresh state
  if ty.consumeMData.isAppOf ``Tools.ShippingGen4FKidsCalc.KeepsCS || ty.consumeMData.isAppOf ``Tools.ShippingGen4FKidsCalc.NoRetSA then
    return ← runTac (← `(tactic| intro st))
  let some p := progOf? ty | do
    if ty.getAppFn.constName? == some ``Tools.ShippingGen4FKidsCalc.GoodS then
      if ← runTac (← `(tactic| first
          | exact Tools.ShippingGen4FKidsCalc.GoodS.refl ‹_›
          | exact Tools.ShippingGen4FKidsCalc.GoodS.of_view ‹_› rfl
          | good_tac
          | exact Tools.ShippingGen4FKidsCalc.GoodS.trans ‹_› ‹_›)) then return true
    -- (fkids3) a child pair's `ParamFree` facts (from `OptPF` / `PairPF` / a member of its design) and `OptPF (some r)`
    if ty.getAppFn.constName? == some ``Tools.ShippingGen4FKids.ParamFree && (← hasPFHyp) then
      if ← runTac (← `(tactic| first
          | assumption
          | exact (‹Tools.ShippingGen4FKidsCalc.OptPFc (some _)› _ rfl).1
          | exact (‹Tools.ShippingGen4FKidsCalc.OptPFc (some _)› _ rfl).2 _ ‹_›
          | exact (‹Tools.ShippingGen4FKids.PairPF _›).1
          | exact (‹Tools.ShippingGen4FKids.PairPF _›).2 _ ‹_›)) then return true
    if ty.getAppFn.constName? == some ``Tools.ShippingGen4FKidsCalc.OptPFc then
      if ← runTac (← `(tactic| first
          | assumption
          | exact Tools.ShippingGen4FKidsCalc.OptPFc.some' ‹_›)) then return true
    -- side goals left by a rule (`SideRef`, `LocalRefType`, a message class, a hypothesis)
    if ← runTac (← `(tactic| assumption)) then return true
    if ← runTac (← `(tactic| rfl)) then return true
    let h := ty.getAppFn.constName?.getD .anonymous
    if h == ``Tools.ShippingChildInv.SideRef || h == ``Tools.ShippingChildInv.LocalRefType then
      return ← runTac (← `(tactic| constructor))
    if h == ``Tools.ShippingChildInv.OkMsg || h == ``Tools.ShippingChildInv.OkExc then
      if ← runTac (← `(tactic| okmsg)) then return true
      -- (rt175) the exception of a caught `some ex`, from `OkOpt (…, some ex).snd`
      return ← runTac (← `(tactic| exact (‹Tools.ShippingChildInv.OkOpt _›) _ rfl))
    return false
  let p := p.consumeMData
  -- (rt175) a do-notation JOIN POINT `have __do_jp := fun x̄ => v; b`: do NOT copy `v` into every use in `b` (that copies the continuation
  -- once per branch: exponential). Prove `∀ x̄, KeepsCP (v x̄)` once and walk `b` with the join point an opaque local `jp` and that fact.
  if p.isLet && p.letName!.toString.startsWith "__do_jp" && p.letValue!.isLambda then
    let hdr := ty.consumeMData.appFn!
    -- (F-kids) a join point is called at whatever state is current there: its fact is the UNPOINTED `KeepsCS`
    let hdrU : Lean.Expr := if ty.consumeMData.isAppOf ``Tools.ShippingGen4FKidsCalc.KCS then
        mkAppN (mkConst ``Tools.ShippingGen4FKidsCalc.KeepsCS) (ty.consumeMData.getAppArgs.extract 0 6)
      else if ty.consumeMData.isAppOf ``Tools.ShippingGen4FKidsCalc.NoRetS then
        mkAppN (mkConst ``Tools.ShippingGen4FKidsCalc.NoRetSA) (ty.consumeMData.getAppArgs.extract 0 6) else hdr
    -- (fkids3) a join point over an optional child pair is called only with `OptPF` pairs: its fact has that premise
    let isOptMD (t : Lean.Expr) : Bool :=
      let t := t.consumeMData
      t.isAppOf ``Option && t.appArg!.consumeMData.isAppOf ``Prod && t.appArg!.consumeMData.getAppArgs[0]!.consumeMData.isConstOf ``Sparkle.IR.AST.Module
    let withPrem (xs : Array Lean.Expr) (body : Lean.Expr) : MetaM Lean.Expr := do
      let mut b := body
      for x in xs.reverse do
        if (← hasChild) && isOptMD (← inferType x) then b := mkForall `hpf .default (mkApp (mkConst ``Tools.ShippingGen4FKidsCalc.OptPFc) x) b
      return b
    let T := p.letType!
    let n := (← getLCtx).decls.size
    let jpName := Name.mkSimple s!"jp_{n}"
    let hName := Name.mkSimple s!"hjp_{n}"
    -- (rt180) the join point and its fact are LET-bound in the proof term (`let jp := v; let hj := hv; body`), not a beta-redex `(fun jp hj => body) v hv`:
    -- `instantiateMVars` beta-reduces the redex and so copies `v` into every use of `jp` in `body` (nested join points: the final instantiation did not finish in 20 GB, H11)
    let hvT ← forallTelescope T fun xs _ => do mkForallFVars xs (← withPrem xs (mkApp hdrU (mkAppN p.letValue! xs).headBeta))
    let hvM ← mkFreshExprSyntheticOpaqueMVar hvT
    let bodyM ← withLetDecl jpName T p.letValue! fun jp => do
      let hypT ← forallTelescope T fun xs _ => do mkForallFVars xs (← withPrem xs (mkApp hdrU (mkAppN jp xs)))
      withLetDecl hName hypT hvM fun hj => do
        let bodyM ← mkFreshExprSyntheticOpaqueMVar (mkApp hdr (p.letBody!.instantiate1 jp))
        g.assign (← mkLetFVars #[jp, hj] bodyM)
        return bodyM
    replaceMainGoal [bodyM.mvarId!, hvM.mvarId!]
    return true
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
    if fn.constName? == some `Sparkle.Compiler.Elab.CompilerM.withLocalDecl then
      logInfo m!"kwalk wld: n {p.getArg! 1} ty {p.getArg! 2} goalDepth {p.approxDepth}"
  -- (fkids3) a goal that never returns: bind (the first part is a `KCS` goal), ite, dite, a lifted `throwError`, a `throw`, a match
  if ty.consumeMData.isAppOf ``Tools.ShippingGen4FKidsCalc.NoRetS then
    if let .const c _ := fn then
      if c == ``Bind.bind then
        return ← runTac (← `(tactic| refine Tools.ShippingGen4FKidsCalc.NoRetS.bind ?_ (fun _ _ _ => ?_)))
      if c == ``ite then
        return ← runTac (← `(tactic| refine Tools.ShippingGen4FKidsCalc.NoRetS.ite (fun _ => ?_) (fun _ => ?_)))
      if c == ``dite then
        return ← runTac (← `(tactic| refine Tools.ShippingGen4FKidsCalc.NoRetS.dite (fun _ => ?_) (fun _ => ?_)))
      if c == ``Sparkle.Compiler.Elab.CompilerM.liftMetaM then
        return ← runTac (← `(tactic| refine Tools.ShippingGen4FKidsCalc.NoRetS.liftThrowError _ ?_))
      if c == ``MonadExcept.throw || c == ``throw then
        return ← runTac (← `(tactic| exact Tools.ShippingGen4FKidsCalc.NoRetS.throw _ (by okmsg)))
      if (← Meta.isMatcher c) then
        return ← runTac (← `(tactic| split))
  match fn with
  | .const c _ =>
    if c == ``Bind.bind then
      -- `get >>= f`: the continuation is run from the very state read
      if ty.consumeMData.isAppOf ``Tools.ShippingGen4FKidsCalc.KCS then
        let a4 := (p.getArg! 4).consumeMData
        if [``get, ``MonadState.get, ``MonadStateOf.get, ``getThe].contains (a4.getAppFn.constName?.getD .anonymous) then
          if ← runTac (← `(tactic| refine Tools.ShippingGen4FKidsCalc.KCS.bindGet ?_)) then
            return true
      -- `getCompilerState >>= f` (the read context carries provenance)
      if (p.getArg! 4).consumeMData.isConstOf ``Sparkle.Compiler.Elab.CompilerM.getCompilerState then
        if ← runTac (← `(tactic| refine Tools.ShippingGen4FKidsCalc.KCS.bindCtx (fun _ _ => ?_))) then
          return true
      if (← IO.getEnv "KWALK_DEBUG").isSome then
        let a4s := (← ppExpr (p.getArg! 4)).pretty
        if (a4s.splitOn "eprintln").length > 1 && a4s.length < 300 then logInfo m!"kwalk bind-eprintln a4: {a4s} :: raw {(p.getArg! 4).consumeMData.getAppFn} / {(p.getArg! 4).consumeMData.getAppNumArgs}"
      -- (rt175) a FUSED pair `liftMetaM (liftM (IO.eprintln _)) >>= fun _ => liftMetaM _` (the stderr pair): a given rule with head `bind`
      do
        let a4 := (p.getArg! 4).consumeMData
        if a4.isAppOf ``liftM && a4.appArg!.consumeMData.getAppFn.constName? == some ``IO.eprintln then
          for (_, h, stx) in rules do
            if h == ``Bind.bind then
              if ← runTac ⟨← `(tactic| (apply $(⟨stx⟩) <;> first | assumption | skip))⟩ then
                return true
        if a4.isAppOf ``Sparkle.Compiler.Elab.CompilerM.liftMetaM then
          let inner := a4.appArg!.consumeMData
          if inner.isAppOf ``liftM && inner.appArg!.consumeMData.getAppFn.constName? == some ``IO.eprintln then
            for (_, h, stx) in rules do
              if h == ``Bind.bind then
                if ← runTac ⟨← `(tactic| (apply $(⟨stx⟩) <;> first | assumption | skip))⟩ then
                  return true
      if ty.consumeMData.isAppOf ``Tools.ShippingChildInv.Keeps then
        return ← runTac (← `(tactic| refine Tools.ShippingChildInv.Keeps.bind ?_ (fun _ => ?_)))
      -- (fkids3) `try (some <$> liftMetaM (childSynthEntry n)) catch h` with a handler that never returns: the child pair's `PairPF` reaches the continuation
      if ty.consumeMData.isAppOf ``Tools.ShippingGen4FKidsCalc.KCS && (← hasChild) &&
          [``MonadExcept.tryCatch, ``tryCatchThe, ``MonadExceptOf.tryCatch].contains ((p.getArg! 4).consumeMData.getAppFn.constName?.getD .anonymous) then
        let hchild := mkIdent `hchild; let hA := mkIdent `hA
        if ← runTac (← `(tactic| refine Tools.ShippingGen4FKidsCalc.KCS.bindTryChild ($hchild _ _ $hA _) (fun _ _ => ?_) (fun _ _ _ _ => ?_))) then
          return true
      -- (rt174) the inline attempt: its caught exception goes to the continuation (hypothesis `htri`)
      if ((p.getArg! 4).consumeMData.getAppFn.constName?.map (·.toString.endsWith "tryInlineUnfold")).getD false then
        -- (fkids3) the lemma is declared LATER (LegacyH7), so its name cannot be resolved inside a quotation here (hygiene): build the identifier
        let bc := mkIdent `Tools.ShippingGen4FKidsLegacyH7.KCS.bindCaught
        if ← runTac (← `(tactic| refine $bc (by assumption) (fun _ _ _ _ => ?_))) then
          return true
      -- (rt175) only for a context read (the defeq test of `bindRead` against a large `tryCatch` program timed out)
      if [``MonadReader.read, ``read, ``MonadReaderOf.read, ``readThe].contains
          ((p.getArg! 4).consumeMData.getAppFn.constName?.getD .anonymous) then
        if ← runTac (← `(tactic| refine Tools.ShippingGen4FKidsCalc.KCS.bindRead (fun _ _ => ?_))) then
          return true
      return ← runTac (← `(tactic| refine Tools.ShippingGen4FKidsCalc.KCS.bind ?_ (fun _ _ _ => ?_)))
    if ty.consumeMData.isAppOf ``Tools.ShippingChildInv.Keeps then
      if c == ``ite then
        return ← runTac (← `(tactic| apply Tools.ShippingChildInv.Keeps.ite)) true
      if c == ``dite then
        return ← runTac (← `(tactic| apply Tools.ShippingChildInv.Keeps.dite)) true
      if c == ``Pure.pure then
        return ← runTac (← `(tactic| exact Tools.ShippingChildInv.Keeps.pure _))
      if c == ``MonadExcept.throw || c == ``throw then
        if ← runTac (← `(tactic| exact Tools.ShippingChildInv.Keeps.throw _ (by okmsg))) then return true
        -- (rt175) an early return `throw r` in `ExceptT ρ MetaM`: a pure `Except.error r`
        return ← runTac (← `(tactic| exact Tools.ShippingChildInv.Keeps.pure (Except.error _)))
    if c == ``ite then
      return ← runTac (← `(tactic| refine Tools.ShippingGen4FKidsCalc.KCS.ite (fun _ => ?_) (fun _ => ?_)))
    if c == ``dite then
      return ← runTac (← `(tactic| refine Tools.ShippingGen4FKidsCalc.KCS.dite (fun _ => ?_) (fun _ => ?_)))
    if c == ``Pure.pure then
      return ← runTac (← `(tactic| exact Tools.ShippingGen4FKidsCalc.KCS.pure _))
    if c == ``MonadExcept.throw || c == ``throw then
      if ← runTac (← `(tactic| exact Tools.ShippingGen4FKidsCalc.KCS.throw _ (by okmsg))) then return true
      return ← runTac (← `(tactic| exact Tools.ShippingGen4FKidsCalc.KCS.throwE _))
    if (c == ``MonadExcept.tryCatch || c == ``tryCatchThe || c == ``MonadExceptOf.tryCatch) &&
        ty.consumeMData.isAppOf ``Tools.ShippingChildInv.Keeps then
      if ← runTac (← `(tactic| refine Tools.ShippingChildInv.Keeps.tryCatch ?_ (fun _ _ => ?_))) then return true
    if c == ``Except.rec then
      if ty.consumeMData.isAppOf ``Tools.ShippingChildInv.Keeps then
        return ← runTac (← `(tactic| (rename_i x; cases x <;> exact Tools.ShippingChildInv.Keeps.pure _)))
      -- (rt180) the general case: a constructor major is iota-reduced; an fvar major is `cases`-split (each arm is then walked; the arms need not be `pure`)
      if p.getAppNumArgs ≥ 6 then
        let major ← whnfCore (p.getArg! 5)
        if major.isAppOf ``Except.error || major.isAppOf ``Except.ok then
          let p' ← whnfCore p
          if p' != p then
            replaceMainGoal [← g.replaceTargetDefEq (mkApp ty.consumeMData.appFn! p')]
            return true
        else if major.isFVar then
          let gs ← g.cases major.fvarId!
          replaceMainGoal (gs.toList.map (·.mvarId))
          return true
      return ← runTac (← `(tactic| (rename_i x; cases x <;> exact Tools.ShippingGen4FKidsCalc.KCS.pure _)))
    if c == ``get || c == ``MonadState.get || c == ``MonadStateOf.get then
      return ← runTac (← `(tactic| exact Tools.ShippingGen4FKidsCalc.KCS.get))
    if c == ``set || c == ``MonadStateOf.set then
      return ← runTac (← `(tactic| refine Tools.ShippingGen4FKidsCalc.KCS.set _ (fun _ => ?_)))
    if c == ``modify || c == ``MonadState.modifyGet then
      return ← runTac (← `(tactic| refine Tools.ShippingGen4FKidsCalc.KCS.modify _ (fun _ => ?_)))
    if c == ``Sparkle.Compiler.Elab.CompilerM.getCompilerState then
      return ← runTac (← `(tactic| exact Tools.ShippingGen4FKidsCalc.KCS.getCompilerState))
    if (← Meta.isMatcher c) then
      return ← runTac (← `(tactic| split))
    -- a lifted MetaM primitive under `Keeps`: a framed or diagnostic operation of the
    -- section's witness `O` at `hA`, for the stable `hS` (names from the context)
    if ty.consumeMData.isAppOf ``Tools.ShippingChildInv.Keeps then
      let O := mkIdent `O; let hA := mkIdent `hA; let hS := mkIdent `hS
      if ← runTac (← `(tactic| exact Tools.ShippingChildVCA.keepsA_framed $O $hA $hS (by constructor))) then
        return true
      if ← runTac (← `(tactic| exact Tools.ShippingChildVCA.keepsA_framed $O $hA $hS (by constructor <;> first | constructor | assumption))) then
        return true
      if ← runTac (← `(tactic| exact Tools.ShippingChildVCA.keepsA_diag $O $hA $hS (by constructor))) then
        return true
    if c == ``Sparkle.Compiler.Elab.CompilerM.liftMetaM then
      return ← runTac (← `(tactic| refine Tools.ShippingGen4FKidsCalc.KCS.lift ?_))
    -- (rt174) reads of the contexts: always succeed
    if ty.consumeMData.isAppOf ``Tools.ShippingChildInv.Keeps then
      if [``read, ``readThe, ``MonadReader.read, ``MonadReaderOf.read, ``Lean.getLCtx,
          ``Lean.MonadLCtx.getLCtx, ``Lean.getRef, ``Lean.MonadRef.getRef, ``Lean.getOptions,
          ``Lean.MonadOptions.getOptions, ``liftM, ``monadLift, ``MonadLiftT.monadLift].contains c then
        if ← runTac (← `(tactic| exact Tools.ShippingChildInv.Keeps.of_ok (fun w => ⟨_, rfl⟩))) then
          return true
    else
      -- the `CompilerM` lifts of the A walker (law-free)
      if c == ``liftM || c == ``monadLift || c == ``MonadLiftT.monadLift then
        -- (rt177) by the type of the lifted action (a failed `liftIO` / `liftBaseIO` try costs 4-7M heartbeats)
        let xty := (← whnfR (← inferType p.appArg!)).consumeMData
        let xh := xty.getAppFn.constName?.getD .anonymous
        if (← IO.getEnv "KWALK_DEBUG").isSome then logInfo m!"kwalk lift xh {xh} :: {xty}"
        let order : List Name :=
          if xh == ``IO || xh == ``EIO then [`liftIO] else if xh == ``BaseIO then [`liftBaseIO] else if xh == ``Lean.Meta.MetaM then [`liftM] else [`liftM]
        for lm in order do
          let t := mkIdent (`Tools.ShippingGen4FKidsCalc.KCS ++ lm)
          if ← runTac (← `(tactic| refine $t ?_)) then return true
      if c == ``ST.Ref.get then
        if ← runTac (← `(tactic| refine Tools.ShippingGen4FKidsCalc.KCS.refGet ?_)) then return true
      if c == ``ST.Ref.set then
        if ← runTac (← `(tactic| refine Tools.ShippingGen4FKidsCalc.KCS.refSet ?_)) then return true
      if c == ``ST.Ref.modify then
        if ← runTac (← `(tactic| refine Tools.ShippingGen4FKidsCalc.KCS.refModify ?_)) then return true
      if c == ``MonadReader.read || c == ``read || c == ``MonadReaderOf.read then
        if ← runTac (← `(tactic| exact Tools.ShippingGen4FKidsCalc.KCS.read)) then return true
    -- (rt177) `withLocalDecl n ty k`: a dedicated step (first-order unification of `n ty k` only; the continuation
    -- goal is opened with `fun _ _ _ x => ?_`, so no `assumption`/defeq test is run against the large `k`)
    if c == ``Sparkle.Compiler.Elab.CompilerM.withLocalDecl && !ty.consumeMData.isAppOf ``Tools.ShippingChildInv.Keeps then
      let M := mkIdent `M; let hS := mkIdent `hS; let hA := mkIdent `hA
      let wl := mkIdent `Tools.ShippingGen4FKidsTele.withLocalDeclPS
      if ← runTacLim (← `(tactic| refine $wl $M $hS (by assumption) _ _ _ (fun _ _ _ x => ?_))) 100000000 then
        return true
    -- a given rule for this head
    for (_, h, stx) in rules do
      if h == c then
        if ← applyRule stx then
          return true
    -- (rt176: AFTER the given rules for the head: a failed attempt costs 13-35M heartbeats (H11), and `liftM` / `ST.Ref.modify` / `addMessageContext` have a rule) (rt174) a lifted MetaM primitive under `Keeps`: a `FramedNM` operation of the section's `M`, `hA`, `hS`
    -- (the constructor and its `SideRefNM` / `LocalRefType` side goals found by `constructor`)
    if ty.consumeMData.isAppOf ``Tools.ShippingChildInv.Keeps then
      let M := mkIdent `M; let hS := mkIdent `hS
      -- (rt177) the `FramedNM` constructors that can match this head, tried directly (no `constructor` search over all ~50)
      let inner := if [``liftM, ``monadLift, ``MonadLiftT.monadLift, ``MonadLift.monadLift].contains c then p.appArg!.consumeMData else p
      let ih := inner.getAppFn.constName?.getD .anonymous
      let cands : List Name :=
        if ih == ``ST.Ref.modifyGet then [`sideModifyGetIO, `sideModifyGet]
        else if ih == ``ST.Ref.get then [`sideGetIO, `exprCacheGetIO, `localGetIO, `sideGet, `cacheGet, `synthGet, `depthGet, `exprCacheGet, `localGet]
        else if ih == ``ST.Ref.set then [`sideSetIO, `localSetIO, `sideSet, `localSet]
        else if ih == ``ST.Ref.modify then [`sideModifyIO, `localModifyIO, `sideModify, `localModify, `exprCacheModify]
        else if ih == ``Lean.Meta.whnf then [`whnf]
        else if ih == ``Lean.Meta.inferType then [`inferType]
        else if ih == ``Lean.Meta.isClass? then [`isClass?]
        else if ih == ``Lean.Meta.whnfUntil then [`whnfUntil]
        else if ih == ``Lean.Meta.instantiateForall then [`instantiateForall]
        else if ih == ``Lean.Meta.mkLambdaFVars then [`mkLambdaFVars]
        else if ih == ``Lean.Meta.mkAppM then [`mkAppM]
        else if ih == ``Lean.Meta.unfoldDefinition? then [`unfoldDefinition?]
        else if ih == ``Lean.Meta.reduce then [`reduce]
        else if ih == ``Lean.getConstInfo then [`constInfo]
        else if ih == ``Lean.MonadEnv.getEnv || ih == ``Lean.getEnv then [`env]
        else if ih == ``Lean.mkFreshFVarId then [`freshFVar]
        else if ih == ``Lean.FVarId.throwUnknown then [`fvarThrowUnknown]
        else if ih == ``IO.getEnv then [`ioEnv]
        else if ih == ``IO.monoMsNow then [`monoMs]
        else if ih == ``modifyTraceState then [`coreModifyTrace]
        else if ih == ``IO.mkRef then [`localMk, `mkExprCache]
        else []
      for cn in cands do
        let k := mkIdent (`Tools.Assume.MemoFamily.FramedNM ++ cn)
        if ← runTac (← `(tactic| exact Tools.ShippingGen4KWalkPrims.keepsK_framedNM $M (by assumption) $hS (by apply $k <;> first | assumption | constructor))) then
          return true
      if cands.isEmpty then
        if (← IO.getEnv "KWALK_DEBUG").isSome then logInfo m!"kwalk framed-fallback: head {c} inner {ih} p {p.approxDepth} :: {(← ppExpr p).pretty.take 900}"
        if ← runTac (← `(tactic| exact Tools.ShippingGen4KWalkPrims.keepsK_framedNM $M (by assumption) $hS (by constructor <;> first | constructor | assumption))) then
          if (← IO.getEnv "KWALK_DEBUG").isSome then logInfo m!"kwalk framed-fallback OK: {ih}"
          return true
    -- a local hypothesis about this very head (a recursive call's induction hypothesis)
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let dty ← instantiateMVars d.type
      let hp? ← forallTelescope dty fun _ concl => pure (progOf? concl)
      if let some hp := hp? then
        if headConst? hp == some c then
          let id := mkIdent d.userName
          if ← runTac (← `(tactic| exact $id)) then return true
          -- (rt176) a size-bounded IH `∀ mctx cctx, AdmCtx → ∀ e', sizeOf e' < n → …` (toIR): the bound is discharged from the context
          if ← runTac (← `(tactic| exact $id _ _ (by assumption) _ (by simp_all <;> omega))) then return true
          if ← runTac (← `(tactic| exact $id _ _ (by assumption) _ _ _ _)) then return true
          if ← runTac (← `(tactic| exact $id _ _ (by assumption) _ _ _)) then return true
          if ← runTac (← `(tactic| exact $id _ _ (by assumption) _ _)) then return true
          if ← runTac (← `(tactic| exact $id _ _ (by assumption) _)) then return true
          if ← runTac (← `(tactic| exact $id _ _ _ _)) then return true
          if ← runTac (← `(tactic| exact $id _)) then return true
    -- unfold a definition once
    let id := mkIdent c
    runTac (← `(tactic| unfold $id:ident))
  | .proj sn i _ =>
    -- (rt175) `tryCatch` under `Keeps` (the `try … catch` of a `MetaM` block): the rule, before the instance is unfolded
    if (sn == ``MonadExcept || sn == ``MonadExceptOf) && i == 1 && ty.consumeMData.isAppOf ``Tools.ShippingChildInv.Keeps then
      if ← runTac (← `(tactic| refine Tools.ShippingChildInv.Keeps.tryCatch ?_ (fun _ _ => ?_))) then return true
    if ty.consumeMData.isAppOf ``Tools.ShippingChildInv.Keeps then
      if ← runTac (← `(tactic| apply Tools.ShippingChildInv.Keeps.forIn_array)) true then return true
      if ← runTac (← `(tactic| apply Tools.ShippingChildInv.Keeps.forIn_list)) true then return true
      if ← runTac (← `(tactic| apply Tools.ShippingChildInv.Keeps.forIn_range)) true then return true
    else
      if ← runTac (← `(tactic| apply Tools.ShippingGen4FKidsCalc.KCS.forIn_array)) true then return true
      if (← hasPFHyp) then
        if ← runTac (← `(tactic| apply Tools.ShippingGen4FKidsCalc.KCS.forIn_list_mem)) true then return true
      if ← runTac (← `(tactic| apply Tools.ShippingGen4FKidsCalc.KCS.forIn_list)) true then return true
      if ← runTac (← `(tactic| apply Tools.ShippingGen4FKidsCalc.KCS.forIn_range)) true then return true
    -- an instance projection (e.g. `withTransparency` through `MonadControlT`): reduce it, as `vca` does
    let inst ← withTransparency .instances (whnf fn.projExpr!)
    let p' ← whnfCore (mkAppN (fn.updateProj! inst) p.getAppArgs)
    if p' != p then
      let g' ← g.replaceTargetDefEq (mkApp ty.consumeMData.appFn! p')
      replaceMainGoal [g']
      return true
    return false
  | .lam .. =>
    -- (rt175) a `Meta.Context` update that the instance reduction left as a lambda (`withTransparency`): `withReader f x`
    if ty.consumeMData.isAppOf ``Tools.ShippingChildInv.Keeps then
      return ← runTac (← `(tactic| refine Tools.ShippingChildWalkA.Keeps.withReaderA (by assumption) _ (fun _ => rfl) (fun _ => ?_)))
    return false
  | .fvar fid =>
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let dty ← instantiateMVars d.type
      let isRule ← forallTelescope dty fun _ concl => pure (progOf? concl).isSome
      -- (rt175) a hypothesis about ANOTHER local function (another join point) is not for this call
      -- (rt176) and a hypothesis about a CONSTANT (`hchild`: `childSynthEntry _`) is not for a call of a local function either (each such try is a failed elaboration)
      let other ← forallTelescope dty fun _ concl => pure <|
        match progOf? concl with
        | some hp => !(hp.consumeMData.getAppFn.isFVar && hp.consumeMData.getAppFn.fvarId! == fid)
        | none => false
      if isRule && !other then
        let id := mkIdent d.userName
        if ← runTac (← `(tactic| apply $id)) then return true
        if ← runTac (← `(tactic| exact $id _ _ (by assumption) _ _ _ _)) then return true
        if ← runTac (← `(tactic| exact $id _ _ (by assumption) _ _ _)) then return true
        if ← runTac (← `(tactic| exact $id _ _ (by assumption) _ _)) then return true
        if ← runTac (← `(tactic| exact $id _ _ (by assumption) _)) then return true
        if ← runTac (← `(tactic| exact $id _ _ _ _)) then return true
        if ← runTac (← `(tactic| exact $id _)) then return true
        if ← runTac (← `(tactic| exact $id)) then return true
    return false
  | _ => return false

def traceRss (tag : String) : IO Unit := do
  if let some path ← IO.getEnv "KWALK_TRACE" then
    let sm ← IO.FS.readFile "/proc/self/statm"
    let h ← IO.FS.Handle.mk path .append
    h.putStrLn s!"KWT-RSS {tag} {((sm.splitOn " ").getD 1 "0").toNat! * 4 / 1024} MB t={← IO.monoMsNow}"
    h.flush

/-- Walk every open goal until no step applies (bounded). (rt176) A goal on which no step applies is set aside for
good (`stuck`) and not retried in later rounds: retrying every stuck goal each round made the cost quadratic in the
number of steps (H11: 1189 steps used 4M heartbeats). -/
partial def kloop (rules : Array (Lean.Expr × Name × Syntax)) (fuel : Nat) (stuck : List MVarId := []) (root : Option MVarId := none) : TacticM Unit := do
  if fuel == 0 then return
  let gs ← getUnsolvedGoals
  let mut rest : List MVarId := []
  let mut stuck' : List MVarId := stuck
  let mut progress := false
  for g in gs do
    if ← g.isAssigned then continue
    if stuck.contains g then
      rest := rest ++ [g]
      continue
    setGoals [g]
    let hb0 ← IO.getNumHeartbeats
    if (← IO.getEnv "KWALK_TRACE").isSome then
      let gty ← instantiateMVars (← g.getType)
      let hd := match progOf? gty with
        | some pp => (pp.consumeMData.getAppFn.constName?.map toString).getD (if pp.consumeMData.isLet then "let" else if pp.consumeMData.isLambda then "lam" else "other")
        | none => "side"
      let sm ← IO.FS.readFile "/proc/self/statm"
      let rssMB := ((sm.splitOn " ").getD 1 "0").toNat!  * 4 / 1024
      let h ← IO.FS.Handle.mk (← IO.getEnv "KWALK_TRACE").get! .append
      h.putStrLn s!"KWT goals {gs.length} head {hd} depth {gty.approxDepth} rssMB {rssMB}"
      if hd == "Pure.pure" then
        let pp := (progOf? gty).get!
        h.putStrLn s!"  PP {((← ppExpr pp).pretty).take 600}"
      h.flush
    let ok ← kstep rules
    if (← IO.getEnv "KWALK_DEBUG").isSome then
      logInfo m!"kwalk hb {(← IO.getNumHeartbeats) - hb0} goals {gs.length}"
    if ok then
      progress := true
      rest := rest ++ (← getUnsolvedGoals)
    else
      stuck' := g :: stuck'
      rest := rest ++ [g]
  setGoals rest
  if (← IO.getEnv "KWALK_TRACE").isSome && (← IO.getEnv "KWALK_INST").isSome then
    if let some r := root then
      let t0 ← IO.monoMsNow
      let e ← instantiateMVars (mkMVar r)
      traceRss s!"round fuel {fuel} goals {rest.length} inst depth {e.approxDepth} took {(← IO.monoMsNow) - t0}ms"
  if progress then kloop rules (fuel - 1) stuck' root

def runSWalkN (ts : Array Syntax) (strict : Bool := false) : TacticM Unit := withMainContext do
  let g0 ← getMainGoal
  let mut rules : Array (Lean.Expr × Name × Syntax) := #[]
  for t in ts do
    let e ← Term.withoutErrToSorry <| Tactic.elabTerm t none (mayPostpone := true)
    if let some h ← ruleHead e then
      rules := rules.push (e, h, t)
  kloop rules 400 [] (some g0)
  -- (rt180) never leave stuck goals for the default "unsolved goals" error: printing them (the whole do-block in the goal) took > 20 GB
  let stuck ← getUnsolvedGoals
  if strict && !stuck.isEmpty then
    let mut hs : List String := []
    for g in stuck.take 5 do
      let gty ← instantiateMVars (← g.getType)
      hs := hs ++ [match progOf? gty with
        | some pp => s!"{pp.consumeMData.getAppFn.constName?.map toString |>.getD "<non-const>"} (depth {gty.approxDepth})"
        | none => s!"side {gty.getAppFn.constName?.map toString |>.getD "?"}"]
    throwError "swalkN: {stuck.length} goal(s) stuck, first heads: {hs}"
  traceRss "walk-done"
  if (← IO.getEnv "KWALK_TRACE").isSome then
    let e ← instantiateMVars (mkMVar g0)
    traceRss s!"instantiated depth {e.approxDepth}"
  if let some path ← IO.getEnv "KWALK_TRACE" then
    let h ← IO.FS.Handle.mk path .append
    h.putStrLn s!"KWT-END unsolved {(← getUnsolvedGoals).length}"
    for g in ← getUnsolvedGoals do
      let gty ← instantiateMVars (← g.getType)
      let hd := match progOf? gty with
        | some pp => (pp.consumeMData.getAppFn.constName?.map toString).getD (if pp.consumeMData.isLet then "let" else if pp.consumeMData.isLambda then "lam" else if pp.consumeMData.getAppFn.isFVar then "fvar" else "other")
        | none => "side:" ++ (gty.getAppFn.constName?.map toString).getD "?"
      h.putStrLn s!"KWT-END goal head {hd} depth {gty.approxDepth} isForall {gty.isForall}"
      if let some pp := progOf? gty then
        h.putStrLn s!"  fn {pp.consumeMData.getAppFn} nargs {pp.consumeMData.getAppNumArgs}"
        for a in pp.consumeMData.getAppArgs do
          h.putStrLn s!"   arg depth {a.approxDepth} :: {a.dbgToString.take 200}"
    h.flush

elab "swalkN" " [" ts:term,* "]" : tactic => runSWalkN (ts.getElems.map (·.raw))
elab "swalkN" : tactic => runSWalkN #[]
/-- (rt180) `swalkN`, but fails with a SHORT message when goals remain (the default "unsolved goals" error prints the goal: > 20 GB on H11). -/
elab "swalkS" " [" ts:term,* "]" : tactic => runSWalkN (ts.getElems.map (·.raw)) true

end Tools.ShippingGen4FKidsTac
