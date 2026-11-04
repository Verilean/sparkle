import Tools.ShippingChildTranslateA
import Tools.ShippingGen4KWalkPrims
import Tools.ShippingChildWalkA
import Tools.ShippingChildVC
-- BUILT: kjob lake build Tools.ShippingGen4KWalkLegacyH8 exit 0 (rt175, source as of this commit; Tac2 and everything that imports it rebuilt); clean build is the coder's. rt175 additions to the tactic (no law): a rule for the fused stderr pair, `bindRead` only for a context read, a do-notation JOIN POINT `have __do_jp` is walked once (not copied into every branch: this was the H8 timeout), `tryCatch` / `Except.rec` / early-return `throw` under `Keeps`, the exception of a caught `some ex`. Earlier header: was BUILT: kjob lake build Tools.ShippingGen4KWalkTac2 exit 0 (rt174, source as of d8c3ec7b). (copy of ShippingGen4KWalkTac + a generic FramedNM step). was: kjob lake build Tools.ShippingGen4KWalkTac exit 0 (rt169, source as of 9e5eb088). A TACTIC only (no law): copy for the K walk of Tools/ShippingChildKWalk.lean; `kwalkN` also walks plain `Keeps` goals (ite/dite/pure/throw, forIn, instance projections, local IH). No sorry (`sorryOk` is a flag name of the nested-elaboration mode).
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

namespace Tools.ShippingGen4KWalkTac2
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

def runTac (stx : TSyntax `tactic) (sorryOk : Bool := false) : TacticM Bool := do
  let s ← saveState
  let hb00 ← IO.getNumHeartbeats
  try
    -- (no error-to-`sorry` recovery: a failed nested `by …` must fail the step; a nested
    -- `by` with unsolved goals only LOGS an error, so a new logged error also fails it)
    let n0 := (← Core.getMessageLog).toList.length
    let hb0 ← IO.getNumHeartbeats
    if sorryOk then evalTactic stx else Term.withoutErrToSorry (evalTactic stx)
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
      let em := (← ex.toMessageData.toString).take 60
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

/-- One step on the main goal. Returns `false` if nothing applied. -/
def kstep (rules : Array (Lean.Expr × Name × Syntax)) : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  if ty.isForall then
    return ← runTac (← `(tactic| intros))
  let some p := progOf? ty | do
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
    let T := p.letType!
    let n := (← getLCtx).decls.size
    let jpName := Name.mkSimple s!"jp_{n}"
    let hName := Name.mkSimple s!"hjp_{n}"
    let (mainM, hvM) ← withLocalDeclD jpName T fun jp => do
      let hypT ← forallTelescope T fun xs _ => mkForallFVars xs (mkApp hdr (mkAppN jp xs))
      let bodyT := mkApp hdr (p.letBody!.instantiate1 jp)
      let mainT ← withLocalDeclD hName hypT fun hj => mkForallFVars #[jp, hj] bodyT
      let hvT ← forallTelescope T fun xs _ => mkForallFVars xs (mkApp hdr (mkAppN p.letValue! xs).headBeta)
      let mainM ← mkFreshExprSyntheticOpaqueMVar mainT
      let hvM ← mkFreshExprSyntheticOpaqueMVar hvT
      return (mainM, hvM)
    g.assign (mkApp2 mainM p.letValue! hvM)
    let (_, g1) ← mainM.mvarId!.intro jpName
    let (_, g2) ← g1.intro hName
    replaceMainGoal [g2, hvM.mvarId!]
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
  match fn with
  | .const c _ =>
    if c == ``Bind.bind then
      -- `getCompilerState >>= f` (the read context carries provenance)
      if (p.getArg! 4).consumeMData.isConstOf ``Sparkle.Compiler.Elab.CompilerM.getCompilerState then
        if ← runTac (← `(tactic| refine Tools.ShippingChildTranslateA.KeepsCP.bindCtx (fun _ _ => ?_))) then
          return true
      -- (rt175) a FUSED pair `liftMetaM (liftM (IO.eprintln _)) >>= fun _ => liftMetaM _` (the stderr pair): a given rule with head `bind`
      do
        let a4 := (p.getArg! 4).consumeMData
        if a4.isAppOf ``Sparkle.Compiler.Elab.CompilerM.liftMetaM then
          let inner := a4.appArg!.consumeMData
          if inner.isAppOf ``liftM && inner.appArg!.consumeMData.getAppFn.constName? == some ``IO.eprintln then
            for (_, h, stx) in rules do
              if h == ``Bind.bind then
                if ← runTac ⟨← `(tactic| (apply $(⟨stx⟩) <;> first | assumption | skip))⟩ then
                  return true
      if ty.consumeMData.isAppOf ``Tools.ShippingChildInv.Keeps then
        return ← runTac (← `(tactic| refine Tools.ShippingChildInv.Keeps.bind ?_ (fun _ => ?_)))
      -- (rt174) the inline attempt: its caught exception goes to the continuation (hypothesis `htri`)
      if ((p.getArg! 4).consumeMData.getAppFn.constName?.map (·.toString.endsWith "tryInlineUnfold")).getD false then
        if ← runTac (← `(tactic| refine Tools.ShippingChildWalkA.KeepsCP.bindCaught (by assumption) (fun _ _ => ?_))) then
          return true
      -- (rt175) only for a context read (the defeq test of `bindRead` against a large `tryCatch` program timed out)
      if [``MonadReader.read, ``read, ``MonadReaderOf.read, ``readThe].contains
          ((p.getArg! 4).consumeMData.getAppFn.constName?.getD .anonymous) then
        if ← runTac (← `(tactic| refine Tools.ShippingChildWalkA.KeepsCP.bindRead (fun _ _ => ?_))) then
          return true
      return ← runTac (← `(tactic| refine Tools.ShippingChildTranslateA.KeepsCP.bind ?_ (fun _ => ?_)))
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
      return ← runTac (← `(tactic| refine Tools.ShippingChildTranslateA.KeepsCP.ite (fun _ => ?_) (fun _ => ?_)))
    if c == ``dite then
      return ← runTac (← `(tactic| refine Tools.ShippingChildTranslateA.KeepsCP.dite (fun _ => ?_) (fun _ => ?_)))
    if c == ``Pure.pure then
      return ← runTac (← `(tactic| exact Tools.ShippingChildTranslateA.KeepsCP.pure _))
    if c == ``MonadExcept.throw || c == ``throw then
      if ← runTac (← `(tactic| exact Tools.ShippingChildTranslateA.KeepsCP.throw _ (by okmsg))) then return true
      return ← runTac (← `(tactic| exact Tools.ShippingChildWalkA.KeepsCP.throwE _))
    if (c == ``MonadExcept.tryCatch || c == ``tryCatchThe || c == ``MonadExceptOf.tryCatch) &&
        ty.consumeMData.isAppOf ``Tools.ShippingChildInv.Keeps then
      if ← runTac (← `(tactic| refine Tools.ShippingChildInv.Keeps.tryCatch ?_ (fun _ _ => ?_))) then return true
    if c == ``Except.rec then
      if ty.consumeMData.isAppOf ``Tools.ShippingChildInv.Keeps then
        return ← runTac (← `(tactic| (rename_i x; cases x <;> exact Tools.ShippingChildInv.Keeps.pure _)))
      return ← runTac (← `(tactic| (rename_i x; cases x <;> exact Tools.ShippingChildTranslateA.KeepsCP.pure _)))
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
    if ty.consumeMData.isAppOf ``Tools.ShippingChildInv.Keeps then
      let O := mkIdent `O; let hA := mkIdent `hA; let hS := mkIdent `hS
      if ← runTac (← `(tactic| exact Tools.ShippingChildVCA.keepsA_framed $O $hA $hS (by constructor))) then
        return true
      if ← runTac (← `(tactic| exact Tools.ShippingChildVCA.keepsA_framed $O $hA $hS (by constructor <;> first | constructor | assumption))) then
        return true
      if ← runTac (← `(tactic| exact Tools.ShippingChildVCA.keepsA_diag $O $hA $hS (by constructor))) then
        return true
    if c == ``Sparkle.Compiler.Elab.CompilerM.liftMetaM then
      return ← runTac (← `(tactic| refine Tools.ShippingChildTranslateA.KeepsCP.lift ?_))
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
          let t := mkIdent (`Tools.ShippingChildWalkA.KeepsCP ++ lm)
          if ← runTac (← `(tactic| refine $t ?_)) then return true
      if c == ``ST.Ref.get then
        if ← runTac (← `(tactic| refine Tools.ShippingChildWalkA.KeepsCP.refGet ?_)) then return true
      if c == ``ST.Ref.set then
        if ← runTac (← `(tactic| refine Tools.ShippingChildWalkA.KeepsCP.refSet ?_)) then return true
      if c == ``ST.Ref.modify then
        if ← runTac (← `(tactic| refine Tools.ShippingChildWalkA.KeepsCP.refModify ?_)) then return true
      if c == ``MonadReader.read || c == ``read || c == ``MonadReaderOf.read then
        if ← runTac (← `(tactic| exact Tools.ShippingChildWalkA.KeepsCP.read)) then return true
    -- (rt177) `withLocalDecl n ty k`: a dedicated step (first-order unification of `n ty k` only; the continuation
    -- goal is opened with `fun _ _ _ x => ?_`, so no `assumption`/defeq test is run against the large `k`)
    if c == ``Sparkle.Compiler.Elab.CompilerM.withLocalDecl && !ty.consumeMData.isAppOf ``Tools.ShippingChildInv.Keeps then
      let M := mkIdent `M; let hS := mkIdent `hS; let hA := mkIdent `hA
      let wl := mkIdent `Tools.ShippingGen4KWalkLegacyH4.withLocalDeclPK
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
        if (← IO.getEnv "KWALK_DEBUG").isSome then logInfo m!"kwalk framed-fallback: head {c} inner {ih} p {p.approxDepth}"
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
      if ← runTac (← `(tactic| apply Tools.ShippingChildWalkA.KeepsCP.forIn_array)) true then return true
      if ← runTac (← `(tactic| apply Tools.ShippingChildWalkA.KeepsCP.forIn_list)) true then return true
      if ← runTac (← `(tactic| apply Tools.ShippingChildWalkA.KeepsCP.forIn_range)) true then return true
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

/-- Walk every open goal until no step applies (bounded). (rt176) A goal on which no step applies is set aside for
good (`stuck`) and not retried in later rounds: retrying every stuck goal each round made the cost quadratic in the
number of steps (H11: 1189 steps used 4M heartbeats). -/
partial def kloop (rules : Array (Lean.Expr × Name × Syntax)) (fuel : Nat) (stuck : List MVarId := []) : TacticM Unit := do
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
  if progress then kloop rules (fuel - 1) stuck'

def runKWalkN (ts : Array Syntax) : TacticM Unit := withMainContext do
  let mut rules : Array (Lean.Expr × Name × Syntax) := #[]
  for t in ts do
    let e ← Term.withoutErrToSorry <| Tactic.elabTerm t none (mayPostpone := true)
    if let some h ← ruleHead e then
      rules := rules.push (e, h, t)
  kloop rules 400

elab "kwalkN" " [" ts:term,* "]" : tactic => runKWalkN (ts.getElems.map (·.raw))
elab "kwalkN" : tactic => runKWalkN #[]

end Tools.ShippingGen4KWalkTac2
