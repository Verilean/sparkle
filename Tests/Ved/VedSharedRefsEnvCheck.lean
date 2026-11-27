import Sparkle
import Sparkle.Compiler.Elab
import Tools.VedMemEntry
import Tools.VedMemPack

/-!
# Residual hazards of the process-wide VED caches (follow-up of `VedSharedRefsCheck`)

Each control forces the hazard deterministically; a control that passes on the code before the fix would be vacuous.

1. `proofCache` (`proveRead`): a failure is a property of the statement AND the budget (here the recursion depth that `ved_omega`, the side-condition
   discharger of `ved_pack_simp`, turns into an ordinary failure).  A failure under a small budget must not be handed to a run with the normal one.
2. A cached proof (`proofCache`, `vedOmegaOk`) that mentions a non-imported auxiliary constant is reused only where a constant of that name has the
   type (and, for a definition, the value) it had when the proof was stored.
3. `declWidthTab`: the table of a module constant is answered only while the constant has the value the table was computed from.
-/

namespace Tests.Ved.VedSharedRefsEnvCheck

open Lean Elab Command Term Meta Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Access to the caches (the only part that knows their shape) -/

/-- store `p` for the closed statement, with the signatures of its non-imported constants as they are now (what the code stores after a proof) -/
def seedProof (closed : Expr) (p : Expr) : CoreM Unit := do
  let sigs ← Tools.VedU1ScriptSeq.constSigs p
  Tools.VedMemPack.proofCache.modify (·.insert closed (.proof p sigs))

def seedOmegaOk (tgt p : Expr) : CoreM Unit := do
  Tools.VedU1ScriptSeq.vedOmegaOk.modify (·.insert tgt { proof := p, used := #[], sigs := ← Tools.VedU1ScriptSeq.constSigs p })

/-- the table of the module constant `mn` as `checkMemE` stores it: with the value `mn` has now -/
def seedWidthTab (mn : Name) (tab : Std.HashMap String Nat) : CoreM Unit := do
  let some v := (← getEnv).find? mn |>.bind (·.value?) | throwError "{mn} has no value"
  Tools.VedMemLoop.declWidthTab.modify (·.insert mn (v, tab))

/-! ## 1. a failure under a small budget -/

/-- the statement `(a * (n + 1) + b) / (n + 1) = a` for `b : Fin (n + 1)`: `ved_pack_simp` proves it (`div_pack`, `div_eq_of_lt`; `ved_omega` discharges `0 < n + 1` and `b < n + 1`), plain
`omega` cannot (`a * (n + 1)` is not linear), so a run that exhausts the recursion budget inside `ved_omega` fails as a whole -/
def bigRead (a n b : Expr) : MetaM (Expr × Expr) := do
  let m ← mkAdd n (mkNatLit 1)
  let S ← mkAppM ``HDiv.hDiv #[← mkAdd (← mkAppM ``HMul.hMul #[a, m]) (← mkAppM ``Fin.val #[b]), m]
  return (S, a)

/-- `proveRead` under a recursion limit `k` above the current depth, for every `k` below 300: where it fails (an ordinary failure: `ved_omega` turns the exhausted
recursion budget into one; at other limits the run throws or succeeds), the next run with the normal limit must prove the statement.  At least one `k` must fail
(else the control is vacuous). -/
elab "sr_budget" : tactic => withMainContext do
  let lctx ← getLCtx
  let some a := lctx.findFromUserName? `a | throwError "no a"
  let some n := lctx.findFromUserName? `n | throwError "no n"
  let some b := lctx.findFromUserName? `b | throwError "no b"
  let (S, F) ← bigRead a.toExpr n.toExpr b.toExpr
  Tools.VedMemPack.proofCache.set {}
  if (← Tools.VedMemPack.proveRead S F).isNone then throwError "proveRead: no proof with the normal budget (vacuous control)"
  logInfo m!"SR1 normal budget: proved; maxRecDepth {(← readThe Core.Context).maxRecDepth} current {(← readThe Core.Context).currRecDepth}"
  let mut failedAt : Array Nat := #[]
  let mut handed : Array Nat := #[]
  let mut outcomes : Array Char := #[]
  for k in List.range 300 do
    Tools.VedMemPack.proofCache.set {}
    let goals ← getGoals
    let r ← tryCatchRuntimeEx
        (withTheReader Core.Context (fun c => { c with maxRecDepth := c.currRecDepth + k }) (Tools.VedMemPack.proveRead S F))
        fun _ => pure (some (mkConst `SrBudget.threw))
    setGoals goals
    outcomes := outcomes.push (if r.isNone then 'n' else if r.any (·.isConstOf `SrBudget.threw) then 't' else 's')
    if r.isNone then
      failedAt := failedAt.push k
      if (← Tools.VedMemPack.proveRead S F).isNone then handed := handed.push k
  Tools.VedMemPack.proofCache.set {}
  logInfo m!"SR1 outcomes (n failure, t threw, s success) for k = 0..: {String.mk outcomes.toList}"
  if failedAt.isEmpty then throwError "proofCache budget: no limit gave an ordinary failure (vacuous control)"
  logInfo m!"SR1 failures at recursion limits {failedAt}; handed to the normal run at {handed}"
  unless handed.isEmpty do throwError "proofCache: a failure under a small budget was handed to a run with the normal budget (limits {handed})"
  if (← Tools.VedMemPack.proveRead S F).isNone then throwError "proveRead: no proof with the normal budget (vacuous control)"
  Tools.VedMemPack.proofCache.set {}

example (a n : Nat) (b : Fin (n + 1)) : True := by sr_budget; trivial

/-! ## 2. a same-named auxiliary constant of another type -/

/-- add `SrAux.p : ty := val` (a theorem) to the environment -/
def addAux (ty val : Expr) : CoreM Unit :=
  addDecl (.thmDecl { name := `SrAux.p, levelParams := [], type := ty, value := val })

/-- run `act` in the environment extended by `SrAux.p : 0 = 0`, then drop that environment and add `SrAux.p : 1 = 1` (a backtracked branch, or another declaration, that made the
name again) -/
def withRebuiltAux (first : MetaM α) : MetaM Unit := do
  let n0 := mkNatLit 0
  let n1 := mkNatLit 1
  let env0 ← getEnv
  addAux (← mkEq n0 n0) (← mkEqRefl n0)
  let _ ← first
  setEnv env0
  addAux (← mkEq n1 n1) (← mkEqRefl n1)

elab "sr_proofcache_type" : tactic => withMainContext do
  let some (_, S, F) := (← instantiateMVars (← getMainTarget)).eq? | throwError "not an equation"
  let eq ← mkEq S F
  let fvs ← Tools.VedMemPack.closure eq
  let closed ← mkForallFVars fvs eq
  Tools.VedMemPack.proofCache.set {}
  let env ← getEnv
  withRebuiltAux (seedProof closed (mkConst `SrAux.p))
  let some p ← Tools.VedMemPack.proveRead S F | throwError "proveRead: no proof"
  if p.getUsedConstants.contains `SrAux.p then throwError "proofCache: a hit handed out a proof of the constant SrAux.p that has another type now"
  Tools.VedMemPack.proofCache.set {}
  setEnv env
  (← getMainGoal).assign p

example (x : Nat) : x + 0 = x := by sr_proofcache_type

elab "sr_omegaok_type" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt := (← instantiateMVars (← g.getType)).consumeMData
  evalTactic (← `(tactic| ved_omega_c_reset))
  let env ← getEnv
  withRebuiltAux (seedOmegaOk tgt (mkConst `SrAux.p))
  evalTactic (← `(tactic| ved_omega_c))
  let v ← instantiateMVars (mkMVar g)
  if v.getUsedConstants.contains `SrAux.p then throwError "vedOmegaOk: a hit handed out a proof of the constant SrAux.p that has another type now"
  evalTactic (← `(tactic| ved_omega_c_reset))

example (x y : Nat) (h : x < 8) : x + y < y + 8 := by sr_omegaok_type

/-! ## 2b. a reader whose two reads straddle the write of another task (the proof and its signatures are read separately) -/

/-- `SrAux.p : dom → True := fun _ => True.intro` -/
def addAuxFun (dom : Expr) : CoreM Unit :=
  addAux (mkForall `x .default dom (Lean.mkConst ``True)) (mkLambda `x .default dom (Lean.mkConst ``True.intro))

run_cmd liftTermElabM do
  let env0 ← getEnv
  let tgt := Lean.mkConst ``True
  -- task A: `SrAux.p : Nat → True`; its proof of `True` and the signatures are stored
  addAuxFun (Lean.mkConst ``Nat)
  let pfA := mkApp (Lean.mkConst `SrAux.p) (mkNatLit 0)
  unless (← isDefEq (← inferType pfA) tgt) do throwError "SR2b: proof A does not check in environment A (vacuous control)"
  let sigsA ← Tools.VedU1ScriptSeq.constSigs pfA
  seedOmegaOk tgt pfA
  -- task B (another environment): `SrAux.p : Bool → True`
  setEnv env0
  addAuxFun (Lean.mkConst ``Bool)
  let pfB := mkApp (Lean.mkConst `SrAux.p) (Lean.mkConst ``Bool.true)
  unless (← isDefEq (← inferType pfB) tgt) do throwError "SR2b: proof B does not check in environment B (vacuous control)"
  let sigsB ← Tools.VedU1ScriptSeq.constSigs pfB
  let entryB : Tools.VedU1ScriptSeq.OmegaOkEntry := { proof := pfB, used := #[], sigs := sigsB }
  let writeB : IO Unit := Tools.VedU1ScriptSeq.vedOmegaOk.modify (·.insert tgt entryB)
  let readEntry : IO (Option Tools.VedU1ScriptSeq.OmegaOkEntry) := do return (← Tools.VedU1ScriptSeq.vedOmegaOk.get)[tgt]?
  -- the reader (environment B) has one read; the write of B comes before it or after it, there is no point between proof and signatures
  let hitAfterB ← Tools.VedU1ScriptSeq.omegaOkHit {} (do writeB; readEntry)
  unless hitAfterB == some pfB do throwError "SR2b: the read after the write of B did not hit proof B"
  let eA : Tools.VedU1ScriptSeq.OmegaOkEntry := { proof := pfA, used := #[], sigs := sigsA }
  Tools.VedU1ScriptSeq.vedOmegaOk.modify (·.insert tgt eA)
  let hitBeforeB ← Tools.VedU1ScriptSeq.omegaOkHit {} (do let e ← readEntry; writeB; return e)
  -- the read before the write sees entry A: its proof with ITS signatures, which environment B rejects
  if hitBeforeB.isSome then throwError "SR2b: the read before the write of B hit {hitBeforeB} in environment B (the entry of A is not valid here)"
  -- each entry is consistent in itself: A's pair is rejected and B's accepted in environment B; the mixed pair (A's proof, B's signatures) has no
  -- representation any more (one entry per target, one read per hit)
  if (← Tools.VedU1ScriptSeq.constsMatch eA.proof eA.sigs) then throwError "SR2b: the pair of A passes in environment B"
  unless (← Tools.VedU1ScriptSeq.constsMatch entryB.proof entryB.sigs) do throwError "SR2b: the pair of B fails in environment B"
  logInfo m!"SR2b a reader sees the entry of A (rejected in environment B) or the entry of B (hit): no mixed pair"

/-! ## 3. a module constant re-declared with another value -/

def srWMod (k : Nat) : Sparkle.IR.AST.Module :=
  { name := "m", inputs := [], outputs := [], wires := [{ name := "w", ty := .bitVector k }], body := [] }

/-- the table `checkMemE` builds for a module -/
def tableOf (m : Sparkle.IR.AST.Module) : Std.HashMap String Nat :=
  m.wires.foldl (fun t p => if t.contains p.name then t else t.insert p.name (Tools.VedU1Contract.declWidth m p.name)) {}

/-- what the pre-simproc answers for `declWidth SrW.m "w"` (`none`: it does not answer) -/
def answerOf : MetaM (Option Nat) := do
  let e := mkApp2 (mkConst ``Tools.VedU1Contract.declWidth) (mkConst `SrW.m) (mkStrLit "w")
  let ctx ← Simp.mkContext (simpTheorems := #[])
  let (r, _) ← Simp.main e ctx (methods := { pre := Tools.VedMemLoop.declWidthAnswer })
  return r.expr.nat?

def addWMod (k : Nat) : CoreM Unit :=
  addDecl (.defnDecl { name := `SrW.m, levelParams := [], type := mkConst ``Sparkle.IR.AST.Module, value := mkApp (mkConst ``srWMod) (mkNatLit k),
                       hints := .abbrev, safety := .safe })

run_cmd liftTermElabM do
  let env0 ← getEnv
  addWMod 3
  let m := srWMod 3
  seedWidthTab `SrW.m (tableOf m)
  unless (← answerOf) == some 3 do throwError "declWidthTab: the table does not answer for the constant it was built from (vacuous control)"
  -- the command that declared `SrW.m` fails and is rolled back; the name is made again with another value
  setEnv env0
  addWMod 5
  match (← answerOf) with
  | some 3 => throwError "declWidthTab: the table of the rolled-back SrW.m (width 3) answers for the new SrW.m (width 5)"
  | _ => logInfo m!"SR3 the stale table is not used"

end Tests.Ved.VedSharedRefsEnvCheck
