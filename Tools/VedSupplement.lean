import Lean
import Tools.VedStrictAudit

/-!
# A user-supplied, already proved lemma for ONE automatically generated local condition (sparkle-ved-proof-supplement)

Entry (option, default off): `set_option ved.mem.userLemma "Ns.myLemma" in #ved_u1_mem d`.  `Tools.VedMemLoop.ved_loop_unfold_mem`
reads the option at the causal side condition `hS` of the strong fixpoint equation of a memory loop (the condition after
`clearOthers`, its local context is the fvars its type mentions) and, when the option names a constant, closes that condition with
`applyUserLemma` INSTEAD of the automatic discharge of exactly that condition (`ved_causal_dag` / `ved_causal_simp` and the loop-size
gate are not run for it).  Option empty (default): nothing changes.

`applyUserLemma g c` accepts the constant `c` only if

1. `c` is a THEOREM whose reachable axiom closure is within the standard three (`Tools.VedStrictAudit.strictAudit`: not a def/axiom,
   no mvars, no `sorryAx`, no `Lean.ofReduceBool` / `native_decide` auxiliaries, no user axiom);
2. the type of `c` instantiated by metavariables for its leading binders is `isDefEq` to the goal's FULL type, in the goal's own local
   context (`g.withContext`; an mvar can only be assigned a term of that context, so a lemma cannot capture a variable it does not
   see, and a binder dependency of the goal must be met by the lemma's statement);
3. afterwards every binder mvar of the lemma is assigned (a hypothesis of the lemma that the match does not determine, i.e. an unproved
   condition, is refused: it is never turned into a new goal or hypothesis) and the instantiated proof term has no mvar;
4. the type inferred for the instantiated proof term is again `isDefEq` to the goal type.

The name is only a way to find the constant; nothing is decided by the name or by a hash of the goal.  A mismatch, a missing constant,
a non-std3 lemma or leftover mvars THROW (a refusal of the entry, stage `proof`); there is no silent fall back to the automation once a
lemma was specified.  The proof the entry builds contains the constant `c`; the final theorem keeps its registered statement, binders
and artifact, and the existing audit of the final theorem (std3 closure, stored type `==` the statement) covers `c` through the closure.
No component is trusted: the kernel checks the final theorem including `c`'s proof term.

`lastRun` records, for the Checks, how long the match took and whether a lemma was applied; it is diagnosis only and decides nothing.
-/

open Lean Meta

namespace Tools.VedSupplement

/-- the public option: the name of a constant (theorem) that closes the causal side condition of the memory loop; "" = off -/
register_option ved.mem.userLemma : String := {
  defValue := ""
  descr := "name of an already proved theorem that closes the causal side condition of a memory loop (matched by `isDefEq` against the goal's full type in its local context; std3 axioms only); empty = the automatic discharge"
}

/-- diagnosis for the Checks: (lemma name, ms spent in the match) of each application, and the generation / kernel ms of the last
memory-entry proof (`Tools.VedMemEntry.checkMemE`) -/
structure Run where
  applied : Array (Name × Nat) := #[]
  genMs : Nat := 0
  kernelMs : Nat := 0
  deriving Inhabited

initialize lastRun : IO.Ref Run ← IO.mkRef {}

/-- the constant the option names ("" = none); a name that does not resolve is a refusal when it is used -/
def optionLemma (o : Options) : Option Name :=
  let s := ved.mem.userLemma.get o
  if s.isEmpty then none else some s.toName

/-- close `g` with the theorem `c` (see the module comment for the checks); throws on every refusal -/
def applyUserLemma (g : MVarId) (c : Name) : MetaM Unit := do
  let t0 ← IO.monoMsNow
  let env ← getEnv
  let some ci := env.find? c
    | throwError "ved user lemma: unknown constant {c}"
  unless ci matches .thmInfo _ do
    throwError "ved user lemma: {c} is not a theorem"
  if (← g.isAssigned) then throwError "ved user lemma: the goal is already assigned"
  -- 1. std3 closure of the lemma (reachable axioms, no mvars)
  try discard <| Tools.VedStrictAudit.strictAudit c
  catch e => throwError "ved user lemma: {c} refused by the strict audit: {e.toMessageData}"
  g.withContext do
    let goalTy ← instantiateMVars (← g.getType)
    -- 2. the lemma's statement against the goal's full type, in the goal's context
    let lvls ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
    let lem := Expr.const c lvls
    -- the lemma's leading binders are the parameters of its statement (here the inputs of the design); the first count `k` of them
    -- that makes the rest `isDefEq` to the goal's type is taken (a lemma may not be matched against a prefix of the goal's own binders
    -- by instantiating them: `k` binders are instantiated, the goal keeps all its own)
    let lemTy ← inferType lem
    let arity := (← forallMetaTelescopeReducing lemTy).2.1.size
    let mut found : Option (Array Expr) := none
    let mut lastBody : Expr := lemTy
    for k in [0:arity + 1] do
      let st ← saveState
      let (ms, _, body) ← forallMetaBoundedTelescope lemTy k
      lastBody := body
      if (← isDefEq body goalTy) then
        found := some ms
        break
      st.restore
    let some ms := found
      | throwError "ved user lemma: the type of {c} does not match the goal.\nlemma: {← ppExpr lemTy}\ngoal:  {← ppExpr goalTy}"
    -- 3. no binder of the lemma is left unassigned (an unproved condition is not turned into a hypothesis or a goal)
    let pf ← instantiateMVars (mkAppN lem ms)
    for m in ms do
      let m' ← instantiateMVars m
      if m'.hasExprMVar then
        throwError "ved user lemma: {c} leaves a binder undetermined by the match ({← ppExpr m'}); an unproved hypothesis is refused"
    if pf.hasExprMVar then throwError "ved user lemma: the instantiated proof of {c} has unassigned metavariables"
    let pf ← instantiateMVars pf
    if pf.hasLevelMVar then throwError "ved user lemma: the universe levels of {c} are not determined by the match"
    -- 4. the instantiated proof really proves the goal type
    unless (← isDefEq (← inferType pf) goalTy) do
      throwError "ved user lemma: the instantiated proof of {c} does not have the goal's type"
    g.assign pf
  let ms := (← IO.monoMsNow) - t0
  lastRun.modify fun r => { r with applied := r.applied.push (c, ms) }

end Tools.VedSupplement
