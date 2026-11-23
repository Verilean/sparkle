import Lean
import Tools.VedMemLoop
import Tools.VedMemS94Local

/-!
# Opaque `memState` atoms for the local closers (`ved.mem.s94Opaque`, sparkle-ved-mem-s94, s94s)

Observed (s94r, `ved_tree_diag`): the 1e7 .. 3.5e7-node trees of the class-B goals are INSIDE the port arguments of the `memState` atoms
(`memState init writeAddr writeData writeEnable n addr`: the eight arguments before `addr` hold `Signal.mk (fun t => ..)` over `Signal.val (loop ..)`), while the arithmetic
of the goal only sees `memState .. addr : BitVec w` as an unknown word.  The size guard of the local closer (`ved_local_small`), `ved_cone_clear` and `omega` pay for those arguments
although no step ever opens them.

`ved_mem_opaque`: every distinct partial application `key = memState <8 arguments>` of the target (after the address step, `ved_mem_addr_l` / `memCanon` made two spellings
of one memory one key) is abstracted to a fresh variable `ved_M<i> : BitVec aw → BitVec dw`; the atoms become `ved_M<i> addr` (the address argument stays visible, and is itself
abstracted for the atoms it contains).  The abstraction is NOT a hypothesis-free weakening: the new goal is `∀ M, tgt[key := M]` and the old goal is closed by applying it to the
keys (the defining equation is `rfl`, kept aside as the proof term, nothing is added to the context), so a closer that proves the abstracted goal proves the original one,
and the kernel checks the instantiation.  The new route only (option `ved.mem.s94Opaque`, default false; the Entry hunk adds one stage step after the local route).
-/

namespace Tools.VedMemS94Opaque

open Lean Meta Elab Tactic Tools.VedU1WireShare

register_option ved.mem.s94Opaque : Bool := {
  defValue := false
  descr := "ved memory tail (class B): after the address step, abstract each distinct memState key (its eight port arguments) to a fresh variable before the local closer, so that no closer walks the port arguments; the old tail is the fallback (default false)"
}

/-- test seams / counters (LocalCheck) -/
initialize opaqueHits : IO.Ref Nat ← IO.mkRef 0
initialize opaqueRefuse : IO.Ref Bool ← IO.mkRef false
initialize opaqueFailLate : IO.Ref Bool ← IO.mkRef false

private def isMemAtom (x : Expr) : Bool :=
  x.isAppOf ``Sparkle.Core.Signal.Signal.memState && x.getAppNumArgs == 9 && !x.hasLooseBVars

/-- the target with every atom `memState a0 .. a7 addr` whose key is in `keys` replaced by `M addr` (the address abstracted by the same map); memoised, one visit per shared node -/
private partial def absGo (keys : Array (Expr × Expr)) (e : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
  if let some r := (← get)[e]? then return r
  let r ← do
    if isMemAtom e then
      let args := e.getAppArgs
      let key := mkAppN e.getAppFn (args.extract 0 8)
      match keys.find? (·.1 == key) with
      | some (_, m) => pure (mkApp m (← absGo keys args[8]!))
      | none => pure e
    else match e with
      | .app f a => pure (e.updateApp! (← absGo keys f) (← absGo keys a))
      | .lam _ t b _ => pure (e.updateLambdaE! (← absGo keys t) (← absGo keys b))
      | .forallE _ t b _ => pure (e.updateForallE! (← absGo keys t) (← absGo keys b))
      | .mdata _ b => pure (e.updateMData! (← absGo keys b))
      | .proj _ _ b => pure (e.updateProj! (← absGo keys b))
      | .letE n t v b nd => pure (Expr.letE n (← absGo keys t) (← absGo keys v) (← absGo keys b) nd)
      | _ => pure e
  modify (·.insert e r)
  return r

/-- abstract the distinct `memState` keys of the target; returns the new goal (the variables introduced) and their number (0: nothing to do, the goal is returned unchanged) -/
def memOpaque (g : MVarId) : MetaM (MVarId × Nat) := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let mut keys : Array Expr := #[]
  for o in collectDag isMemAtom tgt do
    let key := mkAppN o.getAppFn (o.getAppArgs.extract 0 8)
    unless keys.contains key do keys := keys.push key
  if keys.isEmpty then return (g, 0)
  let mut tys : Array Expr := #[]
  for k in keys do tys := tys.push (← inferType k)
  -- bound variables of the abstraction, as free variables of a local telescope
  let rec go (i : Nat) (acc : Array (Expr × Expr)) : MetaM Expr := do
    if h : i < keys.size then
      withLocalDeclD (Name.mkSimple s!"ved_M{i}") tys[i]! fun m => do
        let body ← go (i + 1) (acc.push (keys[i]!, m))
        mkForallFVars #[m] body
    else
      let (t', _) := (absGo acc tgt).run {}
      return t'
  let absTy ← go 0 #[]
  let g' ← mkFreshExprSyntheticOpaqueMVar absTy (← g.getTag)
  g.assign (mkAppN g' keys)
  let (_, g'') ← g'.mvarId!.introN keys.size ((List.range keys.size).map fun i => Name.mkSimple s!"ved_M{i}")
  return (g'', keys.size)

/-- `ved_mem_opaque`: see the module comment; fails when the target has no `memState` atom (nothing is changed then) -/
elab "ved_mem_opaque" : tactic => do
  if ← opaqueRefuse.get then throwError "ved_mem_opaque: refused (test seam)"
  let (g, n) ← memOpaque (← getMainGoal)
  if n == 0 then throwError "ved_mem_opaque: no memState atom in the target"
  opaqueHits.modify (· + 1)
  replaceMainGoal [g]
  if ← opaqueFailLate.get then throwError "ved_mem_opaque: failed after its work (test seam)"

/-- the class-B stage step: the opaque abstraction and the local closer on ONE goal; a goal that is not closed stays exactly as it was -/
macro "ved_mem_opaque_local" : tactic =>
  `(tactic| first | (ved_mem_opaque; ved_local_goal) | skip)

end Tools.VedMemS94Opaque
