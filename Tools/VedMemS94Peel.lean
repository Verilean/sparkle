import Lean
import Tools.VedMem

/-!
# A DAG-aware memory peel (`ved.mem.s94PeelDag`)

Observed (sparkle-ved-mem-s94, eleventh unit): after the memory loop's case split the goal `MemInv name .. (n+1) arr` has an
`arr` that is a DAG (nested updates of all the memories, the update of memory `k+1` pushed under both branches of the
`if en_k then upd_k else hold_k` of memory `k`), and `ved_mem_peel` walks it as a TREE: `3·2^27 - 2` steps per goal on R033.

`MemInv name ..` reads the array at `name` only.  `ved_mem_peel_dag h0 h1 ..` (this file) first PROJECTS the array on `name`:

* `pj name M := M name` (a function `Nat → Nat`), and for every node `e` of `arr` (a memo table keyed by the expression, so a shared
  node is visited once) an array `e'` with a proof of `pj name e = pj name e'`:
  an atom is kept; the update of ANOTHER memory (a different string literal) is dropped (`proj_other`); the update of this memory keeps its
  shape over the projected rest (`proj_self`); `if c then T else E` becomes `if c then T' else E'`, or just `T'` when `T'` and `E'` are the
  same expression (`proj_ite_same`, `proj_ite`);
* `MemInv.of_proj` turns the goal into `MemInv name .. (n+1) arr'`, where `arr'` is the chain of this memory's own writes (one `if` per
  write port), and the old leaves (`MemInv.ite`, `MemInv.write_leaf`, `MemInv.hold_leaf`, `exact h`) close it; the side goals
  (`hen`, `hav`, `hdv`) are left to the caller exactly as `ved_mem_peel` leaves them.

Nothing here is an axiom.  A shape that is not understood (an atom that is not a variable, a payload that is not a literal pair of names,
a memory name that is not a string literal) makes the tactic fail; the caller's `first | .. | ved_mem_peel ..` runs the old peel.
-/

namespace Tools.VedMemS94Peel

open Lean Meta Elab Tactic Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal

/-- the contents of one memory in an array of the IR semantics -/
def pj (name : String) (M : MEnv) : Nat → Nat := M name

theorem proj_ite_same {name : String} {c : Prop} {inst : Decidable c} {T E X : MEnv}
    (hT : pj name T = pj name X) (hE : pj name E = pj name X) :
    pj name (@ite MEnv c inst T E) = pj name X := by
  unfold pj at *
  by_cases hc : c
  · rw [if_pos hc]; exact hT
  · rw [if_neg hc]; exact hE

theorem proj_ite {name : String} {c : Prop} {inst : Decidable c} {T E T' E' : MEnv}
    (hT : pj name T = pj name T') (hE : pj name E = pj name E') :
    pj name (@ite MEnv c inst T E) = pj name (@ite MEnv c inst T' E') := by
  unfold pj at *
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]; exact hT
  · rw [if_neg hc, if_neg hc]; exact hE

/-- the update of ANOTHER memory is invisible -/
theorem proj_other {name other : String} {a v : Nat} {M M' : MEnv}
    {inst : ∀ (nm : String) (i : Nat), Decidable (nm = other ∧ i = a)}
    (hne : other ≠ name) (h : pj name M = pj name M') :
    pj name (fun nm i => @ite Nat (nm = other ∧ i = a) (inst nm i) v (M nm i)) = pj name M' := by
  funext i
  have hn : ¬ (name = other ∧ i = a) := fun hh => hne hh.1.symm
  show (@ite Nat (name = other ∧ i = a) (inst name i) v (M name i)) = M' name i
  rw [if_neg hn]
  exact congrFun h i

/-- the update of THIS memory: the projection commutes with the rest -/
theorem proj_self {name : String} {a v : Nat} {M M' : MEnv}
    {inst : ∀ (nm : String) (i : Nat), Decidable (nm = name ∧ i = a)}
    (h : pj name M = pj name M') :
    pj name (fun nm i => @ite Nat (nm = name ∧ i = a) (inst nm i) v (M nm i))
      = pj name (fun nm i => @ite Nat (nm = name ∧ i = a) (inst nm i) v (M' nm i)) := by
  funext i
  show (@ite Nat (name = name ∧ i = a) (inst name i) v (M name i))
    = (@ite Nat (name = name ∧ i = a) (inst name i) v (M' name i))
  have hi : M name i = M' name i := congrFun h i
  rw [hi]

theorem memInv_of_proj {dom : DomainConfig} {aw dw : Nat} {name : String} {init : BitVec aw → BitVec dw}
    {wa : Signal dom (BitVec aw)} {wd : Signal dom (BitVec dw)} {we : Signal dom Bool} {n : Nat}
    {M M' : MEnv} (hp : pj name M = pj name M') (h : Tools.VedMem.MemInv name init wa wd we n M') :
    Tools.VedMem.MemInv name init wa wd we n M := by
  intro i hi
  have := congrFun hp i
  unfold pj at this
  rw [this]
  exact h i hi

register_option ved.mem.s94PeelDag : Bool := {
  defValue := false
  descr := "the memory peel after the loop's case split projects the array on the memory's name first (shared nodes once, other memories' updates dropped); the old peel is the fallback"
}

/-- number of runs of the DAG peel that completed (test counter) -/
initialize peelDagHits : IO.Ref Nat ← IO.mkRef 0

/-- test seam (never set by production code): the DAG peel refuses, the old peel is the fallback -/
initialize peelDagRefuse : IO.Ref Bool ← IO.mkRef false

/-- test seam: the DAG peel fails after its work (the state is restored by the caller's `first`) -/
initialize peelDagFailLate : IO.Ref Bool ← IO.mkRef false

/-- the projection of `e` (see the header): `(e', proof of pj name e = pj name e')`, a node once -/
partial def projArr (nameE : Expr) (nameS : String) (e : Expr) :
    StateRefT (Std.HashMap Expr (Expr × Expr)) MetaM (Expr × Expr) := do
  if let some r := (← get)[e]? then return r
  let r ← go e
  modify (·.insert e r)
  return r
where
  pjE (x : Expr) : Expr := mkApp2 (mkConst ``pj) nameE x
  go (e : Expr) : StateRefT (Std.HashMap Expr (Expr × Expr)) MetaM (Expr × Expr) := do
    let e0 := e.consumeMData
    if e0.isAppOfArity ``ite 5 then
      let c := e0.getArg! 1
      let inst := e0.getArg! 2
      let T := e0.getArg! 3
      let E := e0.getArg! 4
      let (T', pT) ← projArr nameE nameS T
      let (E', pE) ← projArr nameE nameS E
      if T' == E' then
        return (T', mkAppN (mkConst ``proj_ite_same) #[nameE, c, inst, T, E, T', pT, pE])
      else
        let e' := mkAppN e0.getAppFn #[e0.getArg! 0, c, inst, T', E']
        return (e', mkAppN (mkConst ``proj_ite) #[nameE, c, inst, T, E, T', E', pT, pE])
    else if e0.isLambda then
      let .lam n1 t1 (.lam n2 t2 body bi2) bi1 := e0 | throwError "ved_mem_peel_dag: an update that is not a binary function"
      unless body.isAppOfArity ``ite 5 do throwError "ved_mem_peel_dag: an update that is not an `if`"
      let cond := body.getArg! 1
      let inst := body.getArg! 2
      let v := body.getArg! 3
      let rest := body.getArg! 4
      unless cond.isAppOfArity ``And 2 do throwError "ved_mem_peel_dag: the test of an update is not a conjunction"
      let l := cond.appFn!.appArg!
      let r := cond.appArg!
      unless l.isAppOfArity ``Eq 3 && r.isAppOfArity ``Eq 3 do throwError "ved_mem_peel_dag: the test of an update is not `nm = other ∧ i = a`"
      let other := l.appArg!
      let a := r.appArg!
      unless l.appFn!.appArg! == .bvar 1 && r.appFn!.appArg! == .bvar 0 do
        throwError "ved_mem_peel_dag: the test of an update is not on its own arguments"
      unless !other.hasLooseBVars && !a.hasLooseBVars && !v.hasLooseBVars do
        throwError "ved_mem_peel_dag: an update whose parts depend on its arguments"
      let .app (.app Mx (.bvar 1)) (.bvar 0) := rest | throwError "ved_mem_peel_dag: the rest of an update is not `M nm i`"
      if Mx.hasLooseBVars then throwError "ved_mem_peel_dag: the rest of an update depends on its arguments"
      let .lit (.strVal otherS) := other | throwError "ved_mem_peel_dag: the memory of an update is not a string literal"
      let (Mx', pM) ← projArr nameE nameS Mx
      let instF := Expr.lam n1 t1 (.lam n2 t2 inst bi2) bi1
      if otherS == nameS then
        let rest' := Expr.app (Expr.app Mx' (.bvar 1)) (.bvar 0)
        let e' := Expr.lam n1 t1 (.lam n2 t2 (Expr.app body.appFn! rest') bi2) bi1
        return (e', mkAppN (mkConst ``proj_self) #[nameE, a, v, Mx, Mx', instF, pM])
      else
        let hne ← mkDecideProof (← mkAppM ``Ne #[other, nameE])
        return (Mx', mkAppN (mkConst ``proj_other) #[nameE, other, a, v, Mx, Mx', instF, hne, pM])
    else if e0.isFVar then
      return (e, mkApp2 (mkConst ``Eq.refl [1]) (← mkArrow (mkConst ``Nat) (mkConst ``Nat)) (pjE e))
    else
      throwError "ved_mem_peel_dag: an array that is neither an `if`, an update nor a variable"

/-- close `MemInv name .. n' arr'` (the projected array: `if`s, updates of this memory, a variable) with the leaves of `ved_mem_peel`;
returns the side goals in the order the old peel leaves them -/
partial def closeGo (hs : Array Expr) (g : MVarId) : TacticM (List MVarId) := do
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    unless tgt.isAppOf ``Tools.VedMem.MemInv do throwError "ved_mem_peel_dag: not a MemInv goal"
    let arr := (tgt.getArg! (tgt.getAppNumArgs - 1)).consumeMData
    let refineWith (stx : TSyntax `tactic) : TacticM (List MVarId) := do
      setGoals [g]
      evalTactic stx
      getGoals
    if arr.isFVar then
      for h in hs do
        let hty ← instantiateMVars (← inferType h)
        if (← withReducible (isDefEq tgt hty)) then
          g.assign h
          return []
      let gs ← try refineWith (← `(tactic| refine Tools.VedMem.MemInv.hold_leaf ?_ ?_))
        catch _ => throwError "ved_mem_peel_dag: no invariant hypothesis matches the memory array (name, initial contents, ports and cycle must agree)"
      match gs with
      | [g1, hen] => return (← closeGo hs g1) ++ [hen]
      | _ => throwError "ved_mem_peel_dag: hold_leaf"
    else if arr.isAppOfArity ``ite 5 then
      let gs ← refineWith (← `(tactic| refine Tools.VedMem.MemInv.ite (fun _ => ?_) (fun _ => ?_)))
      match gs with
      | [g1, g2] => return (← closeGo hs g1) ++ (← closeGo hs g2)
      | _ => throwError "ved_mem_peel_dag: ite"
    else if arr.isLambda then
      let gs ← refineWith (← `(tactic| refine Tools.VedMem.MemInv.write_leaf ?_ ?_ ?_ ?_))
      match gs with
      | [g1, hen, hav, hdv] => return (← closeGo hs g1) ++ [hen, hav, hdv]
      | _ => throwError "ved_mem_peel_dag: write_leaf"
    else throwError "ved_mem_peel_dag: unexpected array"

syntax (name := vedMemPeelDag) "ved_mem_peel_dag" (ppSpace colGt ident)* : tactic

def evalVedMemPeelDagCore : Tactic := fun stx => withMainContext do
  if (← peelDagRefuse.get) then throwError "ved_mem_peel_dag: refused (test seam)"
  let g ← getMainGoal
  let restGoals := (← getGoals).drop 1
  let tgt0 ← g.getType
  -- a goal of another head is refused before anything else is touched (the goals are DAGs of tree size 1e13)
  unless tgt0.consumeMData.isAppOf ``Tools.VedMem.MemInv do throwError "ved_mem_peel_dag: not a MemInv goal"
  let tgt ← instantiateMVars tgt0
  unless tgt.isAppOf ``Tools.VedMem.MemInv && tgt.getAppNumArgs == 10 do throwError "ved_mem_peel_dag: not a MemInv goal"
  let nameE := tgt.getArg! 3
  let .lit (.strVal nameS) := nameE | throwError "ved_mem_peel_dag: the memory name is not a string literal"
  let arr := tgt.getArg! 9
  let hs ← (stx[1].getArgs.mapM fun i => do
    let some d := (← getLCtx).findFromUserName? i.getId | throwError "ved_mem_peel_dag: no hypothesis {i.getId}"
    pure d.toExpr)
  let ((arr', pf), _) ← (projArr nameE nameS arr).run {}
  let (xs, _, concl) ← forallMetaTelescope (← inferType (mkConst ``memInv_of_proj))
  unless xs.size ≥ 2 do throwError "ved_mem_peel_dag: of_proj"
  let ip := xs.size - 2
  unless (← isDefEq xs[ip]! pf) do throwError "ved_mem_peel_dag: the projection proof does not fit: {(← inferType xs[ip]!)} vs {(← inferType pf)} (xs {xs.size})"
  unless (← isDefEq concl tgt) do throwError "ved_mem_peel_dag: the goal is not the projection's conclusion"
  g.assign (mkAppN (mkConst ``memInv_of_proj) (xs.set! ip pf))
  let g1 := xs[ip + 1]!.mvarId!
  let side ← closeGo hs g1
  setGoals (side ++ restGoals)
  if (← peelDagFailLate.get) then throwError "ved_mem_peel_dag: failed late (test seam)"
  peelDagHits.modify (· + 1)

/-- the tactic; with `VED_DUMP_DIR` set a refusal is written to `addr.log` (diagnosis only) before it is rethrown -/
@[tactic vedMemPeelDag] def evalVedMemPeelDag : Tactic := fun stx => do
  try evalVedMemPeelDagCore stx
  catch ex =>
    if let some dir ← IO.getEnv "VED_DUMP_DIR" then
      let h ← IO.FS.Handle.mk s!"{dir}/addr.log" .append
      h.putStrLn s!"S94 peel_dag refused: {((← ex.toMessageData.toString).replace "\n" " ").take 300}"
    throw ex

end Tools.VedMemS94Peel
