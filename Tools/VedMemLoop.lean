import Lean
import Tools.VedMem
import Tools.VedU1Entry
import Tools.VedU1WireShare
import Tools.VedMemNest
import Tools.VedSupplement

/-!
# Loop unfolding for a loop body that holds a memory (`sparkle-ved-memory`)

`ved_loop_unfold_mem t` is `ved_loop_unfold_share t` (`Tools/VedU1WireShare.lean`) with the strong fixpoint
equation `Tools.VedMem.loop_val_unfold_strong` in place of `Tools.VedU1Loop.loop_val_unfold`: the loop body's
value at `t+1` may depend on its argument at every cycle `≤ t`, which is what a memory inside the body does.
The side condition is discharged by `ved_causal`: reduce both sides, replace each `memState` of the left side
by the one over the other argument (`Tools.VedMem.memState_congr`, its three side conditions are pointwise
equalities of the port signals, each follows from the agreement hypothesis), then rewrite the value at `t`.
Untrusted: the kernel checks the resulting proof.
-/

namespace Tools.VedMemLoop

open Lean Meta Elab Tactic Sparkle.Core.Signal

/-- run `x` with a local heartbeat budget of `n` (raw heartbeats) that never exceeds what is left of the ambient budget
(the rule of `ved_budget`, `Tools/VedU1Entry.lean` on ved/perf-r281): local max = min(remaining ambient, n), at least 1
(an exhausted ambient budget fails at once, never 0 = unlimited); with an unlimited ambient budget (0) the local `n` alone -/
def withLocalHb {α : Type} (n : Nat) (x : TacticM α) : TacticM α := do
  let hb ← IO.getNumHeartbeats
  withTheReader Core.Context (fun c =>
      let left := c.maxHeartbeats - (hb - c.initHeartbeats)
      { c with maxHeartbeats := if c.maxHeartbeats == 0 then n else max 1 (min left n), initHeartbeats := hb }) x

/-- `t` within a local budget of `n` thousand heartbeats (`withLocalHb`); when the budget runs out the tactic state is
restored to the one before `t` (a partial change does not reach the next alternative) and the failure is reported.
Other errors pass through (with the state restored as well). -/
elab "ved_mem_budget " n:num t:tactic : tactic => do
  let s ← saveState
  let ok ← tryCatchRuntimeEx (do withLocalHb (n.getNat * 1000) (Tactic.withoutRecover (evalTactic t)); pure true)
    fun e => do
      s.restore
      if e.isRuntime then pure false else throw e
  unless ok do throwError "ved_mem_budget: local heartbeat budget exhausted"

/-- `ved_no_recover t`: `t` with error recovery off, so that the first failing step (`case`, `all_goals`) ends the proof at once instead of
being logged and admitted while the remaining stages run (a refusal returns after the first error, not after the whole script). -/
elab "ved_no_recover " t:tactic : tactic => Tactic.withoutRecover (evalTactic t)

/-- the size gate of `ved_loop_unfold_mem` (heuristic limit, public option) -/
register_option ved.mem.loopGate : Nat := {
  defValue := 10000000
  descr := "refuse (stage proof) when a loop `ved_loop_unfold_mem` unfolds has a tree larger than this many nodes; 0 disables the gate (heuristic limit)"
}

/-- the local heartbeat limit of the memory loop's base case (`h0`) -/
register_option ved.mem.h0Budget : Nat := {
  defValue := 1000000
  descr := "refuse (stage proof) when the base case (h0) of the memory loop needs more than this many heartbeats, in the units of `maxHeartbeats`; 0 disables the limit (heuristic limit)"
}

/-- `ved_h0_budget n t`: `t` within the local heartbeat limit `n` (the public option `ved.mem.h0Budget`, read by the entry; the units of `maxHeartbeats`, like the `hb` of the stage stamps; `withLocalHb`, never above what is left of the
ambient budget).  The effective limit is `min(n, remaining ambient budget)` (`n = 0`: the remaining ambient budget alone, the local limit is off, the ambient budget is still enforced).  When a heartbeat limit stops `t` the tactic state is
restored and the refusal says that `t` did not finish within that minimum and which of the two was the smaller (it does not claim the local limit was too small when the ambient budget ended the run).  Other runtime exceptions
(recursion depth) and ordinary errors pass through with the state restored, classified as they are.  Observed there (stage stamps): 35-43k (R037/R038), 260k (R034); R028 spent the whole 8M budget (643 s) in it. -/
elab "ved_h0_budget " n:num t:tactic : tactic => do
  let n := n.getNat
  let s ← saveState
  let hb ← IO.getNumHeartbeats
  let c ← readThe Core.Context
  -- what is left of the ambient budget in the units of `maxHeartbeats` (`none`: unlimited)
  let left? : Option Nat := if c.maxHeartbeats == 0 then none else some ((c.maxHeartbeats - (hb - c.initHeartbeats)) / 1000)
  let ok ← tryCatchRuntimeEx
    (do (if n == 0 then evalTactic t else withLocalHb (n * 1000) (Tactic.withoutRecover (evalTactic t))); pure true)
    fun e => do
      s.restore
      if e.isMaxHeartbeat then pure false else throw e
  unless ok do
    let hint := "raise `maxHeartbeats` or `set_option ved.mem.h0Budget N`, or disable the local limit with `set_option ved.mem.h0Budget 0`"
    let (m, which) : String × String := match n, left? with
      | 0, some l => (s!"{l}", s!"the local limit ved.mem.h0Budget is off (0); the remaining ambient budget (maxHeartbeats) = {l} ended the run")
      | 0, none => ("unlimited", "the local limit ved.mem.h0Budget is off (0) and the ambient budget is unlimited")
      | _, some l =>
        if l < n then (s!"{l}", s!"the remaining ambient budget (maxHeartbeats) = {l} was the smaller one, not the local limit ved.mem.h0Budget = {n}")
        else (s!"{n}", s!"the local limit ved.mem.h0Budget = {n} was the smaller one (the remaining ambient budget was not smaller)")
      | _, none => (s!"{n}", s!"the local limit ved.mem.h0Budget = {n} was the smaller one (the ambient budget is unlimited)")
    throwError "ved_h0_budget: the base case (h0) did not finish within min(local ved.mem.h0Budget, remaining ambient budget) = {m} heartbeats \
      (units of maxHeartbeats): {which}; {hint}"

/-! `.val` of an operator applied directly through the `BitVec`-`Signal` / `Signal`-`BitVec` instances (as the synthesizer's
source writes `0#16 - x`): `Tools.VedU1Lemmas.*_val_sc/_cs` are stated with the other elaboration (`Signal.pure a`). -/
section DirectOps
open Sparkle.Core.Domain
variable {dom : DomainConfig} {n : Nat}
theorem add_val_bs (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HAdd.hAdd (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a + b.val s := rfl
theorem add_val_sb (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HAdd.hAdd (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s + b := rfl
theorem sub_val_bs (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HSub.hSub (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a - b.val s := rfl
theorem sub_val_sb (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HSub.hSub (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s - b := rfl
theorem mul_val_bs (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HMul.hMul (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a * b.val s := rfl
theorem mul_val_sb (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HMul.hMul (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s * b := rfl
theorem and_val_bs (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HAnd.hAnd (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a &&& b.val s := rfl
theorem and_val_sb (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HAnd.hAnd (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s &&& b := rfl
theorem or_val_bs (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HOr.hOr (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a ||| b.val s := rfl
theorem or_val_sb (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HOr.hOr (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s ||| b := rfl
theorem xor_val_bs (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HXor.hXor (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a ^^^ b.val s := rfl
theorem xor_val_sb (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HXor.hXor (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s ^^^ b := rfl
theorem shl_val_bs (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HShiftLeft.hShiftLeft (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a <<< b.val s := rfl
theorem shl_val_sb (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HShiftLeft.hShiftLeft (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s <<< b := rfl
theorem shr_val_bs (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HShiftRight.hShiftRight (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a >>> b.val s := rfl
theorem shr_val_sb (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HShiftRight.hShiftRight (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s >>> b := rfl
end DirectOps

/-- the first pair of differing subterms of two expressions (descending through equal heads / binder bodies) -/
partial def exprDiff (a b : Expr) : Option (Expr × Expr) :=
  if a == b then none else
  match a, b with
  | .app .., .app .. =>
    if a.getAppNumArgs == b.getAppNumArgs && a.getAppFn == b.getAppFn then
      (List.range a.getAppNumArgs).findSome? fun i => exprDiff (a.getAppArgs[i]!) (b.getAppArgs[i]!)
    else some (a, b)
  | .lam _ t x _, .lam _ t' x' _ => (exprDiff t t').orElse fun _ => exprDiff x x'
  | .mdata _ x, _ => exprDiff x b
  | _, .mdata _ x => exprDiff a x
  | _, _ => some (a, b)

/-- the number of nodes of an expression as a tree (shared subterms counted at each occurrence), and as a DAG -/
partial def treeSize (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
  if let some n := (← get)[e]? then return n
  let n ← match e with
    | .app f a => do pure ((← treeSize f) + (← treeSize a) + 1)
    | .lam _ t b _ => do pure ((← treeSize t) + (← treeSize b) + 1)
    | .forallE _ t b _ => do pure ((← treeSize t) + (← treeSize b) + 1)
    | .letE _ t v b _ => do pure ((← treeSize t) + (← treeSize v) + (← treeSize b) + 1)
    | .mdata _ b => treeSize b
    | .proj _ _ b => do pure ((← treeSize b) + 1)
    | _ => pure 1
  modify (·.insert e n)
  return n

/-- `ved_mem_shape ite|lam|fvar`: the memory-array argument (the last) of the goal `MemInv ..` has that outer shape, as written
(the peel must not let the unifier match an `ite` against a `fun` by eta / unfolding: that produces junk) -/
elab "ved_mem_shape " k:ident : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.isAppOf ``Tools.VedMem.MemInv do throwError "ved_mem_shape: not a MemInv goal"
  let m := (tgt.getArg! (tgt.getAppNumArgs - 1)).consumeMData
  let ok := match k.getId.eraseMacroScopes.toString with
    | "ite" => m.isAppOf ``ite
    | "lam" => m.isLambda
    | "fvar" => m.isFVar
    | _ => false
  unless ok do throwError "ved_mem_shape: not {k.getId.eraseMacroScopes}"

/-- debugging: log the part of the main goal from the first `HSub.hSub`, `pp.explicit`, cut to 3500 characters -/
elab "ved_dbg_goal" : tactic => withMainContext do
  let g ← getMainGoal
  let txt ← withOptions (fun o => o.setBool `pp.explicit true) do return toString (← ppGoal g)
  let i := (txt.splitOn "HSub.hSub").head!.length
  logInfo m!"DBG {(txt.drop (i - 500)).take 1200}"

/-- debugging: the number of goals and the target of the first two, each cut to 2500 characters -/
elab "ved_dbg_state" : tactic => do
  let gs ← getGoals
  let mut out := s!"{gs.length} goals"
  if let some dir ← IO.getEnv "VED_DUMP_GOALS" then
    let mut k := 0
    for g in gs do
      let t ← g.withContext do
        withOptions (fun o => (o.insert `format.width (160 : Nat)).setBool `pp.deepTerms true |>.insert `pp.maxSteps (10000000 : Nat)) do
          return toString (← ppGoal g)
      if k < 24 then IO.FS.writeFile s!"{dir}/goal{k}.txt" (t.take 200000).toString
      k := k + 1
  for g in gs.take 2 do
    let t ← g.withContext do return toString (← ppExpr (← instantiateMVars (← g.getType)))
    out := out ++ s!"\n--- target ({t.length} chars):\n" ++ t.take 800 ++ "\n.....\n" ++ t.drop (t.length - 1800)
  let mut summary := ""
  for g in gs do
    let tl := Tools.VedU1WireShare.loopsDag (← g.withContext do instantiateMVars (← g.getType))
    let hs ← g.withContext do
      let mut c := 0
      for d in ← getLCtx do
        unless d.isImplementationDetail do
          c := c + (Tools.VedU1WireShare.loopsDag (← instantiateMVars d.type)).size
      return c
    summary := summary ++ s!" [T{tl.size}/H{hs}]"
  out := out ++ "\nPER GOAL loops (target/hyps):" ++ summary
  let mut sizes := ""
  for g in gs do
    let t ← g.withContext do instantiateMVars (← g.getType)
    let (tr, _) := (treeSize t).run {}
    sizes := sizes ++ s!" [tree {tr}/dag {(Tools.VedU1WireShare.collectDag (fun _ => true) t).size}]"
  out := out ++ "\nGOAL SIZES:" ++ sizes
  let mut shorts := ""
  let mut gi := 0
  for g in gs do
    let t ← g.withContext do return toString (← ppExpr (← instantiateMVars (← g.getType)))
    shorts := shorts ++ s!"\n  #{gi}: " ++ (let t1 := (t.replace "\n" " "); (t1.take 150).toString ++ " ..... " ++ (t1.drop (t1.length - 220)).toString)
    gi := gi + 1
  out := out ++ "\nALL TARGETS:" ++ shorts.take 9000
  for g in gs do
    let tg ← g.withContext do instantiateMVars (← g.getType)
    if tg.isAppOf ``Tools.VedMem.MemInv then
      let rep ← g.withContext do
        let mut o := ""
        for d in ← getLCtx do
          unless d.isImplementationDetail do
            let ty ← instantiateMVars d.type
            if ty.isAppOf ``Tools.VedMem.MemInv then
              let a := tg.getAppArgs
              let b := ty.getAppArgs
              let eqs := (List.range (min a.size b.size)).map fun i => a[i]! == b[i]!
              o := o ++ s!"\n  MEMINV goal vs {d.userName}: arg equal? {eqs}"
              for i in (if a[3]! == b[3]! then [5, 6, 7] else []) do
                if let some (x, y) := exprDiff a[i]! b[i]! then
                  let xs := toString (← ppExpr x)
                  let ys := toString (← ppExpr y)
                  o := o ++ s!"\n   arg {i} first diff:\n    GOAL: {xs.take 500}\n    HYP:  {ys.take 500}"
        return o
      out := out ++ "\nMEMINV GOAL" ++ rep
      if tg.getAppNumArgs ≥ 10 then
        let mm ← g.withContext do withOptions (fun o => (o.setBool `pp.deepTerms false |>.insert `pp.deepTerms.threshold (6 : Nat))) do return toString (← ppExpr (tg.getAppArgs[9]!))
        out := out ++ s!"\nMEMS ARG ({mm.length} chars): " ++ mm.take 3500
  for gi2 in [8, 12] do
    if let some g := gs[gi2]? then
      let t ← g.withContext do return toString (← ppExpr (← instantiateMVars (← g.getType)))
      out := out ++ s!"\nGOAL{gi2} ({t.length} chars):\n" ++ t.take 1500 ++ "\n.....\n" ++ (t.drop (t.length - 1200)).toString
  if let some g := gs.find? (fun g => true) then
    let _ := g
  for g in gs do
    let tg ← g.withContext do instantiateMVars (← g.getType)
    if (Tools.VedU1WireShare.loopsDag tg).size > 0 then
      let occ := Tools.VedU1WireShare.collectDag (fun x => x.isAppOfArity ``Signal.val 4 && (x.getArg! 2).isAppOfArity ``Signal.loop 4) tg
      let ts ← g.withContext do occ.mapM fun o => do return toString (← ppExpr (o.getArg! 3))
      let lp := Tools.VedU1WireShare.collectDag (fun x => x.isAppOfArity ``Signal.loop 4) tg
      let parents := Tools.VedU1WireShare.collectDag (fun x => x.isApp && x.getAppArgs.any (fun a => a.isAppOfArity ``Signal.loop 4)) tg
      let ps ← g.withContext do parents.mapM fun o => do return (toString (← ppExpr o.getAppFn)).take 60
      let tgtS ← g.withContext do
        let ty ← inferType lp[0]!
        withLocalDeclD `LOOP ty fun lv => do
          let t' := tg.replace fun e => if e.isAppOfArity ``Signal.loop 4 then some lv else none
          return toString (← ppExpr t')
      out := out ++ s!"\nT1 TARGET (loop := LOOP, {tgtS.length} chars): " ++ tgtS.take 1800
      let pe := parents[0]!.replace fun e => if e.isAppOfArity ``Signal.loop 4 then some (mkConst `LOOP) else none
      let pes ← g.withContext <| withOptions (fun o => o.setBool `pp.explicit true) do return toString (← ppExpr pe)
      out := out ++ s!"\nPARENT0 (loop := LOOP): {pes.take 700}"
      out := out ++ s!"\nFIRST T1 GOAL: Signal.val-of-loop occurrences at times {ts}; loops {lp.size}; parents heads {ps}"
      break
  if let some g := gs.head? then
    let hy ← g.withContext do
      let mut o := ""
      for d in ← getLCtx do
        unless d.isImplementationDetail do
          o := o ++ s!"\n  {d.userName} : " ++ (← (do let t := toString (← ppExpr (← instantiateMVars d.type)); pure (if t.length > 700 then (t.take 100).toString ++ s!" ...({t.length} chars)" else t) : MetaM String))
      return o
    out := out ++ "\nHYPS:" ++ hy.take 4500
    let extra ← g.withContext do
      let mut o := ""
      let tl := Tools.VedU1WireShare.loopsDag (← instantiateMVars (← g.getType))
      o := o ++ s!"\nTARGET LOOPS {tl.size}"
      for d in ← getLCtx do
        unless d.isImplementationDetail do
          let hl := Tools.VedU1WireShare.loopsDag (← instantiateMVars d.type)
          if hl.size > 0 then
            o := o ++ s!"\nHYP {d.userName}: loops {hl.size}, in target: {hl.map (fun l => tl.contains l)}"
      return o
    out := out ++ extra
  throwError "DBGSTATE {out}"

/-- close a goal `x.toNat < n` (a bit-vector's range) by `BitVec.isLt` -/
elab "ved_lt_close" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.isAppOfArity ``LT.lt 4 do throwError "not <"
  evalTactic (← `(tactic| exact BitVec.isLt _))

def dbgLog (msg : String) : IO Unit := do
  if let some dir ← IO.getEnv "VED_DUMP_DIR" then
    let h ← IO.FS.Handle.mk s!"{dir}/addr.log" .append
    h.putStrLn msg

/-- the gate of the debug output: `VED_DUMP_DIR` is set -/
def dbgOn : IO Bool := return (← IO.getEnv "VED_DUMP_DIR").isSome

/-- `dbgLog` of a string that is BUILT only when the gate is open (the gate is checked first, then `mk` runs) -/
def dbgLogWith {m : Type → Type} [Monad m] [MonadLiftT IO m] (mk : m String) : m Unit := do
  if ← (dbgOn : IO Bool) then
    let msg ← mk
    (dbgLog msg : IO Unit)

/-- `ved_tlog "k"`: (only with `VED_DUMP_DIR`) a timing line in `addr.log` -/
elab "ved_tlog " k:str : tactic => do
  if (← IO.getEnv "VED_DUMP_DIR").isSome then
    let sz ← match (← getGoals).head? with
      | some g => g.withContext do
          let e ← instantiateMVars (← g.getType)
          pure s!" tree={Tools.VedU1Loop.treeSizeVal e} dag={(Tools.VedU1WireShare.collectDag (fun _ => true) e).size}"
      | none => pure ""
    dbgLog s!"TLOG {k.getString} t={← IO.monoMsNow} hb={(← IO.getNumHeartbeats) / 1000} goals={(← getGoals).length}{sz}"

/-- `ved_rw_dag hc`, `hc : T = T'`: rewrite the occurrences of `T` in the main goal by `T'` like `rw [hc]`, but with `Expr.replace`
(a cache by pointer: ONE visit per shared node) and the `congrArg` of the motive, instead of `kabstract` (a walk of the TREE;
observed: on the loop body of R033 the tree has 3.5e11 nodes for 2460 distinct ones and the `rw` did not return in 890 s).  The
occurrences replaced are the syntactic ones (`T` is read off the goal by `ved_mem_congr`); one left unreplaced makes the goal
differ from the one `rw` gives, never the proof wrong (the kernel checks the `congrArg`).  Untrusted: the kernel checks it. -/
elab "ved_rw_dag " h:ident : tactic => withMainContext do
  let hE ← elabTerm h.raw none
  let some (_, l, r) := (← instantiateMVars (← inferType hE)).eq? | throwError "ved_rw_dag: not an equation"
  let tgt ← instantiateMVars (← getMainTarget)
  let motive ← withLocalDeclD `ved_x (← inferType l) fun xv =>
    mkLambdaFVars #[xv] (tgt.replace fun e => if e == l then some xv else none)
  let newTgt := tgt.replace fun e => if e == l then some r else none
  let g ← getMainGoal
  replaceMainGoal [← g.replaceTargetEq newTgt (← mkCongrArg motive hE)]

/-- `ved_mem_congr s1 s2 h t`: rewrite every `memState` of the goal that mentions the fvar `s1` into the one
with `s2` in its place (`h : ∀ k ≤ t, s1.val k = s2.val k`) -/
elab "ved_mem_congr " s1:ident s2:ident h:ident : tactic => withMainContext do
  let s1E ← elabTerm s1.raw none
  let s2E ← elabTerm s2.raw none
  let tgt ← instantiateMVars (← getMainTarget)
  let isMem := fun (x : Expr) => x.isAppOf ``Sparkle.Core.Signal.Signal.memState && x.getAppNumArgs ≥ 8
  let occs := Tools.VedU1WireShare.collectDag isMem tgt
  let mut done : Array Expr := #[]
  for o in occs do
    let args := o.getAppArgs
    let T := mkAppN o.getAppFn (args.extract 0 8)
    if done.contains T || !(T.containsFVar s1E.fvarId!) then continue
    done := done.push T
    let tm0 ← IO.monoMsNow
    let hbm0 ← IO.getNumHeartbeats
    dbgLog s!"mem_congr: lctx={(← getLCtx).size} T #{done.size} of {occs.size} occs, T tree={Tools.VedU1Loop.treeSizeVal T}"
    let T' := T.replaceFVar s1E s2E
    let Ts ← Term.exprToSyntax T
    let T's ← Term.exprToSyntax T'
    let side ← `(tactic| (intro k hk; simp only [$h:ident k (by omega)]))
    let side2 ← `(tactic| (intro k hk; simp [$h:ident k (by omega), Tools.VedU1Contract.PTy.val, Sparkle.Core.Signal.Signal.map, Functor.map, Seq.seq, Sparkle.Core.Signal.Signal.seq, Sparkle.Core.Signal.Signal.ap, Sparkle.Core.Signal.Signal.mux, Sparkle.Core.Signal.Signal.beq, Sparkle.Core.Signal.bundle2]))
    let side3 ← `(tactic| (intro k hk; (try dsimp only); ved_loop_simp [$h:ident k (by omega), Tools.VedU1Contract.PTy.val, Sparkle.Core.Signal.Signal.memoryComboRead_val, Tools.VedU1Lemmas.add_val_sc, Tools.VedU1Lemmas.add_val_cs, Tools.VedU1Lemmas.sub_val_sc, Tools.VedU1Lemmas.sub_val_cs, Tools.VedU1Lemmas.mul_val_sc, Tools.VedU1Lemmas.mul_val_cs, Tools.VedU1Lemmas.and_val_sc, Tools.VedU1Lemmas.and_val_cs, Tools.VedU1Lemmas.or_val_sc, Tools.VedU1Lemmas.or_val_cs, Tools.VedU1Lemmas.xor_val_sc, Tools.VedU1Lemmas.xor_val_cs, Tools.VedU1Lemmas.shl_val_sc, Tools.VedU1Lemmas.shl_val_cs, Tools.VedU1Lemmas.shr_val_sc, Tools.VedU1Lemmas.shr_val_cs, Tools.VedMemLoop.add_val_bs, Tools.VedMemLoop.add_val_sb, Tools.VedMemLoop.sub_val_bs, Tools.VedMemLoop.sub_val_sb, Tools.VedMemLoop.mul_val_bs, Tools.VedMemLoop.mul_val_sb, Tools.VedMemLoop.and_val_bs, Tools.VedMemLoop.and_val_sb, Tools.VedMemLoop.or_val_bs, Tools.VedMemLoop.or_val_sb, Tools.VedMemLoop.xor_val_bs, Tools.VedMemLoop.xor_val_sb, Tools.VedMemLoop.shl_val_bs, Tools.VedMemLoop.shl_val_sb, Tools.VedMemLoop.shr_val_bs, Tools.VedMemLoop.shr_val_sb, Tools.VedU1Lemmas.pure_val, Tools.VedU1Lemmas.mux_val, Tools.VedU1Lemmas.compl_val, Tools.VedU1Lemmas.bool_and_val, Tools.VedU1Lemmas.bool_or_val, Tools.VedU1Lemmas.bool_xor_val, Tools.VedU1Lemmas.bool_compl_val]))
    evalTactic (← `(tactic|
      (have hc : $Ts = $T's := Tools.VedMem.memState_congr _ _
          (by ved_tlog "mem_congr side 1"; first | ($side:tactic; done) | ($side2:tactic; done) | ($side3:tactic; done))
          (by ved_tlog "mem_congr side 2"; first | ($side:tactic; done) | ($side2:tactic; done) | ($side3:tactic; done))
          (by ved_tlog "mem_congr side 3"; first | ($side:tactic; done) | ($side2:tactic; done) | ($side3:tactic; done))
       ved_tlog "mem_congr have done"
       ved_rw_dag hc)))
    dbgLog s!"mem_congr: T #{done.size} ms={(← IO.monoMsNow) - tm0} hb={((← IO.getNumHeartbeats) - hbm0) / 1000}"


/-- `ved_loop_congr s1 s2 h`: rewrite every `(Signal.loop F).val k` of the goal whose body `F` mentions the fvar `s1`
(a loop inside the outer loop's body, driven by the outer state) into the one with `s2` in its place
(`h : ∀ k ≤ t, s1.val k = s2.val k`), by `Tools.VedMemNest.loop_val_congr_le` bounded by `k`: the inner loop at time
`k` reads the outer signal only at cycles `< k`. -/
elab "ved_loop_congr " s1:ident s2:ident h:ident : tactic => withMainContext do
  let s1E ← elabTerm s1.raw none
  let s2E ← elabTerm s2.raw none
  let tgt ← instantiateMVars (← getMainTarget)
  let isLoopVal := fun (x : Expr) =>
    x.isAppOfArity ``Sparkle.Core.Signal.Signal.val 4 && (x.getArg! 2).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4
      && (x.getArg! 2).containsFVar s1E.fvarId!
  let occs := Tools.VedU1WireShare.collectDag isLoopVal tgt
  let mut done : Array Expr := #[]
  for o in occs do
    if done.contains o then continue
    done := done.push o
    let L := o.getArg! 2
    let k := o.getArg! 3
    let L' := L.replaceFVar s1E s2E
    let Fs ← Term.exprToSyntax (L.getArg! 3)
    let F's ← Term.exprToSyntax (L'.getArg! 3)
    let ks ← Term.exprToSyntax k
    let Ls ← Term.exprToSyntax o
    let L's ← Term.exprToSyntax (mkAppN o.getAppFn (o.getAppArgs.set! 2 L'))
    evalTactic (← `(tactic|
      (have hc : $Ls = $L's := Tools.VedMemNest.loop_val_congr_le $Fs $F's $ks
          (by first | (intro a b; rfl) | (intro a b; (try dsimp only); ved_loop_simp [Tools.VedU1Contract.PTy.val, Sparkle.Core.Signal.Signal.memoryComboRead_val, Sparkle.Core.Signal.Signal.fst, Sparkle.Core.Signal.Signal.snd, Tools.VedU1Lemmas.add_val_sc, Tools.VedU1Lemmas.add_val_cs, Tools.VedU1Lemmas.sub_val_sc, Tools.VedU1Lemmas.sub_val_cs, Tools.VedU1Lemmas.mul_val_sc, Tools.VedU1Lemmas.mul_val_cs, Tools.VedU1Lemmas.and_val_sc, Tools.VedU1Lemmas.and_val_cs, Tools.VedU1Lemmas.or_val_sc, Tools.VedU1Lemmas.or_val_cs, Tools.VedU1Lemmas.xor_val_sc, Tools.VedU1Lemmas.xor_val_cs, Tools.VedU1Lemmas.shl_val_sc, Tools.VedU1Lemmas.shl_val_cs, Tools.VedU1Lemmas.shr_val_sc, Tools.VedU1Lemmas.shr_val_cs, Tools.VedMemLoop.add_val_bs, Tools.VedMemLoop.add_val_sb, Tools.VedMemLoop.sub_val_bs, Tools.VedMemLoop.sub_val_sb, Tools.VedMemLoop.mul_val_bs, Tools.VedMemLoop.mul_val_sb, Tools.VedMemLoop.and_val_bs, Tools.VedMemLoop.and_val_sb, Tools.VedMemLoop.or_val_bs, Tools.VedMemLoop.or_val_sb, Tools.VedMemLoop.xor_val_bs, Tools.VedMemLoop.xor_val_sb, Tools.VedMemLoop.shl_val_bs, Tools.VedMemLoop.shl_val_sb, Tools.VedMemLoop.shr_val_bs, Tools.VedMemLoop.shr_val_sb, Tools.VedU1Lemmas.pure_val, Tools.VedU1Lemmas.mux_val, Tools.VedU1Lemmas.compl_val, Tools.VedU1Lemmas.bool_and_val, Tools.VedU1Lemmas.bool_or_val, Tools.VedU1Lemmas.bool_xor_val, Tools.VedU1Lemmas.bool_compl_val]; done))
          (by intro t' ht' a b hab
              have h' : ∀ j, j ≤ t' → Sparkle.Core.Signal.Signal.val $s1 j = Sparkle.Core.Signal.Signal.val $s2 j := fun j hj => $h:ident j (by omega)
              have hab' := hab t' (Nat.le_refl _)
              have hs' := h' t' (Nat.le_refl _)
              first | (ved_loop_simp [hab', hs', Tools.VedU1Contract.PTy.val, Sparkle.Core.Signal.Signal.memoryComboRead_val, Sparkle.Core.Signal.Signal.fst, Sparkle.Core.Signal.Signal.snd, Tools.VedU1Lemmas.add_val_sc, Tools.VedU1Lemmas.add_val_cs, Tools.VedU1Lemmas.sub_val_sc, Tools.VedU1Lemmas.sub_val_cs, Tools.VedU1Lemmas.mul_val_sc, Tools.VedU1Lemmas.mul_val_cs, Tools.VedU1Lemmas.and_val_sc, Tools.VedU1Lemmas.and_val_cs, Tools.VedU1Lemmas.or_val_sc, Tools.VedU1Lemmas.or_val_cs, Tools.VedU1Lemmas.xor_val_sc, Tools.VedU1Lemmas.xor_val_cs, Tools.VedU1Lemmas.shl_val_sc, Tools.VedU1Lemmas.shl_val_cs, Tools.VedU1Lemmas.shr_val_sc, Tools.VedU1Lemmas.shr_val_cs, Tools.VedMemLoop.add_val_bs, Tools.VedMemLoop.add_val_sb, Tools.VedMemLoop.sub_val_bs, Tools.VedMemLoop.sub_val_sb, Tools.VedMemLoop.mul_val_bs, Tools.VedMemLoop.mul_val_sb, Tools.VedMemLoop.and_val_bs, Tools.VedMemLoop.and_val_sb, Tools.VedMemLoop.or_val_bs, Tools.VedMemLoop.or_val_sb, Tools.VedMemLoop.xor_val_bs, Tools.VedMemLoop.xor_val_sb, Tools.VedMemLoop.shl_val_bs, Tools.VedMemLoop.shl_val_sb, Tools.VedMemLoop.shr_val_bs, Tools.VedMemLoop.shr_val_sb, Tools.VedU1Lemmas.pure_val, Tools.VedU1Lemmas.mux_val, Tools.VedU1Lemmas.compl_val, Tools.VedU1Lemmas.bool_and_val, Tools.VedU1Lemmas.bool_or_val, Tools.VedU1Lemmas.bool_xor_val, Tools.VedU1Lemmas.bool_compl_val]; done) | (simp [hab', hs']; done))
          $ks (Nat.le_refl _)
       rw [hc])))

/-! ## `ved_causal_dag`: the causal side condition by a lock-step walk, without the whole-goal simp

`ved_causal_dag` (option `ved.mem.causalDag`, default off) proves `(F s1).val (n+1) = (F s2).val (n+1)` from
`h : ∀ k ≤ n, s1.val k = s2.val k` by walking the two sides in lock step: `Signal.val X k` against `Signal.val Y k` is
unfolded on both sides to the scalar expression of the signal's `Signal.mk` (a definitional step, the proof is `rfl`), the
scalar expressions are compared head by head (congruence of the differing arguments only; `ite` by `ved_ite_congr`), a
`memState` over different write ports by `Tools.VedMem.memState_congr` (its three side conditions are the same walk under a
bound variable), and `s1.val k` against `s2.val k` by `h k` (the bound by `omega`).  Each pair of subterms is visited once
(a cache by pair, the DAG is not expanded).  Untrusted: the kernel checks the proof; a shape the walk does not know fails
and the caller runs the `ved_causal` macro unchanged. -/

theorem ved_ite_congr {α : Sort _} {c c' : Prop} {d : Decidable c} {d' : Decidable c'} {t t' e e' : α}
    (hc : c = c') (ht : t = t') (he : e = e') : @ite α c d t e = @ite α c' d' t' e' := by
  subst hc ht he; congr

register_option ved.mem.causalDag : Bool := {
  defValue := false
  descr := "try the lock-step walk `ved_causal_dag` for the causal side condition of the memory loop before the simp-based `ved_causal`"
}

/-- the proof of `x = y` for `x`/`y` equal except at the arguments `ps` (index, proof of `a_i = b_i`): one `congrArg` per
differing argument (a motive over that argument; fails when a later argument's type depends on it) -/
def congrArgsDag (f : Expr) (as bs : Array Expr) (ps : Array (Nat × Expr)) : MetaM Expr := do
  let mut cur := mkAppN f as
  let mut pf ← mkEqRefl cur
  let mut args := as
  for (i, p) in ps do
    let ai := args[i]!
    let bi := bs[i]!
    let motive ← withLocalDeclD `ved_y (← inferType ai) fun y => do
      mkLambdaFVars #[y] (mkAppN f (args.set! i y))
    let step ← mkCongrArg motive p
    pf ← mkEqTrans pf step
    args := args.set! i bi
    cur := mkAppN f args
  return pf

/-- the scalar the signal `X` has at cycle `k` (`Signal.val X k` unfolded to the body of its `Signal.mk`) -/
def unfoldValDag (A : Expr) : MetaM Expr := do
  let X := A.getArg! 2
  let k := A.getArg! 3
  let Xw ← whnf X
  unless Xw.isAppOfArity ``Sparkle.Core.Signal.Signal.mk 3 do throwError "ved_causal_dag: signal does not unfold to Signal.mk"
  return (mkApp (Xw.getArg! 2) k).headBeta

/-- the cache of the walk, by pair of subterms, SCOPED: a proof found under a binder (`ved_j`/`ved_hj` of a `memState` side
condition, the variable of a `funext`) may mention that binder's free variables (a bound proved by `omega` from the binder's
hypothesis), so it is stored in the scope of the binder only; a scope reads the entries of the scopes around it (those proofs
mention only variables the inner scope has too) and never writes into them. -/
structure DagCache where
  own : IO.Ref (Std.HashMap (Expr × Expr) Expr)
  parent : Option DagCache

namespace DagCache
def new : IO DagCache := return { own := ← IO.mkRef {}, parent := none }
/-- the cache of a new binder scope inside `c` -/
def scope (c : DagCache) : IO DagCache := return { own := ← IO.mkRef {}, parent := some c }
partial def find? (c : DagCache) (k : Expr × Expr) : IO (Option Expr) := do
  match (← c.own.get)[k]? with
  | some p => return some p
  | none => match c.parent with
    | some q => q.find? k
    | none => return none
def insert (c : DagCache) (k : Expr × Expr) (p : Expr) : IO Unit := c.own.modify (·.insert k p)
end DagCache

/-- raw literals (`nat_lit 0` left by the unfolding of a `match`) are not read by `omega`: spell them `OfNat` -/
def normLitsDag (k0 : Expr) : Expr :=
  k0.replace fun e =>
    if e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).isRawNatLit then some e
    else match e with | .lit (.natVal n) => some (mkNatLit n) | _ => none

/-- the leaf `s1.val k = s2.val k` of the agreement hypothesis `h`, the bound by `omega` -/
def leafDag (h k0 : Expr) : TacticM Expr := do
  let k := normLitsDag k0
  let hk := mkApp h k
  let ty ← whnf (← inferType hk)
  unless ty.isForall do throwError "ved_causal_dag: agreement hypothesis has an unexpected type"
  let m ← mkFreshExprMVar ty.bindingDomain!
  let rest ← try Tactic.run m.mvarId! (evalTactic (← `(tactic| omega)))
    catch e =>
      dbgLogWith do return s!"causal_dag leaf: {← e.toMessageData.toString}\nleaf goal: {(toString (← withOptions (fun o => o.setBool `pp.explicit true) (ppExpr ty.bindingDomain!))).take 400}"
      throwError "ved_causal_dag: bound not proved"
  unless rest.isEmpty do throwError "ved_causal_dag: bound not proved"
  return mkApp hk m

/-- a proof of `A = B` (see the module comment) -/
partial def dagEq (cache : DagCache) (s1 s2 h A B : Expr) : TacticM Expr := do
  if A == B then return ← mkEqRefl A
  if let some p ← cache.find? (A, B) then return p
  checkSystem "ved_causal_dag"
  let p ← dagEqCore cache s1 s2 h A B
  cache.insert (A, B) p
  return p
where
  /-- `s.1 k` (the projection spelling of `Signal.val s k`) as `Signal.val s k` -/
  normVal (e : Expr) : MetaM Expr := do
    match e.consumeMData with
    | .app (.proj ``Sparkle.Core.Signal.Signal 0 X) k => mkAppM ``Sparkle.Core.Signal.Signal.val #[X, k]
    | e => pure e
  dagEqCore (cache : DagCache) (s1 s2 h A0 B0 : Expr) : TacticM Expr := do
    let A ← normVal (← whnfCore A0)
    let B ← normVal (← whnfCore B0)
    if A != A0 || B != B0 then
      return ← mkExpectedTypeHint (← dagEq cache s1 s2 h A B) (← mkEq A0 B0)
    -- `Signal.val F k x`: the value of a signal of functions (`<*>`) applied to an argument
    if A.isAppOf ``Sparkle.Core.Signal.Signal.val && A.getAppNumArgs > 4 && B.isAppOf ``Sparkle.Core.Signal.Signal.val
        && B.getAppNumArgs == A.getAppNumArgs then
      let a := A.getAppArgs
      let b := B.getAppArgs
      let mut pf ← dagEq cache s1 s2 h (mkAppN A.getAppFn (a.extract 0 4)) (mkAppN B.getAppFn (b.extract 0 4))
      for i in [4:a.size] do
        if a[i]! != b[i]! then
          pf ← mkCongr pf (← dagEq cache s1 s2 h a[i]! b[i]!)
        else pf ← mkCongrFun pf a[i]!
      return pf
    if A.isAppOfArity ``Sparkle.Core.Signal.Signal.val 4 && B.isAppOfArity ``Sparkle.Core.Signal.Signal.val 4 then
      let X := A.getArg! 2
      let Y := B.getArg! 2
      let k := A.getArg! 3
      unless k == B.getArg! 3 do throwError "ved_causal_dag: different cycles"
      if X == s1 && Y == s2 then return ← mkExpectedTypeHint (← leafDag h k) (← mkEq A B)
      if X.isAppOf ``Sparkle.Core.Signal.Signal.loop || Y.isAppOf ``Sparkle.Core.Signal.Signal.loop then
        throwError "ved_causal_dag: loop"
      let eA ← unfoldValDag A
      let eB ← unfoldValDag B
      let p ← dagEq cache s1 s2 h eA eB
      let l ← mkExpectedTypeHint (← mkEqRefl A) (← mkEq A eA)
      let r ← mkExpectedTypeHint (← mkEqRefl eB) (← mkEq eB B)
      return ← mkEqTrans (← mkEqTrans l p) r
    if A.isAppOf ``Sparkle.Core.Signal.Signal.memState && A.getAppNumArgs ≥ 8 && B.isAppOf ``Sparkle.Core.Signal.Signal.memState
        && B.getAppNumArgs == A.getAppNumArgs then
      let a := A.getAppArgs
      let b := B.getAppArgs
      if ([0, 1, 2, 3, 7].all fun i => a[i]! == b[i]!) then
        let t := a[7]!
        let side (x y : Expr) : TacticM Expr := do
          let cache ← cache.scope
          withLocalDeclD `ved_j (mkConst ``Nat) fun j => do
            withLocalDeclD `ved_hj (← mkAppM ``LT.lt #[j, normLitsDag t]) fun hj => do
              let ValX ← mkAppM ``Sparkle.Core.Signal.Signal.val #[x, j]
              let ValY ← mkAppM ``Sparkle.Core.Signal.Signal.val #[y, j]
              mkLambdaFVars #[j, hj] (← dagEq cache s1 s2 h ValX ValY)
        let ha ← side a[4]! b[4]!
        let hd ← side a[5]! b[5]!
        let he ← side a[6]! b[6]!
        let hc ← mkAppOptM ``Tools.VedMem.memState_congr
          #[a[0]!, a[1]!, a[2]!, a[3]!, a[4]!, b[4]!, a[5]!, b[5]!, a[6]!, b[6]!, t, ha, hd, he]
        let mut pf := hc
        for i in [8:a.size] do
          if a[i]! != b[i]! then
            pf ← mkCongr pf (← dagEq cache s1 s2 h a[i]! b[i]!)
          else pf ← mkCongrFun pf a[i]!
        return pf
    if A.isApp && B.isApp then
      let f := A.getAppFn
      let a := A.getAppArgs
      let b := B.getAppArgs
      if f == B.getAppFn && a.size == b.size then
        if f.isConstOf ``ite && a.size == 5 then
          let pc ← dagEq cache s1 s2 h a[1]! b[1]!
          let pt ← dagEq cache s1 s2 h a[3]! b[3]!
          let pe ← dagEq cache s1 s2 h a[4]! b[4]!
          return ← mkAppOptM ``ved_ite_congr #[a[0]!, a[1]!, b[1]!, a[2]!, b[2]!, a[3]!, b[3]!, a[4]!, b[4]!, pc, pt, pe]
        let mut ps : Array (Nat × Expr) := #[]
        for i in [0:a.size] do
          if a[i]! != b[i]! then
            let q ← try dagEq cache s1 s2 h a[i]! b[i]!
              catch e =>
                dbgLogWith do
                  let extra ← if f.isConstOf ``Sparkle.Core.Signal.Signal.val then
                      do let xs ← a.mapM fun x => do pure ((toString (← ppExpr x)).take 50).toString
                         pure s!" args={xs}"
                    else pure ""
                  return s!"causal_dag: in arg {i}/{a.size} of {(toString (← ppExpr f)).take 80}{extra}"
                throw e
            ps := ps.push (i, q)
        return ← congrArgsDag f a b ps
    if let (.proj n i x, .proj n' i' y) := (A, B) then
      if n == n' && i == i' then
        let p ← dagEq cache s1 s2 h x y
        let motive ← withLocalDeclD `ved_y (← inferType x) fun v => mkLambdaFVars #[v] (.proj n i v)
        return ← mkCongrArg motive p
    if let (.lam n ty bA bi, .lam _ ty' bB _) := (A, B) then
      if ty == ty' then
        let cache ← cache.scope
        let p ← withLocalDecl n bi ty fun x => do
          mkLambdaFVars #[x] (← dagEq cache s1 s2 h (bA.instantiate1 x) (bB.instantiate1 x))
        return ← mkFunExt p
    dbgLogWith do return s!"causal_dag: no rule for [{(toString (← ppExpr A)).take 300}] against [{(toString (← ppExpr B)).take 300}]"
    throwError "ved_causal_dag: no rule for this pair of subterms"

/-- `ved_causal_dag`: the causal side condition (`∀ t s1 s2, (∀ k ≤ t, s1.val k = s2.val k) → (F s1).val (t+1) = (F s2).val (t+1)`)
by `dagEq`; with `VED_DUMP_DIR` the time of the walk is logged -/
elab "ved_causal_dag" : tactic => do
  unless (← getOptions).getBool `ved.mem.causalDag false do throwError "ved_causal_dag: option ved.mem.causalDag is off"
  let (t, s1, s2, h) := (mkIdent `t, mkIdent `s1, mkIdent `s2, mkIdent `h)
  evalTactic (← `(tactic| intro $t $s1 $s2 $h))
  evalTactic (← `(tactic| rcases $t:ident with _ | $t:ident))
  let t0 ← IO.monoMsNow
  let hb0 ← IO.getNumHeartbeats
  dbgLogWith do return s!"TLOG causal_dag begin t={t0}"
  try
   for g in ← getGoals do
    setGoals [g]
    withMainContext do
      let some (_, A, B) := (← instantiateMVars (← getMainTarget)).eq? | throwError "ved_causal_dag: not an equation"
      let lctx ← getLCtx
      let some s1 := lctx.findFromUserName? `s1 | throwError "ved_causal_dag: no s1"
      let some s2 := lctx.findFromUserName? `s2 | throwError "ved_causal_dag: no s2"
      let some h := lctx.findFromUserName? `h | throwError "ved_causal_dag: no h"
      let cache ← DagCache.new
      dbgLogWith do return s!"causal_dag top: nargs={A.getAppNumArgs} head={A.getAppFn} {(toString (← withOptions (fun o => o.setBool `pp.explicit true) (ppExpr (mkAppN A.getAppFn (A.getAppArgs.extract 0 2))))).take 300} | arg2={(toString (← ppExpr (A.getArg! 2))).take 200} | arg3={(toString (← ppExpr (A.getArg! 3))).take 100}"
      let p ← dagEq cache s1.toExpr s2.toExpr h.toExpr A B
      (← getMainGoal).assign p
      dbgLogWith do return s!"TLOG causal_dag goal closed t={← IO.monoMsNow} hb={((← IO.getNumHeartbeats) - hb0) / 1000} cache={(← cache.own.get).size}"
  catch e =>
    dbgLogWith do return s!"TLOG causal_dag failed t={← IO.monoMsNow} hb={((← IO.getNumHeartbeats) - hb0) / 1000}: {(← e.toMessageData.toString).take 600}"
    throw e
  setGoals []

open Lean Meta in
/-- `BitVec.toNat (x ++ y)` read at either spelling of the width (`4` against `2 + 2`: the pattern of `BitVec.toNat_append`
does not unify the width of a `++` used at a literal width) -/
simproc ved_toNat_append (BitVec.toNat _) := fun e => do
  unless e.isAppOfArity ``BitVec.toNat 2 do return .continue
  let a := e.getArg! 1
  unless a.isAppOfArity ``HAppend.hAppend 6 do return .continue
  let x := a.getArg! 4
  let y := a.getArg! 5
  let pf ← mkAppM ``BitVec.toNat_append #[x, y]
  let some (_, l, r) := (← inferType pf).eq? | return .continue
  unless (← isDefEq l e) do return .continue
  return .visit { expr := r, proof? := some pf }

/-- `ved_clear_signals`: clear the hypotheses that speak of signals (`MemInv`, the read equations: whole loop bodies, hundreds of
kilobytes): an address equality does not use them, and `omega` / `generalize ... at *` read every hypothesis. -/
elab "ved_clear_signals" : tactic => withMainContext do
  let mut ids : Array FVarId := #[]
  for d in (← getLCtx) do
    unless d.isImplementationDetail do
      let t ← instantiateMVars d.type
      if (t.find? fun e => e.isConst && (e.constName!.getPrefix == `Sparkle.Core.Signal.Signal
          || e.constName! == ``Tools.VedMem.MemInv)).isSome then ids := ids.push d.fvarId
  let g ← getMainGoal
  let mut g := g
  for i in ids.reverse do
    g ← g.tryClear i
  replaceMainGoal [g]

/-- `ved_decide_small`: a goal over a few small bit-vector fields (every free variable occurs as `BitVec.toNat v` with `v` a
variable of at most `2^14` values together) is closed by `decide +kernel` after the fields are generalised to bounded
`Nat` variables (`∀ a, a < 2^w → ..`): the case analysis `omega` does by splitting every `if` is one kernel evaluation.
Fails when another free variable remains. -/
def decideSmallCore : Lean.Elab.Tactic.TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let isAtom := fun (e : Expr) => e.isAppOfArity ``BitVec.toNat 2 && (e.getArg! 1).isFVar
  let mut atoms : Array Expr := #[]
  for o in Tools.VedU1WireShare.collectDag isAtom tgt do
    unless atoms.contains o do atoms := atoms.push o
  if atoms.isEmpty then throwError "ved_decide_small: no field"
  -- every free variable of the goal is under a collected atom
  let rest := atoms.foldl (fun (t : Expr) a => t.replace fun e => if e == a then some (mkNatLit 0) else none) tgt
  if rest.hasFVar then throwError "ved_decide_small: other variables"
  let mut cases : Nat := 1
  for a in atoms do
    let ty ← whnf (← inferType (a.getArg! 1))
    let some w := (ty.getArg! 0).nat? | throwError "ved_decide_small: width"
    cases := cases * 2 ^ w
  if cases > 16384 then throwError "ved_decide_small: too many cases"
  let mut names : Array (TSyntax `ident) := #[]
  let mut k := 0
  for a in atoms do
    let nm := mkIdent (Name.mkSimple s!"ved_ds_a{k}")
    let bn := mkIdent (Name.mkSimple s!"ved_ds_b{k}")
    let aS ← Term.exprToSyntax a
    let vS ← Term.exprToSyntax (a.getArg! 1)
    let hk := mkIdent (Name.mkSimple s!"ved_ds_h{k}")
    let ty ← whnf (← inferType (a.getArg! 1))
    let wS := Syntax.mkNumLit (toString ((ty.getArg! 0).nat?.getD 0))
    evalTactic (← `(tactic| generalize $hk:ident : $aS = $nm))
    evalTactic (← `(tactic| have $bn : $nm < 2 ^ $wS := by rw [← $hk:ident]; exact BitVec.isLt $vS))
    evalTactic (← `(tactic| clear $hk:ident))
    names := names.push nm
    k := k + 1
  for nm in names.reverse do
    evalTactic (← `(tactic| revert $nm))
  evalTactic (← `(tactic| decide +kernel))

elab "ved_decide_small" : tactic => do
  try decideSmallCore
  catch e =>
    dbgLog s!"decide_small: {← e.toMessageData.toString}"
    try dbgLog s!"{← Lean.Elab.Tactic.withMainContext (do return (← Lean.Meta.ppGoal (← Lean.Elab.Tactic.getMainGoal)).pretty)}" catch _ => pure ()
    throw e

initialize dbgShown : IO.Ref Nat ← IO.mkRef 0

def dbgT (label : String) : IO Unit := do
  dbgLog s!"T {label} t={← IO.monoMsNow} hb={(← IO.getNumHeartbeats) / 1000}"

/-- a goal of at least this many tree nodes gets the address rewrite of `ved_mem_addr` by `Expr.replace` instead of `rw` -/
def addrReplaceMinTree : Nat := 50000000

/-- `ved_mem_addr`: the `memState` atoms of the goal that differ only in the ADDRESS (the IR side spells it as `BitVec.ofNat aw`
of `Nat` arithmetic, the declaration side as `BitVec` arithmetic) are made the same atom: each other address is rewritten to
the first one, by an equality proved with `bv_omega` (the branch conditions of the enclosing `if`s are first propagated into the
branches).  Untrusted: the kernel checks the rewrites. -/
elab "ved_mem_addr" : tactic => withMainContext do
  -- cheap gate: nothing to unify unless two memState atoms differ only in the address (the simp below only drops branches)
  let tgt0 ← instantiateMVars (← getMainTarget)
  let isMem0 := fun (x : Expr) => x.isAppOf ``Sparkle.Core.Signal.Signal.memState && x.getAppNumArgs ≥ 9
  let mut seen0 : Array (Expr × Expr) := #[]
  let mut need := false
  for o in Tools.VedU1WireShare.collectDag isMem0 tgt0 do
    if o.hasLooseBVars then continue
    let args := o.getAppArgs
    let key := mkAppN o.getAppFn (args.extract 0 8)
    if seen0.any (fun (k, a) => k == key && a != args[8]!) then need := true; break
    seen0 := seen0.push (key, args[8]!)
  if !need then return
  dbgT "addr: gate passed"
  let g0 ← getMainGoal
  g0.setTag ((← g0.getTag) ++ `ved_addr)
  let isMem := fun (x : Expr) => x.isAppOf ``Sparkle.Core.Signal.Signal.memState && x.getAppNumArgs ≥ 9
  -- one rewrite per round, the atoms collected again after it (an address can contain another one: the rewrite of the
  -- inner one changes the outer one)
  let mut remaining := true
  for pass in [0:2] do
    if !remaining then break
    if pass == 1 then
      try evalTactic (← `(tactic| simp (config := {contextual := true}) only [↓reduceIte, ite_true, ite_false, if_true, if_false])) catch _ => pure ()
      dbgT "addr: contextual simp done"
    for _ in [0:8] do
      let tgt ← instantiateMVars (← getMainTarget)
      let occs := Tools.VedU1WireShare.collectDag isMem tgt
      let mut groups : Array (Expr × Array Expr) := #[]
      for o in occs do
        if o.hasLooseBVars then continue
        let args := o.getAppArgs
        let key := mkAppN o.getAppFn (args.extract 0 8)
        let a := args[8]!
        match groups.findIdx? (fun g => g.1 == key) with
        | some i => if !groups[i]!.2.contains a then groups := groups.set! i (key, groups[i]!.2.push a)
        | none => groups := groups.push (key, #[a])
      remaining := groups.any (fun g => g.2.size ≥ 2)
      let mut progress := false
      for (_, addrs) in groups do
        if progress then break
        if addrs.size < 2 then continue
        let rep := addrs[0]!
        let repS ← Term.exprToSyntax rep
        for a in addrs.toList.drop 1 do
          if progress then break
          let aS ← Term.exprToSyntax a
          if let some dir ← IO.getEnv "VED_DUMP_DIR" then
            let n := (← IO.monoMsNow)
            IO.FS.writeFile s!"{dir}/pair{n}.txt" s!"A: {← withOptions (fun o => o.setBool `pp.deepTerms true) (ppExpr a)}\n\nREP: {← withOptions (fun o => o.setBool `pp.deepTerms true) (ppExpr rep)}\n"
          try
            evalTactic (← `(tactic| (have hmaddr : $aS = $repS := by
                                       first | rfl | (apply BitVec.eq_of_toNat_eq; (try ved_clear_signals); (try ved_pack_simp); (try ved_bit_simp); (try ved_pack_simp); (try simp only [apply_ite BitVec.toNat, ved_toNat_append, BitVec.extractLsb'_toNat, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]); first | ved_decide_small | ((repeat' split); all_goals (try simp only [ved_toNat_append, BitVec.toNat_append, BitVec.extractLsb'_toNat, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]); all_goals (try ved_pack_simp); all_goals (first | omega | bv_omega))))))
            dbgT "addr: have done"
            -- `rw [hmaddr]` abstracts the occurrences by `kabstract`, a walk of the TREE (12 s per goal of 3e8 nodes, R34); on a goal
            -- the packing step takes (`addrReplaceMinTree`: R034, 3e8) the replacement is `Expr.replace` (cached by pointer: one visit per
            -- shared node) with the `congrArg` of the motive; below it the `rw` as before (R032, 1.7e7 nodes: `rw` abstracts the
            -- occurrences up to instances, the syntactic `Expr.replace` leaves some, and the closing `omega` then fails)
            let tgt ← instantiateMVars (← getMainTarget)
            let hm? ← if Tools.VedU1Loop.treeSizeVal tgt < addrReplaceMinTree then pure none else do
              -- the `have` made a new goal: its local context (not the one this tactic started with) holds `hmaddr`
              (← getMainGoal).withContext do
                let mut r : Option Expr := none
                for d in (← getLCtx).decls.toList.reverse do
                  if let some d := d then
                    if r.isNone && !d.isImplementationDetail then
                      if let some (_, l, rr) := (← instantiateMVars d.type).eq? then
                        if l == a && rr == rep then r := some d.toExpr
                pure r
            dbgT s!"addr: hm found={hm?.isSome} tgt-tree={Tools.VedU1Loop.treeSizeVal tgt}"
            if let some hm := hm? then
              let g ← getMainGoal
              -- in the context of the new goal: `hm` is a hypothesis of it, not of the context this tactic started with
              -- (`mkCongrArg` infers its type: "unknown free variable")
              g.withContext do
                let aTy ← inferType a
                let motive ← withLocalDeclD `ved_x aTy fun xv =>
                  mkLambdaFVars #[xv] (tgt.replace fun e => if e == a then some xv else none)
                let newTgt := tgt.replace fun e => if e == a then some rep else none
                replaceMainGoal [← g.replaceTargetEq newTgt (← mkCongrArg motive hm)]
            else
              evalTactic (← `(tactic| rw [hmaddr]))
            progress := true
            dbgT "addr: rewrite ok"
          catch e => dbgT "addr: equality failed"; dbgLog s!"no equality for {← ppExpr a}: {← e.toMessageData.toString}"
      if !progress then break

/-- `ved_mem_gen`: each `memState` application of the goal (no bound variable) is generalised to a variable `ved_mem_k` (in the
goal and in the hypotheses that mention it).  After `ved_mem_addr` the two sides of a data goal read the same memory atoms and
the rest is arithmetic over the register fields: the atoms (whose write ports are whole loop bodies) only make the goal a
large tree for `ved_wire`.  Untrusted: generalisation of a term by a variable. -/
elab "ved_mem_gen" : tactic => withMainContext do
  dbgT "gen: start"
  let isMem := fun (x : Expr) => x.isAppOf ``Sparkle.Core.Signal.Signal.memState && x.getAppNumArgs ≥ 9
  let tgt ← instantiateMVars (← getMainTarget)
  let mut occs : Array Expr := #[]
  for o in Tools.VedU1WireShare.collectDag isMem tgt do
    if o.hasLooseBVars || occs.contains o then continue
    occs := occs.push o
  let mut k := 0
  for o in occs do
    Tools.VedU1WireShare.generalizeDag o (Name.mkSimple s!"ved_mem{k}")
    k := k + 1
  dbgT "gen: done"

/-- `ved_lt2`: the side condition `x < 2` of the one-bit rewrite rules for the shapes that need no arithmetic (`y % 2`, `Bool.toNat b`,
a numeral, an `if` of those): `omega` reads every `Nat` hypothesis of the context (and the condition of each `if` after `split`),
which in a goal with state-field hypotheses is most of the cost of `ved_hyp_bits` -/
syntax "ved_lt2" : tactic
macro_rules
  | `(tactic| ved_lt2) =>
    `(tactic| first
      | exact Nat.one_lt_two
      | exact Nat.zero_lt_two
      | (apply Nat.mod_lt; exact Nat.zero_lt_two)
      | exact Bool.toNat_lt _
      | (split <;> ved_lt2))

/-- `ved_hyp_bits`: the hypotheses with a bit operation (`&&&`, `|||`, `^^^`) on `Nat` (the write enable of a memory
as the module computes it, `c1 &&& c2` of two conditions) are rewritten like the goal by `ved_bit_simp`'s rules and moved
into the goal, where the closing step splits their `if`s (`omega` does not read `if` or `&&&`).  Untrusted: `revert`. -/
elab "ved_hyp_bits" : tactic => withMainContext do
  let mut hs : Array (TSyntax `ident) := #[]
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      if (Tools.VedU1Loop.natBitOps (← instantiateMVars d.type)).size > 0 then
        hs := hs.push (mkIdent d.userName)
  dbgT s!"hyp: {hs.size} hyps"
  if hs.isEmpty then return
  try evalTactic (← `(tactic| simp (disch := first | ved_lt2 | ved_omega | (split <;> ved_omega) | fail) only
      [Tools.VedU1Loop.and_lt2_l, Tools.VedU1Loop.and_lt2_r, Tools.VedU1Loop.or_lt2, Tools.VedU1Loop.xor_lt2] at $[$hs]*))
  catch e => dbgLog s!"ved_hyp_bits simp: {← e.toMessageData.toString}"
  dbgT "hyp: simp done"
  if (← IO.getEnv "VED_DUMP_DIR").isSome then
    let g ← getMainGoal
    g.withContext do
      let mut sz := #[]
      for d in ← getLCtx do
        unless d.isImplementationDetail do
          if hs.any (·.getId == d.userName) then
            sz := sz.push s!"{d.userName}:{Tools.VedU1Loop.treeSizeVal (← instantiateMVars d.type)}/{(← getLCtx).size}"
      let gsz := Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← g.getType))
      dbgLog s!"hyp sizes {sz} goal={gsz}"
      if gsz < 100 then
        let nShown ← dbgShown.modifyGet fun n => (n, n + 1)
        if nShown < 3 then
          dbgLog s!"GOAL {← ppExpr (← instantiateMVars (← g.getType))}"
          for d in ← getLCtx do
            unless d.isImplementationDetail do
              if hs.any (·.getId == d.userName) then
                let t ← withOptions (fun o => o.setBool `pp.deepTerms true |>.insert `pp.maxSteps (10000000 : Nat)) do
                  return toString (← ppExpr (← instantiateMVars d.type))
                dbgLog s!"HYP {d.userName} ({t.length} chars) {(t.take 3000).toString} ..... {(t.drop (t.length - 1500)).toString}"
  let g ← getMainGoal
  try
    let names := hs.map (·.getId)
    let fvs ← g.withContext do
      return (← getLCtx).foldl (init := (#[] : Array FVarId)) fun a d =>
        if !d.isImplementationDetail && names.contains d.userName then a.push d.fvarId else a
    let (_, g') ← g.revert fvs (preserveOrder := true)
    replaceMainGoal [g']
    dbgLog "ved_hyp_bits: reverted"
  catch e => dbgLog s!"ved_hyp_bits revert: {← e.toMessageData.toString}"

/-- `ved_goal_gate n`: fail when more than `n` goals are open.  A heuristic limit (public option `ved.mem.goalGate`, read by the
entry), not a proof obligation and not a budget argument: the memory loop's case split (`peelAlt`) leaves 16-43 goals on the strict rows
and 842-843 on R029/R031, where the prelude was observed to spend the whole heartbeat budget before the per-goal stages; refusing right
after the split returns the same `[proof]` refusal at once.  Resource budgets are untouched; `n = 0` disables the gate. -/
elab "ved_goal_gate " n:num : tactic => do
  let k := (← getGoals).length
  if n.getNat != 0 && k > n.getNat then
    throwError "ved_goal_gate: {k} goals after the case split exceed the configured limit ved.mem.goalGate ({n.getNat}); \
      raise it with `set_option ved.mem.goalGate N` or disable the gate with `set_option ved.mem.goalGate 0`"

/-- `ved_stamp k`: (only with `VED_DUMP_DIR` set) append the time and the number of goals to `addr.log` -/
elab "ved_stamp " k:num : tactic => do
  if (← IO.getEnv "VED_DUMP_DIR").isSome then
    let gs ← getGoals
    let mut szs : Array Nat := #[]
    for g in gs do
      szs := szs.push (← g.withContext do return Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← g.getType)))
    dbgLog s!"STAMP {k.getNat} t={← IO.monoMsNow} hb={(← IO.getNumHeartbeats) / 1000} goals={gs.length} tree: total={szs.foldl (· + ·) 0} max={szs.foldl max 0} big(>100k)={(szs.filter (· > 100000)).size}"
    if let some st ← IO.getEnv "VED_STOP_AT" then
      if st.toNat? == some k.getNat then
        dbgLog s!"sizes {szs}"
        if let some pi ← IO.getEnv "VED_PROBE" then
          if let some g := gs[pi.toNat!]? then
            -- test only: context of the goal (let values, Signal-typed hypotheses included) and `ved_bit_simp` under a budget of its own
            g.withContext do
              for d in ← getLCtx do
                unless d.isImplementationDetail do
                  let ty ← instantiateMVars d.type
                  let vs := match d.value? with | some v => Tools.VedU1Loop.treeSizeVal v | none => 0
                  dbgLog s!"PROBE hyp {d.userName} type={Tools.VedU1Loop.treeSizeVal ty} value={vs} let={d.value?.isSome}"
            for variant in [0, 1] do
              let sv ← saveState
              setGoals [g]
              let hb0 ← IO.getNumHeartbeats
              let t0 ← IO.monoMsNow
              let r ← try
                  tryCatchRuntimeEx
                    (withLocalHb (400000 * 1000)
                      (Tactic.withoutRecover (evalTactic (← if variant == 0 then `(tactic| ved_bit_simp) else `(tactic| (clear_value *; ved_bit_simp))))))
                    fun _ => throwError "runtime exception (budget)"
                  pure "ok"
                catch e => pure s!"FAILED {(← e.toMessageData.toString).take 200}"
              dbgLog s!"PROBE bit_simp variant={variant} {r} hb={((← IO.getNumHeartbeats) - hb0) / 1000} ms={(← IO.monoMsNow) - t0}"
              sv.restore
            setGoals gs
        if let some l ← IO.getEnv "VED_DUMP_TGT" then
          for w in l.splitOn "," do
            if let some i := w.toNat? then
              if let some g := gs[i]? then
                let t ← g.withContext do
                  withOptions (fun o => (o.insert `format.width (200 : Nat)).setBool `pp.deepTerms true |>.insert `pp.maxSteps (10000000 : Nat)) do
                    return toString (← ppExpr (← instantiateMVars (← g.getType)))
                let dag := (Tools.VedU1WireShare.collectDag (fun _ => true) (← instantiateMVars (← g.getType))).size
                dbgLog s!"TARGET {i} dag={dag} chars={t.length}"
                IO.FS.writeFile s!"{(← IO.getEnv "VED_DUMP_DIR").getD "."}/target{i}.txt" (t.take 400000).toString
                let ctx ← g.withContext do
                  withOptions (fun o => (o.insert `format.width (200 : Nat)).setBool `pp.deepTerms true |>.insert `pp.maxSteps (10000000 : Nat)) do
                    let mut out := ""
                    for d in (← getLCtx) do
                      unless d.isImplementationDetail do
                        let ty ← instantiateMVars d.type
                        if (ty.find? fun e => e.isConst && e.constName!.getPrefix == `Sparkle.Core.Signal.Signal).isNone then
                          out := out ++ s!"{d.userName} : {← ppExpr ty}\n"
                    return out
                IO.FS.writeFile s!"{(← IO.getEnv "VED_DUMP_DIR").getD "."}/ctx{i}.txt" (ctx.take 100000).toString
        throwError "VED_STOP_AT {st}"

/-- `ved_addr_post`: after `ved_mem_addr` has found addresses to unify in a goal (it tags the goal `ved_addr`): the memory atoms
are generalised; in every goal the bit operations of the goal and of the hypotheses are rewritten. -/
elab "ved_addr_post" : tactic => do
  let g ← getMainGoal
  if (← g.getTag).toString.endsWith "ved_addr" then
    evalTactic (← `(tactic| ved_mem_gen))
  dbgT "post: start"
  evalTactic (← `(tactic| (try ved_bit_simp)))
  dbgT "post: bit_simp done"
  evalTactic (← `(tactic| (try ved_hyp_bits)))
  dbgT "post: hyp_bits done"

/-- `ved_if_read tac`: `all_goals (try tac)`, but with many goals (> 64: the 843-way split of the decoder) `tac` runs only on
the goals in which a `Signal.memoryComboRead` occurs (a DAG-wise test: `Expr.find?` visits shared subterms once);
the `memoryComboRead_val` simp has nothing to rewrite in the others.  With few goals always run: the simp set also
normalises bit operations that omega later needs (VedMemCheck memTwoMem, VedMemPackCheck pdBase). -/
elab "ved_if_read " t:tactic : tactic => do
  let gs ← getGoals
  let many := gs.length > 64
  let mut out : List MVarId := []
  for g in gs do
    setGoals [g]
    let run ← if !many then pure true else g.withContext do
      let e ← instantiateMVars (← g.getType)
      pure (e.find? fun e => e.isConstOf ``Sparkle.Core.Signal.Signal.memoryComboRead).isSome
    if run then
      evalTactic (← `(tactic| try ($t:tactic)))
    out := out ++ (← getGoals)
  setGoals out

/-- `ved_dsimp_goals`: `dsimp only at *` in every goal; with many goals (the 843-way split of the decoder) only the
target: the hypotheses of every goal are rescanned (`at *` costs more than 2M heartbeats there, the target alone 0.7M),
and the hypotheses are not what the later steps need in those goals.  With few goals (all small cases) `at *`:
omega needs the normalised hypotheses (VedMemCheck memTwoMem, VedMemPackCheck pdBase). -/
elab "ved_dsimp_goals" : tactic => do
  if (← getGoals).length ≤ 64 then
    evalTactic (← `(tactic| all_goals (try dsimp only at *)))
  else
    evalTactic (← `(tactic| all_goals (try dsimp only)))

/-- the side condition `hS` of the strong fixpoint equation -/
syntax "ved_causal " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

/-- the simp-based proof of the side condition (`ved_causal` without the `ved_causal_dag` alternative) -/
syntax "ved_causal_simp " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| ved_causal [$ex,*]) =>
    `(tactic| first | (ved_mem_budget 200000 (ved_causal_dag)) | (ved_causal_simp [$ex,*]))

macro_rules
  | `(tactic| ved_causal_simp [$ex,*]) =>
    `(tactic| (intro t s1 s2 h
               ved_tlog "causal: intro"
               -- a registered read's value at `t` unfolds only at `t = n + 1`
               rcases t with _ | t <;>
               ved_tlog "causal: rcases" <;>
               (try (ved_loop_simp [Sparkle.Core.Signal.Signal.memoryComboRead_val, Sparkle.Core.Signal.Signal.memory_val_succ, Sparkle.Core.Signal.Signal.memory_val_zero, Sparkle.Core.Signal.Signal.fst, Sparkle.Core.Signal.Signal.snd, $ex,*]))
               <;> ved_tlog "causal: simp1"
               <;> (try ved_loop_congr s1 s2 h)
               <;> (try ved_mem_congr s1 s2 h)
               <;> ved_tlog "causal: congr"
               <;> (try (ved_loop_simp [Tools.VedU1Lemmas.add_val_sc, Tools.VedU1Lemmas.add_val_cs, Tools.VedU1Lemmas.sub_val_sc, Tools.VedU1Lemmas.sub_val_cs, Tools.VedU1Lemmas.mul_val_sc, Tools.VedU1Lemmas.mul_val_cs, Tools.VedU1Lemmas.and_val_sc, Tools.VedU1Lemmas.and_val_cs, Tools.VedU1Lemmas.or_val_sc, Tools.VedU1Lemmas.or_val_cs, Tools.VedU1Lemmas.xor_val_sc, Tools.VedU1Lemmas.xor_val_cs, Tools.VedU1Lemmas.shl_val_sc, Tools.VedU1Lemmas.shl_val_cs, Tools.VedU1Lemmas.shr_val_sc, Tools.VedU1Lemmas.shr_val_cs, Tools.VedMemLoop.add_val_bs, Tools.VedMemLoop.add_val_sb, Tools.VedMemLoop.sub_val_bs, Tools.VedMemLoop.sub_val_sb, Tools.VedMemLoop.mul_val_bs, Tools.VedMemLoop.mul_val_sb, Tools.VedMemLoop.and_val_bs, Tools.VedMemLoop.and_val_sb, Tools.VedMemLoop.or_val_bs, Tools.VedMemLoop.or_val_sb, Tools.VedMemLoop.xor_val_bs, Tools.VedMemLoop.xor_val_sb, Tools.VedMemLoop.shl_val_bs, Tools.VedMemLoop.shl_val_sb, Tools.VedMemLoop.shr_val_bs, Tools.VedMemLoop.shr_val_sb, Tools.VedU1Lemmas.pure_val, Tools.VedU1Lemmas.mux_val, Tools.VedU1Lemmas.compl_val, Tools.VedU1Lemmas.bool_and_val, Tools.VedU1Lemmas.bool_or_val, Tools.VedU1Lemmas.bool_xor_val, Tools.VedU1Lemmas.bool_compl_val, h, Sparkle.Core.Signal.Signal.fst, Sparkle.Core.Signal.Signal.snd, $ex,*])))
               <;> ved_tlog "causal: simp2")

/-- `runSub` that, when a side condition stays open, says which (the first goal, cut to 2500 characters) -/
def runSubMem (m : MVarId) (tac : TSyntax `tactic) : TacticM Unit := do
  let saved ← getGoals
  setGoals [m]
  evalTactic tac
  let rest ← getGoals
  unless rest.isEmpty do
    let g ← ppGoal rest.head!
    let txt := (toString g).take 2500
    throwError "ved_loop_unfold_mem: a side condition is left open ({rest.length} goals); first:\n{txt}"
  setGoals saved

open Tools.VedU1WireShare in
/-- the loops of one goal (target and hypotheses), each once -/
def goalLoops (g : MVarId) : MetaM (Array Expr) := g.withContext do
  let mut loops := loopsDag (← instantiateMVars (← g.getType))
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      for l in loopsDag (← instantiateMVars d.type) do
        unless loops.contains l do loops := loops.push l
  return loops

open Tools.VedU1WireShare in
/-- the goal reads `(loop).val s` somewhere (target or hypotheses) -/
def hasValAt (g : MVarId) (loop s : Expr) : MetaM Bool := g.withContext do
  let isV := fun (e : Expr) => e.isAppOfArity ``Signal.val 4 && e.getArg! 2 == loop && e.getArg! 3 == s
  if !(collectDag isV (← instantiateMVars (← g.getType))).isEmpty then return true
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      if !(collectDag isV (← instantiateMVars d.type)).isEmpty then return true
  return false

open Tools.VedU1WireShare in
/-- `ved_loop_gen_mem s`: `ved_loop_gen_share s` with the loops of ALL goals (the goals of a memory body differ in the
spelling of the loop after the earlier simp steps; the share version reads the loops of the first goal only), and
each loop generalised (tuple taken apart, `Bool` components split) only in the goals that contain it -/
elab "ved_loop_gen_mem " s:ident : tactic => withMainContext do
  let sE ← elabTerm s.raw none
  let mut loops : Array Expr := #[]
  for g in ← getGoals do
    for l in ← goalLoops g do
      unless loops.contains l do loops := loops.push l
  if loops.isEmpty then
    evalTactic (← `(tactic| ved_loop_gen $s))
    return
  dbgLog s!"gen_mem: {loops.size} loops in {(← getGoals).length} goals hb={(← IO.getNumHeartbeats) / 1000}"
  for j in [0:loops.size] do
    dbgLog s!"gen_mem: loop {j} goals={(← getGoals).length} hb={(← IO.getNumHeartbeats) / 1000} t={← IO.monoMsNow}"
    let some α := loops[j]!.getAppArgs[1]? | throwError "ved_loop_gen_mem: malformed Signal.loop"
    let bare := !(← whnfR α).isAppOf ``Prod
    let n := (← Tools.VedU1Loop.stateComps α).length
    let X := mkIdent (Name.mkSimple s!"ved_X{j}")
    let xs := (List.range (if bare then 1 else n + 1)).toArray.map fun i => mkIdent (Name.mkSimple s!"ved_x{j}_{i}")
    let pats ← xs.mapM fun x => `(Lean.Parser.Tactic.rcasesPatLo| $x:ident)
    let mut gsOut : List MVarId := []
    for g in ← getGoals do
      setGoals [g]
      unless (← hasValAt g loops[j]! sE) do
        gsOut := gsOut ++ [g]
        continue
      let v ← g.withContext <| mkAppM ``Sparkle.Core.Signal.Signal.val #[loops[j]!, sE]
      generalizeDag v (if bare then Name.mkSimple s!"ved_x{j}_0" else X.getId)
      unless bare do evalTactic (← `(tactic| all_goals rcases $X:ident with ⟨$pats,*⟩))
      for x in xs do
        let some d := (← withMainContext getLCtx).findFromUserName? x.getId | continue
        if (← whnfR d.type).isConstOf ``Bool then
          evalTactic (← `(tactic| all_goals cases $x:ident))
      gsOut := gsOut ++ (← getGoals)
    setGoals gsOut


/-- `m` with every hypothesis cleared that neither its type nor (transitively) the type of a kept hypothesis mentions:
the side conditions of the strong fixpoint equation are about the loop only, and every `simp`/`omega` call in them
scans the local context (R29: 38 hypotheses of the step case against 5, 30x slower) -/
def clearOthers (m : MVarId) : MetaM MVarId := m.withContext do
  let mut keep : Std.HashSet FVarId := {}
  let mut todo : Array Expr := #[← instantiateMVars (← m.getType)]
  while !todo.isEmpty do
    let e := todo.back!
    todo := todo.pop
    for fv in (collectFVars {} e).fvarIds do
      unless keep.contains fv do
        keep := keep.insert fv
        todo := todo.push (← instantiateMVars (← fv.getType))
        if let some v ← fv.getValue? then todo := todo.push (← instantiateMVars v)
  let mut drop : Array FVarId := #[]
  for d in ← getLCtx do
    unless d.isImplementationDetail || keep.contains d.fvarId do drop := drop.push d.fvarId
  let (m', _) ← m.tryClearMany' drop
  return m'

/-- diagnosis hook: called with the closed causal side condition (the mvar `hSc`) right after `ved_causal` closed it.  A no-op
(`none`) unless a diagnosis module (`Tools/VedMemCausalProbe.lean`, imported only by diagnosis cases) installs a function in its
`initialize`; production modules never install one. -/
initialize causalHook : IO.Ref (Option (MVarId → TacticM Unit)) ← IO.mkRef none

/-- The loop-size gate (public option `ved.mem.loopGate`, read by the entry): refuse a loop of more than `gate` tree nodes.  Comparison:
the loop is refused when `treeSize > gate` (a limit equal to the tree size accepts, one less refuses).  `gate = 0` is off and the tree size is
NOT computed (no walk of the loop at all).

PLACEMENT (implemented in `ved_loop_unfold_mem`): the gate guards only the simp-based causal side condition (`ved_causal_simp`), the one whose
cost grows with the size of the tree; it is a separate step.  Option `ved.mem.causalDag` on: the DAG walk (`ved_causal_dag` under
`ved_mem_budget 200000`, as in `ved_causal`) runs FIRST and is never refused by the gate; only when the walk fails (tactic state restored) the
gate is checked, then `ved_causal_simp` runs.  Option off: the gate is checked right before `ved_causal [..]` (whose walk alternative refuses
at once), unchanged.  The new method is never refused by the tree threshold. -/
def loopGateCheck (L : Expr) (gate : Nat) : MetaM Unit := do
  if gate == 0 then return
  let loopTree := Tools.VedU1Loop.treeSizeVal L
  if loopTree > gate then
    throwError "ved_loop_unfold_mem: the loop has {loopTree} tree nodes, more than the configured limit ved.mem.loopGate ({gate}); \
      raise it with `set_option ved.mem.loopGate N` or disable the gate with `set_option ved.mem.loopGate 0`"

/-- `(limit := n)`: the limit prefix of `ved_loop_unfold_mem` -/
syntax vedLoopLimit := "(" &"limit" " := " num ")"

open Tools.VedU1WireShare in
/-- `ved_loop_unfold_mem t`: rewrite `(Signal.loop F).val t` by the strong fixpoint equation, for every loop
whose value at `t` occurs in the goal (the walk of `ved_loop_unfold_share`, the lemma and the side
conditions changed) -/
elab "ved_loop_unfold_mem " lim:(vedLoopLimit)? " [" ex:Lean.Parser.Tactic.simpLemma,* "]" t:term : tactic => withMainContext do
  -- `(limit := n)`: the public option `ved.mem.loopGate`, read by the entry (absent or 0: no gate)
  let gate := match lim with
    | some l => (l.raw.getArg 3).isNatLit?.getD 0
    | none => 0
  let tgt0 ← instantiateMVars (← getMainTarget)
  let tE ← instantiateMVars (← Term.elabTerm t (some (mkConst ``Nat)))
  let tE ← instantiateMVars tE
  let isOcc0 := fun (x : Expr) =>
    x.isAppOfArity ``Signal.val 4 && (x.getArg! 2).isAppOfArity ``Signal.loop 4
  let occs := fun (e : Expr) => do
    let mut out : Array Expr := #[]
    for x in collectDag isOcc0 e do
      if x.getArg! 3 == tE || (← withReducible <| isDefEq (x.getArg! 3) tE) then out := out.push x
    pure out
  if (← occs tgt0).isEmpty then return
  for _ in [0:64] do
    let tgt ← instantiateMVars (← getMainTarget)
    let some lhs := (← occs tgt)[0]? | break
    let L := lhs.getArg! 2
    let f4 := mkApp4 (mkConst ``Tools.VedMem.loop_val_unfold_strong) (L.getArg! 0) (L.getArg! 1) (L.getArg! 2) (L.getArg! 3)
    let ty ← whnf (← inferType f4)
    let h0T := ty.bindingDomain!
    let h0 ← mkFreshExprMVar h0T
    let ty ← whnf (ty.bindingBody!.instantiate1 h0)
    let hS ← mkFreshExprMVar ty.bindingDomain!
    runSubMem h0.mvarId! (← `(tactic| (intro _ _; rfl)))
    let tc0 ← IO.monoMsNow
    -- the debug line walks the loop (tree size, dag): only when the stage log is on
    if (← IO.getEnv "VED_DUMP_DIR").isSome then
      dbgLog s!"unfold_mem: loop dag={(collectDag (fun _ => true) L).size} tree={Tools.VedU1Loop.treeSizeVal L} hS ctx={(← hS.mvarId!.getDecl).lctx.size} hStype dag={(collectDag (fun _ => true) (← instantiateMVars (← hS.mvarId!.getType))).size} t={tE} nocc={(← occs tgt).size}"
    let hb0 ← IO.getNumHeartbeats
    let hSc ← clearOthers hS.mvarId!
    dbgLog s!"unfold_mem: clearOthers done ms={(← IO.monoMsNow) - tc0}"
    -- the gate guards only the simp-based causal discharge (see `loopGateCheck`).  Option `ved.mem.causalDag` on: the walk runs FIRST
    -- (the walk of the `ved_causal` macro, same budget); only when it fails (state restored) the gate is checked, then `ved_causal_simp`.
    -- Option off: the gate, then `ved_causal` (its walk alternative refuses at once, so the simp path), as before.
    -- a user-supplied lemma (option `ved.mem.userLemma`, `Tools/VedSupplement.lean`) closes this condition INSTEAD of the automatic discharge
    -- (no gate, no `ved_causal*`); a mismatch is a refusal.  Option empty (default): the branches below, unchanged.
    if let some lemName := Tools.VedSupplement.optionLemma (← getOptions) then
      Tools.VedSupplement.applyUserLemma hSc lemName
    else if (← getOptions).getBool `ved.mem.causalDag false then
      let st ← saveState
      let walked ← try runSubMem hSc (← `(tactic| ved_mem_budget 200000 (ved_causal_dag))); pure true
        catch _ => st.restore; pure false
      unless walked do
        loopGateCheck L gate
        runSubMem hSc (← `(tactic| ved_causal_simp [$ex,*]))
    else
      loopGateCheck L gate
      runSubMem hSc (← `(tactic| ved_causal [$ex,*]))
    if let some hook ← causalHook.get then hook hSc
    dbgLog s!"unfold_mem: causal ms={(← IO.monoMsNow) - tc0} hb={((← IO.getNumHeartbeats) - hb0) / 1000}"
    let lem ← instantiateMVars (mkApp3 f4 h0 hS (lhs.getArg! 3))
    let eqTy ← instantiateMVars (← inferType lem)
    let some (_, l, r) := eqTy.eq? | throwError "ved_loop_unfold_mem: unexpected equation {eqTy}"
    unless l == lhs do throwError "ved_loop_unfold_mem: the occurrence is not the left side of the equation"
    let xTy ← inferType lhs
    let motive ← withLocalDeclD `ved_x xTy fun xv =>
      mkLambdaFVars #[xv] (tgt.replace fun e => if e == lhs then some xv else none)
    let pf ← mkCongrArg motive lem
    let newTgt := tgt.replace fun e => if e == lhs then some r else none
    let g ← getMainGoal
    let g' ← g.replaceTargetEq newTgt pf
    dbgLog s!"unfold_mem: replaced, ms since causal start={(← IO.monoMsNow) - tc0}"
    replaceMainGoal [g']

/-- `ved_or_lit_m`: `Tools.VedU1Loop`'s `ved_or_lit` with fewer `omega` calls per candidate: the least `w` with `x < 2^w` is found by
bisection over `[0, 64]` after one test at `64` (a candidate whose operand has no such bound costs one call, not 65) -/
elab "ved_or_lit_m" : tactic => withMainContext do
  let t0 ← IO.monoMsNow
  let calls ← IO.mkRef 0
  let mut nc := 0
  let mut skip : Array Lean.Expr := #[]
  for _ in [0:64] do
    if (← getGoals).isEmpty then break
    let tgt ← instantiateMVars (← getMainTarget)
    let cands := (Tools.VedU1Loop.natOrs tgt).filter (!skip.contains ·)
    let some t := cands[0]? | break
    nc := nc + 1
    let a := t.getArg! 4
    let b := t.getArg! 5
    let mut done := false
    for (c, x, swapped) in [(a, b, false), (b, a, true)] do
      if done then break
      let ltW := fun (w : Nat) => do
        calls.modify (· + 1)
        Tools.VedU1Loop.omegaProof? (← mkAppM ``LT.lt #[x, ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit w]])
      let some pf64 ← ltW 64 | continue
      let mut lo := 0
      let mut hi := 64
      let mut best : Lean.Expr := pf64
      while lo < hi do
        let mid := (lo + hi) / 2
        if let some pf ← ltW mid then
          hi := mid
          best := pf
        else lo := mid + 1
      let w := hi
      let hx ← if lo == 64 then pure pf64 else pure best
      let pc ← mkEq (← mkAppM ``HMod.hMod #[c, ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit w]]) (mkNatLit 0)
      calls.modify (· + 1)
      let some hc ← Tools.VedU1Loop.omegaProof? pc | continue
      let lem ← mkAppM ``Tools.VedU1Lemmas.or_hi #[c, x, mkNatLit w, hx, hc]
      let lemS ← Term.exprToSyntax lem
      if swapped then
        let cs ← Term.exprToSyntax c
        let xs ← Term.exprToSyntax x
        evalTactic (← `(tactic| rw [Nat.or_comm $xs $cs, $lemS:term]))
      else
        evalTactic (← `(tactic| rw [$lemS:term]))
      done := true
    unless done do skip := skip.push t
  dbgLog s!"or_lit_m: cands={nc} omega={← calls.get} ms={(← IO.monoMsNow) - t0}"

/-- `ved_pack_wire_all` with a stage-log line per goal (tree size, time, heartbeats; only with `VED_DUMP_DIR`) -/
elab "ved_pack_wire_all_m" : tactic => do
  let gs ← getGoals
  let mut rest : List MVarId := []
  let mut i := 0
  let mut allSz : Array Nat := #[]
  for g in gs do
    allSz := allSz.push (← g.withContext do return Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← g.getType)))
  dbgLog s!"wire sizes {allSz}"
  if (← IO.getEnv "VED_DUMP_DIR").isSome then
    -- which goals have the same target / hypotheses (fvars read by their user names)
    let mut norm : Array (Expr × Array (Name × Expr)) := #[]
    for g in gs do
      let (t, hs) ← g.withContext do
        let lctx ← getLCtx
        let nm : Expr → Expr := fun e => e.replace fun x => match x with
          | .fvar f => some (mkConst ((lctx.get! f).userName))
          | _ => none
        let t ← instantiateMVars (← g.getType)
        let mut hs : Array (Name × Expr) := #[]
        for d in lctx do
          unless d.isImplementationDetail do hs := hs.push (d.userName, nm (← instantiateMVars d.type))
        pure (nm t, hs)
      norm := norm.push (t, hs)
    let mut line := ""
    for a in [0:norm.size] do
      let mut firstT := a
      let mut firstTH := a
      for j in [0:a] do
        if firstT == a && norm[j]!.1 == norm[a]!.1 then firstT := j
        if firstTH == a && norm[j]!.1 == norm[a]!.1 && norm[j]!.2 == norm[a]!.2 then firstTH := j
      line := line ++ s!" {a}:{firstT}/{firstTH}"
    dbgLog s!"wire same-target/same-target+hyps first index:{line}"
  for g in gs do
    setGoals [g]
    let sz ← g.withContext do return Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← g.getType))
    let h0 ← IO.getNumHeartbeats
    let t0 ← IO.monoMsNow
    evalTactic (← `(tactic| ved_pack_wire))
    dbgLog s!"wire goal {i}: size={sz} ms={(← IO.monoMsNow) - t0} hb={((← IO.getNumHeartbeats) - h0) / 1000}"
    i := i + 1
    rest := rest ++ (← getGoals)
  setGoals rest


/-! `ved_hin_simp M`: the input-bound / reset hypotheses `hin`, `hrst` of the step case, as `simp [C, contractOf, ..., M, declWidth]`
would produce them, WITHOUT unfolding the module constant `M` (a literal as large as the design: the plain `simp` runs out of
steps on it, `decoderPipeline`).  The closed subterms `Contract.dataInputs _` / `Contract.clkRst _` are evaluated by `reduce`
(replaceLocalDeclDefEq, the kernel re-checks the defeq), and each `declWidth M "name"` is stated as an equation proved by
`rfl` (kernel evaluation) and handed to `simp`. -/
elab "ved_hin_simp " m:term : tactic => withMainContext do
  let M ← elabTerm m none
  let names := #[`hin, `hrst]
  let ref ← IO.mkRef (#[] : Array Expr)
  for nm in names do
    let fv := (← getLCtx).findFromUserName? nm |>.map (·.fvarId)
    let some fv := fv | throwError "ved_hin_simp: no {nm}"
    let ty ← instantiateMVars (← fv.getType)
    let ty' ← Meta.transform ty (pre := fun e => do
      if !e.hasLooseBVars && (e.isAppOf ``Tools.VedU1Contract.Contract.dataInputs || e.isAppOf ``Tools.VedU1Contract.Contract.clkRst) then
        return .done (← reduce e)
      else return .continue)
    dbgLog s!"hin_simp: reduced {nm}"
    replaceMainGoal [← (← getMainGoal).replaceLocalDeclDefEq fv ty']
    dbgLog s!"hin_simp: replaced {nm}"
    discard <| Meta.transform ty' (pre := fun e => do
      if e.isAppOfArity ``Sparkle.IR.AST.Port.mk 2 then ref.modify (·.push (e.getArg! 0))
      return .continue)
  let mut ids : Array Name := #[]
  let mut i := 0
  for n in (← ref.get) do
    let lhs := mkApp2 (mkConst ``Tools.VedU1Contract.declWidth) M n
    let v ← whnf lhs
    let some k := v.rawNatLit? <|> v.nat? | throwError "ved_hin_simp: width of {n} is not a numeral: {v}"
    let nm := Name.mkSimple s!"ved_hw{i}"
    i := i + 1
    let g ← getMainGoal
    let (_, g') ← (← g.assert nm (← mkEq lhs (mkNatLit k)) (← mkEqRefl lhs)).intro1P
    replaceMainGoal [g']
    ids := ids.push nm
  let hs ← ids.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let hsSep : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," := Syntax.TSepArray.ofElems hs
  dbgLog s!"hin_simp: {ids.size} widths"
  evalTactic (← `(tactic| simp [$hsSep,*] at $(mkIdent `hin):ident $(mkIdent `hrst):ident))

end Tools.VedMemLoop
