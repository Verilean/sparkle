import Lean
import Tools.VedMem
import Tools.VedU1Entry
import Tools.VedU1WireShare
import Tools.VedMemNest

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

/-- option `ved.mem.h0Dag` (default false): the base case (h0) of the memory loop is first tried with `ved_h0_dag_close` (see there), the old
`ved_loop_simp` step stays the fallback -/
register_option ved.mem.h0Dag : Bool := {
  defValue := false
  descr := "try the lazy base-case closer (no simp over the loop's registers' inputs) first for h0 of the memory loop; the old step stays the fallback"
}

/-- `ved_h0_dag_on`: fails (fixed text) unless the option `ved.mem.h0Dag` is on -/
elab "ved_h0_dag_on" : tactic => do
  unless (← getOptions).getBool `ved.mem.h0Dag false do throwError "ved_h0_dag: option ved.mem.h0Dag is off"

/-- diagnosis seam (never set by production code): `ved_h0_mark 0` (start of `case h0`) records the h0 goal, `ved_h0_mark 1` (before the h0 step) the
time and the heartbeats, `ved_h0_done` (after it) calls the hook with the goal and the elapsed ms / thousand heartbeats of the h0 step.
Installed by `Tools.VedMemCausalProbe`; without a hook all three do nothing but store two numbers. -/
initialize h0Mark : IO.Ref (Option (MVarId × Nat × Nat)) ← IO.mkRef none
initialize h0Hook : IO.Ref (Option (MVarId → Nat → Nat → TacticM Unit)) ← IO.mkRef none

elab "ved_h0_mark " k:num : tactic => do
  if k.getNat == 0 then
    h0Mark.set (some ((← getMainGoal), 0, 0))
  else if let some (g, _, _) ← h0Mark.get then
    h0Mark.set (some (g, ← IO.monoMsNow, ← IO.getNumHeartbeats))

elab "ved_h0_done" : tactic => do
  if let some hook ← h0Hook.get then
    if let some (g, t0, hb0) ← h0Mark.get then
      hook g ((← IO.monoMsNow) - t0) (((← IO.getNumHeartbeats) - hb0) / 1000)

/-- test seam of `ved_h0_dag_close` (the fallback control of `Tests/Ved/VedMemCloseCheck.lean`): when set, the closer refuses.  Never set by production code. -/
initialize h0DagRefuse : IO.Ref Bool ← IO.mkRef false

/-- `ved_h0_dag_close`: closes a goal `a = b` of h0 (`st0 c m name = (X.val 0).proj.toNat`, X a bundle of `Signal.register init x`) by `Eq.refl`
after one `isDefEq`.  At time 0 a register's value is its initial value whatever its input is, so the check reduces the spine of `X` only: the
registers' inputs (the loop body, the 1.76e12-tree of R033) are never visited, no simp rewrite of them.  Under its own local budget
(`ved_mem_budget`, 100000 thousand heartbeats), so that a refusal leaves the old step what is left.  Fails (fixed text) when the sides are not
defeq; the tactic state is restored by the surrounding `first`. -/
elab "ved_h0_dag_close" : tactic => withMainContext do
  let g ← getMainGoal
  let some (_, l, r) := (← instantiateMVars (← g.getType)).eq? | throwError "ved_h0_dag: the goal is not an equation"
  if (← h0DagRefuse.get) then throwError "ved_h0_dag: refused (test seam)"
  let ok ← tryCatchRuntimeEx
    (do withLocalHb (100000 * 1000) (Tactic.withoutRecover (do
          unless (← isDefEq l r) do throwError "ved_h0_dag: the two sides do not reduce to the same value"
          g.assign (← mkEqRefl l)))
        pure true)
    fun e => if e.isRuntime then pure false else throw e
  unless ok do throwError "ved_h0_dag: local heartbeat budget exhausted"
  replaceMainGoal []

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

register_option ved.mem.causalDagBudget : Nat := {
  defValue := 200000
  descr := "local heartbeat budget of the lock-step walk `ved_causal_dag` (same units as `ved_mem_budget`: thousands of heartbeats; \
    0 = no local cap, only the ambient budget); when it runs out the simp-based `ved_causal` follows"
}

/-- `ved_causal_budget t`: `ved_mem_budget n t` with `n` the option `ved.mem.causalDagBudget` (read when the tactic runs; the macro of
`ved_causal` cannot hold the option value as a literal).  `n = 0`: `t` runs under the ambient budget only (state restored on a
runtime failure as in `ved_mem_budget`). -/
elab "ved_causal_budget " t:tactic : tactic => do
  let n := ved.mem.causalDagBudget.get (← getOptions)
  let s ← saveState
  let ok ← tryCatchRuntimeEx (do
      if n == 0 then Tactic.withoutRecover (evalTactic t)
      else withLocalHb (n * 1000) (Tactic.withoutRecover (evalTactic t))
      pure true)
    fun e => do
      s.restore
      if e.isRuntime then pure false else throw e
  unless ok do throwError "ved_causal_budget: local heartbeat budget exhausted"

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

/-! Diagnosis of the walk (ONLY with `VED_DUMP_DIR`; every counter below is a no-op without it, no string is built outside the gate). -/
initialize dgGate : Bool ← dbgOn

/-- counters of one `ved_causal_dag` walk -/
structure DagStats where
  rules : Std.HashMap String Nat := {}
  sizes : Std.HashMap String (Nat × Nat × Nat) := {}
  seen : Std.HashSet (Expr × Expr) := {}
  calls : Nat := 0
  depth : Nat := 0
  maxDepth : Nat := 0
  splitDepth : Nat := 0
  maxSplitDepth : Nat := 0
  instrHb : Nat := 0
  hb0 : Nat := 0
  t0 : Nat := 0
  deriving Inhabited

initialize dgStats : IO.Ref DagStats ← IO.mkRef {}

def stBump (k : String) : IO Unit := do
  if dgGate then dgStats.modify fun s => { s with rules := s.rules.insert k (s.rules.getD k 0 + 1) }

/-- the number of distinct nodes (by pointer) of `e` -/
unsafe def dagNodesUnsafe (e : Expr) : Nat :=
  let rec go (e : Expr) : StateM (Std.HashSet USize) Unit := do
    let p := ptrAddrUnsafe e
    if (← get).contains p then return
    modify (·.insert p)
    match e with
    | .app f a => do go f; go a
    | .lam _ t b _ => do go t; go b
    | .forallE _ t b _ => do go t; go b
    | .letE _ t v b _ => do go t; go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()
  ((go e).run {}).2.size
@[implemented_by dagNodesUnsafe] def dagNodes (_ : Expr) : Nat := 0

/-- count, max and sum of the pointer-DAG sizes of the terms recorded under `k` (the heartbeats spent measuring are counted apart) -/
def stSize (k : String) (e : Expr) : IO Unit := do
  if dgGate then
    let h0 ← IO.getNumHeartbeats
    let n := dagNodes e
    let h1 ← IO.getNumHeartbeats
    dgStats.modify fun s =>
      let (c, m, t) := s.sizes.getD k (0, 0, 0)
      { s with sizes := s.sizes.insert k (c + 1, max m n, t + n), instrHb := s.instrHb + (h1 - h0) }

def stRender : IO String := do
  let s ← dgStats.get
  let hb ← IO.getNumHeartbeats
  let rs := s.rules.toArray.qsort (fun a b => a.1 < b.1)
  let zs := s.sizes.toArray.qsort (fun a b => a.1 < b.1)
  return s!"calls={s.calls} depth={s.depth}/max {s.maxDepth} splitDepth={s.splitDepth}/max {s.maxSplitDepth} seen={s.seen.size} hb={(hb - s.hb0) / 1000} instrHb={s.instrHb / 1000} ms={(← IO.monoMsNow) - s.t0} rules=[{", ".intercalate (rs.toList.map fun (k, n) => s!"{k}:{n}")}] sizes(count/max/sum)=[{", ".intercalate (zs.toList.map fun (k, (c, m, t)) => s!"{k}:{c}/{m}/{t}")}]"

def stReset : IO Unit := do
  if dgGate then dgStats.set { hb0 := ← IO.getNumHeartbeats, t0 := ← IO.monoMsNow }

def stEnter : IO Unit := do
  if dgGate then
    dgStats.modify fun s => { s with calls := s.calls + 1, depth := s.depth + 1, maxDepth := max s.maxDepth (s.depth + 1) }
    let s ← dgStats.get
    if s.calls % 2000 == 0 then dbgLog s!"causal_dag progress {← stRender}"

def stLeave : IO Unit := do
  if dgGate then dgStats.modify fun s => { s with depth := s.depth - 1 }

def stSplit (d : Int) : IO Unit := do
  if dgGate then dgStats.modify fun s =>
    let n := (s.splitDepth + d).toNat
    { s with splitDepth := n, maxSplitDepth := max s.maxSplitDepth n }

/-- the scalar the signal `X` has at cycle `k` (`Signal.val X k` unfolded to the body of its `Signal.mk`) -/
def unfoldValDag (memo : IO.Ref (Std.HashMap Expr Expr)) (A : Expr) : MetaM Expr := do
  let X := A.getArg! 2
  let k := A.getArg! 3
  -- the same signal is unfolded at many pairs (other cycles, other sides): its head normal form is computed once per walk
  let Xw ← match (← memo.get)[X]? with
    | some w => do stBump "whnf-memo-hit"; pure w
    | none => do
      let w ← whnf X
      if w.isAppOfArity ``Sparkle.Core.Signal.Signal.mk 3 then memo.modify (·.insert X w)
      pure w
  stSize "whnf-sig" Xw
  unless Xw.isAppOfArity ``Sparkle.Core.Signal.Signal.mk 3 do
    dbgLogWith do return s!"causal_dag: signal [{(toString (← ppExpr X)).take 200}] whnf [{(toString (← ppExpr Xw)).take 200}]"
    throwError "ved_causal_dag: signal does not unfold to Signal.mk"
  let r := (mkApp (Xw.getArg! 2) k).headBeta
  if dgGate then
    stSize "unfold-val" r
    stSize s!"unfold-by {X.getAppFn.constName?.getD `none}" r
  return r

/-! ### Scope levels, computed compositionally

A cache scope has a depth (the root is 0, a scope made by `DagCache.scope` is its parent's depth + 1).  Every binder variable the
walk introduces (`funext` variable, `memState` side `j`/`hj`, the `a b`/`t' ht a b hab` of the two premises of `loopDag`, the
variables of a `Nat.casesOn` case) is registered with the depth of the scope it is introduced in; the variables of the goal
context (`t s1 s2 h`, the statement's own variables) have depth 0.  The LEVEL MASK of a term or proof is the set of depths of the
variables it mentions, a `Nat` with bit `d` set when a variable of depth `d` occurs.  `dagEq` returns the mask of its proof next to
the proof, and builds it from the pieces: the masks of the child proofs, the masks of the terms the proof is built on (by the
pointer-memoised `termMask`, shared across the whole walk, `hasFVar` prunes closed subterms), the mask of a leaf proof (the leaf
proof is a few nodes: traversed once), and, when a scope is closed by `mkLambdaFVars` over its binders, the mask without that
scope's bit.  A proof whose mask has highest bit `L` mentions only variables of the scopes `0..L` of the chain, so it is stored in
the scope of depth `L` of the chain: it is well-typed in that scope and in every scope below it, siblings included. -/

/-- the pieces shared by all scopes of one walk -/
structure DagShared where
  /-- depth of the scope that introduced a binder variable (absent = 0) -/
  lv : IO.Ref (Std.HashMap FVarId Nat)
  /-- pointer-memo of the level mask of a term (the term is kept alive so that the pointer is not reused) -/
  memo : IO.Ref (Std.HashMap USize (Expr × Nat))
  /-- `whnf` of the signals `unfoldValDag` unfolds (only the results that are a `Signal.mk`), for the whole walk -/
  whnfMemo : IO.Ref (Std.HashMap Expr Expr)
  nextId : IO.Ref Nat

/-- cache hits of the walk (always counted; reset at the start of `ved_causal_dag`): own scope, a scope around, an entry promoted from a scope that is not around the reader (sibling-shared), and the promoted inserts -/
structure DagHits where
  own : Nat := 0
  ancestor : Nat := 0
  shared : Nat := 0
  promoted : Nat := 0
  inserts : Nat := 0
  deriving Inhabited

initialize dgHits : IO.Ref DagHits ← IO.mkRef {}

/-- (ms, thousand heartbeats) of the last `ved_causal_dag` walk (all goals of the side condition), for the probe -/
initialize dgWalk : IO.Ref (Nat × Nat) ← IO.mkRef (0, 0)

def hitsRender : IO String := do
  let h ← dgHits.get
  return s!"hits(own/ancestor/sibling-shared)={h.own}/{h.ancestor}/{h.shared} inserts={h.inserts} promoted={h.promoted}"

/-- check mode (tests): every stored proof is traversed and its true mask compared with the composed one -/
register_option ved.mem.causalDagMaskCheck : Bool := {
  defValue := false
  descr := "check the composed level mask of every stored proof of `ved_causal_dag` against a traversal (tests)"
}

structure DagEntry where
  proof : Expr
  mask : Nat
  /-- id of the scope the proof was built in -/
  by_ : Nat

/-- the cache of the walk, by pair of subterms, SCOPED: a scope reads the entries of the scopes around it.  An entry is stored in the
scope of the depth of its proof's highest level bit (see above), which is a scope around the one that built it (or the same). -/
structure DagCache where
  own : IO.Ref (Std.HashMap (Expr × Expr) DagEntry)
  parent : Option DagCache
  depth : Nat
  id : Nat
  sh : DagShared

namespace DagCache
def newShared : IO DagShared := return { lv := ← IO.mkRef {}, memo := ← IO.mkRef {}, whnfMemo := ← IO.mkRef {}, nextId := ← IO.mkRef 1 }
def new : IO DagCache := return { own := ← IO.mkRef {}, parent := none, depth := 0, id := 0, sh := ← newShared }
/-- the cache of a new binder scope inside `c` -/
def scope (c : DagCache) : IO DagCache := do
  stBump "scope-new"
  let id ← c.sh.nextId.modifyGet fun n => (n, n + 1)
  return { own := ← IO.mkRef {}, parent := some c, depth := c.depth + 1, id, sh := c.sh }
/-- the scope of depth `d` among `c` and the scopes around it -/
partial def at_ (c : DagCache) (d : Nat) : DagCache :=
  if c.depth ≤ d then c else match c.parent with | some q => q.at_ d | none => c
/-- is the scope of id `i` `c` or around `c`? -/
partial def hasId (c : DagCache) (i : Nat) : Bool :=
  c.id == i || (match c.parent with | some q => q.hasId i | none => false)
/-- the entry of the pair and the scope it was found in -/
partial def findE? (c : DagCache) (k : Expr × Expr) : IO (Option (DagEntry × DagCache)) := do
  let m ← c.own.get
  match m[k]? with
  | some e => return some (e, c)
  | none => match c.parent with
    | some q => q.findE? k
    | none => return none
def find? (c : DagCache) (k : Expr × Expr) : IO (Option Expr) := do
  return (← c.findE? k).map (·.1.proof)
/-- store a proof of the mask `mask` for the pair `k` found in the scope `c`: in the scope of depth `highest bit of mask` -/
def store (c : DagCache) (k : Expr × Expr) (p : Expr) (mask : Nat) : IO Unit := do
  let l := if mask == 0 then 0 else min (Nat.log2 mask) c.depth
  let target := c.at_ l
  target.own.modify (·.insert k { proof := p, mask, by_ := c.id })
  dgHits.modify fun h => { h with inserts := h.inserts + 1, promoted := h.promoted + (if l < c.depth then 1 else 0) }
/-- store in the scope `c` itself (the level of the proof is not tracked) -/
def insert (c : DagCache) (k : Expr × Expr) (p : Expr) : IO Unit :=
  c.own.modify (·.insert k { proof := p, mask := 0, by_ := c.id })
/-- register the binder variables of the scope `c` -/
def regAt (c : DagCache) (d : Nat) (xs : Array Expr) : IO Unit :=
  c.sh.lv.modify fun m => xs.foldl (fun m x => if x.isFVar then m.insert x.fvarId! d else m) m
def reg (c : DagCache) (xs : Array Expr) : IO Unit := c.regAt c.depth xs
end DagCache

/-- the set of depths of the variables a term mentions, memoised by pointer (`hasFVar` prunes closed subterms) -/
unsafe def termMaskUnsafe (sh : DagShared) (e : Expr) : IO Nat := do
  let lv ← sh.lv.get
  let rec go (e : Expr) : IO Nat := do
    if !e.hasFVar then return 0
    match e with
    | .fvar id => return 1 <<< (lv.getD id 0)
    | _ =>
      let p := ptrAddrUnsafe e
      let hit ← do let m ← sh.memo.get; pure m[p]?
      if let some (_, m) := hit then return m
      let m ← match e with
        | .app f a => do pure ((← go f) ||| (← go a))
        | .lam _ t b _ => do pure ((← go t) ||| (← go b))
        | .forallE _ t b _ => do pure ((← go t) ||| (← go b))
        | .letE _ t v b _ => do pure ((← go t) ||| (← go v) ||| (← go b))
        | .mdata _ b => go b
        | .proj _ _ b => go b
        | _ => pure 0
      sh.memo.modify (·.insert p (e, m))
      return m
  go e
@[implemented_by termMaskUnsafe] def termMask (_ : DagShared) (_ : Expr) : IO Nat := pure 0

/-- the mask of a term by a traversal that shares nothing with the walk (check mode) -/
unsafe def trueMaskUnsafe (sh : DagShared) (e : Expr) : IO Nat := do
  let lv ← sh.lv.get
  let seen ← IO.mkRef (∅ : Std.HashSet USize)
  let acc ← IO.mkRef 0
  let rec go (e : Expr) : IO Unit := do
    if !e.hasFVar then return
    match e with
    | .fvar id => acc.modify (· ||| (1 <<< (lv.getD id 0)))
    | _ =>
      let p := ptrAddrUnsafe e
      if (← seen.get).contains p then return
      seen.modify (·.insert p)
      match e with
      | .app f a => do go f; go a
      | .lam _ t b _ => do go t; go b
      | .forallE _ t b _ => do go t; go b
      | .letE _ t v b _ => do go t; go v; go b
      | .mdata _ b => go b
      | .proj _ _ b => go b
      | _ => pure ()
  go e
  acc.get
@[implemented_by trueMaskUnsafe] def trueMask (_ : DagShared) (_ : Expr) : IO Nat := pure 0

/-- the mask of the proof of a scope that is closed by abstracting its binders: the bits of the scopes around it -/
def closeMask (c : DagCache) (m : Nat) : Nat := m &&& ((1 <<< c.depth) - 1)

/-- raw literals (`nat_lit 0` left by the unfolding of a `match`) are not read by `omega`: spell them `OfNat` -/
def normLitsDag (k0 : Expr) : Expr :=
  k0.replace fun e =>
    if e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).isRawNatLit then some e
    else match e with | .lit (.natVal n) => some (mkNatLit n) | _ => none

/-- the leaf `s1.val k = s2.val k` of the agreement hypothesis `h`, the bound by `omega`.  Returns the proof, instantiated (the
only `instantiateMVars` of the walk: on this proof, a few nodes) and its mask (one traversal of those few nodes). -/
def leafDag (cache : DagCache) (h k0 : Expr) : TacticM (Expr × Nat) := do
  let k := normLitsDag k0
  let hk := mkApp h k
  let ty ← whnf (← inferType hk)
  unless ty.isForall do throwError "ved_causal_dag: agreement hypothesis has an unexpected type"
  let goalTy := ty.bindingDomain!
  -- `omega` reads every hypothesis of its context into its proof, so the bound is first tried in the context of the variables of the
  -- depth of the bound itself (a bound of the goal context's variables gives a proof of mask 0, which the cache can share with the
  -- sibling scopes), then in the whole context
  let gm ← termMask cache.sh goalTy
  let l0 := if gm == 0 then 0 else Nat.log2 gm
  let lvm ← cache.sh.lv.get
  let tryAt (l : Nat) : TacticM (Option Expr) := do
    let lctx' := (← getLCtx).foldl (init := (← getLCtx)) fun acc d =>
      if lvm.getD d.fvarId 0 > l then acc.erase d.fvarId else acc
    withLCtx lctx' (← getLocalInstances) do
      let m ← mkFreshExprMVar goalTy
      let rest ← try Tactic.run m.mvarId! (evalTactic (← `(tactic| omega)))
        catch _ => pure [m.mvarId!]
      if rest.isEmpty then return some m else return none
  let found ← do
    let r ← if l0 < cache.depth then tryAt l0 else pure none
    match r with
    | some m => pure (some m)
    | none => tryAt cache.depth
  let some m := found | do
    dbgLogWith do return s!"causal_dag leaf: bound not proved\nleaf goal: {(toString (← withOptions (fun o => o.setBool `pp.explicit true) (ppExpr goalTy))).take 400}\nbounds: {(← (← getLCtx).foldlM (fun acc d => do
          if d.userName.toString.startsWith "ved_h" && !d.userName.toString.startsWith "ved_hab" then pure (acc ++ s!" [{d.userName}: {(toString (← ppExpr d.type)).take 120}]") else pure acc) "")}"
    throwError "ved_causal_dag: bound not proved"
  let pf ← instantiateMVars (mkApp hk m)
  return (pf, ← termMask cache.sh pf)

/-- a proof of `A = B` (see the module comment) and the level mask of the proof -/
partial def dagEq (cache : DagCache) (ag : Array (Expr × Expr × Expr)) (A B : Expr) : TacticM (Expr × Nat) := do
  stEnter
  let p ← dagEqBody cache ag A B
  stLeave
  return p
where
  dagEqBody (cache : DagCache) (ag : Array (Expr × Expr × Expr)) (A B : Expr) : TacticM (Expr × Nat) := do
    let sh := cache.sh
    if A == B then
      stBump "refl"
      return (← mkEqRefl A, ← termMask sh A)
    if let some (e, _) ← cache.findE? (A, B) then
      dgHits.modify fun h =>
        if e.by_ == cache.id then { h with own := h.own + 1 }
        else if cache.hasId e.by_ then { h with ancestor := h.ancestor + 1 }
        else { h with shared := h.shared + 1 }
      if dgGate then
        stBump s!"cache-hit-{if e.by_ == cache.id then "own" else if cache.hasId e.by_ then "ancestor" else "sibling"}@{cache.depth}"
      return (e.proof, e.mask)
    if dgGate then
      stBump s!"cache-miss@{cache.depth}"
      let sn ← dgStats.get
      if sn.seen.contains (A, B) then stBump "cache-miss-pair-seen-before"
      else dgStats.modify fun s => { s with seen := s.seen.insert (A, B) }
    checkSystem "ved_causal_dag"
    let (p, m0) ← dagEqCore cache ag A B
    -- the proof is built on `A` and `B` (type, `Eq.refl`, congruence motives): their variables count
    let m := m0 ||| (← termMask sh A) ||| (← termMask sh B)
    if (← getOptions).getBool `ved.mem.causalDagMaskCheck false then
      let tm ← trueMask sh (← instantiateMVars p)
      unless (tm ||| m) == m do
        throwError "ved_causal_dag: level mask check failed: composed {m}, traversal {tm}"
    cache.store (A, B) p m
    return (p, m)
  /-- `s.1 k` (the projection spelling of `Signal.val s k`) as `Signal.val s k` -/
  normVal (e : Expr) : MetaM Expr := do
    match e.consumeMData with
    | .app (.proj ``Sparkle.Core.Signal.Signal 0 X) k => mkAppM ``Sparkle.Core.Signal.Signal.val #[X, k]
    | e => pure e
  /-- `(Signal.loop F).val k = (Signal.loop G).val k` by `Tools.VedMemNest.loop_val_congr_le F G k` at `k`: its two premises are the
  walk itself, in a child cache scope, with the pair of fresh state signals `a`/`b` (agreement `hab` up to the cycle) added to the
  agreements: `h0`, `(F a).val 0 = (G b).val 0`, under `a b`; `hS`, `(F a).val (t'+1) = (G b).val (t'+1)`, under `t' (t' < k) a b hab`.
  The bounds of the leaves are proved by `omega` from `t' < k` and the facts of the context. -/
  loopDag (cache : DagCache) (ag : Array (Expr × Expr × Expr)) (A B : Expr) : TacticM (Expr × Nat) := do
    let L := A.getArg! 2
    let L' := B.getArg! 2
    let k := normLitsDag (A.getArg! 3)
    unless k == normLitsDag (B.getArg! 3) do throwError "ved_causal_dag: different cycles"
    unless (L.getArg! 0) == (L'.getArg! 0) && (L.getArg! 1) == (L'.getArg! 1) do throwError "ved_causal_dag: loop"
    let F := L.getArg! 3
    let G := L'.getArg! 3
    let dom := L.getArg! 0
    let α := L.getArg! 1
    let sigTy := (← whnf (← inferType F)).bindingDomain!
    let sideVal (F a n : Expr) : MetaM Expr :=
      mkAppM ``Sparkle.Core.Signal.Signal.val #[(mkApp F a).headBeta, n]
    let habTy (a b tt : Expr) : MetaM Expr :=
      withLocalDeclD `ved_k (mkConst ``Nat) fun j => do
        mkForallFVars #[j] (← mkArrow (← mkAppM ``LE.le #[j, tt])
          (← mkEq (← mkAppM ``Sparkle.Core.Signal.Signal.val #[a, j]) (← mkAppM ``Sparkle.Core.Signal.Signal.val #[b, j])))
    let (h0, m0) ← do
      let cache ← cache.scope
      withLocalDeclD `ved_a sigTy fun a => withLocalDeclD `ved_b sigTy fun b => do
        cache.reg #[a, b]
        let (p, m) ← dagEq cache ag (← sideVal F a (mkNatLit 0)) (← sideVal G b (mkNatLit 0))
        return (← mkLambdaFVars #[a, b] p, closeMask cache m)
    let (hS, m1) ← do
      let cache ← cache.scope
      withLocalDeclD `ved_t (mkConst ``Nat) fun t' => do
        let ltTy ← mkAppM ``LT.lt #[t', k]
        withLocalDeclD `ved_ht ltTy fun ht => do
          withLocalDeclD `ved_a sigTy fun a => withLocalDeclD `ved_b sigTy fun b => do
            let hab ← habTy a b t'
            withLocalDeclD `ved_hab hab fun hb => do
              cache.reg #[t', ht, a, b, hb]
              let t1 ← mkAppM ``HAdd.hAdd #[t', mkNatLit 1]
              let (p, m) ← dagEq cache (ag.push (a, b, hb)) (← sideVal F a t1) (← sideVal G b t1)
              return (← mkLambdaFVars #[t', ht, a, b, hb] p, closeMask cache m)
    let pf ← mkAppOptM ``Tools.VedMemNest.loop_val_congr_le
      #[dom, α, L.getArg! 2, F, G, k, h0, hS, k, ← mkAppM ``Nat.le_refl #[k]]
    return (← mkExpectedTypeHint pf (← mkEq A B), m0 ||| m1)
  /-- `A = B` by `Nat.casesOn` on the variable `j`: the hypotheses that depend on `j` are reverted into the motive, and in each case
  (`0`, `u+1`) the walk goes on in a child cache scope, with the agreements that mention them re-pointed at the new hypotheses. -/
  splitDag (cache : DagCache) (ag : Array (Expr × Expr × Expr)) (A B j : Expr) : TacticM (Expr × Nat) := do
    let ds := (← collectForwardDeps #[j] false).filter (· != j)
    dbgLogWith do return s!"causal_dag: split on {(toString (← ppExpr j))} deps={ds.size} A=[{(toString (← ppExpr A)).take 300}]"
    let motive ← mkLambdaFVars #[j] (← mkForallFVars ds (← mkEq A B))
    let branch (v : Expr) : TacticM (Expr × Nat) := do
      let cache ← cache.scope
      stSplit 1
      let r ← forallTelescope (motive.beta #[v]) fun ds' body => do
        cache.reg ds'
        let some (_, A', B') := body.eq? | throwError "ved_causal_dag: no rule for this pair of subterms"
        let ag' := ag.map fun (x, y, h) => (x, y, h.replaceFVars ds ds')
        let (p, m) ← dagEq cache ag' A' B'
        return (← mkLambdaFVars ds' p, m)
      stSplit (-1)
      return r
    let (z, mz) ← branch (mkNatLit 0)
    let (sc, ms) ← withLocalDeclD `ved_u (mkConst ``Nat) fun u => do
      cache.regAt (cache.depth + 1) #[u]  -- the depth of the branch scope, which `branch` creates next
      let (p, m) ← branch (← mkAppM ``HAdd.hAdd #[u, mkNatLit 1])
      return (← mkLambdaFVars #[u] p, m)
    let mut mj ← termMask cache.sh j
    for d in ds do mj := mj ||| (← termMask cache.sh d)
    -- the case proofs are closed over their binders (`ds'`, `u`: the bit of the branch scope, `cache.depth + 1`)
    let keep := (1 <<< (cache.depth + 1)) - 1
    return (mkAppN (← mkAppOptM ``Nat.casesOn #[motive, j, z, sc]) ds, mj ||| (mz &&& keep) ||| (ms &&& keep))
  dagEqCore (cache : DagCache) (ag : Array (Expr × Expr × Expr)) (A0 B0 : Expr) : TacticM (Expr × Nat) := do
    let A ← normVal (← whnfCore A0)
    let B ← normVal (← whnfCore B0)
    if A != A0 || B != B0 then
      stBump "whnfCore-step"
      if dgGate then stSize "whnfCore-result" A
      let (p, m) ← dagEq cache ag A B
      return (← mkExpectedTypeHint p (← mkEq A0 B0), m)
    -- `Signal.val F k x`: the value of a signal of functions (`<*>`) applied to an argument
    if A.isAppOf ``Sparkle.Core.Signal.Signal.val && A.getAppNumArgs > 4 && B.isAppOf ``Sparkle.Core.Signal.Signal.val
        && B.getAppNumArgs == A.getAppNumArgs then
      let a := A.getAppArgs
      let b := B.getAppArgs
      stBump "val-applied"
      let (p0, m0) ← dagEq cache ag (mkAppN A.getAppFn (a.extract 0 4)) (mkAppN B.getAppFn (b.extract 0 4))
      let mut pf := p0
      let mut m := m0
      for i in [4:a.size] do
        if a[i]! != b[i]! then
          let (q, mq) ← dagEq cache ag a[i]! b[i]!
          pf ← mkCongr pf q
          m := m ||| mq
        else pf ← mkCongrFun pf a[i]!
      return (pf, m)
    if A.isAppOfArity ``Sparkle.Core.Signal.Signal.val 4 && B.isAppOfArity ``Sparkle.Core.Signal.Signal.val 4 then
      let X := A.getArg! 2
      let Y := B.getArg! 2
      let k := A.getArg! 3
      unless k == B.getArg! 3 do throwError "ved_causal_dag: different cycles"
      -- a signal left as a redex (`(fun x => a) ()`) is the state variable `a` itself: the leaf is found after the head step
      let X' ← whnfCore X
      let Y' ← whnfCore Y
      if X' != X || Y' != Y then
        stBump "val-signal-whnfCore"
        let A' := mkAppN A.getAppFn (A.getAppArgs.set! 2 X')
        let B' := mkAppN B.getAppFn (B.getAppArgs.set! 2 Y')
        let (p, m) ← dagEq cache ag A' B'
        return (← mkExpectedTypeHint p (← mkEq A B), m)
      for (s1, s2, h) in ag do
        if X == s1 && Y == s2 then
          stBump "leaf"
          let (p, m) ← leafDag cache h k
          return (← mkExpectedTypeHint p (← mkEq A B), m)
      if X.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 && Y.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then
        stBump "loopDag"
        return ← loopDag cache ag A B
      if X.isAppOf ``Sparkle.Core.Signal.Signal.loop || Y.isAppOf ``Sparkle.Core.Signal.Signal.loop then
        throwError "ved_causal_dag: loop"
      stBump "unfoldValDag"
      let eA ← unfoldValDag cache.sh.whnfMemo A
      let eB ← unfoldValDag cache.sh.whnfMemo B
      let (p, m) ← dagEq cache ag eA eB
      let l ← mkExpectedTypeHint (← mkEqRefl A) (← mkEq A eA)
      let r ← mkExpectedTypeHint (← mkEqRefl eB) (← mkEq eB B)
      return (← mkEqTrans (← mkEqTrans l p) r, m)
    if A.isAppOf ``Sparkle.Core.Signal.Signal.memState && A.getAppNumArgs ≥ 8 && B.isAppOf ``Sparkle.Core.Signal.Signal.memState
        && B.getAppNumArgs == A.getAppNumArgs then
      let a := A.getAppArgs
      let b := B.getAppArgs
      if ([0, 1, 2, 3, 7].all fun i => a[i]! == b[i]!) then
        stBump "memState"
        let t := a[7]!
        let side (x y : Expr) : TacticM (Expr × Nat) := do
          let cache ← cache.scope
          withLocalDeclD `ved_j (mkConst ``Nat) fun j => do
            withLocalDeclD `ved_hj (← mkAppM ``LT.lt #[j, normLitsDag t]) fun hj => do
              cache.reg #[j, hj]
              let ValX ← mkAppM ``Sparkle.Core.Signal.Signal.val #[x, j]
              let ValY ← mkAppM ``Sparkle.Core.Signal.Signal.val #[y, j]
              let (p, m) ← dagEq cache ag ValX ValY
              return (← mkLambdaFVars #[j, hj] p, closeMask cache m)
        let (ha, ma) ← side a[4]! b[4]!
        let (hd, md) ← side a[5]! b[5]!
        let (he, me) ← side a[6]! b[6]!
        let hc ← mkAppOptM ``Tools.VedMem.memState_congr
          #[a[0]!, a[1]!, a[2]!, a[3]!, a[4]!, b[4]!, a[5]!, b[5]!, a[6]!, b[6]!, t, ha, hd, he]
        let mut pf := hc
        let mut m := ma ||| md ||| me
        for i in [8:a.size] do
          if a[i]! != b[i]! then
            let (q, mq) ← dagEq cache ag a[i]! b[i]!
            pf ← mkCongr pf q
            m := m ||| mq
          else pf ← mkCongrFun pf a[i]!
        return (pf, m)
    -- a `match` on a variable time (a memory or register read at the variable inner time of a loop, or at the variable of a
    -- `memState` side condition) does not reduce: the cases `0` / `u+1` of that variable
    for E in [A, B] do
      if let some m ← matchMatcherApp? E then
        if let some j ← m.discrs.findM? fun d => do
            pure (d.isFVar && (← inferType d).isConstOf ``Nat) then
          stBump "casesOn-split"
          return ← splitDag cache ag A B j
    if A.isApp && B.isApp then
      let f := A.getAppFn
      let a := A.getAppArgs
      let b := B.getAppArgs
      if f == B.getAppFn && a.size == b.size then
        if f.isConstOf ``ite && a.size == 5 then
          stBump "ite"
          let (pc, mc) ← dagEq cache ag a[1]! b[1]!
          let (pt, mt) ← dagEq cache ag a[3]! b[3]!
          let (pe, me) ← dagEq cache ag a[4]! b[4]!
          return (← mkAppOptM ``ved_ite_congr #[a[0]!, a[1]!, b[1]!, a[2]!, b[2]!, a[3]!, b[3]!, a[4]!, b[4]!, pc, pt, pe], mc ||| mt ||| me)
        stBump (if dgGate then s!"congr-app {f.constName?.getD `other}" else "")
        let mut ps : Array (Nat × Expr) := #[]
        let mut m := 0
        for i in [0:a.size] do
          if a[i]! != b[i]! then
            let (q, mq) ← try dagEq cache ag a[i]! b[i]!
              catch e =>
                dbgLogWith do
                  let extra ← if f.isConstOf ``Sparkle.Core.Signal.Signal.val then
                      do let xs ← a.mapM fun x => do pure ((toString (← ppExpr x)).take 50).toString
                         pure s!" args={xs}"
                    else pure ""
                  return s!"causal_dag: in arg {i}/{a.size} of {(toString (← ppExpr f)).take 80}{extra}"
                throw e
            ps := ps.push (i, q)
            m := m ||| mq
        return (← congrArgsDag f a b ps, m)
    if let (.proj n i x, .proj n' i' y) := (A, B) then
      if n == n' && i == i' then
        stBump "proj"
        let (p, m) ← dagEq cache ag x y
        let motive ← withLocalDeclD `ved_y (← inferType x) fun v => mkLambdaFVars #[v] (.proj n i v)
        return (← mkCongrArg motive p, m)
    if let (.lam n ty bA bi, .lam _ ty' bB _) := (A, B) then
      if ty == ty' then
        stBump "funext"
        let cache ← cache.scope
        let (p, m) ← withLocalDecl n bi ty fun x => do
          cache.reg #[x]
          let (p, m) ← dagEq cache ag (bA.instantiate1 x) (bB.instantiate1 x)
          return (← mkLambdaFVars #[x] p, closeMask cache m)
        return (← mkFunExt p, m)
    stBump "no-rule"
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
  stReset
  dgHits.set {}
  tryCatchRuntimeEx (do
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
      let (p, _) ← dagEq cache #[(s1.toExpr, s2.toExpr, h.toExpr)] A B
      (← getMainGoal).assign p
      dgWalk.set ((← IO.monoMsNow) - t0, ((← IO.getNumHeartbeats) - hb0) / 1000)
      dbgLogWith do return s!"TLOG causal_dag goal closed t={← IO.monoMsNow} hb={((← IO.getNumHeartbeats) - hb0) / 1000} cache={(← cache.own.get).size} {← hitsRender} {← stRender}"
   ) fun e => do
    if e.isRuntime then
      dbgLogWith do return s!"TLOG causal_dag RUNTIME EXCEPTION (heartbeats/recursion) t={← IO.monoMsNow} hb={((← IO.getNumHeartbeats) - hb0) / 1000}: {← hitsRender} {← stRender}"
    else
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
    -- distinct loops of the targets / of the hypotheses of the first goal (the option `ved.mem.hstepNorm` keeps both sides the same terms)
    let isLp := fun (x : Expr) => x.isAppOfArity ``Signal.loop 4
    let mut lt : Array Expr := #[]
    for g in gs do
      for l in Tools.VedU1WireShare.collectDag isLp (← instantiateMVars (← g.getType)) do
        unless lt.contains l do lt := lt.push l
    let lh : Array Expr ← match gs.head? with
      | none => pure #[]
      | some g => g.withContext do
        let mut r : Array Expr := #[]
        for d in ← getLCtx do
          unless d.isImplementationDetail do
            for l in Tools.VedU1WireShare.collectDag isLp (← instantiateMVars d.type) do
              unless r.contains l do r := r.push l
        pure r
    let both := (lt.filter fun l => lh.contains l).size
    dbgLog s!"STAMP {k.getNat} t={← IO.monoMsNow} hb={(← IO.getNumHeartbeats) / 1000} goals={gs.length} tree: total={szs.foldl (· + ·) 0} max={szs.foldl max 0} big(>100k)={(szs.filter (· > 100000)).size} loops: tgt={lt.size} hyp1={lh.size} shared={both}"
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
    `(tactic| first | (ved_causal_budget (ved_causal_dag)) | (ved_causal_simp [$ex,*]))

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
`ved_causal_budget`, i.e. the local cap `ved.mem.causalDagBudget`, as in `ved_causal`) runs FIRST and is never refused by the gate; only when the walk fails (tactic state restored) the
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
    if (← getOptions).getBool `ved.mem.causalDag false then
      let st ← saveState
      let walked ← try runSubMem hSc (← `(tactic| ved_causal_budget (ved_causal_dag))); pure true
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


/-! ## `ved.mem.hstepDag`: the two whole-term simps of the step case, as rewrites of the occurrences they need

The step case of the memory loop (`memLoopScript`, `Tools/VedMemEntry.lean`) starts with two `simp`s over the whole goal / the whole
hypotheses, whose terms hold the declaration's loops (tree 6.2e10 nodes on R033, a DAG of a few thousand): `simp only [O, List.mem_singleton,
forall_eq, key]` (packed rows; observed 428 s, ONE conjunct changes) and `ved_loop_simp [..] at hreg* hM* hL* hD*` (every hypothesis re-simplifies
the same loops: `Simp.main` has a cache per location).  With the option ON the new tactics are the first alternative, the old ones the
fallback (`first`, the state is restored): `ved_obtain_dag` takes `hR` apart by projections, `ved_hnorm_dag` simplifies each distinct
loop of the hypotheses ONCE and puts the result in by `Expr.replace` + `congrArg`.  Untrusted: the kernel checks the proofs. -/

register_option ved.mem.hstepDag : Bool := {
  defValue := false
  descr := "step case of the memory loop: rewrite only the needed occurrences (`ved_obtain_dag`, `ved_hnorm_dag`) instead of the whole-term simps; the old tactics stay the fallback"
}

/-- `ved_hstep_dag_on`: fails (fixed text) unless the option `ved.mem.hstepDag` is on -/
elab "ved_hstep_dag_on" : tactic => do
  unless (← getOptions).getBool `ved.mem.hstepDag false do throwError "ved_hstep_dag: option ved.mem.hstepDag is off"

/-- test seam (never set by production code): when set `ved_obtain_dag` / `ved_hnorm_dag` refuse, the old tactic is the fallback -/
initialize hstepRefuse : IO.Ref Bool ← IO.mkRef false

/-- test log (never read by production code): the names of the new tactics that ran -/
initialize hstepRan : IO.Ref (Array String) ← IO.mkRef #[]

def obtainDagCore (h : TSyntax `ident) (ids : Array (TSyntax `ident)) : TacticM Unit := withMainContext do
  if (← hstepRefuse.get) then throwError "ved_obtain_dag: refused (test seam)"
  let t0 ← IO.monoMsNow
  let some d := (← getLCtx).findFromUserName? h.getId | throwError "ved_obtain_dag: no hypothesis {h.getId}"
  if ids.size < 2 then throwError "ved_obtain_dag: fewer than two components"
  let mut g ← getMainGoal
  let mut cur : Expr := mkFVar d.fvarId
  let mut ty := (← instantiateMVars d.type).consumeMData
  for i in [0:ids.size] do
    if i + 1 == ids.size then
      let (_, g1) ← (← g.assert ids[i]!.getId ty cur).intro1P
      g := g1
    else
      unless ty.isAppOfArity ``And 2 do throwError "ved_obtain_dag: component {i} is not a conjunction"
      let a := ty.getArg! 0
      let b := (ty.getArg! 1).consumeMData
      let (_, g1) ← (← g.assert ids[i]!.getId a (mkApp3 (mkConst ``And.left) a b cur)).intro1P
      g := g1
      cur := mkApp3 (mkConst ``And.right) a b cur
      ty := b
  g ← g.clear d.fvarId
  replaceMainGoal [g]
  hstepRan.modify (·.push "obtain_dag")
  dbgLog s!"obtain_dag: {ids.size} components ms={(← IO.monoMsNow) - t0}"

/-- `ved_obtain_dag hR [h₀, .., hₖ]`: `obtain ⟨h₀, .., hₖ⟩ := hR` for a right-nested conjunction by projections (`And.left` / `And.right` of the
hypothesis, one `have` each, then `hR` cleared).  The `cases` of `rcases` abstracts the goal at each of the components (observed on R033: 426 s for
the 28 components, the goal a DAG of a few thousand nodes with tree 6e10); the projections never read the goal. -/
elab "ved_obtain_dag " h:ident " [" ids:ident,* "]" : tactic => do
  try obtainDagCore h ids.getElems
  catch e =>
    dbgLog s!"obtain_dag: refused: {← e.toMessageData.toString}"
    throw e

/-- the outermost `Signal.loop`s of `e` (closed ones; a loop inside a loop is not listed), each once -/
partial def outerLoops (e : Expr) : Array Expr := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut out : Array Expr := #[]
  let mut todo : Array Expr := #[e]
  while !todo.isEmpty do
    let x := todo.back!
    todo := todo.pop
    if seen.contains x then continue
    seen := seen.insert x
    if x.isAppOfArity ``Signal.loop 4 && !x.hasLooseBVars then
      unless out.contains x do out := out.push x
      continue
    match x with
    | .app f a => todo := (todo.push a).push f
    | .lam _ t b _ => todo := (todo.push b).push t
    | .forallE _ t b _ => todo := (todo.push b).push t
    | .letE _ t v b _ => todo := ((todo.push b).push v).push t
    | .mdata _ b => todo := todo.push b
    | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return out

/-- `ved_hnorm_dag [lemmas] at h₁ .. hₖ`: `ved_loop_simp [lemmas] at h₁ .. hₖ` where each distinct loop of the hypotheses is simplified once.
(1) every outermost loop `L` of the hypotheses is simplified alone (`L = L'`); (2) `L` is replaced in the hypotheses by a `let` variable
`x := L` (definitional), so that (3) the old `ved_loop_simp ... at ..` sees an atom; (4) `x` is replaced by `L'` (`congrArg` over the replaced
occurrences, one `Expr.replace` per hypothesis); (5) the `let` variables are cleared. -/
def hnormDagCore (ls : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma ",") (hs : Array (TSyntax `ident)) : TacticM Unit := withMainContext do
  if (← hstepRefuse.get) then throwError "ved_hnorm_dag: refused (test seam)"
  let t0 ← IO.monoMsNow
  let stx0 ← `(tactic| ved_loop_simp [$ls,*])
  let some (_, .ok stx1) ← liftMacroM (Lean.Elab.expandMacroImpl? (← getEnv) stx0) | throwError "ved_hnorm_dag: ved_loop_simp does not expand"
  let sc ← Lean.Elab.Tactic.mkSimpContext stx1 (eraseLocal := false)
  let fvs ← hs.mapM fun h => do
    let some d := (← getLCtx).findFromUserName? h.getId | throwError "ved_hnorm_dag: no hypothesis {h.getId}"
    pure d.fvarId
  let mut loops : Array Expr := #[]
  for fv in fvs do
    for l in outerLoops (← instantiateMVars (← fv.getType)) do
      unless loops.contains l do loops := loops.push l
  dbgLog s!"hnorm_dag: {fvs.size} hypotheses, {loops.size} outermost loops"
  -- (1) each loop once
  let mut res : Array (Expr × Option Expr) := #[]
  for l in loops do
    let t1 ← IO.monoMsNow
    let (r, _) ← sc.dischargeWrapper.with fun d? => Meta.simp l sc.ctx sc.simprocs d?
    dbgLog s!"hnorm_dag: loop simp ms={(← IO.monoMsNow) - t1} changed={r.expr != l}"
    let pf? ← if r.expr == l then pure none else do pure (some (← r.getProof))
    res := res.push (r.expr, pf?)
  -- (2) the let variables
  let find (g : MVarId) (h : TSyntax `ident) : MetaM (Option FVarId) := g.withContext do
    return (← getLCtx).findFromUserName? h.getId |>.map (·.fvarId)
  let mut g ← getMainGoal
  let mut xs : Array Expr := #[]
  for j in [0:loops.size] do
    let ty ← g.withContext (inferType loops[j]!)
    let g1 ← g.define (Name.mkSimple s!"ved_hx{j}") ty loops[j]!
    let (xv, g2) ← g1.intro1P
    xs := xs.push (mkFVar xv)
    g := g2
  for h in hs do
    let some hf ← find g h | continue
    let r? ← g.withContext do
      let ty ← instantiateMVars (← hf.getType)
      let ty' := ty.replace fun e =>
        if e.isAppOfArity ``Signal.loop 4 then
          match loops.findIdx? (· == e) with
          | some j => some xs[j]!
          | none => none
        else none
      if ty' == ty then return none
      return some (ty', ← mkExpectedTypeHint (← mkEqRefl ty) (← mkEq ty ty'))
    if let some (ty', pf) := r? then
      let (r : AssertAfterResult) ← g.replaceLocalDecl hf ty' pf
      g := r.mvarId
  replaceMainGoal [g]
  dbgLog s!"hnorm_dag: atoms ms={(← IO.monoMsNow) - t0}"
  -- (3) the old step on the atomised hypotheses
  evalTactic (← `(tactic| ved_loop_simp [$ls,*] at $hs*))
  dbgLog s!"hnorm_dag: simp ms={(← IO.monoMsNow) - t0}"
  -- (4) the atoms become the simplified loops
  let mut g4 ← getMainGoal
  let xfv : Array FVarId := xs.map (·.fvarId!)
  for h in hs do
    let some hf ← find g4 h | continue
    let r? ← g4.withContext do
      let ty ← instantiateMVars (← hf.getType)
      if !(xfv.any fun x => ty.containsFVar x) then return none
      let mut cur := ty
      let mut pf? : Option Expr := none
      for j in [0:loops.size] do
        let some pj := res[j]!.2 | continue
        unless cur.containsFVar xfv[j]! do continue
        let xj := xs[j]!
        let motive ← withLocalDeclD `ved_y (← inferType xj) fun y =>
          mkLambdaFVars #[y] (cur.replace fun e => if e == xj then some y else none)
        let new := cur.replace fun e => if e == xj then some res[j]!.1 else none
        let step ← mkCongrArg motive pj
        pf? := some (← match pf? with | none => pure step | some p => mkEqTrans p step)
        cur := new
      -- the atoms without a change: back to the loop itself
      let cur' := cur.replace fun e =>
        match xs.findIdx? (· == e) with
        | some j => some loops[j]!
        | none => none
      let pf ← match pf? with
        | some p => pure p
        | none => mkExpectedTypeHint (← mkEqRefl ty) (← mkEq ty cur')
      return some (cur', pf)
    if let some (ty', pf) := r? then
      let (r : AssertAfterResult) ← g4.replaceLocalDecl hf ty' pf
      g4 := r.mvarId
  -- (5) the let variables
  g4 ← g4.tryClearMany xfv
  replaceMainGoal [g4]
  hstepRan.modify (·.push "hnorm_dag")
  dbgLog s!"hnorm_dag: done ms={(← IO.monoMsNow) - t0}"

elab "ved_hnorm_dag " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" " at " hs:ident+ : tactic => do
  try hnormDagCore ls hs
  catch e =>
    dbgLog s!"hnorm_dag: refused: {← e.toMessageData.toString}"
    throw e

/-! ## `ved.mem.hstepNorm`: the loops are not normalised; the goal's loop is replaced by the hypotheses' loop

Observed (first unit, R033): one `Meta.simp` of one loop of the invariant takes 104 s (loop 2 does not finish in 314 s), and stage 94 repeats the
same simp on the goal's loops.  What fires inside a loop body (`set_option trace.Meta.Tactic.simp.rewrite true` on a small design) is the
unfolding of the signal combinators (`Signal.map/seq/ap/mux/beq/register/fst/snd`, `bundle2`, `PTy.sig`, the state-field projections) and a few
rewrites of the value layer (`pure_val`, `add_val`, `ne_eq`, `ite_not`, ..); the body grows (tree 4611 -> 7745 on the smallest design).  The loops of
the hypotheses (`R`, built from `declBody`: lets inlined, the input names literal) and the loop that the goal's `srcOf C f ins ..` unfolds to (the
declaration with its lets and `applyIns` name lookups) are two spellings of the same loop; the old script puts both into the simp normal form.  With the
option on, simp does not enter a `Signal.loop` (`↓ vedMemLoopFreeze`, `.done`: no proof, no rewrite inside the loop), and after the goal's simp
(stage 94) `ved_hstep_unify` replaces a loop of the goal that is definitionally (default transparency, a local heartbeat budget per test) the loop of a
hypothesis by that loop (one `Expr.replace` over the DAG, one `replaceTargetDefEq`; the kernel compares the two targets, which differ only at those
loops).  The loops of the goal and of the hypotheses are then the same terms, without a rewrite inside a loop.  Why a separate step and not the
simproc: simp runs at reducible transparency and keeps the type argument of `Signal.val dom α L s`; the entry spells the state type `QState`, the
declaration the product, which only default transparency identifies. -/

register_option ved.mem.hstepNorm : Bool := {
  defValue := false
  descr := "step case of the memory loop: the simps after the invariant do not normalise `Signal.loop` bodies, the goal's loops are made the hypotheses' loops by definitional equality; the old script is the fallback"
}

/-- local heartbeat budget (thousands) of one `isDefEq` of `vedMemLoopFreeze` -/
register_option ved.mem.hstepNormBudget : Nat := {
  defValue := 2000
  descr := "local heartbeat budget (thousands) of one definitional-equality test of a goal loop against a hypothesis loop (`ved.mem.hstepNorm`)"
}

/-- test/diagnosis counter: answered from the table (`declWidth M "lit"`) -/
initialize declWidthHits : IO.Ref Nat ← IO.mkRef 0

/-- the new branch of the step case has started (set by `ved_hstep_norm_on`; read and reset by `ved_hstep_fallback_reset`, `Tools/VedMemPack.lean`).
Global, like the caches it guards; one script runs at a time. -/
initialize hstepAttempted : IO.Ref Bool ← IO.mkRef false

/-- `ved_hstep_norm_on`: fails (fixed text) unless the option `ved.mem.hstepNorm` is on, or when the test seam `hstepRefuse` is set -/
elab "ved_hstep_norm_on" : tactic => do
  unless (← getOptions).getBool `ved.mem.hstepNorm false do throwError "ved_hstep_norm: option ved.mem.hstepNorm is off"
  if (← hstepRefuse.get) then throwError "ved_hstep_norm: refused (test seam)"
  hstepAttempted.set true

/-- test seam: the new branch fails at its very end (after the tail stages, whose auxiliary proofs it has created) -/
initialize hstepFailLate : IO.Ref Bool ← IO.mkRef false

/-- test log: the new branch ran to its end -/
elab "ved_hstep_norm_ran" : tactic => do
  if (← hstepFailLate.get) then throwError "ved_hstep_norm: failed late (test seam)"
  hstepRan.modify (·.push "norm_skip")

/-- the loops of the hypotheses (types), the targets of `vedMemLoopFreeze` -/
initialize hnormLoops : IO.Ref (Array Expr) ← IO.mkRef #[]

/-- (loops replaced by a hypothesis' loop, loops left alone) of the last `ved_hstep_unify`, test log -/
initialize hnormStats : IO.Ref (Nat × Nat) ← IO.mkRef (0, 0)

/-- `ved_hstep_loops`: remember the outermost loops of the hypotheses of the main goal -/
elab "ved_hstep_loops" : tactic => withMainContext do
  let mut ls : Array Expr := #[]
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      for l in outerLoops (← instantiateMVars d.type) do
        unless ls.contains l do ls := ls.push l
  hnormLoops.set ls
  hnormStats.set (0, 0)
  dbgLog s!"hstep_loops: {ls.size} loops of the hypotheses"

/-- `ved_hstep_loops_clear`: forget them -/
elab "ved_hstep_loops_clear" : tactic => do
  dbgLog s!"hstep_loops_clear: converted/left {← hnormStats.get} declWidth answered {← declWidthHits.get}"
  hnormLoops.set #[]

open Lean Meta Simp in
/-- `simp [↓vedMemLoopFreeze, ..]` does not look into a `Signal.loop` (the goal's loops are made the hypotheses' loops afterwards, `ved_hstep_unify`; same simproc as `vedLoopFreeze` of `Tools/VedU1ScriptSeqGen.lean`).
Sound: no rewriting inside the loop. -/
simproc_decl vedMemLoopFreeze (Sparkle.Core.Signal.Signal.loop _) := fun e => do
  return .done { expr := e }

/-! ### `declWidth M "wire"` is looked up from a table, not by unfolding `List.find?`

Observed (R033 diagnosis run, stage 94, loops frozen; the goal's DAG is 3636 nodes): the simp does not stop at the goal's size; it unfolds
`declWidth M x = (M.wires.find? (fun p => p.name == x))` for every width query of the module semantics, a walk over the whole wire list per query:
visits (pre-simproc calls) grow linearly at 5.4e3 per second (2.0e6 visits at 370 s, still counting), 95% of them `Eq`, `BEq.beq`, `Port.name`,
`Not`, `List.find?`, `<mvar>` (the `find?` unrolling), against ~1e4 visits for the whole stage on the small examples.
`Entry` puts the table `wire name ↦ declWidth M name` of the module into `declWidthTab` (only with `ved.mem.hstepNorm` on); the pre-simproc
`vedDeclWidth` answers `declWidth M "lit"` from it (`.done`, definitional: the kernel checks the step by evaluating the lookup once), and
`vedDeclWidth1` keeps the partial application `declWidth M` (the `we` of `evalAssigns`) from being unfolded into the `find?` lambda. -/

/-- (module constant, its table), set by `checkMemE` around the proof elaboration when `ved.mem.hstepNorm` is on -/
initialize declWidthTab : IO.Ref (Option (Name × Std.HashMap String Nat)) ← IO.mkRef none

open Lean Meta Simp in
def declWidthAnswer (e : Expr) : SimpM Step := do
  let some (mn, tab) ← declWidthTab.get | return .continue
  unless e.isAppOfArity ``Tools.VedU1Contract.declWidth 2 do return .continue
  let args := e.getAppArgs
  unless args[0]!.isConstOf mn do return .continue
  let .lit (.strVal s) := args[1]! | return .continue
  declWidthHits.modify (· + 1)
  return .done { expr := mkNatLit (tab.getD s 0) }

open Lean Meta Simp in
simproc_decl vedDeclWidth (Tools.VedU1Contract.declWidth _ _) := declWidthAnswer

open Lean Meta Simp in
simproc_decl vedDeclWidth1 (Tools.VedU1Contract.declWidth _) := fun e => do
  let some (mn, _) ← declWidthTab.get | return .continue
  if e.isAppOfArity ``Tools.VedU1Contract.declWidth 1 && e.appArg!.isConstOf mn then return .done { expr := e }
  return .continue

/-! ### `Option.bind m f` is evaluated in order: `m` first, the continuation `f` only after `m` is `some x`

Observed (small examples, per-conjunct diagnosis of stage 94, `VED_S94_SAMPLE` samples of the visited `ite`/`Eq`): the conjunct `stepModule .. = some ..`
takes ALL the time of stage 94 (small: 2255 ms of 2946; others <= 41 ms), and the terms it visits contain the pending variables of the module
semantics (`v✝`, `env'`, `if n = "w" then v✝ else env' n`): simp's congruence for `Option.bind m (fun v => rest)` (the `do` blocks of `evalAssigns`,
`evalExpr`, `regNexts`, `memNexts`) visits the continuation `rest` UNDER the binder, i.e. evaluates the whole remaining module with an opaque `v`, and only
after `Option.bind_some` substitutes the value and simplifies the (rebuilt) continuation again: every statement re-simplifies everything after it
(quadratic, the substituted continuations are new terms: the memory growth).  `vedBindStrict*` (pre-simprocs, new branch only) simplify `m` first
and, when it is `some x`, continue with `f x` (beta): the continuation is never visited with an opaque `v`.  The step is definitional up to the
simplification of `m` (`congrArg` over `m`, then `Option.bind (some x) f ≡ f x`). -/

/-- number of `Option.bind` steps taken by `vedBindStrict*` (test counter) -/
initialize bindStrictHits : IO.Ref Nat ← IO.mkRef 0
/-- diagnosis timers of `bindStrictStep` (ms): nested `Simp.simp m`, proof construction -/
initialize bindStrictMs : IO.Ref (Nat × Nat) ← IO.mkRef (0, 0)

open Lean Meta Simp in
def bindStrictStep (e : Expr) : SimpM Step := do
  let (mi, f) ←
    if e.isAppOfArity ``Option.bind 4 then pure (2, e.getArg! 3)
    else if e.isAppOfArity ``Bind.bind 6 && (e.getArg! 0).isConstOf ``Option then pure (4, e.getArg! 5)
    else return .continue
  let m := e.getArg! mi
  if m.isAppOfArity ``Option.some 2 then return .continue
  unless f.isLambda do return .continue
  let t0 ← IO.monoNanosNow
  let r ← Simp.simp m
  let t1 ← IO.monoNanosNow
  bindStrictMs.modify fun (a, b) => (a + (t1 - t0) / 1000, b)
  unless r.expr.isAppOfArity ``Option.some 2 do return .continue
  let new := (mkApp f r.expr.appArg!).headBeta
  match r.proof? with
  | none => return .continue
  | some p =>
    bindStrictHits.modify (· + 1)
    let t2 ← IO.monoNanosNow
    try
      let mT ← inferType m
      let motive := Expr.lam `y mT (mkAppN e.getAppFn (e.getAppArgs.set! mi (.bvar 0))) .default
      let x := r.expr.appArg!
      let mut pf ← mkCongrArg motive p
      if mi == 4 then pf ← mkEqTrans pf (← mkCongrFun (← mkCongrFun (← mkAppOptM ``Option.bind_eq_bind #[some (e.getArg! 2), some (e.getArg! 3)]) r.expr) f)
      pf ← mkEqTrans pf (← mkAppM ``Option.bind_some #[x, f])
      return .visit { expr := new, proof? := some pf }
    finally
      let t3 ← IO.monoNanosNow
      bindStrictMs.modify fun (a, b) => (a, b + (t3 - t2) / 1000)

open Lean Meta Simp in
simproc_decl vedBindStrictO (Option.bind _ _) := bindStrictStep

open Lean Meta Simp in
simproc_decl vedBindStrictB (Bind.bind _ _) := bindStrictStep

/-! ### The environment functions of the module semantics are not entered (`ved.mem.s94EnvFreeze`)

Observed (small examples, `VED_S94_SAMPLE`: the visited `ite` of conjunct `stepModule .. = some ..` are `if n = "w" then v else (fun n => ..) n` UNDER a binder `n`):
`evalAssigns` extends the environment by `fun n => if n = l then v else env n`; simp enters this lambda, beta-reduces `env n` (`env` is the
previous, already flattened, function) and so rewrites the whole chain of the `k` earlier statements again, with a fresh `n`, for EVERY statement:
the `ite` visits of the statement `k` cost `O(k)` each (`Expr.instantiate` of the flat chain), `O(n^2)` visits and `O(n^3)` work in all, and every visit
builds a new copy of the chain (pointer objects 5x the DAG).  `vedEnvFreeze` (pre-simproc, `.done`, no rewrite, no proof) leaves a function of exactly this
shape unchanged: the value `v` is simplified before the function is built (`vedBindStrict*`), `env "lit"` is beta-reduced on demand (the lookup chain is
walked by `reduceIte`, each step a small term).  Sound: no rewriting inside the function. -/

/-- number of environment functions left alone by `vedEnvFreeze` (test counter) -/
initialize envFreezeHits : IO.Ref Nat ← IO.mkRef 0

/-- `fun n : String => if n = "lit" then v else f n` with `v`, `f` not mentioning `n` -/
def isEnvCell (e : Lean.Expr) : Bool :=
  match e with
  | .lam _ ty body _ =>
    ty.isConstOf ``String && body.isAppOfArity ``ite 5 &&
    (let c := body.getArg! 1
     c.isAppOfArity ``Eq 3 && c.getArg! 1 == .bvar 0 && (match c.getArg! 2 with | .lit (.strVal _) => true | _ => false)) &&
    !(body.getArg! 3).hasLooseBVars &&
    (let el := body.getArg! 4
     el.isApp && el.appArg! == .bvar 0 && !el.appFn!.hasLooseBVars)
  | _ => false

open Lean Meta Simp in
simproc_decl vedEnvFreeze (_) := fun e => do
  unless e.isLambda && isEnvCell e do return .continue
  envFreezeHits.modify (· + 1)
  return .done { expr := e }

register_option ved.mem.s94EnvFreeze : Bool := {
  defValue := false
  descr := "the stage-94 simps of the new branch (`ved.mem.hstepNorm`) do not enter the environment functions `fun n => if n = \"w\" then v else env n` (`vedEnvFreeze`)"
}

/-- `ved_hstep_logfail t`: `t`; a failure is logged (`addr.log`, first 600 characters) and rethrown -/
elab "ved_hstep_logfail " t:tactic : tactic => do
  try evalTactic t
  catch e =>
    dbgLogWith (do return s!"hstep new branch failed: {((← e.toMessageData.toString).replace "\n" " ").take 600}")
    throw e

/-- `ved_hstep_unify`: in the target of every goal, a loop that is (definitionally, at default transparency, within the budget
`ved.mem.hstepNormBudget` per test) the loop of a hypothesis (`ved_hstep_loops`) is replaced by that loop, and a read `Signal.val dom α L s` of it
by `Signal.val dom α' l s` (`α'` the type argument of `l`: the entry spells the state `QState`, the declaration the product, and `generalize` matches the
spelling).  One `Expr.replace` over the DAG per goal, one `replaceTargetDefEq` (the kernel compares the two targets, which differ only at those loops). -/
elab "ved_hstep_unify" : tactic => do
  let ls ← hnormLoops.get
  let n := (← getOptions).get `ved.mem.hstepNormBudget (2000 : Nat)
  let mut out : List MVarId := []
  let mut conv := 0
  let mut left := 0
  for g in ← getGoals do
    let tgt ← instantiateMVars (← g.getType)
    let isLoop := fun (x : Expr) => x.isAppOfArity ``Signal.loop 4
    let loops := Tools.VedU1WireShare.collectDag isLoop tgt
    let mut memo : Std.HashMap Expr Expr := {}
    for L in loops do
      if ls.contains L then continue
      let some α := L.getAppArgs[1]? | continue
      let mut found : Option Expr := none
      for l in ls do
        unless l.getAppArgs[1]? == some α || (← g.withContext <| withDefault (isDefEq (l.getAppArgs[1]!) α)) do continue
        let hb ← IO.getNumHeartbeats
        let t0 ← IO.monoMsNow
        let ok ← g.withContext <| try
            withTheReader Core.Context (fun c =>
              let left := c.maxHeartbeats - (hb - c.initHeartbeats)
              { c with maxHeartbeats := if c.maxHeartbeats == 0 then n * 1000 else max 1 (min left (n * 1000)), initHeartbeats := hb }) do
              tryCatchRuntimeEx (withDefault (isDefEq L l)) fun _ => pure false
          catch _ => pure false
        dbgLog s!"hstep_unify: isDefEq {ok} ms={(← IO.monoMsNow) - t0} hb={((← IO.getNumHeartbeats) - hb) / 1000}"
        if ok then found := some l; break
      match found with
      | some l => memo := memo.insert L l; conv := conv + 1
      | none => left := left + 1
    let target' := tgt.replace fun x =>
      if x.isAppOfArity ``Signal.val 4 && isLoop (x.getArg! 2) then
        let L := x.getArg! 2
        if let some l := (if ls.contains L then some L else memo[L]?) then
          let xs := x.getAppArgs
          let new := mkAppN x.getAppFn #[xs[0]!, l.getArg! 1, l, xs[3]!]
          if new == x then none else some new
        else none
      else if isLoop x then
        match memo[x]? with
        | some l => some l
        | none => none
      else none
    if target' == tgt then out := out ++ [g]
    else out := out ++ [← g.replaceTargetDefEq target']
  dbgLog s!"hstep_unify: loops converted {conv} left {left}"
  hnormStats.set (conv, left)
  setGoals out

/-! ## Diagnosis of stage 94 (`VED_PROBE_S94` and `VED_DUMP_DIR` set; never in a default script)

`↓ vedMemProbe` (a wildcard pre-simproc, only added to the stage-94 simp when the gate is open) counts the visited sub-terms (a pre call happens after the
simp cache missed) by head symbol; a monitor thread (`ved_s94_probe_start` / `ved_s94_probe_stop`) writes the counters to `addr.log` every 15 s, so that a run
that is killed still shows where it was: visits, the simp state's step count and cache size, the time since the last visit (a stall = work outside the node
visits), the largest head counts, the last heads visited.  The first `And` / `Exists` visits are logged with their time and tree size. -/

initialize s94Hist : IO.Ref (Std.HashMap String Nat) ← IO.mkRef {}
initialize s94Visits : IO.Ref Nat ← IO.mkRef 0
initialize s94SimpState : IO.Ref (Nat × Nat) ← IO.mkRef (0, 0)
initialize s94LastMs : IO.Ref Nat ← IO.mkRef 0
initialize s94Last : IO.Ref (Array String) ← IO.mkRef #[]
initialize s94Stop : IO.Ref Bool ← IO.mkRef false
initialize s94Logged : IO.Ref Nat ← IO.mkRef 0
initialize s94T0 : IO.Ref Nat ← IO.mkRef 0
/-- gap diagnosis: time (µs) between two consecutive visits by (previous head → head), and the last visit's time stamp (ns) -/
initialize s94Gap : IO.Ref (Std.HashMap String Nat) ← IO.mkRef {}
initialize s94GapT : IO.Ref Nat ← IO.mkRef 0

def s94Head (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => n.toString
  | .fvar _ => "<fvar>"
  | .lam .. => "<lam>"
  | .forallE .. => "<forall>"
  | .letE .. => "<let>"
  | .mdata .. => "<mdata>"
  | .proj .. => "<proj>"
  | .lit _ => "<lit>"
  | .bvar _ => "<bvar>"
  | .sort _ => "<sort>"
  | .mvar _ => "<mvar>"
  | .app .. => "<app>"

open Lean Meta Simp in
simproc_decl vedMemProbe (_) := fun e => do
  let h := s94Head e
  s94Hist.modify fun m => m.insert h (m.getD h 0 + 1)
  let v ← s94Visits.modifyGet fun v => (v + 1, v + 1)
  let now ← IO.monoMsNow
  s94LastMs.set now
  let nowN ← IO.monoNanosNow
  let prevN ← s94GapT.get
  if prevN != 0 then
    let ph := (← s94Last.get).back?.getD "-"
    s94Gap.modify fun m => let k := ph ++ " -> " ++ h; m.insert k (m.getD k 0 + (nowN - prevN) / 1000)
  s94GapT.set nowN
  s94Last.modify fun a => (a.push h).extract (a.size + 1 - 6) (a.size + 1)
  if v % 2000 == 0 then
    let st ← get
    s94SimpState.set (st.numSteps, st.usedTheorems.map.foldl (fun a _ _ => a + 1) 0)
  if (← IO.getEnv "VED_S94_SAMPLE").isSome && (h == "ite" || h == "Eq") && (← s94Hist.get).getD h 0 % 400 == 1 then
    dbgLog s!"S94 sample {h} v={v} dag={(Tools.VedU1WireShare.collectDag (fun _ => true) e).size}: {((toString (← Meta.ppExpr e)).replace "\n" " ").take 260}"
  if (h == "And" || h == "Exists") && (← s94Logged.get) < 16 then
    s94Logged.modify (· + 1)
    dbgLog s!"S94 visit {h} t={now - (← s94T0.get)} ms visits={v} tree={Tools.VedU1Loop.treeSizeVal e}"
  return .continue

/-- `ved_s94_probe_start`: reset the counters, log the goal's DAG size, start the monitor thread (only with the two env vars set) -/
elab "ved_s94_probe_start" : tactic => do
  if (← IO.getEnv "VED_PROBE_S94").isSome && (← IO.getEnv "VED_DUMP_DIR").isSome then
    s94Hist.set {}; s94Visits.set 0; s94Stop.set false; s94Logged.set 0; s94Last.set #[]
    s94T0.set (← IO.monoMsNow); s94LastMs.set (← IO.monoMsNow); s94SimpState.set (0, 0)
    for g in ← getGoals do
      let e ← instantiateMVars (← g.getType)
      dbgLog s!"S94 start dag={(Tools.VedU1WireShare.collectDag (fun _ => true) e).size} tree={Tools.VedU1Loop.treeSizeVal e}"
    let _ ← IO.asTask (prio := .dedicated) do
      let mut k := 0
      while !(← s94Stop.get) do
        IO.sleep 15000
        if (← s94Stop.get) then break
        k := k + 1
        let now ← IO.monoMsNow
        let h ← s94Hist.get
        let top := (h.toList.toArray.qsort (fun a b => a.2 > b.2)).toList.take 8
        let (steps, csz) ← s94SimpState.get
        let rss ← try
            let st ← IO.FS.readFile "/proc/self/status"
            pure ((st.splitOn "\n").find? (·.startsWith "VmRSS") |>.getD "")
          catch _ => pure ""
        dbgLog s!"S94 tick {k} {rss.replace "\t" " "} t={now - (← s94T0.get)} ms visits={← s94Visits.get} sinceLastVisit={now - (← s94LastMs.get)} ms steps@={steps} usedThms@={csz} top={top} last={← s94Last.get}"

elab "ved_s94_probe_stop" : tactic => do
  if (← IO.getEnv "VED_PROBE_S94").isSome && (← IO.getEnv "VED_DUMP_DIR").isSome then
    s94Stop.set true
    dbgLog s!"S94 stop t={(← IO.monoMsNow) - (← s94T0.get)} ms visits={← s94Visits.get}"

/-! ### Per-conjunct diagnosis of stage 94 (`VED_S94_DIAG`, `VED_PROBE_S94`, `VED_DUMP_DIR` all set; never in a default script)

`ved_s94_diag [lemmas]` takes the target of the main goal apart at the top (`∃` binders become local hypotheses, `∧` are split) and runs `Meta.simp`
(the context of `ved_loop_simp [lemmas]`, simprocs included) once per conjunct under a local heartbeat budget, logging per conjunct: milliseconds,
probe visits, DAG/tree size before and after, the top heads, whether the budget ran out.  Then the process exits (a diagnosis run, no proof). -/

open Lean Meta Elab Tactic in
partial def s94Walk (e : Expr) (k : Expr → TacticM Unit) : TacticM Unit := do
  let e ← whnfR e
  if e.isAppOfArity ``And 2 then
    s94Walk e.appFn!.appArg! k
    s94Walk e.appArg! k
  else if e.isAppOfArity ``Exists 2 then
    let α := e.appFn!.appArg!
    let p := e.appArg!
    match p with
    | .lam n t b bi => withLocalDecl n bi t fun x => s94Walk (b.instantiate1 x) k
    | _ => k e
  else k e

open Lean Meta Elab Tactic in
elab "ved_s94_diag " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => withMainContext do
  unless (← IO.getEnv "VED_S94_DIAG").isSome && (← IO.getEnv "VED_PROBE_S94").isSome && (← IO.getEnv "VED_DUMP_DIR").isSome do return
  let stx0 ← `(tactic| ved_loop_simp [$ls,*])
  let some (_, .ok stx1) ← liftMacroM (Lean.Elab.expandMacroImpl? (← getEnv) stx0) | throwError "ved_s94_diag: ved_loop_simp does not expand"
  let sc ← Lean.Elab.Tactic.mkSimpContext stx1 (eraseLocal := false)
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let t0 ← IO.monoMsNow
  -- prefixes of the module body: `evalAssigns we mems (body.take m) env0` simplified alone, to see the growth with the number of statements
  let calls := Tools.VedU1WireShare.collectDag (fun x => x.isAppOfArity ``Sparkle.IR.Semantics.stepModule 4) tgt
  if let some sm := calls[0]? then
    let a := sm.getAppArgs
    let bodyE ← do
      match ← unfoldDefinition? a[1]! with
      | some b => pure b
      | none => pure a[1]!
    let mut elems : Array Expr := #[]
    let mut cur := bodyE
    let ty := Lean.mkConst ``Sparkle.IR.AST.Stmt
    while cur.isAppOfArity ``List.cons 3 do
      elems := elems.push (cur.getArg! 1)
      cur := cur.getArg! 2
    let kinds := elems.foldl (fun (m : Std.HashMap String Nat) e => let h := e.getAppFn.constName?.map toString |>.getD "?"; m.insert h (m.getD h 0 + 1)) {}
    dbgLog s!"S94D body: {elems.size} statements, kinds={kinds.toList} tail-is-nil={cur.isAppOfArity ``List.nil 1}"
    let n := elems.size
    let mut stop := false
    for m in [n / 64, n / 32, n / 16, n / 8, n / 4] do
      if stop || m == 0 then continue
      let pre ← mkListLit ty (elems.extract 0 m).toList
      let e := mkApp4 (Lean.mkConst ``Sparkle.IR.Semantics.evalAssigns) a[0]! a[3]! pre a[2]!
      s94Hist.set {}
      let v0 ← s94Visits.get
      let t1 ← IO.monoMsNow
      let hb ← IO.getNumHeartbeats
      let r ← try
          withTheReader Core.Context (fun c => { c with maxHeartbeats := 500000000, initHeartbeats := hb }) do
            tryCatchRuntimeEx (do
              let (r, _) ← sc.dischargeWrapper.with fun d? => Meta.simp e sc.ctx sc.simprocs d?
              pure (some r)) fun ex => if ex.isRuntime then pure none else throw ex
        catch _ => pure none
      let ms := (← IO.monoMsNow) - t1
      let h ← s94Hist.get
      let top := (h.toList.toArray.qsort (fun a b => a.2 > b.2)).toList.take 5
      match r with
      | some r =>
        dbgLog s!"S94D prefix {m}/{n}: ms={ms} hb={((← IO.getNumHeartbeats) - hb) / 1000} visits={(← s94Visits.get) - v0} result dag={(Tools.VedU1WireShare.collectDag (fun _ => true) r.expr).size} tree={Tools.VedU1Loop.treeSizeVal r.expr} top={top}"
      | none =>
        dbgLog s!"S94D prefix {m}/{n}: BUDGET ms={ms} visits={(← s94Visits.get) - v0} top={top}"
        stop := true
    pure ()
  let idx ← IO.mkRef 0
  s94Walk tgt fun c => do
    let i ← idx.modifyGet fun i => (i, i + 1)
    let dag0 := (Tools.VedU1WireShare.collectDag (fun _ => true) c).size
    let tree0 := Tools.VedU1Loop.treeSizeVal c
    let head := (toString (← ppExpr c)).replace "\n" " "
    if (← IO.monoMsNow) - t0 > 500000 then
      dbgLog s!"S94D #{i} SKIPPED (total 500 s used) dag={dag0} tree={tree0}"
      return
    s94Hist.set {}
    s94Gap.set {}; s94GapT.set 0
    let v0 ← s94Visits.get
    let h0 ← declWidthHits.get
    let t1 ← IO.monoMsNow
    let hb ← IO.getNumHeartbeats
    let r ← try
        withTheReader Core.Context (fun c => { c with maxHeartbeats := (if i == 0 then 2000000000 else 500000000), initHeartbeats := hb }) do
          tryCatchRuntimeEx (do
            let (r, _) ← sc.dischargeWrapper.with fun d? => Meta.simp c sc.ctx sc.simprocs d?
            pure (some r)) fun ex => if ex.isRuntime then do dbgLog s!"S94D #{i} runtime exception: {((← ex.toMessageData.toString).replace "\n" " ").take 700}"; pure none else throw ex
      catch ex => do dbgLog s!"S94D #{i} error {← ex.toMessageData.toString}"; pure none
    let ms := (← IO.monoMsNow) - t1
    let hbd := ((← IO.getNumHeartbeats) - hb) / 1000
    let v1 ← s94Visits.get
    let h ← s94Hist.get
    let top := (h.toList.toArray.qsort (fun a b => a.2 > b.2)).toList.take 6
    if i == 0 then
      let gp := ((← s94Gap.get).toList.toArray.qsort (fun a b => a.2 > b.2)).toList.take 10
      dbgLog s!"S94D #0 gap(us) by prev->head: {gp}"
      -- variants: the same simp with one simp lemma erased (diagnosis of which rule's cost dominates)
      for nm in ((← IO.getEnv "VED_S94_ERASE").getD "").splitOn "," do
        if nm.isEmpty then continue
        let thms ← sc.ctx.simpTheorems.mapM fun th => do
          try th.erase (.decl nm.toName) catch _ => pure th
        let ctx2 := sc.ctx.setSimpTheorems thms
        -- a name that is a simproc is erased from the simprocs as well (diagnosis of builtin simprocs such as `reduceIte`)
        let sps := sc.simprocs.map fun sp => sp.erase nm.toName
        s94Hist.set {}
        let v0 ← s94Visits.get
        let t1 ← IO.monoMsNow
        let hb ← IO.getNumHeartbeats
        let r2 ← try
            withTheReader Core.Context (fun c => { c with maxHeartbeats := 2000000000, initHeartbeats := hb }) do
              tryCatchRuntimeEx (do
                let (r, _) ← sc.dischargeWrapper.with fun d? => Meta.simp c ctx2 sps d?
                pure (some r)) fun ex => if ex.isRuntime then pure none else throw ex
          catch _ => pure none
        let h ← s94Hist.get
        let top := (h.toList.toArray.qsort (fun a b => a.2 > b.2)).toList.take 6
        dbgLog s!"S94D #0 erase {nm}: {if r2.isSome then "done" else "BUDGET"} ms={(← IO.monoMsNow) - t1} hb={((← IO.getNumHeartbeats) - hb) / 1000} visits={(← s94Visits.get) - v0} tree={match r2 with | some r => Tools.VedU1Loop.treeSizeVal r.expr | none => 0} top={top}"
    match r with
    | some r =>
      dbgLog s!"S94D #{i} ms={ms} hb={hbd} visits={v1 - v0} declWidthHits={(← declWidthHits.get) - h0} bindUs(simp m, proof)={← bindStrictMs.get} dag {dag0}->{(Tools.VedU1WireShare.collectDag (fun _ => true) r.expr).size} ptrObjs {← Lean.Expr.numObjs c}->{← Lean.Expr.numObjs r.expr} tree {tree0}->{Tools.VedU1Loop.treeSizeVal r.expr} top={top} src={head.take 110}"
    | none =>
      dbgLog s!"S94D #{i} BUDGET/ERR ms={ms} visits={v1 - v0} dag={dag0} tree={tree0} top={top} src={head.take 110}"
  dbgLog s!"S94D done total ms={(← IO.monoMsNow) - t0}"
  IO.Process.exit 0


end Tools.VedMemLoop
