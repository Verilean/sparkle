import Lean
import Tools.VedMemLoop
import Tools.VedU1WireShare

/-!
# Diagnosis of stage 94 of the memory loop (diagnosis only)

Everything here is behind `VED_PROBE_S94` + `VED_DUMP_DIR` (and `VED_S94_DIAG` for the per-conjunct diagnosis); the entry (`Tools/VedMemEntry.lean`)
emits the calls only when the gate is open at generation time.  The default script contains none of it.
-/

namespace Tools.VedMemS94Diag

open Lean Meta Elab Tactic Tools.VedMemLoop

/-! ## Diagnosis of stage 94 (`VED_PROBE_S94` and `VED_DUMP_DIR` set; never in a default script; nothing here runs otherwise)

`↓ vedMemProbe` (a wildcard pre-simproc, only added to the stage-94 simp when the gate is open) counts the visited sub-terms (a pre call happens after the
simp cache missed) by head symbol; a monitor task (`ved_s94_probe [t]`, one stop token per call) writes the counters to `addr.log` every 15 s, so that a run
that is killed still shows where it was: visits, the simp state's step count and cache size, the time since the last visit (a stall = work outside the node
visits), the largest head counts, the last heads visited.  The first `And` / `Exists` visits are logged with their time and tree size. -/

initialize s94Hist : IO.Ref (Std.HashMap String Nat) ← IO.mkRef {}
initialize s94Visits : IO.Ref Nat ← IO.mkRef 0
initialize s94SimpState : IO.Ref (Nat × Nat) ← IO.mkRef (0, 0)
initialize s94LastMs : IO.Ref Nat ← IO.mkRef 0
initialize s94Last : IO.Ref (Array String) ← IO.mkRef #[]
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

/-- the gate of all stage-94 diagnosis: `VED_PROBE_S94` and `VED_DUMP_DIR` are set -/
def s94Gate : IO Bool := return (← IO.getEnv "VED_PROBE_S94").isSome && (← IO.getEnv "VED_DUMP_DIR").isSome

/-- `VED_S94_NOBIND` (diagnosis only): the new branch without the in-order `Option.bind` simprocs -/
def s94NoBind : IO Bool := return (← IO.getEnv "VED_S94_NOBIND").isSome

/-- the monitor of ONE stage-94 run: its own stop token and its task.  There is no global stop flag: a later start cannot revive or hide an earlier monitor. -/
structure S94Monitor where
  stop : IO.Ref Bool
  task : Task (Except IO.Error Unit)

/-- start the monitor: reset the counters, log the goal's DAG size, start the task (it checks ITS token every 100 ms and logs a tick every
`VED_S94_TICK_MS` ms, default 15000) -/
def s94Start : TacticM S94Monitor := do
  s94Hist.set {}; s94Visits.set 0; s94Logged.set 0; s94Last.set #[]
  s94T0.set (← IO.monoMsNow); s94LastMs.set (← IO.monoMsNow); s94SimpState.set (0, 0)
  for g in ← getGoals do
    let e ← instantiateMVars (← g.getType)
    dbgLog s!"S94 start dag={(Tools.VedU1WireShare.collectDag (fun _ => true) e).size} tree={Tools.VedU1Loop.treeSizeVal e}"
  let tickMs := ((← IO.getEnv "VED_S94_TICK_MS").bind String.toNat?).getD 15000
  let stop ← IO.mkRef false
  let task ← IO.asTask (prio := .dedicated) do
    let mut k := 0
    let mut waited := 0
    while !(← stop.get) do
      IO.sleep 100
      waited := waited + 100
      if (← stop.get) then break
      if waited < tickMs then continue
      waited := 0
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
  return { stop, task }

/-- stop the monitor: set ITS token, wait until its task has ended (no log line of it after this), log the stop line -/
def S94Monitor.finish (m : S94Monitor) : IO Unit := do
  m.stop.set true
  let _ ← IO.wait m.task
  dbgLog s!"S94 stop t={(← IO.monoMsNow) - (← s94T0.get)} ms visits={← s94Visits.get}"

/-- `ved_s94_probe [t]`: `t` (the stage-94 simp) under a monitor of its own that is stopped in a `finally` (also when `t` throws, incl. a runtime
exception).  The entry emits it only when the gate is open at generation time.  Seam `VED_S94_FORCE_FAIL=ms`: wait that many ms, then throw
before `t` (a forced failure of the stage-94 simp, to show that the monitor stops). -/
elab "ved_s94_probe " "[" t:tactic "]" : tactic => do
  unless (← s94Gate) do evalTactic t; return
  let m ← s94Start
  try
    if let some ms := (← IO.getEnv "VED_S94_FORCE_FAIL").bind String.toNat? then
      IO.sleep ms.toUInt32
      throwError "ved_s94_probe: forced failure (diagnosis seam VED_S94_FORCE_FAIL)"
    evalTactic t
  finally
    m.finish

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
  unless (← IO.getEnv "VED_S94_DIAG").isSome && (← s94Gate) do return
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

end Tools.VedMemS94Diag
