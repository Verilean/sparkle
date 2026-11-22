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
/-- gap diagnosis: the previous visited term, and the largest single gaps (µs, previous head, head, the previous term printed, the next term printed) -/
initialize s94PrevE : IO.Ref (Option Lean.Expr) ← IO.mkRef none
initialize s94PrevHb : IO.Ref Nat ← IO.mkRef 0
initialize s94Big : IO.Ref (Array (Nat × String)) ← IO.mkRef #[]

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

/-- `VED_S94_DISCH` (diagnosis only): (calls, us, heartbeats) of the discharger of the conjunct simp (inclusive: nested calls are counted twice) -/
initialize s94Dis : IO.Ref (Nat × Nat × Nat) ← IO.mkRef (0, 0, 0)

open Lean Meta Simp in
/-- the discharger of the simp set with a timer around it -/
def s94TimedDisch (d? : Option Simp.Discharge) : Simp.Discharge := fun e => do
  let t0 ← IO.monoNanosNow
  let h0 ← IO.getNumHeartbeats
  let r ← (match d? with | some d => d e | none => Simp.dischargeDefault? e)
  let t1 ← IO.monoNanosNow
  let h1 ← IO.getNumHeartbeats
  s94Dis.modify fun (a, b, c) => (a + 1, b + (t1 - t0) / 1000, c + (h1 - h0))
  return r

/-- `VED_S94_OPS` (diagnosis only): number of operation tables logged -/
initialize s94OpsN : IO.Ref Nat ← IO.mkRef 0

/-- time (us) of single `Expr`/`Meta` operations on `e`, the term visited right after a large gap (diagnosis only; the ones that simp itself runs between two visits) -/
def s94Ops (e : Expr) : MetaM String := do
  let mut out : Array String := #[]
  let timed := fun (nm : String) (act : MetaM Unit) => do
    let t ← IO.monoNanosNow
    try act catch _ => pure ()
    pure s!"{nm}={((← IO.monoNanosNow) - t) / 1000}"
  out := out.push (← timed "instMVars" do discard <| instantiateMVars e)
  out := out.push (← timed "replaceId" do discard <| pure (e.replace fun _ => none))
  let saved ← get
  modify fun s => { s with cache := {} }
  out := out.push (← timed "inferType(cold)" do discard <| inferType e)
  out := out.push (← timed "inferType(warm)" do discard <| inferType e)
  out := out.push (← timed "isProof" do discard <| isProof e)
  out := out.push (← timed "whnfCore" do discard <| whnfCore e)
  -- a structurally equal copy with other pointers at the free variables
  let e' := e.replace fun x => if x.isFVar then some (mkFVar x.fvarId!) else none
  out := out.push (← timed "eqvCopy" do discard <| pure (e == e'))
  out := out.push (← timed "hashMapCopy" do
    let m : Std.HashMap Expr Nat := ({} : Std.HashMap Expr Nat).insert e 1
    discard <| pure (m[e']?))
  let ites := Tools.VedU1WireShare.collectDag (fun x => x.isAppOfArity ``ite 5) e
  if let some i := ites[0]? then
    let c := i.getArg! 1
    out := out.push (← timed "synthDecidable" do
      let ty ← mkAppM ``Decidable #[c]
      discard <| synthInstance ty)
    out := out.push (← timed "inferType(ite cond)" do discard <| inferType c)
  let lts := Tools.VedU1WireShare.collectDag (fun x => x.isAppOfArity ``LT.lt 4) e
  if let some i := lts[0]? then
    out := out.push (← timed "isDefEq(lt,lt)" do discard <| isDefEq i i)
  set saved
  return s!"dag={(Tools.VedU1WireShare.collectDag (fun _ => true) e).size} ites={ites.size} lts={lts.size} " ++ " ".intercalate out.toList

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
    let gapUs := (nowN - prevN) / 1000
    -- the largest single gaps (>= 20 ms) with the terms around them
    if gapUs ≥ 20000 && ((← s94Big.get).size < 6 || gapUs > ((← s94Big.get).foldl (fun a x => min a x.1) gapUs)) then
      let pp (x : Expr) : MetaM String := do
        try pure (((toString (← Meta.ppExpr x)).replace "\n" " ").take 240).toString catch _ => pure "?"
      let pe ← s94PrevE.get
      let ps ← match pe with | some x => pp x | none => pure "-"
      let hbGap := (← IO.getNumHeartbeats) - (← s94PrevHb.get)
      let line := s!"gap {gapUs} us hb={hbGap} {ph} -> {h}; prev dag={match pe with | some x => (Tools.VedU1WireShare.collectDag (fun _ => true) x).size | none => 0} tree={match pe with | some x => Tools.VedU1Loop.treeSizeVal x | none => 0}; next dag={(Tools.VedU1WireShare.collectDag (fun _ => true) e).size} tree={Tools.VedU1Loop.treeSizeVal e}: {ps} || next: {← pp e}"
      if gapUs ≥ 200000 && (← IO.getEnv "VED_S94_OPS").isSome && (← s94OpsN.get) < 6 then
        s94OpsN.modify (· + 1)
        dbgLog s!"S94 ops after gap {gapUs} us {ph} -> {h}: next: {← s94Ops e}"
        if let some x := pe then
          -- the largest argument of the previously visited term (the gap is the simp of its arguments, answered by the cache)
          let mut best : Option Expr := none
          let mut bsz := 0
          for a in x.getAppArgs do
            let z := (Tools.VedU1WireShare.collectDag (fun _ => true) a).size
            if z > bsz then best := some a; bsz := z
          if let some a := best then dbgLog s!"S94 ops   prev's largest arg ({s94Head a}): {← s94Ops a}"
      s94Big.modify fun a =>
        let a := a.push (gapUs, line)
        if a.size > 6 then (a.qsort (fun x y => x.1 > y.1)).extract 0 6 else a
  s94GapT.set nowN
  s94PrevHb.set (← IO.getNumHeartbeats)
  s94PrevE.set (some e)
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

/-- `VED_S94_PROF` (with `VED_DUMP_DIR`): the exclusive-time profile (`Tools/VedMemS94Prof.lean`) replaces the counting probe -/
def s94Prof : IO Bool := return (← IO.getEnv "VED_S94_PROF").isSome && (← IO.getEnv "VED_DUMP_DIR").isSome

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
  s94OpsN.set 6
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
  -- `VED_S94_MATCH`: time of the match test (`isDefEq` at reducible transparency) of the left side of the first `hreg*` hypotheses against the first `Signal.val` terms of the goal
  if (← IO.getEnv "VED_S94_MATCH").isSome then
    let vals := Tools.VedU1WireShare.collectDag (fun x => x.isAppOf ``Sparkle.Core.Signal.Signal.val) tgt
    dbgLog s!"S94D match: {vals.size} Signal.val terms in the goal"
    let mut shown := 0
    for d in (← getLCtx) do
      if d.isImplementationDetail || !(d.userName.toString.startsWith "hreg") || shown ≥ 3 then continue
      shown := shown + 1
      let ty ← instantiateMVars d.type
      let (_, _, body) ← forallMetaTelescopeReducing ty
      let lhs := (body.getAppArgs[1]?).getD body
      dbgLog s!"S94D match {d.userName}: type={((toString (← ppExpr ty)).replace "\n" " ").take 500}"
      dbgLog s!"S94D match {d.userName}: lhs head={lhs.getAppFn.constName?} dag={(Tools.VedU1WireShare.collectDag (fun _ => true) lhs).size}"
      for v in vals.extract 0 4 do
        let t1 ← IO.monoNanosNow
        let ok ← withReducible do
          let sv ← saveState
          let r ← try isDefEq lhs v catch _ => pure false
          sv.restore
          pure r
        dbgLog s!"S94D match   vs val dag={(Tools.VedU1WireShare.collectDag (fun _ => true) v).size}: {ok} {((← IO.monoNanosNow) - t1) / 1000} us"
  if (← IO.getEnv "VED_S94_MATCH_ONLY").isSome then IO.Process.exit 0
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
    s94Gap.set {}; s94GapT.set 0; s94Big.set #[]; s94PrevE.set none; s94OpsN.set 0
    s94Dis.set (0, 0, 0)
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
      let gp2 := ((← s94Gap.get).toList.toArray.qsort (fun a b => a.2 > b.2)).toList.take 40
      dbgLog s!"S94D #0 gap40 total={((← s94Gap.get).fold (fun a _ v => a + v) 0)}: {gp2.drop 10}"
      for (_, l) in ← s94Big.get do dbgLog s!"S94D #0 big {l}"
      -- variants: the same simp with one simp lemma erased (diagnosis of which rule's cost dominates)
      for nm in ((← IO.getEnv "VED_S94_ERASE").getD "").splitOn "," do
        if nm.isEmpty then continue
        -- `fvars:PREFIX`: the local hypotheses whose name starts with PREFIX are erased from the simp set (`hreg`, `hM`, `hD`, `hL` of the step case)
        let lctx ← getLCtx
        let fvIds : Array FVarId :=
          if nm.startsWith "fvars:" then
            lctx.foldl (fun a d => if !d.isImplementationDetail && (d.userName.toString.startsWith (nm.drop 6).toString) then a.push d.fvarId else a) #[]
          else #[]
        dbgLog s!"S94D #0 erase {nm}: {fvIds.size} hypotheses"
        let thms ← sc.ctx.simpTheorems.mapM fun th => do
          let mut th := th
          for id in fvIds do
            try th ← th.erase (.fvar id) catch _ => pure ()
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
      dbgLog s!"S94D #{i} disch(calls,us,hb)={← s94Dis.get}"
      dbgLog s!"S94D #{i} ms={ms} hb={hbd} visits={v1 - v0} declWidthHits={(← declWidthHits.get) - h0} bindUs(simp m, proof)={← bindStrictMs.get} dag {dag0}->{(Tools.VedU1WireShare.collectDag (fun _ => true) r.expr).size} ptrObjs {← Lean.Expr.numObjs c}->{← Lean.Expr.numObjs r.expr} tree {tree0}->{Tools.VedU1Loop.treeSizeVal r.expr} top={top} src={head.take 110}"
    | none =>
      dbgLog s!"S94D #{i} BUDGET/ERR ms={ms} visits={v1 - v0} dag={dag0} tree={tree0} top={top} src={head.take 110}"
  dbgLog s!"S94D done total ms={(← IO.monoMsNow) - t0}"
  IO.Process.exit 0

/-- `ved_s94_exit k` (diagnosis only; emitted by the entry right after `ved_stamp k` when the gate and `VED_EXIT_AT=k` are set at generation time):
the process ends here (no fallback, no later stages) -/
elab "ved_s94_exit " k:num : tactic => do
  unless (← s94Gate) do return
  if (← IO.getEnv "VED_EXIT_AT").bind String.toNat? == some k.getNat then
    dbgLog s!"S94 exit at stamp {k.getNat}"
    IO.Process.exit 0

end Tools.VedMemS94Diag
