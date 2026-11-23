import Lean
import Tools.VedMemLoop
import Tools.VedMemS94Fix
import Tools.VedMemS94Peel
import Tools.VedMemS94Gen
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

syntax (name := vedS97Peel) "ved_s97_peel " ident : tactic

/-- the same expansion as `ved_mem_peel` (`Tools/VedMemEntry.lean`, which imports this module) -/
macro_rules
  | `(tactic| ved_s97_peel $h:ident) =>
    `(tactic| first
      | exact $h
      | (ved_mem_shape ite; refine Tools.VedMem.MemInv.ite (fun _ => ?_) (fun _ => ?_) <;> ved_s97_peel $h)
      | (ved_mem_shape lam; refine Tools.VedMem.MemInv.other_leaf ?_ (by decide) _ _; ved_s97_peel $h)
      | (ved_mem_shape lam; refine Tools.VedMem.MemInv.write_leaf ?_ ?_ ?_ ?_; ved_s97_peel $h)
      | (ved_mem_shape fvar; refine Tools.VedMem.MemInv.hold_leaf ?_ ?_; ved_s97_peel $h))

/-! ### Stage-97 checkpoint (`VED_S94_CKPT=DIR` and `VED_S94_CKPT_AT=97`, with the gate; never in a default script)

`ved_s94_ckpt97 [hM0, hM1, ..]` (emitted by the entry right after `ved_stamp 97` instead of the stage-94 checkpoint) writes EVERY open goal as the axiom
`ved_ckpt97.goal<j> : ∀ (context), target` into `DIR/VedCkpt.olean` (as above, the same module data) and `DIR/ckpt97.txt` (`n<TAB>goals`, then per goal
`hm<TAB>j<TAB>positions of the memory invariants hM_i in its context`), then the process ends.  `#ved_s94_ckpt97_replay "DIR"` re-creates goal(s) (hypotheses
`ck0, ck1, ..`) and runs the peel (`all_goals (try (first | ved_mem_peel ck_a | ved_mem_peel ck_b ..))`, the step of the script after stamp 97) goal by goal with
a per-goal line (time, heartbeats, goals left). -/

open Lean Meta Elab Tactic in
elab "ved_s94_ckpt97 " "[" hs:ident,* "]" : tactic => do
  unless (← s94Gate) do return
  let some dir := (← IO.getEnv "VED_S94_CKPT") | return
  let gs ← getGoals
  dbgLog s!"S94 ckpt97: start, {gs.length} goals"
  let mut lines : Array String := #[s!"n\t{gs.length}"]
  let mut j : Nat := 0
  -- an axiom that only transports the term: no kernel check
  for g in gs do
    let (ty, hmLine) ← g.withContext do
      let tgt ← instantiateMVars (← g.getType)
      let fvs : Array Expr := (← getLCtx).foldl (fun a d => if d.isImplementationDetail then a else a.push d.toExpr) #[]
      let ids := fvs.map (·.fvarId!)
      let mut pos : Array String := #[]
      for h in hs.getElems do
        let some d := (← getLCtx).findFromUserName? h.getId | throwError "ved_s94_ckpt97: no hypothesis {h.getId}"
        let some i := ids.findIdx? (· == d.fvarId) | throwError "ved_s94_ckpt97: hypothesis not in the context"
        pos := pos.push (toString i)
      pure ((← instantiateMVars (← mkForallFVars fvs tgt (usedLetOnly := false))), s!"hm\t{j}\t" ++ "\t".intercalate pos.toList)
    lines := lines.push hmLine
    if ty.hasFVar || ty.hasMVar || ty.hasLevelParam || ty.hasLevelMVar then
      throwError "ved_s94_ckpt97: goal {j} still has fvars/mvars/level parameters (fvar {ty.hasFVar} mvar {ty.hasMVar} lparam {ty.hasLevelParam})"
    withTheReader Core.Context (fun c => { c with options := c.options.setBool `debug.skipKernelTC true }) do
      addDecl (.axiomDecl { name := Name.mkSimple s!"ved_ckpt97_goal{j}", levelParams := [], type := ty, isUnsafe := false })
    j := j + 1
  dbgLog "S94 ckpt97: axioms added"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/ckpt97.txt") ("\n".intercalate lines.toList ++ "\n")
  let md ← Lean.mkModuleData (← getEnv)
  let realized (n : Name) : Bool :=
    match n with
    | .str _ s => s == "splitter" || s == "eq_def" || s == "sunfold" || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
    | _ => false
  let keep := md.constants.filter (fun c => !realized c.name)
  let md' := { md with constNames := keep.map (·.name), constants := keep }
  Lean.saveModuleData (dir ++ "/VedCkpt.olean") (← getEnv).mainModule md'
  dbgLog s!"S94 ckpt97 written to {dir}: {gs.length} goals, {md.constants.size} constants ({md.constants.size - keep.size} realized equation constants left out)"
  IO.Process.exit 0

/-! ### Stage-100 checkpoint (`VED_S94_CKPT=DIR` and `VED_S94_CKPT_AT=100`, with the gate; never in a default script)

`ved_s94_ckpt100 s [hM0, ..]` (emitted by the entry right after `ved_stamp 100`, i.e. just before `ved_loop_gen_mem s`) writes every open goal as the axiom
`ved_ckpt100.goal<j> : ∀ (context), target` into `DIR/VedCkpt.olean` and `DIR/ckpt100.txt` (`n<TAB>goals`, then per goal `hm<TAB>j<TAB>positions of the
hM_i` and `sp<TAB>j<TAB>position of s`), then the process ends.  `#ved_s94_ckpt100_replay "DIR"` re-creates the goals (hypotheses `ck0, ck1, ..`) and
runs `ved_loop_gen_mem ck<s>` (see there). -/

open Lean Meta Elab Tactic in
elab "ved_s94_ckpt100 " s:ident " [" hs:ident,* "]" : tactic => do
  unless (← s94Gate) do return
  let some dir := (← IO.getEnv "VED_S94_CKPT") | return
  let gs ← getGoals
  dbgLog s!"S94 ckpt100: start, {gs.length} goals"
  let mut lines : Array String := #[s!"n\t{gs.length}"]
  let mut j : Nat := 0
  for g in gs do
    let (ty, hmLine, spLine, ksLine) ← g.withContext do
      let tgt ← instantiateMVars (← g.getType)
      let fvs : Array Expr := (← getLCtx).foldl (fun a d => if d.isImplementationDetail then a else a.push d.toExpr) #[]
      let ids := fvs.map (·.fvarId!)
      let mut pos : Array String := #[]
      for h in hs.getElems do
        let some d := (← getLCtx).findFromUserName? h.getId | throwError "ved_s94_ckpt100: no hypothesis {h.getId}"
        let some i := ids.findIdx? (· == d.fvarId) | throwError "ved_s94_ckpt100: hypothesis not in the context"
        pos := pos.push (toString i)
      let some sd := (← getLCtx).findFromUserName? s.getId | throwError "ved_s94_ckpt100: no variable {s.getId}"
      let some si := ids.findIdx? (· == sd.fvarId) | throwError "ved_s94_ckpt100: variable not in the context"
      pure ((← instantiateMVars (← mkForallFVars fvs tgt (usedLetOnly := false))), s!"hm\t{j}\t" ++ "\t".intercalate pos.toList, s!"sp\t{j}\t{si}",
        s!"ks\t{j}\t" ++ "\t".intercalate (ids.toList.map (·.name.toString)))
    lines := ((lines.push hmLine).push spLine).push ksLine
    if ty.hasFVar || ty.hasMVar || ty.hasLevelParam || ty.hasLevelMVar then
      throwError "ved_s94_ckpt100: goal {j} still has fvars/mvars/level parameters"
    withTheReader Core.Context (fun c => { c with options := c.options.setBool `debug.skipKernelTC true }) do
      addDecl (.axiomDecl { name := Name.mkSimple s!"ved_ckpt100_goal{j}", levelParams := [], type := ty, isUnsafe := false })
    j := j + 1
  dbgLog "S94 ckpt100: axioms added"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/ckpt100.txt") ("\n".intercalate lines.toList ++ "\n")
  let md ← Lean.mkModuleData (← getEnv)
  let realized (n : Name) : Bool :=
    match n with
    | .str _ s => s == "splitter" || s == "eq_def" || s == "sunfold" || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
    | _ => false
  let keep := md.constants.filter (fun c => !realized c.name)
  let md' := { md with constNames := keep.map (·.name), constants := keep }
  Lean.saveModuleData (dir ++ "/VedCkpt.olean") (← getEnv).mainModule md'
  dbgLog s!"S94 ckpt100 written to {dir}: {gs.length} goals, {md.constants.size} constants ({md.constants.size - keep.size} realized equation constants left out)"
  IO.Process.exit 0

/-! ### Stage-94 checkpoint (`VED_S94_CKPT=DIR`, with the gate; never in a default script)

`ved_s94_ckpt [lemmas]` (emitted by the entry right after `ved_stamp 94`, i.e. with the goal the stage-94 simp starts from, only when the gate and
`VED_S94_CKPT` are set at generation time) writes the goal so that the stage-94 simp can be run again in a SEPARATE process without the prefix:

* `DIR/VedCkpt.olean`: `Lean.writeModule` of the whole environment of the run (the generated declarations of the module, the user's definitions of the file)
  plus the axiom `ved_ckpt.goal : ∀ (context) , target` (`mkForallFVars` over the local context of the goal, `let` variables stay `let`s; the axiom is
  never used in a proof: it only transports the term).  It imports what the run imported (same header) and is imported by name (`import VedCkpt`
  with `DIR` on `LEAN_PATH`).
* `DIR/ckpt.txt`: the simp arguments (pre/post arrow, `←`, a local hypothesis by its position in the local context, or a constant by its name components)
  and the table of `Tools.VedMemLoop.declWidthTab` (the only state outside the goal that the stage-94 simprocs read).

`#ved_s94_ckpt_replay "DIR"` (in a file that imports the same modules and `VedCkpt`) re-creates the goal (hypotheses named `ck0, ck1, ..`), runs
`ved_loop_simp [args]` on it (inside `ved_s94_noitecongr (..)` when the option `ved.mem.s94NoIteCongr` is set) and logs the time, heartbeats and the result sizes.
The process ends after the write (a diagnosis run, no proof). -/

private def nameComps (n : Name) : List String :=
  n.components.map fun
    | .str _ s => "s" ++ s
    | .num _ k => "n" ++ toString k
    | .anonymous => "a"

private def compsName (cs : List String) : Name :=
  cs.foldl (fun n c => if c.startsWith "n" then Name.mkNum n (c.drop 1).toNat! else Name.mkStr n (c.drop 1).toString) Name.anonymous

open Lean Meta Elab Tactic in
elab "ved_s94_ckpt " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => withMainContext do
  unless (← s94Gate) do return
  let some dir := (← IO.getEnv "VED_S94_CKPT") | return
  let g ← getMainGoal
  unless (← getGoals).length == 1 do throwError "ved_s94_ckpt: {(← getGoals).length} goals"
  let tgt ← instantiateMVars (← g.getType)
  let fvs : Array Expr := (← getLCtx).foldl (fun a d => a.push d.toExpr) #[]
  let fvIds := fvs.map (·.fvarId!)
  dbgLog "S94 ckpt: start"
  let ty ← instantiateMVars (← mkForallFVars fvs tgt (usedLetOnly := false))
  dbgLog "S94 ckpt: goal closed over the context"
  if ty.hasFVar || ty.hasMVar || ty.hasLevelParam || ty.hasLevelMVar then
    throwError "ved_s94_ckpt: the goal still has fvars/mvars/level parameters (fvar {ty.hasFVar} mvar {ty.hasMVar} lparam {ty.hasLevelParam})"
  let mut lines : Array String := #[]
  for l in ls.getElems do
    let pre := if l.raw[0].getNumArgs > 0 then ((l.raw[0].reprint.getD "?").trimAscii.toString) else ""
    let arrow := if l.raw[1].getNumArgs > 0 then "1" else "0"
    unless l.raw[2].isIdent do throwError "ved_s94_ckpt: a simp argument that is not an identifier: {l.raw[2]}"
    -- an identifier elaborates to the constant (or variable) applied to metavariables for its implicit arguments
    let e := (← instantiateMVars (← Tactic.elabTerm l.raw[2] none)).getAppFn
    if e.isFVar then
      let some i := fvIds.findIdx? (· == e.fvarId!) | throwError "ved_s94_ckpt: hypothesis not in the context"
      lines := lines.push s!"fv\t{pre}\t{arrow}\t{i}"
    else if e.isConst then
      lines := lines.push ("c\t" ++ pre ++ "\t" ++ arrow ++ "\t" ++ "\t".intercalate (nameComps e.constName!))
    else throwError "ved_s94_ckpt: unsupported simp argument {← ppExpr e}"
  let tab ← Tools.VedMemLoop.declWidthTab.get
  match tab with
  | some (mn, t) =>
    lines := lines.push ("tab\t" ++ "\t".intercalate (nameComps mn))
    for (k, v) in t.toList do lines := lines.push s!"w\t{k}\t{v}"
  | none => lines := lines.push "notab"
  -- an axiom that only transports the term: no kernel check (the type is the stage-94 goal, tree size ~4.5e8)
  withTheReader Core.Context (fun c => { c with options := c.options.setBool `debug.skipKernelTC true }) do
    addDecl (.axiomDecl { name := `ved_ckpt.goal, levelParams := [], type := ty, isUnsafe := false })
  dbgLog "S94 ckpt: axiom added"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/ckpt.txt") ("\n".intercalate lines.toList ++ "\n")
  -- the equation lemmas / splitters that the run realized lazily are left out (the replay realizes them again: an imported splitter without its extension
  -- entry makes `getEquationsFor` fail)
  let md ← Lean.mkModuleData (← getEnv)
  let realized (n : Name) : Bool :=
    match n with
    | .str _ s => s == "splitter" || s == "eq_def" || s == "sunfold" || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
    | _ => false
  let keep := md.constants.filter (fun c => !realized c.name)
  let md' := { md with constNames := keep.map (·.name), constants := keep }
  dbgLog s!"S94 ckpt: {md.constants.size} constants, {md.constants.size - keep.size} realized equation constants left out"
  Lean.saveModuleData (dir ++ "/VedCkpt.olean") (← getEnv).mainModule md'
  dbgLog s!"S94 ckpt written to {dir}: {fvs.size} context entries, {ls.getElems.size} simp arguments, goal dag={(Tools.VedU1WireShare.collectDag (fun _ => true) tgt).size}"
  IO.Process.exit 0


/-! ### Progress output of the checkpoint replay (`VED_S94_PROGRESS=tickMs`, diagnosis only)

`↓ vedMemProgress` is a wildcard pre-simproc that only counts (visits, heartbeats since the replay start, the simp state's step count, the head of the term
being visited, the time of the visit) and returns `.continue`: it never rewrites, so the simp path is the one without it (checked by the result DAG/tree and
the heartbeat total on the s150r checkpoint).  A monitor task with its own stop token (stopped in a `finally`) logs a line every `tickMs` ms:
elapsed, visits, visits/s of the interval, heartbeats (k), steps, RSS, time since the last visit, the current head and a few recent heads. -/

initialize progVisits : IO.Ref Nat ← IO.mkRef 0
initialize progHb : IO.Ref Nat ← IO.mkRef 0
initialize progHb0 : IO.Ref Nat ← IO.mkRef 0
initialize progSteps : IO.Ref Nat ← IO.mkRef 0
initialize progLastMs : IO.Ref Nat ← IO.mkRef 0
initialize progHead : IO.Ref String ← IO.mkRef "-"
initialize progRecent : IO.Ref (Array String) ← IO.mkRef #[]
/-- a node of a DAG listing: shared nodes (`ids`) are named `nK` unless `top`; instance and type arguments are left out -/
partial def s94DagStr (ids : Std.HashMap Lean.Expr Nat) (x : Lean.Expr) (top : Bool) : String :=
  match (if top then none else ids[x]?) with
  | some n => s!"n{n}"
  | none => match x with
    | .app .. =>
      let args := x.getAppArgs.filter fun a =>
        !(match a.getAppFn with
          | .const n _ => n == ``Nat || n == ``Bool || n == ``Int || n == ``BitVec || (n.components.getLast?.map (·.toString.startsWith "inst")).getD false
          | .sort .. => true | _ => false)
      s!"({s94Head x} {" ".intercalate (args.map (s94DagStr ids · false)).toList})"
    | .lam .. => "(fun …)"
    | .mdata _ b => s94DagStr ids b false
    | .fvar f => s!"{f.name}"
    | .lit (.natVal v) => s!"{v}"
    | .const n _ => n.toString
    | _ => s94Head x

/-- a depth-limited rendering (heads only; the raw `toString` of a stalled term can be exponentially large) -/
partial def progShallow (d : Nat) (e : Lean.Expr) : String :=
  if d == 0 then "…" else
  match e with
  | .app .. =>
    let args := e.getAppArgs.map (progShallow (d - 1))
    s!"({s94Head e} {" ".intercalate args.toList})"
  | .lam _ _ b _ => s!"(fun {progShallow (d - 1) b})"
  | .mdata _ b => progShallow d b
  | .fvar f => s!"{f.name}"
  | .lit (.natVal n) => s!"{n}"
  | .const n _ => n.toString
  | _ => s94Head e

/-- the last visited terms (the stall dump prints them raw when `sinceLastVisit` passes `VED_S94_STALL_MS`) -/
initialize progLastE : IO.Ref (Array Lean.Expr) ← IO.mkRef #[]
/-- the number of recent visited terms kept (3; more with `VED_S94_CAPTURE_AT`, for the ancestor search of the capture) -/
initialize progKeepRef : IO.Ref Nat ← IO.mkRef 3
initialize progDumped : IO.Ref Bool ← IO.mkRef false

initialize progCap : IO.Ref (Option (Lean.Expr × Lean.LocalContext × Lean.LocalInstances)) ← IO.mkRef none

open Lean Meta Simp in
simproc_decl vedMemProgress (_) := fun e => do
  let h := s94Head e
  let v ← progVisits.modifyGet fun v => (v + 1, v + 1)
  progHead.set h
  progLastMs.set (← IO.monoMsNow)
  progHb.set ((← IO.getNumHeartbeats) - (← progHb0.get))
  progSteps.set (← get).numSteps
  let keep ← progKeepRef.get
  progLastE.modify fun a => (a.push e).extract (a.size + 1 - keep) (a.size + 1)
  -- diagnosis: reset the diagnostics counters at visit `VED_S94_RESET_AT`, so that a refusal soon after shows only the counters of the stalled step
  if let some r := (← IO.getEnv "VED_S94_RESET_AT").bind String.toNat? then
    if v == r then
      modifyThe Meta.State fun s => { s with diag := {} }
      modify fun s => { s with diag := {} }
  -- diagnosis: at visit `VED_S94_CAPTURE_AT` keep the visited term and abort the simp (the replay then re-runs the simp on that term alone, traced)
  if let some r := (← IO.getEnv "VED_S94_CAPTURE_AT").bind String.toNat? then
    if v == r then
      progCap.set (some (e, ← getLCtx, ← getLocalInstances))
      throwError "S94 captured visit {v}"
  if v % 1000 == 0 then
    progRecent.modify fun a => (a.push h).extract (a.size + 1 - 8) (a.size + 1)
  return .continue

/-- the progress monitor: (stop token, task) -/
def progStart (tickMs : Nat) : IO (IO.Ref Bool × Task (Except IO.Error Unit)) := do
  progVisits.set 0; progHb.set 0; progHb0.set (← IO.getNumHeartbeats); progSteps.set 0
  let t0 ← IO.monoMsNow
  progLastMs.set t0; progHead.set "-"; progRecent.set #[]; progLastE.set #[]; progDumped.set false
  progKeepRef.set (if (← IO.getEnv "VED_S94_CAPTURE_AT").isSome then 400 else 3)
  let stallMs := ((← IO.getEnv "VED_S94_STALL_MS").bind String.toNat?)
  let stop ← IO.mkRef false
  let task ← IO.asTask (prio := .dedicated) do
    let mut waited := 0
    let mut k := 0
    let mut prevV := 0
    let mut prevT := t0
    while !(← stop.get) do
      IO.sleep 100
      waited := waited + 100
      if (← stop.get) then break
      if waited < tickMs then continue
      waited := 0
      k := k + 1
      let now ← IO.monoMsNow
      let v ← progVisits.get
      let rate := (v - prevV) * 1000 / (max 1 (now - prevT))
      prevV := v; prevT := now
      let rss ← try
          let st ← IO.FS.readFile "/proc/self/status"
          pure ((st.splitOn "\n").find? (·.startsWith "VmRSS") |>.getD "")
        catch _ => pure ""
      dbgLog s!"S94 progress {k} t={now - t0} ms visits={v} rate={rate}/s hb(k)={(← progHb.get) / 1000} steps={← progSteps.get} {(rss.replace "\t" " ").replace "  " " "} sinceLastVisit={now - (← progLastMs.get)} ms head={← progHead.get} recent={← progRecent.get}"
      if let some sm := stallMs then
        if now - (← progLastMs.get) ≥ sm && !(← progDumped.get) then
          progDumped.set true
          for e in ← progLastE.get do
            dbgLog s!"S94 stall term ({s94Head e}) dag={(Tools.VedU1WireShare.collectDag (fun _ => true) e).size} tree={Tools.VedU1Loop.treeSizeVal e}: {(progShallow 5 e).take 1800}"
          if (← IO.getEnv "VED_S94_STALL_EXIT").isSome then
            dbgLog "S94 stall exit"
            IO.Process.exit 3
  return (stop, task)

/-- stop the progress monitor and log the last counters -/
def progFinish (stop : IO.Ref Bool) (task : Task (Except IO.Error Unit)) : IO Unit := do
  stop.set true
  let _ ← IO.wait task
  dbgLog s!"S94 progress stop visits={← progVisits.get} hb(k)={(← progHb.get) / 1000} steps={← progSteps.get}"

open Lean Meta in
/-- realize the equations of the matchers reachable from `n` (project constants only, bounded depth) -/
partial def ckptRealize (seen : IO.Ref (Std.HashSet Name)) (n : Name) (depth : Nat) : MetaM Unit := do
  if depth == 0 || (← seen.get).contains n then return
  seen.modify (·.insert n)
  let some info := (← getEnv).find? n | return
  if (← Meta.isMatcher n) then
    try discard <| Lean.Meta.Match.getEquationsFor n; dbgLog s!"S94 replay: equations of {n} realized"
    catch ex => dbgLog s!"S94 replay: equations of {n} FAILED: {((← ex.toMessageData.toString).replace "\n" " ").take 200}"
  let mut cs : Array Name := #[]
  for e in [info.type] ++ (match info.value? with | some v => [v] | none => []) do
    cs := cs ++ (Tools.VedU1WireShare.collectDag (fun x => x.isConst) e).map (·.constName!)
  for c in cs do
    if (`Sparkle).isPrefixOf c || (`Tools).isPrefixOf c || (`Tests).isPrefixOf c || (`_private).isPrefixOf c then ckptRealize seen c (depth - 1)

open Lean Meta Elab Command Term in
elab "#ved_s94_ckpt_replay " d:str : command => do
  let dir := d.getString
  let rows := ((← IO.FS.readFile (dir ++ "/ckpt.txt")).splitOn "\n").filter (· ≠ "") |>.map (·.splitOn "\t")
  let mut args : Array (Bool × String × Bool × (Sum Nat Name)) := #[]
  let mut tab : Option (Name × Std.HashMap String Nat) := none
  for r in rows do
    match r with
    | "fv" :: pre :: ar :: [i] => args := args.push (true, pre, ar == "1", .inl i.toNat!)
    | "c" :: pre :: ar :: cs =>
      -- the counting probe is a diagnosis simproc (open gate at generation time), not part of the production simp set
      unless compsName cs == ``vedMemProbe do args := args.push (true, pre, ar == "1", .inr (compsName cs))
    | "tab" :: cs => tab := some (compsName cs, {})
    | ["w", k, v] => tab := tab.map fun (n, t) => (n, t.insert k v.toNat!)
    | _ => pure ()
  liftTermElabM do
    let ci ← getConstInfo `ved_ckpt.goal
    let tgtConsts : Array Name := (Tools.VedU1WireShare.collectDag (fun x => x.isConst) ci.type).map (·.constName!)
    -- the equations of the matchers that the simp unfolds are realized in the EMPTY local context (in the run they were realized by earlier stages;
    -- realized here inside the goal's context they fail the instances-transparency check of the context's `let` values)
    let seen ← IO.mkRef (({} : Std.HashSet Name))
    let mut roots : Array Name := tgtConsts
    for (_, _, _, a) in args do
      if let .inr n := a then roots := roots.push n
    for c in roots do ckptRealize seen c 6
    dbgLog s!"S94 replay: {(← seen.get).size} constants visited for matcher equations"
    let mut g := (← mkFreshExprMVar ci.type).mvarId!
    let mut k := 0
    -- the binder names of the context (the original user names: `s`, `hM<i>`), for the stage-95 checkpoint
    let mut binderNames : Array Name := #[]
    let mut tyW := ci.type
    repeat
      match tyW with
      | .forallE n _ b _ | .letE n _ _ b _ => binderNames := binderNames.push n; tyW := b
      | _ => break
    repeat
      unless (← g.getType).isForall || (← g.getType).isLet do break
      let (_, g') ← g.intro (Name.mkSimple s!"ck{k}")
      g := g'; k := k + 1
    let tgt ← instantiateMVars (← g.getType)
    dbgLog s!"S94 replay: {k} context entries, goal dag={(Tools.VedU1WireShare.collectDag (fun _ => true) tgt).size} tree={Tools.VedU1Loop.treeSizeVal tgt}"
    if (← IO.getEnv "VED_CKPT_CHECK").isSome then
      for tr in [TransparencyMode.default, .instances] do
        let r ← try g.withContext (withTransparency tr (do Meta.check tgt; pure "ok")) catch ex => pure ((← ex.toMessageData.toString).replace "\n" " " |>.take 400 |>.toString)
        dbgLog s!"S94 replay: Meta.check ({repr tr}) of the goal: {r}"
    let mut elems : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
    for (_, pre, ar, a) in args do
      let t : Term := match a with
        | .inl i => mkIdent (Name.mkSimple s!"ck{i}")
        | .inr n => mkCIdent n
      let st ← match pre.trimAscii.toString, ar with
        | "↓", false => `(Lean.Parser.Tactic.simpLemma| ↓ $t:term)
        | "↓", true => `(Lean.Parser.Tactic.simpLemma| ↓ ← $t:term)
        | _, false => `(Lean.Parser.Tactic.simpLemma| $t:term)
        | _, true => `(Lean.Parser.Tactic.simpLemma| ← $t:term)
      elems := elems.push st
    let prog? := ((← IO.getEnv "VED_S94_PROGRESS").bind String.toNat?)
    if prog?.isSome then
      elems := elems.push (← `(Lean.Parser.Tactic.simpLemma| ↓ $(mkCIdent ``vedMemProgress):term))
    let simp ← `(tactic| ved_loop_simp [$elems,*])
    let simp ← if (← IO.getEnv "VED_S94_ATOM").isSome then `(tactic| ved_s94_atom ($simp:tactic)) else pure simp
    let nic := Tools.VedMemS94Fix.ved.mem.s94NoIteCongr.get (← getOptions)
    let stx ← if nic then `(tactic| ved_s94_noitecongr ($simp:tactic)) else pure simp
    Tools.VedMemLoop.declWidthTab.set tab
    let mon ← match prog? with
      | some ms => do pure (some (← progStart (max ms 1000)))
      | none => pure none
    let t0 ← IO.monoMsNow
    let hb0 ← IO.getNumHeartbeats
    try
      let gs ← Tactic.run g (Tactic.evalTactic stx)
      let ms := (← IO.monoMsNow) - t0
      let mut sz := ""
      for g2 in gs do
        let e ← instantiateMVars (← g2.getType)
        sz := sz ++ s!" [dag={(Tools.VedU1WireShare.collectDag (fun _ => true) e).size} tree={Tools.VedU1Loop.treeSizeVal e}]"
      dbgLog s!"S94 replay: simp {if nic then "without" else "with"} ite_congr done ms={ms} hb(k)={((← IO.getNumHeartbeats) - hb0) / 1000} goals={gs.length}{sz}"
      logInfo m!"ckpt replay ok: ms={ms} goals={gs.length}"
      -- `VED_S95_OUT=DIR`: `ved_hstep_unify` (the rest of stage 94) and the stage-95 checkpoint of the one goal (`ckpt95.txt`, `VedCkpt.olean`), then the process ends
      if let some out := (← IO.getEnv "VED_S95_OUT") then
        let [g2] := gs | throwError "VED_S95_OUT: {gs.length} goals after the simp"
        let t1 ← IO.monoMsNow
        let hb1 ← IO.getNumHeartbeats
        let gs2 ← Tactic.run g2 (Tactic.evalTactic (← `(tactic| ved_hstep_unify)))
        dbgLog s!"S94 replay: ved_hstep_unify ms={(← IO.monoMsNow) - t1} hb(k)={((← IO.getNumHeartbeats) - hb1) / 1000} goals={gs2.length}"
        let [g3] := gs2 | throwError "VED_S95_OUT: {gs2.length} goals after ved_hstep_unify"
        let (ty, hmLine, spLine) ← g3.withContext do
          let tgt3 ← instantiateMVars (← g3.getType)
          let fvs : Array Expr := (← getLCtx).foldl (fun a d => if d.isImplementationDetail then a else a.push d.toExpr) #[]
          unless fvs.size == k do throwError "VED_S95_OUT: {fvs.size} context entries, expected {k}"
          let hms := (List.range 64).filterMap fun i => binderNames.findIdx? (· == Name.mkSimple s!"hM{i}")
          let some si := binderNames.findIdx? (· == `s) | throwError "VED_S95_OUT: no binder s"
          pure ((← instantiateMVars (← mkForallFVars fvs tgt3 (usedLetOnly := false))), "hm\t0\t" ++ "\t".intercalate (hms.map toString), s!"sp\t0\t{si}")
        if ty.hasFVar || ty.hasMVar || ty.hasLevelParam || ty.hasLevelMVar then throwError "VED_S95_OUT: goal still has fvars/mvars/level parameters"
        withTheReader Core.Context (fun c => { c with options := c.options.setBool `debug.skipKernelTC true }) do
          addDecl (.axiomDecl { name := `ved_ckpt95_goal0, levelParams := [], type := ty, isUnsafe := false })
        let mut lines : Array String := #["n\t1", hmLine, spLine]
        match tab with
        | some (mn, t) =>
          lines := lines.push ("tab\t" ++ "\t".intercalate (nameComps mn))
          for (kk, v) in t.toList do lines := lines.push s!"w\t{kk}\t{v}"
        | none => lines := lines.push "notab"
        IO.FS.createDirAll out
        IO.FS.writeFile (out ++ "/ckpt95.txt") ("\n".intercalate lines.toList ++ "\n")
        let md ← Lean.mkModuleData (← getEnv)
        let realized (n : Name) : Bool :=
          match n with
          | .str _ s => s == "splitter" || s == "eq_def" || s == "sunfold" || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
          | _ => false
        let keep := md.constants.filter (fun c => !realized c.name)
        let md' := { md with constNames := keep.map (·.name), constants := keep }
        Lean.saveModuleData (out ++ "/VedCkpt.olean") (← getEnv).mainModule md'
        dbgLog s!"S95 ckpt written to {out}: {md.constants.size} constants"
        IO.Process.exit 0
    catch ex =>
      dbgLog s!"S94 replay: FAILED ms={(← IO.monoMsNow) - t0}: {((← ex.toMessageData.toString).replace "\n" " ").take 600}"
      if let some (e, lctx, linst) := ← progCap.get then
       withLCtx lctx linst do
        -- diagnosis: the captured term alone, under a local budget (`VED_S94_CAP_HB` thousand heartbeats), traced
        let e ← instantiateMVars e
        dbgLog s!"S94 capture: dag={(Tools.VedU1WireShare.collectDag (fun _ => true) e).size} tree={Tools.VedU1Loop.treeSizeVal e} looseBVars={e.hasLooseBVars} head={s94Head e}"
        for fv in (Tools.VedU1WireShare.collectDag (fun x => x.isFVar) e).map (·.fvarId!) do
          let d ← fv.getDecl
          dbgLog s!"S94 capture fvar {fv.name} {d.userName} isLet={d.isLet} type={(progShallow 4 d.type).take 300} value={if d.isLet then (progShallow 4 d.value).take 300 else "-"}"
        let sub := ((Tools.VedU1WireShare.collectDag (fun x => x.isAppOf ``Sparkle.Core.Signal.Signal.val) e).extract 0 3)
        let withHb (n : Nat) (act : MetaM String) : MetaM String := do
          let hb ← IO.getNumHeartbeats
          withTheReader Core.Context (fun c => { c with maxHeartbeats := n * 1000, initHeartbeats := hb }) do
            tryCatchRuntimeEx act fun ex => do pure s!"EXN {((← ex.toMessageData.toString).replace "\n" " ").take 120}"
        for x in sub do
          for (nm, f) in [("whnfCore", fun (y : Lean.Expr) => Meta.whnfCore y), ("whnfR", fun y => Meta.whnfR y), ("whnf", fun y => Meta.whnf y)] do
            let t2 ← IO.monoMsNow
            let r ← withHb 200000 do
              let y ← f x
              pure s!"head={s94Head y} tree={Tools.VedU1Loop.treeSizeVal y}"
            dbgLog s!"S94 capture probe {nm} of Signal.val-app (tree={Tools.VedU1Loop.treeSizeVal x}): {r} ms={(← IO.monoMsNow) - t2}"
        let parts : List (String × Lean.Expr) :=
          if e.isAppOfArity ``And 2 && (e.appFn!.appArg!).isAppOfArity ``And 2 then
            let e12 := e.appFn!.appArg!
            [("E1", e12.appFn!.appArg!), ("E2", e12.appArg!), ("E1&E2", e12), ("E3", e.appArg!)]
          else []
        if (← IO.getEnv "VED_S94_TCTRACE").isSome then
          if let some (_, x) := parts[0]? then
            let _ ← withHb 300000 <| withOptions (fun o => ((o.setBool `trace.Meta.synthInstance true).setBool `trace.Meta.isDefEq true).setBool `trace.Meta.synthInstance.unusedInstances false) do
              let r ← Meta.synthInstance? (mkApp (mkConst ``Decidable) x)
              pure s!"{r.isSome}"
        for (nm, x) in parts ++ [("And (capture)", e), ("recent#2 Eq", (← progLastE.get).reverse[1]!)] do
          let t2 ← IO.monoMsNow
          let r ← withHb 300000 do
            let r ← Meta.synthInstance? (mkApp (mkConst ``Decidable) x)
            pure s!"{r.isSome}"
          dbgLog s!"S94 capture probe synthInstance (Decidable {nm}): {r} ms={(← IO.monoMsNow) - t2}"
        if e.isAppOfArity ``And 2 && (e.appFn!.appArg!).isAppOfArity ``And 2 then
          let e12 := e.appFn!.appArg!
          let e1 := e12.appFn!.appArg!
          let e2 := e12.appArg!
          let e3 := e.appArg!
          for (nm, a, b) in [("E1=?=E3", e1, e3), ("E2=?=E3", e2, e3), ("E1=?=E2", e1, e2)] do
            let t2 ← IO.monoMsNow
            let r ← withHb 300000 do
              let ok ← withReducible (Meta.isDefEq a b)
              pure s!"{ok}"
            dbgLog s!"S94 capture probe reducible isDefEq {nm} (trees {Tools.VedU1Loop.treeSizeVal a} {Tools.VedU1Loop.treeSizeVal b}): {r} ms={(← IO.monoMsNow) - t2}"
        if e.isAppOfArity ``And 2 then
          let e3 := e.appArg!
          let recent := (← progLastE.get).reverse
          let mut shown := 0
          for t in recent do
            let hasE3 := !(Tools.VedU1WireShare.collectDag (fun x => x == e3) t).isEmpty
            if shown < 8 || hasE3 then
              shown := shown + 1
              dbgLog s!"S94 capture recent ({s94Head t}) dag={(Tools.VedU1WireShare.collectDag (fun _ => true) t).size} tree={Tools.VedU1Loop.treeSizeVal t} containsE3={hasE3}: {(progShallow 4 t).take 500}"
            if shown > 40 then break
        let hbN := ((← IO.getEnv "VED_S94_CAP_HB").bind String.toNat?).getD 100000
        let hbL := Syntax.mkNumLit (toString hbN)
        let tr ← `(tactic| first | (set_option trace.Debug.Meta.Tactic.simp true in ved_budget $hbL ($simp:tactic)) | skip)
        let g2 := (← mkFreshExprMVar e).mvarId!
        let t1 ← IO.monoMsNow
        let gs ← Tactic.run g2 (Tactic.evalTactic tr)
        dbgLog s!"S94 capture: isolated simp done ms={(← IO.monoMsNow) - t1} goals={gs.length}"
        if let some hb2 := (← IO.getEnv "VED_S94_CAP2_HB").bind String.toNat? then
          let hbL2 := Syntax.mkNumLit (toString hb2)
          for v in ((← IO.getEnv "VED_S94_VARIANTS").getD "").splitOn "," do
            if v == "" then continue
            let inner ← `(tactic| ved_budget $hbL2 ($simp:tactic))
            let tr2 ← match v with
              | "sp" => `(tactic| set_option simprocs false in $inner:tactic)
              | "tr" => `(tactic| set_option trace.Meta.Tactic.simp true in set_option trace.Meta.synthInstance true in $inner:tactic)
              | _ => pure inner
            let g3 := (← mkFreshExprMVar e).mvarId!
            let t3 ← IO.monoMsNow
            let res ← try
                let gs3 ← Tactic.run g3 (Tactic.evalTactic tr2)
                let mut sz3 := ""
                for g4 in gs3 do
                  let r ← instantiateMVars (← g4.getType)
                  sz3 := sz3 ++ s!" [dag={(Tools.VedU1WireShare.collectDag (fun _ => true) r).size} tree={Tools.VedU1Loop.treeSizeVal r} head={s94Head r}]"
                pure s!"ok goals={gs3.length}{sz3}"
              catch ex => pure s!"FAIL {((← ex.toMessageData.toString).replace "\n" " ").take 160}"
            dbgLog s!"S94 capture variant {v}: ms={(← IO.monoMsNow) - t3} {res}"
       return
      throw ex
    finally
      Tools.VedMemLoop.declWidthTab.set none
      if let some (st, tk) := mon then progFinish st tk

open Lean Meta Elab Command Term in
/-- replay of the stage-97 checkpoint: `VED_S97_GOALS=a-b` (default all), `VED_S97_HB` (thousand heartbeats per goal; default the ambient budget) -/
elab "#ved_s94_ckpt97_replay " d:str : command => do
  let dir := d.getString
  let rows := ((← IO.FS.readFile (dir ++ "/ckpt97.txt")).splitOn "\n").filter (· ≠ "") |>.map (·.splitOn "\t")
  let mut nG := 0
  let mut hms : Std.HashMap Nat (List Nat) := {}
  for r in rows do
    match r with
    | ["n", k] => nG := k.toNat!
    | "hm" :: j :: ps => hms := hms.insert j.toNat! (ps.map String.toNat!)
    | _ => pure ()
  let (lo, hi) := match ((← IO.getEnv "VED_S97_GOALS").getD "").splitOn "-" with
    | [a, b] => (a.toNat!, b.toNat!)
    | [a] => if a == "" then (0, nG - 1) else (a.toNat!, a.toNat!)
    | _ => (0, nG - 1)
  let hbN? := (← IO.getEnv "VED_S97_HB").bind String.toNat?
  liftTermElabM do
    for j in [lo:hi+1] do
      let nm := Name.mkSimple s!"ved_ckpt97_goal{j}"
      let ci ← getConstInfo nm
      if j == lo then
        let seen ← IO.mkRef (({} : Std.HashSet Name))
        for c in (Tools.VedU1WireShare.collectDag (fun x => x.isConst) ci.type).map (·.constName!) do ckptRealize seen c 6
        dbgLog s!"S97 replay: {(← seen.get).size} constants visited for matcher equations"
      let mut g := (← mkFreshExprMVar ci.type).mvarId!
      let mut k := 0
      repeat
        unless (← g.getType).isForall || (← g.getType).isLet do break
        let (_, g') ← g.intro (Name.mkSimple s!"ck{k}")
        g := g'; k := k + 1
      let tgt ← instantiateMVars (← g.getType)
      dbgLog s!"S97 replay goal {j}: {k} context entries, goal dag={(Tools.VedU1WireShare.collectDag (fun _ => true) tgt).size} tree={Tools.VedU1Loop.treeSizeVal tgt}"
      let hs := (hms.getD j []).map fun i => mkIdent (Name.mkSimple s!"ck{i}")
      let mut peels : Array (TSyntax `tactic) := #[]
      for h in hs do peels := peels.push (← `(tactic| (ved_s97_peel $h:ident)))
      let mut alt : TSyntax `tactic := peels[0]!
      for c in peels.toList.drop 1 do alt ← `(tactic| first | ($alt:tactic) | ($c:tactic))
      if (← IO.getEnv "VED_S97_STEPS").isSome then
        -- diagnosis: the steps of the peel one by one, each under its own budget (`VED_S97_STEPHB` thousand heartbeats)
        let stepHb := ((← IO.getEnv "VED_S97_STEPHB").bind String.toNat?).getD 50000
        let tg ← instantiateMVars (← g.getType)
        g.withContext do
          let nArgs := tg.getAppNumArgs
          let mArr := tg.getArg! (nArgs - 1)
          dbgLog s!"S97 step goal {j}: head={s94Head tg} nargs={nArgs} memArray head={s94Head mArr.consumeMData} tree={Tools.VedU1Loop.treeSizeVal mArr}; args trees={(tg.getAppArgs.map Tools.VedU1Loop.treeSizeVal).toList}"
          let hbA ← IO.getNumHeartbeats
          let withB (act : MetaM String) : MetaM String :=
            withTheReader Core.Context (fun c => { c with maxHeartbeats := stepHb * 1000, initHeartbeats := hbA }) (tryCatchRuntimeEx act fun ex => do pure s!"EXN {((← ex.toMessageData.toString).replace "\n" " ").take 80}")
          for (h, i) in (hms.getD j []).zipIdx do
            if i > 2 then break
            let hd ← (mkIdent (Name.mkSimple s!"ck{h}")).getId |> fun n => pure n
            let some d := (← getLCtx).findFromUserName? hd | continue
            let t1 ← IO.monoMsNow
            let hb1 ← IO.getNumHeartbeats
            let r ← withB do
              let hb ← IO.getNumHeartbeats
              withTheReader Core.Context (fun c => { c with initHeartbeats := hb }) do
                let a ← withTransparency .default (Meta.isDefEq d.type tg)
                pure s!"isDefEq(hM_{i} type, goal)={a}"
            dbgLog s!"S97 step goal {j} exact-h{i}: {r} ms={(← IO.monoMsNow) - t1} hb(k)={((← IO.getNumHeartbeats) - hb1) / 1000} hType head={s94Head d.type} tree={Tools.VedU1Loop.treeSizeVal d.type}"
      if (← IO.getEnv "VED_S97_COUNT").isSome then
        -- diagnosis: the number of peel steps the memory array needs: ite = 1 + both branches (as a tree), update lambda = 1 + the inner array, other = 1
        let tg ← instantiateMVars (← g.getType)
        if tg.isAppOf ``Tools.VedMem.MemInv then
          let cache ← IO.mkRef (({} : Std.HashMap Lean.Expr Nat))
          let rec cnt (e : Lean.Expr) (fuel : Nat) : IO Nat := do
            match fuel with
            | 0 => return 0
            | fuel + 1 =>
            let e := e.consumeMData
            if let some v := (← cache.get)[e]? then return v
            let r ← if e.isAppOfArity ``ite 5 then
                pure ((← cnt (e.getArg! 3) fuel) + (← cnt (e.getArg! 4) fuel) + 1)
              else if e.isLambda then
                let body := (e.bindingBody!).bindingBody!
                if body.isAppOfArity ``ite 5 then
                  let els := body.getArg! 4
                  -- the else branch is `M nm i` (M = the application without its last two arguments)
                  if els.isApp && els.appFn!.isApp && !els.appFn!.appFn!.hasLooseBVars then pure ((← cnt els.appFn!.appFn! fuel) + 1) else pure 1
                else pure 1
              else pure 1
            cache.modify (·.insert e r)
            return r
          let steps ← cnt (tg.getArg! (tg.getAppNumArgs - 1)) 100000
          dbgLog s!"S97 count goal {j}: peel steps (tree count of the memory array) = {steps}"
      if (← IO.getEnv "VED_S97_WALK").isSome then
        -- diagnosis: the whole peel as a worklist over ALL branches (hypothesis = the one of the goal's name), the refine steps one at a time,
        -- each under its own budget (`VED_S97_STEPHB` thousand heartbeats); logs every step over 100 ms or 2M heartbeats and the totals
        let stepHb := ((← IO.getEnv "VED_S97_STEPHB").bind String.toNat?).getD 50000
        let mut work : Array MVarId := #[g]
        let mut steps := 0
        let mut sideGoals : Array String := #[]
        let mut leafs := 0
        let tStart ← IO.monoMsNow
        let hbStart ← IO.getNumHeartbeats
        let seenH ← IO.mkRef (({} : Std.HashSet UInt64))
        let walkMs := ((← IO.getEnv "VED_S97_WALKMS").bind String.toNat?).getD 100000000
        while !work.isEmpty && (← IO.monoMsNow) - tStart < walkMs do
          let cur := work.back!
          work := work.pop
          let tg ← instantiateMVars (← cur.getType)
          if !tg.isAppOf ``Tools.VedMem.MemInv then
            sideGoals := sideGoals.push s!"{s94Head tg}:{Tools.VedU1Loop.treeSizeVal tg}"
            continue
          let mArr := tg.getArg! (tg.getAppNumArgs - 1)
          let sh := s94Head mArr.consumeMData
          seenH.modify (·.insert (hash mArr))
          let cands : List (String × TSyntax `tactic) := [
            ("ite", ← `(tactic| (ved_mem_shape ite; refine Tools.VedMem.MemInv.ite (fun _ => ?_) (fun _ => ?_)))),
            ("other", ← `(tactic| (ved_mem_shape lam; refine Tools.VedMem.MemInv.other_leaf ?_ (by decide) _ _))),
            ("write", ← `(tactic| (ved_mem_shape lam; refine Tools.VedMem.MemInv.write_leaf ?_ ?_ ?_ ?_))),
            ("hold", ← `(tactic| (ved_mem_shape fvar; refine Tools.VedMem.MemInv.hold_leaf ?_ ?_)))]
          let mut done := false
          for (nm, tac) in cands do
            let t1 ← IO.monoMsNow
            let hb1 ← IO.getNumHeartbeats
            let res ← try
                withTheReader Core.Context (fun c => { c with maxHeartbeats := stepHb * 1000, initHeartbeats := hb1 }) (tryCatchRuntimeEx (do
                    let gs ← Tactic.run cur (Tactic.evalTactic tac)
                    pure (some gs)) fun _ => pure none)
              catch _ => pure none
            let ms := (← IO.monoMsNow) - t1
            let hbd := ((← IO.getNumHeartbeats) - hb1) / 1000
            if res.isSome && (ms > 100 || hbd > 2000) then dbgLog s!"S97 walk SLOW step {nm} shape={sh} ms={ms} hb(k)={hbd}"
            if let some gs := res then
              steps := steps + 1
              work := work ++ gs.reverse.toArray
              done := true
              break
          if !done then
            leafs := leafs + 1
            let okAny ← IO.mkRef false
            cur.withContext do
              for h in hms.getD j [] do
                let some d := (← getLCtx).findFromUserName? (Name.mkSimple s!"ck{h}") | continue
                let t1 ← IO.monoMsNow
                let hb1 ← IO.getNumHeartbeats
                let r ← withTheReader Core.Context (fun c => { c with maxHeartbeats := stepHb * 1000, initHeartbeats := hb1 }) (tryCatchRuntimeEx (do
                    let a ← Meta.isDefEq d.type tg
                    pure s!"{a}") fun ex => do pure s!"EXN {((← ex.toMessageData.toString).replace "\n" " ").take 60}")
                let ms := (← IO.monoMsNow) - t1
                if r == "true" then okAny.set true
                if (r != "false" && r != "true") || ms > 100 then dbgLog s!"S97 walk leaf exact ck{h}: {r} ms={ms}"
            if !(← okAny.get) then dbgLog s!"S97 walk leaf NO hypothesis accepted: shape={sh} trees={(tg.getAppArgs.map Tools.VedU1Loop.treeSizeVal).toList}"
        dbgLog s!"S97 walk goal {j} done (work left {work.size}, distinct memory arrays {(← seenH.get).size}): steps={steps} leaves={leafs} side goals={sideGoals.size} ({(sideGoals.toList.take 4)}) ms={(← IO.monoMsNow) - tStart} hb(k)={((← IO.getNumHeartbeats) - hbStart) / 1000}"
      let t0 ← IO.monoMsNow
      let hb0 ← IO.getNumHeartbeats
      -- `VED_S97_DAG` set: the DAG peel first (`ved.mem.s94PeelDag`'s tactic), the old peel as the fallback
      let pickT : TSyntax `tactic ← if (← IO.getEnv "VED_S97_DAG") == some "only" then `(tactic| (first | (ved_mem_peel_dag $[$hs.toArray]*) | skip)) else if (← IO.getEnv "VED_S97_DAG").isSome then `(tactic| first | (ved_mem_peel_dag $[$hs.toArray]*) | ($alt:tactic)) else pure alt
      let run : TermElabM String := do
        try
          let gs ← Tactic.run g (Tactic.evalTactic (← if (← IO.getEnv "VED_S97_DAG") == some "only" then `(tactic| (ved_mem_peel_dag $[$hs.toArray]*)) else `(tactic| try $pickT:tactic)))
          let mut shapes : Array String := #[]
          for sg in gs do
            if (← IO.getEnv "VED_S97_SHAPES").isNone then continue
            let ty ← instantiateMVars (← sg.getType)
            let nctx ← sg.withContext do pure (← getLCtx).decls.size
            shapes := shapes.push s!"{ty.getAppFn.constName?.getD `_}/{ty.getAppNumArgs}/{Tools.VedU1Loop.treeSizeVal ty}/h{ty.hash}/ctx{nctx}"
          pure s!"ok goals={gs.length} shapes={(shapes.toList.take 12)} hits={← Tools.VedMemS94Peel.peelDagHits.get}"
        catch ex => pure s!"FAILED {((← ex.toMessageData.toString).replace "\n" " ").take 300}"
      let res ← match hbN? with
        | some n => withTheReader Core.Context (fun c => { c with maxHeartbeats := n * 1000, initHeartbeats := hb0 }) (tryCatchRuntimeEx run fun ex => do pure s!"EXN {((← ex.toMessageData.toString).replace "\n" " ").take 200}")
        | none => run
      dbgLog s!"S97 replay goal {j}: {res} ms={(← IO.monoMsNow) - t0} hb(k)={((← IO.getNumHeartbeats) - hb0) / 1000}"

open Tools.VedU1WireShare in
/-- diagnosis: `ved_loop_gen_mem s` with a clock per sub-step (loops preamble, `hasValAt`, `mkAppM`, `generalizeDag`, `rcases`, the Bool `cases`), one summary line per loop:
ms and heartbeats (thousand) of each sub-step, goals before / after.  The same steps in the same order as `ved_loop_gen_mem`. -/
def s94Clock {α : Type} (acc : IO.Ref (Nat × Nat)) (act : TacticM α) : TacticM α := do
  let t0 ← IO.monoMsNow
  let h0 ← IO.getNumHeartbeats
  let r ← act
  let t1 ← IO.monoMsNow
  let h1 ← IO.getNumHeartbeats
  acc.modify fun (m, h) => (m + (t1 - t0), h + (h1 - h0) / 1000)
  return r

elab "ved_loop_gen_mem_prof " s:ident : tactic => withMainContext do
  let sE ← elabTerm s.raw none
  let tPre ← IO.monoMsNow
  let hPre ← IO.getNumHeartbeats
  let mut loops : Array Expr := #[]
  for g in ← getGoals do
    for l in ← goalLoops g do
      unless loops.contains l do loops := loops.push l
  dbgLog s!"genprof: {loops.size} loops in {(← getGoals).length} goals, preamble ms={(← IO.monoMsNow) - tPre} hb(k)={((← IO.getNumHeartbeats) - hPre) / 1000}"
  for j in [0:loops.size] do
    let aHas ← IO.mkRef (0, 0); let aMk ← IO.mkRef (0, 0); let aGen ← IO.mkRef (0, 0); let aRc ← IO.mkRef (0, 0); let aCs ← IO.mkRef (0, 0)
    let tL ← IO.monoMsNow
    let nBefore := (← getGoals).length
    let some α := loops[j]!.getAppArgs[1]? | throwError "ved_loop_gen_mem_prof: malformed Signal.loop"
    let bare := !(← whnfR α).isAppOf ``Prod
    let n := (← Tools.VedU1Loop.stateComps α).length
    let X := mkIdent (Name.mkSimple s!"ved_X{j}")
    let xs := (List.range (if bare then 1 else n + 1)).toArray.map fun i => mkIdent (Name.mkSimple s!"ved_x{j}_{i}")
    let pats ← xs.mapM fun x => `(Lean.Parser.Tactic.rcasesPatLo| $x:ident)
    let mut gsOut : List MVarId := []
    let mut nHit := 0
    for g in ← getGoals do
      setGoals [g]
      unless (← s94Clock aHas (hasValAt g loops[j]! sE)) do
        gsOut := gsOut ++ [g]
        continue
      nHit := nHit + 1
      let v ← s94Clock aMk (g.withContext <| mkAppM ``Sparkle.Core.Signal.Signal.val #[loops[j]!, sE])
      s94Clock aGen (Tools.VedU1WireShare.generalizeDag v (if bare then Name.mkSimple s!"ved_x{j}_0" else X.getId))
      unless bare do s94Clock aRc (evalTactic (← `(tactic| all_goals rcases $X:ident with ⟨$pats,*⟩)))
      for x in xs do
        let some d := (← withMainContext getLCtx).findFromUserName? x.getId | continue
        if (← whnfR d.type).isConstOf ``Bool && (← IO.getEnv "VED_S100_NOSPLIT").isNone then
          s94Clock aCs (evalTactic (← `(tactic| all_goals cases $x:ident)))
      gsOut := gsOut ++ (← getGoals)
    setGoals gsOut
    let f (a : IO.Ref (Nat × Nat)) : IO String := do let (m, h) ← a.get; pure s!"{m}ms/{h}k"
    dbgLog s!"genprof loop {j}: goals {nBefore} -> {gsOut.length} (with the loop: {nHit}), bool comps={(← xs.filterM fun _ => pure true).size}, total ms={(← IO.monoMsNow) - tL}: hasValAt {← f aHas} mkAppM {← f aMk} generalizeDag {← f aGen} rcases {← f aRc} cases {← f aCs}"

open Lean Meta Elab Command Term in
/-- replay of the stage-100 checkpoint: `ved_loop_gen_mem ck<s>` (the step of the script after stamp 100).  `VED_S100_GOALS` (default all; `a-b` or a comma list
of numbers and ranges), `VED_S100_HB` (thousand heartbeats per goal / per run; default the ambient budget), `VED_S100_MODE=single` (default: every chosen goal alone,
one line each with ms and heartbeats) or `all` (the chosen goals together, as the script does: one `ved_loop_gen_mem`).  Each line ends with the shape
of the result (goals, tree total / max, as `ved_stamp`) so that it can be compared with the in-line run's next stamp. -/
elab "#ved_s94_ckpt100_replay " d:str : command => do
  let dir := d.getString
  let rows := ((← IO.FS.readFile (dir ++ "/ckpt100.txt")).splitOn "\n").filter (· ≠ "") |>.map (·.splitOn "\t")
  let mut nG := 0
  let mut sps : Std.HashMap Nat Nat := {}
  let mut kss : Std.HashMap Nat (List String) := {}
  for r in rows do
    match r with
    | ["n", k] => nG := k.toNat!
    | ["sp", j, i] => sps := sps.insert j.toNat! i.toNat!
    | "ks" :: j :: ks => kss := kss.insert j.toNat! ks
    | _ => pure ()
  let mut chosen : Array Nat := #[]
  match (← IO.getEnv "VED_S100_GOALS") with
  | none => chosen := (List.range nG).toArray
  | some str =>
    for w in str.splitOn "," do
      match w.splitOn "-" with
      | [a, b] => for i in [a.toNat!:b.toNat!+1] do chosen := chosen.push i
      | [a] => if a != "" then chosen := chosen.push a.toNat!
      | _ => pure ()
  let hbN? := (← IO.getEnv "VED_S100_HB").bind String.toNat?
  let single := (← IO.getEnv "VED_S100_MODE") != some "all"
  liftTermElabM do
    let seen ← IO.mkRef (({} : Std.HashSet Name))
    let sharedFv ← IO.mkRef (({} : Std.HashMap String (FVarId × Expr × Option Expr)))
    let mut mvs : Array (Nat × MVarId × Name) := #[]
    for j in chosen do
      let ci ← getConstInfo (Name.mkSimple s!"ved_ckpt100_goal{j}")
      if mvs.isEmpty then
        for c in (Tools.VedU1WireShare.collectDag (fun x => x.isConst) ci.type).map (·.constName!) do ckptRealize seen c 6
        dbgLog s!"S100 replay: {(← seen.get).size} constants visited for matcher equations"
      -- the goal's context is built from SHARED fvars (the original fvarId names: goals of one run share their common prefix, as the loops they
      -- contain do), so that `ved_loop_gen_mem` sees the same loops as in the script; the user name of a hypothesis is `ck<original fvarId>`
      let keys := (kss.getD j []).toArray
      let mut lctx : LocalContext := {}
      let mut ty := ci.type
      let mut k := 0
      let mut sName : Name := .anonymous
      repeat
        let (dom, val?, body) ← match ty with
          | .forallE _ d b _ => pure (d, (none : Option Expr), b)
          | .letE _ d v b _ => pure (d, some v, b)
          | _ => pure (ty, none, ty)
        unless ty.isForall || ty.isLet do break
        let key := keys[k]!
        let nm := Name.mkSimple s!"ck{key}"
        if k == sps.getD j 0 then sName := nm
        let fv ← match (← sharedFv.get).get? key with
          | some (id, _, _) => pure id
          | none =>
            let id ← mkFreshFVarId
            sharedFv.modify (·.insert key (id, dom, val?))
            pure id
        let (_, dom0, val0) := ((← sharedFv.get).get! key)
        lctx := match val? with
          | none => lctx.mkLocalDecl fv nm dom0
          | some _ => lctx.mkLetDecl fv nm dom0 (val0.getD dom0)
        ty := body.instantiate1 (.fvar fv)
        k := k + 1
      let g := (← mkFreshExprMVarAt lctx #[] ty).mvarId!
      mvs := mvs.push (j, g, sName)
    let shape (gs : List MVarId) : MetaM String := do
      let mut szs : Array Nat := #[]
      for g in gs do
        szs := szs.push (← g.withContext do return Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← g.getType)))
      pure s!"goals={gs.length} tree: total={szs.foldl (· + ·) 0} max={szs.foldl max 0}"
    let runOn (label : String) (items : Array (Nat × MVarId × Name)) : TermElabM Unit := do
      let some (_, g0, s0) := items[0]? | return
      let t0 ← IO.monoMsNow
      let hb0 ← IO.getNumHeartbeats
      let run : TermElabM String := do
        try
          let gs ← Tactic.run g0 (do
            -- all chosen goals open at once (mode `all`), the first one's `s`
            Tactic.setGoals (items.toList.map (·.2.1))
            if (← IO.getEnv "VED_S100_PROF").isSome then Tactic.evalTactic (← `(tactic| ved_loop_gen_mem_prof $(mkIdent s0))) else Tactic.evalTactic (← `(tactic| ved_loop_gen_mem $(mkIdent s0))))
          pure s!"ok {← shape gs}"
        catch ex => pure s!"FAILED {((← ex.toMessageData.toString).replace "\n" " ").take 300}"
      let res ← match hbN? with
        | some n => withTheReader Core.Context (fun c => { c with maxHeartbeats := n * 1000, initHeartbeats := hb0 }) (tryCatchRuntimeEx run fun ex => do pure s!"EXN {((← ex.toMessageData.toString).replace "\n" " ").take 200}")
        | none => run
      dbgLog s!"S100 replay {label}: {res} ms={(← IO.monoMsNow) - t0} hb(k)={((← IO.getNumHeartbeats) - hb0) / 1000}"
    if single then
      for it in mvs do
        let tgt ← instantiateMVars (← it.2.1.getType)
        dbgLog s!"S100 goal {it.1}: tree={Tools.VedU1Loop.treeSizeVal tgt} dag={(Tools.VedU1WireShare.collectDag (fun _ => true) tgt).size}"
        runOn s!"goal {it.1}" #[it]
    else
      runOn s!"all {mvs.size} goals" mvs


open Lean Meta Elab Command Term Tools.VedU1WireShare in
/-- replay of the stage-95 checkpoint (`VED_S95_OUT` of `#ved_s94_ckpt_replay`): the ONE goal after `ved_hstep_unify`.  It runs the steps of the script from stamp 95
on, one step at a time, each with a line (ms, heartbeats (k), goals, tree total / max, and how many goals still contain a loop value `(loop).val s` in the target or a
hypothesis).  `VED_S95_MODE`: `old` (default; the script's steps with `ved_loop_gen_mem s` at the end), `once` (`ved_loop_gen_once s` right after stamp 95,
`ved_loop_gen_resid s` at the end), `onceLate` (as `once`, but the generalisation after the stage-99 simp, before the split is not possible there: runs it at the
stamp-96 goal-count 96, i.e. after `And.intro`, single goal is not given: only for the occurrence counts).  `VED_S95_UPTO=k` (stop after step k, k = 95, 951 refine, 96, 97, 98, 99, 991 dsimp, 100). -/
elab "#ved_s95_replay " d:str : command => do
  let dir := d.getString
  let rows := ((← IO.FS.readFile (dir ++ "/ckpt95.txt")).splitOn "\n").filter (· ≠ "") |>.map (·.splitOn "\t")
  let mut hms : List Nat := []
  let mut sp := 0
  let mut tab : Option (Name × Std.HashMap String Nat) := none
  for r in rows do
    match r with
    | "hm" :: _ :: ps => hms := ps.map String.toNat!
    | ["sp", _, i] => sp := i.toNat!
    | "tab" :: cs => tab := some (compsName cs, {})
    | ["w", k, v] => tab := tab.map fun (n, t) => (n, t.insert k v.toNat!)
    | _ => pure ()
  let mode := (← IO.getEnv "VED_S95_MODE").getD "old"
  let upto := ((← IO.getEnv "VED_S95_UPTO").bind String.toNat?).getD 100
  -- `VED_S95_LOG=FILE`: the replay's own lines go to FILE (so that `VED_DUMP_DIR`, which makes the tail's tactics dump their goals, can stay unset)
  let s95lg : String → IO Unit := fun msg => do
    if let some f ← IO.getEnv "VED_S95_LOG" then
      let h ← IO.FS.Handle.mk f .append
      h.putStrLn msg
    else dbgLog msg
  liftTermElabM do
    let dbgLog := s95lg
    dbgLog "S95 replay: start"
    let ci ← getConstInfo `ved_ckpt95_goal0
    dbgLog "S95 replay: constant found"
    let seen ← IO.mkRef (({} : Std.HashSet Name))
    let cs95 := (Tools.VedU1WireShare.collectDag (fun x => x.isConst) ci.type).map (·.constName!)
    dbgLog s!"S95 replay: {cs95.size} constants in the goal type"
    for c in cs95 do ckptRealize seen c 6
    dbgLog s!"S95 replay: {(← seen.get).size} constants visited for matcher equations"
    let mut g := (← mkFreshExprMVar ci.type).mvarId!
    let mut k := 0
    repeat
      unless (← g.getType).isForall || (← g.getType).isLet do break
      let (_, g') ← g.intro (Name.mkSimple s!"ck{k}")
      g := g'; k := k + 1
    let sId := mkIdent (Name.mkSimple s!"ck{sp}")
    -- the memory invariants: the hypotheses of type `MemInv ..`, in context order (the stored positions of `hM<i>` are not reliable here)
    let hs : Array (TSyntax `ident) ← g.withContext do
      let mut a : Array (TSyntax `ident) := #[]
      for d in ← getLCtx do
        unless d.isImplementationDetail do
          if (← instantiateMVars d.type).isAppOf ``Tools.VedMem.MemInv then a := a.push (mkIdent d.userName)
      pure a
    dbgLog s!"S95 replay: {hs.size} MemInv hypotheses (stored hm positions {hms.length})"
    Tools.VedMemLoop.declWidthTab.set tab
    let sE ← g.withContext do elabTerm sId none
    let isV := fun (e : Expr) => e.isAppOfArity ``Sparkle.Core.Signal.Signal.val 4 && (e.getArg! 2).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 && e.getArg! 3 == sE
    -- (goals with a loop value, distinct loop-value terms) over all goals; each distinct type scanned once
    let resid (gs : List MVarId) : MetaM String := do
      let memo ← IO.mkRef (({} : Std.HashMap Expr (Array Expr)))
      let scan (e : Expr) : MetaM (Array Expr) := do
        let e ← instantiateMVars e
        if let some r := (← memo.get)[e]? then return r
        let r := collectDag isV e
        memo.modify (·.insert e r)
        return r
      let mut nGoals := 0
      let mut all : Array Expr := #[]
      for g in gs do
        let found ← g.withContext do
          let mut f : Array Expr := ← scan (← g.getType)
          for d in ← getLCtx do
            unless d.isImplementationDetail do f := f ++ (← scan d.type)
          pure f
        unless found.isEmpty do nGoals := nGoals + 1
        for x in found do unless all.contains x do all := all.push x
      pure s!"goals with a loop value={nGoals} distinct loop values={all.size}"
    let shape (gs : List MVarId) : MetaM String := do
      let mut szs : Array Nat := #[]
      for g in gs do
        szs := szs.push (← g.withContext do return Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← g.getType)))
      pure s!"goals={gs.length} tree: total={szs.foldl (· + ·) 0} max={szs.foldl max 0}"
    let opts ← getOptions
    -- the stage-99 simp set of the script (`fzs.push mcr`)
    let mut r99 : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[
      ← `(Lean.Parser.Tactic.simpLemma| ↓ $(mkCIdent ``Tools.VedMemLoop.vedMemLoopFreeze):term),
      ← `(Lean.Parser.Tactic.simpLemma| ↓ $(mkCIdent ``Tools.VedMemLoop.vedDeclWidth):term),
      ← `(Lean.Parser.Tactic.simpLemma| ↓ $(mkCIdent ``Tools.VedMemLoop.vedDeclWidth1):term),
      ← `(Lean.Parser.Tactic.simpLemma| ↓ $(mkCIdent ``Tools.VedMemLoop.vedBindStrictO):term),
      ← `(Lean.Parser.Tactic.simpLemma| ↓ $(mkCIdent ``Tools.VedMemLoop.vedBindStrictB):term)]
    if Tools.VedMemLoop.ved.mem.s94EnvFreeze.get opts then
      r99 := r99.push (← `(Lean.Parser.Tactic.simpLemma| ↓ $(mkCIdent ``Tools.VedMemLoop.vedEnvFreeze):term))
    r99 := r99.push (← `(Lean.Parser.Tactic.simpLemma| Sparkle.Core.Signal.Signal.memoryComboRead_val))
    let mut peels : Array (TSyntax `tactic) := #[]
    for h in hs do peels := peels.push (← `(tactic| (ved_s97_peel $h:ident)))
    let mut peelAlt : TSyntax `tactic := peels[0]!
    for c in peels.toList.drop 1 do peelAlt ← `(tactic| first | ($peelAlt:tactic) | ($c:tactic))
    if Tools.VedMemS94Peel.ved.mem.s94PeelDag.get opts then
      peelAlt ← `(tactic| first | (ved_mem_peel_dag $[$hs]*) | ($peelAlt:tactic))
    let once := mode == "once" || mode == "once2"
    -- `once2`: the stage-99 simp (`memoryComboRead_val`, which creates new loop values) runs on the shared goal before the generalisation
    let genOnceT ← if mode == "once2" then `(tactic| first | ((try (ved_loop_simp [$r99,*])); ved_loop_gen_once $sId) | skip)
      else if once then `(tactic| first | ved_loop_gen_once $sId | skip) else `(tactic| skip)
    let genLastT ← if once then `(tactic| ved_loop_gen_resid $sId) else `(tactic| ved_loop_gen_mem $sId)
    let steps : List (Nat × String × TSyntax `tactic) := [
      (95, "gen_once", genOnceT),
      (951, "refine", ← `(tactic| all_goals refine ⟨_, _, _, ⟨rfl, rfl, rfl⟩, ?_⟩)),
      (96, "and_intro", ← `(tactic| all_goals (try (repeat' apply And.intro)))),
      (97, "peel", ← `(tactic| all_goals (try $peelAlt:tactic))),
      (99, "if_read_simp", ← `(tactic| ved_if_read (ved_loop_simp [$r99,*]))),
      (991, "dsimp_goals", ← `(tactic| ved_dsimp_goals)),
      (100, if once then "gen_resid" else "gen_mem", genLastT)]
    let stepNo (n : Nat) : Nat := match n with | 951 => 95 | 991 => 99 | n => n
    let mut cur : List MVarId := [g]
    dbgLog s!"S95 replay mode={mode}: start {← shape cur}; {← resid cur}"
    let tAll ← IO.monoMsNow
    let hbAll ← IO.getNumHeartbeats
    let mut res0 := "ok"
    for (no, name, tac) in steps do
      if stepNo no > upto then break
      let t0 ← IO.monoMsNow
      let hb0 ← IO.getNumHeartbeats
      -- `VED_S95_PEELDBG`: the DAG peel alone on each MemInv goal (error text, ms, heartbeats), the first goals only; the goals stay as they are
      if no == 97 && (← IO.getEnv "VED_S95_PEELDBG").isSome then
        let mut shown := 0
        for gq in cur do
          let tg ← instantiateMVars (← gq.getType)
          unless tg.isAppOf ``Tools.VedMem.MemInv do continue
          if shown ≥ 4 then break
          shown := shown + 1
          let t1 ← IO.monoMsNow
          let hb1 ← IO.getNumHeartbeats
          let r ← try
              withTheReader Core.Context (fun c => { c with maxHeartbeats := 300000000, initHeartbeats := hb1 }) do
                let gs ← Tactic.run gq (Tactic.evalTactic (← `(tactic| ved_mem_peel_dag $[$hs]*)))
                pure s!"ok goals={gs.length}"
            catch ex => pure s!"FAILED {((← ex.toMessageData.toString).replace "\n" " ").take 500}"
          if shown ≤ 2 then
            gq.withContext do
              for h in hs do
                let some d := (← getLCtx).findFromUserName? h.getId | continue
                let ht ← instantiateMVars d.type
                let n := min ht.getAppNumArgs tg.getAppNumArgs
                let mut diff : List String := []
                for i in [0:n] do
                  let a1 := ht.getArg! i
                  let a2 := tg.getArg! i
                  unless a1 == a2 do
                    diff := diff ++ [s!"#{i}: hyp tree={Tools.VedU1Loop.treeSizeVal a1} goal tree={Tools.VedU1Loop.treeSizeVal a2} heads {s94Head a1}/{s94Head a2} {(progShallow 3 a1).take 160} || {(progShallow 3 a2).take 160}"]
                dbgLog s!"S95 peeldbg hyp {h.getId}: head {s94Head ht} nargs={ht.getAppNumArgs}/{tg.getAppNumArgs} differing args: {diff}"
          dbgLog s!"S95 peeldbg MemInv goal: {r} ms={(← IO.monoMsNow) - t1} hb(k)={((← IO.getNumHeartbeats) - hb1) / 1000} args trees={(tg.getAppArgs.map Tools.VedU1Loop.treeSizeVal).toList}"
        break
      let res ← try
          let gs ← Tactic.run cur.head! (do Tactic.setGoals cur; Tactic.evalTactic tac)
          cur := gs
          pure "ok"
        catch ex => pure s!"FAILED {((← ex.toMessageData.toString).replace "\n" " ").take 400}"
      dbgLog s!"S95 step {no} {name}: {res} ms={(← IO.monoMsNow) - t0} hb(k)={((← IO.getNumHeartbeats) - hb0) / 1000}; {← shape cur}; {← resid cur}"
      if res != "ok" then res0 := res; break
    -- `VED_S95_TAIL=FILE` (with `VED_S95_ARGS=DIR`, the stage-94 checkpoint directory): the tail of the script after stamp 100, one step per line of FILE
    -- (`name TAB tactic`, parsed at run time; the line `@EX2SIMP` stands for the first tail simp `ved_loop_simp [O, M, B, .., ex2F]`, whose arguments are those
    -- of the stage-94 simp (`DIR/ckpt.txt`) without the first 15 + the probe, plus `hrst`); each step with ms, heartbeats, goals and tree sizes, as the steps above
    if res0 == "ok" && (upto ≥ 100 || (← IO.getEnv "VED_S95_NAMES").isSome) then
     if let some tf := (← IO.getEnv "VED_S95_TAIL") then
      let argDir := (← IO.getEnv "VED_S95_ARGS").getD ""
      let arows := ((← IO.FS.readFile (argDir ++ "/ckpt.txt")).splitOn "\n").filter (· ≠ "") |>.map (·.splitOn "\t")
      let mut args : Array (String × Bool × (Sum Nat Name)) := #[]
      for r in arows do
        match r with
        | "fv" :: pre :: ar :: [i] => args := args.push (pre.trimAscii.toString, ar == "1", .inl i.toNat!)
        | "c" :: pre :: ar :: cs =>
          unless compsName cs == ``vedMemProbe do args := args.push (pre.trimAscii.toString, ar == "1", .inr (compsName cs))
        | _ => pure ()
      let mut binderNames : Array Name := #[]
      let mut tyW := ci.type
      repeat
        match tyW with
        | .forallE n _ b _ | .letE n _ _ b _ => binderNames := binderNames.push n; tyW := b
        | _ => break
      -- the binders of the stage-95 goal are named `ck<i>` with i the position in the STAGE-94 context (the stage-94 replay introduced them so), while the
      -- replay above names them by their position here: `posOf i` is the position of the binder `ck<i>`
      let posOf (i : Nat) : Nat := (binderNames.findIdx? (· == Name.mkSimple s!"ck{i}")).getD i
      args := args.map fun (a, b, x) => (a, b, match x with | .inl i => .inl (posOf i) | y => y)
      dbgLog s!"S95 tail: binders {binderNames.toList.zipIdx.map fun (n, i) => s!"{i}:{n}"}"
      if (← IO.getEnv "VED_S95_NAMES").isSome then
        -- the context entries that are not simp arguments of the stage-94 simp: their position, name and a truncated type
        let used := args.filterMap fun (_, _, x) => match x with | .inl i => some i | _ => none
        g.withContext do
          for d in ← getLCtx do
            unless d.isImplementationDetail do
              let nm := d.userName.toString
              let i := (nm.drop 2).toNat!
              unless used.contains i do
                let ty ← instantiateMVars d.type
                unless ty.isAppOf ``Tools.VedMem.MemInv do
                  dbgLog s!"S95 names: {nm} : {((← ppExpr ty).pretty.replace "\n" " ").take 200}"
        return
      let some hrstI := (← IO.getEnv "VED_S95_HRST").bind String.toNat? | throwError "S95 tail: VED_S95_HRST (position of hrst) not set"
      let mkLem (a : String × Bool × Sum Nat Name) : TermElabM (TSyntax ``Lean.Parser.Tactic.simpLemma) := do
        let (pre, ar, x) := a
        let t : Term := match x with
          | .inl i => mkIdent (Name.mkSimple s!"ck{i}")
          | .inr n => mkCIdent n
        match pre, ar with
        | "↓", false => `(Lean.Parser.Tactic.simpLemma| ↓ $t:term)
        | "↓", true => `(Lean.Parser.Tactic.simpLemma| ↓ ← $t:term)
        | _, false => `(Lean.Parser.Tactic.simpLemma| $t:term)
        | _, true => `(Lean.Parser.Tactic.simpLemma| ← $t:term)
      let mut ex2 : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
      for a in args.extract 0 9 do ex2 := ex2.push (← mkLem a)
      for a in args.extract 15 args.size do ex2 := ex2.push (← mkLem a)
      ex2 := ex2.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent (Name.mkSimple s!"ck{hrstI}")):term))
      dbgLog s!"S95 tail: {ex2.size} simp arguments, hrst = ck{hrstI}"
      let tailRows := ((← IO.FS.readFile tf).splitOn "\n").filter (· ≠ "") |>.map (·.splitOn "\t")
      let mut perGoal := false
      for row in tailRows do
        let [name, txt] := row | continue
        let tac : TSyntax `tactic ← if txt == "@EX2SIMP" then `(tactic| all_goals (try ved_loop_simp [$ex2,*])) else
          match Parser.runParserCategory (← getEnv) `tactic txt with
          | .ok st => pure ⟨st⟩
          | .error e => throwError "S95 tail: cannot parse step {name}: {e}"
        let t0 ← IO.monoMsNow
        let hb0 ← IO.getNumHeartbeats
        -- `VED_S95_PERGOAL=step`: from that step on every step runs goal by goal, each under `VED_S95_GOALHB` thousand heartbeats (default 30000), one line per goal
        -- (ms, heartbeats, goals out, process RSS in MB); a failing goal stays as it is
        if name == (← IO.getEnv "VED_S95_PERGOAL").getD "" then perGoal := true
        let res ← if perGoal then do
            let cap := ((← IO.getEnv "VED_S95_GOALHB").bind String.toNat?).getD 30000
            let mut outG : List MVarId := []
            let mut nFail := 0
            let mut i := 0
            for gq in cur do
              let t1 ← IO.monoMsNow
              let hb1 ← IO.getNumHeartbeats
              dbgLog s!"S95 tail {name} goal {i}: start tree={Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← gq.getType))} ctx={(← gq.withContext getLCtx).decls.size}"
              let (gsO, r) : Option (List MVarId) × String ← tryCatchRuntimeEx
                (do
                  let gs ← withTheReader Core.Context (fun c => { c with maxHeartbeats := cap * 1000, initHeartbeats := hb1 }) do
                    Tactic.run gq (Tactic.evalTactic tac)
                  pure (some gs, s!"ok out={gs.length}"))
                (fun ex => do pure (none, s!"FAILED {((← ex.toMessageData.toString).replace "\n" " ").take 200}"))
              match gsO with
              | some gs => outG := outG ++ gs
              | none => outG := outG ++ [gq]; nFail := nFail + 1
              let rss := ((← IO.FS.readFile "/proc/self/status").splitOn "\n").find? (·.startsWith "VmRSS") |>.getD ""
              let ms1 := (← IO.monoMsNow) - t1
              let hbk := ((← IO.getNumHeartbeats) - hb1) / 1000
              if i < 8 || ms1 > 3000 || r.startsWith "FAILED" then
                dbgLog s!"S95 tail {name} goal {i}: {r} ms={ms1} hb(k)={hbk} {rss.replace " " ""}"
              i := i + 1
            cur := outG
            pure s!"ok (per goal; {nFail} failed)"
          else try
            let gs ← Tactic.run cur.head! (do Tactic.setGoals cur; Tactic.evalTactic tac)
            cur := gs
            pure "ok"
          catch ex => pure s!"FAILED {((← ex.toMessageData.toString).replace "\n" " ").take 400}"
        dbgLog s!"S95 tail {name}: {res} ms={(← IO.monoMsNow) - t0} hb(k)={((← IO.getNumHeartbeats) - hb0) / 1000}; {← shape cur}; {← resid cur}"
        -- `VED_S95_CLASSIFY=step`: after that tail step, one line per goal (tree, DAG nodes, nodes only in this goal, free variables, shallow head), the DAG nodes
        -- shared by all goals, and the process leaves the tail (diagnosis: which register / memory word the goal states and how large its cone is)
        if name == (← IO.getEnv "VED_S95_CLASSIFY").getD "" then
          let cnt ← IO.mkRef (({} : Std.HashMap Expr Nat))
          let per ← IO.mkRef (#[] : Array (Array Expr))
          for gq in cur do
            let e ← instantiateMVars (← gq.getType)
            let ns := Tools.VedU1WireShare.collectDag (fun _ => true) e
            per.modify (·.push ns)
            for x in ns do cnt.modify fun m => m.insert x (m.getD x 0 + 1)
          let m ← cnt.get
          let n := cur.length
          dbgLog s!"S95 cls: goals={n} union DAG nodes={m.size} nodes in all goals={(m.toList.filter (·.2 == n)).length}"
          let mut i := 0
          for gq in cur do
            let e ← instantiateMVars (← gq.getType)
            let ns := (← per.get)[i]!
            let uniq := (ns.filter fun x => m.getD x 0 == 1).size
            let fvs := (ns.filter (·.isFVar)).map fun x => (x.fvarId!).name.toString
            dbgLog s!"S95 cls {i}: tree={Tools.VedU1Loop.treeSizeVal e} dag={ns.size} uniq={uniq} nfv={fvs.size} fv={(" ".intercalate fvs.toList).take 300} head={(progShallow 5 e).take 500}"
            i := i + 1
          -- `VED_S95_DAGDUMP=i,j,..` (+ `VED_S95_DAGOUT=FILE`): the goals as DAGs (a line per node with at least two parents, the root, children named `nK` when shared)
          if let (some ds, some fo) := ((← IO.getEnv "VED_S95_DAGDUMP"), (← IO.getEnv "VED_S95_DAGOUT")) then
            let mut out := ""
            for ds1 in ds.splitOn "," do
              let some gi := ds1.toNat? | continue
              let some gq := cur[gi]? | continue
              let e ← instantiateMVars (← gq.getType)
              let ns := Tools.VedU1WireShare.collectDag (fun _ => true) e
              let mut par : Std.HashMap Expr Nat := {}
              for x in ns do
                let kids : Array Expr := match x with
                  | .app f a => #[f, a] | .lam _ t b _ => #[t, b] | .forallE _ t b _ => #[t, b] | .mdata _ b => #[b] | .proj _ _ b => #[b] | _ => #[]
                for kd in kids do par := par.insert kd (par.getD kd 0 + 1)
              -- the shared non-trivial nodes, children first: the order of `collectDag` is parents first, so reversed
              let isTriv (x : Expr) : Bool := match x with | .const .. | .fvar .. | .lit .. | .sort .. | .bvar .. => true | _ => false
              let sh := (ns.filter fun x => !isTriv x && (par.getD x 0 ≥ 2 || x == e)).reverse
              let mut ids : Std.HashMap Expr Nat := {}
              let mut kk := 0
              for x in sh do ids := ids.insert x kk; kk := kk + 1
              out := out ++ s!"## goal {gi} nodes={sh.size}\n"
              for x in sh do
                out := out ++ s!"n{ids[x]!} := {(s94DagStr ids x true).take 400}\n"
            IO.FS.writeFile fo out
          -- `VED_S95_T3OUT=DIR`: every goal as an axiom `ved_t3_g<i> : ∀ context, target` (+ the file `t3.txt`), for replays that start here
          if let some outD := (← IO.getEnv "VED_S95_T3OUT") then
            let mut ti : Nat := 0
            for gq in cur do
              let ty ← gq.withContext do
                let tgt ← instantiateMVars (← gq.getType)
                let fvs : Array Expr := (← getLCtx).foldl (fun a d => if d.isImplementationDetail then a else a.push d.toExpr) #[]
                instantiateMVars (← mkForallFVars fvs tgt (usedLetOnly := false))
              if ty.hasFVar || ty.hasMVar || ty.hasLevelParam || ty.hasLevelMVar then throwError "T3OUT: goal {ti} still has fvars/mvars/level parameters"
              withTheReader Core.Context (fun c => { c with options := c.options.setBool `debug.skipKernelTC true }) do
                addDecl (.axiomDecl { name := Name.mkSimple s!"ved_t3_g{ti}", levelParams := [], type := ty, isUnsafe := false })
              ti := ti + 1
            IO.FS.createDirAll outD
            IO.FS.writeFile (outD ++ "/t3.txt") s!"n\t{ti}\n"
            let md ← Lean.mkModuleData (← getEnv)
            let realized (n : Name) : Bool :=
              match n with
              | .str _ s => s == "splitter" || s == "eq_def" || s == "sunfold" || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
              | _ => false
            let keep := md.constants.filter (fun c => !realized c.name)
            let md' := { md with constNames := keep.map (·.name), constants := keep }
            Lean.saveModuleData (outD ++ "/VedT3.olean") (← getEnv).mainModule md'
            dbgLog s!"S95 t3 written to {outD}: {ti} goals, {md.constants.size} constants"
          break
        if !res.startsWith "ok" then
          for gq in cur.take 1 do
            dbgLog s!"S95 tail failing goal (truncated): {((← gq.withContext do ppExpr (← instantiateMVars (← gq.getType))).pretty.replace "\n" " ").take 600}"
          break
    dbgLog s!"S95 replay total ms={(← IO.monoMsNow) - tAll} hb(k)={((← IO.getNumHeartbeats) - hbAll) / 1000}"
    Tools.VedMemLoop.declWidthTab.set none

/-- replay from the t3 checkpoint (`VED_S95_T3OUT` of `#ved_s95_replay`): `VED_T3_GOALS=i,j,..` (default all) the goals `ved_t3_g<i>`; for each goal a line with its
cone (the free variables of the target with name and type, the context entries that mention them) and, with `VED_T3_TAIL=FILE` (`name TAB tactic`), the steps of FILE
run on the goal under `VED_T3_GOALHB` thousand heartbeats (default 30000), one line per step (result, ms, heartbeats, tree) -/
elab "#ved_t3_replay " d:str : command => do
  let dir := d.getString
  let n := ((← IO.FS.readFile (dir ++ "/t3.txt")).splitOn "\n").filter (· ≠ "") |>.map (·.splitOn "\t") |>.findSome? fun r => match r with | ["n", k] => k.toNat? | _ => none
  let n := n.getD 0
  let sel : List Nat := match (← IO.getEnv "VED_T3_GOALS") with
    | some ds => (ds.splitOn ",").filterMap String.toNat?
    | none => List.range n
  let lg : String → IO Unit := fun msg => do
    if let some f ← IO.getEnv "VED_T3_LOG" then
      let h ← IO.FS.Handle.mk f .append
      h.putStrLn msg
    else dbgLog msg
  let tailRows ← match (← IO.getEnv "VED_T3_TAIL") with
    | some tf => do pure (((← IO.FS.readFile tf).splitOn "\n").filter (· ≠ "") |>.map (·.splitOn "\t"))
    | none => pure []
  let cap := ((← IO.getEnv "VED_T3_GOALHB").bind String.toNat?).getD 30000
  Lean.Elab.Command.liftTermElabM do
    let seen ← IO.mkRef (({} : Std.HashSet Name))
    for i in sel do
      let some ci := (← getEnv).find? (Name.mkSimple s!"ved_t3_g{i}") | lg s!"T3 goal {i}: no constant"; continue
      let cs := (Tools.VedU1WireShare.collectDag (fun x => x.isConst) ci.type).map (·.constName!)
      for c in cs do ckptRealize seen c 6
      let mut g := (← mkFreshExprMVar ci.type).mvarId!
      let mut k := 0
      repeat
        unless (← g.getType).isForall || (← g.getType).isLet do break
        let (_, g') ← g.intro (Name.mkSimple s!"ck{k}")
        g := g'; k := k + 1
      let tgt ← instantiateMVars (← g.getType)
      let fvs := (Tools.VedU1WireShare.collectDag (fun x => x.isFVar) tgt).map (·.fvarId!)
      let desc ← g.withContext do
        let mut parts : Array String := #[]
        for f in fvs do
          let d ← f.getDecl
          parts := parts.push s!"{d.userName}:{(progShallow 3 (← instantiateMVars d.type)).take 60}"
        pure (" ".intercalate parts.toList)
      let nHyp ← g.withContext do
        let mut c := 0
        for d in ← getLCtx do
          unless d.isImplementationDetail do
            let t ← instantiateMVars d.type
            if ((Tools.VedU1WireShare.collectDag (fun x => x.isFVar) t).any fun x => fvs.contains x.fvarId!) then c := c + 1
        pure c
      let nodes := Tools.VedU1WireShare.collectDag (fun _ => true) tgt
      let cnt (c : Name) : Nat := (nodes.filter fun x => x.isAppOf c).size
      lg s!"T3 goal {i} feat: memState={cnt ``Sparkle.Core.Signal.Signal.memState} ite={cnt ``ite} div={cnt ``HDiv.hDiv} mod={cnt ``HMod.hMod} mul={cnt ``HMul.hMul} add={cnt ``HAdd.hAdd} sub={cnt ``HSub.hSub} fst={cnt ``Prod.fst} snd={cnt ``Prod.snd} toNat={cnt ``BitVec.toNat} xor={cnt ``HXor.hXor} and={cnt ``HAnd.hAnd} or={cnt ``HOr.hOr} shr={cnt ``HShiftRight.hShiftRight} shl={cnt ``HShiftLeft.hShiftLeft} lt={cnt ``LT.lt} le={cnt ``LE.le} Or={cnt ``Or} And={cnt ``And} Not={cnt ``Not}"
      lg s!"T3 goal {i}: ctx={k} tree={Tools.VedU1Loop.treeSizeVal tgt} dag={(Tools.VedU1WireShare.collectDag (fun _ => true) tgt).size} nfv={fvs.size} hyps-mentioning={nHyp}; cone: {desc.take 1500}"
      if let some nh := (← IO.getEnv "VED_T3_HYPS").bind String.toNat? then
        g.withContext do
          let mut c := 0
          for d in ← getLCtx do
            unless d.isImplementationDetail do
              let t ← instantiateMVars d.type
              if ((Tools.VedU1WireShare.collectDag (fun x => x.isFVar) t).any fun x => fvs.contains x.fvarId!) && c < nh then
                c := c + 1
                lg s!"T3 goal {i} hyp {d.userName} (tree {Tools.VedU1Loop.treeSizeVal t}): {((← ppExpr t).pretty.replace "\n" " ").take ((← IO.getEnv "VED_T3_HYPLEN").bind String.toNat? |>.getD 260)}"
      if let some lim := (← IO.getEnv "VED_T3_PP").bind String.toNat? then
        g.withContext do
          lg s!"T3 goal {i} pp: {((← ppExpr tgt).pretty.replace "\n" " ").take lim}"
      let mut cur : List MVarId := [g]
      for row in tailRows do
        let [name, txt] := row | continue
        let tac : TSyntax `tactic ← match Parser.runParserCategory (← getEnv) `tactic txt with
          | .ok st => pure ⟨st⟩
          | .error e => throwError "T3: cannot parse step {name}: {e}"
        let t1 ← IO.monoMsNow
        let hb1 ← IO.getNumHeartbeats
        let (gsO, r) : Option (List MVarId) × String ← tryCatchRuntimeEx
          (do
            let gs ← withTheReader Core.Context (fun c => { c with maxHeartbeats := cap * 1000, initHeartbeats := hb1 }) do
              Tactic.run cur.head! (do Tactic.setGoals cur; Tactic.withoutRecover (Tactic.evalTactic tac))
            pure (some gs, s!"ok out={gs.length}"))
          (fun ex => do pure (none, s!"FAILED {((← ex.toMessageData.toString).replace "\n" " ").take 200}"))
        if let some gs := gsO then cur := gs
        let mut tr := 0
        for q in cur do tr := tr + Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← q.getType))
        let ctxN ← match cur.head? with | some q => q.withContext do return (← getLCtx).decls.size | none => pure 0
        lg s!"T3 goal {i} step {name}: {r} ms={(← IO.monoMsNow) - t1} hb(k)={((← IO.getNumHeartbeats) - hb1) / 1000} goals={cur.length} tree={tr} ctx={ctxN}"
        if cur.isEmpty then break

end Tools.VedMemS94Diag
