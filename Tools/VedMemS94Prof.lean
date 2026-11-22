import Lean
import Tools.VedMemLoop

/-!
# Exclusive-time profile of the stage-94 simp (diagnosis only; never in a default script)

`ved_s94_prof [lemmas]` (env `VED_S94_PROF`, `VED_PROBE_S94`, `VED_DUMP_DIR` all set at the call site in `VedMemEntry`) takes the
target of the main goal apart like `ved_s94_diag` (`∃` binders become local hypotheses, `∧` are split) and runs `Simp.mainCore` on the
selected conjuncts (`VED_S94_PROF_ONLY`, comma list, default `0`) with `Simp.Methods` whose `pre`/`post`/`dpre`/`dpost`/`discharge?` and
every simproc of the simp set are wrapped by a timer.  The wrappers call the default ones unchanged.

Accounting: a stack of frames (`pre`, `post`, `dpre`, `dpost`, `disch`, `sp:NAME`) with an event clock.  The time between two events is charged to
the frame on top of the stack (exclusive time, nanoseconds and heartbeats = allocations); the bottom frame `main` is simp's own work outside the
wrapped methods (visit order, cache, congruence, proof assembly `mkCongrArg`/`mkEqTrans`).  Time inside a discharger that is spent outside the
nested visits' methods is charged to `disch`.  `fired:NAME` counts the lemma (head of the proof term of the step result) that a `pre`/`post` call
ended with, and the exclusive time of that call.

With `VED_S94_PROF_PLAIN` the same conjunct is first simplified with the unwrapped methods and the counters (numSteps, cache size, result
dag/tree, `==` of the results) are compared: the wrapper must not change the path.  A monitor thread logs the table every
`VED_S94_PROF_TICK` seconds (default 60); it has its own stop token and is stopped in `finally`.  At the end the process exits (a diagnosis run).
-/

namespace Tools.VedMemS94Prof

open Lean Meta Simp

structure Frame where
  label : String
  self : Nat × Nat := (0, 0)      -- exclusive ns / heartbeats before the first child and after the last one
  betw : Nat × Nat := (0, 0)      -- between two children (nested simp work outside the wrapped methods)
  pend : Nat × Nat := (0, 0)      -- since the last event
  sawChild : Bool := false

structure Acc where
  tab   : IO.Ref (Std.HashMap String (Nat × Nat × Nat))
  stack : IO.Ref (Array Frame)
  last  : IO.Ref (Nat × Nat)
  fired : IO.Ref (Std.HashMap String (Nat × Nat))
  lastChild : IO.Ref String
  pairs : IO.Ref (Std.HashMap String (Nat × Nat × Nat))   -- "prevChild -> nextChild" -> calls, ns, hb (intervals of >= 50 us only)
  lastPost : IO.Ref (Option (Expr × Step))
  ops : IO.Ref Nat
  big : IO.Ref (Array (Nat × Nat × String))               -- the largest single between-intervals

def Acc.new : IO Acc := do
  return { tab := ← IO.mkRef {}, stack := ← IO.mkRef #[{ label := "main", sawChild := true }],
           last := ← IO.mkRef ((← IO.monoNanosNow), (← IO.getNumHeartbeats)), fired := ← IO.mkRef {},
           lastChild := ← IO.mkRef "", pairs := ← IO.mkRef {}, lastPost := ← IO.mkRef none, ops := ← IO.mkRef 0, big := ← IO.mkRef #[] }

def add2 (a b : Nat × Nat) : Nat × Nat := (a.1 + b.1, a.2 + b.2)

/-- charge the time since the last event to the pending part of the frame on top of the stack -/
def Acc.charge (a : Acc) : IO Unit := do
  let now ← IO.monoNanosNow
  let hb ← IO.getNumHeartbeats
  let (t0, h0) ← a.last.get
  a.last.set (now, hb)
  a.stack.modify fun s => s.modify (s.size - 1) fun f => { f with pend := add2 f.pend (now - t0, hb - h0) }

def Acc.push (a : Acc) (l : String) : IO Unit := do
  a.charge
  -- the interval between the previous child's end and this child's start (nested simp work outside the wrapped methods)
  let st ← a.stack.get
  if let some f := st.back? then
    if f.sawChild && f.pend.1 ≥ 50000 then
      let k := s!"{f.label} | {← a.lastChild.get} -> {l}"
      a.pairs.modify fun m => let (c, n, h) := m.getD k (0, 0, 0); m.insert k (c + 1, n + f.pend.1, h + f.pend.2)
      a.big.modify fun b =>
        if b.size < 12 || f.pend.1 > (b.foldl (fun m x => min m x.1) f.pend.1) then
          let b := b.push (f.pend.1, f.pend.2, k)
          if b.size > 12 then (b.qsort (fun x y => x.1 > y.1)).extract 0 12 else b
        else b
  a.stack.modify fun s =>
    let s := s.modify (s.size - 1) fun f =>
      if f.sawChild then { f with betw := add2 f.betw f.pend, pend := (0, 0) } else { f with self := add2 f.self f.pend, pend := (0, 0) }
    s.push { label := l }
  a.tab.modify fun m => let (c, n, h) := m.getD l (0, 0, 0); m.insert l (c + 1, n, h)

def Acc.addTab (a : Acc) (l : String) (v : Nat × Nat) : IO Unit :=
  a.tab.modify fun m => let (c, n0, h0) := m.getD l (0, 0, 0); m.insert l (c, n0 + v.1, h0 + v.2)

/-- pop the top frame: its exclusive time (ns, heartbeats) -/
def Acc.pop (a : Acc) : IO (Nat × Nat) := do
  a.charge
  let s ← a.stack.get
  match s.back? with
  | none => return (0, 0)
  | some f =>
    let f := { f with self := add2 f.self f.pend, pend := (0, 0) }
    a.stack.set ((s.pop).modify (s.size - 2) fun p => { p with sawChild := true })
    a.addTab f.label f.self
    a.lastChild.set f.label
    if f.betw.1 + f.betw.2 > 0 then a.addTab (f.label ++ "/between") f.betw
    return f.self

/-- run `x` as a frame; also returns the frame's exclusive time -/
def Acc.frame (a : Acc) (l : String) (x : SimpM α) : SimpM (α × Nat) := do
  a.push l
  let r ← try (Except.ok <$> x) catch ex => pure (Except.error ex)
  let (n, _) ← a.pop
  match r with
  | .ok v => return (v, n)
  | .error ex => throw ex

def Acc.fire (a : Acc) (l : String) (pf? : Option Expr) (ns : Nat) : IO Unit := do
  let nm := match pf? with
    | some p => (match p.getAppFn with | .const c _ => toString c | .fvar _ => "<fvar>" | _ => "<other>")
    | none => "<no proof>"
  let k := l ++ ":" ++ nm
  a.fired.modify fun m => let (c, n) := m.getD k (0, 0); m.insert k (c + 1, n + ns)

def stepProof? : Step → Option Expr
  | .visit r | .done r => r.proof?
  | .continue (some r) => r.proof?
  | .continue none => none

def stepFired : Step → Bool
  | .continue none => false
  | _ => true

/-- time (us) of single operations on the step result of the previous `post` and on the term `e` of the next `pre` (cold `Meta` caches, state restored) -/
def gapOps (e : Expr) (prev : Option (Expr × Step)) : MetaM String := do
  let saved ← get
  let timed := fun (nm : String) (act : MetaM String) => do
    let t ← IO.monoNanosNow
    let r ← try act catch ex => pure s!"ERR {(← ex.toMessageData.toString).take 60}"
    pure s!"{nm}={((← IO.monoNanosNow) - t) / 1000}us({r})"
  let mut out : Array String := #[]
  modify fun st => { st with cache := {} }
  out := out.push (← timed "inferType e" do discard <| inferType e; pure "")
  out := out.push (← timed "isProof e" do return toString (← isProof e))
  if let some (pe, st) := prev then
    let some r := (match st with | .visit r | .done r => some r | .continue (some r) => some r | .continue none => none) | do
      out := out.push s!"prev step has no result; dag(e)={(Tools.VedU1WireShare.collectDag (fun _ => true) e).size} tree(e)={Tools.VedU1Loop.treeSizeVal e} dag(prev e)={(Tools.VedU1WireShare.collectDag (fun _ => true) pe).size} tree(prev e)={Tools.VedU1Loop.treeSizeVal pe} e==prev:{e == pe} prevHead={pe.getAppFn.constName?}"
      modify fun st => { st with cache := {} }
      out := out.push (← timed "unfoldDefinition? prev" do
        match ← unfoldDefinition? pe with
        | some u => return s!"some, == e: {u == e}, headBeta == e: {u.headBeta == e}, head={u.getAppFn.constName?}"
        | none => return "none")
      out := out.push (← timed "whnfCore prev" do discard <| whnfCore pe; pure "")
      out := out.push (← timed "instantiateMVars prev" do discard <| instantiateMVars pe; pure "")
      out := out.push (← timed "inferType prev" do discard <| inferType pe; pure "")
      set saved
      return " ".intercalate out.toList
    out := out.push s!"dag(e)={(Tools.VedU1WireShare.collectDag (fun _ => true) e).size} tree(e)={Tools.VedU1Loop.treeSizeVal e} dag(prev)={(Tools.VedU1WireShare.collectDag (fun _ => true) pe).size} dag(r.expr)={(Tools.VedU1WireShare.collectDag (fun _ => true) r.expr).size} e==r.expr:{e == r.expr}"
    if let some p := r.proof? then
      out := out.push s!"dag(proof)={(Tools.VedU1WireShare.collectDag (fun _ => true) p).size}"
      modify fun st => { st with cache := {} }
      out := out.push (← timed "instantiateMVars proof" do discard <| instantiateMVars p; pure "")
      modify fun st => { st with cache := {} }
      let ty ← IO.mkRef (none : Option Expr)
      out := out.push (← timed "inferType proof" do let t ← inferType p; ty.set (some t); pure s!"head={t.getAppFn.constName?}")
      if let some t ← ty.get then
        if let some (_, a, b) := t.eq? then
          out := out.push (← timed "mkEqTrans p (refl b)" do discard <| mkEqTrans p (← mkEqRefl b); pure "")
          out := out.push (← timed "isDefEq b r.expr" do return toString (← isDefEq b r.expr))
          out := out.push (← timed "isDefEq a prevE" do return toString (← isDefEq a pe))
  set saved
  return " ".intercalate out.toList

def Acc.simproc (a : Acc) (l : String) (p : Simproc) : Simproc := fun e => do
  if l == "pre" then
    -- a large interval since the last event (diagnosis of the stall right before this visit): operations on the step result of the previous `post`
    let (t0, _) ← a.last.get
    let gap := (← IO.monoNanosNow) - t0
    if gap ≥ 150000000 && (← a.ops.get) < 4 then
      a.ops.modify (· + 1)
      a.charge
      let msg ← gapOps e (← a.lastPost.get)
      let path := String.intercalate " > " ((← a.stack.get).map (·.label)).toList
      Tools.VedMemLoop.dbgLog s!"S94P gapops after {gap / 1000} us before pre:{Tools.VedMemLoop.s94Head e}: ptrObjs(e)={← Lean.Expr.numObjs e} stack={path.take 600}: {msg}"
      a.last.set ((← IO.monoNanosNow), (← IO.getNumHeartbeats))
  let (s, ns) ← a.frame (l ++ ":" ++ Tools.VedMemLoop.s94Head e) (p e)
  if l == "post" then a.lastPost.set (some (e, s))
  if stepFired s then a.fire l (stepProof? s) ns
  return s

def Acc.dproc (a : Acc) (l : String) (p : DSimproc) : DSimproc := fun e => do
  let (s, _) ← a.frame (l ++ ":" ++ Tools.VedMemLoop.s94Head e) (p e)
  return s

/-- the body of `bindStrictStep` (same operations in the same order) with a frame around each part; used instead of the simproc itself in the wrapped run -/
def bindStrictTimed (a : Acc) : Simproc := fun e => do
  let (mi, f) ←
    if e.isAppOfArity ``Option.bind 4 then pure (2, e.getArg! 3)
    else if e.isAppOfArity ``Bind.bind 6 && (e.getArg! 0).isConstOf ``Option then pure (4, e.getArg! 5)
    else return .continue
  let m := e.getArg! mi
  if m.isAppOfArity ``Option.some 2 then return .continue
  unless f.isLambda do return .continue
  let (r, _) ← a.frame "bs:simp m" (Simp.simp m)
  unless r.expr.isAppOfArity ``Option.some 2 do return .continue
  let (new, _) ← a.frame "bs:headBeta" (pure ((mkApp f r.expr.appArg!).headBeta))
  match r.proof? with
  | none => return .continue
  | some p =>
    Tools.VedMemLoop.bindStrictHits.modify (· + 1)
    let mT ← inferType m
    let motive := Expr.lam `y mT (mkAppN e.getAppFn (e.getAppArgs.set! mi (.bvar 0))) .default
    let x := r.expr.appArg!
    let (pf0, _) ← a.frame "bs:mkCongrArg" (mkCongrArg motive p)
    let mut pf := pf0
    if mi == 4 then
      let (pf1, _) ← a.frame "bs:mkEqTrans(bind_eq_bind)" do
        mkEqTrans pf (← mkCongrFun (← mkCongrFun (← mkAppOptM ``Option.bind_eq_bind #[some (e.getArg! 2), some (e.getArg! 3)]) r.expr) f)
      pf := pf1
    let (bs, _) ← a.frame "bs:mkAppM bind_some" (mkAppM ``Option.bind_some #[x, f])
    let (pf2, _) ← a.frame "bs:mkEqTrans(bind_some)" (mkEqTrans pf bs)
    return .visit { expr := new, proof? := some pf2 }

def wrapEntry (a : Acc) (timedBs : Bool) (en : SimprocEntry) : SimprocEntry :=
  let lbl := s!"sp:{en.declName}"
  let isBs := timedBs && (en.declName == ``Tools.VedMemLoop.vedBindStrictB || en.declName == ``Tools.VedMemLoop.vedBindStrictO)
  { en with proc := match en.proc with
    | .inl p => .inl (fun e => do
        let (s, _) ← a.frame lbl (if isBs then bindStrictTimed a e else p e)
        return s)
    | .inr p => .inr (fun e => do
        let (s, _) ← a.frame lbl (p e)
        return s) }

def wrapSimprocs (a : Acc) (timedBs : Bool) (s : Simprocs) : Simprocs :=
  { s with pre := s.pre.mapArrays (·.map (wrapEntry a timedBs)), post := s.post.mapArrays (·.map (wrapEntry a timedBs)) }

/-- `VED_S94_PROF_CLEAR=N` (diagnosis): every N-th `pre` call empties the `Meta` caches `inferType`, `funInfo`, `synthInstance`, `whnf` -/
def clearEvery (n : Nat) (cnt : IO.Ref Nat) (p : Simproc) : Simproc := fun e => do
  if n != 0 then
    let k ← cnt.modifyGet fun k => (k + 1, k + 1)
    if k % n == 0 then
      modifyThe Meta.State fun st => { st with cache := { st.cache with inferType := {}, funInfo := {}, synthInstance := {}, whnf := {} } }
  p e

def wrapMethods (a : Acc) (clr : Nat) (cnt : IO.Ref Nat) (m : Methods) : Methods :=
  { m with
    pre := clearEvery clr cnt (a.simproc "pre" m.pre)
    post := a.simproc "post" m.post
    dpre := a.dproc "dpre" m.dpre
    dpost := a.dproc "dpost" m.dpost
    discharge? := fun e => do
      let (r, _) ← a.frame "disch" (m.discharge? e)
      return r }

def mkMeth (simprocs : SimprocsArray) (d? : Option Simp.Discharge) : Methods :=
  match d? with
  | none => mkDefaultMethodsCore simprocs
  | some d => mkMethods simprocs d (wellBehavedDischarge := false)

def Acc.report (a : Acc) (tag : String) : IO Unit := do
  let tab ← a.tab.get
  let some bot := (← a.stack.get)[0]? | return
  let tab := tab.insert "main/between" (0, bot.betw.1 + bot.pend.1, bot.betw.2 + bot.pend.2)
  let tot := tab.fold (fun s _ (_, n, _) => s + n) 0
  let arr := (tab.toList.toArray.qsort fun x y => x.2.2.1 > y.2.2.1)
  let hbTot := tab.fold (fun s _ (_, _, h) => s + h) 0
  Tools.VedMemLoop.dbgLog s!"S94P {tag}: exclusive total {tot / 1000000} ms, {hbTot / 1000} k allocations"
  -- group totals by the part before the first `:`
  let g := tab.fold (fun (m : Std.HashMap String (Nat × Nat × Nat)) l (c, n, h) =>
    let k := (l.splitOn ":").head!.replace "/between" "" ++ (if l.endsWith "/between" then "/between" else "")
    let (c0, n0, h0) := m.getD k (0, 0, 0); m.insert k (c0 + c, n0 + n, h0 + h)) {}
  for (k, (c, n, h)) in (g.toList.toArray.qsort fun x y => x.2.2.1 > y.2.2.1) do
    Tools.VedMemLoop.dbgLog s!"S94P {tag} group {k}: calls={c} ms={n / 1000000} hb(k)={h / 1000} share={(n * 1000 / (tot + 1)) / 10}.{(n * 1000 / (tot + 1)) % 10}%"
  for (k, (c, n, h)) in arr.extract 0 28 do
    Tools.VedMemLoop.dbgLog s!"S94P {tag} row {k}: calls={c} ms={n / 1000000} hb(k)={h / 1000} share={(n * 1000 / (tot + 1)) / 10}.{(n * 1000 / (tot + 1)) % 10}%"
  let pr ← a.pairs.get
  for (k, (c, n, h)) in (pr.toList.toArray.qsort fun x y => x.2.2.1 > y.2.2.1).extract 0 14 do
    Tools.VedMemLoop.dbgLog s!"S94P {tag} between {k}: calls={c} ms={n / 1000000} hb(k)={h / 1000}"
  for (n, h, k) in (← a.big.get).qsort (fun x y => x.1 > y.1) do
    Tools.VedMemLoop.dbgLog s!"S94P {tag} bigone {k}: us={n / 1000} hb(k)={h / 1000}"
  let f ← a.fired.get
  for (k, (c, n)) in (f.toList.toArray.qsort fun x y => x.2.2 > y.2.2).extract 0 16 do
    Tools.VedMemLoop.dbgLog s!"S94P {tag} fired {k}: calls={c} ms={n / 1000000}"

/-- the monitor: logs the table every `secs` seconds; returns its own stop token -/
def startMonitor (a : Acc) (secs : Nat) : IO (IO.Ref Bool) := do
  let stop ← IO.mkRef false
  let _ ← IO.asTask (prio := .dedicated) do
    let mut k := 0
    while !(← stop.get) do
      IO.sleep (secs * 1000).toUInt32
      if (← stop.get) then break
      k := k + 1
      a.report s!"tick {k}"
  return stop

open Lean Elab Tactic in
elab "ved_s94_prof " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => withMainContext do
  unless (← IO.getEnv "VED_S94_PROF").isSome && (← IO.getEnv "VED_DUMP_DIR").isSome do return
  let stx0 ← `(tactic| ved_loop_simp [$ls,*])
  let some (_, .ok stx1) ← liftMacroM (Lean.Elab.expandMacroImpl? (← getEnv) stx0) | throwError "ved_s94_prof: ved_loop_simp does not expand"
  let sc ← Lean.Elab.Tactic.mkSimpContext stx1 (eraseLocal := false)
  -- `VED_S94_PROF_CFG=field=val,...` (diagnosis): override `Simp.Config` fields of the stage's config for every run of this call
  let sc ← do
    let mut cfg := sc.ctx.config
    for kv in ((← IO.getEnv "VED_S94_PROF_CFG").getD "").splitOn "," do
      match kv.splitOn "=" with
      | [k, v] =>
        let b := v == "true"
        cfg := match k with
          | "dsimp" => { cfg with dsimp := b } | "proj" => { cfg with proj := b } | "beta" => { cfg with beta := b }
          | "eta" => { cfg with eta := b } | "etaStruct" => { cfg with etaStruct := if b then .all else .none }
          | "zeta" => { cfg with zeta := b } | "zetaDelta" => { cfg with zetaDelta := b } | "iota" => { cfg with iota := b }
          | "memoize" => { cfg with memoize := b } | "contextual" => { cfg with contextual := b } | "arith" => { cfg with arith := b }
          | "ground" => { cfg with ground := b } | "index" => { cfg with index := b }
          | "implicitDefEqProofs" => { cfg with implicitDefEqProofs := b }
          | "decide" => { cfg with decide := b } | "autoUnfold" => { cfg with autoUnfold := b }
          | _ => cfg
      | _ => pure ()
    let ctx ← sc.ctx.setConfig cfg
    -- `nocongr=true`: no user congruence theorems; `congrdrop=NAME` drops the congruence theorems whose theorem or function name is NAME (`+`-separated list)
    let cfgS := ((← IO.getEnv "VED_S94_PROF_CFG").getD "").splitOn ","
    let drops := (cfgS.filterMap fun kv => (match kv.splitOn "=" with | ["congrdrop", v] => some (v.splitOn "+") | _ => none)).flatten
    let all := sc.ctx.congrTheorems.lemmas.fold (fun (acc : Array SimpCongrTheorem) _ l => acc ++ l.toArray) #[]
    Tools.VedMemLoop.dbgLog s!"S94P congr theorems: {all.size}: {", ".intercalate (all.map fun c => s!"{c.theoremName}@{c.funName}").toList}"
    let ctx ← if cfgS.contains "nocongr=true" then Simp.mkContext ctx.config ctx.simpTheorems {} ctx.userConfig
      else if drops.isEmpty then pure ctx
      else
        let kept := all.filter fun c => !(drops.contains c.theoremName.toString || drops.contains c.funName.toString)
        Simp.mkContext ctx.config ctx.simpTheorems { lemmas := kept.foldl (fun (m : SMap Name (List SimpCongrTheorem)) c => m.insert c.funName (c :: m.findD c.funName [])) {} } ctx.userConfig
    pure { sc with ctx := ctx }
  Tools.VedMemLoop.dbgLog s!"S94P config: dsimp={sc.ctx.config.dsimp} proj={sc.ctx.config.proj} beta={sc.ctx.config.beta} eta={sc.ctx.config.eta} etaStruct={repr sc.ctx.config.etaStruct} zeta={sc.ctx.config.zeta} zetaDelta={sc.ctx.config.zetaDelta} iota={sc.ctx.config.iota} memoize={sc.ctx.config.memoize} contextual={sc.ctx.config.contextual} arith={sc.ctx.config.arith} ground={sc.ctx.config.ground} index={sc.ctx.config.index} implicitDefEqProofs={sc.ctx.config.implicitDefEqProofs} decide={sc.ctx.config.decide} maxSteps={sc.ctx.config.maxSteps}"
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let only := ((← IO.getEnv "VED_S94_PROF_ONLY").getD "0").splitOn "," |>.filterMap (·.toNat?)
  let plain := (← IO.getEnv "VED_S94_PROF_PLAIN").isSome
  let tick := ((← IO.getEnv "VED_S94_PROF_TICK").bind (·.toNat?)).getD 60
  let idx ← IO.mkRef 0
  let dagOf := fun (x : Expr) => (Tools.VedU1WireShare.collectDag (fun _ => true) x).size
  Tools.VedMemLoop.s94Walk tgt fun c => do
    let i ← idx.modifyGet fun i => (i, i + 1)
    unless only.contains i do return
    Tools.VedMemLoop.dbgLog s!"S94P #{i} start dag={dagOf c} tree={Tools.VedU1Loop.treeSizeVal c}"
    let reset := (← IO.getEnv "VED_S94_PROF_RESET").getD ""
    let clr := ((← IO.getEnv "VED_S94_PROF_CLEAR").bind (·.toNat?)).getD 0
    let cnt ← IO.mkRef 0
    let timedBs := (← IO.getEnv "VED_S94_PROF_BS").isSome
    let run := fun (wrap : Option Acc) => do
      let sv ← Meta.saveState
      let hb ← IO.getNumHeartbeats
      let t0 ← IO.monoMsNow
      let r ← withTheReader Core.Context (fun cc => { cc with maxHeartbeats := 2000000000, initHeartbeats := hb }) do
        sc.dischargeWrapper.with fun d? => do
          let m := match wrap with
            | none => mkMeth sc.simprocs d?
            | some a => wrapMethods a clr cnt (mkMeth (sc.simprocs.map (wrapSimprocs a timedBs)) d?)
          Simp.mainCore c sc.ctx {} (methods := m)
      let ms := (← IO.monoMsNow) - t0
      let st ← getThe Meta.State
      let cnt := fun {α β : Type} [BEq α] [Hashable α] (m : PersistentHashMap α β) => m.foldl (fun n _ _ => n + 1) 0
      Tools.VedMemLoop.dbgLog s!"S94P #{i} Meta caches after run: inferType={cnt st.cache.inferType} funInfo={cnt st.cache.funInfo} synth={cnt st.cache.synthInstance} whnf={cnt st.cache.whnf} defEqTrans={cnt st.cache.defEqTrans} defEqPerm={cnt st.cache.defEqPerm}"
      if reset == "full" then sv.restore
      else if reset == "cache" then modifyThe Meta.State fun st => { st with cache := {} }
      else if reset != "" then
        let fs := reset.splitOn ","
        modifyThe Meta.State fun st => { st with cache := {
          inferType := if fs.contains "inferType" then {} else st.cache.inferType
          funInfo := if fs.contains "funInfo" then {} else st.cache.funInfo
          synthInstance := if fs.contains "synth" then {} else st.cache.synthInstance
          whnf := if fs.contains "whnf" then {} else st.cache.whnf
          defEqTrans := if fs.contains "defEqTrans" then {} else st.cache.defEqTrans
          defEqPerm := if fs.contains "defEqPerm" then {} else st.cache.defEqPerm } }
      return (r, ms, ((← IO.getNumHeartbeats) - hb) / 1000)
    let summary := fun (tag : String) (r : Simp.Result × Simp.State) (ms hb : Nat) => do
      let pf := match r.1.proof? with | some p => dagOf p | none => 0
      Tools.VedMemLoop.dbgLog s!"S94P #{i} {tag}: ms={ms} hb(k)={hb} numSteps={r.2.numSteps} cache={r.2.cache.foldStage2 (fun n _ _ => n + 1) 0} usedThms={r.2.usedTheorems.map.foldl (fun n _ _ => n + 1) 0} result dag={dagOf r.1.expr} tree={Tools.VedU1Loop.treeSizeVal r.1.expr} proofDag={pf} hash={r.1.expr.hash}"
    let bs0 ← Tools.VedMemLoop.bindStrictMs.get
    let mut plainRes : Option Expr := none
    let plain2 := (← IO.getEnv "VED_S94_PROF_PLAIN") == some "2"
    if plain then
      let (r, ms, hb) ← run none
      summary "plain" r ms hb
      plainRes := some r.1.expr
    if (← IO.getEnv "VED_S94_PROF_NOWRAP").isSome then
      let (r, ms, hb) ← run none
      summary "plain-only" r ms hb
      if let some pe := plainRes then
        Tools.VedMemLoop.dbgLog s!"S94P #{i} plain-only result == first plain result: {pe == r.1.expr}"
      return
    let a ← Acc.new
    let stop ← startMonitor a tick
    try
      let (r, ms, hb) ← run (some a)
      summary "wrapped" r ms hb
      if let some pe := plainRes then
        Tools.VedMemLoop.dbgLog s!"S94P #{i} wrapped result == plain result: {pe == r.1.expr}"
    finally
      stop.set true
    let bs1 ← Tools.VedMemLoop.bindStrictMs.get
    Tools.VedMemLoop.dbgLog s!"S94P #{i} bindStrict counters (plain+wrapped runs): simp m us={bs1.1 - bs0.1} proof us={bs1.2 - bs0.2}"
    a.report s!"#{i} final"
    if plain2 then
      let (r, ms, hb) ← run none
      summary "plain again" r ms hb
  Tools.VedMemLoop.dbgLog "S94P done"
  IO.Process.exit 0

end Tools.VedMemS94Prof
