import Lean
import Tools.VedMemLoop

/-!
# `ved_causal` simp1 timing (DIAGNOSIS ONLY; not imported by any production module)

Imported only by a diagnosis case file.  With the env var `VED_DIAG` unset every `ved_loop_simp` runs exactly as in
production (the production macro is called directly).  With `VED_DIAG` set, at the `VED_DIAG_K`-th (default 1) `ved_loop_simp`
call that has the shape of the `ved_causal` simp1 (its lemma list holds `memory_val_succ`, no location) and whose goal has
a tree of more than `VED_DIAG_MIN` (default 1000000; 0 = every such goal) nodes, the simp1 is run ONCE through `Simp.main`
with wrapped `pre`/`post`/`dpre`/`dpost`, and the process is stopped:

  `VED DIAG STOP diagnostic_only reason=<fixed code>` on stderr, the measurement lines, then `IO.Process.exit 3`
  (never 0).  A stopped run is never a ledger row.

The simp1 syntax is the one the production macro expands `ved_loop_simp [...]` to (the production macro function is called
on the very syntax, so lemma list and config are the production ones by construction).

Measured: `totalMs` of the `Simp.main` call; `insideMs` = the time spent in `pre`/`post` (and `dpre`/`dpost`, reported
apart) calls at re-entry depth 0 (a nested call from a discharger / recursive simp is counted in `depthGt0Calls` only: its time
is inside the depth-0 call that contains it); recorded also when the call throws.  No size counting of results or
proofs, no message `toString`; only finite counters and head constant names.

Cooperative cancel (NOT a hard cap): every wrapper call compares the wall clock with `VED_DIAG_CAP_S` (default 300; `VED_DIAG_CAP_MS` overrides, for controls) and, after
it, throws a fixed error (sticky: later calls throw again, so a swallowing `try` inside simp does not cancel the cancel).  A
cancel can only happen at a pre/post call; the hard limits are the outer `timeout` and the RSS guard.
The state is restored in a `finally` path.  `VED_DIAG_AFTER=continue` (controls only) restores and carries on with the
production tactic instead of exiting.

Test hooks (controls): `VED_DIAG_THROW_AT=N` makes the N-th depth-0 pre/post call throw after its work;
`ved_diag_test [lemmas]` runs the measurement on the current goal with an arbitrary `simp [lemmas]` (always continues).
-/

namespace Tools.VedMemCausalDiag

open Lean Meta Elab Tactic

/-- phase sampling state.  `cur` is written by the simp thread (at hook entry/exit) and read by the sampler thread;
`samples`/`sampNs`/`ticks` are written by the sampler thread only and read after it has ended; `hb` is written by the simp
thread only (the heartbeat delta since the previous phase change is added to the phase being left). -/
structure Phases where
  cur : IO.Ref Nat
  stop : IO.Ref Bool
  samples : IO.Ref (Array Nat)
  sampNs : IO.Ref (Array Nat)
  ticks : IO.Ref Nat
  hb : IO.Ref (Array Nat)
  hbLast : IO.Ref Nat

/-- phase ids: 0 outside every wrapped hook; 1..4 pre/post/dpre/dpost at depth 0; 7..10 the same nested (inside another
hook); 11 inside a `discharge?` call (nested hooks of its nested simp show as 7..10 while they run) -/
def nPhases : Nat := 12

def phaseLabel : Nat → String
  | 0 => "outside" | 1 => "pre0" | 2 => "post0" | 3 => "dpre0" | 4 => "dpost0"
  | 7 => "pre>0" | 8 => "post>0" | 9 => "dpre>0" | 10 => "dpost>0" | 11 => "discharge" | _ => "unused"

def Phases.new : IO Phases := do
  return { cur := ← IO.mkRef 0, stop := ← IO.mkRef false, samples := ← IO.mkRef (Array.replicate nPhases 0),
           sampNs := ← IO.mkRef (Array.replicate nPhases 0), ticks := ← IO.mkRef 0,
           hb := ← IO.mkRef (Array.replicate nPhases 0), hbLast := ← IO.mkRef 0 }

/-- enter phase `new` (simp thread); returns the phase left, which gets the heartbeats allocated since the last change -/
def Phases.switch (p : Phases) (new : Nat) : IO Nat := do
  let old ← p.cur.get
  let h ← IO.getNumHeartbeats
  let last ← p.hbLast.get
  p.hb.modify fun a => a.modify old (· + (h - last))
  p.hbLast.set h
  p.cur.set new
  return old

/-- the sampler/watcher thread: every `periodMs` ms it reads the current phase and counts a sample (and the elapsed ns)
for it, and sets the cancel token once the cooperative cap is over.  It only reads/writes its own refs and the token. -/
def startSampler (p : Phases) (periodMs : UInt32) (t0 capNs : Nat) (tk : IO.CancelToken) : IO (Task (Except IO.Error Unit)) :=
  IO.asTask (prio := .dedicated) do
    let mut last ← IO.monoNanosNow
    repeat
      IO.sleep periodMs
      let now ← IO.monoNanosNow
      let ph ← p.cur.get
      p.samples.modify fun a => a.modify ph (· + 1)
      p.sampNs.modify fun a => a.modify ph (· + (now - last))
      p.ticks.modify (· + 1)
      last := now
      if now - t0 > capNs then tk.set
      if (← p.stop.get) then break

/-- finite counters of one instrumented measurement -/
structure Acc where
  t0 : IO.Ref Nat                      -- set when `Simp.main` starts
  capNs : Nat
  throwAt : Nat
  depth : IO.Ref Nat
  cancelled : IO.Ref Bool
  inNs : IO.Ref Nat
  inDNs : IO.Ref Nat
  calls : IO.Ref (Array Nat)           -- pre, post, dpre, dpost at depth 0
  deep : IO.Ref Nat                    -- calls at depth > 0
  n0 : IO.Ref Nat                      -- depth-0 pre/post calls so far (for the test throw)
  slow : IO.Ref (Array (Nat × Name × Nat))   -- (ns, head, kind) the slowest depth-0 calls
  heads : IO.Ref (Std.HashMap Name (Nat × Nat)) -- head -> (ns, calls), pre/post depth 0
  ph : Phases
  disDepth : IO.Ref Nat
  dis : IO.Ref (Nat × Nat)             -- outermost `discharge?` calls: (calls, ns)
  lastSteps : IO.Ref Nat               -- Simp.State.numSteps read at the end of the last depth-0 hook

def Acc.new (capMs throwAt : Nat) (ph : Phases) : IO Acc := do
  return { t0 := ← IO.mkRef 0, capNs := capMs * 1000000, throwAt, depth := ← IO.mkRef 0, cancelled := ← IO.mkRef false,
           inNs := ← IO.mkRef 0, inDNs := ← IO.mkRef 0, calls := ← IO.mkRef #[0, 0, 0, 0], deep := ← IO.mkRef 0,
           n0 := ← IO.mkRef 0, slow := ← IO.mkRef #[], heads := ← IO.mkRef {}, ph,
           disDepth := ← IO.mkRef 0, dis := ← IO.mkRef (0, 0), lastSteps := ← IO.mkRef 0 }

def headName (e : Expr) : Name :=
  match e.getAppFn with
  | .const c _ => c
  | .proj .. => `_proj
  | .fvar .. => `_fvar
  | .lam .. => `_lam
  | .forallE .. => `_forall
  | .letE .. => `_let
  | .mdata .. => `_mdata
  | .lit .. => `_lit
  | _ => `_other

def kindName : Nat → String
  | 0 => "pre" | 1 => "post" | 2 => "dpre" | _ => "dpost"

/-- run `k` (a `pre`/`post`/`dpre`/`dpost`) timed at depth 0 only; the time is added also when `k` throws.  The phase
(for the sampler and the heartbeat deltas) is set for the duration of the call at every depth and restored. -/
def timed {α : Type} (a : Acc) (kind : Nat) (e : Expr) (k : Simp.SimpM α) : Simp.SimpM α := do
  let t ← IO.monoNanosNow
  if (← a.cancelled.get) || t - (← a.t0.get) > a.capNs then
    a.cancelled.set true
    throwError "ved_diag: cooperative cancel"
  let d ← a.depth.get
  let old ← a.ph.switch (kind + 1 + (if d > 0 then 6 else 0))
  try
    if d > 0 then
      a.deep.modify (· + 1)
      return (← k)
    a.depth.set 1
    a.calls.modify fun c => c.modify kind (· + 1)
    try
      let r ← k
      if kind < 2 && a.throwAt > 0 then
        let n ← a.n0.modifyGet fun n => (n + 1, n + 1)
        if n == a.throwAt then throwError "ved_diag: test throw"
      return r
    finally
      let dt := (← IO.monoNanosNow) - t
      a.depth.set 0
      let st ← get
      a.lastSteps.set st.numSteps
      if kind < 2 then
        a.inNs.modify (· + dt)
        let h := headName e
        a.heads.modify fun m => let (n, c) := m.getD h (0, 0); m.insert h (n + dt, c + 1)
      else
        a.inDNs.modify (· + dt)
      let sl ← a.slow.get
      if sl.size < 10 || dt > (sl.back!).1 then
        a.slow.set ((sl.push (dt, headName e, kind)).qsort (fun x y => x.1 > y.1) |>.extract 0 10)
  finally
    discard <| a.ph.switch old

/-- the wrapped `discharge?`: phase 11 while it runs; the time of outermost calls is summed -/
def timedDis (a : Acc) (k : Simp.SimpM (Option Expr)) : Simp.SimpM (Option Expr) := do
  let t ← IO.monoNanosNow
  let dd ← a.disDepth.get
  a.disDepth.set (dd + 1)
  let old ← a.ph.switch 11
  try k
  finally
    discard <| a.ph.switch old
    a.disDepth.set dd
    let dt := (← IO.monoNanosNow) - t
    if dd == 0 then a.dis.modify fun (n, ns) => (n + 1, ns + dt)

def wrap (a : Acc) (m : Simp.Methods) : Simp.Methods :=
  { m with
    pre := fun e => timed a 0 e (m.pre e)
    post := fun e => timed a 1 e (m.post e)
    dpre := fun e => timed a 2 e (m.dpre e)
    dpost := fun e => timed a 3 e (m.dpost e)
    discharge? := fun e => timedDis a (m.discharge? e) }

/-- the real stderr (Lean isolates `IO.getStderr` while a command elaborates; a line written there is lost on `exit`) -/
def rawErr : IO IO.FS.Handle := IO.FS.Handle.mk "/dev/stderr" .append

initialize diagStarted : IO.Ref Bool ← IO.mkRef false

/-- the first call writes a padding line: the RSS guard writes its summary at the start of a shared stderr FILE (a separate
open of `/dev/stderr` does not share the file offset) and would overwrite the head of our first line -/
def diagLine (l : String) : IO Unit := do
  let h ← rawErr
  unless (← diagStarted.get) do
    diagStarted.set true
    h.putStrLn ("VED DIAG begin (padding line, may be overwritten by the RSS guard summary) " ++ String.ofList (List.replicate 160 '.'))
  h.putStrLn l
  h.flush

def fmtMs (ns : Nat) : String := s!"{ns / 1000000}"

/-- process user/system CPU time in clock ticks (1/100 s), from `/proc/self/stat` (all threads) -/
def cpuTicks : IO (Nat × Nat) := do
  try
    let s ← IO.FS.readFile "/proc/self/stat"
    let ws := ((s.splitOn ") ").getLast!.splitOn " ").toArray
    return ((ws[11]!).toNat?.getD 0, (ws[12]!).toNat?.getD 0)
  catch _ => return (0, 0)

/-- result of one variant run (finite counters only) -/
structure VRes where
  tag : String
  reason : String := "measured"
  totalNs : Nat := 0
  hbDelta : Nat := 0
  cpu : Nat × Nat := (0, 0)
  steps : Nat := 0
  cacheSz : Nat := 0
  congrSz : Nat := 0
  dsimpSz : Nat := 0
  res : Option Simp.Result := none
  acc : Option Acc := none
  prof : Array (Name × Nat × Nat) := #[]
  tickN : Nat := 0

def reportInstr (a : Acc) (totalNs : Nat) (reason : String) : IO Unit := do
  let inN ← a.inNs.get
  let inD ← a.inDNs.get
  let cs ← a.calls.get
  let deep ← a.deep.get
  let sl ← a.slow.get
  let hs := (← a.heads.get).toArray.qsort (fun x y => x.2.1 > y.2.1)
  let tot := totalNs / 1000000
  let ins := (inN + inD) / 1000000
  let cls :=
    if reason != "measured" then "unknown"
    else if ins * 3 > tot * 2 then "inside_dominated"
    else if ins * 3 < tot then "outside_dominated"
    else "mixed"
  let l1 := s!"VED DIAG [b] totalMs={tot} insideMs={ins} (prepostMs={fmtMs inN} dprepostMs={fmtMs inD}) outsideMs={if tot ≥ ins then tot - ins else 0} totalUs={totalNs / 1000} insideUs={(inN + inD) / 1000} insideOverTotal={if tot == 0 then 0 else ins * 100 / tot}% class={cls}"
  let l2 := s!"VED DIAG [b] calls depth0 pre={cs[0]!} post={cs[1]!} dpre={cs[2]!} dpost={cs[3]!} depthGt0Calls={deep} (not timed separately)"
  let l3 := "VED DIAG [b] slowest depth0 calls: " ++ String.intercalate "; " (sl.toList.map fun (ns, h, k) => s!"{kindName k} {h} {fmtMs ns}ms")
  let l4 := "VED DIAG [b] top heads by inside ms (pre/post depth0): " ++ String.intercalate "; " ((hs.toList.take 10).map fun (h, (ns, c)) => s!"{h} {fmtMs ns}ms/{c}")
  let (dn, dns) ← a.dis.get
  let l5 := s!"VED DIAG [b] outermost discharge? calls={dn} ms={fmtMs dns} (inside the depth-0 calls above); last depth-0 hook saw numSteps={← a.lastSteps.get}"
  for l in [l1, l2, l3, l4, l5] do
    diagLine l

def reportPhases (ph : Phases) (totalNs : Nat) : IO Unit := do
  let sm ← ph.samples.get
  let ns ← ph.sampNs.get
  let hb ← ph.hb.get
  let n := sm.foldl (· + ·) 0
  let sns := ns.foldl (· + ·) 0
  let hbs := hb.foldl (· + ·) 0
  diagLine s!"VED DIAG [b] sampler ticks={← ph.ticks.get} samples={n} sampledMs={fmtMs sns} wallMs={fmtMs totalNs} heartbeatsK={hbs / 1000}"
  for i in [0:nPhases] do
    if i != 5 && i != 6 then
      diagLine s!"VED DIAG [b] phase {phaseLabel i} samples={sm[i]!} share={if n == 0 then 0 else sm[i]! * 100 / n}% ms={fmtMs ns[i]!} hbK={hb[i]! / 1000} hbShare={if hbs == 0 then 0 else hb[i]! * 100 / hbs}%"

def reportVariant (r : VRes) : IO Unit := do
  diagLine s!"VED DIAG [{r.tag}] reason={r.reason} totalMs={r.totalNs / 1000000} totalUs={r.totalNs / 1000} heartbeatsK={r.hbDelta / 1000} cpuUserTicks={r.cpu.1} cpuSysTicks={r.cpu.2} numSteps={r.steps} cacheSize={r.cacheSz} congrCacheSize={r.congrSz} dsimpCacheSize={r.dsimpSz}"
  if let some a := r.acc then
    reportInstr a r.totalNs r.reason
    reportPhases a.ph r.totalNs
  if r.prof.size > 0 then
    let top := r.prof.qsort (fun x y => x.2.1 > y.2.1)
    diagLine ("VED DIAG [" ++ r.tag ++ "] trace.profiler exclusive ms by class (nodes over the threshold; sub-threshold children are inside their parent): " ++ String.intercalate "; " ((top.toList.take 15).map fun (c, (ns, k)) => s!"{c} {fmtMs ns}ms/{k}"))

/-- aggregate the profiler trace nodes by class (exclusive time = node time - time of its traced children); no toString -/
partial def walkTrace (acc : IO.Ref (Std.HashMap Name (Nat × Nat))) : MessageData → IO Nat
  | .trace d _ cs => do
    let mut childSum := 0
    for c in cs do
      childSum := childSum + (← walkTrace acc c)
    let ns := ((d.stopTime - d.startTime) * 1000000000.0).toUInt64.toNat
    acc.modify fun m => let (x, c) := m.getD d.cls (0, 0); m.insert d.cls (x + (ns - childSum), c + 1)
    return ns
  | .withContext _ m | .withNamingContext _ m | .nest _ m | .group m | .tagged _ m | .ofWidget _ m => walkTrace acc m
  | .compose a b => do return (← walkTrace acc a) + (← walkTrace acc b)
  | _ => return 0

def envNat (n : String) (d : Nat) : IO Nat := return ((← IO.getEnv n).bind String.toNat?).getD d

/-- run `x` and return its exception as a value, INCLUDING interrupt exceptions (which `try`/`catch` and
`tryCatchRuntimeEx` rethrow): the cancel token makes Lean's own `checkSystem` points throw an interrupt, and that interrupt
has to stop only this measurement, not the command -/
def tryAllCore {α : Type} (x : CoreM α) : CoreM (Except Exception α) := fun ctx sref => do
  let r ← EIO.toBaseIO (x ctx sref)
  pure r

def tryAllMeta {α : Type} (x : MetaM α) : MetaM (Except Exception α) := fun mctx msref =>
  tryAllCore (x mctx msref)

/-- ONE run of the simp1 syntax `simpStx` on the main goal from the saved state, which is restored afterwards (also on
exception).  `v`: 0 = plain `Simp.mainCore` with the production methods (no wrapper, no phase hooks; only a 100 ms watcher
thread that sets the cancel token at the cap), 1 = the full instrument (wrapped hooks + 10 ms sampler), 2 = plain methods
under `trace.profiler` with threshold `profMs`.  The cap is cooperative (cancel token read by Lean's own `checkSystem`
points, plus the hook check in variant 1). -/
def runVariant (v : Nat) (tag : String) (simpStx : Syntax) (capMs throwAt profMs : Nat) (keep : Bool) : TacticM VRes := do
  let g ← getMainGoal
  let s ← saveState
  let tk ← IO.CancelToken.new
  let ph ← Phases.new
  let a ← Acc.new capMs throwAt ph
  let out ← IO.mkRef ({ tag } : VRes)
  let stRef ← IO.mkRef (none : Option Simp.State)
  try
    tryCatchRuntimeEx (do
      withTheReader Core.Context (fun c => { c with cancelTk? := some tk }) do
        g.withContext do
          let mc ← mkSimpContext simpStx (eraseLocal := false)
          let target ← instantiateMVars (← g.getType)
          let m0 := Simp.mkDefaultMethodsCore mc.simprocs
          let methods := if v == 1 then wrap a m0 else m0
          let opts : Options → Options := if v == 2 then (fun (o : Options) => ((o.set `trace.profiler true).set `trace.profiler.threshold profMs))
                      else id
          let hb0 ← IO.getNumHeartbeats
          let cpu0 ← cpuTicks
          ph.hbLast.set hb0
          let t ← IO.monoNanosNow
          a.t0.set t
          let wms := (← envNat "VED_DIAG_WATCH_MS" 100).toUInt32
          let th ← startSampler ph (if v == 1 then 10 else wms) t (capMs * 1000000) tk
          try
            match (← tryAllMeta (withOptions opts <| Simp.mainCore target mc.ctx (methods := methods))) with
            | .ok (r, st) =>
              stRef.set (some st)
              out.modify fun o => { o with steps := st.numSteps, res := if keep then some r else none }
            | .error e =>
              let r := if (← a.cancelled.get) || (← tk.isSet) then "cooperative_cancel"
                       else if e.isRuntime then "runtime_exception" else "simp_exception"
              out.modify fun o => { o with reason := r }
          finally
            let tt := (← IO.monoNanosNow) - t
            let hb1 ← IO.getNumHeartbeats
            let cpu1 ← cpuTicks
            discard <| ph.switch 0
            ph.stop.set true
            discard <| IO.wait th
            out.modify fun o => { o with totalNs := tt, hbDelta := hb1 - hb0, cpu := (cpu1.1 - cpu0.1, cpu1.2 - cpu0.2),
                                         tickN := 0, acc := if v == 1 then some a else none }) (fun e => do
      let r := if (← a.cancelled.get) || (← tk.isSet) then "cooperative_cancel"
               else if e.isRuntime then "runtime_exception" else "simp_exception"
      out.modify fun o => { o with reason := r })
    if (← a.cancelled.get) || (← tk.isSet) then
      out.modify fun o => { o with reason := "cooperative_cancel" }
    -- map sizes by one fold each, after the timing ended
    if let some st := (← stRef.get) then
      out.modify fun o => { o with cacheSz := st.cache.map₁.size + st.cache.map₂.foldl (fun n _ _ => n + 1) 0,
                                   congrSz := st.congrCache.size,
                                   dsimpSz := st.dsimpCache.size }
    if v == 2 then
      let m ← IO.mkRef ({} : Std.HashMap Name (Nat × Nat))
      for el in (← getTraceState).traces.toArray do
        discard <| walkTrace m el.msg
      let arr := (← m.get).toArray
      out.modify fun o => { o with prof := arr }
  finally
    resetTraceState
    s.restore
  return (← out.get)

/-- gated wall-clock marker around one variant (for matching external `perf` timestamps: CLOCK_MONOTONIC ns, and unix ms) -/
def wallLine (what tag : String) : IO Unit := do
  let mono ← IO.monoNanosNow
  let unix ← try
      let o ← IO.Process.output { cmd := "date", args := #["+%s%3N"] }
      pure o.stdout.trimAscii.toString
    catch _ => pure "unknown"
  diagLine s!"VED DIAG T {what} variant={tag} mono_ns={mono} unix_ms={unix}"

/-- all requested variants in order (`VED_DIAG_VARIANTS`, default "ab": a = plain, b = instrument, c = trace.profiler)
within a total wall budget; prints each variant's lines as it ends; returns the overall reason code -/
def measureAll (simpStx : Syntax) (capMs throwAt : Nat) : TacticM String := do
  let variants := (← IO.getEnv "VED_DIAG_VARIANTS").getD "ab"
  let budgetMs := (← envNat "VED_DIAG_BUDGET_S" 700) * 1000
  let profMs ← envNat "VED_DIAG_PROF_MS" 1000
  let keep := (← IO.getEnv "VED_DIAG_EQ").isSome
  let t00 ← IO.monoMsNow
  let mut results : Array VRes := #[]
  let mut final := "measured"
  for c in variants.toList do
    let left := budgetMs - min budgetMs ((← IO.monoMsNow) - t00)
    let tag := String.singleton c
    if left < 5000 then
      diagLine s!"VED DIAG [{tag}] reason=skipped_budget"
      final := "skipped_budget"
      continue
    let v := if c == 'a' then 0 else if c == 'b' then 1 else 2
    wallLine "start" tag
    let r ← runVariant v tag simpStx (min capMs left) throwAt profMs keep
    wallLine "end" tag
    reportVariant r
    if r.reason != "measured" then final := r.reason
    results := results.push r
  let ra? := results.toList.reverse.find? (·.tag == "a")
  let rb? := results.toList.reverse.find? (·.tag == "b")
  if let (some ra, some rb) := (ra?, rb?) then
    if ra.reason == "measured" && rb.reason == "measured" then
      let ov : Int := (Int.ofNat rb.totalNs - Int.ofNat ra.totalNs) / 1000
      let hbd : Int := (Int.ofNat rb.hbDelta - Int.ofNat ra.hbDelta) / 1000
      diagLine s!"VED DIAG overhead (b)-(a) totalUs={ov} aMs={ra.totalNs / 1000000} bMs={rb.totalNs / 1000000} percentOfA={if ra.totalNs == 0 then 0 else ov * 100 / Int.ofNat (ra.totalNs / 1000)} hbKdelta={hbd}"
    else
      diagLine s!"VED DIAG overhead (b)-(a) unknown (a={ra.reason} b={rb.reason})"
    if let (some x, some y) := (ra.res, rb.res) then
      diagLine s!"VED DIAG result a/b: sameExpr={x.expr == y.expr} sameProofPresence={x.proof?.isSome == y.proof?.isSome}"
  return final

/-- the production expansion of a `ved_loop_simp` syntax: the oldest macro registered for the kind -/
def prodExpansion (stx : Syntax) : TacticM Syntax := do
  let es := macroAttribute.getEntries (← getEnv) stx.getKind
  match es.getLast? with
  | some e => liftMacroM (e.value stx)
  | none => throwError "ved_diag: no production macro for {stx.getKind}"

initialize loopSeen : IO.Ref Nat ← IO.mkRef 0

/-- the cooperative wall time in ms: `VED_DIAG_CAP_MS`, else `VED_DIAG_CAP_S` (default 300; `VED_DIAG_CAP_MS` overrides, for controls) seconds -/
def capMs : IO Nat := do
  match (← IO.getEnv "VED_DIAG_CAP_MS").bind String.toNat? with
  | some ms => return ms
  | none => return (← envNat "VED_DIAG_CAP_S" 300) * 1000

syntax (name := diagSimp) "ved_diag_simp " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| ved_loop_simp [$ex,*] $[$loc]?) => `(tactic| ved_diag_simp [$ex,*] $[$loc]?)

@[tactic diagSimp] def evalDiagSimp : Tactic := fun stx => do
  -- the production syntax of this very call
  let orig := (stx.setKind ``Tools.VedU1Entry.vedLoopSimp).setArg 0 (mkAtom "ved_loop_simp ")
  let prod ← prodExpansion orig
  let isSimp1 := stx[4].isNone && (stx[2].getSepArgs.any fun s => (s.reprint.getD "").contains "memory_val_succ")
  if isSimp1 && (← IO.getEnv "VED_DIAG").isSome then
    let g ← getMainGoal
    let e0 ← g.withContext do instantiateMVars (← g.getType)
    if Tools.VedU1Loop.treeSizeVal e0 > (← envNat "VED_DIAG_MIN" 1000000) then
      let n ← loopSeen.modifyGet fun n => (n + 1, n + 1)
      if n == (← envNat "VED_DIAG_K" 1) then
        let reason ← measureAll prod (← capMs) (← envNat "VED_DIAG_THROW_AT" 0)
        if (← IO.getEnv "VED_DIAG_AFTER") == some "continue" then
          diagLine s!"VED DIAG continue diagnostic_only reason={reason}"
        else
          diagLine s!"VED DIAG STOP diagnostic_only reason={reason}"
          IO.Process.exit 3
  evalTactic prod

/-- control: the measurement on the current goal with `simp [lemmas]`; always continues (state restored) -/
elab "ved_diag_test " "[" ex:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let stx ← `(tactic| simp [$ex,*])
  let reason ← measureAll stx (← capMs) (← envNat "VED_DIAG_THROW_AT" 0)
  diagLine s!"VED DIAG test-continue diagnostic_only reason={reason}"

end Tools.VedMemCausalDiag
