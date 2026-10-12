import Sparkle
import Sparkle.IR.ReorderInvariance
import IP.Net.IPv4
import IP.Net.TCP
import IP.Net.Ethernet
import IP.Net.HTTP
import IP.BitNet.SignalHelpers
import IP.Crypto.SHA256
import IP.Video.H264.Quant
import IP.RV32.SoC

/-! # Is the legacy arm's memo read ever answered? (logs only; never throws)

`synthesizeFromConst` reads `sparkleSubModuleCache` in its legacy arm
(`Sparkle/Compiler/Elab.lean` 5309–5313) and returns the stored result on a
hit. Reading the program (docs/parallel/B-memo.md §1c) suggests the hit is
unreachable on designs without a by-name cycle. This file MEASURES it.

**How a hit is observed.** The entry builds its logger itself (from the
environment variable `SPARKLE_PROFILE`): a caller cannot pass one, so the
`MEMO HIT` log line cannot be captured from inside the process. Instead every
NESTED synthesis is observed where it starts: all of them go through the ref
`sparkleChildSynth` (= `synthesizeChild`), which this test replaces, for the
duration of one run, by a wrapper that looks at the two caches and then calls
the REAL `synthesizeChild`. The entry, the translator and the memo are the
real ones.

At a nested request for `n` the wrapper records

* `inCache` — `sparkleChildCache` holds `n` (the request is answered there;
  `synthesizeFromConst` does not run);
* `inMemo` — `sparkleSubModuleCache` holds `n`;
* `cycle` — a synthesis of `n` is in progress (the wrapper's own stack, with
  the outermost declaration at its bottom);
* the route the entry's pure gates give `n`'s entry constant.

**Why this decides the question.** A read of the memo returns an entry for
`n` only if one is there at the read. Entries for `n` are written only by
runs of `synthesizeFromConst` on `n`; the memo never shrinks inside one
depth-0 run. So a hit in a nested run on `n` needs, at its request, `inMemo`
(an earlier run on `n` completed) or `cycle` (one is in progress and
completes before the read). A hit in the OUTERMOST run needs a nested request
for its own name: a `cycle`. Hence:

* `HIT` = a request with `¬inCache ∧ inMemo` whose constant the gates route
  to `legacy` — the run reaches the read with the entry present: a certain
  hit;
* `POSSIBLE` = `¬inCache ∧ inMemo` on the `machine` route (a hit iff the
  machine synthesis declines and falls through);
* `CYCLE` = a request for a name in progress;
* all three zero ⇒ no memo hit happened in the run.

For a direct check outside the process: run with `SPARKLE_PROFILE=1` and
count `MEMO HIT` lines in `/tmp/sparkle-profile.log`.

**Population.** The candidates of `Tests/Compiler/LegacyArmCensusTest.lean`
(Signal-valued definitions of the imported `IP` / `Examples` / `Tests`
modules, in name order, cap 400), ALL routes except `certified` (a
certified-route declaration has no child) — legacy-route first, then machine,
then mixed: the instance parents are among the last two. Each run is isolated
as in that census. `Tests/Compiler/HierBindsCensusTest.lean` does not exist
on this branch; its instance parents are not added.

**Undeclared reads.** `WIREWIDTH UNDECLARED` counts, in the emitted modules,
assignment reads of a name the module does not declare. Every caller of
`getWireWidth` emits an assignment reading the wire whose width it asked
for, so 0 means: no kept statement comes from a width query on an undeclared
name (the case in which a builder-first lookup still falls back to the
cache).

**Digests.** For every RETURNED declaration a digest of the
module and of the design. The line `WIREWIDTH DIGEST` is meant to be diffed
between a build WITHOUT and WITH the wire-width candidate
(docs/parallel/B-wirewidth.md): equal lines ⇒ no emitted module of the
population changes. -/

open Lean Meta Sparkle.Compiler.Elab

namespace Sparkle.Tests.Compiler.MemoHitCensusTest

/-- The census never examines more than this many definitions. -/
def cap : Nat := 400

/-- Heartbeat bound of one run, in thousands. -/
def runHeartbeats : Nat := 200000

/-- Wall-clock budget of all runs, in milliseconds. -/
def runBudgetMs : Nat := 360000

/-- What the wrapper saw. -/
structure Obs where
  requests : Nat := 0
  cacheAnswers : Nat := 0
  hits : Array String := #[]
  possible : Array String := #[]
  cycles : Array String := #[]

/-- The route the entry's pure gates give `n`'s entry constant. -/
def routeOf (n : Name) : MetaM String := do
  try
    let env ← getEnv
    let ci ← getConstInfo n
    let ec := entryConst true false [] ci (instancePredicate env) (userInliner env)
      (structEnv env)
    if (certifiedShape? false [] ec).isSome then pure "certified"
    else if (mixedCertifiedShape? false [] ec (instancePredicate env)).isSome then pure "mixed"
    else if (machineShape? false [] ec (structEnv env)).isSome then pure "machine"
    else pure "legacy"
  catch _ => pure "unknown"

/-- The observed child entry: look, then run the REAL `synthesizeChild`. -/
def observedChild (obs : IO.Ref Obs) (stack : IO.Ref (List Name)) (top : Name) (n : Name) :
    MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
  let childCache ← (sparkleChildCache.get : IO _)
  let memo ← (sparkleSubModuleCache.get : IO _)
  let inCache : Bool := childCache.contains n
  let inMemo : Bool := memo.contains n
  let st ← (stack.get : IO _)
  let cyc : Bool := st.contains n
  let route ← routeOf n
  let tag : String := s!"{n} (in the run of {top}, route {route})"
  (obs.modify fun o =>
    { o with
      requests := o.requests + 1
      cacheAnswers := if inCache then o.cacheAnswers + 1 else o.cacheAnswers
      hits := if !inCache && inMemo && route == "legacy" then o.hits.push tag else o.hits
      possible :=
        if !inCache && inMemo && route != "legacy" then o.possible.push tag else o.possible
      cycles := if cyc then o.cycles.push tag else o.cycles } : IO Unit)
  (stack.modify (fun l => n :: l) : IO Unit)
  try
    let r ← synthesizeChild n
    (stack.modify (fun l => l.tail) : IO Unit)
    pure r
  catch ex =>
    (stack.modify (fun l => l.tail) : IO Unit)
    throw ex

/-- The digest of a result. -/
def digest (r : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) : String :=
  let all : UInt64 := hash (r.2.modules.map fun x => (repr x).pretty)
  s!"{hash (repr r.1).pretty}/{all}"

/-- The names the assignments of `m` read that `m` does not declare (clock
and reset apart: they are added when the module is finished). -/
def undeclaredReads (m : Sparkle.IR.AST.Module) : List String :=
  let declared : List String := (m.wires ++ m.inputs ++ m.outputs).map (·.name)
  (m.body.flatMap Sparkle.IR.Reorder.stmtReads).filter fun x =>
    !declared.contains x && x != "clk" && x != "rst"

/-- The undeclared reads of every module of a result, tagged by the module. -/
def undeclaredOf (r : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) : List String :=
  (r.1 :: r.2.modules).flatMap fun m => (undeclaredReads m).map fun x => s!"{m.name}:{x}"

/-- ONE run of the shipping entry on `n`, isolated and bounded, with the
child entry observed. `none`: the run did not return. Otherwise the digest
and the undeclared reads of the emitted modules. -/
def runObserved (obs : IO.Ref Obs) (n : Name) : MetaM (Option (String × List String)) := do
  let saved ← Meta.saveState
  sparkleSynthDepth.set 0
  sparkleCallCounter.set 0
  let stack ← IO.mkRef ([n] : List Name)
  let old ← (sparkleChildSynth.get : IO _)
  (sparkleChildSynth.set (some (observedChild obs stack n)) : IO Unit)
  let r ← tryCatchRuntimeEx
    (do
      let md ← withTheReader Core.Context
        (fun c => { c with maxHeartbeats := runHeartbeats * 1000 }) <|
        withCurrHeartbeats <| synthesizeCombinationalCore n [] false
      pure (some (digest md, undeclaredOf md)))
    (fun _ => pure none)
  (sparkleChildSynth.set old : IO Unit)
  saved.restore
  sparkleSynthDepth.set 0
  pure r

/-- At most `k` entries of a list of tags, with the total. -/
def showSome (xs : Array String) (k : Nat) : String :=
  s!"{xs.size} [{String.intercalate "; " (xs.toList.take k)}]"

run_cmd Lean.Elab.Command.liftTermElabM do
  try
    let env ← getEnv
    let roots : List Name := [`IP, `Examples, `Tests]
    let all : Array Name := env.constants.fold (fun acc n ci =>
      match ci with
      | .defnInfo _ =>
        let root : Option Name :=
          (env.getModuleIdxFor? n).bind fun idx =>
            (env.header.moduleNames[idx.toNat]?).map (·.getRoot)
        let inRoots : Bool := match root with
          | some r => roots.contains r
          | none => false
        if inRoots && !n.isInternal &&
            ci.type.getForallBody.getAppFn.isConstOf ``Sparkle.Core.Signal.Signal then
          acc.push n
        else acc
      | _ => acc) #[]
    let sorted := all.qsort (fun a b => decide (a.toString < b.toString))
    let cands := sorted.extract 0 cap
    -- by route: legacy first, then machine, then mixed (certified: no child)
    let mut legacy : Array Name := #[]
    let mut machine : Array Name := #[]
    let mut mixed : Array Name := #[]
    for n in cands do
      let r ← routeOf n
      if r == "legacy" then legacy := legacy.push n
      else if r == "machine" then machine := machine.push n
      else if r == "mixed" then mixed := mixed.push n
    let order := legacy ++ machine ++ mixed
    let obs ← IO.mkRef ({} : Obs)
    let t0 ← IO.monoMsNow
    let mut runs : Nat := 0
    let mut returned : Nat := 0
    let mut notRun : Nat := 0
    let mut digests : Array String := #[]
    let mut undeclared : Array String := #[]
    for n in order do
      let now ← IO.monoMsNow
      if now - t0 > runBudgetMs then
        notRun := notRun + 1
      else
        runs := runs + 1
        let r ← try runObserved obs n catch _ => pure none
        match r with
        | some (dg, und) =>
          returned := returned + 1
          digests := digests.push s!"{n}={dg}"
          undeclared := undeclared ++ und.toArray
        | none => pure ()
    let t1 ← IO.monoMsNow
    let o ← (obs.get : IO _)
    logInfo m!"MEMOHIT CENSUS: {runs} runs of the shipping entry ({legacy.size} legacy-route, {machine.size} machine-route, {mixed.size} mixed-route candidates; {returned} returned; {notRun} not run: time budget; {t1 - t0} ms); nested requests {o.requests}, answered by sparkleChildCache {o.cacheAnswers}; hits {showSome o.hits 20}; possible hits (memo entry present, machine or mixed route) {showSome o.possible 20}; by-name cycles {showSome o.cycles 20}"
    logInfo m!"WIREWIDTH UNDECLARED: in the emitted modules of the {returned} returned declarations, assignment reads of a name the module does not declare (clk / rst apart): {showSome undeclared 20} (every caller of getWireWidth emits an assignment that reads the wire it asked the width of: 0 here means no such caller asked for a name its module does not declare, in a statement that was kept)"
    let total : UInt64 := hash digests.toList
    logInfo m!"WIREWIDTH DIGEST: {digests.size} returned declarations, combined digest {total}"
    logInfo m!"WIREWIDTH DIGEST, per declaration (name=top/design): {String.intercalate " " digests.toList}"
  catch ex =>
    logInfo m!"MEMOHIT CENSUS: harness error: {ex.toMessageData}"

end Sparkle.Tests.Compiler.MemoHitCensusTest
