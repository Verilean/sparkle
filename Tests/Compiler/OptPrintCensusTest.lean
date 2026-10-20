import Tests.Compiler.MemoHitCensusTest
import Tests.Compiler.OptPrintGuardDefs

/-! # A census of the two candidate guards over the test corpus (round par/b-19)

LOG ONLY: asserts nothing, proves nothing, never throws. Target-built, NOT
for `Tests.AllTests`. WRITTEN, NOT BUILT. The compiler is not changed: both
candidate guards are computed here (`OptPrintGuardDefs`).

**Population.** Exactly the enumeration of `MemoHitCensusTest` (the same
expression over the same imports — this file imports that test and one file
without Signal-valued definitions, nothing else): the Signal-valued
definitions of the imported `IP` / `Examples` / `Tests` modules, in name
order, cap `MemoHitCensusTest.cap`; run in its order — legacy, machine,
mixed route — and, AFTER those (so that its counts stay comparable),
the certified-route candidates it leaves out. Each run is isolated and
bounded as there (`runHeartbeats`, wall-clock `runBudgetMs`).

**What one run gives.** `synthesizeCombinationalCore n [] false`, then
`OptPrintGuardDefs.shippedDesign`: the zero-width cleanup and the checked
merge of the top, and the design of `synthesizeHierarchical` (the top
appended when absent). A declaration whose design fails the name validation
(`validateDesignNames`: the command would throw) is counted and left out.

**The optimizer guard** (`Sparkle/IR/RefineCheck.lean` 385–386:
`if refineCheck m o then o else m` → `if refineCheck m o && printOk o …`).
For EVERY module `x` of every design (an occurrence: a child module is
counted once per design it is in), `o := optimizeModule x`:

* (a) instance-free; of them by branch of `checkedOptimize`: `simple`
  (optCheck), `seq` (refineCheck: the branch of the guard), `other`;
* (b) of (a): `o != x`;
* (c) of (b): `refineCheck x o = true`;
* (d) of (c): `printOk o = false` — listed: declaration, module, branch,
  whether it is the module the design writer optimizes (`top`: its name is
  the design's `topModule`), `printOk x`;
* `fires`: (d) in branch `seq` on a `top` — the modules whose printed text
  the guard changes. (`refineCheck` implies both bodies are assign +
  register, so (c) lies in `simple ∪ seq`; in `simple` the writer's test is
  `optCheck`, not `refineCheck`. A (d) module that is not a `top` is printed
  unoptimized today: the guard does not touch it.)

A module with more than `SPARKLE_OPTPRINT_MAXSTMTS` (default 3000)
statements is not evaluated (`refineCheck` builds tree normal forms); a
declaration whose TOP is that large is left out of the digests too. Counted.

**Digests.** Per declaration the hash of `toVerilogDesignChecked design`
(the text shipped today) and of `guardedText design` (the text that WOULD be
shipped under the guard); the two combined digests; the declarations whose
text changes.

**The merge guard** (`mergeChecked`, `RefineCheck.lean` 270: the candidate
conjunct `!(r.body.all isAssign)`, `docs/parallel/A-leaf-entry-2.md` §1.4).
On each declaration's top BEFORE the merge (children come out of their own
full entry already merged: each is measured where it is itself a
candidate): bodies not assignment-only, merges that change the module,
merges accepted today, and `fires` — accepted today with an assignment-only
result. PREDICTED 0 on elaborator output.

    OPTPRINT CENSUS: …
    OPTPRINT CENSUS BY ROUTE <route>: …
    OPTPRINT D <i>: decl=<…> module=<…> branch=<…> top=<T/F> printOk(m)=<T/F>
    OPTPRINT DIGEST today: <k> declarations, combined digest <H>
    OPTPRINT DIGEST guarded: <k> declarations, combined digest <H'>
    OPTPRINT DIGEST changed: <c> declarations […]
    OPTPRINT DIGEST, per declaration (name=today/guarded): …
    OPTPRINT MERGE: … -/

open Lean Meta Sparkle.Compiler.Elab

namespace Tests.Compiler.OptPrintCensusTest
open Tests.Compiler.OptPrintGuardDefs

/-- One module occurrence. -/
structure ModRow where
  decl : String
  route : String
  modName : String
  isTop : Bool
  free : Bool
  evaluated : Bool
  branch : String
  differs : Bool
  rc : Bool
  pm : Bool
  po : Bool

/-- One declaration. -/
structure DeclRow where
  decl : String
  route : String
  mods : Nat
  topFound : Bool
  today : UInt64
  guarded : UInt64
  changed : Bool
  mNonAssign : Bool
  mChanged : Bool
  mAccepted : Bool
  mFires : Bool

/-- ONE isolated, bounded run of the shipping entry core (as
`NestedLetCacheTest.runIsolated` / `MemoHitCensusTest.runObserved`, without
an observer). -/
def runCore (n : Name) : MetaM (Option (Mod × Dsn)) := do
  let saved ← Meta.saveState
  sparkleSynthDepth.set 0
  sparkleCallCounter.set 0
  let r ← tryCatchRuntimeEx
    (do
      let md ← withTheReader Core.Context
        (fun c => { c with maxHeartbeats :=
          Sparkle.Tests.Compiler.MemoHitCensusTest.runHeartbeats * 1000 }) <|
        withCurrHeartbeats <| synthesizeCombinationalCore n [] false
      pure (some md))
    (fun _ => pure none)
  saved.restore
  sparkleSynthDepth.set 0
  pure r

def rowOf (decl route : String) (topName : String) (maxStmts : Nat) (x : Mod) : ModRow :=
  let free : Bool := instFree x
  let ev : Bool := free && decide (x.body.length ≤ maxStmts)
  if ev then
    let ob := optObs x
    { decl := decl, route := route, modName := x.name, isTop := x.name == topName, free := free
      evaluated := true, branch := ob.branch, differs := ob.differs, rc := ob.rc, pm := ob.pm
      po := ob.po }
  else
    { decl := decl, route := route, modName := x.name, isTop := x.name == topName, free := free
      evaluated := false, branch := if free then "notEvaluated" else "inst", differs := false
      rc := false, pm := false, po := false }

def isD (r : ModRow) : Bool := r.free && r.evaluated && r.differs && r.rc && !r.po

def firesOpt (r : ModRow) : Bool := isD r && r.branch == "seq" && r.isTop

def countP (rows : Array ModRow) (p : ModRow → Bool) : Nat := (rows.filter p).size

/-- The (a)–(d) counts of a set of module rows, as text. -/
def countsText (rows : Array ModRow) : String :=
  let a := countP rows fun r => r.free
  let aE := countP rows fun r => r.free && r.evaluated
  let aSimple := countP rows fun r => r.free && r.evaluated && r.branch == "simple"
  let aSeq := countP rows fun r => r.free && r.evaluated && r.branch == "seq"
  let aOther := countP rows fun r => r.free && r.evaluated && r.branch == "other"
  let b := countP rows fun r => r.free && r.evaluated && r.differs
  let bSeq := countP rows fun r => r.free && r.evaluated && r.differs && r.branch == "seq"
  let c := countP rows fun r => r.free && r.evaluated && r.differs && r.rc
  let cSeq := countP rows fun r => r.free && r.evaluated && r.differs && r.rc && r.branch == "seq"
  let d := countP rows isD
  let dSeq := countP rows fun r => isD r && r.branch == "seq"
  let f := countP rows firesOpt
  let dPm := countP rows fun r => isD r && r.pm
  s!"module occurrences {rows.size}; (a) instance-free {a} (evaluated {aE}: simple {aSimple}, seq {aSeq}, other {aOther}; not evaluated, too large {a - aE}); (b) candidate differs {b} (seq {bSeq}); (c) of (b) refineCheck true {c} (seq {cSeq}); (d) of (c) printOk of the candidate false {d} (seq {dSeq}; of (d) with printOk of the module itself true {dPm}); fires = (d) in seq on the design's top, i.e. printed text changes under the guard {f}"

run_cmd Lean.Elab.Command.liftTermElabM do
  try
    let env ← getEnv
    let maxStmts : Nat :=
      ((← IO.getEnv "SPARKLE_OPTPRINT_MAXSTMTS").bind String.toNat?).getD 3000
    -- the enumeration of `MemoHitCensusTest`, verbatim
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
    let cands := sorted.extract 0 Sparkle.Tests.Compiler.MemoHitCensusTest.cap
    let mut legacy : Array (Name × String) := #[]
    let mut machine : Array (Name × String) := #[]
    let mut mixed : Array (Name × String) := #[]
    let mut certified : Array (Name × String) := #[]
    let mut unknown : Nat := 0
    for n in cands do
      let r ← Sparkle.Tests.Compiler.MemoHitCensusTest.routeOf n
      if r == "legacy" then legacy := legacy.push (n, r)
      else if r == "machine" then machine := machine.push (n, r)
      else if r == "mixed" then mixed := mixed.push (n, r)
      else if r == "certified" then certified := certified.push (n, r)
      else unknown := unknown + 1
    let order := legacy ++ machine ++ mixed ++ certified
    let t0 ← IO.monoMsNow
    let mut runs : Nat := 0
    let mut returned : Nat := 0
    let mut notRun : Nat := 0
    let mut nameRejected : Array String := #[]
    let mut bigTop : Array String := #[]
    let mut modRows : Array ModRow := #[]
    let mut declRows : Array DeclRow := #[]
    for (n, route) in order do
      let now ← IO.monoMsNow
      if now - t0 > Sparkle.Tests.Compiler.MemoHitCensusTest.runBudgetMs then
        notRun := notRun + 1
      else
        runs := runs + 1
        let r ← try runCore n catch _ => pure none
        match r with
        | none => pure ()
        | some md =>
          returned := returned + 1
          let p := shippedDesign md
          let nameOk : Bool ←
            try
              let _ ← validateDesignNames p.design
              pure true
            catch _ => pure false
          if !nameOk then
            nameRejected := nameRejected.push (toString n)
          else if decide (p.top.body.length > maxStmts) || decide (p.pre.body.length > maxStmts) then
            bigTop := bigTop.push s!"{n} ({p.top.body.length} statements)"
          else
            let topName := p.design.topModule
            for x in p.design.modules do
              modRows := modRows.push (rowOf (toString n) route topName maxStmts x)
            let today : String := Sparkle.Backend.Verilog.toVerilogDesignChecked p.design
            let guarded : String := guardedText p.design
            let mo := mergeObs p.pre
            declRows := declRows.push
              { decl := toString n, route := route, mods := p.design.modules.length
                topFound := p.design.modules.any (fun x => x.name == topName)
                today := hash today, guarded := hash guarded, changed := today != guarded
                mNonAssign := mo.nonAssign, mChanged := mo.changed, mAccepted := mo.accepted
                mFires := mo.fires }
    let t1 ← IO.monoMsNow
    logInfo m!"OPTPRINT CENSUS: {cands.size} candidates ({legacy.size} legacy-route, {machine.size} machine-route, {mixed.size} mixed-route, {certified.size} certified-route, {unknown} of unknown route: not run); {runs} runs of the shipping entry, {returned} returned, {notRun} not run: time budget; {t1 - t0} ms; left out: name validation fails {nameRejected.size} {nameRejected.toList.take 10}, top over {maxStmts} statements {bigTop.size} {bigTop.toList.take 10}; measured declarations {declRows.size}, of them without a module named by the design's topModule field (the writer optimizes nothing) {(declRows.filter fun r => !r.topFound).size}. ALL ROUTES: {countsText modRows}"
    for route in ["legacy", "machine", "mixed", "certified"] do
      logInfo m!"OPTPRINT CENSUS BY ROUTE {route}: declarations {(declRows.filter fun r => r.route == route).size}; {countsText (modRows.filter fun r => r.route == route)}"
    let dRows := modRows.filter isD
    let mut i : Nat := 0
    for r in dRows do
      logInfo m!"OPTPRINT D {i}: decl={r.decl} route={r.route} module={r.modName} branch={r.branch} top={tf r.isTop} printOk(m)={tf r.pm} fires={tf (firesOpt r)}"
      i := i + 1
    let dNames : List String := (dRows.toList.map fun r => r.modName).eraseDups
    logInfo m!"OPTPRINT D TOTAL: {dRows.size} occurrences, {dNames.length} distinct module names"
    -- the three-of-four population of `MemoHitCensusTest` first, then all
    let memoRows := declRows.filter fun r => r.route != "certified"
    for (tag, rs) in [("legacy+machine+mixed (the MemoHitCensusTest population)", memoRows),
        ("all four routes", declRows)] do
      let todayAll : UInt64 := hash (rs.toList.map fun r => s!"{r.decl}={r.today}")
      let guardAll : UInt64 := hash (rs.toList.map fun r => s!"{r.decl}={r.guarded}")
      let changed := rs.filter fun r => r.changed
      logInfo m!"OPTPRINT DIGEST today [{tag}]: {rs.size} declarations, combined digest {todayAll}"
      logInfo m!"OPTPRINT DIGEST guarded [{tag}]: {rs.size} declarations, combined digest {guardAll}"
      logInfo m!"OPTPRINT DIGEST changed [{tag}]: {changed.size} declarations {(changed.toList.map fun r => r.decl).take 40}"
    logInfo m!"OPTPRINT DIGEST, per declaration (name=today/guarded): {String.intercalate " " (declRows.toList.map fun r => s!"{r.decl}={r.today}/{r.guarded}")}"
    let mNon := declRows.filter fun r => r.mNonAssign
    let mChg := declRows.filter fun r => r.mNonAssign && r.mChanged
    let mAcc := declRows.filter fun r => r.mNonAssign && r.mChanged && r.mAccepted
    let mFire := declRows.filter fun r => r.mFires
    logInfo m!"OPTPRINT MERGE: tops measured {declRows.size} (before the merge, after the zero-width cleanup); body not assignment-only {mNon.size}; of them the merge changes the module {mChg.size}; of them accepted today (refineCheck && masksKept && printOk) {mAcc.size}; FIRES (accepted today and the merged body is assignment-only: the candidate conjunct would refuse it) {mFire.size} {(mFire.toList.map fun r => r.decl).take 20}"
  catch ex =>
    logInfo m!"OPTPRINT CENSUS: harness error: {ex.toMessageData}"

end Tests.Compiler.OptPrintCensusTest
