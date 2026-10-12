import Tests.Compiler.MachineNoneStaleRefsTest
import Tests.Compiler.MemoHitCensusTest

/-! # A nested entry and its parent's `let` / loop / alias caches (finding F)

Uses NO declaration of a candidate: it builds on poc (`66766481`) and on the
isolated candidate `fix/nested-let-cache`; build it on both and diff the
lines. Whether the entry is the FIXED one is MEASURED (`NESTEDLET FIXED`,
below), and the assertions are made only when it is. Not in `Tests.AllTests`.
WRITTEN, not built.

Finding F (`docs/parallel/F-let-cache-leak.md`, measured on poc): a nested
entry clears `sparkleLetWireCache`, `sparkleLoopWireCache`, `sparkleWireCanon`
at its start and its `finally` restores only `sparkleFvarValueMap` and
`sparkleWireWidthCache`; the parent goes on with the CHILD's let-wire
entries, and a parent `let` with the key of a child `let` is emitted as
`assign _gen_t = _gen_t`.

## 0. Is the entry fixed?

The three refs are seeded at depth 1, one nested entry is run
(`synthesizeChild kCount`), and the refs are read again.

    NESTEDLET FIXED: nested entry restores let=<T/F> loop=<T/F> canon=<T/F> => fixed=<T/F>

## 1. The declarations

* `fMid` / `fTop` — the pair of the first observation (`WireRefsTest.dMid` /
  `dTop`, copied so that this file builds on poc): a register machine whose
  machine arm DECLINES (it calls a sequential one-output child), the child
  itself a legacy-route module, both with `let rs` and `let t := x + y`;
* `lPlain` — NO `circuit do`, no register, so no machine arm at all: a plain
  definition with the child call FIRST and `let t := x + y` after it, and a
  tuple projection meant to keep the gates away. Its route is printed;
* `fTop` once more through the entry with the front end OFF
  (`noFrontEnd`): the legacy route from depth 0, no machine arm anywhere in
  the parent — the case a rollback at a declined machine arm cannot cover.

    NESTEDLET <decl> <run>: route=<…> stmts=<n> insts=[…] selfAssign=[…] undriven=[…] outCone=[…] outReachesRegister=<T/F> outReachesInput=<T/F> endOrphans let=[…] loop=[…] canon=[…] top=<hash>
    NESTEDLET <decl> <run> STMT <i>: <statement>
    NESTEDLET <decl> real==cold <T/F>
    NESTEDLET <decl> TEXT: <the SystemVerilog of the design, as the design writer emits it>

`run`: `real` (`synthesizeCombinationalCore`, the entry), `cold`
(`cleanLegacy`: everything reset, front end off, `synthesizeFromConst` at
depth 1), `nofe` (`noFrontEnd`).

`endOrphans`: THE MODULE-LOCAL CHECK. At the end of the run, the wire names
the `let` cache, the loop cache and the alias map hold that the returned
module does not declare. The invariant it tests the end of: "at every point
of a module's legacy walk these refs hold only entries written while
building THIS module". Expected on poc for `fTop`: NOT empty (the child's
names); with the fix: empty.

Expected on poc (prediction for `lPlain`, measured for the `dTop` pair):
`fTop real: selfAssign=[_gen_rs, _gen_t] outReachesRegister=F`,
`lPlain real: selfAssign=[_gen_t]`. Expected with the fix: `selfAssign=[]`
everywhere, `fTop … outReachesRegister=T`, `real==cold T`.

## 2. The legacy-route population

The enumeration, cap and isolation of `MemoHitCensusTest` (as
`WireRefsTest` §3): each legacy-route candidate through the shipping entry.

    NESTEDLET LOCAL: <r> legacy-route runs returned (<k> not run: time budget); with child modules <b>; end orphans in <v> runs without a machine shape […] and in <v'> runs with one (logged only: a declined machine arm's harness) […]; self-assignments in <s> runs […]
    NESTEDLET DIGEST: <k> declarations, combined digest <H>
    NESTEDLET DIGEST, per declaration: …

Compare the `DIGEST` lines of poc and of the candidate: expected identical
(the first observation saw no legacy-route run with child modules among 84).
The machine- and mixed-route population: the `WIREWIDTH DIGEST` lines of
`MemoHitCensusTest`, built on both trees.

Asserted when `fixed=T`: no self-assignment in the rows of §1 that returned;
no end orphan in the `cold` / `nofe` rows (a `real` row of a declaration
with a machine shape may end with entries of the declined arm's HARNESS —
the business of the rollback at a declined arm, not of this fix: logged);
`fTop real==cold`; `fTop` `outReachesRegister`; in the population no
self-assignment, and no end orphan in a run without a machine shape. -/
namespace Tests.Compiler.NestedLetCacheTest
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Tests.Compiler.CallWidthHuntTest (Mod Dsn bs gatesOf resetRefs kCount)
open Tests.Compiler.MachineNoneStaleRefsTest (declW)
open Tests.Compiler.MachineFallThroughCensusTest (cleanLegacy noFrontEnd undriven)

/-- A sequential one-output child that itself goes through the legacy
translator (its machine arm declines: it calls the sequential `kCount`). -/
@[hardware_module]
def fMid (en : Signal defaultDomain Bool) (x y : Signal defaultDomain (BitVec 5)) :
    Signal defaultDomain (BitVec 5) :=
  circuit do
    let r ← Signal.reg 0#5
    let rs := (r : Signal defaultDomain (BitVec 5))
    let t := x + y
    let k := kCount en
    r <~ Signal.mux en (t + k) rs
    return rs

/-- Its parent, with the same `let`s over inputs of the same names. -/
def fTop (en : Signal defaultDomain Bool) (x y : Signal defaultDomain (BitVec 5)) :
    Signal defaultDomain (BitVec 5) :=
  circuit do
    let r ← Signal.reg 0#5
    let rs := (r : Signal defaultDomain (BitVec 5))
    let t := x + y
    let m := fMid en x y
    r <~ Signal.mux en (t + m) rs
    return rs

/-- No `circuit do`, no register: the child call first, then a `let` with
the key of the child's `let t`. -/
def lPlain (en : Signal defaultDomain Bool) (x y : Signal defaultDomain (BitVec 5)) :
    Signal defaultDomain (BitVec 5) :=
  let m := fMid en x y
  let t := x + y
  Signal.fst (bundle2 (t + m) t)

def fTopName : Name := `Tests.Compiler.NestedLetCacheTest.fTop
def fMidName : Name := `Tests.Compiler.NestedLetCacheTest.fMid
def lPlainName : Name := `Tests.Compiler.NestedLetCacheTest.lPlain
def kCountName : Name := `Tests.Compiler.CallWidthHuntTest.kCount

def oneLine (f : Std.Format) : String := (f.pretty 1000000).replace "\n" " "

def connStr (conns : List (String × Sparkle.IR.AST.Expr)) : String :=
  String.intercalate ", " (conns.map fun c => "." ++ c.1 ++ "(" ++ oneLine (repr c.2) ++ ")")

def stmtStr : Sparkle.IR.AST.Stmt → String
  | .assign l r => "assign " ++ l ++ " = " ++ oneLine (repr r)
  | .inst mn inm conns => "inst " ++ mn ++ " " ++ inm ++ " (" ++ connStr conns ++ ")"
  | s => oneLine (repr s)

def instNames (m : Mod) : List String :=
  m.body.filterMap fun s => match s with
    | .inst mn _ _ => some mn
    | _ => none

def selfAssigned (m : Mod) : List String :=
  m.body.filterMap fun s => match s with
    | .assign l (.ref r) => if l == r then some l else none
    | _ => none

def registerOuts (m : Mod) : List String :=
  m.body.filterMap fun s => match s with
    | .register o _ _ _ _ => some o
    | _ => none

/-- The names an assignment of `x` reads (empty when `x` is not assigned). -/
def assignReads (m : Mod) (x : String) : List String :=
  m.body.flatMap fun s => match s with
    | .assign l r => if l == x then Sparkle.IR.Reorder.refsOf r else []
    | _ => []

/-- The combinational cone of a name through the assignments: the names
reached, the start included (bounded by the number of statements). -/
def cone (m : Mod) (x : String) : List String :=
  let step (seen : List String) : List String :=
    (seen ++ seen.flatMap (assignReads m)).eraseDups
  (List.range (m.body.length + 1)).foldl (fun seen _ => step seen) [x]

/-- The wire names of the three refs that a module does not declare. -/
structure Orphans where
  letW : List String := []
  loopW : List String := []
  canon : List String := []

def Orphans.clean (o : Orphans) : Bool := o.letW.isEmpty && o.loopW.isEmpty && o.canon.isEmpty

/-- THE MODULE-LOCAL CHECK, at the moment it is called: every wire name the
`let` cache, the loop cache and the alias map hold is declared in `m`. -/
def orphansOf (m : Mod) : IO Orphans := do
  let a ← (sparkleLetWireCache.get : IO _)
  let b ← (sparkleLoopWireCache.get : IO _)
  let c ← (sparkleWireCanon.get : IO _)
  let undecl : String → Bool := fun x => (declW m x).isNone
  return {
    letW := ((a.toList.map fun p => p.2).filter undecl).eraseDups
    loopW := ((b.toList.map fun p => p.2).filter undecl).eraseDups
    canon := ((c.toList.flatMap fun p => [p.1, p.2]).filter undecl).eraseDups }

/-- What a row reports of a run. -/
structure Obs where
  res : Mod × Dsn
  orph : Orphans

def obsOf (x : MetaM (Mod × Dsn)) : MetaM (Option Obs) := do
  resetRefs
  sparkleSynthDepth.set 0
  let r : Option Obs ←
    try
      let res ← x
      let orph ← orphansOf res.1
      pure (some { res := res, orph := orph })
    catch _ => pure none
  sparkleSynthDepth.set 0
  resetRefs
  pure r

def routeStr (n : Name) : MetaM String := do
  try
    let g ← gatesOf n
    pure (if g.gate then "gate" else if g.mixed then "mixed"
      else if g.shape.isSome then "machine-shape" else "legacy-only")
  catch _ => pure "?"

/-- One row: the line, whether the run is free of self-assignments and
whether it is free of end orphans (`none`: the run threw), and the module. -/
def rowOf (n : Name) (tag : String) (stmts : Bool) (o? : Option Obs) :
    MetaM (Option (Bool × Bool) × Option Mod) := do
  let route ← routeStr n
  match o? with
  | none =>
    logInfo m!"NESTEDLET {n} {tag}: route={route} the run threw"
    pure (none, none)
  | some o =>
    let m := o.res.1
    let outName := (m.outputs.head?.map (·.name)).getD "out"
    let cn := cone m outName
    let regs := registerOuts m
    let ins := m.inputs.map (·.name)
    let reachesReg := cn.any fun x => regs.contains x
    let reachesIn := cn.any fun x => ins.contains x
    let sa := selfAssigned m
    logInfo m!"NESTEDLET {n} {tag}: route={route} stmts={m.body.length} insts={instNames m} selfAssign={sa} undriven={undriven m} outCone={cn} outReachesRegister={bs reachesReg} outReachesInput={bs reachesIn} endOrphans let={o.orph.letW} loop={o.orph.loopW} canon={o.orph.canon} top={hash (repr m).pretty}"
    if stmts then
      let mut i : Nat := 0
      for s in m.body do
        logInfo m!"NESTEDLET {n} {tag} STMT {i}: {stmtStr s}"
        i := i + 1
    pure (some (sa.isEmpty, o.orph.clean), some m)

/-- The design of a result, the top included. -/
def designOf (r : Mod × Dsn) : Dsn :=
  if r.2.modules.any (·.name == r.1.name) then r.2 else r.2.addModule r.1

/-- ONE isolated, bounded run of the shipping entry core, with the check at
its end (as `MemoHitCensusTest.runObserved`, without the child observer). -/
def runIsolated (n : Name) : MetaM (Option Obs) := do
  let saved ← Meta.saveState
  sparkleSynthDepth.set 0
  sparkleCallCounter.set 0
  let r ← tryCatchRuntimeEx
    (do
      let md ← withTheReader Core.Context
        (fun c => { c with maxHeartbeats :=
          Sparkle.Tests.Compiler.MemoHitCensusTest.runHeartbeats * 1000 }) <|
        withCurrHeartbeats <| synthesizeCombinationalCore n [] false
      let orph ← orphansOf md.1
      pure (some ({ res := md, orph := orph } : Obs)))
    (fun _ => pure none)
  saved.restore
  sparkleSynthDepth.set 0
  pure r

/-- Wall-clock budget of the population runs, in milliseconds. -/
def localBudgetMs : Nat := 300000

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  -- §0 is the entry fixed?
  resetRefs
  sparkleLetWireCache.set (({} : Std.HashMap String String).insert "seed:let" "seed_let_wire")
  sparkleLoopWireCache.set (({} : Std.HashMap String String).insert "seed:loop" "seed_loop_wire")
  sparkleWireCanon.set (({} : Std.HashMap String String).insert "seed_canon_a" "seed_canon_b")
  sparkleSynthDepth.set 1
  let nestedRan : Bool ←
    try
      let _ ← synthesizeChild kCountName
      pure true
    catch _ => pure false
  sparkleSynthDepth.set 0
  let la := (← (sparkleLetWireCache.get : IO _)).toList
  let lb := (← (sparkleLoopWireCache.get : IO _)).toList
  let lc := (← (sparkleWireCanon.get : IO _)).toList
  let okLet : Bool := la == [("seed:let", "seed_let_wire")]
  let okLoop : Bool := lb == [("seed:loop", "seed_loop_wire")]
  let okCanon : Bool := lc == [("seed_canon_a", "seed_canon_b")]
  let fixed : Bool := nestedRan && okLet && okLoop && okCanon
  resetRefs
  logInfo m!"NESTEDLET FIXED: nested entry ran={bs nestedRan} restores let={bs okLet} loop={bs okLoop} canon={bs okCanon} => fixed={bs fixed} (assertions are made only when it is T)"
  let mut failures : Array String := #[]
  -- §1 the declarations
  let fReal ← obsOf (synthesizeCombinationalCore fTopName [] false)
  let (fRealOk, fRealM) ← rowOf fTopName "real" true fReal
  let fCold ← obsOf (do
    let g ← gatesOf fTopName
    cleanLegacy fTopName g.ec)
  let (fColdOk, fColdM) ← rowOf fTopName "cold" true fCold
  let fNofe ← obsOf (noFrontEnd fTopName)
  let (fNofeOk, _) ← rowOf fTopName "nofe" true fNofe
  let sameRC : String := match fRealM, fColdM with
    | some a, some b => bs (a == b)
    | _, _ => "err"
  logInfo m!"NESTEDLET {fTopName} real==cold {sameRC}"
  let mReal ← obsOf (synthesizeCombinationalCore fMidName [] false)
  let (mRealOk, _) ← rowOf fMidName "real" false mReal
  let pReal ← obsOf (synthesizeCombinationalCore lPlainName [] false)
  let (pRealOk, _) ← rowOf lPlainName "real" true pReal
  let pNofe ← obsOf (noFrontEnd lPlainName)
  let (pNofeOk, _) ← rowOf lPlainName "nofe" true pNofe
  for (tag, ok) in [("fTop real", fRealOk), ("fTop cold", fColdOk), ("fTop nofe", fNofeOk),
      ("fMid real", mRealOk), ("lPlain real", pRealOk), ("lPlain nofe", pNofeOk)] do
    match ok with
    | some (selfOk, orphOk) =>
      if !selfOk then failures := failures.push (tag ++ ": self-assignment")
      -- a run whose parent went through a machine arm may end with the
      -- HARNESS's entries (another matter: the rollback at a declined arm);
      -- the end orphans are asserted where no machine arm ran in the parent
      if !orphOk && (tag.endsWith "cold" || tag.endsWith "nofe") then
        failures := failures.push (tag ++ ": end orphans")
    | none => pure ()
  if sameRC != "T" then failures := failures.push "fTop real==cold"
  match fRealM with
  | some m =>
    let outName := (m.outputs.head?.map (·.name)).getD "out"
    if !((cone m outName).any fun x => (registerOuts m).contains x) then
      failures := failures.push "fTop real: out does not reach a register"
  | none => failures := failures.push "fTop real threw"
  -- the texts
  for (n, o?) in [(fTopName, fReal), (lPlainName, pReal)] do
    match o? with
    | some o =>
      let text := Sparkle.Backend.Verilog.toVerilogDesignChecked (designOf o.res)
      logInfo m!"NESTEDLET {n} TEXT:\n{text}"
    | none => pure ()
  -- §2 the legacy-route population
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
  let t0 ← IO.monoMsNow
  let mut returned : Nat := 0
  let mut notRun : Nat := 0
  let mut withKids : Nat := 0
  let mut orphBad : Array String := #[]
  let mut orphShape : Array String := #[]
  let mut selfBad : Array String := #[]
  let mut digests : Array String := #[]
  let own : List Name := [fTopName, fMidName, lPlainName]
  for n in cands do
    if own.contains n then continue
    let route ← Sparkle.Tests.Compiler.MemoHitCensusTest.routeOf n
    if route == "legacy" then
      let now ← IO.monoMsNow
      if now - t0 > localBudgetMs then
        notRun := notRun + 1
      else
        let r ← try runIsolated n catch _ => pure none
        match r with
        | some o =>
          returned := returned + 1
          digests := digests.push s!"{n}={Sparkle.Tests.Compiler.MemoHitCensusTest.digest o.res}"
          if !o.res.2.modules.isEmpty then withKids := withKids + 1
          if !o.orph.clean then
            let hasShape : Bool ←
              try
                let g ← gatesOf n
                pure g.shape.isSome
              catch _ => pure true
            let line := s!"{n}: let={o.orph.letW} loop={o.orph.loopW} canon={o.orph.canon}"
            if hasShape then orphShape := orphShape.push line else orphBad := orphBad.push line
          let sa := selfAssigned o.res.1
          if !sa.isEmpty then selfBad := selfBad.push s!"{n}: {sa}"
        | none => pure ()
  logInfo m!"NESTEDLET LOCAL: {returned} legacy-route runs returned ({notRun} not run: time budget); with child modules {withKids}; end orphans in {orphBad.size} runs without a machine shape {orphBad.toList.take 10} and in {orphShape.size} runs with one (logged only: a declined machine arm's harness) {orphShape.toList.take 10}; self-assignments in {selfBad.size} runs {selfBad.toList.take 10}"
  let total : UInt64 := hash digests.toList
  logInfo m!"NESTEDLET DIGEST: {digests.size} declarations, combined digest {total}"
  logInfo m!"NESTEDLET DIGEST, per declaration: {String.intercalate " " digests.toList}"
  resetRefs
  logInfo m!"NESTEDLET: fixed={bs fixed}; failing rows {failures.toList}"
  if fixed then
    if !failures.isEmpty then
      throwError "NESTEDLET: the nested entry restores the parent's caches, but these rows are not clean: {failures.toList}"
    if !orphBad.isEmpty || !selfBad.isEmpty then
      throwError "NESTEDLET: with the fixed entry, legacy-route runs of the population end with foreign cache entries {orphBad.toList.take 10} or self-assignments {selfBad.toList.take 10}"

end Tests.Compiler.NestedLetCacheTest
