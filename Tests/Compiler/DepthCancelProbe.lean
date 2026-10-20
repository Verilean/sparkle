import Sparkle

/-! # PROBE (logs only): two synthesis runs alive in ONE process; cancellation (round par/k-depth)

WRITTEN, NOT BUILT/RUN. TARGET-ONLY; not in `Tests.AllTests`. It asserts
NOTHING and never throws on an observation: every observation is a log line
`DEPTHCANCEL <case>: …`, and the last line is `DEPTHCANCEL SUMMARY`. The
compiler is not edited. The predictions are in `docs/parallel/K-depth-cell.md`.

What it controls, and how, without a language server:

* A run is `synthesizeCombinational <decl>` started in a TASK
  (`Core.wrapAsync … (some cancelToken)` then `EIO.asTask`, a dedicated
  thread), i.e. a `MetaM` run with its own cancellation token, as a command
  elaborated by the language server has one.
* A run is made long at a KNOWN point inside the entry through the public
  cell `sparkleChildSynth` (the child entry the translator calls for a
  `@[hardware_module]` call): the probe puts a wrapper there that, the first
  time it is asked for one named child, raises a flag and HOLDS until
  released, then calls the real `synthesizeChild`. While it holds, the run
  is inside the entry's `try` (depth ≥ 1), its module half built. Three
  kinds of hold: polling `Core.checkInterrupted` (what compiler code inside
  a `whnf` / `inferType` does); polling WITHOUT a check (a stretch with no
  Meta call); throwing an ordinary exception (control).
  The wrapper is the probe's, not the compiler's: it changes WHEN the child
  entry runs, not what it computes.
* The command's thread watches the flags, reads the depth and the caches,
  starts the second run, sets the token.

The cases:

* `clean` — each declaration from depth 0, alone: the reference results.
* `overlap` — A (`topA`) held at its child; B (`topB`) started meanwhile and
  held at ITS child; then B released, then A. Read at each stop: depth, the
  child cache (a sentinel the entry would empty at depth 0), the wire-width
  cache (does it still have A's wires while B is inside?).
* `stale` — A held; under the name of B's child the child cache gets a module
  compiled from ANOTHER declaration (PLANTED: what a run on the previous text
  of a file leaves under that name; a second environment with a re-bodied
  declaration is not built here); B (`topS`) run to the end and compared with
  its clean result; then the same B from depth 0.
* `cancel-check` — A held with checks; token set; then B from that state.
* `cancel-nocheck` — A held WITHOUT checks; token set; A still alive; B run
  meanwhile; A released.
* `throw` — A's hold throws an ordinary exception.
* `model` — NOT a run of the entry: the entry's three operations on the depth
  cell (`get`, `set (d + 1)`, `modify (· - 1)`) in one interleaving of two
  threads of control, on the real cell. Arithmetic only.

Every case starts by reading the depth it finds (logged) and setting it to 0,
and the whole command restores the depth, the child-entry cell and the caches
in a `finally`. -/

open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit

namespace Tests.Compiler.DepthCancelProbe
open Lean Meta

/-! ### The declarations -/

@[hardware_module]
def kidA (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))

@[hardware_module]
def kidB (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 2#8 : Signal defaultDomain (BitVec 8))

/-- The child whose NAME the `stale` case reuses. -/
@[hardware_module]
def kidS (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 3#8 : Signal defaultDomain (BitVec 8))

/-- Another body: stands for `kidS` in the previous text of a file. -/
@[hardware_module]
def kidSOld (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 4#8 : Signal defaultDomain (BitVec 8))

def topA (aIn : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  kidA aIn + aIn

def topB (bIn : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  kidB bIn + bIn

def topS (sIn : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  kidS sIn + sIn

def topSOld (sIn : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  kidSOld sIn + sIn

/-! ### The machinery -/

abbrev Res := Sparkle.IR.AST.Module × Sparkle.IR.AST.Design

/-- A hold at the child entry of one named child. -/
structure Gate where
  target : Name
  /-- raised when the run reaches the hold -/
  entered : IO.Ref Bool
  /-- the hold ends when this is raised -/
  release : IO.Ref Bool
  /-- the hold happens once -/
  fired : IO.Ref Bool
  /-- poll `Core.checkInterrupted` while holding -/
  checks : Bool
  /-- throw an ordinary exception instead of holding -/
  throws : Bool

def mkGate (target : Name) (checks : Bool) (throws : Bool := false) : IO Gate := do
  let entered ← IO.mkRef false
  let release ← IO.mkRef false
  let fired ← IO.mkRef false
  pure { target, entered, release, fired, checks, throws }

/-- Hold until released (at most `left` polls of 2 ms). -/
partial def holdLoop (g : Gate) (left : Nat) : MetaM Unit := do
  if g.checks then
    Core.checkInterrupted
  let rel ← g.release.get
  if rel then
    return
  if left == 0 then
    throwError "DEPTHCANCEL: the hold at {g.target} was never released"
  IO.sleep 2
  holdLoop g (left - 1)

/-- The child entry with the holds in front of it. -/
def gatedChild (gates : List Gate) (n : Name) : MetaM Res := do
  for g in gates do
    if g.target == n then
      let fired ← g.fired.get
      if !fired then
        g.fired.set true
        g.entered.set true
        if g.throws then
          throwError "DEPTHCANCEL control: an ordinary exception at the child entry of {n}"
        holdLoop g 30000
  synthesizeChild n

/-- Start `synthesizeCombinational decl` in a task with the cancellation token. -/
def spawnSynth (decl : Name) (tk : IO.CancelToken) : CoreM (Task (Except Exception Res)) := do
  let f ← Core.wrapAsync
    (fun (_ : Unit) => ((synthesizeCombinational decl).run' : CoreM Res)) (some tk)
  let t ← (f ()).asTask (prio := Task.Priority.dedicated)
  pure t

/-- Wait for a flag (at most `left` polls of 2 ms). -/
partial def waitFlag (flag : IO.Ref Bool) (left : Nat) : IO Bool := do
  let v ← flag.get
  if v then
    return true
  if left == 0 then
    return false
  IO.sleep 2
  waitFlag flag (left - 1)

/-- Wait for a task (at most `left` polls of 2 ms). -/
partial def waitTask (t : Task (Except Exception Res)) (left : Nat) :
    IO (Option (Except Exception Res)) := do
  let fin ← IO.hasFinished t
  if fin then
    return some t.get
  if left == 0 then
    return none
  IO.sleep 2
  waitTask t (left - 1)

def resStr : Option (Except Exception Res) → String
  | none => "STILL RUNNING (wait budget used up)"
  | some (.ok _) => "ok"
  | some (.error e) => if e.isInterrupt then "INTERRUPTED" else "ordinary error"

def resOk? : Option (Except Exception Res) → Option Res
  | some (.ok r) => some r
  | _ => none

def bs (b : Bool) : String := if b then "T" else "F"

/-- Equal to the reference result? `-` when either is missing. -/
def sameAs (r : Option (Except Exception Res)) (ref : Option Res) : String :=
  match resOk? r, ref with
  | some a, some b => bs (a == b)
  | _, _ => "-"

def modNames (r : Option (Except Exception Res)) : List String :=
  match resOk? r with
  | some x => x.2.modules.map (·.name)
  | none => []

/-- What the process-global cells hold. -/
structure Snap where
  depth : Nat
  child : List Name
  subMod : Nat
  typeC : Nat
  subInst : Nat
  singleOut : Nat
  fvar : Nat
  wireW : List String
  letW : Nat
  loopW : Nat
  canon : Nat

def snap : IO Snap := do
  let depth ← sparkleSynthDepth.get
  let child ← sparkleChildCache.get
  let subMod ← sparkleSubModuleCache.get
  let typeC ← sparkleTypeCache.get
  let subInst ← sparkleSubInstanceOutputs.get
  let singleOut ← sparkleSingleOutInstanceCache.get
  let fvar ← sparkleFvarValueMap.get
  let wireW ← sparkleWireWidthCache.get
  let letW ← sparkleLetWireCache.get
  let loopW ← sparkleLoopWireCache.get
  let canon ← sparkleWireCanon.get
  pure { depth, child := child.keys, subMod := subMod.size, typeC := typeC.size,
         subInst := subInst.size, singleOut := singleOut.size, fvar := fvar.size,
         wireW := wireW.keys, letW := letW.size, loopW := loopW.size, canon := canon.size }

def Snap.str (s : Snap) : String :=
  s!"depth={s.depth} childCache={s.child} subModuleMemo={s.subMod} typeCache={s.typeC} subInstanceOutputs={s.subInst} singleOut={s.singleOut} fvarMap={s.fvar} wireWidth={s.wireW} letCache={s.letW} loopCache={s.loopW} wireCanon={s.canon}"

/-- Every wire of `a` is still a key of the wire-width cache in `b`. -/
def Snap.hasWiresOf (b a : Snap) : Bool := a.wireW.all fun k => b.wireW.contains k

/-- A name no declaration has: the sentinel entry of the child cache. -/
def sentinel : Name := `DepthCancelProbe.sentinel.notADeclaration

/-- Start of a case: the depth found, then depth 0 and the given holds. -/
def beginCase (tag : String) (gates : List Gate) : CoreM Unit := do
  let d ← sparkleSynthDepth.get
  logInfo m!"DEPTHCANCEL {tag}: START (depth found at the start of the case: {d}; set to 0)"
  sparkleSynthDepth.set 0
  sparkleChildSynth.set (some (gatedChild gates))

/-- Run one declaration to its end on a task, no hold of its own. -/
def runToEnd (decl : Name) : CoreM (Option (Except Exception Res)) := do
  let tk ← IO.CancelToken.new
  let t ← spawnSynth decl tk
  waitTask t 30000

/-- The wait budgets, in polls of 2 ms. -/
def budget : Nat := 15000

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftCoreM do
  let mut summary : Array String := #[]
  try
    -- ------------------------------------------------------------ clean
    beginCase "clean" []
    logInfo m!"DEPTHCANCEL clean: START topA, topB, topS, topSOld, each from depth 0"
    let rA ← runToEnd ``topA
    let sA ← snap
    logInfo m!"DEPTHCANCEL clean topA: {resStr rA}; modules {modNames rA}; afterwards {sA.str}"
    let rB ← runToEnd ``topB
    let sB ← snap
    logInfo m!"DEPTHCANCEL clean topB: {resStr rB}; modules {modNames rB}; afterwards {sB.str}"
    let rS ← runToEnd ``topS
    let sS ← snap
    logInfo m!"DEPTHCANCEL clean topS: {resStr rS}; modules {modNames rS}; afterwards {sS.str}"
    let rSOld ← runToEnd ``topSOld
    let cacheOld ← sparkleChildCache.get
    let oldKid : Option Res := cacheOld.get? ``kidSOld
    logInfo m!"DEPTHCANCEL clean topSOld: {resStr rSOld}; modules {modNames rSOld}; the child cache has kidSOld: {bs oldKid.isSome}"
    let refA := resOk? rA
    let refB := resOk? rB
    let refS := resOk? rS
    summary := summary.push s!"clean runs ok: {bs (refA.isSome && refB.isSome && refS.isSome)}"

    -- ---------------------------------------------------------- overlap
    let gA ← mkGate ``kidA true
    let gB ← mkGate ``kidB true
    beginCase "overlap" [gA, gB]
    logInfo m!"DEPTHCANCEL overlap: START run A = topA in a task (it holds at the child entry of kidA)"
    let tkA ← IO.CancelToken.new
    let tA ← spawnSynth ``topA tkA
    let inA ← waitFlag gA.entered budget
    let s1 ← snap
    logInfo m!"DEPTHCANCEL overlap A-held: A reached its hold: {bs inA}; {s1.str}"
    sparkleChildCache.modify fun c => match refS with
      | some r => c.insert sentinel r
      | none => c
    logInfo m!"DEPTHCANCEL overlap: START run B = topB in a task while A is held (it holds at the child entry of kidB); a sentinel entry was put in the child cache: {bs refS.isSome}"
    let tkB ← IO.CancelToken.new
    let tB ← spawnSynth ``topB tkB
    let inB ← waitFlag gB.entered budget
    let s2 ← snap
    logInfo m!"DEPTHCANCEL overlap B-held: B reached its hold: {bs inB}; depth B's entry found = (depth now) - 1 = {s2.depth - 1}; child cache still has the sentinel (B did NOT empty it: nested branch): {bs (s2.child.contains sentinel)}; wire-width cache still has every wire A had at its hold: {bs (s2.hasWiresOf s1)}; {s2.str}"
    logInfo m!"DEPTHCANCEL overlap: START release B"
    gB.release.set true
    let rB2 ← waitTask tB budget
    let s3 ← snap
    logInfo m!"DEPTHCANCEL overlap B-ended: B {resStr rB2}; B == its clean result: {sameAs rB2 refB}; wire-width cache has A's wires again (B's finally put its entry snapshot back): {bs (s3.hasWiresOf s1)}; {s3.str}"
    logInfo m!"DEPTHCANCEL overlap: START release A"
    gA.release.set true
    let rA2 ← waitTask tA budget
    let s4 ← snap
    logInfo m!"DEPTHCANCEL overlap A-ended: A {resStr rA2}; A == its clean result: {sameAs rA2 refA}; {s4.str}"
    summary := summary.push s!"overlap: B entered at depth {s2.depth - 1}, sentinel kept {bs (s2.child.contains sentinel)}, A's wires visible while B inside {bs (s2.hasWiresOf s1)}, B==clean {sameAs rB2 refB}, A==clean {sameAs rA2 refA}, depth at the end {s4.depth}"

    -- ------------------------------------------------------------ stale
    let gA ← mkGate ``kidA true
    beginCase "stale" [gA]
    logInfo m!"DEPTHCANCEL stale: START run A = topA in a task (held at kidA)"
    let tkA ← IO.CancelToken.new
    let tA ← spawnSynth ``topA tkA
    let inA ← waitFlag gA.entered budget
    sparkleChildCache.modify fun c => match oldKid with
      | some r => c.insert ``kidS r
      | none => c
    let s1 ← snap
    logInfo m!"DEPTHCANCEL stale A-held: A reached its hold: {bs inA}; PLANTED under the name kidS the module compiled from kidSOld: {bs oldKid.isSome}; {s1.str}"
    logInfo m!"DEPTHCANCEL stale: START run B = topS to its end while A is held"
    let rS2 ← runToEnd ``topS
    let s2 ← snap
    logInfo m!"DEPTHCANCEL stale B-ended: B {resStr rS2}; B == its clean result: {sameAs rS2 refS}; B's modules {modNames rS2} (clean: {modNames rS}); {s2.str}"
    logInfo m!"DEPTHCANCEL stale: START release A, then B = topS again from depth 0"
    gA.release.set true
    let rA3 ← waitTask tA budget
    let dAfterA ← sparkleSynthDepth.get
    let rS3 ← runToEnd ``topS
    logInfo m!"DEPTHCANCEL stale after: A {resStr rA3}, depth {dAfterA}; topS from that depth: {resStr rS3}, == its clean result: {sameAs rS3 refS}"
    summary := summary.push s!"stale: B (nested, name-keyed child cache) == clean {sameAs rS2 refS}; the same B from depth 0 == clean {sameAs rS3 refS}"

    -- ----------------------------------------------------- cancel-check
    let gA ← mkGate ``kidA true
    beginCase "cancel-check" [gA]
    logInfo m!"DEPTHCANCEL cancel-check: START run A = topA in a task (held at kidA, polling checkInterrupted)"
    let tkA ← IO.CancelToken.new
    let tA ← spawnSynth ``topA tkA
    let inA ← waitFlag gA.entered budget
    let s1 ← snap
    logInfo m!"DEPTHCANCEL cancel-check A-held: A reached its hold: {bs inA}; {s1.str}"
    logInfo m!"DEPTHCANCEL cancel-check: START set A's cancellation token (the hold is NOT released)"
    tkA.set
    let rA4 ← waitTask tA budget
    let s2 ← snap
    logInfo m!"DEPTHCANCEL cancel-check A-ended: A {resStr rA4}; depth back to 0 (the finally ran on the interrupt): {bs (s2.depth == 0)}; what A left in the cells: {s2.str}"
    sparkleChildCache.modify fun c => match refS with
      | some r => c.insert sentinel r
      | none => c
    logInfo m!"DEPTHCANCEL cancel-check: START run B = topB after the cancelled A"
    let rB3 ← runToEnd ``topB
    let s3 ← snap
    logInfo m!"DEPTHCANCEL cancel-check B-ended: B {resStr rB3}; B == its clean result: {sameAs rB3 refB}; the sentinel is gone (B emptied the child cache: depth-0 branch): {bs (!s3.child.contains sentinel)}; {s3.str}"
    gA.release.set true
    summary := summary.push s!"cancel-check: A {resStr rA4}, depth after {s2.depth}, next run from depth 0 == clean {sameAs rB3 refB}"

    -- --------------------------------------------------- cancel-nocheck
    let gA ← mkGate ``kidA false
    beginCase "cancel-nocheck" [gA]
    logInfo m!"DEPTHCANCEL cancel-nocheck: START run A = topA in a task (held at kidA, NO check while holding)"
    let tkA ← IO.CancelToken.new
    let tA ← spawnSynth ``topA tkA
    let inA ← waitFlag gA.entered budget
    logInfo m!"DEPTHCANCEL cancel-nocheck: START set A's cancellation token, then wait 300 ms"
    tkA.set
    IO.sleep 300
    let finA ← IO.hasFinished tA
    let s1 ← snap
    logInfo m!"DEPTHCANCEL cancel-nocheck A-cancelled: A reached its hold: {bs inA}; 300 ms after the token was set A has ended: {bs finA}; {s1.str}"
    sparkleChildCache.modify fun c => match refS with
      | some r => c.insert sentinel r
      | none => c
    logInfo m!"DEPTHCANCEL cancel-nocheck: START run B = topB while the cancelled A is still alive"
    let rB4 ← runToEnd ``topB
    let s2 ← snap
    logInfo m!"DEPTHCANCEL cancel-nocheck B-ended: B {resStr rB4}; B == its clean result: {sameAs rB4 refB}; child cache still has the sentinel (B took the nested branch): {bs (s2.child.contains sentinel)}; {s2.str}"
    logInfo m!"DEPTHCANCEL cancel-nocheck: START release A's hold (its token is set)"
    gA.release.set true
    let rA5 ← waitTask tA budget
    let s3 ← snap
    logInfo m!"DEPTHCANCEL cancel-nocheck A-ended: A {resStr rA5} (INTERRUPTED = it met a check after the hold; ok = it met none before its end); {s3.str}"
    summary := summary.push s!"cancel-nocheck: A alive 300 ms after cancellation {bs (!finA)} at depth {s1.depth}; B meanwhile nested {bs (s2.child.contains sentinel)}; A finally {resStr rA5}; depth at the end {s3.depth}"

    -- ------------------------------------------------------------ throw
    let gA ← mkGate ``kidA true true
    beginCase "throw" [gA]
    logInfo m!"DEPTHCANCEL throw: START run A = topA in a task (an ordinary exception at the child entry of kidA)"
    let rA6 ← runToEnd ``topA
    let hit ← gA.entered.get
    let s1 ← snap
    logInfo m!"DEPTHCANCEL throw A-ended: the exception was thrown: {bs hit}; A {resStr rA6} (ok = a handler of the compiler caught it and went on; an interrupt cannot be caught that way); A == its clean result: {sameAs rA6 refA}; {s1.str}"
    summary := summary.push s!"throw: A {resStr rA6}, depth after {s1.depth}"

    -- ------------------------------------------------------------ model
    beginCase "model" []
    logInfo m!"DEPTHCANCEL model: START the entry's operations on the depth cell in one interleaving (NOT a run of the entry)"
    -- two runs alive: A's outer entry and B's entry
    sparkleSynthDepth.set 2
    -- A's child entry reads the depth …
    let dRead ← sparkleSynthDepth.get
    -- … B ends meanwhile (its finally) …
    sparkleSynthDepth.modify (· - 1)
    -- … A's child entry writes what it read, plus one
    sparkleSynthDepth.set (dRead + 1)
    -- A's child ends, A ends
    sparkleSynthDepth.modify (· - 1)
    sparkleSynthDepth.modify (· - 1)
    let dLeak ← sparkleSynthDepth.get
    logInfo m!"DEPTHCANCEL model: get (2), the other run's modify (-1), set (2 + 1), then the two remaining modify (-1): the cell reads {dLeak} with no run alive (0 = balanced; 1 = one decrement lost: every later entry of the process is nested)"
    summary := summary.push s!"model: depth with no run alive {dLeak}"
  finally
    sparkleSynthDepth.set 0
    sparkleChildSynth.set (some synthesizeChild)
    sparkleChildCache.set {}
    sparkleSubModuleCache.set {}
    sparkleTypeCache.set {}
    sparkleSubInstanceOutputs.set {}
    sparkleSingleOutInstanceCache.set {}
    sparkleFvarValueMap.set {}
    sparkleWireWidthCache.set {}
    sparkleLetWireCache.set {}
    sparkleLoopWireCache.set {}
    sparkleWireCanon.set {}
  logInfo m!"DEPTHCANCEL SUMMARY: {summary}"

end Tests.Compiler.DepthCancelProbe
