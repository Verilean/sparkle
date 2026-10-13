import Lean.Elab.Command
import Tests.Compiler.CallWidthHuntTest

/-! # A nested entry and the single-output instance map (finding I): the INTEGRATION regression test

WRITTEN, NOT BUILT, NOT RUN (par/f-1). Every "PREDICTED" is from reading
`Sparkle/Compiler/Elab.lean` and from the lines the comparison probe
`SingleOutNestedFixTest` gave on the candidate
(`docs/parallel/verification-i-fix-isolated.md`), not an observation of this
file.

This test ASSERTS, unconditionally. It is meant for `Tests.AllTests` on a
tree WITH the fix of finding I (`synthesizeCombinationalCoreWith` saves
`sparkleSingleOutInstanceCache` at a nested entry, starts the child with it
empty, and puts it back in the `finally`). There is no "measured as not
fixed, so skipped" path: on a tree without the fix the command THROWS.

It imports `Tests.Compiler.CallWidthHuntTest` only (already in
`Tests.AllTests`); `cleanLegacy` is a local copy of the eight lines of
`MachineFallThroughCensusTest`, so that census is not pulled into the
closure of `Tests.AllTests`.

The three tests of finding I:

* this file — suite (to be imported by `Tests/AllTests.lean`);
* `SingleOutNestedFixTest` — the comparison probe (measures `fixed`, asserts
  only when it is true; builds on both trees) — target-only;
* `SingleOutStaleProbe` — the BEFORE evidence (asserts the DIFFERENCE; on a
  fixed tree it throws "the two modules are EQUAL") — never in a suite.

The finding was shown on a CONSTRUCTED state (a pre-set depth, an emptied
memo); by reading no real compile reaches it
(`docs/parallel/I-singleout-stale.md` §2). Sections (a) to (d) below work on
constructed states of that kind; section (e) on real commands.

## What is asserted (the command throws unless ALL hold)

(b) THE SCENARIO OF THE FINDING. Run A: the full entry on `pTop` from reset
refs at depth 0. Run B: the full entry again with the depth pre-set to 1,
the refs as A left them, the legacy memo emptied. Required: A returns, B
returns, each has at least one `hIrr` instance statement, the two modules
are EQUAL. Also required, so that the scenario is the one of the finding and
B is a build and not a memo hit: after A the map holds at least one key
`<pTop module>#<hIrr module>#…` (the stale entry B would hit), and `pTop` is
absent from `sparkleSubModuleCache` before B and present after.

(a) FIXED, required. `fixed` = "a nested entry gives the parent's map back
exactly" (run R1: the seed is all that is in the map afterwards — not the
seed plus the child's entry) AND "a nested entry starts from the empty map"
(run R2, see (d)). `fixed=F` is a failure.

(c) PARENT SEED RESTORATION. Seven nested entries, each at depth 1 from reset
refs with the map seeded; afterwards the map must hold EXACTLY the seed (same
size, every seeded key at its seeded value) and the depth must read 1:

* R1, R2, R3 RETURN (`pTop`; through `synthesizeCombinational` twice and
  `synthesizeChild` once);
* R4, R5 THROW late (`pBad`, through `synthesizeChild` and
  `synthesizeCombinationalCore`): its first result leaf is `pTop`'s body
  (it instantiates `hIrr`: the child's builder writes its own entry), its
  second leaf an `if … then … else`, refused in `Rec.handleErrorPatterns`;
* R6, R7 THROW early (an undeclared name: `getConstInfo` is the first
  statement inside the `try`, after the map was cleared).

Reachability, as in `NestedFailRestoreTest`: the message must be the
intended one ("if-then-else expressions cannot be synthesized to hardware" /
"unknown constant", lower case); `hIrr` must be ABSENT from
`sparkleSubModuleCache` and `sparkleChildCache` just before the run (both
are emptied: no cache hit can fake it) and PRESENT after for `pTop` and
`pBad` (the run got as far as the helper's instance), absent for the
undeclared name; for the returning runs the declaration itself must be
absent before and present after (a build, not a memo hit). Neither module
cache is cleared or restored by a nested entry, so the keys survive.

(d) THE CHILD DOES NOT SEE THE PARENT'S ENTRIES. Observed without editing
the compiler: the seed of R2 to R5 contains, besides a foreign key, every
key run A left under `<pTop module>#<hIrr module>#` — the exact key the
nested builder of `pTop` looks up — bound to a POISON wire name that no
builder makes. A child that read the parent's map would take the hit: the
legacy handler would return the poison wire, emit no instance, and the
poison name would occur in the module. Required for R2 and R3: at least one
`hIrr` instance, the poison name does not occur in the module, the module
EQUALS run A's. (And by (c) the poisoned key still holds the poison
afterwards: the child's own entry under the same key did not replace it.)

(e) REAL COMMANDS (no pre-set depth, no emptied memo). `pOuter` (calls the
tagged `pMid`, which instantiates `hIrr` through the legacy handler): the
entry returns, the nested `pMid` is in the design, `pMid` alone returns, the
two are EQUAL, with at least one `hIrr` instance. `pMach` (a register
machine with `hIrr` in its body; the hole the reading closed by
`unifiedGateRoot`): the real entry and the clean legacy arm both return,
with the SAME number of `hIrr` instances, at least one. The machine gate's
verdict is logged, not asserted.

## The lines (each START also on standard error, flushed, before the run)

    SINGLEOUTREG START <what>
    SINGLEOUTREG A: returned=<T or F> hIrr insts=<n> stmts=<n>
    SINGLEOUTREG STALE: keys left by A under the pTop and hIrr prefix=<n> map size=<n>
    SINGLEOUTREG B: returned=<T or F> hIrr insts=<n> stmts=<n>
    SINGLEOUTREG RESULT: equal=<T or F> B built=<T or F> (pTop memoised before B=<T or F>)
    SINGLEOUTREG RUN <label>: threw=.. intended=.. reachedKid=.. selfBuilt=.. seedRestored=.. depthBack=.. hIrr insts=<n> poison in module=<T or F or -> equals A=<T or F or -> [..]
    SINGLEOUTREG THREW [<label>]: <the message>
    SINGLEOUTREG FIXED: restores=<T or F> child starts empty=<T or F> => fixed=<T or F>
    SINGLEOUTREG pOuter: returned=.. pMid nested found=.. hIrr insts nested=<n> alone=<n> nested==alone=..
    SINGLEOUTREG pMach: machine shape=.. real=.. cold=.. hIrr insts real=<n> cold=<n> => stale hit on a real command=..
    SINGLEOUTREG: <n> nested runs; failing checks [...]

PREDICTED on a tree with the fix: `A 1/3`, `STALE 1 / 1`, `B 1/3`,
`equal=T B built=T`; R1 to R3 `threw=F intended=T reachedKid=T selfBuilt=T
seedRestored=T depthBack=T hIrr insts=1`, R2 and R3 `poison in module=F
equals A=T`; R4 and R5 `threw=T intended=T reachedKid=T selfBuilt=F
seedRestored=T depthBack=T`; R6 and R7 `threw=T intended=T reachedKid=F
selfBuilt=F seedRestored=T depthBack=T`; `fixed=T`; `pOuter … nested=1
alone=1 nested==alone=T`; `pMach: machine shape=F real=T cold=T … real=1
cold=1 => stale hit=F`; `failing checks []`.

PREDICTED on a tree without the fix: `B 0/2`, `equal=F`; R1 `seedRestored=F`
(seed and the child's entry); R2 and R3 `hIrr insts=0`, `poison in
module=T`, `equals A=F`, `seedRestored=T` (the child HIT the poisoned key
and wrote nothing: that flag alone does not tell the trees apart there); R4
and R5 `seedRestored=F` (the seed and `pBad`'s own entry, written before
the throw); R6 and R7 `seedRestored=T` (never cleared, nothing written:
those two lines do not tell the trees apart); `fixed=F`; the command
throws. -/
namespace Tests.Compiler.SingleOutNestedRegressionTest
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Tests.Compiler.CallWidthHuntTest (Mod Dsn bs gatesOf resetRefs)

/-- An untagged helper that default-transparency unfolding leaves alone (the
helper of `SingleOutStaleProbe`). -/
@[irreducible]
def hIrr {dom : DomainConfig} (y : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  y + (Signal.pure 1#8 : Signal dom (BitVec 8))

def pTop (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  hIrr x + x

/-- A tagged child whose body instantiates `hIrr` through the legacy handler. -/
@[hardware_module]
def pMid (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  hIrr x + x

def pOuter (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  pMid x - x

/-- A register machine with the helper in its body. -/
def pMach (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let h := hIrr x
    r <~ h + rs
    return rs

structure Two (dom : DomainConfig) where
  a : Signal dom (BitVec 8)
  b : Signal dom (BitVec 8)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (Two dom) dom := ⟨⟩

/-- The failing writer (the pattern of `NestedFailRestoreTest.fBadW`): its
first leaf is `pTop`'s body, its second leaf an `if … then … else`, which
the translator refuses. -/
@[hardware_module]
def pBad (x y : Signal defaultDomain (BitVec 8)) : Two defaultDomain :=
  { a := hIrr x + x, b := if (0 : Nat) = 0 then x else y }

def hIrrName : Name := ``hIrr
def pTopName : Name := ``pTop
def pBadName : Name := ``pBad
/-- NOT declared, on purpose. -/
def missingName : Name := `Tests.Compiler.SingleOutNestedRegressionTest.noSuchDeclaration

def hIrrMod : String := Sparkle.IR.ModuleName.ofDecl ``hIrr
def pTopMod : String := Sparkle.IR.ModuleName.ofDecl ``pTop
def pMidMod : String := Sparkle.IR.ModuleName.ofDecl ``pMid

/-- The prefix of the key the builder of `pTop` looks its `hIrr` instance up
under (`parent#child#connections`, Elab.lean, the `[singleOut]` branch). -/
def staleKeyPrefix : String := pTopMod ++ "#" ++ hIrrMod ++ "#"

/-- A wire name no builder makes. -/
def poisonWire : String := "POISON_single_out_wire_of_the_parent"

def seedForeign : List (String × String) :=
  [("seed#single#out", "seed_single_out_wire")]

/-- The message of the INTENDED failure of `pBad`, lower case (the text of
`Rec.handleErrorPatterns`). -/
def needleIte : String := "if-then-else expressions cannot be synthesized to hardware"

/-- The message of `getConstInfo` on an undeclared name, lower case. -/
def needleMissing : String := "unknown constant"

def emit (s : String) : MetaM Unit := do
  IO.eprintln s
  (← IO.getStderr).flush
  logInfo m!"{s}"

/-- `sub` occurs in `s`. -/
def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The map holds exactly the seeded entries. -/
def sameMap (m : Std.HashMap String String) (seed : List (String × String)) : Bool :=
  m.size == seed.length && seed.all fun p => m.get? p.1 == some p.2

/-- The instance statements of the helper's module. -/
def hInsts (m : Mod) : Nat :=
  (m.body.filter fun s => match s with
    | .inst mn _ _ => mn == hIrrMod
    | _ => false).length

/-- The poison wire name occurs somewhere in the module. -/
def poisoned (m : Mod) : Bool := hasSub (toString (repr m)) poisonWire

def optBs : Option Bool → String
  | some b => bs b
  | none => "-"

/-- The legacy arm on the given entry constant, from reset refs, at depth 1
(a copy of `MachineFallThroughCensusTest.cleanLegacy`). -/
def cleanLegacy (n : Name) (ec : ConstantInfo) : MetaM (Mod × Dsn) := do
  let tenv ← Lean.getEnv
  let env ← getEnv
  resetRefs
  sparkleSynthDepth.set 1
  try
    synthesizeFromConst (fun e hint top named => translateExprToWire tenv e hint top named)
      (fun _ => pure ()) n [] false false ec (instancePredicate env)
  finally
    sparkleSynthDepth.set 0

/-- One run of the full entry on `pTop` at the given pre-set depth; the refs
are NOT reset here (the scenario of the finding). -/
def runOnce (label : String) (depth : Nat) : MetaM (Option Mod) := do
  sparkleSynthDepth.set depth
  let r : Option Mod ←
    try
      let res ← Sparkle.Compiler.Elab.synthesizeCombinational ``pTop
      pure (some res.1)
    catch _ => pure none
  sparkleSynthDepth.set 0
  match r with
  | some m => emit s!"SINGLEOUTREG {label}: returned=T hIrr insts={hInsts m} stmts={m.body.length}"
  | none => emit s!"SINGLEOUTREG {label}: returned=F hIrr insts=0 stmts=0"
  return r

/-- The entry function a nested run goes through. -/
inductive Via where
  | full
  | child
  | core

def viaStr : Via → String
  | Via.full => "synthesizeCombinational"
  | Via.child => "synthesizeChild"
  | Via.core => "synthesizeCombinationalCore"

def runVia (v : Via) (n : Name) : MetaM (Mod × Dsn) := do
  match v with
  | Via.full => Sparkle.Compiler.Elab.synthesizeCombinational n
  | Via.child => synthesizeChild n
  | Via.core => synthesizeCombinationalCore n [] false

/-- What a nested run is, and what it must do. -/
structure Spec where
  label : String
  via : Via
  decl : Name
  seed : List (String × String)
  expectThrow : Bool
  /-- lower-case text the message must contain (`""`: the run must return) -/
  needle : String
  /-- `hIrr` is in a module cache afterwards -/
  expectKid : Bool
  /-- the declaration itself is in a module cache afterwards -/
  expectSelf : Bool

/-- What a nested run reports. -/
structure Row where
  modl : Option Mod
  threw : Bool
  msg : String
  depthAfter : Nat
  mapAfter : Std.HashMap String String
  kidBefore : Bool
  kidAfter : Bool
  selfBefore : Bool
  selfAfter : Bool

/-- The depth a nested entry reads: its parent, entered at 0, set it to 1. -/
def nestedDepth : Nat := 1

/-- ONE nested entry: every ref reset, the single-output map seeded as the
parent would hold it, the depth as a nested entry reads it, the entry inside
`try … catch`, the refs read back. Everything is reset afterwards. -/
def nestedRun (s : Spec) : MetaM Row := do
  emit s!"SINGLEOUTREG START RUN {s.label} via {viaStr s.via} (depth {nestedDepth}, reset refs, {s.seed.length} seeded entries)"
  resetRefs
  sparkleSingleOutInstanceCache.set (Std.HashMap.ofList s.seed)
  sparkleSynthDepth.set nestedDepth
  -- reachability cannot come from a cache hit: `resetRefs` emptied both module
  -- caches, and the absence is READ here, just before the run
  let sub0 ← (sparkleSubModuleCache.get : IO _)
  let child0 ← (sparkleChildCache.get : IO _)
  let kidBefore : Bool := sub0.contains hIrrName || child0.contains hIrrName
  let selfBefore : Bool := sub0.contains s.decl || child0.contains s.decl
  let r : Option Mod × String ←
    try
      let res ← runVia s.via s.decl
      pure (some res.1, "")
    catch e =>
      let text ← e.toMessageData.toString
      pure (none, text)
  let depthAfter : Nat ← (sparkleSynthDepth.get : IO _)
  let mapAfter ← (sparkleSingleOutInstanceCache.get : IO _)
  let sub1 ← (sparkleSubModuleCache.get : IO _)
  let child1 ← (sparkleChildCache.get : IO _)
  let kidAfter : Bool := sub1.contains hIrrName || child1.contains hIrrName
  let selfAfter : Bool := sub1.contains s.decl || child1.contains s.decl
  sparkleSynthDepth.set 0
  resetRefs
  let row : Row := {
    modl := r.1
    threw := r.1.isNone
    msg := r.2
    depthAfter := depthAfter
    mapAfter := mapAfter
    kidBefore := kidBefore
    kidAfter := kidAfter
    selfBefore := selfBefore
    selfAfter := selfAfter }
  pure row

/-- The lines of one nested run; returns the checks that do not hold.
`ref?` is run A's module for a run whose module must equal it and must not
contain the poison (section (d)); `none` for the others. -/
def report (s : Spec) (r : Row) (ref? : Option Mod) : MetaM (Array String) := do
  let name : String := s.label ++ " via " ++ viaStr s.via
  let lowered : String := r.msg.toLower
  let intended : Bool :=
    if s.expectThrow then r.threw && hasSub lowered s.needle else !r.threw
  let restored : Bool := sameMap r.mapAfter s.seed
  let depthBack : Bool := r.depthAfter == nestedDepth
  let insts : Nat := (r.modl.map hInsts).getD 0
  let pois? : Option Bool := r.modl.map poisoned
  let eqA? : Option Bool := match r.modl, ref? with
    | some m, some a => some (m == a)
    | _, _ => none
  emit s!"SINGLEOUTREG RUN {name}: threw={bs r.threw} intended={bs intended} reachedKid={bs r.kidAfter} selfBuilt={bs r.selfAfter} seedRestored={bs restored} depthBack={bs depthBack} hIrr insts={insts} poison in module={optBs pois?} equals A={optBs eqA?} [entries after={r.mapAfter.size}, seeded={s.seed.length}; expected reachedKid={bs s.expectKid} selfBuilt={bs s.expectSelf}; cached before the run: hIrr={bs r.kidBefore} self={bs r.selfBefore}; depth before={nestedDepth} after={r.depthAfter}]"
  if r.threw then
    let flat : String := r.msg.replace "\n" " | "
    emit s!"SINGLEOUTREG THREW [{name}]: {flat}"
  let mut bad : Array String := #[]
  if !restored then
    bad := bad.push s!"sparkleSingleOutInstanceCache NOT RESTORED after {name}: {r.mapAfter.size} entries left, {s.seed.length} seeded"
  if !depthBack then
    bad := bad.push s!"sparkleSynthDepth NOT BACK after {name}: {nestedDepth} before, {r.depthAfter} after"
  if s.expectThrow && !r.threw then
    bad := bad.push s!"{name}: the nested entry was expected to THROW and returned (the failing path was not exercised)"
  if s.expectThrow && r.threw && !intended then
    bad := bad.push s!"{name}: the nested entry threw ANOTHER error than the intended one (expected text '{s.needle}'): {r.msg}"
  if !s.expectThrow && r.threw then
    bad := bad.push s!"{name}: the nested entry was expected to return and threw: {r.msg}"
  if r.kidBefore then
    bad := bad.push s!"{name}: hIrr was already in a module cache before the run (reachability would be a cache hit)"
  if r.selfBefore then
    bad := bad.push s!"{name}: the declaration was already in a module cache before the run (the run would be a memo hit)"
  if r.kidAfter != s.expectKid then
    bad := bad.push s!"{name}: reachedKid={bs r.kidAfter}, expected {bs s.expectKid}: the run did not fail (or return) where intended"
  if r.selfAfter != s.expectSelf then
    bad := bad.push s!"{name}: selfBuilt={bs r.selfAfter}, expected {bs s.expectSelf}"
  if !s.expectThrow && !r.threw && insts == 0 then
    bad := bad.push s!"{name}: the returned module has no hIrr instance statement"
  if ref?.isSome then
    if pois? != some false then
      bad := bad.push s!"{name}: the parent's poisoned entry was SEEN by the child (the poison wire occurs in its module, or it did not return)"
    if eqA? != some true then
      bad := bad.push s!"{name}: the module of the nested entry started over a poisoned map differs from the clean one (run A), or it did not return"
  pure bad

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let mut bad : Array String := #[]
  -- (b) the scenario of the finding
  emit "SINGLEOUTREG START A (depth 0, reset refs)"
  resetRefs
  let a ← runOnce "A" 0
  let mapA ← (sparkleSingleOutInstanceCache.get : IO _)
  let staleKeys : List String :=
    (mapA.toList.map fun p => p.1).filter fun k => k.startsWith staleKeyPrefix
  emit s!"SINGLEOUTREG STALE: keys left by A under the pTop and hIrr prefix={staleKeys.length} map size={mapA.size}"
  if staleKeys.isEmpty then
    bad := bad.push "run A left no single-output entry for pTop's hIrr instance (the state of the finding is not constructed)"
  emit "SINGLEOUTREG START B (depth 1, refs as A left them, the sub-module memo emptied)"
  sparkleSubModuleCache.set {}
  let memoBeforeB ← (sparkleSubModuleCache.get : IO _)
  let pTopBeforeB : Bool := memoBeforeB.contains pTopName
  let b ← runOnce "B" 1
  let memoAfterB ← (sparkleSubModuleCache.get : IO _)
  let bBuilt : Bool := !pTopBeforeB && memoAfterB.contains pTopName
  resetRefs
  sparkleSynthDepth.set 0
  match a, b with
  | some ma, some mb =>
    let eq : Bool := ma == mb
    emit s!"SINGLEOUTREG RESULT: equal={bs eq} B built={bs bBuilt} (pTop memoised before B={bs pTopBeforeB})"
    if hInsts ma == 0 then
      bad := bad.push "run A has no hIrr instance (the legacy single-output path is not exercised)"
    if hInsts mb == 0 then
      bad := bad.push "run B has no hIrr instance (the stale hit of finding I)"
    if !eq then
      bad := bad.push "run A and run B differ"
    if !bBuilt then
      bad := bad.push "run B was not a build of pTop (pTop not memoised by it, or memoised before it)"
  | _, _ =>
    emit "SINGLEOUTREG RESULT: a run did not return"
    bad := bad.push "a run of the scenario (A or B) did not return"
  -- (a) (c) (d) seeded nested entries
  let seedPoison : List (String × String) :=
    seedForeign ++ staleKeys.map fun k => (k, poisonWire)
  let r1 : Spec := {
    label := "R1 RETURN pTop (foreign seed)", via := Via.full, decl := pTopName,
    seed := seedForeign, expectThrow := false, needle := "", expectKid := true, expectSelf := true }
  let r2 : Spec := {
    label := "R2 RETURN pTop (poisoned seed)", via := Via.full, decl := pTopName,
    seed := seedPoison, expectThrow := false, needle := "", expectKid := true, expectSelf := true }
  let r3 : Spec := {
    label := "R3 RETURN pTop (poisoned seed)", via := Via.child, decl := pTopName,
    seed := seedPoison, expectThrow := false, needle := "", expectKid := true, expectSelf := true }
  let r4 : Spec := {
    label := "R4 THROW pBad (writes, then if-then-else)", via := Via.child, decl := pBadName,
    seed := seedPoison, expectThrow := true, needle := needleIte, expectKid := true, expectSelf := false }
  let r5 : Spec := {
    label := "R5 THROW pBad (writes, then if-then-else)", via := Via.core, decl := pBadName,
    seed := seedPoison, expectThrow := true, needle := needleIte, expectKid := true, expectSelf := false }
  let r6 : Spec := {
    label := "R6 THROW missing declaration", via := Via.child, decl := missingName,
    seed := seedPoison, expectThrow := true, needle := needleMissing, expectKid := false, expectSelf := false }
  let r7 : Spec := {
    label := "R7 THROW missing declaration", via := Via.core, decl := missingName,
    seed := seedPoison, expectThrow := true, needle := needleMissing, expectKid := false, expectSelf := false }
  let row1 ← nestedRun r1
  let bad1 ← report r1 row1 none
  bad := bad ++ bad1
  let row2 ← nestedRun r2
  let bad2 ← report r2 row2 a
  bad := bad ++ bad2
  let row3 ← nestedRun r3
  let bad3 ← report r3 row3 a
  bad := bad ++ bad3
  let row4 ← nestedRun r4
  let bad4 ← report r4 row4 none
  bad := bad ++ bad4
  let row5 ← nestedRun r5
  let bad5 ← report r5 row5 none
  bad := bad ++ bad5
  let row6 ← nestedRun r6
  let bad6 ← report r6 row6 none
  bad := bad ++ bad6
  let row7 ← nestedRun r7
  let bad7 ← report r7 row7 none
  bad := bad ++ bad7
  -- (a) fixed, REQUIRED
  let restores : Bool := !row1.threw && sameMap row1.mapAfter seedForeign
  let startsEmpty : Bool :=
    !staleKeys.isEmpty && (row2.modl.map fun m => !poisoned m && hInsts m != 0) == some true
  let fixed : Bool := restores && startsEmpty
  emit s!"SINGLEOUTREG FIXED: restores={bs restores} child starts empty={bs startsEmpty} => fixed={bs fixed}"
  if !fixed then
    bad := bad.push "NOT FIXED: a nested entry does not start from the empty single-output map and give the parent's back"
  -- (e) real commands: pOuter
  emit "SINGLEOUTREG START pOuter (real entry, depth 0)"
  resetRefs
  sparkleSynthDepth.set 0
  let outer? : Option (Mod × Dsn) ←
    try
      let res ← Sparkle.Compiler.Elab.synthesizeCombinational ``pOuter
      pure (some res)
    catch _ => pure none
  sparkleSynthDepth.set 0
  emit "SINGLEOUTREG START pMid alone (real entry, depth 0)"
  let alone? : Option Mod ←
    try
      let res ← Sparkle.Compiler.Elab.synthesizeCombinational ``pMid
      pure (some res.1)
    catch _ => pure none
  sparkleSynthDepth.set 0
  resetRefs
  let nested? : Option Mod := outer?.bind fun r => r.2.modules.find? fun m => m.name == pMidMod
  let same? : Option Bool := match nested?, alone? with
    | some x, some y => some (x == y)
    | _, _ => none
  let nestedInsts : Nat := (nested?.map hInsts).getD 0
  let aloneInsts : Nat := (alone?.map hInsts).getD 0
  emit s!"SINGLEOUTREG pOuter: returned={bs outer?.isSome} pMid nested found={bs nested?.isSome} hIrr insts nested={nestedInsts} alone={aloneInsts} nested==alone={optBs same?}"
  if same? != some true then
    bad := bad.push "pOuter: the entry did not return, or the nested pMid is missing, or it differs from the alone one"
  if nestedInsts == 0 then
    bad := bad.push "pOuter: the nested pMid has no hIrr instance statement"
  -- (e) real commands: pMach
  emit "SINGLEOUTREG START pMach (gates, real entry at depth 0, clean legacy arm)"
  let shape : Bool ←
    try
      let g ← gatesOf ``pMach
      pure g.shape.isSome
    catch _ => pure false
  resetRefs
  sparkleSynthDepth.set 0
  let real? : Option Mod ←
    try
      let res ← synthesizeCombinationalCore ``pMach [] false
      pure (some res.1)
    catch _ => pure none
  sparkleSynthDepth.set 0
  resetRefs
  let cold? : Option Mod ←
    try
      let g ← gatesOf ``pMach
      let res ← cleanLegacy ``pMach g.ec
      pure (some res.1)
    catch _ => pure none
  sparkleSynthDepth.set 0
  resetRefs
  let realInsts : Nat := (real?.map hInsts).getD 0
  let coldInsts : Nat := (cold?.map hInsts).getD 0
  let stale? : Option Bool := match real?, cold? with
    | some _, some _ => some (realInsts != coldInsts)
    | _, _ => none
  emit s!"SINGLEOUTREG pMach: machine shape={bs shape} real={bs real?.isSome} cold={bs cold?.isSome} hIrr insts real={realInsts} cold={coldInsts} => stale hit on a real command={optBs stale?}"
  if stale? != some false then
    bad := bad.push "pMach: a REAL command took a stale single-output hit (instance counts differ), or a run did not return"
  if realInsts == 0 then
    bad := bad.push "pMach: the real entry's module has no hIrr instance statement (the path is not exercised)"
  emit s!"SINGLEOUTREG: 7 nested runs; failing checks {bad.toList}"
  if !bad.isEmpty then
    throwError "SINGLEOUTREG: the regression test of finding I FAILS: {bad.toList}"

end Tests.Compiler.SingleOutNestedRegressionTest
