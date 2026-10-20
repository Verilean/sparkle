import Lean.Elab.Command
import Sparkle

/-! # A nested entry that FAILS still gives its parent's caches back (findings F and G)

WRITTEN, NOT BUILT, NOT RUN: every "expected" below is a PREDICTION from
reading `Sparkle/Compiler/Elab.lean` at `41a835f4`
(`docs/parallel/F-nested-fail-restore.md`), not an observation.

This test ASSERTS. It is meant for `Tests.AllTests` on a tree WITH the fixes
of findings F and G (`synthesizeCombinationalCoreWith` saves the parent's
`sparkleLetWireCache`, `sparkleLoopWireCache`, `sparkleWireCanon` and
`sparkleSubInstanceOutputs` before a nested entry and puts them back in its
`finally` under `depth != 0`). On a tree WITHOUT the fixes it is expected to
FAIL, with one line per ref that was not given back, of the form

    <ref> NOT RESTORED after <case>: <n> entries left, <k> seeded

It imports only `Sparkle` (its children are local), so it does not pull the
census of `NestedLetCacheTest` into the closure of `Tests.AllTests`.

## What is read from the code

`synthesizeCombinationalCoreWith` reads the four refs into locals when
`depth != 0` (Elab.lean 5472–5491), clears them for the child (5510–5515),
sets the depth to `depth + 1` (5516) and runs the synthesis in
`try doSynth finally …` (5529–5540); the `finally` decrements the depth and,
when `depth != 0`, writes the locals back. `getConstInfo declName` is the
first statement of `doSynth` (5522): INSIDE the `try`.

## The nested entries

Each is run as a nested entry sees the world: `sparkleSynthDepth = 1`, the
refs seeded with entries no run writes, through BOTH entry functions —
`synthesizeChild` (what a call site runs, `childSynthEntry`) and
`synthesizeCombinationalCore` (the function with the `finally`, directly).

FAILING:

* `missing` — a name that is not declared. `getConstInfo` throws
  ("unknown constant", PREDICTED text) as the first step inside the `try`:
  the child has cleared the refs and written nothing.
* `fBadW` — a `@[hardware_module]` with two result leaves. The first,
  `(kSD x y).sm + (kSD x y).df`, is the body of `SubInstanceKeyTest.hW`
  (which leaves two port-map entries, measured there); the second is
  `if (0 : Nat) = 0 then x else y`, whose head `ite` the translator refuses
  in `Rec.handleErrorPatterns` (Elab.lean 5662–5670, "if-then-else
  expressions cannot be synthesized to hardware"). `emitLeaves` translates
  the leaves in order and has no `catch`, so (PREDICTED) the throw comes
  AFTER the child wrote its own port-map entries, and after a completed
  nested entry of `kSD` at depth 2.

SUCCEEDING (the control): `okW`, the first leaf of `fBadW` alone.

## The lines

    NESTEDFAIL <ref>: threw=<T/F> restored=<T/F> depthBack=<T/F> [<case>; entries after=<n>, seeded=<k>; depth before=1 after=<d>]
    NESTEDOK <ref>: threw=<T/F> restored=<T/F> depthBack=<T/F> [...]            (the control)
    NESTEDFAIL THREW [<case>]: <the message>
    NESTEDFAIL OTHER [<case>]: …                                                 (the refs outside the fix, LOG ONLY)
    NESTEDFAIL CASE <case> via <entry>: threw=<T/F> intended=<T/F> reachedKid=<T/F> […]
    NESTEDFAIL: <n> runs; failing checks [...]                                    (last line; then the assertion)

`<ref>` is one of `sparkleLetWireCache`, `sparkleLoopWireCache`,
`sparkleWireCanon`, `sparkleSubInstanceOutputs`. `restored`: the ref holds
EXACTLY the seeded entries (same size, every seeded key at its seeded value)
— not empty, not the child's. `depthBack`: `sparkleSynthDepth` reads 1 again.

ASSERTED: in every FAILING run `threw=T`, `restored=T` for the four refs,
`depthBack=T`; in every control run `threw=F`, `restored=T`, `depthBack=T`.

ALSO ASSERTED, per run (the `CASE` line), so that a run failing EARLIER than
meant is not green:

* `intended`: `fBadW` — the message contains "if-then-else expressions cannot
  be synthesized to hardware" (the text of `Rec.handleErrorPatterns`, Elab.lean
  5665); `missing` — it contains "unknown constant"; both compared in lower
  case; `okW` — no throw. Any other error fails the test with its message.
* `reachedKid`: `kSD` is a key of `sparkleSubModuleCache` (written by
  `synthesizeFromConst` when `kSD`'s synthesis returns) or of
  `sparkleChildCache` (written by `synthesizeChild` after it). Neither ref is
  cleared or restored by a NESTED entry (they are cleared at depth 0 only), so
  the key survives the failing run; both are emptied before each run and
  `kSD`'s absence is read just before it, so the key cannot be a seed or a
  cache hit. Required `T` for `fBadW` and `okW`, `F` for `missing`.

`intended=T` for `fBadW` says its SECOND leaf was being translated;
`emitLeaves` reaches it only after the first leaf's translation returned
(READ), and the first leaf is where the port-map entries are written. The
entries themselves cannot be seen after a restore.

PREDICTED on a tree with the fixes: all of them hold, 24 lines `T`.

PREDICTED on a tree without the fixes (poc before `41a835f4`'s change):

* the three finding-F refs: `restored=F` in ALL six runs, `entries after=0`
  in the `missing` runs (the nested entry cleared them and nothing wrote);
* `sparkleSubInstanceOutputs`: `restored=F` in the `fBadW` and `okW` runs
  (seed AND the child's two entries: `entries after=4`), but `restored=T` in
  the `missing` runs — that entry neither cleared the map nor wrote to it,
  so those two lines do NOT tell the trees apart;
* `depthBack=T` everywhere (the decrement was in the `finally` before).

## The reviewer's other two points (not duplicated here)

Sibling order: `SubInstanceKeyTest` rows `WR` / `RW` (`gTopWR`, `gTopRW`) and
their `collision` flags, asserted `F` when `fixed=T`. Same / different
arguments of one callee: its `hW` (`kSD x y` twice) against `hR` (`kSD y x`,
then `kSD x y`) in row `hWR`, the line `CHILD …hR: nested==alone …`.

NOT established: see `docs/parallel/F-nested-fail-restore.md` §5. -/
namespace Tests.Compiler.NestedFailRestoreTest
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit

structure SumDiff (dom : DomainConfig) where
  sm : Signal dom (BitVec 5)
  df : Signal dom (BitVec 5)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (SumDiff dom) dom := ⟨⟩

/-- A combinational child with two outputs (as `SubInstanceKeyTest.kSD`). -/
@[hardware_module]
def kSD {dom : DomainConfig} (x y : Signal dom (BitVec 5)) : SumDiff dom :=
  { sm := x + y, df := x - y }

/-- The control: a nested entry that succeeds and writes two port-map entries
of its own (the body of `SubInstanceKeyTest.hW`). -/
@[hardware_module]
def okW (x y : Signal defaultDomain (BitVec 5)) : Signal defaultDomain (BitVec 5) :=
  (kSD x y).sm + (kSD x y).df

/-- The failing writer: its first leaf is `okW`'s body, its second leaf an
`if … then … else`, which the translator refuses. -/
@[hardware_module]
def fBadW (x y : Signal defaultDomain (BitVec 5)) : SumDiff defaultDomain :=
  { sm := (kSD x y).sm + (kSD x y).df, df := if (0 : Nat) = 0 then x else y }

def kSDName : Name := ``kSD
def okWName : Name := ``okW
def fBadWName : Name := ``fBadW
/-- NOT declared, on purpose. -/
def missingName : Name := `Tests.Compiler.NestedFailRestoreTest.noSuchDeclaration

def bs (b : Bool) : String := if b then "T" else "F"

/-- The depth a nested entry reads: its parent, entered at 0, set it to 1. -/
def nestedDepth : Nat := 1

def seedLet : List (String × String) :=
  [("seed:let:a", "seed_let_wire_a"), ("seed:let:b", "seed_let_wire_b")]
def seedLoop : List (String × String) :=
  [("seed:loop:a", "seed_loop_wire_a"), ("seed:loop:b", "seed_loop_wire_b")]
def seedCanon : List (String × String) :=
  [("seed_canon_a", "seed_canon_b"), ("seed_canon_c", "seed_canon_d")]
def seedSub : List ((UInt64 × String) × String) :=
  [(((0 : UInt64), "seed_port_a"), "seed_sub_wire_a"),
   (((1 : UInt64), "seed_port_b"), "seed_sub_wire_b")]

def seedFvar : Name := `seedFvarOfTheParent
def seedZeta : Name := `seedZetaOfTheParent
def seedWidthWire : String := "seed_width_wire"
def seedSingleKey : String := "seed#single#out"
def seedSingleWire : String := "seed_single_wire"

/-- The map holds exactly the seeded entries. -/
def sameMap {α β : Type} [BEq α] [Hashable α] [BEq β]
    (m : Std.HashMap α β) (seed : List (α × β)) : Bool :=
  m.size == seed.length && seed.all fun p => m.get? p.1 == some p.2

/-- Every per-synthesis ref empty, as an outermost entry starts. -/
def resetAll : MetaM Unit := do
  sparkleTypeCache.set {}
  sparkleSubModuleCache.set {}
  sparkleChildCache.set {}
  sparkleSubInstanceOutputs.set {}
  sparkleSingleOutInstanceCache.set {}
  sparkleFvarValueMap.set {}
  sparkleWireWidthCache.set {}
  sparkleLetWireCache.set {}
  sparkleLoopWireCache.set {}
  sparkleWireCanon.set {}
  sparkleFvarZetaVisited.set {}
  sparkleCallCounter.set 0

/-- The entry function a run goes through. -/
inductive Via where
  | child
  | core

def viaStr : Via → String
  | Via.child => "synthesizeChild"
  | Via.core => "synthesizeCombinationalCore"

def runVia (v : Via) (n : Name) : MetaM Unit := do
  match v with
  | Via.child =>
    let _ ← synthesizeChild n
    pure ()
  | Via.core =>
    let _ ← synthesizeCombinationalCore n [] false
    pure ()

/-- What one run reports. -/
structure Row where
  caseName : String
  expectThrow : Bool
  threw : Bool
  msg : String
  okLet : Bool
  okLoop : Bool
  okCanon : Bool
  okSub : Bool
  nLet : Nat
  nLoop : Nat
  nCanon : Nat
  nSub : Nat
  depthAfter : Nat
  other : String
  /-- lower-case text the message must contain (`""`: the run must return) -/
  needle : String
  expectKid : Bool
  /-- `kSD` was in `sparkleChildCache` / `sparkleSubModuleCache` BEFORE the run -/
  kidBefore : Bool
  reachedKid : Bool
  kidWhere : String

/-- `sub` occurs in `s`. -/
def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The message of the INTENDED failure of `fBadW`, lower case: the text of
`Rec.handleErrorPatterns` (Elab.lean 5665),
"if-then-else expressions cannot be synthesized to hardware.". -/
def needleIte : String := "if-then-else expressions cannot be synthesized to hardware"

/-- The message of `getConstInfo` on an undeclared name, lower case (the
capital of its first letter differs between Lean versions). -/
def needleMissing : String := "unknown constant"

/-- ONE nested entry: the refs seeded as the parent would hold them, the
depth as a nested entry reads it, the entry inside `try … catch`, the refs
read back. Everything is reset before and after. -/
def probe (caseName : String) (v : Via) (n : Name) (expectThrow : Bool)
    (needle : String) (expectKid : Bool) : MetaM Row := do
  resetAll
  -- the four refs of the fix
  sparkleLetWireCache.set (Std.HashMap.ofList seedLet)
  sparkleLoopWireCache.set (Std.HashMap.ofList seedLoop)
  sparkleWireCanon.set (Std.HashMap.ofList seedCanon)
  sparkleSubInstanceOutputs.set (Std.HashMap.ofList seedSub)
  -- refs outside the fix (reported only)
  sparkleFvarValueMap.set
    (({} : Std.HashMap Lean.Name Lean.Expr).insert seedFvar (Lean.mkNatLit 7))
  sparkleWireWidthCache.set (({} : Std.HashMap String Nat).insert seedWidthWire 7)
  sparkleSingleOutInstanceCache.set
    (({} : Std.HashMap String String).insert seedSingleKey seedSingleWire)
  sparkleFvarZetaVisited.set (({} : Std.HashSet Lean.Name).insert seedZeta)
  sparkleSynthDepth.set nestedDepth
  -- reachability cannot come from a cache hit: `resetAll` emptied both module
  -- caches, and that `kSD` is in neither is READ here, just before the run
  let subModBefore ← (sparkleSubModuleCache.get : IO _)
  let childBefore ← (sparkleChildCache.get : IO _)
  let kidBefore : Bool := subModBefore.contains kSDName || childBefore.contains kSDName
  let r : Bool × String ←
    try
      runVia v n
      pure (false, "")
    catch e =>
      let text ← e.toMessageData.toString
      pure (true, text)
  let depthAfter : Nat ← (sparkleSynthDepth.get : IO _)
  let mLet ← (sparkleLetWireCache.get : IO _)
  let mLoop ← (sparkleLoopWireCache.get : IO _)
  let mCanon ← (sparkleWireCanon.get : IO _)
  let mSub ← (sparkleSubInstanceOutputs.get : IO _)
  let mFvar ← (sparkleFvarValueMap.get : IO _)
  let mWidth ← (sparkleWireWidthCache.get : IO _)
  let mSingle ← (sparkleSingleOutInstanceCache.get : IO _)
  let sZeta ← (sparkleFvarZetaVisited.get : IO _)
  let mSubMod ← (sparkleSubModuleCache.get : IO _)
  let mChild ← (sparkleChildCache.get : IO _)
  let mType ← (sparkleTypeCache.get : IO _)
  let okFvar : Bool := mFvar.size == 1 && mFvar.contains seedFvar
  let okWidth : Bool := mWidth.size == 1 && mWidth.get? seedWidthWire == some 7
  let singleKept : Bool := mSingle.get? seedSingleKey == some seedSingleWire
  let zetaKept : Bool := sZeta.contains seedZeta
  let subModKeys : List String := mSubMod.toList.map fun p => toString p.1
  let childKeys : List String := mChild.toList.map fun p => toString p.1
  let inSubMod : Bool := mSubMod.contains kSDName
  let inChild : Bool := mChild.contains kSDName
  let reachedKid : Bool := inSubMod || inChild
  let kidWhere : String :=
    s!"sparkleSubModuleCache={bs inSubMod} sparkleChildCache={bs inChild}"
  let other : String :=
    s!"restored by the entry before the fixes: sparkleFvarValueMap={bs okFvar} (size {mFvar.size}) sparkleWireWidthCache={bs okWidth} (size {mWidth.size}); neither cleared nor restored: sparkleSingleOutInstanceCache seed kept={bs singleKept} size={mSingle.size}, sparkleFvarZetaVisited seed kept={bs zetaKept} size={sZeta.size}, sparkleSubModuleCache keys={subModKeys}, sparkleChildCache keys={childKeys}, sparkleTypeCache size={mType.size}; the run synthesised kSD (it got as far as its instance call)={bs reachedKid}"
  let row : Row := {
    caseName := caseName ++ " via " ++ viaStr v
    expectThrow := expectThrow
    threw := r.1
    msg := r.2
    okLet := sameMap mLet seedLet
    okLoop := sameMap mLoop seedLoop
    okCanon := sameMap mCanon seedCanon
    okSub := sameMap mSub seedSub
    nLet := mLet.size
    nLoop := mLoop.size
    nCanon := mCanon.size
    nSub := mSub.size
    depthAfter := depthAfter
    other := other
    needle := needle
    expectKid := expectKid
    kidBefore := kidBefore
    reachedKid := reachedKid
    kidWhere := kidWhere }
  sparkleSynthDepth.set 0
  resetAll
  pure row

/-- The lines of one run; returns the checks that do not hold. -/
def report (r : Row) : MetaM (Array String) := do
  let tag : String := if r.expectThrow then "NESTEDFAIL" else "NESTEDOK"
  let depthBack : Bool := r.depthAfter == nestedDepth
  let refs : List (String × Bool × Nat × Nat) :=
    [("sparkleLetWireCache", r.okLet, r.nLet, seedLet.length),
     ("sparkleLoopWireCache", r.okLoop, r.nLoop, seedLoop.length),
     ("sparkleWireCanon", r.okCanon, r.nCanon, seedCanon.length),
     ("sparkleSubInstanceOutputs", r.okSub, r.nSub, seedSub.length)]
  let mut bad : Array String := #[]
  for (refName, ok, cnt, seeded) in refs do
    logInfo m!"{tag} {refName}: threw={bs r.threw} restored={bs ok} depthBack={bs depthBack} [{r.caseName}; entries after={cnt}, seeded={seeded}; depth before={nestedDepth} after={r.depthAfter}]"
    if !ok then
      bad := bad.push s!"{refName} NOT RESTORED after {r.caseName}: {cnt} entries left, {seeded} seeded"
  if r.threw then
    let flat : String := r.msg.replace "\n" " | "
    logInfo m!"NESTEDFAIL THREW [{r.caseName}]: {flat}"
  logInfo m!"NESTEDFAIL OTHER [{r.caseName}]: {r.other}"
  -- the intended outcome: the intended message when a throw is expected, a
  -- return otherwise
  let lowered : String := r.msg.toLower
  let intended : Bool :=
    if r.expectThrow then r.threw && hasSub lowered r.needle else !r.threw
  logInfo m!"NESTEDFAIL CASE {r.caseName}: threw={bs r.threw} intended={bs intended} reachedKid={bs r.reachedKid} [expected reachedKid={bs r.expectKid}; kSD cached before the run={bs r.kidBefore}; after: {r.kidWhere}]"
  if r.expectThrow && r.threw && !intended then
    bad := bad.push s!"{r.caseName}: the nested entry threw ANOTHER error than the intended one (expected text '{r.needle}'): {r.msg}"
  if r.kidBefore then
    bad := bad.push s!"{r.caseName}: kSD was already in a module cache before the run (reachability would be a cache hit)"
  if r.reachedKid != r.expectKid then
    bad := bad.push s!"{r.caseName}: reachedKid={bs r.reachedKid}, expected {bs r.expectKid} ({r.kidWhere}): the run did not fail (or return) where intended"
  if r.expectThrow && !r.threw then
    bad := bad.push s!"{r.caseName}: the nested entry was expected to THROW and returned (the failing path was not exercised)"
  if !r.expectThrow && r.threw then
    bad := bad.push s!"{r.caseName}: the control nested entry threw: {r.msg}"
  if !depthBack then
    bad := bad.push s!"sparkleSynthDepth NOT BACK after {r.caseName}: {nestedDepth} before, {r.depthAfter} after"
  pure bad

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let runs : List (String × Via × Name × Bool × String × Bool) :=
    [("FAILING missing declaration", Via.child, missingName, true, needleMissing, false),
     ("FAILING missing declaration", Via.core, missingName, true, needleMissing, false),
     ("FAILING fBadW (writes, then if-then-else)", Via.child, fBadWName, true, needleIte, true),
     ("FAILING fBadW (writes, then if-then-else)", Via.core, fBadWName, true, needleIte, true),
     ("SUCCEEDING okW", Via.child, okWName, false, "", true),
     ("SUCCEEDING okW", Via.core, okWName, false, "", true)]
  let mut bad : Array String := #[]
  for (caseName, v, n, expectThrow, needle, expectKid) in runs do
    let row ← probe caseName v n expectThrow needle expectKid
    let b ← report row
    bad := bad ++ b
  resetAll
  sparkleSynthDepth.set 0
  logInfo m!"NESTEDFAIL: {runs.length} runs; failing checks {bad.toList}"
  if !bad.isEmpty then
    throwError "NESTEDFAIL: a nested entry did not leave its parent's caches as it found them (or the failing path was not exercised): {bad.toList}"

end Tests.Compiler.NestedFailRestoreTest
