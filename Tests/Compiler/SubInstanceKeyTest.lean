import Tests.Compiler.NestedLetCacheTest

/-! # The multi-output instance port map across modules of one top-level run (candidate G)

Uses NO declaration of a candidate: it is meant to build on poc (`85ebb9fd`)
and on the isolated `fix/nested-let-cache-build`; build it on both and diff
the lines. On an entry that does NOT restore the port map around a nested
synthesis (poc, `fix/nested-let-cache-build`) it LOGS ONLY; whether the entry
is the fixed one is MEASURED (`SUBINSTKEY FIXED`, §0 = `fixedProbe`), and only
when `fixed=T` the three `collision` flags are asserted to be `F`
(`docs/parallel/G-fix-candidate.md`). The last existing line keeps its text
("nothing is asserted") — it is true of the unfixed trees; the line after it
says what was asserted. Not in
`Tests.AllTests`. WRITTEN, NOT BUILT: every "expected" below is a PREDICTION
from reading `Sparkle/Compiler/Elab.lean` at `85ebb9fd`
(`docs/parallel/B-cache-keys.md` §1), not an observation.

## What is read from the code

`sparkleSubInstanceOutputs : (UInt64 × String) ↦ String` maps
`(hash (canonHardwareKey callExpr), output port name)` to a WIRE NAME. The
key is the call expression with every free variable replaced by the name of
the wire it denotes; the callee is in it (the head constant), the module
being built is NOT. The ref is cleared at depth 0 only: a nested entry
neither clears nor restores it, and the two readers
(`Rec.handleDefinitionUnfold`, the projection shortcut;
`translateProjInstanceUncachedWith`) return a hit without asking whether the
current builder declares the wire.

## The declarations

`kSD x y` is a combinational two-output child (`sm = x + y`, `df = x - y`).

* `gW` reads `(kSD x y).sm + (kSD x y).df`;
* `gR` reads `(kSD y x).sm + (kSD x y).df` — the SAME walk as `gW` up to the
  order of the first call's arguments, so (prediction) its first instance
  gets the wire names `gW`'s instance got in `gW`;
* `gTopWR = gW x y + gR x y`, `gTopRW = gR x y + gW x y`;
* `hW` / `hR` / `hTopWR`: the same with the projections written directly on
  the call (no `let`).

Inputs of both children are named `x`, `y`, so the key of `kSD x y` is the
same string in both.

## The lines

    SUBINSTKEY FIXED: nested entry ran=<T/F> restores sub-instance port map=<T/F> (entries left=<n>, the seed is 1) => fixed=<T/F> …
    SUBINSTKEY: fixed=<T/F>; collisions [<labels with collision=T>]      (last line; then the assertion when fixed=T)
    SUBINSTKEY <label> alone MODULE <child>: stmts=<n> insts=[…] kSDinsts=<n> undeclared=[…] undriven=[…]
    SUBINSTKEY <label> top <top>: route=<…> modules=[…] leftover sub-instance keys=[<hash>/<port>-><wire>, …]
    SUBINSTKEY <label> nested MODULE <m>: …            (the top, then each child as the nested run built it)
    SUBINSTKEY <label> … MODULE <m> STMT <i>: <statement>
    SUBINSTKEY <label> CHILD <child>: nested==alone <T/F> kSD instances nested=<n> alone=<n> undeclared nested=[…]
    SUBINSTKEY <label> TEXT: <the SystemVerilog of the design>
    SUBINSTKEY <label> DETECT: … => collision=<T/F>

`alone`: the full entry (`synthesizeCombinational`, what a design command and
a nested child synthesis both run) on the child as its own top, from reset
refs at depth 0. `nested`: the same entry on the top; the child's module is
taken from the returned design. Without a collision `nested==alone` is `T`
(the same function on the same declaration; only the refs differ).

PREDICTED on both trees:

* `WR`, `hWR`: `CHILD gW: nested==alone T`; `CHILD gR: nested==alone F`,
  `kSD instances nested=1 alone=2`, `undeclared nested=[]` — the second
  projection of `gR` is answered with `gW`'s entry, a name `gR` itself
  declared for the `df` port of `kSD y x`; emitted `gR = (y+x) + (y-x)`,
  source `(y+x) + (x-y)`. `collision=T`.
* `RW`: `CHILD gR: nested==alone T`; `CHILD gW: nested==alone F` with
  `kSD instances nested=0` and `undeclared nested` not empty (it reads the
  wire names of `gR`'s second instance), or the top run throws.
  `collision=T`.

NOT established: all of the above (nothing was run); the exact wire
numbers; whether a later stage refuses a module that reads undeclared
names. The simulation against the source:
`scripts/shipping-coverage/subinst_key_sim.sh`. -/
namespace Tests.Compiler.SubInstanceKeyTest
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Tests.Compiler.CallWidthHuntTest (Mod Dsn bs resetRefs)
open Tests.Compiler.MachineFallThroughCensusTest (undeclared undriven)
open Tests.Compiler.NestedLetCacheTest (stmtStr instNames routeStr designOf)

structure SumDiff (dom : DomainConfig) where
  sm : Signal dom (BitVec 5)
  df : Signal dom (BitVec 5)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (SumDiff dom) dom := ⟨⟩

/-- A combinational child with two outputs; `df` is not symmetric. -/
@[hardware_module]
def kSD {dom : DomainConfig} (x y : Signal dom (BitVec 5)) : SumDiff dom :=
  { sm := x + y, df := x - y }

/-- The writer: both projections of ONE call `kSD x y`. -/
@[hardware_module]
def gW (x y : Signal defaultDomain (BitVec 5)) : Signal defaultDomain (BitVec 5) :=
  let p := kSD x y
  let q := kSD x y
  p.sm + q.df

/-- The reader: `kSD y x` first, then the call `kSD x y` the writer made. -/
@[hardware_module]
def gR (x y : Signal defaultDomain (BitVec 5)) : Signal defaultDomain (BitVec 5) :=
  let p := kSD y x
  let q := kSD x y
  p.sm + q.df

def gTopWR (x y : Signal defaultDomain (BitVec 5)) : Signal defaultDomain (BitVec 5) :=
  gW x y + gR x y

def gTopRW (x y : Signal defaultDomain (BitVec 5)) : Signal defaultDomain (BitVec 5) :=
  gR x y + gW x y

/-- As `gW`, the projections directly on the calls. -/
@[hardware_module]
def hW (x y : Signal defaultDomain (BitVec 5)) : Signal defaultDomain (BitVec 5) :=
  (kSD x y).sm + (kSD x y).df

/-- As `gR`, the projections directly on the calls. -/
@[hardware_module]
def hR (x y : Signal defaultDomain (BitVec 5)) : Signal defaultDomain (BitVec 5) :=
  (kSD y x).sm + (kSD x y).df

def hTopWR (x y : Signal defaultDomain (BitVec 5)) : Signal defaultDomain (BitVec 5) :=
  hW x y + hR x y

def kSDName : Name := `Tests.Compiler.SubInstanceKeyTest.kSD
def gWName : Name := `Tests.Compiler.SubInstanceKeyTest.gW
def gRName : Name := `Tests.Compiler.SubInstanceKeyTest.gR
def gTopWRName : Name := `Tests.Compiler.SubInstanceKeyTest.gTopWR
def gTopRWName : Name := `Tests.Compiler.SubInstanceKeyTest.gTopRW
def hWName : Name := `Tests.Compiler.SubInstanceKeyTest.hW
def hRName : Name := `Tests.Compiler.SubInstanceKeyTest.hR
def hTopWRName : Name := `Tests.Compiler.SubInstanceKeyTest.hTopWR

/-- The number of instances of the module named `child` in `m`. -/
def instOf (m : Mod) (child : String) : Nat :=
  ((instNames m).filter fun x => x == child).length

/-- One run of the full entry from reset refs at depth 0; the refs are left
as the run left them. `none` and the message: it threw. -/
def runFull (n : Name) : MetaM (Option (Mod × Dsn) × String) := do
  resetRefs
  sparkleSynthDepth.set 0
  let r : Option (Mod × Dsn) × String ←
    try
      let res ← Sparkle.Compiler.Elab.synthesizeCombinational n
      pure (some res, "")
    catch e =>
      let msg ← e.toMessageData.toString
      pure (none, msg)
  sparkleSynthDepth.set 0
  pure r

/-- The module named after a declaration in the design of a result. -/
def findMod (r : Mod × Dsn) (n : Name) : Option Mod :=
  (designOf r).modules.find? fun m => m.name == Sparkle.IR.ModuleName.ofDecl n

def modRow (tag : String) (m : Mod) : MetaM Unit := do
  let child : String := Sparkle.IR.ModuleName.ofDecl kSDName
  logInfo m!"SUBINSTKEY {tag} MODULE {m.name}: stmts={m.body.length} insts={instNames m} kSDinsts={instOf m child} undeclared={undeclared m} undriven={undriven m}"
  let mut i : Nat := 0
  for s in m.body do
    logInfo m!"SUBINSTKEY {tag} MODULE {m.name} STMT {i}: {stmtStr s}"
    i := i + 1

/-- The rows of one top: each child alone, the top, each child as the nested
run built it. Returns the detection flag. -/
def probe (label : String) (top : Name) (kids : List Name) : MetaM Bool := do
  let child : String := Sparkle.IR.ModuleName.ofDecl kSDName
  let mut alone : List (Name × Option Mod) := []
  for k in kids do
    let (r?, msg) ← runFull k
    match r? with
    | some r =>
      modRow (label ++ " alone") r.1
      alone := alone ++ [(k, some r.1)]
    | none =>
      logInfo m!"SUBINSTKEY {label} alone {k}: the run threw: {msg}"
      alone := alone ++ [(k, none)]
  let (t?, tmsg) ← runFull top
  let left := (← (sparkleSubInstanceOutputs.get : IO _)).toList
  let leftS : List String := left.map fun p => toString p.1.1 ++ "/" ++ p.1.2 ++ "->" ++ p.2
  match t? with
  | none =>
    let allAlone : Bool := alone.all fun p => p.2.isSome
    logInfo m!"SUBINSTKEY {label} top {top}: the run threw: {tmsg}"
    logInfo m!"SUBINSTKEY {label} DETECT: the nested run threw; every child compiles alone={bs allAlone} => collision={bs allAlone}"
    resetRefs
    return allAlone
  | some t =>
    let route ← routeStr top
    let modNames : List String := (designOf t).modules.map fun m => m.name
    logInfo m!"SUBINSTKEY {label} top {top}: route={route} modules={modNames} leftover sub-instance keys={leftS}"
    modRow (label ++ " nested") t.1
    let mut bad : Array String := #[]
    for (k, a?) in alone do
      match findMod t k, a? with
      | some mN, some mA =>
        modRow (label ++ " nested") mN
        let same : Bool := mN == mA
        let un : List String := undeclared mN
        logInfo m!"SUBINSTKEY {label} CHILD {k}: nested==alone {bs same} kSD instances nested={instOf mN child} alone={instOf mA child} undeclared nested={un}"
        if !same || !un.isEmpty then bad := bad.push (toString k)
      | _, _ =>
        logInfo m!"SUBINSTKEY {label} CHILD {k}: not comparable (no module of that name in the nested design, or the alone run threw)"
    let text := Sparkle.Backend.Verilog.toVerilogDesignChecked (designOf t)
    logInfo m!"SUBINSTKEY {label} TEXT:\n{text}"
    logInfo m!"SUBINSTKEY {label} DETECT: children whose nested module differs from their alone module or reads undeclared names: {bad.toList} => collision={bs (!bad.isEmpty)}"
    resetRefs
    return !bad.isEmpty

/-- §0, is the entry the FIXED one? MEASURED, not assumed: the port map is
seeded with one entry no run writes, the child `hW` (which writes two entries
of its own, the ports of `kSD x y`) is synthesised as a NESTED entry (depth
1), and the map is read back. An entry that saves and restores the parent's
map leaves exactly the seed; the entry of `85ebb9fd` / `83b2faf9` leaves the
seed AND `hW`'s entries. Returns (the nested run returned, the map is exactly
the seed, the number of entries left). -/
def fixedProbe : MetaM (Bool × Bool × Nat) := do
  resetRefs
  let seed : Std.HashMap (UInt64 × String) String :=
    ({} : Std.HashMap (UInt64 × String) String).insert ((0 : UInt64), "seed_port") "seed_sub_wire"
  sparkleSubInstanceOutputs.set seed
  sparkleSynthDepth.set 1
  let nestedRan : Bool ←
    try
      let _ ← synthesizeChild hWName
      pure true
    catch _ => pure false
  sparkleSynthDepth.set 0
  let left := (← (sparkleSubInstanceOutputs.get : IO _)).toList
  let okSub : Bool := left == [(((0 : UInt64), "seed_port"), "seed_sub_wire")]
  resetRefs
  pure (nestedRan, okSub, left.length)

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let (nestedRan, okSub, leftN) ← fixedProbe
  let fixed : Bool := nestedRan && okSub
  logInfo m!"SUBINSTKEY FIXED: nested entry ran={bs nestedRan} restores sub-instance port map={bs okSub} (entries left={leftN}, the seed is 1) => fixed={bs fixed} (assertions are made only when it is T)"
  let wr ← probe "WR" gTopWRName [gWName, gRName]
  let rw ← probe "RW" gTopRWName [gWName, gRName]
  let hwr ← probe "hWR" hTopWRName [hWName, hRName]
  resetRefs
  sparkleSynthDepth.set 0
  logInfo m!"SUBINSTKEY: collision WR={bs wr} RW={bs rw} hWR={bs hwr} (logged only; nothing is asserted)"
  let colls : List String :=
    (if wr then ["WR"] else []) ++ (if rw then ["RW"] else []) ++ (if hwr then ["hWR"] else [])
  logInfo m!"SUBINSTKEY: fixed={bs fixed}; collisions {colls}"
  if fixed then
    if wr || rw || hwr then
      throwError "SUBINSTKEY: the nested entry restores the parent's sub-instance port map, but a child's nested module still differs from its alone module or reads undeclared names: WR={bs wr} RW={bs rw} hWR={bs hwr}"

end Tests.Compiler.SubInstanceKeyTest
