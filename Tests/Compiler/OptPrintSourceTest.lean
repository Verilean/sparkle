import Tests.Compiler.NestedLetCacheTest
import Tests.Compiler.OptPrintGuardDefs

/-! # Signal sources for the optimizer / print-guard gap (round par/b-19)

LOG ONLY: asserts nothing, proves nothing, never throws. Target-built, NOT
for `Tests.AllTests`. WRITTEN, NOT BUILT.

`docs/parallel/A-leaf-entry-2.md` §3 (confirmed by evaluation on the
hand-written module `optCex`): in its instance-free assign + register branch
`checkedOptimize` returns the optimizer's candidate after `refineCheck` only
(`Sparkle/IR/RefineCheck.lean` 385–386) — the candidate may be outside the
print fragment (`printOk` false) although the module was inside. No Signal
source producing such a module was known. This file writes declarations a
user could write and LOGS what the real entry and the real checked optimizer
do with them.

## The declarations

All are `circuit do` register machines over `defaultDomain` with the enable
mux of `CallWidthHuntTest.kCount` (the idiom known to take the machine
route). `c k` stands for `(Signal.pure k#w : Signal defaultDomain (BitVec w))`.

| declaration | next value (enable arm) | predicted `printOk (checkedOptimize b)` |
|---|---|---|
| `shlAdd32` | `(rs <<< c 2) + c 1`, width 32 | F |
| `shlAddLet32` | `let t := rs <<< c 2`; `t + c 1` | F |
| `shlAdd8` / `shlAdd16` | the same at width 8 / 16 | T (the inliner's `& mask`) |
| `shlAdd64` | the same at width 64 | F |
| `shlAddLit32` | `(rs <<< 2#32) + 1#32` (literal operands) | F |
| `shlVar32` | `(rs <<< (x &&& c 7)) + c 1` (amount not a literal) | T |
| `shlSub32` | `(rs <<< c 2) - c 1` | F |
| `shlAnd32` | `(rs <<< c 2) &&& x` | T (`shlSideOK`) |
| `shlMux32` | `rs <<< c 2` as the mux arm itself | T |
| `shlEq32` | condition `(rs <<< c 2) === x` | F |
| `addShlRight32` | `c 1 + (rs <<< c 2)` (shift on the RIGHT) | T |

These are PREDICTIONS made by reading `sf4` (`Sparkle/IR/PrintGuard.lean`
141–226: `notShl = !isShlLit a` looks at the LEFT operand only) and the
optimizer; the shape of the machine-route module was not seen. The reasoning
is in `docs/parallel/B-optprint.md` §2.

## The lines

    OPTPRINT SRC <decl>: route=<…> branch=<simple/seq/other/inst> instFree=<T/F> stmts=<n> printOk(b)=<T/F> opt!=b=<T/F> refineCheck(b,opt b)=<T/F> printOk(opt b)=<T/F> checkedOptimize(b)==b=<T/F> printOk(checkedOptimize b)=<T/F> guard-changes-shipped=<T/F> printOk(guarded)=<T/F> hit=<T/F>
    OPTPRINT SRC <decl> B <i>: <statement of b>
    OPTPRINT SRC <decl> SHIPPED <i>: <statement of checkedOptimize b>
    OPTPRINT SRC <decl> TEXT:\n<emitModule (checkedOptimize b)>
    OPTPRINT SRC <decl> GUARDED TEXT:\n<emitModule (guardedOptimize b)>      (only when it differs)
    OPTPRINT SRC SUMMARY: …

`b`: the module of the full entry `synthesizeCombinational` (the entry, the
zero-width cleanup, the checked merge) — the endpoints' `b`, the module the
design writer sends through `checkedOptimize`. `route`: `routeOf` of
`CallWidthHuntTest` on the core run. `hit`: branch `seq`, `printOk b`,
candidate accepted and `printOk (checkedOptimize b) = false` — the situation
of `optCex` on a real source. `guarded`: `OptPrintGuardDefs.guardedOptimize`
(the candidate guard, computed here; the compiler is not changed).

A `hit` is NOT a wrong output: it says the shipped text is outside the
fragment for which "text meaning = IR meaning" is proved. Whether the text
differs from the source is what `scripts/shipping-coverage/optprint_sim.sh`
measures. -/
namespace Tests.Compiler.OptPrintSourceTest
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Tests.Compiler.CallWidthHuntTest (resetRefs routeOf)
open Tests.Compiler.OptPrintGuardDefs

/-- Width 32, the shift on the left of `+`. -/
def shlAdd32 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 32) :=
  circuit do
    let r ← Signal.reg 0#32
    let rs := (r : Signal defaultDomain (BitVec 32))
    r <~ Signal.mux en
      ((rs <<< (Signal.pure 2#32 : Signal defaultDomain (BitVec 32))) +
        (Signal.pure 1#32 : Signal defaultDomain (BitVec 32))) rs
    return rs

/-- The same with the shift bound by a `let`. -/
def shlAddLet32 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 32) :=
  circuit do
    let r ← Signal.reg 0#32
    let rs := (r : Signal defaultDomain (BitVec 32))
    let t := rs <<< (Signal.pure 2#32 : Signal defaultDomain (BitVec 32))
    r <~ Signal.mux en (t + (Signal.pure 1#32 : Signal defaultDomain (BitVec 32))) rs
    return rs

def shlAdd8 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    r <~ Signal.mux en
      ((rs <<< (Signal.pure 2#8 : Signal defaultDomain (BitVec 8))) +
        (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))) rs
    return rs

def shlAdd16 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 16) :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal defaultDomain (BitVec 16))
    r <~ Signal.mux en
      ((rs <<< (Signal.pure 2#16 : Signal defaultDomain (BitVec 16))) +
        (Signal.pure 1#16 : Signal defaultDomain (BitVec 16))) rs
    return rs

def shlAdd64 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 64) :=
  circuit do
    let r ← Signal.reg 0#64
    let rs := (r : Signal defaultDomain (BitVec 64))
    r <~ Signal.mux en
      ((rs <<< (Signal.pure 2#64 : Signal defaultDomain (BitVec 64))) +
        (Signal.pure 1#64 : Signal defaultDomain (BitVec 64))) rs
    return rs

/-- Literal operands (the idiom of `IP/RV32/Divider.lean` 151 and
`IP/RV32/CLINT.lean` 57). -/
def shlAddLit32 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 32) :=
  circuit do
    let r ← Signal.reg 0#32
    let rs := (r : Signal defaultDomain (BitVec 32))
    r <~ Signal.mux en ((rs <<< 2#32) + 1#32) rs
    return rs

/-- The amount is not a literal. -/
def shlVar32 (en : Signal defaultDomain Bool) (x : Signal defaultDomain (BitVec 32)) :
    Signal defaultDomain (BitVec 32) :=
  circuit do
    let r ← Signal.reg 1#32
    let rs := (r : Signal defaultDomain (BitVec 32))
    r <~ Signal.mux en
      ((rs <<< (x &&& (Signal.pure 7#32 : Signal defaultDomain (BitVec 32)))) +
        (Signal.pure 1#32 : Signal defaultDomain (BitVec 32))) rs
    return rs

/-- The shift on the left of `-`. -/
def shlSub32 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 32) :=
  circuit do
    let r ← Signal.reg 3#32
    let rs := (r : Signal defaultDomain (BitVec 32))
    r <~ Signal.mux en
      ((rs <<< (Signal.pure 2#32 : Signal defaultDomain (BitVec 32))) -
        (Signal.pure 1#32 : Signal defaultDomain (BitVec 32))) rs
    return rs

/-- The shift on the left of `&&&`. -/
def shlAnd32 (en : Signal defaultDomain Bool) (x : Signal defaultDomain (BitVec 32)) :
    Signal defaultDomain (BitVec 32) :=
  circuit do
    let r ← Signal.reg 4294967295#32
    let rs := (r : Signal defaultDomain (BitVec 32))
    r <~ Signal.mux en
      ((rs <<< (Signal.pure 2#32 : Signal defaultDomain (BitVec 32))) &&& x) rs
    return rs

/-- The shift as a mux arm. -/
def shlMux32 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 32) :=
  circuit do
    let r ← Signal.reg 1#32
    let rs := (r : Signal defaultDomain (BitVec 32))
    r <~ Signal.mux en (rs <<< (Signal.pure 2#32 : Signal defaultDomain (BitVec 32))) rs
    return rs

/-- The shift on the left of a comparison. -/
def shlEq32 (en : Signal defaultDomain Bool) (x : Signal defaultDomain (BitVec 32)) :
    Signal defaultDomain (BitVec 32) :=
  circuit do
    let r ← Signal.reg 0#32
    let rs := (r : Signal defaultDomain (BitVec 32))
    let hit := (rs <<< (Signal.pure 2#32 : Signal defaultDomain (BitVec 32))) === x
    r <~ Signal.mux en
      (Signal.mux hit (Signal.pure 0#32 : Signal defaultDomain (BitVec 32))
        (rs + (Signal.pure 1#32 : Signal defaultDomain (BitVec 32)))) rs
    return rs

/-- The contrast: the shift on the RIGHT of `+`. -/
def addShlRight32 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 32) :=
  circuit do
    let r ← Signal.reg 0#32
    let rs := (r : Signal defaultDomain (BitVec 32))
    r <~ Signal.mux en
      ((Signal.pure 1#32 : Signal defaultDomain (BitVec 32)) +
        (rs <<< (Signal.pure 2#32 : Signal defaultDomain (BitVec 32)))) rs
    return rs

/-- The declarations, by name (single-backtick names: a declaration that did
not elaborate is reported by its row, the others still run), with the
PREDICTED `printOk (checkedOptimize b)`. -/
def decls : List (Name × Bool) :=
  [ (`Tests.Compiler.OptPrintSourceTest.shlAdd32, false),
    (`Tests.Compiler.OptPrintSourceTest.shlAddLet32, false),
    (`Tests.Compiler.OptPrintSourceTest.shlAdd8, true),
    (`Tests.Compiler.OptPrintSourceTest.shlAdd16, true),
    (`Tests.Compiler.OptPrintSourceTest.shlAdd64, false),
    (`Tests.Compiler.OptPrintSourceTest.shlAddLit32, false),
    (`Tests.Compiler.OptPrintSourceTest.shlVar32, true),
    (`Tests.Compiler.OptPrintSourceTest.shlSub32, false),
    (`Tests.Compiler.OptPrintSourceTest.shlAnd32, true),
    (`Tests.Compiler.OptPrintSourceTest.shlMux32, true),
    (`Tests.Compiler.OptPrintSourceTest.shlEq32, false),
    (`Tests.Compiler.OptPrintSourceTest.addShlRight32, true) ]

def oneLine (f : Std.Format) : String := (f.pretty 1000000).replace "\n" " "

def stmtStr : Sparkle.IR.AST.Stmt → String
  | Sparkle.IR.AST.Stmt.assign l r => "assign " ++ l ++ " = " ++ oneLine (repr r)
  | s => oneLine (repr s)

/-- The core run (for the route) and the full entry, from reset refs. -/
def runBoth (n : Name) : MetaM (String × Mod × Dsn) := do
  resetRefs
  sparkleSynthDepth.set 0
  let (raw, _) ← synthesizeCombinationalCore n [] false
  let (route, _, _) ← routeOf n raw
  resetRefs
  sparkleSynthDepth.set 0
  let (b, d) ← Sparkle.Compiler.Elab.synthesizeCombinational n
  return (route, b, d)

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let mut ran : Nat := 0
  let mut hits : Array String := #[]
  let mut predOk : Nat := 0
  let mut predBad : Array String := #[]
  let mut notRun : Array String := #[]
  for (n, pred) in decls do
    let r? : Option (String × Mod × Dsn) ←
      try
        let r ← runBoth n
        pure (some r)
      catch e =>
        let msg ← e.toMessageData.toString
        logInfo m!"OPTPRINT SRC {n}: the run threw: {clip 400 msg}"
        pure none
    (sparkleSynthDepth.set 0 : IO Unit)
    resetRefs
    match r? with
    | none => notRun := notRun.push (toString n)
    | some (route, b, _) =>
      ran := ran + 1
      let ob := optObs b
      let k := Sparkle.IR.OptCheck.checkedOptimize b
      let g := guardedOptimize b
      let pg : Bool := Sparkle.IR.PrintGuard.printOk g
      let hit : Bool := ob.branch == "seq" && ob.pm && !ob.kept && !ob.pk
      if hit then hits := hits.push (toString n)
      if ob.pk == pred then predOk := predOk + 1
      else predBad := predBad.push s!"{n} (predicted {tf pred}, got {tf ob.pk})"
      logInfo m!"OPTPRINT SRC {n}: route={route} branch={ob.branch} instFree={tf (instFree b)} stmts={b.body.length} printOk(b)={tf ob.pm} opt!=b={tf ob.differs} refineCheck(b,opt b)={tf ob.rc} printOk(opt b)={tf ob.po} checkedOptimize(b)==b={tf ob.kept} printOk(checkedOptimize b)={tf ob.pk} guard-changes-shipped={tf (!ob.sameUnderGuard)} printOk(guarded)={tf pg} hit={tf hit}"
      let mut i : Nat := 0
      for s in b.body do
        logInfo m!"OPTPRINT SRC {n} B {i}: {stmtStr s}"
        i := i + 1
      let mut j : Nat := 0
      for s in k.body do
        logInfo m!"OPTPRINT SRC {n} SHIPPED {j}: {stmtStr s}"
        j := j + 1
      logInfo m!"OPTPRINT SRC {n} TEXT:\n{Sparkle.Backend.Verilog.emitModule k}"
      if !ob.sameUnderGuard then
        logInfo m!"OPTPRINT SRC {n} GUARDED TEXT:\n{Sparkle.Backend.Verilog.emitModule g}"
  logInfo m!"OPTPRINT SRC SUMMARY: {ran} of {decls.length} declarations ran (not run: {notRun.toList}); hits (branch seq, printOk b, candidate accepted, printOk of the shipped module false) {hits.size} {hits.toList}; predictions of printOk(checkedOptimize b) right {predOk}, wrong {predBad.size} {predBad.toList}. A hit is a shipped text outside the proved print fragment, NOT a wrong output: see scripts/shipping-coverage/optprint_sim.sh"

end Tests.Compiler.OptPrintSourceTest
