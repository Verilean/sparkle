import Sparkle
import Sparkle.Core.CircuitDo
import Sparkle.Core.StateMacro
import Sparkle.Compiler.InlineAttr
import Tools.ShippingReaderFuelDriver
import Tests.Compiler.ReaderFuelGridTest
import Tests.Compiler.MultiInstanceTest
import Tests.Compiler.Issue107LetBoundInstanceDup

/-! # SHADOW: the doubling driver against the real reader on a FIXED list

TARGET-ONLY (`lake build Tests.Compiler.ReaderFuelShadowTest`); not in
`Tests.AllTests`. WRITTEN, NOT BUILT (worker I, branch `par/r-13`, reviewer
ruling 2026-10-16). Nothing in the compiler changes; production still calls
the `partial` `machineShape?`. No full corpus, no environment sweep.

40 cases (40 constants), listed explicitly below (`## The fixed list`), in seven
groups: loops; nested / shared sub-machines; calls and callers of callers;
`instS` (structure-typed instance results); multi-output machines; memory
machines; ordinary refusals.

## Where the declarations come from

* IMPORTED (cheap: no endpoint generation in these modules):
  `Tests.Compiler.ReaderFuelGridTest` (BUILT, target-only; its own 18 grid
  cases ran when it was built and are NOT re-run on import),
  `Tests.Compiler.MultiInstanceTest` (in `Tests.AllTests`; only
  `#assertHwInstances` / `#synthesizeVerilog`),
  `Tests.Compiler.Issue107LetBoundInstanceDup` (only `#assertInstCount*`).
* COPIED here (verbatim up to namespace / `section variable`), because their
  home modules run `#machine_endpoint` / `#machine_composed*` /
  `#machine_ships_hier*` / `generate`, which a stale olean would re-run:
  `ShippingMachineSeqTest` (CntOut, cnt, parent, chained, mid, grand),
  `ShippingMachineDepthHTest` (rcH, midH, grandH), `ShippingDesignSVTest`
  (mid2, topD2, mixD1), `ShippingChildBoundaryTest` (mixDeep),
  `ShippingMachineNestTest` (latch2, Pair, pair, Out, source, consumer),
  `ShippingMachineTeleTest` (PulseOut, CountOut, detect, countOn, chain3),
  `ShippingMachineFuseTest` (innerCnt, siblings, withMemory),
  `ShippingMachineLinkedTest` (pickByteH, counterB, callerLN),
  `ShippingMachineInstTest` (pickD, callerD), `ShippingMachineLoopTest`
  (wholeLoop, loopPair), `ShippingMachineMemLinkedTest` (mixedMems).
  Two refusals are written here (`loopCall`, `natSig`).

## Per case

Two commands per case. The first logs (and writes to stderr, flushed)

    SHADOW CASE START <label>

and ENDS, so the line is reported before the work starts. The second runs
the work on a dedicated task under a wall-clock guard of `caseBudgetMs` and
logs ONE line, BEFORE any comparison verdict is acted on:

    SHADOW <label> [<group>]: real=<OK|FAIL> driver=<OK|FAIL|OUT> path=<…> fields=<…> equal=<true|false> doublings=<k> fuel=<n> realMs=<t> driverMs=<t>

* `real` = the class of the real `machineShape?` on the real entry constant
  (`entryConst true sm ps ci …`, as the elaborator builds it);
* `driver` = `driveShape defaultRounds 1` (START FUEL 1, doubling on OUT only);
* `path` = `OK@1` / `FAIL@1` (decided at the start fuel, no doubling),
  `OUT→OK` / `OUT→FAIL` (decided after doubling), `OUT(budget)` (still OUT
  after `defaultRounds` doublings: undecided within the trial budget);
* `fields` = ALL-FIELD comparison of the two `MachineShape`s when both are
  OK: `all-equal`, or `differ:<f,…>` naming every differing field among
  `binders, body, layout.slots, layout.outs, layout.resetKind, layout.lets,
  runs, insts, loops, instFields` (every field of `MachineShape` and of its
  `Layout`, each compared with its `BEq`; `body` by `Expr` `==`); `n/a`
  otherwise;
* `equal` = same class and, on OK, `fields=all-equal`;
* `doublings`, `fuel` = the driver's doublings and final fuel;
* `realMs`, `driverMs` = `IO.monoMsNow` around each (the answer is forced,
  by branching on a key the compiler cannot fold, before the second clock
  read).

A case whose work does not return within `caseBudgetMs` logs instead

    SHADOW <label> [<group>]: TIMEOUT after <ms> ms (no class: the real reader or the driver did not return)

— a hang is NEVER reported as OUT (OUT is a value the driver returns). A
TIMEOUT is a warning, not an error; the stuck task cannot be cancelled (pure
code) and keeps its thread, so the integrator's outer `cgrun` timeout stays
the backstop: a hang the guard cannot catch shows up as a `SHADOW CASE START`
with no `SHADOW <label>` line after it. A case errors (after its line) iff
`equal=false`. Peak memory is recorded by the integrator's `cgrun`.

## PREDICTED (by reading; NOT observed)

* every machine case (33): `real=OK driver=OK path=OUT→OK fields=all-equal
  equal=true`, `doublings` 4–6, `fuel` 16–64 (the grid measured 4–5 / 16–32
  on the small bodies; the deeper ones — `mixDeep`, `topD2`, `chain3`,
  `siblings`, `withMemory`, `mesh2x2` — may need one more doubling);
  lowest confidence in the OK class of the slotless parents `mesh2x2`,
  `twinCalls` (no register of their own, structure children: admitted by
  the `n = 0` test only through `instStruct`) and of `pair`, `source`
  (structure results with no enclosing machine / unascribed constructor);
  whatever the class, `equal=true` is the prediction;
* `twoLoops`, `opaqueInit`, `loopCall`: `real=FAIL driver=FAIL
  path=OUT→FAIL fields=n/a equal=true` (refused only after reading);
* `notHw`, `natSig`, `gridInit`, `latchSymbolic`: `real=FAIL driver=FAIL
  path=FAIL@1 fields=n/a equal=true doublings=0 fuel=1` (refused before any
  reader call, `machineShapeF_of_pre_none`);
* no TIMEOUT; `realMs`, `driverMs` small (≤ 100 ms each). -/
namespace Tests.Compiler.ReaderFuelShadowTest
open Lean Elab Command Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Tools.ShippingReaderFuel (driveShape defaultRounds resClass DriveResult)
open Tests.Compiler.ReaderFuelGridTest (latch stage pick)

/-! ## Copied declarations -/

/-! ### `ShippingMachineSeqTest` (copies) -/

structure CntOut (dom : DomainConfig) where
  n : Signal dom (BitVec 8)
  hit : Signal dom Bool
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (CntOut dom) dom := ⟨⟩

/-- `ShippingMachineSeqTest.cnt`. -/
@[hardware_module] def cnt {dom : DomainConfig} (en : Signal dom Bool) : CntOut dom :=
  circuit do
    let c ← Signal.reg 0#8
    let cs := (c : Signal dom (BitVec 8))
    c <~ Signal.mux en (cs + (Signal.pure 1#8 : Signal dom (BitVec 8))) cs
    return ({ n := cs, hit := cs === (Signal.pure 7#8 : Signal dom (BitVec 8)) } : CntOut dom)

/-- `ShippingMachineSeqTest.parent`. -/
def parent (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let k := cnt en
    r <~ Signal.mux k.hit (rs + k.n) rs
    return rs

/-- `ShippingMachineSeqTest.chained`. -/
def chained (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let k := cnt en
    let k2 := cnt k.hit
    r <~ Signal.mux k2.hit (rs + k.n) rs
    return rs

/-- `ShippingMachineSeqTest.mid`. -/
@[hardware_module] def mid {dom : DomainConfig} (en : Signal dom Bool) : CntOut dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let k := cnt en
    r <~ k.n
    return ({ n := rs, hit := k.hit } : CntOut dom)

/-- `ShippingMachineSeqTest.grand`. -/
def grand (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let m := mid en
    let nz := ((fun c => !(c == 0#8)) <$> m.n : Signal defaultDomain Bool)
    r <~ Signal.mux (m.hit &&& nz) (rs + m.n) rs
    return rs

/-! ### `ShippingMachineDepthHTest` (copies) -/

/-- `ShippingMachineDepthHTest.rcH`. -/
@[hardware_module]
def rcH {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.mux (x === (Signal.pure 0#8 : Signal dom (BitVec 8)))
    (Signal.pure 1#8 : Signal dom (BitVec 8)) (x + x)

/-- `ShippingMachineDepthHTest.midH`. -/
@[hardware_module]
def midH {dom : DomainConfig} (en : Signal dom Bool) : CntOut dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let y := rcH rs
    r <~ Signal.mux en y rs
    return ({ n := rs, hit := rs === (Signal.pure 7#8 : Signal dom (BitVec 8)) } : CntOut dom)

/-- `ShippingMachineDepthHTest.grandH`. -/
def grandH (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let m := midH en
    r <~ Signal.mux m.hit (rs + m.n) rs
    return rs

/-! ### `ShippingDesignSVTest` and `ShippingChildBoundaryTest` (copies) -/

/-- `ShippingDesignSVTest.mid2`. -/
@[hardware_module]
def mid2 {dom : DomainConfig} (en : Signal dom Bool) : CntOut dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let k := midH en
    r <~ Signal.mux k.hit (rs + k.n) rs
    return ({ n := rs, hit := k.hit } : CntOut dom)

/-- `ShippingDesignSVTest.topD2`. -/
def topD2 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let m := mid2 en
    r <~ Signal.mux m.hit (rs + m.n) rs
    return rs

/-- `ShippingDesignSVTest.mixD1`. -/
def mixD1 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let a := midH en
    let b := cnt en
    r <~ Signal.mux a.hit (rs + b.n) rs
    return rs

/-- `ShippingChildBoundaryTest.mixDeep`. -/
def mixDeep (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let a := mid2 en
    let b := midH en
    let c := cnt en
    r <~ Signal.mux a.hit (rs + b.n + c.n) rs
    return rs

/-! ### `ShippingMachineNestTest` (copies; `latch` / `stage` are the grid's
copies of the same declarations) -/

/-- `ShippingMachineNestTest.latch2`. -/
def latch2 {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  latch (latch x)

/-- `ShippingMachineNestTest.Pair`. -/
structure Pair (dom : DomainConfig) where
  a : Signal dom (BitVec 8)
  b : Signal dom (BitVec 8)

/-- `ShippingMachineNestTest.pair`. -/
def pair {dom : DomainConfig} (x y : Signal dom (BitVec 8)) : Pair dom :=
  { a := latch x, b := stage y (Signal.pure true) }

/-- `ShippingMachineNestTest.Out`. -/
structure Out (dom : DomainConfig) where
  v : Signal dom (BitVec 8)
  f : Signal dom Bool
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (Out dom) dom := ⟨⟩

/-- `ShippingMachineNestTest.source`. -/
def source {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Out dom :=
  circuit do
    let c ← Signal.reg 0#8
    let cS := (c : Signal dom (BitVec 8))
    c <~ cS + x
    return { v := cS, f := cS === (Signal.pure 3#8) }

/-- `ShippingMachineNestTest.consumer`. -/
def consumer {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  circuit do
    let s := source x
    let n ← Signal.reg 0#8
    let nS := (n : Signal dom (BitVec 8))
    n <~ Signal.mux s.f (nS + s.v) nS
    return nS

/-! ### `ShippingMachineTeleTest` (copies) -/

structure PulseOut (dom : DomainConfig) where
  hit : Signal dom Bool
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (PulseOut dom) dom := ⟨⟩

structure CountOut (dom : DomainConfig) where
  n : Signal dom (BitVec 8)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (CountOut dom) dom := ⟨⟩

/-- `ShippingMachineTeleTest.detect`. -/
def detect {dom : DomainConfig} (x : Signal dom (BitVec 8)) : PulseOut dom :=
  circuit do
    let h ← Signal.reg false
    h <~ (x === (Signal.pure 7#8 : Signal dom (BitVec 8)))
    return ({ hit := (h : Signal dom Bool) } : PulseOut dom)

/-- `ShippingMachineTeleTest.countOn`. -/
def countOn {dom : DomainConfig} (en : Signal dom Bool) : CountOut dom :=
  circuit do
    let c ← Signal.reg 0#8
    let cs := (c : Signal dom (BitVec 8))
    c <~ Signal.mux en (cs + (Signal.pure 1#8 : Signal dom (BitVec 8))) cs
    return ({ n := cs } : CountOut dom)

/-- `ShippingMachineTeleTest.chain3`: the same sub-machine (`countOn`) twice. -/
def chain3 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let d := detect x
  let k := countOn d.hit
  let k2 := countOn (d.hit &&& (k.n === (Signal.pure 3#8 : Signal defaultDomain (BitVec 8))))
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    r <~ k2.n ^^^ rs
    return rs

/-! ### `ShippingMachineFuseTest` (copies) -/

/-- `ShippingMachineFuseTest.innerCnt`. -/
def innerCnt (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  let s := Signal.loop fun (s : Signal defaultDomain (BitVec 8)) =>
    Signal.register 0#8 (Signal.mux go (s + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))) s)
  s

/-- `ShippingMachineFuseTest.siblings`: the same inner loop twice. -/
def siblings (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 8)) =>
    let c1 := innerCnt en
    let c2 := innerCnt (c1 === (Signal.pure 3#8 : Signal defaultDomain (BitVec 8)))
    Signal.register 0#8 (st + c1 + c2)
  st

/-- `ShippingMachineFuseTest.withMemory`. -/
def withMemory (we : Signal defaultDomain Bool) (wd : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let rd := Signal.memoryComboRead addr wd we addr
    let _dead := Signal.memoryComboRead addr wd we (Signal.pure 0#4)
    let c := innerCnt (rd === (Signal.pure 0#8 : Signal defaultDomain (BitVec 8)))
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 (rd + c))
  Signal.snd st

/-! ### `ShippingMachineLinkedTest` and `ShippingMachineInstTest` (copies) -/

/-- `ShippingMachineLinkedTest.pickByteH`. -/
@[hardware_module]
def pickByteH (w : Signal defaultDomain (BitVec 16)) (sel : Signal defaultDomain (BitVec 2)) :
    Signal defaultDomain (BitVec 8) :=
  let hi := w.map (BitVec.extractLsb' 8 8 ·)
  let lo := w.map (BitVec.extractLsb' 0 8 ·)
  let x := hi ^^^ lo
  Signal.mux (sel === (Signal.pure 0#2 : Signal defaultDomain (BitVec 2))) hi
    (Signal.mux (sel === (Signal.pure 1#2 : Signal defaultDomain (BitVec 2))) lo
      (Signal.mux (sel === (Signal.pure 2#2 : Signal defaultDomain (BitVec 2))) x (x + x)))

/-- `ShippingMachineLinkedTest.counterB`. -/
def counterB (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 2) :=
  circuit do
    let c ← Signal.reg 0#2
    let cS := (c : Signal defaultDomain (BitVec 2))
    c <~ Signal.mux en (cS + (Signal.pure 1#2 : Signal defaultDomain (BitVec 2))) cS
    return cS

/-- `ShippingMachineLinkedTest.callerLN`. -/
def callerLN (w : Signal defaultDomain (BitVec 16)) (en : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let s := counterB en
    let acc ← Signal.reg 0#16
    let accS := (acc : Signal defaultDomain (BitVec 16))
    acc <~ accS ^^^ w
    return pickByteH accS s

/-- `ShippingMachineInstTest.pickD`. -/
@[hardware_module]
def pickD {dom : DomainConfig} (sel : Signal dom (BitVec 2)) (x : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) :=
  Signal.mux (sel === (Signal.pure 0#2 : Signal dom (BitVec 2))) x
    (x ^^^ (Signal.pure 0xFF#8 : Signal dom (BitVec 8)))

/-- `ShippingMachineInstTest.callerD`. -/
def callerD {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  circuit do
    let sel ← Signal.reg 0#2
    let acc ← Signal.reg 0#8
    let selS := (sel : Signal dom (BitVec 2))
    let accS := (acc : Signal dom (BitVec 8))
    let y := pickD selS (accS + x)
    sel <~ selS + (Signal.pure 1#2 : Signal dom (BitVec 2))
    acc <~ y
    return y

/-! ### `ShippingMachineLoopTest` and `ShippingMachineMemLinkedTest` (copies) -/

/-- `ShippingMachineLoopTest.wholeLoop`. -/
def wholeLoop : Signal defaultDomain (BitVec 8) :=
  Signal.loop fun (self : Signal defaultDomain (BitVec 8)) =>
    Signal.register 0#8 (self + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8)))

/-- `ShippingMachineLoopTest.loopPair`. -/
def loopPair (start : Signal defaultDomain Bool) (act : Signal defaultDomain (BitVec 32)) :
    Signal defaultDomain (BitVec 32 × BitVec 32) :=
  Signal.loop fun (self : Signal defaultDomain (BitVec 32 × BitVec 32)) =>
    let counter := Signal.fst self
    let acc := Signal.snd self
    let nextCounter : Signal defaultDomain (BitVec 32) :=
      Signal.mux start (Signal.pure 0#32 : Signal defaultDomain (BitVec 32))
        (counter + (Signal.pure 1#32 : Signal defaultDomain (BitVec 32)))
    let nextAcc : Signal defaultDomain (BitVec 32) :=
      Signal.mux start (Signal.pure 0#32 : Signal defaultDomain (BitVec 32)) (acc + act)
    bundle2 (Signal.register 0#32 nextCounter) (Signal.register 0#32 nextAcc)

/-- `ShippingMachineMemLinkedTest.mixedMems`: a combinational and a
synchronous read. -/
def mixedMems (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let r1 := Signal.memoryComboRead wa wd we addr
    let r2 := Signal.memory wa (Signal.snd st) we addr
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 (r1 ^^^ r2))
  Signal.snd st

/-! ### Refusals written here -/

/-- Refusal after reading (predicted): a hand-written loop alone that calls a
one-output `@[hardware_module]` (a loop with calls and no enclosing machine
is not read). -/
def loopCall (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let s := Signal.loop fun (s : Signal defaultDomain (BitVec 8)) =>
    Signal.register 0#8 (pick (Signal.pure 0#2 : Signal defaultDomain (BitVec 2)) (s + x))
  s

/-- Refusal before any reader call (predicted): a `Nat` signal is not a
hardware binder. -/
def natSig (x : Signal defaultDomain Nat) : Signal defaultDomain Nat := x

/-! ## The shadow harness -/

/-- The fields of `MachineShape` (and of its `Layout`) that differ, each by
its `BEq`. -/
def fieldDiffs (a b : MachineShape) : List String :=
  (if a.binders == b.binders then [] else ["binders"]) ++
  (if a.body == b.body then [] else ["body"]) ++
  (if a.layout.slots == b.layout.slots then [] else ["layout.slots"]) ++
  (if a.layout.outs == b.layout.outs then [] else ["layout.outs"]) ++
  (if a.layout.resetKind == b.layout.resetKind then [] else ["layout.resetKind"]) ++
  (if a.layout.lets == b.layout.lets then [] else ["layout.lets"]) ++
  (if a.runs == b.runs then [] else ["runs"]) ++
  (if a.insts == b.insts then [] else ["insts"]) ++
  (if a.loops == b.loops then [] else ["loops"]) ++
  (if a.instFields == b.instFields then [] else ["instFields"])

/-- `(fields text, equal)` of the real answer against the driver's. -/
def compareRes : Option MachineShape → Option (Option MachineShape) → String × Bool
  | none, some none => ("n/a", true)
  | some a, some (some b) =>
    match fieldDiffs a b with
    | [] => ("all-equal", true)
    | ds => ("differ:" ++ ",".intercalate ds, false)
  | _, _ => ("n/a", false)

def realClass : Option MachineShape → String
  | some _ => "OK"
  | none => "FAIL"

/-- How the driver reached its answer from start fuel 1. -/
def pathOf (dr : DriveResult) : String :=
  let c := resClass dr.res
  if c == "OUT" then "OUT(budget)"
  else if dr.doublings == 0 then c ++ "@1"
  else "OUT→" ++ c

/-- What one case's work returns. -/
structure Obs where
  real : Option MachineShape
  dr : DriveResult
  realMs : Nat
  driverMs : Nat

/-- Wall-clock guard per case. -/
def caseBudgetMs : Nat := 60000

/-- A key of an answer that the compiler cannot fold: branching on it forces
the answer (down to its body's hash) before the next clock read. -/
def shapeKey : Option MachineShape → UInt64
  | none => 7
  | some s => mixHash (hash s.body) (hash s.binders.length)

/-- The work: the real reader, then the driver, each timed; the answer is
forced (branched on its key) before the second clock read of each. -/
def work (sm : Bool) (ps : List (String × Nat)) (entry : ConstantInfo) (senv : StructEnv) :
    IO (Option Obs) := do
  let t0 ← IO.monoMsNow
  let real := machineShape? sm ps entry senv
  let t1 ← if shapeKey real == 0 then pure 0 else IO.monoMsNow
  let dr := driveShape defaultRounds 1 sm ps entry senv
  let dk : UInt64 := match dr.res with
    | none => 3
    | some r => shapeKey r
  let t2 ← if dk + dr.finalFuel.toUInt64 == 0 then pure 0 else IO.monoMsNow
  return some { real := real, dr := dr, realMs := t1 - t0, driverMs := t2 - t1 }

/-- The guard: returns `none` after `ms` (polling for cancellation). -/
def sleeper (ms : Nat) : IO (Option Obs) := do
  for _ in [0:ms / 50] do
    if ← IO.checkCanceled then return none
    IO.sleep 50
  return none

/-- The START line, in its own command (reported before the work starts). -/
def caseStart (label : String) : TermElabM Unit := do
  let err ← IO.getStderr
  err.putStrLn s!"SHADOW CASE START {label}"
  err.flush
  logInfo m!"SHADOW CASE START {label}"

/-- One shadow case: its line is logged BEFORE acting on the comparison; a
mismatch throws after the line; a TIMEOUT is a warning. -/
def shadowCase (label group : String) (n : Name) (sm : Bool := false)
    (ps : List (String × Nat) := []) : TermElabM Unit := do
  let env ← getEnv
  let senv := structEnv env
  let ci ← getConstInfo n
  let entry := entryConst true sm ps ci (instancePredicate env) (userInliner env) senv
  let tw ← IO.asTask (work sm ps entry senv) .dedicated
  let ts ← IO.asTask (sleeper caseBudgetMs) .dedicated
  let r ← IO.waitAny [tw, ts]
  match r with
  | .error e =>
    IO.cancel ts
    throwError m!"SHADOW {label} [{group}]: ERROR {toString e}"
  | .ok none =>
    IO.cancel tw
    let line := s!"SHADOW {label} [{group}]: TIMEOUT after {caseBudgetMs} ms (no class: the real reader or the driver did not return)"
    (← IO.getStderr).putStrLn line
    logWarning m!"{line}"
  | .ok (some o) =>
    IO.cancel ts
    let (fields, eq) := compareRes o.real o.dr.res
    let line := s!"SHADOW {label} [{group}]: real={realClass o.real} driver={resClass o.dr.res} path={pathOf o.dr} fields={fields} equal={eq} doublings={o.dr.doublings} fuel={o.dr.finalFuel} realMs={o.realMs} driverMs={o.driverMs}"
    (← IO.getStderr).putStrLn line
    logInfo m!"{line}"
    unless eq do
      throwError m!"SHADOW {label}: the driver's answer differs from the real reader's"

/-! ## The fixed list (40 cases)

`G.` = `Tests.Compiler.ReaderFuelGridTest` (imported), `MI.` =
`Sparkle.Tests.Compiler.MultiInstance` (imported), `I107.` =
`Sparkle.Tests.Compiler.Issue107LetBoundInstanceDup` (imported); unprefixed
= copied in this file.

| # | label | group | declaration |
|---|---|---|---|
| 1 | counterLoop | loop | G.counterLoop |
| 2 | accLoop | loop | G.accLoop |
| 3 | wholeLoop | loop | wholeLoop |
| 4 | loopPair | loop | loopPair |
| 5 | toggle107 | loop | I107.toggle |
| 6 | latch2 | nested | latch2 |
| 7 | pair | nested | pair |
| 8 | consumer | nested | consumer |
| 9 | chain3 | nested-shared | chain3 |
| 10 | siblings | nested-shared | siblings |
| 11 | caller | calls | G.caller |
| 12 | callerNested | calls | G.callerNested |
| 13 | callerInner | calls | G.callerInner |
| 14 | callerD | calls | callerD |
| 15 | callerLN | calls | callerLN |
| 16 | threeInstances | calls | I107.threeInstances |
| 17 | parent | instS | parent |
| 18 | chained | instS | chained |
| 19 | grand | instS-callers | grand |
| 20 | grandH | instS-callers | grandH |
| 21 | topD2 | instS-callers | topD2 |
| 22 | mixD1 | instS-callers | mixD1 |
| 23 | mixDeep | instS-callers | mixDeep |
| 24 | twinCalls | instS | MI.twinCalls |
| 25 | mesh2x2 | instS | MI.mesh2x2 |
| 26 | cnt | multi-output | cnt |
| 27 | mid2 | multi-output | mid2 |
| 28 | pe | multi-output | MI.pe |
| 29 | source | multi-output | source |
| 30 | memCounter | memory | G.memCounter |
| 31 | twoMems | memory | G.twoMems |
| 32 | mixedMems | memory | mixedMems |
| 33 | withMemory | memory | withMemory |
| 34 | twoLoops | refusal | G.twoLoops |
| 35 | opaqueInit | refusal | G.opaqueInit |
| 36 | loopCall | refusal | loopCall |
| 37 | notHw | refusal | G.notHw |
| 38 | natSig | refusal | natSig |
| 39 | gridInit | refusal | G.gridInit (an `opaque` constant) |
| 40 | latchSymbolic | refusal | G.latch in symbolic mode |

33 machine cases (rows 1–33) and 7 refusals (rows 34–40). -/

run_cmd liftTermElabM do
  logInfo m!"READER FUEL SHADOW START: 40 cases, start fuel 1, round bound {defaultRounds}, guard {caseBudgetMs} ms per case"

-- loops
run_cmd liftTermElabM <| caseStart "counterLoop"
run_cmd liftTermElabM <| shadowCase "counterLoop" "loop" ``Tests.Compiler.ReaderFuelGridTest.counterLoop
run_cmd liftTermElabM <| caseStart "accLoop"
run_cmd liftTermElabM <| shadowCase "accLoop" "loop" ``Tests.Compiler.ReaderFuelGridTest.accLoop
run_cmd liftTermElabM <| caseStart "wholeLoop"
run_cmd liftTermElabM <| shadowCase "wholeLoop" "loop" ``wholeLoop
run_cmd liftTermElabM <| caseStart "loopPair"
run_cmd liftTermElabM <| shadowCase "loopPair" "loop" ``loopPair
run_cmd liftTermElabM <| caseStart "toggle107"
run_cmd liftTermElabM <| shadowCase "toggle107" "loop" ``Sparkle.Tests.Compiler.Issue107LetBoundInstanceDup.toggle

-- nested / shared sub-machines
run_cmd liftTermElabM <| caseStart "latch2"
run_cmd liftTermElabM <| shadowCase "latch2" "nested" ``latch2
run_cmd liftTermElabM <| caseStart "pair"
run_cmd liftTermElabM <| shadowCase "pair" "nested" ``pair
run_cmd liftTermElabM <| caseStart "consumer"
run_cmd liftTermElabM <| shadowCase "consumer" "nested" ``consumer
run_cmd liftTermElabM <| caseStart "chain3"
run_cmd liftTermElabM <| shadowCase "chain3" "nested-shared" ``chain3
run_cmd liftTermElabM <| caseStart "siblings"
run_cmd liftTermElabM <| shadowCase "siblings" "nested-shared" ``siblings

-- calls, callers of callers
run_cmd liftTermElabM <| caseStart "caller"
run_cmd liftTermElabM <| shadowCase "caller" "calls" ``Tests.Compiler.ReaderFuelGridTest.caller
run_cmd liftTermElabM <| caseStart "callerNested"
run_cmd liftTermElabM <| shadowCase "callerNested" "calls" ``Tests.Compiler.ReaderFuelGridTest.callerNested
run_cmd liftTermElabM <| caseStart "callerInner"
run_cmd liftTermElabM <| shadowCase "callerInner" "calls" ``Tests.Compiler.ReaderFuelGridTest.callerInner
run_cmd liftTermElabM <| caseStart "callerD"
run_cmd liftTermElabM <| shadowCase "callerD" "calls" ``callerD
run_cmd liftTermElabM <| caseStart "callerLN"
run_cmd liftTermElabM <| shadowCase "callerLN" "calls" ``callerLN
run_cmd liftTermElabM <| caseStart "threeInstances"
run_cmd liftTermElabM <| shadowCase "threeInstances" "calls" ``Sparkle.Tests.Compiler.Issue107LetBoundInstanceDup.threeInstances

-- instS: structure-typed instance results
run_cmd liftTermElabM <| caseStart "parent"
run_cmd liftTermElabM <| shadowCase "parent" "instS" ``parent
run_cmd liftTermElabM <| caseStart "chained"
run_cmd liftTermElabM <| shadowCase "chained" "instS" ``chained
run_cmd liftTermElabM <| caseStart "grand"
run_cmd liftTermElabM <| shadowCase "grand" "instS-callers" ``grand
run_cmd liftTermElabM <| caseStart "grandH"
run_cmd liftTermElabM <| shadowCase "grandH" "instS-callers" ``grandH
run_cmd liftTermElabM <| caseStart "topD2"
run_cmd liftTermElabM <| shadowCase "topD2" "instS-callers" ``topD2
run_cmd liftTermElabM <| caseStart "mixD1"
run_cmd liftTermElabM <| shadowCase "mixD1" "instS-callers" ``mixD1
run_cmd liftTermElabM <| caseStart "mixDeep"
run_cmd liftTermElabM <| shadowCase "mixDeep" "instS-callers" ``mixDeep
run_cmd liftTermElabM <| caseStart "twinCalls"
run_cmd liftTermElabM <| shadowCase "twinCalls" "instS" ``Sparkle.Tests.Compiler.MultiInstance.twinCalls
run_cmd liftTermElabM <| caseStart "mesh2x2"
run_cmd liftTermElabM <| shadowCase "mesh2x2" "instS" ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2

-- multi-output machines (structure results)
run_cmd liftTermElabM <| caseStart "cnt"
run_cmd liftTermElabM <| shadowCase "cnt" "multi-output" ``cnt
run_cmd liftTermElabM <| caseStart "mid2"
run_cmd liftTermElabM <| shadowCase "mid2" "multi-output" ``mid2
run_cmd liftTermElabM <| caseStart "pe"
run_cmd liftTermElabM <| shadowCase "pe" "multi-output" ``Sparkle.Tests.Compiler.MultiInstance.pe
run_cmd liftTermElabM <| caseStart "source"
run_cmd liftTermElabM <| shadowCase "source" "multi-output" ``source

-- memory machines
run_cmd liftTermElabM <| caseStart "memCounter"
run_cmd liftTermElabM <| shadowCase "memCounter" "memory" ``Tests.Compiler.ReaderFuelGridTest.memCounter
run_cmd liftTermElabM <| caseStart "twoMems"
run_cmd liftTermElabM <| shadowCase "twoMems" "memory" ``Tests.Compiler.ReaderFuelGridTest.twoMems
run_cmd liftTermElabM <| caseStart "mixedMems"
run_cmd liftTermElabM <| shadowCase "mixedMems" "memory" ``mixedMems
run_cmd liftTermElabM <| caseStart "withMemory"
run_cmd liftTermElabM <| shadowCase "withMemory" "memory" ``withMemory

-- ordinary refusals
run_cmd liftTermElabM <| caseStart "twoLoops"
run_cmd liftTermElabM <| shadowCase "twoLoops" "refusal" ``Tests.Compiler.ReaderFuelGridTest.twoLoops
run_cmd liftTermElabM <| caseStart "opaqueInit"
run_cmd liftTermElabM <| shadowCase "opaqueInit" "refusal" ``Tests.Compiler.ReaderFuelGridTest.opaqueInit
run_cmd liftTermElabM <| caseStart "loopCall"
run_cmd liftTermElabM <| shadowCase "loopCall" "refusal" ``loopCall
run_cmd liftTermElabM <| caseStart "notHw"
run_cmd liftTermElabM <| shadowCase "notHw" "refusal" ``Tests.Compiler.ReaderFuelGridTest.notHw
run_cmd liftTermElabM <| caseStart "natSig"
run_cmd liftTermElabM <| shadowCase "natSig" "refusal" ``natSig
run_cmd liftTermElabM <| caseStart "gridInit"
run_cmd liftTermElabM <| shadowCase "gridInit" "refusal" ``Tests.Compiler.ReaderFuelGridTest.gridInit
run_cmd liftTermElabM <| caseStart "latchSymbolic"
run_cmd liftTermElabM <| shadowCase "latchSymbolic" "refusal" ``Tests.Compiler.ReaderFuelGridTest.latch true

run_cmd liftTermElabM do
  logInfo m!"READER FUEL SHADOW DONE: 40 cases (a mismatch is an error of its own case; a TIMEOUT a warning of its own case)"

end Tests.Compiler.ReaderFuelShadowTest
