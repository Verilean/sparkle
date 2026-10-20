import Sparkle
import Sparkle.Core.CircuitDo
import Sparkle.Core.StateMacro
import Sparkle.Compiler.InlineAttr
import Tools.ShippingReaderFuelDriver

/-! # GRID: the fuel wrapper + doubling driver against the real reader

TARGET-ONLY (`lake build Tests.Compiler.ReaderFuelGridTest`); not in
`Tests.AllTests`. WRITTEN, NOT BUILT (worker F, branch `par/r-9`). No
synthesis is run; nothing in the compiler changes; production still calls
the `partial` `machineShape?`.

For each case — the entry constant exactly as the real elaborator builds it
(`entryConst true sm ps ci …`) — the line

    GRID <label>: real=<OK|FAIL> driver=<OK|FAIL|OUT> at0=<…> at1=<…> equal=<true|false> fuel=<n> doublings=<k>

is logged BEFORE the comparison (one `run_cmd` per case, each preceded by
`GRID CASE START <label>`): `real` = `machineShape?`, `driver` =
`driveShape defaultRounds 1` (start fuel 1, doubling on OUT only),
`at0`/`at1` = `machineShapeF` at fuel 0 / 1, `equal` = same class and, for
OK, the same shape (binders, body `==`, layout fields, runs, insts, loops,
instFields), `fuel` = the driver's final fuel, `doublings` = how many times it
doubled. A case throws AFTER its line iff `equal=false`.

Declarations are COPIES of existing test declarations (so this target does
not import and re-run those tests' endpoints):
`ShippingMachineNestTest` (latch, stage, loopBack, front),
`ShippingMachineInstTest` (pick, caller, callerTwice, counter2, callerNested,
innerPick, callerInner), `ShippingMachineLoopTest` (CntState, counterLoop,
accLoop), `ShippingMachineMemLinkedTest` (memCounter, twoMems); plus four
refusal cases written here (twoLoops, opaqueInit, notHw) and three calls with
a refused mode (parameters, symbolic, not a definition).

## PREDICTED (by reading; NOT observed)

* the 12 machine cases: `real=OK driver=OK at0=OUT at1=OUT equal=true`,
  `fuel = 2^k`, `doublings = k ≥ 1` (k = the needed recursion depth, rounded
  up to a power of two; expected 5–8 for these small bodies);
* `twoLoops`, `opaqueInit`: `real=FAIL driver=FAIL at0=OUT at1=OUT equal=true`,
  `doublings ≥ 1` (the refusal is found only after reading: two loops alone /
  a non-literal reset) — the OUT → FAIL-after-doubling cases;
* `notHw`, `latchParams`, `latchSymbolic`, `natInductive`:
  `real=FAIL driver=FAIL at0=FAIL at1=FAIL equal=true fuel=1 doublings=0`
  (an ordinary FAIL before any reader call: finite at every fuel,
  `machineShapeF_of_pre_none`). -/
namespace Tests.Compiler.ReaderFuelGridTest
open Lean Elab Command Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Tools.ShippingReaderFuel (machineShapeF driveShape defaultRounds resClass)

/-! ## Declarations (copies) -/

section
variable {dom : DomainConfig}

/-- `ShippingMachineNestTest.latch`. -/
def latch (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    r <~ x
    return r

/-- `ShippingMachineNestTest.stage`. -/
def stage (x : Signal dom (BitVec 8)) (en : Signal dom Bool) : Signal dom (BitVec 8) :=
  circuit do
    let s ← Signal.reg 0#8
    let sS := (s : Signal dom (BitVec 8))
    s <~ Signal.mux en (sS + x) sS
    return sS

/-- `ShippingMachineNestTest.loopBack`. -/
def loopBack (r : Signal dom (BitVec 8)) (en : Signal dom Bool) : Signal dom (BitVec 8) :=
  circuit do
    let xReg ← Signal.reg 1#8
    let x := (xReg : Signal dom (BitVec 8))
    let u := stage (r - x) en
    xReg <~ x + u
    return x

/-- `ShippingMachineNestTest.front`. -/
def front (x : Signal dom (BitVec 8)) (en : Signal dom Bool) : Signal dom (BitVec 8) :=
  let l := latch x
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal dom (BitVec 8))
    acc <~ Signal.mux en (accS + l) accS
    return accS
end

/-- `ShippingMachineInstTest.pick`. -/
@[hardware_module]
def pick (sel : Signal defaultDomain (BitVec 2)) (x : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  Signal.mux (sel === (Signal.pure 0#2 : Signal defaultDomain (BitVec 2))) x
    (Signal.mux (sel === (Signal.pure 1#2 : Signal defaultDomain (BitVec 2)))
      (x + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8)))
      (x ^^^ (Signal.pure 0xFF#8 : Signal defaultDomain (BitVec 8))))

/-- `ShippingMachineInstTest.caller`. -/
def caller (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let sel ← Signal.reg 0#2
    let acc ← Signal.reg 0#8
    let selS := (sel : Signal defaultDomain (BitVec 2))
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let y := pick selS (accS + x)
    sel <~ selS + (Signal.pure 1#2 : Signal defaultDomain (BitVec 2))
    acc <~ y
    return y

/-- `ShippingMachineInstTest.callerTwice`. -/
def callerTwice (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let sel ← Signal.reg 0#2
    let selS := (sel : Signal defaultDomain (BitVec 2))
    let y := pick selS x
    sel <~ Signal.mux (y === (Signal.pure 7#8 : Signal defaultDomain (BitVec 8))) selS
      (selS + (Signal.pure 1#2 : Signal defaultDomain (BitVec 2)))
    return y

/-- `ShippingMachineInstTest.counter2`. -/
def counter2 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 2) :=
  circuit do
    let c ← Signal.reg 0#2
    let cS := (c : Signal defaultDomain (BitVec 2))
    c <~ Signal.mux en (cS + (Signal.pure 1#2 : Signal defaultDomain (BitVec 2))) cS
    return cS

/-- `ShippingMachineInstTest.callerNested`. -/
def callerNested (x : Signal defaultDomain (BitVec 8)) (en : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let s := counter2 en
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    acc <~ pick s (accS + x)
    return accS

/-- `ShippingMachineInstTest.innerPick`. -/
def innerPick (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let c ← Signal.reg 0#8
    let cS := (c : Signal defaultDomain (BitVec 8))
    c <~ Signal.mux en (pick (Signal.pure 1#2 : Signal defaultDomain (BitVec 2)) cS) cS
    return cS

/-- `ShippingMachineInstTest.callerInner`. -/
def callerInner (x : Signal defaultDomain (BitVec 8)) (en : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  let s := innerPick en
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    acc <~ pick (Signal.pure 2#2 : Signal defaultDomain (BitVec 2)) (accS + s + x)
    return accS

declare_signal_state CntState
  | cnt  : BitVec 8 := 0#8
  | flag : Bool     := false

/-- `ShippingMachineLoopTest.counterLoop`. -/
def counterLoop (en : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8 × Bool) :=
  let s := Signal.loop fun state =>
    let c := CntState.cnt state
    let f := CntState.flag state
    let next := Signal.mux en (c + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))) c
    let wrap := c === (Signal.pure 255#8 : Signal defaultDomain (BitVec 8))
    bundleAll! [Signal.register 0#8 next, Signal.register false (Signal.mux en wrap f)]
  bundle2 (CntState.cnt s) (CntState.flag s)

/-- `ShippingMachineLoopTest.accLoop`. -/
def accLoop (x : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  let s := Signal.loop fun (acc : Signal defaultDomain (BitVec 16)) =>
    Signal.register 0#16 (acc + x)
  s

/-- `ShippingMachineMemLinkedTest.memCounter`. -/
def memCounter (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let rd := Signal.memoryComboRead wa wd we addr
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 rd)
  Signal.snd st

/-- `ShippingMachineMemLinkedTest.twoMems`. -/
def twoMems (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let r1 := Signal.memoryComboRead wa wd we addr
    let r2 := Signal.memoryComboRead addr wd we (Signal.pure 0#4)
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 (r1 + r2))
  Signal.snd st

/-- Refusal after reading (predicted): two hand-written loops alone. -/
def twoLoops (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let a := Signal.loop fun (s : Signal defaultDomain (BitVec 8)) =>
    Signal.register 0#8 (s + x)
  let b := Signal.loop fun (s : Signal defaultDomain (BitVec 8)) =>
    Signal.register 0#8 (s + a)
  b

/-- A reset value the reader cannot evaluate. -/
opaque gridInit : BitVec 8

/-- Refusal after reading (predicted): a non-literal reset value. -/
def opaqueInit (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let s := Signal.loop fun (acc : Signal defaultDomain (BitVec 8)) =>
    Signal.register gridInit (acc + x)
  s

/-- Refusal before any reader call: not a hardware binder. -/
def notHw (n : Nat) : Nat := n + 1

/-! ## The grid -/

/-- Same shape (the comparable data of `MachineShape`). -/
def shapeSame (a b : MachineShape) : Bool :=
  a.binders == b.binders && a.body == b.body &&
  a.layout.slots == b.layout.slots && a.layout.outs == b.layout.outs &&
  a.layout.resetKind == b.layout.resetKind && a.layout.lets == b.layout.lets &&
  a.runs == b.runs && a.insts == b.insts && a.loops == b.loops &&
  a.instFields == b.instFields

/-- The real answer against the driver's: same class, same shape on OK. -/
def sameRes : Option MachineShape → Option (Option MachineShape) → Bool
  | none, some none => true
  | some a, some (some b) => shapeSame a b
  | _, _ => false

def realClass : Option MachineShape → String
  | some _ => "OK"
  | none => "FAIL"

/-- One grid line: logged BEFORE the comparison; throws after it on a
mismatch. -/
def gridCase (label : String) (n : Name) (sm : Bool := false)
    (ps : List (String × Nat) := []) : TermElabM Unit := do
  logInfo m!"GRID CASE START {label}"
  let env ← getEnv
  let senv := structEnv env
  let ci ← getConstInfo n
  let entry := entryConst true sm ps ci (instancePredicate env) (userInliner env) senv
  let real := machineShape? sm ps entry senv
  let at0 := machineShapeF 0 sm ps entry senv
  let at1 := machineShapeF 1 sm ps entry senv
  let dr := driveShape defaultRounds 1 sm ps entry senv
  let eq := sameRes real dr.res
  logInfo m!"GRID {label}: real={realClass real} driver={resClass dr.res} at0={resClass at0} at1={resClass at1} equal={eq} fuel={dr.finalFuel} doublings={dr.doublings}"
  unless eq do
    throwError m!"GRID {label}: the driver's answer differs from the real reader's"

run_cmd liftTermElabM do
  logInfo m!"READER FUEL GRID START: 18 cases, start fuel 1, round bound {defaultRounds}"

-- machine cases (register / nested / instance / loop / memory)
run_cmd liftTermElabM <| gridCase "latch" ``latch
run_cmd liftTermElabM <| gridCase "stage" ``stage
run_cmd liftTermElabM <| gridCase "loopBack" ``loopBack
run_cmd liftTermElabM <| gridCase "front" ``front
run_cmd liftTermElabM <| gridCase "caller" ``caller
run_cmd liftTermElabM <| gridCase "callerTwice" ``callerTwice
run_cmd liftTermElabM <| gridCase "callerNested" ``callerNested
run_cmd liftTermElabM <| gridCase "callerInner" ``callerInner
run_cmd liftTermElabM <| gridCase "counterLoop" ``counterLoop
run_cmd liftTermElabM <| gridCase "accLoop" ``accLoop
run_cmd liftTermElabM <| gridCase "memCounter" ``memCounter
run_cmd liftTermElabM <| gridCase "twoMems" ``twoMems

-- refusals found after reading (OUT at small fuel, FAIL after doubling)
run_cmd liftTermElabM <| gridCase "twoLoops" ``twoLoops
run_cmd liftTermElabM <| gridCase "opaqueInit" ``opaqueInit

-- ordinary refusals before any reader call (FAIL at every fuel)
run_cmd liftTermElabM <| gridCase "notHw" ``notHw
run_cmd liftTermElabM <| gridCase "latchParams" ``latch false [("W", 8)]
run_cmd liftTermElabM <| gridCase "latchSymbolic" ``latch true
run_cmd liftTermElabM <| gridCase "natInductive" ``Nat

run_cmd liftTermElabM do
  logInfo m!"READER FUEL GRID DONE: 18 cases (a mismatch is an error of its own case)"

end Tests.Compiler.ReaderFuelGridTest
