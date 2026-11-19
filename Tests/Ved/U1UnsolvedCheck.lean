import Tools.VedU1Entry
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# `#ved_u1`: the loop script for one-register `circuit do`, bare loops, and the closers

Issue sparkle-ved-unsolved (rows R6, R19, R79, R82, R87, R89, R91, R99, R100, R116, R217-R219,
R229 of the real-IP inventory).  The generated script's obstacles, found by printing the
unsolved goals of those rows, were:

* a `circuit do` module with ONE register is a `Signal.loop` (not a `Signal.register`): it is
  routed to the loop script (`usesLoop`);
* a loop whose state is a bare `Signal (BitVec w)` (no tuple): one component;
* closers: `x * 2` against `2 * x` in the range facts, the `Bool` test `(a == b) = (c != 0)` of a
  CRC's top bit, `Int.bmod` and `Nat` subtraction of the signed arithmetic, `|||` of a sign
  extension against `+` (the concatenation), `^^^ 1` of a one-bit field;
* the registers of two loops of one width numbered in another order than the components: matched
  by input support.

What is fixed here (`#guard_msgs`):
1. Positives (local declarations shaped like those rows): each is accepted, the registered
   theorem's type is rebuilt by hand and compared with `==` against `U1Stmt c m f`, and its axioms
   are exactly the three standard ones.
2. Controls (`expectRefused`, the stage is checked and nothing the checker registered is left):
   the module with another register initial value, another declaration's module, another
   declaration's theorem as the proof.
-/

namespace Tests.Ved.U1UnsolvedCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core
open Tools.VedU1Contract Tools.VedU1Entry

/-- CRC-like shift register with a Bool input compared against the top bit (R79/R82/R83 shape). -/
def crcLike (start bitIn valid : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 15) :=
  circuit do
    let r ← Signal.reg (0#15)
    let rSig := (r : Signal defaultDomain (BitVec 15))
    let topAnd := (rSig &&& (Signal.pure 0x4000#15 : Signal defaultDomain (BitVec 15)) : Signal defaultDomain (BitVec 15))
    let topBit := (~~~(topAnd === (Signal.pure 0#15 : Signal defaultDomain (BitVec 15)) : Signal defaultDomain Bool) : Signal defaultDomain Bool)
    let xorBit := ((· ^^ ·) <$> topBit <*> bitIn : Signal defaultDomain Bool)
    let shifted := (rSig <<< (Signal.pure 1#15 : Signal defaultDomain (BitVec 15)) : Signal defaultDomain (BitVec 15))
    let shiftedXor := (shifted ^^^ (Signal.pure 0x4599#15 : Signal defaultDomain (BitVec 15)) : Signal defaultDomain (BitVec 15))
    r <~ Signal.mux start (Signal.pure 0#15) (Signal.mux valid (Signal.mux xorBit shiftedXor shifted) rSig)
    return rSig

/-- Same shape, another polynomial (a different meaning). -/
def crcLike2 (start bitIn valid : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 15) :=
  circuit do
    let r ← Signal.reg (0#15)
    let rSig := (r : Signal defaultDomain (BitVec 15))
    let topAnd := (rSig &&& (Signal.pure 0x4000#15 : Signal defaultDomain (BitVec 15)) : Signal defaultDomain (BitVec 15))
    let topBit := (~~~(topAnd === (Signal.pure 0#15 : Signal defaultDomain (BitVec 15)) : Signal defaultDomain Bool) : Signal defaultDomain Bool)
    let xorBit := ((· ^^ ·) <$> topBit <*> bitIn : Signal defaultDomain Bool)
    let shifted := (rSig <<< (Signal.pure 1#15 : Signal defaultDomain (BitVec 15)) : Signal defaultDomain (BitVec 15))
    let shiftedXor := (shifted ^^^ (Signal.pure 0x4598#15 : Signal defaultDomain (BitVec 15)) : Signal defaultDomain (BitVec 15))
    r <~ Signal.mux start (Signal.pure 0#15) (Signal.mux valid (Signal.mux xorBit shiftedXor shifted) rSig)
    return rSig

/-- A bare `Signal.loop` (the state is the signal itself, no tuple; R6 shape). -/
def bareLoop (reqA reqB : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 2) :=
  Signal.loop fun state =>
    let isIdle := state === (Signal.pure 0#2)
    let goA := reqA &&& (isIdle ||| (state === (Signal.pure 2#2)))
    Signal.register 0#2 (Signal.mux goA (Signal.pure 1#2) (Signal.mux reqB (Signal.pure 2#2) (Signal.pure 0#2)))

/-- Same type, another transition (a different meaning). -/
def bareLoop2 (reqA reqB : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 2) :=
  Signal.loop fun state =>
    let isIdle := state === (Signal.pure 0#2)
    let goA := reqA &&& (isIdle ||| (state === (Signal.pure 2#2)))
    Signal.register 0#2 (Signal.mux goA (Signal.pure 2#2) (Signal.mux reqB (Signal.pure 1#2) (Signal.pure 0#2)))

/-- A sign extension concatenated with a slice (`|||` of the extension and the slice; R19 shape). -/
def signExt (inst : Signal defaultDomain (BitVec 32)) : Signal defaultDomain (BitVec 32) :=
  let s31 := inst.map (BitVec.extractLsb' 31 1 ·)
  let hi := Signal.mux (s31 === 1#1) (Signal.pure 0xFFFFF#20) (Signal.pure 0#20)
  let lo := inst.map (BitVec.extractLsb' 20 12 ·)
  hi ++ lo

/-- Two counters of ONE width in two loops, driven by different inputs (R229 shape: the
registers' numbering need not follow the loops' components). -/
def twoCounters (a b : Signal defaultDomain Bool) : Signal defaultDomain Bool :=
  circuit do
    let x ← Signal.reg (0#4)
    let y ← Signal.reg (0#4)
    let xS := (x : Signal defaultDomain (BitVec 4))
    let yS := (y : Signal defaultDomain (BitVec 4))
    x <~ Signal.mux a (xS + 1#4) xS
    y <~ Signal.mux b (yS + 1#4) yS
    return (xS === (Signal.pure 3#4 : Signal defaultDomain (BitVec 4))) &&& (yS === (Signal.pure 3#4 : Signal defaultDomain (BitVec 4)))

/-! ## 1. Positives -/

#guard_msgs (drop info) in
#ved_u1 crcLike
#guard_msgs (drop info) in
#ved_u1 crcLike2
#guard_msgs (drop info) in
#ved_u1 bareLoop
#guard_msgs (drop info) in
#ved_u1 bareLoop2
#guard_msgs (drop info) in
#ved_u1 signExt
#guard_msgs (drop info) in
#ved_u1 twoCounters

/-- The registered theorem's type is `U1Stmt` of the registered contract and module over the
ORIGINAL constant (rebuilt by hand, compared with `==`), and its axioms are the three standard
ones. -/
def checkStmt (n : Name) : MetaM Unit := do
  let ci ← getConstInfo (n ++ `ved_u1)
  let expected := mkAppN (mkConst ``U1Stmt) #[mkConst (n ++ `ved_contract), mkConst (n ++ `ved_mod), mkConst n]
  unless ci.type == expected do throwError "{n}: the statement differs from U1Stmt of the original constant"
  let ax ← collectAxioms (n ++ `ved_u1)
  let std := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all std.contains && ax.size == 3 do throwError "{n}: axioms {ax}"
  logInfo m!"{n}: exact statement, standard axioms"

/-- info: Tests.Ved.U1UnsolvedCheck.crcLike: exact statement, standard axioms -/
#guard_msgs in
run_meta checkStmt ``crcLike
/-- info: Tests.Ved.U1UnsolvedCheck.bareLoop: exact statement, standard axioms -/
#guard_msgs in
run_meta checkStmt ``bareLoop
/-- info: Tests.Ved.U1UnsolvedCheck.signExt: exact statement, standard axioms -/
#guard_msgs in
run_meta checkStmt ``signExt
/-- info: Tests.Ved.U1UnsolvedCheck.twoCounters: exact statement, standard axioms -/
#guard_msgs in
run_meta checkStmt ``twoCounters

/-! ## 2. Controls: must stay refused -/

/-- The module a previous entry run registered (its closed term evaluated). -/
def modOf (base : Name) : TermElabM Sparkle.IR.AST.Module := do
  let some v := (← getConstInfo (base ++ `ved_mod)).value? | throwError "no value"
  evalModule v

def checkerNames (base : Name) : List Name :=
  [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_u1].map (base ++ ·)

def assertClean (absent : List Name) : TermElabM Unit := do
  let env ← getEnv
  for n in absent do
    if env.contains n then throwError "left behind: {n}"

def expectRefused (stage : String) (absent : List Name) (act : TermElabM Unit) :
    CommandElabM Unit := liftTermElabM do
  let accepted ← try act; pure true catch e =>
    let s ← e.toMessageData.toString
    unless s.startsWith "VED U1 REFUSED" && (s.splitOn s!"[{stage}]").length > 1 do throw e
    pure false
  if accepted then throwError "control ACCEPTED (expected a refusal at [{stage}])"
  assertClean absent
  logInfo m!"refused [{stage}], clean"

/-- Every register's initial value changed. -/
def mutInit (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .register o c r i v => .register o c r i (v + 1)
      | s => s }

-- The one-register loop script, the module's register started elsewhere.
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlCrcInit) do
  discard <| checkU1 ``crcLike `ctlCrcInit ``crcLike (mutInit (← modOf ``crcLike)) .generated

-- the bare loop, the module's register started elsewhere
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlBareInit) do
  discard <| checkU1 ``bareLoop `ctlBareInit ``bareLoop (mutInit (← modOf ``bareLoop)) .generated

-- the two counters, the module's registers started elsewhere
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlTwoInit) do
  discard <| checkU1 ``twoCounters `ctlTwoInit ``twoCounters (mutInit (← modOf ``twoCounters)) .generated

-- the other polynomial's module for `crcLike`
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlCrcOther) do
  discard <| checkU1 ``crcLike `ctlCrcOther ``crcLike (← modOf ``crcLike2) .generated

-- the other transition table's module for `bareLoop`
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlBareOther) do
  discard <| checkU1 ``bareLoop `ctlBareOther ``bareLoop (← modOf ``bareLoop2) .generated

-- another declaration's theorem as the proof of `crcLike`'s statement
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlCrcProof) do
  discard <| checkU1 ``crcLike `ctlCrcProof ``crcLike (← modOf ``crcLike) (.term (mkCIdent ``crcLike2.ved_u1))

end Tests.Ved.U1UnsolvedCheck
