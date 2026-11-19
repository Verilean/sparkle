import Tools.VedU1Entry
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# `#ved_u1` on chained bit-serial CRC bodies (sharing-preserving loop script)

Issue sparkle-ved-u1-wire-share (rows R83 `synth_crsfCrc8`, R84 `synth_droneCanCrc16`, R212 `crc32EngineTop`
of the real-IP inventory).  A CRC byte step chains bit steps whose step uses its argument three times
(`c &&& msb`, `c <<< 1` twice), so the unfolded body is a DAG whose tree is exponential in the number of
steps.  The loop script (`Tools/VedU1Entry.lean`) reads it by walks over the shared subterms
(`Tools/VedU1WireShare.lean`: unfolding the loop at the next cycle, generalising the state), and `ved_wire`
(`Tools/VedU1Wire.lean`) makes the atoms and every operation a variable (`^^^` / `&&&` / `|||` included), proves
the wires of equal sample values equal one at a time in a small context (the equalities already proved are
substituted; `^^^ 1`, `&&& 1`, `||| 1` are rewritten to `/ 2` and `% 2`), and closes the goal from them.

What is fixed here (`#guard_msgs`):
1. Positives (local declarations shaped like those rows, 3 bit steps at 8 bits, 2 at 16): each is accepted, the
   registered theorem's type is rebuilt by hand and compared with `==` against `U1Stmt c m f`, and its axioms are
   exactly the three standard ones.
2. Controls (`expectRefused`, the stage is checked and nothing the checker registered is left): the module with
   another register initial value, the module of the chain with the arms of a step swapped, the module of the chain
   with another polynomial.
-/

namespace Tests.Ved.U1WireShareCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core
open Tools.VedU1Contract Tools.VedU1Entry

/-- one bit step of an 8-bit CRC (polynomial 0x07) -/
def step8 (c : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let msbAnd := (c &&& (Signal.pure 0x80#8 : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8))
  let msbNZ := (~~~(msbAnd === (Signal.pure 0#8 : Signal defaultDomain (BitVec 8)) : Signal defaultDomain Bool) : Signal defaultDomain Bool)
  let shifted := (c <<< (Signal.pure 1#8 : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8))
  let shiftedXor := (shifted ^^^ (Signal.pure 0x07#8 : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8))
  Signal.mux msbNZ shiftedXor shifted

/-- the same step with the arms of the `mux` swapped (a different meaning) -/
def step8Swap (c : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let msbAnd := (c &&& (Signal.pure 0x80#8 : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8))
  let msbNZ := (~~~(msbAnd === (Signal.pure 0#8 : Signal defaultDomain (BitVec 8)) : Signal defaultDomain Bool) : Signal defaultDomain Bool)
  let shifted := (c <<< (Signal.pure 1#8 : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8))
  let shiftedXor := (shifted ^^^ (Signal.pure 0x07#8 : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8))
  Signal.mux msbNZ shifted shiftedXor

/-- the same step with another polynomial (a different meaning) -/
def step8Poly (c : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let msbAnd := (c &&& (Signal.pure 0x80#8 : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8))
  let msbNZ := (~~~(msbAnd === (Signal.pure 0#8 : Signal defaultDomain (BitVec 8)) : Signal defaultDomain Bool) : Signal defaultDomain Bool)
  let shifted := (c <<< (Signal.pure 1#8 : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8))
  let shiftedXor := (shifted ^^^ (Signal.pure 0x09#8 : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8))
  Signal.mux msbNZ shiftedXor shifted

/-- a byte-serial CRC-8: the register takes the byte, three bit steps (the shape of `crc8HW`, R83) -/
def crc8Chain (start : Signal defaultDomain Bool) (byteIn : Signal defaultDomain (BitVec 8))
    (valid : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (0#8)
    let rSig := (r : Signal defaultDomain (BitVec 8))
    let c0 := (rSig ^^^ byteIn : Signal defaultDomain (BitVec 8))
    let c1 := step8 c0
    let c2 := step8 c1
    let c3 := step8 c2
    r <~ Signal.mux start (Signal.pure 0#8) (Signal.mux valid c3 rSig)
    return rSig

/-- the chain whose steps have the arms swapped -/
def crc8ChainSwap (start : Signal defaultDomain Bool) (byteIn : Signal defaultDomain (BitVec 8))
    (valid : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (0#8)
    let rSig := (r : Signal defaultDomain (BitVec 8))
    let c0 := (rSig ^^^ byteIn : Signal defaultDomain (BitVec 8))
    let c1 := step8Swap c0
    let c2 := step8Swap c1
    let c3 := step8Swap c2
    r <~ Signal.mux start (Signal.pure 0#8) (Signal.mux valid c3 rSig)
    return rSig

/-- the chain with another polynomial -/
def crc8ChainPoly (start : Signal defaultDomain Bool) (byteIn : Signal defaultDomain (BitVec 8))
    (valid : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (0#8)
    let rSig := (r : Signal defaultDomain (BitVec 8))
    let c0 := (rSig ^^^ byteIn : Signal defaultDomain (BitVec 8))
    let c1 := step8Poly c0
    let c2 := step8Poly c1
    let c3 := step8Poly c2
    r <~ Signal.mux start (Signal.pure 0#8) (Signal.mux valid c3 rSig)
    return rSig

/-- one bit step of a 16-bit CRC (CCITT, polynomial 0x1021) -/
def step16 (c : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  let msbAnd := (c &&& (Signal.pure 0x8000#16 : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16))
  let msbNZ := (~~~(msbAnd === (Signal.pure 0#16 : Signal defaultDomain (BitVec 16)) : Signal defaultDomain Bool) : Signal defaultDomain Bool)
  let shifted := (c <<< (Signal.pure 1#16 : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16))
  let shiftedXor := (shifted ^^^ (Signal.pure 0x1021#16 : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16))
  Signal.mux msbNZ shiftedXor shifted

/-- a CRC-16 with two bit steps and a widened input byte (the shape of `crc16CcittHW`, R84) -/
def crc16Chain (start : Signal defaultDomain Bool) (byteIn : Signal defaultDomain (BitVec 8))
    (valid : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 16) :=
  circuit do
    let r ← Signal.reg (0xFFFF#16)
    let rSig := (r : Signal defaultDomain (BitVec 16))
    let widened := ((Signal.pure 0#8 : Signal defaultDomain (BitVec 8)) ++ byteIn : Signal defaultDomain (BitVec 16))
    let shBy8 := (widened <<< (Signal.pure 8#16 : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16))
    let c0 := (rSig ^^^ shBy8 : Signal defaultDomain (BitVec 16))
    let c1 := step16 c0
    let c2 := step16 c1
    r <~ Signal.mux start (Signal.pure 0xFFFF#16) (Signal.mux valid c2 rSig)
    return rSig

/-! ## 1. Positives -/

#guard_msgs (drop info) in
#ved_u1 crc8Chain
#guard_msgs (drop info) in
#ved_u1 crc8ChainSwap
#guard_msgs (drop info) in
#ved_u1 crc8ChainPoly
#guard_msgs (drop info) in
#ved_u1 crc16Chain

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

/-- info: Tests.Ved.U1WireShareCheck.crc8Chain: exact statement, standard axioms -/
#guard_msgs in
run_meta checkStmt ``crc8Chain
/-- info: Tests.Ved.U1WireShareCheck.crc8ChainSwap: exact statement, standard axioms -/
#guard_msgs in
run_meta checkStmt ``crc8ChainSwap
/-- info: Tests.Ved.U1WireShareCheck.crc8ChainPoly: exact statement, standard axioms -/
#guard_msgs in
run_meta checkStmt ``crc8ChainPoly
/-- info: Tests.Ved.U1WireShareCheck.crc16Chain: exact statement, standard axioms -/
#guard_msgs in
run_meta checkStmt ``crc16Chain

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

-- the 8-bit chain, the module's register started elsewhere
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlChainInit) do
  discard <| checkU1 ``crc8Chain `ctlChainInit ``crc8Chain (mutInit (← modOf ``crc8Chain)) .generated

-- the 16-bit chain, the module's register started elsewhere
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlChain16Init) do
  discard <| checkU1 ``crc16Chain `ctlChain16Init ``crc16Chain (mutInit (← modOf ``crc16Chain)) .generated

-- the module of the chain with the arms of a step swapped, for the original chain
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlChainSwap) do
  discard <| checkU1 ``crc8Chain `ctlChainSwap ``crc8Chain (← modOf ``crc8ChainSwap) .generated

-- the module of the chain with another polynomial, for the original chain
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlChainPoly) do
  discard <| checkU1 ``crc8Chain `ctlChainPoly ``crc8Chain (← modOf ``crc8ChainPoly) .generated

end Tests.Ved.U1WireShareCheck
