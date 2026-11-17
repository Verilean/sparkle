import Sparkle
import Tools.VedU1Entry
import Tools.VedStrictAudit

/-!
# Check for `ved_bit_simp_pk` (`Tools/VedU1MerkleWhnf.lean`, unit sparkle-ved-merkle-whnf)

`merkleMini` is a shrunk copy of the R165 shape (`IP/Crypto/MerkleHW.lean`, `merkleRootHW`; one slot, a 2-bit occupancy
mask, carry, level, busy flag = 5 registers in one `Signal.loop`; `&&&` / `|||` masks on the packed state).  At stage 3 of the
loop script (`Tools/VedU1Entry.lean`) the bit step used to run on the still-packed registers and every refused `omega` side
condition charged the proof budget (`ved.u1.proofHeartbeats`).

* ACCEPTED (same entry, default stage 3 `ved_bit_simp_pk`): `#ved_u1 merkleMini` under the lowered proof budget
  `ved.u1.proofHeartbeats 2000000` (2e9 heartbeats; the default is 8e9).  The stored type is `==` the entry statement
  (`U1Stmt contract mod decl`), the axioms are the standard three.
* BEFORE (measured in scratch with stage 3 switched back to `ved_bit_simp_share`, never committed): the same declaration under
  the same budget is refused at `[proof]` (whnf heartbeat 2000000, 148 s); with `ved_bit_simp_pk` it is accepted (140 s).
* CONTROL: the module with its output altered (`out + 1`) against the declaration, default budget: refused at `[proof]`,
  nothing left behind.
-/

namespace Tests.Ved.U1MerkleWhnfCheck

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core
open Tools.VedU1Contract Tools.VedU1Entry

def merkleMini (start push : Signal defaultDomain Bool)
    (leafIn combineOut : Signal defaultDomain (BitVec 8))
    (combineDone : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let s0R ← Signal.reg (0#8)
    let occR ← Signal.reg (0#2)
    let carryR ← Signal.reg (0#8)
    let lvlR ← Signal.reg (0#2)
    let busyR ← Signal.reg false
    let s0Sig := (s0R : Signal defaultDomain (BitVec 8))
    let occSig := (occR : Signal defaultDomain (BitVec 2))
    let carrySig := (carryR : Signal defaultDomain (BitVec 8))
    let lvlSig := (lvlR : Signal defaultDomain (BitVec 2))
    let busySig := (busyR : Signal defaultDomain Bool)
    let p0_2 := (Signal.pure 0#2 : Signal defaultDomain (BitVec 2))
    let p1_2 := (Signal.pure 1#2 : Signal defaultDomain (BitVec 2))
    let pOccBit0 := (Signal.pure 1#2 : Signal defaultDomain (BitVec 2))
    let pOccBit1 := (Signal.pure 2#2 : Signal defaultDomain (BitVec 2))
    let p0_8 := (Signal.pure 0#8 : Signal defaultDomain (BitVec 8))
    let isL0 := (lvlSig === p0_2 : Signal defaultDomain Bool)
    let occMask := Signal.mux isL0 pOccBit0 pOccBit1
    let occAnd := (occSig &&& occMask : Signal defaultDomain (BitVec 2))
    let occIsZero := (occAnd === p0_2 : Signal defaultDomain Bool)
    let occHere := (~~~occIsZero : Signal defaultDomain Bool)
    let combineReq := (busySig &&& occHere : Signal defaultDomain Bool)
    let pushAccepted := ((fun b p => !b && p) <$> busySig <*> push : Signal defaultDomain Bool)
    let placeNow := (busySig &&& occIsZero : Signal defaultDomain Bool)
    let combStep := (combineReq &&& combineDone : Signal defaultDomain Bool)
    let lvlInc := (lvlSig + p1_2 : Signal defaultDomain (BitVec 2))
    let occSet := (occSig ||| occMask : Signal defaultDomain (BitVec 2))
    let notMask := (~~~occMask : Signal defaultDomain (BitVec 2))
    let occClr := (occSig &&& notMask : Signal defaultDomain (BitVec 2))
    let placeS0 := (placeNow &&& isL0 : Signal defaultDomain Bool)
    s0R <~ Signal.mux start p0_8 (Signal.mux placeS0 carrySig s0Sig)
    occR <~ Signal.mux start p0_2
              (Signal.mux placeNow occSet
                (Signal.mux combStep occClr occSig))
    carryR <~ Signal.mux start p0_8
                (Signal.mux pushAccepted leafIn
                  (Signal.mux combStep combineOut carrySig))
    lvlR <~ Signal.mux start p0_2
              (Signal.mux pushAccepted p0_2
                (Signal.mux combStep lvlInc
                  (Signal.mux placeNow p0_2 lvlSig)))
    busyR <~ Signal.mux start (Signal.pure false : Signal defaultDomain Bool)
              (Signal.mux pushAccepted (Signal.pure true : Signal defaultDomain Bool)
                (Signal.mux placeNow (Signal.pure false : Signal defaultDomain Bool) busySig))
    return s0Sig

/-! ## Accepted -/

/-- info: VED U1 OK Tests.Ved.U1MerkleWhnfCheck.merkleMini.ved_u1: [Classical.choice, Quot.sound, propext] -/
#guard_msgs (info, drop warning) in
set_option Elab.async false in
set_option ved.u1.proofHeartbeats 2000000 in
run_cmd liftTermElabM do
  let (_, _, thm) ← vedU1Entry ``merkleMini
  let r ← Tools.VedStrictAudit.strictAudit thm
  logInfo m!"VED U1 OK {thm}: {Tools.VedStrictAudit.showNames r.axioms}"

example : U1Stmt merkleMini.ved_contract merkleMini.ved_mod merkleMini := merkleMini.ved_u1

/-- info: complete type and std3 axioms: merkleMini -/
#guard_msgs in
run_cmd liftTermElabM do
  let n := ``merkleMini
  let ti ← getConstInfo (n ++ `ved_u1)
  let expected := mkAppN (mkConst ``U1Stmt) #[mkConst (n ++ `ved_contract), mkConst (n ++ `ved_mod), mkConst n]
  unless ti.type == expected do throwError "type of {n}.ved_u1 is not the expected statement"
  let axs ← collectAxioms (n ++ `ved_u1)
  let std3 : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless axs.all (std3.contains ·) do throwError "{n}.ved_u1 axioms {axs}"
  logInfo "complete type and std3 axioms: merkleMini"

/-! ## Control: altered output stays refused -/

def modOf (base : Name) : TermElabM Sparkle.IR.AST.Module := do
  let some v := (← getConstInfo (base ++ `ved_mod)).value? | throwError "no value"
  evalModule v

def checkerNames (base : Name) : List Name :=
  [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_u1].map (base ++ ·)

def expectRefused (stage : String) (absent : List Name) (act : TermElabM Unit) : CommandElabM Unit := liftTermElabM do
  let accepted ← try act; pure true catch e =>
    let s ← e.toMessageData.toString
    unless s.startsWith "VED U1 REFUSED" && (s.splitOn s!"[{stage}]").length > 1 do throw e
    pure false
  if accepted then throwError "control ACCEPTED (expected a refusal at [{stage}])"
  let env ← getEnv
  for n in absent do
    if env.contains n then throwError "left behind: {n}"
  logInfo m!"refused [{stage}], clean"

/-- the output altered by the constant 1 -/
def mutOut (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .assign "out" e => .assign "out" (.op .add [e, .const 1 8])
      | s => s }

/-- info: mutation differs from the original -/
#guard_msgs in
run_cmd liftTermElabM do
  let m ← modOf ``merkleMini
  if decide (mutOut m = m) then throwError "the mutation is the identity"
  logInfo "mutation differs from the original"

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlOut) do
  discard <| checkU1 ``merkleMini `ctlOut ``merkleMini (mutOut (← modOf ``merkleMini)) .generated

end Tests.Ved.U1MerkleWhnfCheck
