import Tests.Ved.U1MultiLoopRow
import Tests.IP.Crypto.BIP32CKDHWTest

/-!
# `#ved_u1` on a real IP row with eleven registers built by `Signal.loop` (sparkle-ved-script-cost, round 4)

The generated script of `Tools/VedU1Loop.lean` simplified the whole step of the module in one `simp`;
on a module with many registers (a BIP-32 child-key FSM: eleven registers packed into one loop, 49
assignments, 64-bit and 256-bit words) that `simp` exceeds its step limit, so the row was refused
at `[proof]`.  `Tools/VedU1ScriptSeq.lean` and `Tools/VedU1ScriptSeqGen.lean` are the first attempt the
entry now makes for a module with two or more registers (`tryScriptFirst`): the step of the module
from ONE lemma (`step_seq`: one environment `E`, one equation per assignment over that same `E`,
the register updates as a pure list), every assignment normalised on its own and kept as an
auxiliary theorem, the packed loop state read back field by field.  If the attempt fails the flat
script of `Tools/VedU1Entry.lean` runs as before.

What is fixed here:
1. the ORIGINAL (`private`) declaration `synth_ckd_cc0` is accepted by `#ved_u1`, followed by the
   audit (std3 axioms);
2. `checkRows`: the stored type of `<decl>.ved_u1` compared with `==` against the expected
   `U1Stmt <decl>.ved_contract <decl>.ved_mod <decl>`, axioms within std3;
3. refusals (`expectRefused`, stage `[proof]`, nothing left behind) on the real module with one
   change each: a wrong initial value, one mux constant of the state machine changed, two registers of
   the same width exchanging their output names.
-/

namespace Tests.Ved.U1SeqCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.VedU1Contract Tools.VedU1Entry
open Tests.Ved.U1MultiLoopRow

/-! ## 1. Positive (the original declaration) -/

#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Crypto.BIP32CKDHWTest synth_ckd_cc0

/-! ## 2. Stored type and axioms -/

def rows : List (Name × Name) :=
  [(`Tests.IP.Crypto.BIP32CKDHWTest, `synth_ckd_cc0)]

/-- info: OK 1 rows: stored type = U1Stmt c m F, axioms within std3 -/
#guard_msgs in
run_cmd checkRows rows

/-! ## 3. Refusals -/

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

def decl : Name :=
  privName `Tests.IP.Crypto.BIP32CKDHWTest `synth_ckd_cc0

/-- A wrong initial value on every register. -/
def mutInit (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .register o c r e i => .register o c r e (i + 1)
      | s => s }

/-- One mux constant of the state machine changed (state `5` becomes `6`). -/
def mutConst (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .assign n (.const 5 3) => .assign n (.const 6 3)
      | s => s }

/-- The first two registers of width 64 exchange their output names (cones, inits and wires stay). -/
def mutSwap64 (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  let ws := (regsOf m.body).filter (fun r => declWidth m r.1 == 64)
  match ws with
  | (r1, _, _, _) :: (r2, _, _, _) :: _ =>
    { m with body := m.body.map fun s => match s with
        | .register o c r e i =>
          .register (if o == r1 then r2 else if o == r2 then r1 else o) c r e i
        | s => s }
  | _ => m

/-- info: mutations differ from the original -/
#guard_msgs in
run_cmd liftTermElabM do
  let m ← modOf decl
  if decide (mutInit m = m) || decide (mutConst m = m) || decide (mutSwap64 m = m) then
    throwError "a mutation is the identity"
  logInfo "mutations differ from the original"

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlInit) do
  discard <| checkU1 decl `ctlInit decl (mutInit (← modOf decl)) .generated

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlConst) do
  discard <| checkU1 decl `ctlConst decl (mutConst (← modOf decl)) .generated

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlSwap) do
  discard <| checkU1 decl `ctlSwap decl (mutSwap64 (← modOf decl)) .generated

end Tests.Ved.U1SeqCheck
