import Tests.Ved.U1MultiLoopRow
import Tests.IP.Crypto.Eip1559EnvelopeHWTest
import Tests.IP.Net.UARTTest
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# `#ved_u1` on real IP rows with SEVERAL registers built by `Signal.loop` (sparkle-ved-u1-multiloop)

A `circuit do` block with `k` registers is ONE `Signal.loop` over the tuple of their values (and a
nested `circuit do` inside is a second loop).  The generated script proves, by induction on the cycle,
that register `n` of the returned module is the `toNat` of the loop-state component it implements
(`Tools/VedU1Loop.lean`: `loop_val_unfold`, the tactics `ved_loop_R` / `ved_loop_gen`; the script is
`loopScriptFor` in `Tools/VedU1Entry.lean`).  No unsupplied hypothesis, no change to the statement
(`U1Stmt c m f`), the kernel checks everything.

This is the PR check: three representative rows and the refusal controls.  The other 23 accepted rows
are in `U1MultiLoopFull1` / `Full2` / `Full3` (split so no single Lake module carries all 26 proofs;
the one-file version took about 15 minutes as one module) and `U1MultiLoopAll` checks all 26 together.

What is fixed here:
1. the ORIGINAL (`private`) declarations `synth_uartTx`, `synth_uartRx`, `synth_envByte` are accepted
   by `#ved_u1`, each followed by the audit (std3 axioms);
2. `checkRows`: for each row the stored type of `<decl>.ved_u1` compared with `==` against the expected
   `U1Stmt <decl>.ved_contract <decl>.ved_mod <decl>` and the axioms are within std3;
3. refusals (`expectRefused`, stage `[proof]`, nothing left behind): on the real `synth_uartTx`
   one register's next value changed, a wrong initial value; on the real `synth_envByte` two
   same-width registers swapped; on local stand-ins a register read one cycle late.
-/

namespace Tests.Ved.U1MultiLoopCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core
open Tools.VedU1Contract Tools.VedU1Entry

open Tests.Ved.U1MultiLoopRow

/-! ## 1. Positives (the original declarations) -/

#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Net.UARTTest synth_uartTx
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Net.UARTTest synth_uartRx
#guard_msgs (drop info) in
#ved_u1_row Tests.IP.Crypto.Eip1559EnvelopeHWTest synth_envByte

/-! ## 2. Stored type and axioms -/

def rows : List (Name × Name) :=
  [(`Tests.IP.Net.UARTTest, `synth_uartTx), (`Tests.IP.Net.UARTTest, `synth_uartRx),
   (`Tests.IP.Crypto.Eip1559EnvelopeHWTest, `synth_envByte)]

/-- info: OK 3 rows: stored type = U1Stmt c m F, axioms within std3 -/
#guard_msgs in
run_cmd checkRows rows

example : rows.length = 3 := by decide

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

/-- One register's next value changed: the constant `10#4` (the bit counter's reload value) is `11#4`. -/
def mutNext (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .assign n (.const 10 4) => .assign n (.const 11 4)
      | s => s }

/-- A wrong initial value on every register. -/
def mutInit (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .register o c r e i => .register o c r e (i + 1)
      | s => s }

/-- The two registers of width 11 exchange their output names (their cones, inits and the wires stay). -/
def mutSwap11 (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  let ws := (regsOf m.body).filter (fun r => declWidth m r.1 == 11)
  match ws with
  | (r1, _, _, _) :: (r2, _, _, _) :: _ =>
    { m with body := m.body.map fun s => match s with
        | .register o c r e i =>
          .register (if o == r1 then r2 else if o == r2 then r1 else o) c r e i
        | s => s }
  | _ => m

/-- info: mutations differ from the originals -/
#guard_msgs in
run_cmd liftTermElabM do
  let m ← modOf (privName `Tests.IP.Net.UARTTest `synth_uartTx)
  let e ← modOf (privName `Tests.IP.Crypto.Eip1559EnvelopeHWTest `synth_envByte)
  if decide (mutNext m = m) || decide (mutInit m = m) || decide (mutSwap11 e = e) then
    throwError "a mutation is the identity"
  logInfo "mutations differ from the originals"

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlNext) do
  let d := privName `Tests.IP.Net.UARTTest `synth_uartTx
  discard <| checkU1 d `ctlNext d (mutNext (← modOf d)) .generated

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlInit) do
  let d := privName `Tests.IP.Net.UARTTest `synth_uartTx
  discard <| checkU1 d `ctlInit d (mutInit (← modOf d)) .generated

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlSwap) do
  let d := privName `Tests.IP.Crypto.Eip1559EnvelopeHWTest `synth_envByte
  discard <| checkU1 d `ctlSwap d (mutSwap11 (← modOf d)) .generated

/-! ### a register read one cycle late (local stand-ins)

`lateA` is the module that is synthesized; the statement `lateB` reads register `a` through one more
register (one cycle late).  The module of `lateA` does not have `lateB`'s meaning. -/

def lateA (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg 0#8
    let b ← Signal.reg 0#8
    a <~ a + x
    b <~ b + a
    let aS := (a : Signal defaultDomain (BitVec 8))
    let bS := (b : Signal defaultDomain (BitVec 8))
    return aS + bS

def lateB (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg 0#8
    let b ← Signal.reg 0#8
    a <~ a + x
    b <~ b + a
    let aS := (a : Signal defaultDomain (BitVec 8))
    let bS := (b : Signal defaultDomain (BitVec 8))
    return Signal.register 0#8 aS + bS

-- the stand-in itself is accepted (two loop registers, same width)
#guard_msgs (drop info) in
#ved_u1 lateA

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlLate) do
  let (m, _) ← Sparkle.Compiler.Elab.synthesizeCombinational ``lateA
  discard <| checkU1 ``lateB `ctlLate ``lateB m .generated

end Tests.Ved.U1MultiLoopCheck
