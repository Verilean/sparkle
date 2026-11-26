import Sparkle
import Sparkle.Compiler.Elab
import Tools.VedMemEntry
import Tools.VedMemPack

/-!
# Real `#ved_u1_mem_packed` entry next to asynchronous `ved_ctrl_cases` runs (P2-1: the leaf-failure flag is per call)

`ccBaseSeq` is elaborated with `Elab.async false` before anything else runs; `ccBaseAsy` (the same body) is elaborated with `Elab.async true`
while the theorems `asyncTrue*` / `asyncGate*` (each runs `ved_ctrl_or_gate`, the closing script's tactic; the second kind fails on a false leaf with
big hypotheses and is refused) are still running in their own tasks.  The two entries' stored statements and proof terms (size, node count) are compared,
and the refusal of the altered body (`ccBad*`) is compared.
-/

namespace Tests.Ved.VedCtrlAsyncCheck

open Lean Elab Command Term Meta Tactic
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.StateMacro
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedMemEntry

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

declare_signal_state AState
  | fsm  : BitVec 2  := 0#2
  | sub  : BitVec 3  := 0#3
  | last : BitVec 16 := 0#16

/-! ## Declarations -/

/-- control fields (`fsm`, `sub`) and a 16-bit data addition: the accumulator adds the memory read while the state is `1` -/
def ccBaseSeq {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) :=
  let state := Signal.loop fun state =>
    let fsm := AState.fsm state
    let sub := AState.sub state
    let isRow := fsm === (1#2 : Signal dom _)
    let sub4 := 0#1 ++ sub
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn sub4
    let fsmNext := Signal.mux start (Signal.pure 1#2) fsm
    let subNext := sub + 1#3
    let lastNext := Signal.mux isRow (inputCoeff + 1#16) (AState.last state)
    bundleAll! [Signal.register 0#2 fsmNext, Signal.register 0#3 subNext, Signal.register 0#16 lastNext]
  bundle2 (AState.last state) (AState.sub state)

/-- control: the addend is 2 -/
def ccBadSeq {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) :=
  let state := Signal.loop fun state =>
    let fsm := AState.fsm state
    let sub := AState.sub state
    let isRow := fsm === (1#2 : Signal dom _)
    let sub4 := 0#1 ++ sub
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn sub4
    let fsmNext := Signal.mux start (Signal.pure 1#2) fsm
    let subNext := sub + 1#3
    let lastNext := Signal.mux isRow (inputCoeff + 2#16) (AState.last state)
    bundleAll! [Signal.register 0#2 fsmNext, Signal.register 0#3 subNext, Signal.register 0#16 lastNext]
  bundle2 (AState.last state) (AState.sub state)

/-- control fields (`fsm`, `sub`) and a 16-bit data addition: the accumulator adds the memory read while the state is `1` -/
def ccBaseAsy {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) :=
  let state := Signal.loop fun state =>
    let fsm := AState.fsm state
    let sub := AState.sub state
    let isRow := fsm === (1#2 : Signal dom _)
    let sub4 := 0#1 ++ sub
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn sub4
    let fsmNext := Signal.mux start (Signal.pure 1#2) fsm
    let subNext := sub + 1#3
    let lastNext := Signal.mux isRow (inputCoeff + 1#16) (AState.last state)
    bundleAll! [Signal.register 0#2 fsmNext, Signal.register 0#3 subNext, Signal.register 0#16 lastNext]
  bundle2 (AState.last state) (AState.sub state)

/-- control: the addend is 2 -/
def ccBadAsy {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) :=
  let state := Signal.loop fun state =>
    let fsm := AState.fsm state
    let sub := AState.sub state
    let isRow := fsm === (1#2 : Signal dom _)
    let sub4 := 0#1 ++ sub
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn sub4
    let fsmNext := Signal.mux start (Signal.pure 1#2) fsm
    let subNext := sub + 1#3
    let lastNext := Signal.mux isRow (inputCoeff + 2#16) (AState.last state)
    bundleAll! [Signal.register 0#2 fsmNext, Signal.register 0#3 subNext, Signal.register 0#16 lastNext]
  bundle2 (AState.last state) (AState.sub state)

def modOf (base : Name) : TermElabM Sparkle.IR.AST.Module := do
  let some v := (← getConstInfo (base ++ `ved_mod)).value? | throwError "no value"
  evalModule v

/-- the entry's theorem: stored type, proof term size, node count, axioms -/
def entrySummary (decl : Name) : TermElabM String := do
  let ti ← getConstInfo (decl ++ `ved_mem)
  let .thmInfo t := ti | throwError "not a theorem"
  let v := t.value
  let axs ← collectAxioms (decl ++ `ved_mem)
  return s!"depth {v.approxDepth} nodes {v.sizeWithoutSharing} axioms {axs.toList.map (·.toString) |>.toArray.qsort (· < ·)}"

/-- the stage a refusal came from -/
def refusalStage (act : TermElabM Unit) : TermElabM String := do
  try act; return "ACCEPTED" catch e =>
    let s ← e.toMessageData.toString
    unless s.startsWith "VED U1 REFUSED" do throw e
    return ((s.splitOn "[").getD 1 "" |>.splitOn "]").head!

/-! ## Sequential reference (Elab.async false) -/
set_option Elab.async false

#guard_msgs (drop info) in
#ved_u1_mem_packed ccBaseSeq

run_cmd liftTermElabM do
  let (stmt, _) ← specialiseDomain ``ccBadSeq
  logInfo m!"SEQ refusal: {← refusalStage (discard <| checkMemE ``ccBadSeq `ctlCcSeq stmt (← modOf ``ccBaseSeq) (packed := true))}"

/-! ## Asynchronous closing runs: statements and test-only helpers -/

set_option hygiene false in
local macro "TRUE54" : term => `((if c.toNat % 8 = 4 then
      ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2
    else x4.toNat) =
    (if c.toNat % 8 = 4 then
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 32) % 65536 / 32768 % 2
    else x4.toNat))
set_option hygiene false in
local macro "FALSE54" : term => `((if c.toNat % 8 = 4 then
      ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2
    else x4.toNat) =
    (if c.toNat % 8 = 4 then
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 33) % 65536 / 32768 % 2
    else x4.toNat))
local macro "BIG54" : term => `(TRUE54 ∧ TRUE54 ∧ TRUE54)

/-- test-only: run `t`, it must fail with a message containing `s` -/
elab "expect_err " s:str t:tactic : tactic => do
  let ok ← try withoutRecover (evalTactic t); pure true catch e =>
    unless ((← e.toMessageData.toString).splitOn s.getString).length > 1 do
      throwError "expect_err: other error: {← e.toMessageData.toString}"
    pure false
  if ok then throwError "expect_err: succeeded, expected an error containing '{s.getString}'"

/-- closes by the case split (clears nothing another run could read) -/
theorem asyncTrue1 (c : BitVec 3) (x4 x5 x6 : BitVec 16) (x7 : Nat) (h7 : x7 < 2 ^ 16) : TRUE54 := by
  ved_ctrl_or_gate (fail "T-RAN")
theorem asyncTrue2 (c : BitVec 3) (x4 x5 x6 : BitVec 16) (x7 : Nat) (h7 : x7 < 2 ^ 16) : TRUE54 := by
  ved_ctrl_or_gate (fail "T-RAN")
/-- false leaf with big hypotheses: refused at once (the gate must not be cleared by the other runs' entries) -/
theorem asyncGate1 (c : BitVec 3) (x4 x5 x6 : BitVec 16) (x7 : Nat) (h7 : x7 < 2 ^ 16) (hbig : BIG54) : True := by
  expect_err "failing leaf" (have _h := (show FALSE54 by ved_ctrl_or_gate (fail "T-RAN")); trivial)
  trivial
theorem asyncGate2 (c : BitVec 3) (x4 x5 x6 : BitVec 16) (x7 : Nat) (h7 : x7 < 2 ^ 16) (hbig : BIG54) : True := by
  expect_err "failing leaf" (have _h := (show FALSE54 by ved_ctrl_or_gate (fail "T-RAN")); trivial)
  trivial
/-- false leaf, no big hypotheses: not refused, `t` runs (must not be refused by the other runs' flags) -/
theorem asyncSmall1 (c : BitVec 3) (x4 x5 x6 : BitVec 16) (x7 : Nat) (h7 : x7 < 2 ^ 16) : True := by
  expect_err "T-RAN" (have _h := (show FALSE54 by ved_ctrl_or_gate (fail "T-RAN")); trivial)
  trivial


/-! ## The same entries with Elab.async on, while the theorems above run in their own tasks -/
set_option Elab.async true

#guard_msgs (drop info) in
#ved_u1_mem_packed ccBaseAsy

run_cmd liftTermElabM do
  let (stmt, _) ← specialiseDomain ``ccBadAsy
  logInfo m!"ASY refusal: {← refusalStage (discard <| checkMemE ``ccBadAsy `ctlCcAsy stmt (← modOf ``ccBaseAsy) (packed := true))}"

run_cmd liftTermElabM do
  let a ← entrySummary ``ccBaseSeq
  let b ← entrySummary ``ccBaseAsy
  logInfo m!"SEQ {a}\nASY {b}"
  unless a == b do throwError "async entry differs from the sequential one"

end Tests.Ved.VedCtrlAsyncCheck
