import Sparkle
import Sparkle.Compiler.Elab
import Tools.VedMemEntry
import Tools.VedMemPack

/-!
# Checks for the stage tactics of the memory script (`Tools/VedMemPack.lean`; sparkle-ved-memory)

Small bodies through the memory entry (`#ved_u1_mem` / `#ved_u1_mem_packed`), one per tactic, each with proof that the tactic ran
and one refusal control (the same body with an altered output, refused at `[proof]`, nothing left behind).

* PROOF THAT A TACTIC RAN: `Tools.VedMemPack.ranLog` (test-only: each tactic appends to it on success, nothing in the proof path
  reads it) is cleared before the entry run and read after it.
* `ved_pack_dag` (stage 5, goals of at least `minTree` = 5000 nodes): `pdBase`, two memories whose address arithmetic is selected by
  the state.  A read of the packed state occurs in the proposition of an `if` and in its `Decidable` instance in different
  spellings (`2 ^ (1 + 1)` / `4`, a projection of a constructor): the log has `pack_dag_class` (a class of several spellings is
  rewritten at once; rewriting one spelling alone made the kernel unfold `Nat.div` / `Nat.mod`).  `memTwoMem` of `VedMemCheck`
  is the larger case of the same shape.
* `ved_decide_small2` (stage 7): `dsBase`, a packed result over bounded control fields only (every goal is a function of `BitVec.toNat`
  of small variables, closed by one kernel evaluation); `ved_ctrl_cases` does not run.
* `ved_ctrl_cases` (stage 7): `ccBase`, control fields and a 16-bit data addition (`ved_decide_small2` fails on the 16-bit atom).
-/

namespace Tests.Ved.VedMemPackCheck

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.StateMacro
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedMemEntry

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

declare_signal_state AState
  | fsm  : BitVec 2  := 0#2
  | sub  : BitVec 3  := 0#3
  | last : BitVec 16 := 0#16

/-! ## Declarations -/

/-- two memories, the read address (`BitVec` arithmetic) selected by the state, the second memory written by the state -/
def pdBase {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  let state := Signal.loop fun state =>
    let fsm := AState.fsm state
    let sub := AState.sub state
    let isRow := fsm === (1#2 : Signal dom _)
    let sub4 := 0#1 ++ sub
    let rowA := (sub4 * 2#4) + sub4
    let colA := (sub4 * 4#4) + 1#4
    let readAddr4 := Signal.mux isRow rowA colA
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr4
    let isCol := fsm === (2#2 : Signal dom _)
    let interWrEn := isRow &&& (sub === (4#3 : Signal dom _))
    let interRd := Signal.mux isCol readAddr4 (Signal.pure 0#4)
    let interData := Signal.memoryComboRead readAddr4 (AState.last state) interWrEn interRd
    let src := Signal.mux isRow inputCoeff interData
    let fsmNext := Signal.mux start (Signal.pure 1#2) fsm
    let subNext := sub + 1#3
    let lastNext := Signal.mux (sub === (0#3 : Signal dom _)) src (AState.last state)
    bundleAll! [Signal.register 0#2 fsmNext, Signal.register 0#3 subNext, Signal.register 0#16 lastNext]
  AState.last state

/-- control: the column address is one more -/
def pdBad {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  let state := Signal.loop fun state =>
    let fsm := AState.fsm state
    let sub := AState.sub state
    let isRow := fsm === (1#2 : Signal dom _)
    let sub4 := 0#1 ++ sub
    let rowA := (sub4 * 2#4) + sub4
    let colA := (sub4 * 4#4) + 2#4
    let readAddr4 := Signal.mux isRow rowA colA
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr4
    let isCol := fsm === (2#2 : Signal dom _)
    let interWrEn := isRow &&& (sub === (4#3 : Signal dom _))
    let interRd := Signal.mux isCol readAddr4 (Signal.pure 0#4)
    let interData := Signal.memoryComboRead readAddr4 (AState.last state) interWrEn interRd
    let src := Signal.mux isRow inputCoeff interData
    let fsmNext := Signal.mux start (Signal.pure 1#2) fsm
    let subNext := sub + 1#3
    let lastNext := Signal.mux (sub === (0#3 : Signal dom _)) src (AState.last state)
    bundleAll! [Signal.register 0#2 fsmNext, Signal.register 0#3 subNext, Signal.register 0#16 lastNext]
  AState.last state

declare_signal_state QState
  | idx  : BitVec 5  := 0#5
  | busy : Bool      := false
  | last : BitVec 16 := 0#16

/-- a counter reads an input memory and a registered output memory is written at that address while busy (`quantModule`'s
shape, a product result); the stored word is the sign-corrected read -/
def dsBase {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) :
    Signal dom (BitVec 16 × BitVec 5 × Bool) :=
  let state := Signal.loop fun state =>
    let idx := QState.idx state
    let busy := QState.busy state
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr4
    let signBit := inputCoeff.map (BitVec.extractLsb' 15 1 ·)
    let isNeg := signBit === 1#1
    let result := Signal.mux isNeg (0#16 - inputCoeff) inputCoeff
    let outMemRead := Signal.memory readAddr4 result busy (Signal.pure 0#4)
    let done := busy &&& (idx === 15#5)
    let busyNext := Signal.mux done (Signal.pure false) (Signal.mux start (Signal.pure true) busy)
    let idxNext := Signal.mux busy (idx + 1#5) (Signal.pure 0#5)
    bundleAll! [Signal.register 0#5 idxNext, Signal.register false busyNext, Signal.register 0#16 outMemRead]
  bundle2 (QState.last state) (bundle2 (QState.idx state) (QState.busy state))

/-- control: the done index is 14, not 15 -/
def dsBad {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) :
    Signal dom (BitVec 16 × BitVec 5 × Bool) :=
  let state := Signal.loop fun state =>
    let idx := QState.idx state
    let busy := QState.busy state
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr4
    let signBit := inputCoeff.map (BitVec.extractLsb' 15 1 ·)
    let isNeg := signBit === 1#1
    let result := Signal.mux isNeg (0#16 - inputCoeff) inputCoeff
    let outMemRead := Signal.memory readAddr4 result busy (Signal.pure 0#4)
    let done := busy &&& (idx === 14#5)
    let busyNext := Signal.mux done (Signal.pure false) (Signal.mux start (Signal.pure true) busy)
    let idxNext := Signal.mux busy (idx + 1#5) (Signal.pure 0#5)
    bundleAll! [Signal.register 0#5 idxNext, Signal.register false busyNext, Signal.register 0#16 outMemRead]
  bundle2 (QState.last state) (bundle2 (QState.idx state) (QState.busy state))

/-- control fields (`fsm`, `sub`) and a 16-bit data addition: the accumulator adds the memory read while the state is `1` -/
def ccBase {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
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
def ccBad {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
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

/-! ## Entry runs, with proof of which tactic ran -/

/-- the tactics that ran since the log was cleared: `want` all present, `absent` none -/
def ranCheck (want absent : List String) : CommandElabM Unit := do
  let log ← Tools.VedMemPack.ranLog.get
  for w in want do
    unless log.contains w do throwError "tactic did not run: {w} (log {log})"
  for a in absent do
    if log.contains a then throwError "tactic ran: {a} (log {log})"
  logInfo m!"ran: {want}"

run_cmd Tools.VedMemPack.ranLog.set #[]
#guard_msgs (drop info) in
#ved_u1_mem pdBase
/-- info: ran: [pack_dag, pack_dag_class] -/
#guard_msgs in
run_cmd ranCheck ["pack_dag", "pack_dag_class"] []

run_cmd Tools.VedMemPack.ranLog.set #[]
#guard_msgs (drop info) in
#ved_u1_mem_packed dsBase
/-- info: ran: [decide_small2] -/
#guard_msgs in
run_cmd ranCheck ["decide_small2"] ["ctrl_cases"]

run_cmd Tools.VedMemPack.ranLog.set #[]
#guard_msgs (drop info) in
#ved_u1_mem_packed ccBase
/-- info: ran: [ctrl_cases] -/
#guard_msgs in
run_cmd ranCheck ["ctrl_cases"] []

/-! ## Stored type `==` the statement, standard axioms (independent probe) -/

def storedOk (decl : Name) (packed : Bool) : TermElabM Unit := do
  let (stmt, _) ← specialiseDomain decl
  let thm := decl ++ `ved_mem
  let ti ← getConstInfo thm
  let expected := mkAppN (Lean.mkConst (if packed then ``MemPackedStmt else ``Tools.VedMem.MemStmt))
    #[Lean.mkConst (decl ++ `ved_contract), Lean.mkConst (decl ++ `ved_mod), stmt]
  unless ti.type == expected do throwError "{thm}: stored type differs from the statement"
  let axs ← collectAxioms thm
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless axs.all (std.contains ·) && std.all (axs.contains ·) do throwError "{thm}: axioms {axs}"
  logInfo m!"stored type == statement, axioms std3: {decl}"

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemPackCheck.pdBase -/
#guard_msgs (info, drop trace) in
run_cmd liftTermElabM <| storedOk ``pdBase false
/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemPackCheck.dsBase -/
#guard_msgs (info, drop trace) in
run_cmd liftTermElabM <| storedOk ``dsBase true
/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemPackCheck.ccBase -/
#guard_msgs (info, drop trace) in
run_cmd liftTermElabM <| storedOk ``ccBase true

/-! ## Controls (through `checkMemE`: the statement of the altered declaration over the module of the accepted one) -/

def modOf (base : Name) : TermElabM Sparkle.IR.AST.Module := do
  let some v := (← getConstInfo (base ++ `ved_mod)).value? | throwError "no value"
  evalModule v

def checkerNames (base : Name) : List Name :=
  [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_mem].map (base ++ ·)

def assertClean (absent : List Name) : TermElabM Unit := do
  let env ← getEnv
  for n in absent do
    if env.contains n then throwError "left behind: {n}"

/-- `act` must be refused at `stage`, and afterwards none of `absent` may be in the environment -/
def expectRefused (stage : String) (absent : List Name) (act : TermElabM Unit) :
    CommandElabM Unit := liftTermElabM do
  let accepted ← try act; pure true catch e =>
    let s ← e.toMessageData.toString
    unless s.startsWith "VED U1 REFUSED" && (s.splitOn s!"[{stage}]").length > 1 do throw e
    pure false
  if accepted then throwError "control ACCEPTED (expected a refusal at [{stage}])"
  assertClean absent
  logInfo m!"refused [{stage}], clean"

/-- info: refused [proof], clean -/
#guard_msgs (info, drop trace) in
run_cmd expectRefused "proof" (checkerNames `ctlPd) do
  let (stmt, _) ← specialiseDomain ``pdBad
  discard <| checkMemE ``pdBad `ctlPd stmt (← modOf ``pdBase)

/-- info: refused [proof], clean -/
#guard_msgs (info, drop trace) in
run_cmd expectRefused "proof" (checkerNames `ctlDs) do
  let (stmt, _) ← specialiseDomain ``dsBad
  discard <| checkMemE ``dsBad `ctlDs stmt (← modOf ``dsBase) (packed := true)

/-- info: refused [proof], clean -/
#guard_msgs (info, drop trace) in
run_cmd expectRefused "proof" (checkerNames `ctlCc) do
  let (stmt, _) ← specialiseDomain ``ccBad
  discard <| checkMemE ``ccBad `ctlCc stmt (← modOf ``ccBase) (packed := true)

end Tests.Ved.VedMemPackCheck
