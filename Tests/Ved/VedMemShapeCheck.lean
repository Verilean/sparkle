import Sparkle
import Sparkle.Compiler.Elab
import Tools.VedMemEntry

/-!
# Checks for loops inside a loop body (`Tools/VedMemShape.lean`, `Tools/VedMemNest.lean`; sparkle-ved-memory-rest)

* ENTRY RUN: `#ved_u1_mem memNest`, a loop with a memory whose body holds a second `Signal.loop` driven by the outer
  state (a counter enabled by `busy`; the shape of the SoC's divider).  The inner loop mentions the outer state
  variable, so the loops with no loose bound variable (`Tools.VedU1Loop.loopsOf`) miss it and its two registers had no
  component; `Tools.VedMemShape.nestedLoops` enters the loop bodies and pairs them.  The stored type is `==` the
  statement the entry builds and the axioms are the three standard ones.
* CONTROLS (the entry's own checker with the statement of a DIFFERENT declaration over the module of `memNest`):
  a declaration without the inner loop (3 components against 5 registers) is refused at `shape`; one whose inner
  counter steps by 2 (the pairing is by width and position, the proof compares every register's equation) is refused
  at `proof`.  The checker's constants are absent afterwards.
-/

namespace Tests.Ved.VedMemShapeCheck

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.StateMacro
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedMemEntry

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

declare_signal_state NQ
  | idx  : BitVec 5  := 0#5
  | busy : Bool      := false
  | last : BitVec 16 := 0#16

/-- a 2-register inner loop, driven by the outer state -/
def innerCnt {dom : DomainConfig} (en : Signal dom Bool) : Signal dom (BitVec 3 × Bool) :=
  Signal.loop fun st =>
    let c := Signal.fst st
    bundleAll! [Signal.register 0#3 (Signal.mux en (c + 1#3) c), Signal.register false (c === (7#3 : Signal dom _))]

/-- the same with a counter that steps by 2 -/
def innerCnt2 {dom : DomainConfig} (en : Signal dom Bool) : Signal dom (BitVec 3 × Bool) :=
  Signal.loop fun st =>
    let c := Signal.fst st
    bundleAll! [Signal.register 0#3 (Signal.mux en (c + 2#3) c), Signal.register false (c === (7#3 : Signal dom _))]

def memNest {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  let state := Signal.loop fun state =>
    let idx := NQ.idx state
    let busy := NQ.busy state
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr4
    let outMemRead := Signal.memory readAddr4 inputCoeff busy (Signal.pure 0#4)
    let cnt := innerCnt busy
    let cf := Signal.snd cnt
    let done := busy &&& cf
    let busyNext := Signal.mux done (Signal.pure false) (Signal.mux start (Signal.pure true) busy)
    let idxNext := Signal.mux busy (idx + 1#5) (Signal.pure 0#5)
    bundleAll! [Signal.register 0#5 idxNext, Signal.register false busyNext, Signal.register 0#16 outMemRead]
  NQ.last state

/-- control: no inner loop (`done` from the index) -/
def memNoInner {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  let state := Signal.loop fun state =>
    let idx := NQ.idx state
    let busy := NQ.busy state
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr4
    let outMemRead := Signal.memory readAddr4 inputCoeff busy (Signal.pure 0#4)
    let done := busy &&& (idx === (15#5 : Signal dom _))
    let busyNext := Signal.mux done (Signal.pure false) (Signal.mux start (Signal.pure true) busy)
    let idxNext := Signal.mux busy (idx + 1#5) (Signal.pure 0#5)
    bundleAll! [Signal.register 0#5 idxNext, Signal.register false busyNext, Signal.register 0#16 outMemRead]
  NQ.last state

/-- control: the inner counter steps by 2 -/
def memNest2 {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  let state := Signal.loop fun state =>
    let idx := NQ.idx state
    let busy := NQ.busy state
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr4
    let outMemRead := Signal.memory readAddr4 inputCoeff busy (Signal.pure 0#4)
    let cnt := innerCnt2 busy
    let cf := Signal.snd cnt
    let done := busy &&& cf
    let busyNext := Signal.mux done (Signal.pure false) (Signal.mux start (Signal.pure true) busy)
    let idxNext := Signal.mux busy (idx + 1#5) (Signal.pure 0#5)
    bundleAll! [Signal.register 0#5 idxNext, Signal.register false busyNext, Signal.register 0#16 outMemRead]
  NQ.last state

#guard_msgs (drop info) in
#ved_u1_mem memNest

def storedOk (decl : Name) : TermElabM Unit := do
  let (stmt, _) ← specialiseDomain decl
  let thm := decl ++ `ved_mem
  let ti ← getConstInfo thm
  let expected := mkAppN (Lean.mkConst ``Tools.VedMem.MemStmt)
    #[Lean.mkConst (decl ++ `ved_contract), Lean.mkConst (decl ++ `ved_mod), stmt]
  unless ti.type == expected do throwError "{thm}: stored type differs from the statement"
  let axs ← collectAxioms thm
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless axs.all (std.contains ·) && std.all (axs.contains ·) do throwError "{thm}: axioms {axs}"
  logInfo m!"stored type == statement, axioms std3: {decl}"

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemShapeCheck.memNest -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``memNest

/-- the lemma of the congruence: standard axioms only -/
def lemmaOk : TermElabM Unit := do
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let axs ← collectAxioms ``Tools.VedMemNest.loop_val_congr_le
  unless axs.all (std.contains ·) do throwError "axioms {axs}"
  logInfo m!"loop_val_congr_le: axioms within std3"

/-- info: loop_val_congr_le: axioms within std3 -/
#guard_msgs in
run_cmd liftTermElabM lemmaOk

def modOf (base : Name) : TermElabM Sparkle.IR.AST.Module := do
  let some v := (← getConstInfo (base ++ `ved_mod)).value? | throwError "no value"
  evalModule v

def checkerNames (base : Name) : List Name :=
  [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_mem].map (base ++ ·)

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

def cross (modDecl stmtDecl : Name) (base : Name) : TermElabM Unit := do
  let (stmt, _) ← specialiseDomain stmtDecl
  discard <| checkMemE stmtDecl base stmt (← modOf modDecl)

/-- info: refused [shape], clean -/
#guard_msgs (info, drop trace) in
run_cmd expectRefused "shape" (checkerNames `ctlNoInner) (cross ``memNest ``memNoInner `ctlNoInner)

/-- info: refused [proof], clean -/
#guard_msgs (info, drop trace) in
run_cmd expectRefused "proof" (checkerNames `ctlInner2) (cross ``memNest ``memNest2 `ctlInner2)

end Tests.Ved.VedMemShapeCheck
