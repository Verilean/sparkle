import Sparkle
import Sparkle.Compiler.Elab
import Tools.VedMemEntry

/-!
# Checks for the memory entry (`Tools/VedMemEntry.lean`, `Tools/VedMem.lean`; sparkle-ved-memory)

* ENTRY RUNS: `#ved_u1_mem d` (register-free and `Signal.loop` modules with memories) and `#ved_u1_mem_packed d`
  (a product result), one `synthesizeCombinational` per run, kernel, strict audit.  The examples are
  `quantModule`'s memory shape (a combinational-read input memory written from ports, a registered-read output memory
  written at the counter's address while busy) in a smaller body.
* STORED TYPE: the theorem's type is `==` the statement the entry builds (`MemStmt` / `MemPackedStmt`) over the
  module and contract constants it registered and the declaration; axioms are the three standard ones, read by an
  independent `collectAxioms` probe.
* CONTROLS (through `checkMemE`, the entry's own checker with the statement of a DIFFERENT declaration over the module
  of another): changed write value, write address, write enable, read timing (combinational vs registered), initial
  contents.  Each is pinned as a refusal at a named stage, and the checker's constants are absent afterwards.
-/

namespace Tests.Ved.VedMemCheck

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.StateMacro
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedMemEntry

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Declarations (single memory, no registers) -/

def memBase {dom : DomainConfig} (writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) (readAddr : Signal dom (BitVec 4)) (go : Signal dom Bool) :
    Signal dom (BitVec 16) :=
  Signal.memoryComboRead writeAddr writeData writeEn readAddr

/-- another write VALUE -/
def memData {dom : DomainConfig} (writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) (readAddr : Signal dom (BitVec 4)) (go : Signal dom Bool) :
    Signal dom (BitVec 16) :=
  Signal.memoryComboRead writeAddr (writeData + 1#16) writeEn readAddr

/-- another write ADDRESS (the other address input) -/
def memAddr {dom : DomainConfig} (writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) (readAddr : Signal dom (BitVec 4)) (go : Signal dom Bool) :
    Signal dom (BitVec 16) :=
  Signal.memoryComboRead readAddr writeData writeEn writeAddr

/-- another write ENABLE (the other `Bool` input) -/
def memEn {dom : DomainConfig} (writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) (readAddr : Signal dom (BitVec 4)) (go : Signal dom Bool) :
    Signal dom (BitVec 16) :=
  Signal.memoryComboRead writeAddr writeData go readAddr

/-- another READ TIMING: registered read -/
def memSync {dom : DomainConfig} (writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) (readAddr : Signal dom (BitVec 4)) (go : Signal dom Bool) :
    Signal dom (BitVec 16) :=
  Signal.memory writeAddr writeData writeEn readAddr

/-- another INITIAL value -/
def memInit {dom : DomainConfig} (writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) (readAddr : Signal dom (BitVec 4)) (go : Signal dom Bool) :
    Signal dom (BitVec 16) :=
  Signal.memoryWithInit (fun _ => 7#16) writeAddr writeData writeEn readAddr

/-! ## Declarations (two memories, `quantModule`'s shape) -/

/-- two memories, no registers -/
def memPair {dom : DomainConfig} (writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) (readAddr : Signal dom (BitVec 4)) (go : Signal dom Bool) :
    Signal dom (BitVec 16) :=
  let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr
  let signBit := inputCoeff.map (BitVec.extractLsb' 15 1 ·)
  let isNeg := signBit === 1#1
  let result := Signal.mux isNeg (0#16 - inputCoeff) inputCoeff
  Signal.memory readAddr result go (Signal.pure 0#4)

declare_signal_state QState
  | idx  : BitVec 5  := 0#5
  | busy : Bool      := false
  | last : BitVec 16 := 0#16

/-- `quantModule` in miniature: a counter reads an input memory, and a registered output memory is written at that
address while busy (a 5-bit counter addresses 4-bit memories through `idx[3:0]`) -/
def memQuant {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
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
  QState.last state

/-- the same with a product result (the shape of `quantModule`'s three outputs) -/
def memQuantP {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
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

/-! ## Entry runs -/

#guard_msgs (drop info) in
#ved_u1_mem memBase
#guard_msgs (drop info) in
#ved_u1_mem memData
#guard_msgs (drop info) in
#ved_u1_mem memAddr
#guard_msgs (drop info) in
#ved_u1_mem memEn
#guard_msgs (drop info) in
#ved_u1_mem memSync
#guard_msgs (drop info) in
#ved_u1_mem memPair
#guard_msgs (drop info) in
#ved_u1_mem memQuant
#guard_msgs (drop info) in
#ved_u1_mem_packed memQuantP

/-! ## Stored type `==` the statement, standard axioms (independent probe) -/

/-- the stored theorem's type is `MemStmt` / `MemPackedStmt` of the registered contract and module and the
declaration (specialised at `defaultDomain`), and `collectAxioms` gives exactly the three standard axioms -/
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

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCheck.memBase -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``memBase false
/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCheck.memPair -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``memPair false
/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCheck.memQuant -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``memQuant false
/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCheck.memQuantP -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``memQuantP true

/-! ## The lemmas: standard axioms only (independent probe) -/

/-- every lemma of `Tools/VedMem.lean` (and the operator lemmas of `Tools/VedMemLoop.lean`) uses `propext`,
`Classical.choice`, `Quot.sound` at most -/
def lemmasOk : TermElabM Unit := do
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let names : List Name := [``Tools.VedMem.memState_init, ``Tools.VedMem.mem_read_after_write, ``Tools.VedMem.mem_hold_disabled, ``Tools.VedMem.mem_hold_other, ``Tools.VedMem.mem_step_eq, ``Tools.VedMem.memory_val_zero', ``Tools.VedMem.memory_registered_read, ``Tools.VedMem.memory_eq_combo_delayed, ``Tools.VedMem.memory_same_cycle_reads_old, ``Tools.VedMem.memory_next_cycle_reads_new, ``Tools.VedMem.combo_same_cycle_reads_old, ``Tools.VedMem.combo_next_cycle_reads_new, ``Tools.VedMem.combo_unwritten_reads_init, ``Tools.VedMem.memoryWithInit_val_zero, ``Tools.VedMem.memoryWithInit_zero_eq_memory, ``Tools.VedMem.memory_ne_combo, ``Tools.VedMem.memoryWithInit_ne_memory, ``Tools.VedMem.evalPayload_ref, ``Tools.VedMem.memWritePorts_one, ``Tools.VedMem.memWritePorts_ref_one, ``Tools.VedMem.memNexts_one, ``Tools.VedMem.loop_val_unfold_strong, ``Tools.VedMem.memState_congr, ``Tools.VedMem.ofNat_mask_eq, ``Tools.VedMem.MemInv.read, ``Tools.VedMem.ofNat_eq_iff, ``Tools.VedMem.ofNat_mod_eq_extract, ``Tools.VedMem.ofNat_mod_eq_extract', ``Tools.VedMem.mask_toNat, ``Tools.VedMem.MemInv.write, ``Tools.VedMem.MemInv.other, ``Tools.VedMem.MemInv.write', ``Tools.VedMem.MemInv.other', ``Tools.VedMem.MemInv.write'', ``Tools.VedMem.MemInv.other'', ``Tools.VedMem.MemInv.read', ``Tools.VedMem.outputs_of_step_mem, ``Tools.VedMem.outputs_of_orderM, ``Tools.VedMem.MemInv.zero,
    ``Tools.VedMemLoop.add_val_bs, ``Tools.VedMemLoop.sub_val_bs, ``Tools.VedMemLoop.mul_val_sb]
  for n in names do
    let axs ← collectAxioms n
    unless axs.all (std.contains ·) do throwError "{n}: axioms {axs}"
  logInfo m!"{names.length} lemmas, axioms within std3"

/-- info: 42 lemmas, axioms within std3 -/
#guard_msgs in
run_cmd liftTermElabM lemmasOk

/-! ## Controls -/

/-- The module a previous entry run registered (its closed term evaluated). -/
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

/-- the statement of `stmtDecl` over the module of `modDecl` -/
def cross (modDecl stmtDecl : Name) (base : Name) : TermElabM Unit := do
  let (stmt, _) ← specialiseDomain stmtDecl
  discard <| checkMemE stmtDecl base stmt (← modOf modDecl)

/-- info: refused [proof], clean -/
#guard_msgs (info, drop trace) in
run_cmd expectRefused "proof" (checkerNames `ctlValue) (cross ``memBase ``memData `ctlValue)
/-- info: refused [proof], clean -/
#guard_msgs (info, drop trace) in
run_cmd expectRefused "proof" (checkerNames `ctlValue2) (cross ``memData ``memBase `ctlValue2)
/-- info: refused [proof], clean -/
#guard_msgs (info, drop trace) in
run_cmd expectRefused "proof" (checkerNames `ctlAddr) (cross ``memBase ``memAddr `ctlAddr)
/-- info: refused [proof], clean -/
#guard_msgs (info, drop trace) in
run_cmd expectRefused "proof" (checkerNames `ctlEn) (cross ``memBase ``memEn `ctlEn)

/-! Read timing: the memory statement of a combinational read is not matched to the registered read of the other
declaration's call (and the other way): refused at `shape`, before any proof. -/

/-- info: refused [shape], clean -/
#guard_msgs (info, drop trace) in
run_cmd expectRefused "shape" (checkerNames `ctlTiming) (cross ``memBase ``memSync `ctlTiming)
/-- info: refused [shape], clean -/
#guard_msgs (info, drop trace) in
run_cmd expectRefused "shape" (checkerNames `ctlTiming2) (cross ``memSync ``memBase `ctlTiming2)

/-! The initial contents: `Signal.memoryWithInit` has no hardware meaning in the synthesizer (it is refused at
`synthesis`, not given a zero image), so a declaration with a non-zero initial image is not accepted. -/

/-- info: refused [synthesis], clean -/
#guard_msgs (info, drop trace) in
run_cmd expectRefused "synthesis" (checkerNames ``memInit) do
  discard <| vedMemEntryS ``memInit

/-! A packed result is refused by the single-output entry, and a single result by the packed one. -/

/-- info: refused [multi-output], clean -/
#guard_msgs (info, drop trace) in
run_cmd expectRefused "multi-output" (checkerNames `ctlPk1) do
  let (stmt, _) ← specialiseDomain ``memQuantP
  discard <| checkMemE ``memQuantP `ctlPk1 stmt (← modOf ``memQuantP)

/-- info: refused [packed], clean -/
#guard_msgs (info, drop trace) in
run_cmd expectRefused "packed" (checkerNames `ctlPk2) do
  let (stmt, _) ← specialiseDomain ``memBase
  discard <| checkMemE ``memBase `ctlPk2 stmt (← modOf ``memBase) (packed := true)

end Tests.Ved.VedMemCheck
