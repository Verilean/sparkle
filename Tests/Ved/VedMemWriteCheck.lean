import Sparkle
import Sparkle.Compiler.Elab
import Tools.VedMemEntry
import Tools.VedWriteChecked

/-!
# Checks for `#ved_write_checked mem_packed` (`Tools/VedWriteChecked.lean`; sparkle-ved-memory-conn)

`#ved_write_checked mem_packed decl "x.sv" "x_cppsim.h" [wires]` synthesizes ONCE, runs the memory entry's checker
(`checkMemE`, packed) on that `(m, d)` and hands the same design to the writer.  The small examples here are
NOT part of the 327 inventory rows.

* POSITIVE: a packed memory-in-a-loop declaration; the command succeeds; the stored theorem's type is `==`
  `MemPackedStmt` over the registered contract / module and the declaration; axioms are the three standard ones;
  the three files it writes are byte-identical to the files `#writeDesign` wrote for the same declaration.
* CONTROLS: the checker's refusals (`[packed]` for a one-output declaration) leave no file; the writer handed the
  design of another declaration, or a tampered module, is refused at `[written]` and no file is written.
-/

namespace Tests.Ved.VedMemWriteCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST (Design)
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.StateMacro
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedMemEntry Tools.VedWriteChecked

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

declare_signal_state QState
  | idx  : BitVec 5  := 0#5
  | busy : Bool      := false
  | last : BitVec 16 := 0#16

-- a combinational-read input memory written from ports, a registered-read output memory written while busy;
-- the result is a product (the shape of `quantModule`'s outputs)
set_option hygiene false in
macro "defWm " n:ident : command => `(def $n {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
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
  bundle2 (QState.last state) (bundle2 (QState.idx state) (QState.busy state)))

defWm wmP
defWm wmP2
defWm wmP3

/-- a one-output declaration (the packed entry refuses it) -/
def wmOne {dom : DomainConfig} (writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) (readAddr : Signal dom (BitVec 4)) :
    Signal dom (BitVec 16) :=
  Signal.memoryComboRead writeAddr writeData writeEn readAddr

/-! ## Positive: `#writeDesign` (A) and `#ved_write_checked mem_packed` (B) -/

#writeDesign wmP ".lake/build/gen/wm/wmP_a.sv" ".lake/build/gen/wm/wmP_a_cppsim.h"

#guard_msgs (drop info) in
#ved_write_checked mem_packed wmP ".lake/build/gen/wm/wmP_b.sv" ".lake/build/gen/wm/wmP_b_cppsim.h"

def std3 : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def checkPositive (stem : String) (decl : Name) : CommandElabM Unit := liftTermElabM do
  let (stmt, _) ← specialiseDomain decl
  let thm := decl ++ `ved_mem
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  let expected := mkAppN (Lean.mkConst ``MemPackedStmt)
    #[Lean.mkConst (decl ++ `ved_contract), Lean.mkConst (decl ++ `ved_mod), stmt]
  unless ti.type == expected do throwError "{thm}: stored type differs"
  let ax ← collectAxioms thm
  unless ax.all (std3.contains ·) && std3.all (ax.contains ·) do throwError "axioms {ax}"
  let d := ".lake/build/gen/wm/"
  for suf in [".sv", "_cppsim.h", "_jit.c"] do
    let a ← IO.FS.readFile (d ++ stem ++ "_a" ++ suf)
    let b ← IO.FS.readFile (d ++ stem ++ "_b" ++ suf)
    unless a == b do throwError "{decl}: file {suf} differs between #writeDesign and #ved_write_checked"
    if a.isEmpty then throwError "{decl}: empty {suf}"
  logInfo m!"checked-and-written OK {decl}"

/-- info: checked-and-written OK Tests.Ved.VedMemWriteCheck.wmP -/
#guard_msgs in
run_cmd checkPositive "wmP" ``wmP

/-! ## Controls: no file is written -/

def ctlPaths (tag : String) : IO (String × String) := do
  let sv := s!".lake/build/gen/wm/ctl_{tag}.sv"
  let h := s!".lake/build/gen/wm/ctl_{tag}_cppsim.h"
  for f in [sv, h, s!".lake/build/gen/wm/ctl_{tag}_jit.c"] do
    if ← System.FilePath.pathExists f then IO.FS.removeFile f
  return (sv, h)

def expectRefused (stage : String) (tag : String) (decl : Name)
    (feed : Sparkle.IR.AST.Module → Design → CommandElabM Design := fun m d => pure (hierDesignOf m d)) :
    CommandElabM Unit := do
  let (sv, h) ← ctlPaths tag
  let msgs0 := (← get).messages
  let mut refused := false
  let mut got := ""
  try
    discard <| run .memPacked decl sv h none feed
  catch e =>
    let t ← e.toMessageData.toString
    got := t
    if t.startsWith "VED U1 REFUSED" && (t.splitOn s!"[{stage}]").length > 1 then refused := true
  modify fun s => { s with messages := msgs0 }
  unless refused do throwError "control {tag} ACCEPTED or wrong stage (expected [{stage}]): {got}"
  for f in [sv, h, s!".lake/build/gen/wm/ctl_{tag}_jit.c"] do
    if ← System.FilePath.pathExists f then throwError "control {tag}: file {f} was written"
  logInfo m!"refused [{stage}], no file"

def tamperMod (x : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module := { x with body := x.body.drop 1 }

/-- info: refused [packed], no file -/
#guard_msgs in
run_cmd expectRefused "packed" "one" ``wmOne

/-- info: refused [written], no file -/
#guard_msgs in
run_cmd expectRefused "written" "tamper" ``wmP2 (fun m d => pure (hierDesignOf (tamperMod m) d))

/-- info: refused [written], no file -/
#guard_msgs in
run_cmd expectRefused "written" "swap" ``wmP3 (fun _ _ => liftTermElabM (Sparkle.Compiler.Elab.synthesizeHierarchical ``wmOne))

end Tests.Ved.VedMemWriteCheck
