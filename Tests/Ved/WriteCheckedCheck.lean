import Tools.VedWriteChecked
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Checks for `#ved_write_checked` (one synthesis, checked, then the very same value written)

`#ved_write_checked KIND decl "x.sv" "x_cppsim.h" [wires]` synthesizes ONCE, runs the entry's checker
(`u1` / `packed` / `u1_hier` / `u2_hier`) on that `(m, d)` and hands the same design to the writer
(`Tools/VedWriteChecked.lean`).  The small examples here are NOT part of the 327 inventory rows.

* POSITIVES (top plus children, with and without the wires constant): the command succeeds; the
  registered theorem has exactly the entry's statement; the standard axioms only; the files it writes
  (SystemVerilog, C++ simulation, JIT wrapper) are byte-identical to the files the original
  `#writeDesign` wrote for the same declaration (the writer is the same function sequence on the
  same IR).
* CONTROLS (through the command's body `run` with a `feed` hook that hands the writer something other
  than the checked design; each is refused at `[written]` and NO file is written): the design of a
  different declaration (checking A while writing B); the checked design with the top module
  tampered; with a child tampered; with a child dropped; with the children reordered; with an extra
  module appended; for the flat kinds a second module.  Checker refusals (`[packed]`, `[multi-output]`)
  also leave no file.
* EARLY `[shape]` REFUSAL of the packed entry: a packed body with a memory or with a submodule instance
  is refused at `[shape]` (`memInstFree`, tested before the artifact / order / proof steps), no file, no
  `ved_*` constant left.
* Not tested and not claimed: that the optimised C++ / JIT or the printed SystemVerilog preserves the
  IR's semantics.
-/

namespace Tests.Ved.WriteCheckedCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST (Design)
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier Tools.VedU1HierEntry Tools.VedU2Hier
open Tools.VedWriteChecked

def wiresC : Array String := #["_gen_x"]

def one (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := ~~~a

def one2 (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := a &&& a

def pk2 (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) := bundle2 (~~~a) b

def pk3 (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) := bundle2 (a &&& (Signal.pure 15#8 : Signal defaultDomain (BitVec 8))) b

@[hardware_module] def wA (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x - y

@[hardware_module] def wB (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  (x ^^^ y) - y

def hpar (a b c : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let p := wA a b
  let q := wA b c
  wB p q

def hpar2 (a b c : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let p := wA a b
  let q := wA b c
  wB p q

@[hardware_module]
def accMod (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (0#8)
    let a := (r : Signal defaultDomain (BitVec 8))
    r <~ a + x
    return a

@[hardware_module]
def parTwo (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let p := accMod a
  let q := accMod b
  p - q + a

@[hardware_module]
def parTwo2 (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let p := accMod a
  let q := accMod b
  p - q + a

#verify_elab_deep accMod

/-! ## Positives: the same declaration through `#writeDesign` (A) and `#ved_write_checked` (B) -/

#writeDesign one ".lake/build/gen/wc/one_a.sv" ".lake/build/gen/wc/one_a_cppsim.h"
#writeDesign pk2 ".lake/build/gen/wc/pk2_a.sv" ".lake/build/gen/wc/pk2_a_cppsim.h" wiresC
#writeDesign hpar ".lake/build/gen/wc/hpar_a.sv" ".lake/build/gen/wc/hpar_a_cppsim.h" wiresC
#writeDesign hpar2 ".lake/build/gen/wc/hpar2_a.sv" ".lake/build/gen/wc/hpar2_a_cppsim.h"
#writeDesign parTwo ".lake/build/gen/wc/parTwo_a.sv" ".lake/build/gen/wc/parTwo_a_cppsim.h" wiresC
#writeDesign parTwo2 ".lake/build/gen/wc/parTwo2_a.sv" ".lake/build/gen/wc/parTwo2_a_cppsim.h"

#guard_msgs (drop info) in
#ved_write_checked u1 one ".lake/build/gen/wc/one_b.sv" ".lake/build/gen/wc/one_b_cppsim.h"
#guard_msgs (drop info) in
#ved_write_checked packed pk2 ".lake/build/gen/wc/pk2_b.sv" ".lake/build/gen/wc/pk2_b_cppsim.h" wiresC
#guard_msgs (drop info) in
#ved_write_checked u1_hier hpar ".lake/build/gen/wc/hpar_b.sv" ".lake/build/gen/wc/hpar_b_cppsim.h" wiresC
#guard_msgs (drop info) in
#ved_write_checked u1_hier hpar2 ".lake/build/gen/wc/hpar2_b.sv" ".lake/build/gen/wc/hpar2_b_cppsim.h"
#guard_msgs (drop info) in
#ved_write_checked u2_hier parTwo ".lake/build/gen/wc/parTwo_b.sv" ".lake/build/gen/wc/parTwo_b_cppsim.h" wiresC
#guard_msgs (drop info) in
#ved_write_checked u2_hier parTwo2 ".lake/build/gen/wc/parTwo2_b.sv" ".lake/build/gen/wc/parTwo2_b_cppsim.h"

def std3 : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def readAll (p : String) : IO String := IO.FS.readFile p

/-- the three files of `#writeDesign` (A) and of `#ved_write_checked` (B) are byte-identical; the
theorem has exactly the entry's statement and the standard axioms -/
def checkPositive (stem : String) (decl thm : Name) (expected : Lean.Expr) : CommandElabM Unit :=
  liftTermElabM do
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: stored type differs"
  let ax ← collectAxioms thm
  unless ax.all (std3.contains ·) do throwError "axioms {ax}"
  let d := ".lake/build/gen/wc/"
  for suf in [".sv", "_cppsim.h", "_jit.c"] do
    let a ← readAll (d ++ stem ++ "_a" ++ suf)
    let b ← readAll (d ++ stem ++ "_b" ++ suf)
    unless a == b do throwError "{decl}: file {suf} differs between #writeDesign and #ved_write_checked"
    if a.isEmpty then throwError "{decl}: empty {suf}"
  logInfo m!"checked-and-written OK {decl}"

def u1Pos (stem : String) (decl : Name) : CommandElabM Unit :=
  let nm := Names.ofBase decl
  checkPositive stem decl nm.thm
    (mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst decl])

def packedPos (stem : String) (decl : Name) (stmtStx : Term) : CommandElabM Unit := do
  let nm := Names.ofBase decl
  let stmt ← liftTermElabM do instantiateMVars (← Term.elabTerm stmtStx none)
  checkPositive stem decl nm.thm
    (mkAppN (Lean.mkConst ``Tools.VedU1Packed.PackedStmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt])

def hierPos (stem : String) (decl : Name) (u2 : Bool) : CommandElabM Unit :=
  let nm := HNames.ofBase decl
  checkPositive stem decl nm.thm
    (mkAppN (Lean.mkConst (if u2 then ``U2HStmt else ``U1HStmt))
      #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, Lean.mkConst decl])

/-- info: checked-and-written OK Tests.Ved.WriteCheckedCheck.one -/
#guard_msgs in
run_cmd u1Pos "one" ``one

/-- info: checked-and-written OK Tests.Ved.WriteCheckedCheck.pk2 -/
#guard_msgs in
run_cmd do packedPos "pk2" ``pk2 (← `(pk2))

/-- info: checked-and-written OK Tests.Ved.WriteCheckedCheck.hpar -/
#guard_msgs in
run_cmd hierPos "hpar" ``hpar false

/-- info: checked-and-written OK Tests.Ved.WriteCheckedCheck.hpar2 -/
#guard_msgs in
run_cmd hierPos "hpar2" ``hpar2 false

/-- info: checked-and-written OK Tests.Ved.WriteCheckedCheck.parTwo -/
#guard_msgs in
run_cmd hierPos "parTwo" ``parTwo true

/-- info: checked-and-written OK Tests.Ved.WriteCheckedCheck.parTwo2 -/
#guard_msgs in
run_cmd hierPos "parTwo2" ``parTwo2 true

/-! ## Controls: the writer is handed something other than the checked design -/

set_option hygiene false in
macro "defOne " n:ident : command => `(def $n (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := ~~~a)
set_option hygiene false in
macro "defPk " n:ident : command => `(def $n (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) := bundle2 (~~~a) b)
set_option hygiene false in
macro "defHier " n:ident : command => `(def $n (a b c : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let p := wA a b
  let q := wA b c
  wB p q)
set_option hygiene false in
macro "defU2 " n:ident : command => `(@[hardware_module] def $n (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let p := accMod a
  let q := accMod b
  p - q + a)

defOne cu1a
defOne cu1b
defOne cu1c
defPk cpka
defPk cpkb
defHier ch1
defHier ch2
defHier ch3
defHier ch4
defHier ch5
defHier ch6
defU2 cu2a
defU2 cu2b

def tamperMod (x : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module := { x with body := x.body.drop 1 }

/-- the checked design with the module at index `i` of the written design transformed -/
def mapMods (f : Nat → Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) (d : Design) : Design :=
  { d with modules := d.modules.mapIdx f }

def ctlPaths (tag : String) : IO (String × String) := do
  let sv := s!".lake/build/gen/wc/ctl_{tag}.sv"
  let h := s!".lake/build/gen/wc/ctl_{tag}_cppsim.h"
  for f in [sv, h, s!".lake/build/gen/wc/ctl_{tag}_jit.c"] do
    if ← System.FilePath.pathExists f then IO.FS.removeFile f
  return (sv, h)

/-- run the command body with a `feed`; it must be refused at `stage` and no file may be written -/
def expectRefused (stage : String) (tag : String) (kind : Kind) (decl : Name)
    (feed : Sparkle.IR.AST.Module → Design → CommandElabM Design := fun m d => pure (hierDesignOf m d)) :
    CommandElabM Unit := do
  let (sv, h) ← ctlPaths tag
  let msgs0 := (← get).messages
  let mut refused := false
  let mut got := ""
  try
    discard <| run kind decl sv h none feed
  catch e =>
    let t ← e.toMessageData.toString
    got := t
    if t.startsWith "VED U1 REFUSED" && (t.splitOn s!"[{stage}]").length > 1 then refused := true
  modify fun s => { s with messages := msgs0 }
  unless refused do throwError "control {tag} ACCEPTED or wrong stage (expected [{stage}]): {got}"
  for f in [sv, h, s!".lake/build/gen/wc/ctl_{tag}_jit.c"] do
    if ← System.FilePath.pathExists f then throwError "control {tag}: file {f} was written"
  logInfo m!"refused [{stage}], no file"

def onTop (f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) (m : Sparkle.IR.AST.Module) (d : Design) : Design :=
  mapMods (fun _ x => if x.name == m.name then f x else x) (hierDesignOf m d)

def onKids (f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) (m : Sparkle.IR.AST.Module) (d : Design) : Design :=
  mapMods (fun _ x => if x.name == m.name then x else f x) (hierDesignOf m d)

def dropKids (m : Sparkle.IR.AST.Module) (d : Design) : Design :=
  let d' := hierDesignOf m d
  { d' with modules := d'.modules.filter (·.name == m.name) }

def reorderMods (m : Sparkle.IR.AST.Module) (d : Design) : Design :=
  let d' := hierDesignOf m d
  { d' with modules := d'.modules.reverse }

def extraMod (m : Sparkle.IR.AST.Module) (d : Design) : Design :=
  let d' := hierDesignOf m d
  { d' with modules := d'.modules ++ [m] }

/-- hand the writer the design of ANOTHER declaration (check A, write B) -/
def otherDesign (other : Name) : Sparkle.IR.AST.Module → Design → CommandElabM Design :=
  fun _ _ => liftTermElabM (Sparkle.Compiler.Elab.synthesizeHierarchical other)

/-- info: refused [written], no file -/
#guard_msgs in
run_cmd expectRefused "written" "u1_swap" .u1 ``cu1a (otherDesign ``cu1b)

/-- info: refused [written], no file -/
#guard_msgs in
run_cmd expectRefused "written" "u1_tamper" .u1 ``cu1b (fun m d => pure (onTop tamperMod m d))

/-- info: refused [written], no file -/
#guard_msgs in
run_cmd expectRefused "written" "u1_extra" .u1 ``cu1c (fun m d => pure (extraMod m d))

/-- info: refused [written], no file -/
#guard_msgs in
run_cmd expectRefused "written" "pk_swap" .packed ``cpka (otherDesign ``pk2)

/-- info: refused [written], no file -/
#guard_msgs in
run_cmd expectRefused "written" "pk_tamper" .packed ``cpkb (fun m d => pure (onTop tamperMod m d))

/-- info: refused [written], no file -/
#guard_msgs in
run_cmd expectRefused "written" "h_swap" .u1Hier ``ch1 (otherDesign ``hpar)

/-- info: refused [written], no file -/
#guard_msgs in
run_cmd expectRefused "written" "h_swap_other_shape" .u1Hier ``ch2 (otherDesign ``parTwo)

/-- info: refused [written], no file -/
#guard_msgs in
run_cmd expectRefused "written" "h_top" .u1Hier ``ch3 (fun m d => pure (onTop tamperMod m d))

/-- info: refused [written], no file -/
#guard_msgs in
run_cmd expectRefused "written" "h_child" .u1Hier ``ch4 (fun m d => pure (onKids tamperMod m d))

/-- info: refused [written], no file -/
#guard_msgs in
run_cmd expectRefused "written" "h_drop" .u1Hier ``ch5 (fun m d => pure (dropKids m d))

/-- info: refused [written], no file -/
#guard_msgs in
run_cmd expectRefused "written" "h_reorder" .u1Hier ``ch6 (fun m d => pure (reorderMods m d))

/-- info: refused [written], no file -/
#guard_msgs in
run_cmd expectRefused "written" "u2_swap" .u2Hier ``cu2a (otherDesign ``parTwo)

/-- info: refused [written], no file -/
#guard_msgs in
run_cmd expectRefused "written" "u2_child" .u2Hier ``cu2b (fun m d => pure (onKids tamperMod m d))

/-! ## Checker refusals also leave no file -/

def pkWrong (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) := bundle2 (~~~a) b

/-- info: refused [packed], no file -/
#guard_msgs in
run_cmd expectRefused "packed" "ck_packed" .packed ``one

/-- info: refused [multi-output], no file -/
#guard_msgs in
run_cmd expectRefused "multi-output" "ck_hier_pk" .u1Hier ``pkWrong

/-- info: refused [multi-output], no file -/
#guard_msgs in
run_cmd expectRefused "multi-output" "ck_u1_pk" .u1 ``pkWrong

/-! ## Early `[shape]` refusal (a memory / an instance in a packed body; `memInstFree` is tested before the
artifact / order / proof steps, so the declaration is refused at `[shape]`, not later) -/

def pkMem (wa : Signal defaultDomain (BitVec 4)) (wd : Signal defaultDomain (BitVec 8))
    (we : Signal defaultDomain Bool) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) :=
  bundle2 (Signal.memory wa wd we b) b

def pkInst (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) := bundle2 (wA a a) b

/-- info: refused [shape], no file -/
#guard_msgs in
run_cmd expectRefused "shape" "ck_pk_mem" .packed ``pkMem

/-- info: refused [shape], no file -/
#guard_msgs in
run_cmd expectRefused "shape" "ck_pk_inst" .packed ``pkInst

/-- info: clean -/
#guard_msgs in
run_cmd do
  for d in [``pkMem, ``pkInst] do
    for n in [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_u1] do
      if (← getEnv).contains (d ++ n) then throwError "left behind: {d ++ n}"
  logInfo "clean"

end Tests.Ved.WriteCheckedCheck
