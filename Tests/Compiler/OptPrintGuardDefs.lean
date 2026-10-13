import Sparkle.IR.RefineCheck
import Sparkle.IR.ZeroWidth
import Sparkle.Backend.VerilogDesign

/-! # The two candidate guards, computed OUTSIDE the compiler (round par/b-19)

Pure helper definitions for `OptPrintSourceTest`, `OptPrintCensusTest` and
`scripts/shipping-coverage/optprint_sim.lean`. Nothing here is used by the
compiler and nothing is proved. No Signal-valued definition lives in this
file (it is imported by the census, whose population is "the Signal-valued
definitions of the imported `IP` / `Examples` / `Tests` modules": this file
must not add one).

* `guardedOptimize` — `checkedOptimize` with the candidate guard of
  `docs/parallel/A-leaf-entry-2.md` §3.3 in its instance-free
  assign + register branch (`Sparkle/IR/RefineCheck.lean` 385–386):
  `if refineCheck m o && printOk o then o else m`. Every other branch is
  `checkedOptimize` itself.
* `mergeGuarded` — `mergeChecked` with the candidate conjunct of §1.4 of the
  same note: an accepted merge of a body that is not assignment-only must
  not be assignment-only.
* `guardedArtifact` / `guardedText` — `designArtifact` /
  `toVerilogDesignChecked` (`Sparkle/Backend/VerilogDesign.lean` 25–32) with
  `guardedOptimize` in place of `checkedOptimize`.
* `shippedDesign` — what `synthesizeCombinationalWith` (`Elab.lean`
  5515–5529) and `synthesizeHierarchical` (9032–9035) do to the entry's
  result, without the name validation and without the `SPARKLE_NO_REGDEDUP`
  switch, keeping the top module BEFORE the merge.

WRITTEN, NOT BUILT. -/
namespace Tests.Compiler.OptPrintGuardDefs

abbrev Mod := Sparkle.IR.AST.Module
abbrev Dsn := Sparkle.IR.AST.Design

def tf (b : Bool) : String := if b then "T" else "F"

def isInstStmt : Sparkle.IR.AST.Stmt → Bool
  | Sparkle.IR.AST.Stmt.inst .. => true
  | _ => false

def isRegStmt : Sparkle.IR.AST.Stmt → Bool
  | Sparkle.IR.AST.Stmt.register .. => true
  | _ => false

/-- No instance statement. -/
def instFree (m : Mod) : Bool := !(m.body.any isInstStmt)

/-- The branch of `checkedOptimize` a module takes, without evaluating the
hierarchical gates: `simple` (optCheck), `seq` (refineCheck — the branch the
candidate guard is for), `other` (instance-free, not assign + register: the
optimizer unchecked), `inst` (an instance: the hierarchical branches). -/
def branchOf (m : Mod) : String :=
  if Sparkle.IR.OptCheck.simpleBody m then "simple"
  else if m.body.all Sparkle.IR.OptCheck.seqStmtOk then "seq"
  else if instFree m then "other"
  else "inst"

/-- `checkedOptimize` with the candidate print guard in the `seq` branch. -/
def guardedOptimize (m : Mod) : Mod :=
  let o := Sparkle.IR.Optimize.optimizeModule m
  if Sparkle.IR.OptCheck.simpleBody m then Sparkle.IR.OptCheck.checkedOptimize m
  else if m.body.all Sparkle.IR.OptCheck.seqStmtOk then
    if Sparkle.IR.RefineCheck.refineCheck m o && Sparkle.IR.PrintGuard.printOk o then o else m
  else Sparkle.IR.OptCheck.checkedOptimize m

/-- What the census reads of one module. -/
structure OptObs where
  branch : String
  /-- the optimizer's candidate differs from the module -/
  differs : Bool
  /-- `refineCheck m (optimizeModule m)` -/
  rc : Bool
  /-- `printOk m` -/
  pm : Bool
  /-- `printOk (optimizeModule m)` -/
  po : Bool
  /-- `checkedOptimize m == m` -/
  kept : Bool
  /-- `printOk (checkedOptimize m)` -/
  pk : Bool
  /-- `guardedOptimize m == checkedOptimize m` -/
  sameUnderGuard : Bool

def optObs (m : Mod) : OptObs :=
  let o := Sparkle.IR.Optimize.optimizeModule m
  let k := Sparkle.IR.OptCheck.checkedOptimize m
  let g := guardedOptimize m
  { branch := branchOf m
    differs := o != m
    rc := Sparkle.IR.RefineCheck.refineCheck m o
    pm := Sparkle.IR.PrintGuard.printOk m
    po := Sparkle.IR.PrintGuard.printOk o
    kept := k == m
    pk := Sparkle.IR.PrintGuard.printOk k
    sameUnderGuard := g == k }

/-- The modules the design writer would print under the guard. -/
def guardedArtifact (d : Dsn) : List Mod :=
  d.modules.map fun m => if m.name == d.topModule then guardedOptimize m else m

/-- The text the design writer would print under the guard. -/
def guardedText (d : Dsn) : String :=
  String.intercalate "\n" ((guardedArtifact d).map Sparkle.Backend.Verilog.emitModule)

/-- `mergeChecked` with the candidate conjunct (innermost, as in the note). -/
def mergeGuarded (m : Mod) : Mod :=
  let r := Sparkle.IR.RegDedup.mergeDuplicates m
  if m.body.all Sparkle.IR.RegDedup.isAssign then r
  else if Sparkle.IR.RefineCheck.refineCheck m r &&
      (Sparkle.IR.RefineCheck.masksKept m r &&
        (Sparkle.IR.PrintGuard.printOk r && !(r.body.all Sparkle.IR.RegDedup.isAssign))) then r
  else m

/-- What the census reads of one merge. -/
structure MergeObs where
  /-- the body is not assignment-only (the guarded branch of `mergeChecked`) -/
  nonAssign : Bool
  /-- `mergeDuplicates m != m` -/
  changed : Bool
  /-- the present condition accepts the merge -/
  accepted : Bool
  /-- the candidate conjunct is the one that fails: accepted today, and the
  merged body is assignment-only -/
  fires : Bool

def mergeObs (m : Mod) : MergeObs :=
  let r := Sparkle.IR.RegDedup.mergeDuplicates m
  let na : Bool := !(m.body.all Sparkle.IR.RegDedup.isAssign)
  let acc : Bool := na && (Sparkle.IR.RefineCheck.refineCheck m r &&
    (Sparkle.IR.RefineCheck.masksKept m r && Sparkle.IR.PrintGuard.printOk r))
  { nonAssign := na
    changed := r != m
    accepted := acc
    fires := acc && r.body.all Sparkle.IR.RegDedup.isAssign }

/-- The entry's result as the commands ship it. -/
structure Post where
  /-- the top after the zero-width cleanup, BEFORE the merge -/
  pre : Mod
  /-- the top after the checked merge (the endpoints' `b`) -/
  top : Mod
  /-- the design `synthesizeHierarchical` returns (name validation apart) -/
  design : Dsn

def shippedDesign (r : Mod × Dsn) : Post :=
  let m := r.1
  let onTop (f : Mod → Mod) (d : Dsn) : Dsn :=
    { d with modules := d.modules.map fun x => if x.name == m.name then f x else x }
  let m0 := Sparkle.IR.ZeroWidth.dropZeroWidthModule m
  let m1 := Sparkle.IR.RefineCheck.mergeChecked m0
  let d1 := onTop Sparkle.IR.RefineCheck.mergeChecked
    (onTop Sparkle.IR.ZeroWidth.dropZeroWidthModule r.2)
  let design := if d1.modules.any (fun x => x.name == m1.name) then d1 else d1.addModule m1
  { pre := m0, top := m1, design := design }

def clip (k : Nat) (s : String) : String := String.ofList (s.toList.take k)

end Tests.Compiler.OptPrintGuardDefs
