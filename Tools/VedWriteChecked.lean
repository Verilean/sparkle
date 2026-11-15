import Lean
import Sparkle.Compiler.Elab
import Tools.VedStrictAudit
import Tools.VedU1Entry
import Tools.VedU1PackedEntry
import Tools.VedU1HierEntry
import Tools.VedU2HierRegEntry
import Tools.VedU2HierEntry

/-!
# `#ved_write_checked`: check ONE synthesis result, then write exactly that value

`#writeDesign decl "x.sv" "x_cppsim.h" [wires]` runs `synthesizeHierarchical decl` and writes the
SystemVerilog / C++ / JIT files from that design.  The `#ved_*_write` adapters of
`Tools/VedWriteForms.lean` run an entry with its OWN synthesis and write nothing, so they say
nothing about what a `#writeDesign` writes.  This command connects the checker to the writer:

```
#ved_write_checked KIND decl "x.sv" "x_cppsim.h" [wires]      KIND ∈ u1 | packed | u1_hier | u2_hier

  (m, d) := synthesizeCombinational decl            -- ONCE
  thm    := checker KIND decl m d                   -- the entry's checker on that very (m, d)
  design := d plus m if absent                      -- what `synthesizeHierarchical` does
  guard  : `design` (the value handed to the writer) is anchored to the checked artifact
  writer : runDesignDRC design; toVerilogDesign design; optimizeDesign / toCDesign / toCJIT design
```

There is no synthesis after the check.  The guard compares the design the writer is about to receive
with the values the theorem is about: `decl.ved_mod` (and, for the hierarchical kinds,
`decl.ved_design`) read back from the environment with `evalModule` / `evalDesign`, using `==` on the
module bodies.  A design that differs in any module (top or child), in the module list, or in the top
name is refused at `[written]` before anything is written.  `u1` / `packed` kinds have no child
modules in the statement: the design must be exactly `[m]`.

The writer part is the body of `writeDesignCore` of `Sparkle/Compiler/Elab.lean` (private there; the
functions it calls are public and are the ones called here).  Whether the files equal what
`#writeDesign` writes is tested by byte comparison in `Tests/Ved/WriteCheckedCheck.lean`.

What this does NOT say: that the optimised C++ / JIT or the printed SystemVerilog preserves the IR's
semantics (no proof about `optimizeDesign`, `toCDesign`, `toVerilogDesign`).  It says: the IR design
those functions are given is the IR the strict theorem is about.
-/

namespace Tools.VedWriteChecked

open Lean Elab Command Term Meta
open Sparkle.IR.AST (Design)

inductive Kind | u1 | packed | u1Hier | u2Hier
  deriving BEq, Repr

def Kind.hier : Kind → Bool
  | .u1Hier | .u2Hier => true
  | _ => false

/-- evaluate an `Array String` constant (as `#writeDesign` does for its wires argument) -/
private unsafe def evalStringArrayImpl (name : Name) : TermElabM (Array String) :=
  Lean.Meta.evalExpr (Array String)
    (mkApp (mkConst ``Array [.zero]) (mkConst ``String []))
    (mkConst name [])

@[implemented_by evalStringArrayImpl]
private opaque evalStringArray (name : Name) : TermElabM (Array String)

/-- `synthesizeHierarchical`'s design from the pair `synthesizeCombinational` returned -/
def hierDesignOf (m : Sparkle.IR.AST.Module) (d : Design) : Design :=
  if d.modules.any (·.name == m.name) then d else d.addModule m

/-- the writer: the body of `writeDesignCore` after its synthesis -/
def writeDesignOn (design : Design) (svPath cppPath : String)
    (observableWires : Option (List String)) : TermElabM Unit := do
  Sparkle.Compiler.Elab.runDesignDRC design
  if let some svDir := (System.FilePath.mk svPath).parent then
    IO.FS.createDirAll svDir
  if let some cppDir := (System.FilePath.mk cppPath).parent then
    IO.FS.createDirAll cppDir
  let verilog := Sparkle.Backend.Verilog.toVerilogDesign design
  IO.FS.writeFile svPath verilog
  IO.println s!"Written {design.modules.length} modules to {svPath}"
  let optimized := Sparkle.IR.Optimize.optimizeDesign design
  let cSrc := Sparkle.Backend.CSim.toCDesign optimized
  IO.FS.writeFile cppPath cSrc
  IO.println s!"Written C simulation ({optimized.modules.length} modules) to {cppPath}"
  let jitOptimized := Sparkle.IR.Optimize.optimizeDesign design observableWires
  let jitC := Sparkle.Backend.CSim.toCJIT jitOptimized observableWires
  let jitPath := (cppPath.replace "_cppsim.h" "_jit.c").replace "_jit.c" "_jit.c"
  IO.FS.writeFile jitPath jitC
  IO.println s!"Written JIT wrapper to {jitPath}"

private def refuseWritten {α} (decl : Name) (msg : MessageData) : CommandElabM α :=
  throwError m!"VED U1 REFUSED {decl} [written]: {msg}"

/-- the design the writer is about to receive is the checked artifact: `decl.ved_mod` (and
`decl.ved_design` for the hierarchical kinds) read back from the environment -/
def guardWritten (kind : Kind) (decl : Name) (written : Design) : CommandElabM Unit := do
  let env ← getEnv
  let base := decl
  let some (.defnInfo dm) := env.find? (base ++ `ved_mod)
    | refuseWritten decl m!"{base ++ `ved_mod} is missing (nothing was checked)"
  let vm ← liftTermElabM <| Tools.VedU1Entry.evalModule dm.value
  if kind.hier then
    let some (.defnInfo dd) := env.find? (base ++ `ved_design)
      | refuseWritten decl m!"{base ++ `ved_design} is missing (nothing was checked)"
    let vd ← liftTermElabM <| Tools.VedU1HierEntry.evalDesign dd.value
    let expected := hierDesignOf vm vd
    unless written.topModule == expected.topModule do
      refuseWritten decl m!"top name {written.topModule} differs from the checked design's {expected.topModule}"
    unless written.modules.map (·.name) == expected.modules.map (·.name) do
      refuseWritten decl
        m!"module list {written.modules.map (·.name)} differs from the checked design's {expected.modules.map (·.name)}"
    for (w, e) in written.modules.zip expected.modules do
      unless w == e do
        refuseWritten decl m!"module {w.name} differs from the checked one"
  else
    unless written.modules.length == 1 do
      refuseWritten decl
        m!"the design has {written.modules.length} modules; the statement covers exactly the one module {vm.name}"
    for w in written.modules do
      unless w == vm do refuseWritten decl m!"module {w.name} differs from the checked {vm.name}"

/-- run the entry's checker on the given `(m, d)`; the preamble (domain / table refusals) is the
entry's, the checker is the entry's own function. -/
def checkOn (kind : Kind) (decl : Name) (m : Sparkle.IR.AST.Module) (d : Design) : CommandElabM Name := do
  match kind with
  | .u1 => liftTermElabM do
    let (thm, _) ← do
      let (stmt, nDom, names) ← Tools.VedU1Entry.stmtOf decl
      Tools.VedU1Entry.vedU1EntryOn decl stmt nDom names m
    return thm
  | .packed => liftTermElabM do
    let (stmt, _, tbl) ← Tools.VedU1PackedEntry.packedStmtOf decl
    Tools.VedU1PackedEntry.checkPackedE decl stmt tbl tbl.out.slices m .generated
  | .u1Hier => liftTermElabM do
    let (stmt, nDom) ← try Tools.VedU1Contract.specialiseDomain decl
      catch e => Tools.VedU1Entry.refuse decl "table" e.toMessageData
    let (thm, _, _) ← Tools.VedU1HierEntry.checkU1H decl stmt nDom m d
    return thm
  | .u2Hier =>
    let (stmt, nDom) ← liftTermElabM <| try Tools.VedU1Contract.specialiseDomain decl
      catch e => Tools.VedU1Entry.refuse decl "table" e.toMessageData
    if (Tools.VedU1Contract.regsOf m.body).isEmpty then
      let (thm, _, _) ← liftTermElabM (Tools.VedU2HierEntry.checkU2H decl stmt nDom m d)
      return thm
    else
      let (thm, _, _) ← Tools.VedU2HierRegEntry.checkU2HR decl stmt nDom m d
      return thm

/-- the entries' refusals before the synthesis (one-output / packed table) -/
def preamble (kind : Kind) (decl : Name) : CommandElabM Unit := liftTermElabM do
  match kind with
  | .u1 => discard <| Tools.VedU1Entry.stmtOf decl
  | .packed => discard <| Tools.VedU1PackedEntry.packedStmtOf decl
  | .u1Hier | .u2Hier =>
    let (stmt, _) ← try Tools.VedU1Contract.specialiseDomain decl
      catch e => Tools.VedU1Entry.refuse decl "table" e.toMessageData
    let tbl ← try Tools.VedU1Contract.readTableOfType decl (← inferType stmt)
      catch e => Tools.VedU1Entry.refuse decl "table" e.toMessageData
    unless tbl.out.flat.length == 1 do
      Tools.VedU1Entry.refuse decl "multi-output"
        m!"{tbl.out.flat.length} output projections (multi-output: H3), refused (one output)"

/-- The command's body.  `feed` receives the checked `(m, d)` and returns the design handed to the
writer; the command uses `fun m d => pure (hierDesignOf m d)`, tests pass a function that swaps or
tampers (the guard must then refuse). Returns the design that was written. -/
def run (kind : Kind) (decl : Name) (svPath cppPath : String) (wires : Option Name)
    (feed : Sparkle.IR.AST.Module → Design → CommandElabM Design := fun m d => pure (hierDesignOf m d)) :
    CommandElabM Design := do
  let wiresArr ← match wires with
    | some w => pure (some (← liftTermElabM (evalStringArray w)).toList)
    | none => pure none
  preamble kind decl
  -- ONE synthesis; its result is what is checked and what is written
  let (m, d) ← liftTermElabM <| try Sparkle.Compiler.Elab.synthesizeCombinational decl
    catch e => Tools.VedU1Entry.refuse decl "synthesis" e.toMessageData
  let thm ← checkOn kind decl m d
  let r ← liftTermElabM <| Tools.VedStrictAudit.strictAudit thm
  let design ← feed m d
  guardWritten kind decl design
  liftTermElabM <| writeDesignOn design svPath cppPath wiresArr
  logInfo m!"VED WRITE CHECKED OK {thm}: {Tools.VedStrictAudit.showNames r.axioms}; wrote {design.modules.map (·.name)}"
  return design

private def kindOf (k : Syntax) : CommandElabM Kind :=
  match k.getId.toString with
  | "u1" => pure .u1
  | "packed" => pure .packed
  | "u1_hier" => pure .u1Hier
  | "u2_hier" => pure .u2Hier
  | s => throwErrorAt k "unknown kind {s} (u1 | packed | u1_hier | u2_hier)"

elab "#ved_write_checked " k:ident id:ident svPath:str cppPath:str : command => do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverload id
  discard <| run (← kindOf k) decl svPath.getString cppPath.getString none

elab "#ved_write_checked " k:ident id:ident svPath:str cppPath:str wiresId:ident : command => do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverload id
  let w ← Command.liftCoreM <| realizeGlobalConstNoOverload wiresId
  discard <| run (← kindOf k) decl svPath.getString cppPath.getString (some w)

end Tools.VedWriteChecked
