/-
  Property checking commands for Signal-DSL circuits.

  A PROPERTY is an ordinary circuit that returns `Signal dom Bool`: a
  monitor that instantiates the design under test, watches it, and outputs
  `true` while everything is fine.  Its inputs are the free inputs of the
  check — the solver chooses them.

    def counterOk (en : Signal dom Bool) : Signal dom Bool :=
      (fun c => c.toNat < 10) <$> counter10 en   -- or any Bool-valued circuit

    #bmc counterOk 20          -- no violation in cycles 0..20 from reset
    #kinduction counterOk 1    -- no violation in ANY cycle (k-induction)
    #writeSvaChecker counterOk "counter_ok.sv"   -- the monitor + `assert property`

  A violation is a build error showing the trace (one column per cycle)
  and the path of a VCD waveform.  `expect violation` / `expect failure`
  invert that for tests and tutorials.  Without z3 (`SPARKLE_Z3` or `z3`
  on PATH) the commands only write the query and warn.
-/
import Sparkle.Compiler.Elab
import Sparkle.Verification.Bmc

namespace Sparkle.Verification.BmcCommand

open Lean Lean.Elab Lean.Elab.Command Lean.Meta
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Verification.Bmc

/-- Turn a synthesized monitor into a property module: its single 1-bit
    output becomes the assertion. -/
def propertyModule (m : Sparkle.IR.AST.Module) : Except String Sparkle.IR.AST.Module :=
  match m.outputs with
  | [out] =>
    if out.ty.bitWidth? == some 1 then
      -- 0-width wires (the `Unit` slot of `circuit do` state) are not
      -- valid SMT bit-vectors; drop them.  The full optimizer is not run,
      -- so user-named wires stay visible in traces.
      .ok { Sparkle.IR.Optimize.eliminateZeroBits m with
            assertions := [(out.name, .ref out.name)] }
    else .error s!"a property must return `Signal dom Bool`; `{m.name}` returns {out.ty}"
  | outs => .error s!"a property must return one `Signal dom Bool`; `{m.name}` has {outs.length} outputs"

def synthesizeProperty (declName : Name) : MetaM Sparkle.IR.AST.Module := do
  let (module, _) ← Sparkle.Compiler.Elab.synthesizeCombinational declName
  match propertyModule module with
  | .ok m => pure m
  | .error e => throwError e

private def tagOf (declName : Name) : String :=
  (toString declName).map fun c => if c.isAlphanum || c == '_' then c else '_'

private def traceReport (m : Sparkle.IR.AST.Module) (trace : Trace) (tag : String) : MetaM String := do
  let path ← writeVcd m trace tag
  return s!"{renderTrace m trace}\n  waveform: {path}"

/-- `#bmc f k` — check the property `f` for cycles 0..k from reset. -/
syntax (name := bmcCmd) "#bmc " ident num (&" expect " &"violation")? : command

@[command_elab bmcCmd] def elabBmc : CommandElab := fun stx => do
  let id : Ident := ⟨stx[1]⟩
  let k := stx[2].toNat
  let expectViolation := !stx[3].isNone
  let declName ← liftCoreM (resolveGlobalConstNoOverload id)
  liftTermElabM do
    let m ← synthesizeProperty declName
    let tag := tagOf declName
    match ← checkBmc m k tag with
    | .holds k =>
      if expectViolation then
        throwError "#bmc {declName}: expected a violation, but the property holds in cycles 0..{k}"
      logInfo m!"#bmc {declName}: z3 finds no violation in cycles 0..{k} (bounded; use #kinduction for all cycles)"
    | .violated c _ trace =>
      let report ← traceReport m trace tag
      if expectViolation then
        logInfo m!"#bmc {declName}: violated at cycle {c} (as expected)\n{report}"
      else
        throwError "#bmc {declName}: the property is violated at cycle {c}\n{report}"
    | .noSolver path =>
      logWarning m!"#bmc {declName}: z3 not found (set SPARKLE_Z3 or put z3 on PATH); query written to {path} — NOT checked"
    | .unknown why => throwError "#bmc {declName}: {why}"
    | .proved _ | .notInductive .. => throwError "#bmc {declName}: unexpected verdict"

/-- `#kinduction f k` — prove the property `f` for EVERY cycle by
    k-induction (base: cycles 0..k-1 from reset; step: k good cycles from
    any state are followed by a good one). -/
syntax (name := kinductionCmd) "#kinduction " ident num (&" expect " &"failure")? : command

@[command_elab kinductionCmd] def elabKinduction : CommandElab := fun stx => do
  let id : Ident := ⟨stx[1]⟩
  let k := stx[2].toNat
  let expectFailure := !stx[3].isNone
  let declName ← liftCoreM (resolveGlobalConstNoOverload id)
  liftTermElabM do
    let m ← synthesizeProperty declName
    let tag := tagOf declName
    match ← checkInduction m k tag with
    | .proved k =>
      if expectFailure then
        throwError "#kinduction {declName}: expected the induction to fail, but the property is proved (k = {k})"
      logInfo m!"#kinduction {declName}: holds in every cycle (k-induction, k = {k}; checked by z3, not by the Lean kernel)"
    | .notInductive k _ trace =>
      let report ← traceReport m trace s!"{tag}.step"
      let msg := m!"the property is not {k}-inductive. No violation within {k - 1} cycle(s) of reset, but from the state below — which may be unreachable — {k} good cycle(s) are followed by a bad one. Raise k, or strengthen the property so it excludes that state.\n{report}"
      if expectFailure then logInfo m!"#kinduction {declName}: {msg}"
      else throwError "#kinduction {declName}: {msg}"
    | .violated c _ trace =>
      let report ← traceReport m trace tag
      throwError "#kinduction {declName}: the property is violated at cycle {c} (from reset)\n{report}"
    | .noSolver path =>
      logWarning m!"#kinduction {declName}: z3 not found (set SPARKLE_Z3 or put z3 on PATH); query written to {path} — NOT checked"
    | .unknown why => throwError "#kinduction {declName}: {why}"
    | .holds _ => throwError "#kinduction {declName}: unexpected verdict"

/-- The monitor as SystemVerilog with a concurrent assertion on its
    output, for use in another simulator or formal tool. -/
def svaChecker (m : Sparkle.IR.AST.Module) : String :=
  let optimized := Sparkle.IR.Optimize.optimizeModule m
  let sv := Sparkle.Backend.Verilog.toVerilog optimized
  let out := (m.outputs.head?.map (·.name)).getD "out"
  let hasClk := m.inputs.any (·.name == "clk")
  let hasRst := m.inputs.any (·.name == "rst")
  let check :=
    if hasClk then
      let disable := if hasRst then " disable iff (rst)" else ""
      s!"    assert property (@(posedge clk){disable} {out})\n" ++
      s!"      else $error(\"{m.name}: property violated\");\n"
    else
      s!"    always_comb assert ({out}) else $error(\"{m.name}: property violated\");\n"
  let block := "\n`ifndef SYNTHESIS\n" ++
    s!"    // Property: `{out}` must be 1 in every cycle.\n" ++ check ++ "`endif\n\n"
  match (sv.splitOn "endmodule").reverse with
  | last :: rest => "endmodule".intercalate rest.reverse ++ block ++ "endmodule" ++ last
  | [] => sv

/-- `#writeSvaChecker f "path.sv"` — write the property `f` as a
    SystemVerilog checker module. -/
elab "#writeSvaChecker " id:ident path:str : command => do
  let declName ← liftCoreM (resolveGlobalConstNoOverload id)
  liftTermElabM do
    let m ← synthesizeProperty declName
    let p := path.getString
    if let some dir := (System.FilePath.mk p).parent then
      IO.FS.createDirAll dir
    IO.FS.writeFile p (svaChecker m)
    IO.println s!"Written SVA checker to {p}"

end Sparkle.Verification.BmcCommand
