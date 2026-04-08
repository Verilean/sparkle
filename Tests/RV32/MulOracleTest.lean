/-
  MulOracle Test — OracleSpec framework validation

  Tests the generic oracle-driven reverse synthesis pipeline:
  1. OracleReduction type class instance ("pcpi_mul")
  2. Register pattern matching and resolution
  3. IR reduction (dead wire elimination)
  4. Oracle creation from type class

  Also validates the IR reduction effect on LiteX PicoRV32 SoC.
-/

import Sparkle.Core.JIT
import Sparkle.Core.OracleSpec
import Sparkle.Core.MulOracle  -- provides instance : OracleReduction "pcpi_mul"
import Tools.SVParser.Lower
import Sparkle.Backend.CppSim

open Sparkle.Core.JIT
open Sparkle.Core.OracleSpec
open Tools.SVParser.Lower

def main : IO Unit := do
  IO.println "=== OracleSpec Framework Test ==="

  -- Check prerequisites
  let picorv32Exists ← System.FilePath.pathExists "/tmp/picorv32.v"
  if !picorv32Exists then
    IO.println "Downloading picorv32.v..."
    let r ← IO.Process.output {
      cmd := "curl", args := #["-sL", "-o", "/tmp/picorv32.v",
        "https://raw.githubusercontent.com/YosysHQ/picorv32/main/picorv32.v"]
    }
    if r.exitCode != 0 then
      IO.println "FAIL: could not download picorv32.v"; return

  let socExists ← System.FilePath.pathExists "/tmp/picorv32_soc_m.v"
  if !socExists then
    IO.println "SKIP: /tmp/picorv32_soc_m.v not found"; return

  -- Phase 1: Parse SoC
  IO.print "  Phase 1: Parse M-ext SoC... "
  let soc ← IO.FS.readFile "/tmp/picorv32_soc_m.v"
  let cpu ← IO.FS.readFile "/tmp/picorv32.v"
  match Tools.SVParser.Lower.parseAndLowerFlat (soc ++ "\n" ++ cpu) with
  | Except.error e => IO.println s!"FAIL: {e}"; return
  | Except.ok design =>

  match design.modules.head? with
  | none => IO.println "FAIL (no modules)"; return
  | some m =>
  IO.println s!"OK ({m.body.length} stmts)"

  -- Phase 2: IR reduction via OracleReduction "pcpi_mul"
  IO.print "  Phase 2: IR reduction... "
  let reducedBody := reduceIR "pcpi_mul" m.body
  let removed := m.body.length - reducedBody.length
  IO.println s!"OK (removed {removed} stmts, {m.body.length} → {reducedBody.length})"

  -- Phase 3: Compile JIT (original, for oracle resolution test)
  IO.print "  Phase 3: JIT compile (original)... "
  let cppCode := Sparkle.Backend.CppSim.toCppSimJIT design
  IO.FS.writeFile "/tmp/picorv32_oraclespec_jit.cpp" cppCode
  let h ← JIT.compileAndLoad "/tmp/picorv32_oraclespec_jit.cpp"
  IO.println "OK"

  -- Phase 4: Resolve OracleReduction "pcpi_mul" against JIT
  IO.print "  Phase 4: Resolve oracle... "
  match ← resolve "pcpi_mul" h with
  | none => IO.println "FAIL (register resolution failed)"
  | some resolved =>
    IO.println s!"OK ({resolved.regIndices.size} registers resolved)"
    let mut idx : Nat := 0
    let regs := (OracleReduction.registers (tag := "pcpi_mul"))
    for role in regs do
      if h2 : idx < resolved.regIndices.size then
        IO.println s!"    {role.role} → idx {resolved.regIndices[idx]}"
      idx := idx + 1

    -- Phase 5: Create oracle from type class
    IO.print "  Phase 5: Create oracle... "
    let (_, stateRef) ← mkOracle "pcpi_mul" resolved
    let st ← stateRef.get
    IO.println s!"OK (triggers={st.triggerCount}, skipped={st.totalSkipped})"

  IO.println "\n=== OracleSpec Framework Test Complete ==="
  JIT.destroy h
