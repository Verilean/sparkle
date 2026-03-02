import Lake
open Lake DSL

package «sparkle» where

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "main"

-- C FFI library for Signal memoization barriers (defeats Lean 4.28 LICM)
extern_lib «sparkle_barrier» pkg := do
  let srcFile := pkg.dir / "c_src" / "sparkle_barrier.c"
  let oFile := pkg.buildDir / "c_src" / "sparkle_barrier.o"
  let srcJob ← inputTextFile srcFile
  let oJob ← buildLeanO oFile srcJob (weakArgs := #["-O2"])
  buildStaticLib (pkg.buildDir / "c_src" / nameToStaticLib "sparkle_barrier") #[oJob]

-- C FFI library for JIT dlopen/dlsym wrappers
extern_lib «sparkle_jit» pkg := do
  let srcFile := pkg.dir / "c_src" / "sparkle_jit.c"
  let oFile := pkg.buildDir / "c_src" / "sparkle_jit.o"
  let srcJob ← inputTextFile srcFile
  let oJob ← buildLeanO oFile srcJob (weakArgs := #["-O2"])
  buildStaticLib (pkg.buildDir / "c_src" / nameToStaticLib "sparkle_jit") #[oJob]

lean_lib «Sparkle» where

lean_lib «Examples.BitNet» where
  roots := #[`Examples.BitNet]

lean_lib «Examples.RV32» where
  roots := #[`Examples.RV32]

lean_lib «Examples.YOLOv8» where
  roots := #[`Examples.YOLOv8]

lean_lib «Tests» where
  -- Test circuits library

@[default_target]
lean_exe «sparkle» where
  root := `Main

lean_exe «verilog-tests» where
  root := `Tests.VerilogTests
  supportInterpreter := true

lean_exe «sparkle-bitnet-verilog-dump» where
  root := `Tests.BitNet.SparkleBitNetVerilogDump

lean_exe «sparkle-rv32-sim» where
  root := `Tests.RV32.SimTest

lean_exe «sparkle-rv32-min» where
  root := `Tests.RV32.MinTest

lean_exe «rv32-flow-test» where
  root := `Tests.RV32.TestFlowMain

lean_exe «rv32-lean-sim-runner» where
  root := `Tests.RV32.LeanSimRunner

lean_exe «rv32-jit-test» where
  root := `Tests.RV32.JITTest

@[test_driver]
lean_exe «test» where
  root := `Tests.AllTests
  supportInterpreter := true
