import Lake
open Lake DSL

package «sparkle» where
  -- add package configuration options here

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "main"

lean_lib «Sparkle» where
  -- add library configuration options here

lean_lib «Examples.BitNet» where
  roots := #[`Examples.BitNet]

lean_lib «Examples.RV32» where
  roots := #[`Examples.RV32]

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

@[test_driver]
lean_exe «test» where
  root := `Tests.AllTests
  supportInterpreter := true
