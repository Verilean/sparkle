import Lake
open Lake DSL

package «sparkle-fpu» where
  version := v!"0.1.0"

-- Depend on Sparkle HDL
require sparkle from git
  "https://github.com/Verilean/sparkle.git" @ "main"

@[default_target]
lean_lib «FPU» where
  roots := #[`FPU]
  srcDir := "."

lean_exe «fpu-sim-test» where
  root := `FPU.SimTest
  srcDir := "."
