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

lean_lib «IP.BitNet» where
  roots := #[`IP.BitNet]

lean_lib «IP.Drone» where
  roots := #[`IP.Drone]

lean_lib «IP.Humanoid» where
  roots := #[`IP.Humanoid]

lean_lib «IP.RV32» where
  roots := #[`IP.RV32]

lean_lib «IP.YOLOv8» where
  roots := #[`IP.YOLOv8]

lean_lib «IP.Arbiter» where
  roots := #[`IP.Arbiter]

lean_lib «Examples.CDC» where
  roots := #[`Examples.CDC]

lean_lib «Examples.FPU» where
  roots := #[`Examples.FPU]

lean_lib «IP.Video» where
  roots := #[`IP.Video]

lean_lib «IP.Bus» where
  roots := #[`IP.Bus]

lean_lib «Tools.SVParser» where
  roots := #[`Tools.SVParser]

lean_lib «TutorialExtended» where
  roots := #[`TutorialExtended]
  srcDir := "tutorial-extended"

-- Display: a shim for xeus-lean's `Display.*` library so that
-- chapter cells can `import Display` and call
-- `Display.waveform`, `Display.boolWave`, `Display.blockDiagram`,
-- `Display.writeWdb`, etc. from headless `lake build` as well as
-- from inside xeus-lean.  In the xeus-lean kernel the real Display
-- library takes precedence; this shim is the offline fallback.
lean_lib «Display» where
  roots := #[`Display]
  srcDir := "docs/tutorial"

lean_lib «TutorialNotebooks» where
  roots := #[`Notebooks]
  srcDir := "docs/tutorial"

lean_exe «tutorial-extended-run» where
  root := `TutorialExtended.Run
  srcDir := "tutorial-extended"
  supportInterpreter := true

lean_exe «tutorial-mermaid-test» where
  root := `TutorialExtended.MermaidHelperTest
  srcDir := "tutorial-extended"
  supportInterpreter := true

lean_lib «Tests» where
  -- Test circuits library

@[default_target]
lean_exe «sparkle» where
  root := `Main

lean_exe «verilog-tests» where
  root := `Tests.VerilogTests
  supportInterpreter := true

-- Smoke-runs the Signal-DSL counter from docs/Tutorial.md Step 1 so CI
-- verifies the `#eval` path actually executes (not just type-checks).
lean_exe «tutorial-smoke» where
  root := `Tests.Tutorial.SmokeTest
  supportInterpreter := true

lean_exe «tutorial-hierarchy» where
  root := `Tests.Tutorial.HierarchyTest
  supportInterpreter := true

-- Runtime check for the statement-level `if/else` extension to
-- `Signal.circuit do`.  Drives a few reset-counter / priority-
-- mux / hold-semantics designs through `Signal.loop`'s native
-- FFI and asserts the cycle-by-cycle output matches what a
-- hand-rolled `Signal.mux` lowering would produce.
lean_exe «circuit-if-test» where
  root := `Tests.Drivers.CircuitIfTestMain
  supportInterpreter := true

-- Runtime check for the raw `Signal.loop` / `Signal.register`
-- form (no macro DSL).  Pairs each loop-direct circuit with
-- its `Signal.circuit do` equivalent and asserts the
-- cycle-by-cycle outputs agree, so future macro changes can't
-- silently drift from the loop semantics they desugar to.
lean_exe «signal-loop-test» where
  root := `Tests.Drivers.SignalLoopTestMain
  supportInterpreter := true

-- Runtime check for the statement-level `match` extension to
-- `Signal.circuit do`.  Drives a 3-state FSM and variations
-- through `Signal.loop` and asserts the cycle-by-cycle output
-- matches what a hand-rolled Signal.mux chain would produce.
lean_exe «circuit-match-test» where
  root := `Tests.Drivers.CircuitMatchTestMain
  supportInterpreter := true

-- PoC v2 (branch poc/circuit-monad-v2) — sim parity check
-- between the new HList / Prod-chain monad surface
-- (`runCircuit1` / `runCircuit2`) and the `Signal.circuit do`
-- macro on the same circuits.  Synthesis isn't end-to-end
-- green yet (see commit notes); sim is the part we drive
-- here.  Not wired into `lake test` until synthesis catches up.
lean_exe «circuit-monad-v2-test» where
  root := `Tests.Drivers.CircuitMonadV2TestMain
  supportInterpreter := true

-- Sim parity for the `circuit do` macro (v2 monad surface with
-- statement-level if/else syntax sugar).  Pairs each cdo
-- circuit with its `Signal.circuit do` macro reference and
-- asserts cycle-by-cycle outputs agree.
lean_exe «circuit-do-test» where
  root := `Tests.Drivers.CircuitDoTestMain
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

lean_exe «rv32-jit-loop-test» where
  root := `Tests.RV32.JITLoopTest

lean_exe «rv32-jit-cycle-skip-test» where
  root := `Tests.RV32.JITCycleSkipTest
  supportInterpreter := true

lean_exe «rv32-jit-oracle-test» where
  root := `Tests.RV32.JITOracleTest
  supportInterpreter := true

lean_exe «rv32-jit-dynamic-warp-test» where
  root := `Tests.RV32.JITDynamicWarpTest
  supportInterpreter := true

lean_exe «rv32-jit-speculative-warp-test» where
  root := `Tests.RV32.JITSpeculativeWarpTest
  supportInterpreter := true

lean_exe «rv32-jit-boot-oracle-test» where
  root := `Tests.RV32.JITBootOracleTest
  supportInterpreter := true

lean_exe «oracle-accuracy-test» where
  root := `Tests.RV32.OracleAccuracyTest
  supportInterpreter := true

lean_exe «rv32-jit-linux-boot-test» where
  root := `Tests.RV32.JITLinuxBootTest
  supportInterpreter := true

lean_exe «bitnet-mmio-probe» where
  root := `Tests.RV32.BitNetMmioProbe
  supportInterpreter := true

-- End-to-end Linux driver test: boots a kernel image patched with the
-- in-tree sparkle-bitnet driver and an initramfs /init that exercises
-- /dev/bitnet0 against 8 golden vectors. Asserts on UART markers
-- "sparkle-bitnet … registered" + "BITNET PASS".
lean_exe «bitnet-linux-test» where
  root := `Tests.Integration.BitNetLinuxTest
  supportInterpreter := true

lean_exe «h264-jit-test» where
  root := `Tests.Video.H264JITTest
  supportInterpreter := true

lean_exe «h264-jit-pipeline-test» where
  root := `Tests.Video.H264JITPipelineTest
  supportInterpreter := true

lean_exe «h264-bitstream-test» where
  root := `Tests.Video.H264BitstreamTest
  supportInterpreter := true

lean_exe «h264-playable-test» where
  root := `Tests.Video.H264PlayableTest
  supportInterpreter := true

lean_exe «h264-frame-encoder-test» where
  root := `Tests.Video.H264FrameEncoderTest
  supportInterpreter := true

lean_exe «h264-mp4-encoder-test» where
  root := `Tests.Video.H264MP4EncoderTest
  supportInterpreter := true

lean_exe «cdc-multi-clock-test» where
  root := `Tests.CDC.MultiClockTest
  supportInterpreter := true

lean_exe «sim-runner-test» where
  root := `Tests.Sim.SimRunnerTest
  supportInterpreter := true

lean_exe «bitnet-soc-test» where
  root := `Tests.Integration.BitNetSoCTest
  supportInterpreter := true

lean_exe «timemux-sim-test» where
  root := `Tests.Synthesis.TimeMuxSim
  supportInterpreter := true

lean_exe «golden-compare-test» where
  root := `Tests.Synthesis.GoldenCompare
  supportInterpreter := true

lean_exe «ffn-golden-test» where
  root := `Tests.Synthesis.FFNGolden
  supportInterpreter := true

lean_exe «toplevel-sim-test» where
  root := `Tests.Synthesis.TopLevelSim
  supportInterpreter := true

lean_exe «svparser-test» where
  root := `Tests.SVParser.ParserTest
  supportInterpreter := true

lean_exe «verilog-sim-le» where
  root := `Examples.SVParser.VerilogSim
  supportInterpreter := true

lean_exe «generate-verify» where
  root := `Tools.SVParser.GenerateVerify
  supportInterpreter := true

lean_exe «circuit-sim-test» where
  root := `Tests.Circuit.SimTest
  supportInterpreter := true

lean_exe «mext-rv32i-test» where
  root := `Tests.SVParser.MExtRv32iTest
  supportInterpreter := true

lean_exe «mul-oracle-test» where
  root := `Tests.RV32.MulOracleTest
  supportInterpreter := true

lean_exe «litex-test» where
  root := `Tests.SVParser.LiteXTest
  supportInterpreter := true

lean_exe «drone-closed-loop-test» where
  root := `Tests.Integration.DroneClosedLoopSim
  supportInterpreter := true

@[test_driver]
lean_exe «test» where
  root := `Tests.AllTests
  supportInterpreter := true
