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

-- Linker args making an IP lib's monolithic `libsparkle_IP_*.so` depend on
-- every PER-MODULE Sparkle dynlib (in `.lake/build/lib/lean`).
--
-- Why this exists: the interpreter/LSP force-loads an IP lib's monolithic
-- `.so` (via `--load-dynlib`, see `lake setup-file`) at startup — *before*
-- Sparkle's per-module dynlibs are loaded by olean imports. The monolithic
-- references Sparkle closures/initializers (e.g.
-- `Signal.map___redArg___lam__0`, `initialize_sparkle_Sparkle`) and so failed
-- to load with a confusing *undefined symbol* even though the `.olean` built
-- fine. (Triggered once `Signal.map` started routing through the
-- `@[extern "sparkle_cache_get"]` LICM barrier, which the IP libs reference.)
--
-- We depend on the PER-MODULE `.so` — the SAME files olean imports load — so
-- the dynamic loader dedups them by path and each module initializer runs
-- exactly once. Depending on the aggregate `libsparkle_Sparkle.so` instead
-- loads a second full copy and double-registers env extensions
-- ("'Sparkle.Compiler.hardwareModuleAttr' has already been used"). The
-- monolithic transitively needs the root `Sparkle` module, so we list them
-- all. `--no-as-needed` forces every entry to be recorded as NEEDED;
-- `$ORIGIN/lean` rpath finds them at runtime (monolithic is in `lib`, these
-- in `lib/lean`).
--
-- Regenerate after adding/removing Sparkle modules:
--   ls .lake/build/lib/lean/sparkle_Sparkle*.so
-- A missing entry shows up as an undefined-symbol load error naming the module.
def sparkleModuleDeps : Array String := #[
    "-l:sparkle_Sparkle_Backend_CppSim.so",
    "-l:sparkle_Sparkle_Backend_VCD.so",
    "-l:sparkle_Sparkle_Backend_Verilog.so",
    "-l:sparkle_Sparkle_Compiler_DRC.so",
    "-l:sparkle_Sparkle_Compiler_Elab.so",
    "-l:sparkle_Sparkle_Compiler_InlineAttr.so",
    "-l:sparkle_Sparkle_Core_CircuitDo.so",
    "-l:sparkle_Sparkle_Core_CircuitMonad.so",
    "-l:sparkle_Sparkle_Core_Domain.so",
    "-l:sparkle_Sparkle_Core_JITLoop.so",
    "-l:sparkle_Sparkle_Core_JIT.so",
    "-l:sparkle_Sparkle_Core_MulOracleProof.so",
    "-l:sparkle_Sparkle_Core_MulOracle.so",
    "-l:sparkle_Sparkle_Core_OptimizedSim.so",
    "-l:sparkle_Sparkle_Core_Oracle.so",
    "-l:sparkle_Sparkle_Core_OracleSpec.so",
    "-l:sparkle_Sparkle_Core_Signal.so",
    "-l:sparkle_Sparkle_Core_SimParallel.so",
    "-l:sparkle_Sparkle_Core_SimPureLean.so",
    "-l:sparkle_Sparkle_Core_Sim.so",
    "-l:sparkle_Sparkle_Core_SimVerilator.so",
    "-l:sparkle_Sparkle_Core_StateMacro.so",
    "-l:sparkle_Sparkle_Core_Vector.so",
    "-l:sparkle_Sparkle_Core_Wireable.so",
    "-l:sparkle_Sparkle_Data_BitPack.so",
    "-l:sparkle_Sparkle_Display_Diagram.so",
    "-l:sparkle_Sparkle_Display_Interactive.so",
    "-l:sparkle_Sparkle_Display_Mime.so",
    "-l:sparkle_Sparkle_Display.so",
    "-l:sparkle_Sparkle_Display_Synthesise.so",
    "-l:sparkle_Sparkle_IR_AST.so",
    "-l:sparkle_Sparkle_IR_Builder.so",
    "-l:sparkle_Sparkle_IR_Optimize.so",
    "-l:sparkle_Sparkle_IR_Type.so",
    "-l:sparkle_Sparkle.so",
    "-l:sparkle_Sparkle_Utils_HexLoader.so",
    "-l:sparkle_Sparkle_Verification_Equivalence.so",
    "-l:sparkle_Sparkle_Verification_LoopProps.so",
    "-l:sparkle_Sparkle_Verification_MulProps.so",
    "-l:sparkle_Sparkle_Verification_Temporal.so"
  ]

-- These args are GNU-ld specific: `-l:NAME.so` exact-file linking, the
-- `--no-as-needed`/`--as-needed` toggles, and the ELF `$ORIGIN` rpath token.
-- Apple `ld64` rejects all of them (per-module dynlibs are `.dylib`, not `.so`;
-- the rpath origin token is `@loader_path`), and the force-load ordering bug
-- they work around is itself Linux/glibc/GNU-ld-only — see
-- docs/lean-lake-force-load-ordering-issue.md ("OS: Linux (x86_64, glibc), GNU
-- ld"). So guard per-platform exactly like the `Sparkle` lib's `moreLinkArgs`
-- below: on macOS/Windows fall back to Lake's default linking (empty extra
-- args), which is also all the IP libs need there since the editor force-load
-- path that triggers the bug is the Linux interpreter/LSP.
def sparkleDynlibLinkArgs : Array String :=
  if System.Platform.isOSX || System.Platform.isWindows then
    #[]
  else
    #["-L", "./.lake/build/lib/lean", "-Wl,--no-as-needed"]
      ++ sparkleModuleDeps
      ++ #["-Wl,--as-needed", "-Wl,-rpath,$ORIGIN/lean"]

-- `precompileModules := true` builds a shared library
-- (`.lake/build/lib/libsparkle_Sparkle.so`) alongside the oleans.
-- The xeus-lean kernel needs this when it encounters `@[extern]`
-- calls like `Sparkle.Core.JIT.JIT.load` inside a notebook `#eval`:
-- the interpreter dlsym-loads the per-module `lp_*` wrapper from
-- the shared lib instead of expecting it to be statically linked
-- into the kernel binary.  Without it, the kernel binary only has
-- the raw C symbols (we wired those through `XEUS_LEAN_EXTRA_LIBS`
-- in the tutorial Dockerfile) but is missing the Lean-side boxing
-- wrappers, so every `JIT.load` throws "Could not find native
-- implementation".
--
-- Visibility of the C-side externs is handled in the .c sources
-- themselves (see `#pragma GCC visibility push(default)` in
-- `c_src/sparkle_barrier.c` and `c_src/sparkle_jit.c`), which is
-- portable across Linux / macOS / Windows.
--
-- Visibility alone, however, is NOT enough for the *precompiled*
-- `libsparkle_Sparkle.so`: a plain `-l:…a` only pulls the archive
-- members that resolve a currently-undefined symbol, and Lake links
-- the extern archives into executables but not into the precompiled
-- shared lib.  The result is that `libsparkle_Sparkle.so` keeps
-- `sparkle_cache_get` / `sparkle_jit_load` as *undefined* symbols and
-- is only loadable when something else has already pulled the C side
-- into the global symbol scope.  Once `Signal.map` started routing
-- through the `@[extern "sparkle_cache_get"]` LICM barrier, every
-- downstream IP lib that references a `Signal` closure (e.g.
-- `libsparkle_IP_x2eBitNet.so` → `Signal.map___redArg___lam__0`)
-- began failing to load with a confusing *undefined symbol* on the
-- Signal closure — the real cause being that `libsparkle_Sparkle.so`
-- itself can't resolve `sparkle_cache_get`.
--
-- So force the two extern archives whole-into the precompiled `.so`
-- so it is self-contained regardless of load order / dlopen scope.
-- `--whole-archive` is GNU-ld only; on Apple `ld64` the equivalent is
-- `-force_load`. Guard per-platform; Windows/MSVC keeps relying on the
-- visibility pragmas above. The `./.lake/build/c_src` path resolves
-- against Sparkle's own package dir during `lake build` here; a
-- separate downstream consumer that precompiles Sparkle may need an
-- absolute path (see commit 67d2c73 for that history).
lean_lib «Sparkle» where
  precompileModules := true
  moreLinkArgs :=
    if System.Platform.isOSX then
      #["-Wl,-force_load,.lake/build/c_src/libsparkle_barrier.a",
        "-Wl,-force_load,.lake/build/c_src/libsparkle_jit.a"]
    else if System.Platform.isWindows then
      #[]
    else
      #["-L", "./.lake/build/c_src",
        "-Wl,--whole-archive",
        "-l:libsparkle_barrier.a",
        "-l:libsparkle_jit.a",
        "-Wl,--no-whole-archive"]

lean_lib «IP.BitNet» where
  roots := #[`IP.BitNet]
  -- See `sparkleDynlibLinkArgs` above: makes the force-loaded monolithic
  -- resolve Sparkle symbols against the per-module dynlibs (no double-init).
  moreLinkArgs := sparkleDynlibLinkArgs

lean_lib «IP.Drone» where
  roots := #[`IP.Drone]

lean_lib «IP.Humanoid» where
  roots := #[`IP.Humanoid]

lean_lib «IP.RV32» where
  roots := #[`IP.RV32]
  -- See `sparkleDynlibLinkArgs` above.
  moreLinkArgs := sparkleDynlibLinkArgs

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

-- Runtime check for the raw `Signal.loop` / `Signal.register`
-- form (no `circuit do` sugar).  Pairs each loop-direct circuit
-- with its `circuit do` equivalent and asserts the cycle-by-
-- cycle outputs agree, so future macro changes can't silently
-- drift from the loop semantics they desugar to.
lean_exe «signal-loop-test» where
  root := `Tests.Drivers.SignalLoopTestMain
  supportInterpreter := true

-- Sim parity for the `circuit do` macro itself: counter, reset
-- counter (if/else), two-register reset, hold semantics, 3-state
-- FSM (match), and FSM-hold (match + hold).  Plus a duplicate-
-- `<~` detection guard.
lean_exe «circuit-do-test» where
  root := `Tests.Drivers.CircuitDoTestMain
  supportInterpreter := true

-- Sim + synth check for the HList-based generic `runCircuitH`
-- — the sole register-DSL helper after the per-arity
-- `runCircuit{1..4}` were removed.  Covers N=1..4 plus
-- mixed-width state and `forM` over the register list.
lean_exe «run-circuit-h-test» where
  root := `Tests.Drivers.RunCircuitHTestMain
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

lean_exe «iverilog-roundtrip-test» where
  root := `Tests.Drivers.IVerilogSimMain
  supportInterpreter := true

@[test_driver]
lean_exe «test» where
  root := `Tests.AllTests
  supportInterpreter := true

