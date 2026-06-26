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
-- portable across Linux / macOS / Windows.  A previous attempt
-- used `-Wl,--whole-archive` here, but that flag (a) doesn't exist
-- on Apple ld64 and (b) used a relative `-L ./.lake/build/c_src`
-- which resolved against the *downstream consumer's* cwd, not
-- Sparkle's package dir — so downstream `lake build` from a
-- separate project broke on every OS.
lean_lib «Sparkle» where
  precompileModules := true

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

-- HFT-leaning TCP/IP stack (10 GbE XGMII ↔ TCP payload stream).
-- Layers under IP/Net/: CRC32, Ethernet, ARP, IPv4, UDP, TCP, HFTStack.
lean_lib «IP.Net» where
  roots := #[`IP.Net]

-- Ledger-style crypto (SHA-256, Ed25519, secp256k1) for signed
-- order packets in the HFT stack and as standalone Sparkle IPs.
lean_lib «IP.Crypto» where
  roots := #[`IP.Crypto]

-- TLS 1.3 stack: record layer, handshake state machine.
-- Builds on IP.Crypto (AES-GCM, HKDF, X25519, SHA-256).
lean_lib «IP.TLS» where
  roots := #[`IP.TLS]

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

-- IP.Net.CRC32 (Ethernet FCS, reflected CRC-32/IEEE-802.3).
-- Sim test: pure Lean reference, Signal-DSL engine, and IEEE
-- 802.3 golden vectors must all agree.
lean_exe «crc32-test» where
  root := `Tests.Drivers.CRC32TestMain
  supportInterpreter := true

-- IP.Net.Ethernet (byte-feed RX framer).
-- Sim test: a synthetic 18-byte frame fed cycle-by-cycle, and the
-- six RX outputs (DMAC / SMAC / EthType / hdrDone / payloadByte /
-- payloadValid) checked against golden values.  Also exercises
-- the `circuit do { … return { field := … } }` multi-output
-- return path that the runCircuitH ρ-generalisation enables.
lean_exe «ethernet-test» where
  root := `Tests.Drivers.EthernetTestMain
  supportInterpreter := true

lean_exe «eth-trace» where
  root := `Tests.Drivers.EthTraceMain
  supportInterpreter := true

lean_exe «ethernet-tx-test» where
  root := `Tests.Drivers.EthernetTxTestMain
  supportInterpreter := true

lean_exe «arp-test» where
  root := `Tests.Drivers.ARPTestMain
  supportInterpreter := true

lean_exe «arp-trace» where
  root := `Tests.Drivers.ArpTraceMain
  supportInterpreter := true

lean_exe «ipv4-test» where
  root := `Tests.Drivers.IPv4TestMain
  supportInterpreter := true

lean_exe «icmp-test» where
  root := `Tests.Drivers.ICMPTestMain
  supportInterpreter := true

lean_exe «icmp-trace» where
  root := `Tests.Drivers.IcmpTraceMain
  supportInterpreter := true

lean_exe «tcp-header-test» where
  root := `Tests.Drivers.TCPHeaderTestMain
  supportInterpreter := true

lean_exe «tcp-state-test» where
  root := `Tests.Drivers.TCPStateTestMain
  supportInterpreter := true

lean_exe «tcp-loopback-test» where
  root := `Tests.Drivers.TCPLoopbackTestMain
  supportInterpreter := true

lean_exe «http-test» where
  root := `Tests.Drivers.HTTPTestMain
  supportInterpreter := true

lean_exe «hft-strategy-test» where
  root := `Tests.Drivers.HFTStrategyTestMain
  supportInterpreter := true

lean_exe «sha256-test» where
  root := `Tests.Drivers.SHA256TestMain
  supportInterpreter := true

lean_exe «ed25519-field-test» where
  root := `Tests.Drivers.Ed25519FieldTestMain
  supportInterpreter := true

lean_exe «ed25519-point-test» where
  root := `Tests.Drivers.Ed25519PointTestMain
  supportInterpreter := true

lean_exe «ed25519-sign-test» where
  root := `Tests.Drivers.Ed25519SignTestMain
  supportInterpreter := true

lean_exe «ed25519-verify-test» where
  root := `Tests.Drivers.Ed25519VerifyTestMain
  supportInterpreter := true

lean_exe «p256-ecdsa-test» where
  root := `Tests.Drivers.P256ECDSATestMain
  supportInterpreter := true

lean_exe «rsa-pss-test» where
  root := `Tests.Drivers.RSAPSSTestMain
  supportInterpreter := true

lean_exe «x509-parser-test» where
  root := `Tests.Drivers.X509ParserTestMain
  supportInterpreter := true

lean_exe «x509-verify-test» where
  root := `Tests.Drivers.X509VerifyTestMain
  supportInterpreter := true

lean_exe «tls-client-server-test» where
  root := `Tests.Drivers.TLSClientServerTestMain
  supportInterpreter := true

lean_exe «https-demo» where
  root := `Tests.Drivers.HTTPSDemoMain
  supportInterpreter := true

lean_exe «can-test» where
  root := `Tests.Drivers.CANTestMain
  supportInterpreter := true

lean_exe «canopen-test» where
  root := `Tests.Drivers.CANopenTestMain
  supportInterpreter := true

lean_exe «dronecan-test» where
  root := `Tests.Drivers.DroneCANTestMain
  supportInterpreter := true

lean_exe «serial-bus-test» where
  root := `Tests.Drivers.SerialBusTestMain
  supportInterpreter := true

lean_exe «avionics-bus-test» where
  root := `Tests.Drivers.AvionicsBusTestMain
  supportInterpreter := true

lean_exe «can-hw-test» where
  root := `Tests.Drivers.CANHWTestMain
  supportInterpreter := true

lean_exe «uart-test» where
  root := `Tests.Drivers.UARTTestMain
  supportInterpreter := true

lean_exe «slip-test» where
  root := `Tests.Drivers.SLIPTestMain
  supportInterpreter := true

lean_exe «usb-webserver-sim» where
  root := `Tests.Drivers.UsbWebServerSimMain
  supportInterpreter := true

lean_exe «x25519-test» where
  root := `Tests.Drivers.X25519TestMain
  supportInterpreter := true

lean_exe «aes-test» where
  root := `Tests.Drivers.AESTestMain
  supportInterpreter := true

lean_exe «ghash-test» where
  root := `Tests.Drivers.GHASHTestMain
  supportInterpreter := true

lean_exe «ghash-hw-test» where
  root := `Tests.Drivers.GHASHHWTestMain
  supportInterpreter := true

lean_exe «probe-ghash» where
  root := `Tests.Drivers.ProbeGhashMain
  supportInterpreter := true

lean_exe «aes-gcm-test» where
  root := `Tests.Drivers.AESGCMTestMain
  supportInterpreter := true

lean_exe «hkdf-test» where
  root := `Tests.Drivers.HKDFTestMain
  supportInterpreter := true

lean_exe «tls-keysched-test» where
  root := `Tests.Drivers.TLSKeyScheduleTestMain
  supportInterpreter := true

lean_exe «tls-client-fsm-test» where
  root := `Tests.Drivers.TLSClientFsmTestMain
  supportInterpreter := true

lean_exe «hft-over-tls-test» where
  root := `Tests.Drivers.HFTOverTLSTestMain
  supportInterpreter := true

lean_exe «tls-x509-test» where
  root := `Tests.Drivers.TLSX509TestMain
  supportInterpreter := true

lean_exe «sha512-check» where
  root := `Tests.Drivers.Sha512CheckMain
  supportInterpreter := true

lean_exe «secp256k1-test» where
  root := `Tests.Drivers.Secp256k1TestMain
  supportInterpreter := true

lean_exe «goldilocks-test» where
  root := `Tests.Drivers.GoldilocksTestMain
  supportInterpreter := true

lean_exe «merkle-test» where
  root := `Tests.Drivers.MerkleTestMain
  supportInterpreter := true

lean_exe «polynomial-test» where
  root := `Tests.Drivers.PolynomialTestMain
  supportInterpreter := true

lean_exe «mini-stark-test» where
  root := `Tests.Drivers.MiniSTARKTestMain
  supportInterpreter := true

lean_exe «pcie-test» where
  root := `Tests.Drivers.PCIeTestMain
  supportInterpreter := true

lean_exe «pcie-hft-test» where
  root := `Tests.Drivers.PCIeHFTTestMain
  supportInterpreter := true

lean_exe «sim-cost» where
  root := `Tests.Drivers.SimCostMain
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

