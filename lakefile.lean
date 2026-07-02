import Lake
open Lake DSL

package «sparkle» where

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
    "-l:sparkle_Sparkle_Backend_CSim.so",
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
    "-l:sparkle_Sparkle_Core_SignalLeavesDerive.so",
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
-- Absolute path to this package's build dir, captured at lakefile
-- elaboration.  `decide`-free: `__dir__` is the directory containing
-- *this* lakefile, so `<pkgdir>/.lake/build/c_src` is correct whether
-- Sparkle is the root package (`lake build` here) OR a git dependency
-- of a downstream project (`<downstream>/.lake/packages/sparkle/…`).
-- Using this instead of a relative `./.lake/build/c_src` is what keeps
-- the barrier/jit force_load args from breaking downstream consumers,
-- whose CWD-relative `./.lake/build/c_src` is their own empty build dir.
def sparkleCSrcDir : System.FilePath :=
  (__dir__ : System.FilePath) / ".lake" / "build" / "c_src"

lean_lib «Sparkle» where
  precompileModules := true
  -- Force the two extern archives whole-into the precompiled
  -- `libsparkle_Sparkle.so` so it self-resolves `sparkle_cache_get` /
  -- `sparkle_eval_at` (the `@[extern]` LICM barriers `Signal.loop`'s
  -- memoization uses) regardless of dlopen load order.  Without this the
  -- interpreter/LSP fails to load the `.so` with an undefined-symbol
  -- error.  The path is ABSOLUTE (`sparkleCSrcDir`) so a downstream
  -- consumer that inherits these args still finds Sparkle's own populated
  -- c_src — the relative form (PR #65 `c59820c`) broke downstream-smoke.
  moreLinkArgs :=
    let barrier := (sparkleCSrcDir / "libsparkle_barrier.a").toString
    let jit := (sparkleCSrcDir / "libsparkle_jit.a").toString
    if System.Platform.isOSX then
      #[s!"-Wl,-force_load,{barrier}", s!"-Wl,-force_load,{jit}"]
    else if System.Platform.isWindows then
      #[]
    else
      #["-Wl,--whole-archive", barrier, jit, "-Wl,--no-whole-archive"]

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

lean_exe «keccak256-test» where
  root := `Tests.Drivers.Keccak256TestMain
  supportInterpreter := true

lean_exe «rlp-test» where
  root := `Tests.Drivers.RLPTestMain
  supportInterpreter := true

lean_exe «eip1559-tx-test» where
  root := `Tests.Drivers.Eip1559TxTestMain
  supportInterpreter := true

lean_exe «erc20-abi-test» where
  root := `Tests.Drivers.Erc20AbiTestMain
  supportInterpreter := true

lean_exe «bip39-test» where
  root := `Tests.Drivers.Bip39TestMain
  supportInterpreter := true

lean_exe «bip32-test» where
  root := `Tests.Drivers.Bip32TestMain
  supportInterpreter := true

lean_exe «eth-wallet-test» where
  root := `Tests.Drivers.EthWalletTestMain
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

lean_exe «lin-hw-test» where
  root := `Tests.Drivers.LINHWTestMain
  supportInterpreter := true

lean_exe «i2c-hw-test» where
  root := `Tests.Drivers.I2CHWTestMain
  supportInterpreter := true

lean_exe «spi-hw-test» where
  root := `Tests.Drivers.SPIHWTestMain
  supportInterpreter := true

lean_exe «sbus-hw-test» where
  root := `Tests.Drivers.SBUSHWTestMain
  supportInterpreter := true

lean_exe «crsf-hw-test» where
  root := `Tests.Drivers.CRSFHWTestMain
  supportInterpreter := true

lean_exe «mil1553-hw-test» where
  root := `Tests.Drivers.MIL1553HWTestMain
  supportInterpreter := true

lean_exe «canopen-hw-test» where
  root := `Tests.Drivers.CANopenHWTestMain
  supportInterpreter := true

lean_exe «dronecan-hw-test» where
  root := `Tests.Drivers.DroneCANHWTestMain
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

lean_exe «memcached-oracle-test» where
  root := `Tests.Drivers.MemcachedOracleTestMain
  supportInterpreter := true

lean_exe «memcached-hw-test» where
  root := `Tests.Drivers.MemcachedHWTestMain
  supportInterpreter := true

lean_exe «memcached-server-test» where
  root := `Tests.Drivers.MemcachedServerTestMain
  supportInterpreter := true

-- JIT-backed variant of memcached-server-test.  Same coverage
-- as the pure-Lean form above, but routes the cycle loop
-- through `#sim`-generated C++ + dlopen rather than evaluating
-- `Signal.val` per cycle (which was hitting the 25-min CI cap
-- on the BitVec 128 path).
lean_exe «memcached-server-jit-test» where
  root := `Tests.Drivers.MemcachedServerJITTestMain
  supportInterpreter := true

-- JIT-backed pilot on a single-output, sub-module-free design
-- (CRC32 engine).  Same golden vectors as `crc32-test` but
-- routes the cycle loop through `#sim` + dlopen, demonstrating
-- the wall-time win on a design that doesn't hit Issue #71.
lean_exe «crc32-jit-test» where
  root := `Tests.Drivers.CRC32JITTestMain
  supportInterpreter := true

-- JIT-backed variant of toplevel-sim-test.  The BitNet
-- accelerator's pure-Lean Signal evaluation hits the same
-- O(t²) Signal.val cost that times out usb-webserver-sim
-- and memcached-server-test in CI; this driver runs the
-- same 50-cycle stimulus via JIT.
lean_exe «toplevel-sim-jit-test» where
  root := `Tests.Drivers.TopLevelSimJITTestMain
  supportInterpreter := true

-- JIT-backed variant of usb-webserver-sim.  Each multi-output
-- sub-module projection is wrapped in its own scalar
-- `@[hardware_module]` to keep the elaborator on its known
-- struct-projection path.
lean_exe «usb-webserver-jit-test» where
  root := `Tests.Drivers.UsbWebServerJITTestMain
  supportInterpreter := true

lean_exe «ipv4-jit-test» where
  root := `Tests.Drivers.IPv4JITTestMain
  supportInterpreter := true


-- Repro for the known sub-module-instance + multi-register
-- caller hang in the synth elaborator.  Builds clean (the
-- failing #synthesizeVerilog is commented out); see the file's
-- docstring for the pattern and where it bites in real IPs.
lean_exe «multi-output-submodule-hang-repro» where
  root := `Tests.Drivers.MultiOutputSubModuleHangReproMain
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

-- Crypto HW modules (Wave 1: byte/word FSM tier).  Each pairs a
-- pure-data reference in `IP/Crypto/<Name>.lean` with a `circuit
-- do` HW module in `IP/Crypto/<Name>HW.lean`; behavioural + synth
-- checks live under `Tests/IP/Crypto/<Name>HWTest.lean`.
lean_exe «rlp-hw-test» where
  root := `Tests.Drivers.RLPHWTestMain
  supportInterpreter := true

lean_exe «merkle-hw-test» where
  root := `Tests.Drivers.MerkleHWTestMain
  supportInterpreter := true

lean_exe «hkdf-hw-test» where
  root := `Tests.Drivers.HKDFHWTestMain
  supportInterpreter := true

lean_exe «sha512-hw-test» where
  root := `Tests.Drivers.SHA512HWTestMain
  supportInterpreter := true

lean_exe «aes-hw-test» where
  root := `Tests.Drivers.AESHWTestMain
  supportInterpreter := true

lean_exe «aes-gcm-hw-test» where
  root := `Tests.Drivers.AESGCMHWTestMain
  supportInterpreter := true

lean_exe «keccak256-hw-test» where
  root := `Tests.Drivers.Keccak256HWTestMain
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

lean_exe «goldilocks-mul-hw-test» where
  root := `Tests.Drivers.GoldilocksHWTestMain
  supportInterpreter := true

lean_exe «secp256k1-mul-hw-test» where
  root := `Tests.Drivers.Secp256k1FieldHWTestMain
  supportInterpreter := true

lean_exe «secp256k1-pointop-hw-test» where
  root := `Tests.Drivers.Secp256k1PointOpHWTestMain
  supportInterpreter := true

lean_exe «secp256k1-scalarmul-hw-test» where
  root := `Tests.Drivers.Secp256k1ScalarMulHWTestMain
  supportInterpreter := true

lean_exe «modinv-hw-test» where
  root := `Tests.Drivers.ModInvHWTestMain
  supportInterpreter := true

lean_exe «secp256k1-ordermul-hw-test» where
  root := `Tests.Drivers.Secp256k1OrderHWTestMain
  supportInterpreter := true

lean_exe «secp256k1-ecdsa-hw-test» where
  root := `Tests.Drivers.Secp256k1ECDSAHWTestMain
  supportInterpreter := true

lean_exe «sha512-block-hw-test» where
  root := `Tests.Drivers.SHA512BlockHWTestMain
  supportInterpreter := true

lean_exe «hmac-sha512-hw-test» where
  root := `Tests.Drivers.HMACSHA512HWTestMain
  supportInterpreter := true

lean_exe «bip32-ckd-hw-test» where
  root := `Tests.Drivers.BIP32CKDHWTestMain
  supportInterpreter := true

lean_exe «eip1559-envelope-hw-test» where
  root := `Tests.Drivers.Eip1559EnvelopeHWTestMain
  supportInterpreter := true

lean_exe «p256-mul-hw-test» where
  root := `Tests.Drivers.P256FieldHWTestMain
  supportInterpreter := true

lean_exe «ed25519-mul-hw-test» where
  root := `Tests.Drivers.Ed25519FieldHWTestMain
  supportInterpreter := true

lean_exe «ed25519-pointop-hw-test» where
  root := `Tests.Drivers.Ed25519PointOpHWTestMain
  supportInterpreter := true

lean_exe «ed25519-scalarmul-hw-test» where
  root := `Tests.Drivers.Ed25519ScalarMulHWTestMain
  supportInterpreter := true

lean_exe «ed25519-sign-hw-test» where
  root := `Tests.Drivers.Ed25519SignHWTestMain
  supportInterpreter := true

lean_exe «bls12381-test» where
  root := `Tests.Drivers.BLS12381TestMain
  supportInterpreter := true

lean_exe «fp381-montmul-hw-test» where
  root := `Tests.Drivers.Fp381MontMulHWTestMain
  supportInterpreter := true

lean_exe «fp2-mul-hw-test» where
  root := `Tests.Drivers.Fp2MulHWTestMain
  supportInterpreter := true

lean_exe «fp6-mul-hw-test» where
  root := `Tests.Drivers.Fp6MulHWTestMain
  supportInterpreter := true

lean_exe «fp12-mul-hw-test» where
  root := `Tests.Drivers.Fp12MulHWTestMain
  supportInterpreter := true

lean_exe «bls12-miller-proj-test» where
  root := `Tests.Drivers.BLS12MillerProjTestMain
  supportInterpreter := true

lean_exe «bls12-miller-hw-test» where
  root := `Tests.Drivers.BLS12MillerHWTestMain
  supportInterpreter := true

lean_exe «g2-pointop-hw-test» where
  root := `Tests.Drivers.G2PointOpHWTestMain
  supportInterpreter := true

lean_exe «g2-scalarmul-hw-test» where
  root := `Tests.Drivers.G2ScalarMulHWTestMain
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

