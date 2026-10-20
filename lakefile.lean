import Lake
open Lake DSL

package «sparkle» where

-- Pinned to the revision Reservoir verifies against v4.32.1.  `main` is
-- newer (9389649) but its own lean-toolchain still says v4.31.0; the pin
-- is what the toolchain bump is actually tested on.
require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "3e23a4a"

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
    "-l:sparkle_Sparkle_Backend_CudaIntra.so",
    "-l:sparkle_Sparkle_Backend_CudaSim.so",
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
    "-l:sparkle_Sparkle_IR_FreshNames.so",
    "-l:sparkle_Sparkle_IR_Optimize.so",
    "-l:sparkle_Sparkle_IR_ReorderInvariance.so",
    "-l:sparkle_Sparkle_IR_Semantics.so",
    "-l:sparkle_Sparkle_IR_Specialize.so",
    "-l:sparkle_Sparkle_IR_Type.so",
    "-l:sparkle_Sparkle_IR_ZeroWidth.so",
    "-l:sparkle_Sparkle_IR_RegDedup.so",
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
-- SVParser's `:shared` dynlib is linked by a HARD `cc`/`ld` step
-- (a native dep of `verilog!` consumers like CounterProps), unlike the
-- IP libs whose monolithic is only ever `--load-dynlib`-ed by the
-- interpreter.  A hard link cannot tolerate `-l:` naming a file Lake
-- never produces, so this variant (a) drops the two phantom entries
-- from `sparkleModuleDeps` — `sparkle_Sparkle.so` (the root is only
-- ever the aggregate `libsparkle_Sparkle.so`) and
-- `..._Verification_LoopProps.so` (not built by default) — and (b)
-- links the aggregate by name for the root module's initializer
-- symbols.
def sparkleSVParserLinkArgs : Array String :=
  if System.Platform.isOSX || System.Platform.isWindows then
    #[]
  else
    #["-L", "./.lake/build/lib/lean", "-L", "./.lake/build/lib",
      "-Wl,--no-as-needed"]
      ++ (sparkleModuleDeps.filter fun a =>
           a != "-l:sparkle_Sparkle.so"
           && a != "-l:sparkle_Sparkle_Verification_LoopProps.so")
      ++ #["-l:libsparkle_Sparkle.so",
           "-Wl,--as-needed", "-Wl,-rpath,$ORIGIN/lean", "-Wl,-rpath,$ORIGIN"]

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

-- USB / FIDO2 transport: CTAPHID report framing, CBOR byte emitter,
-- and the FIDO2 authenticator top.
lean_lib «IP.USB» where
  roots := #[`IP.USB]

-- Ledger-style crypto (SHA-256, Ed25519, secp256k1) for signed
-- order packets in the HFT stack and as standalone Sparkle IPs.
lean_lib «IP.Crypto» where
  roots := #[`IP.Crypto]

-- TLS 1.3 stack: record layer, handshake state machine.
-- Builds on IP.Crypto (AES-GCM, HKDF, X25519, SHA-256).
lean_lib «IP.TLS» where
  roots := #[`IP.TLS]

-- Fixed-point control datapaths: IIR biquad, PID, LQR state feedback.
-- Mathlib-free by construction — these are the synthesized circuits.  The
-- ℝ-level Lyapunov/LQR design that justifies the coefficients lives in the
-- `proofs/` sidecar package, which is outside this build graph.
lean_lib «IP.Control» where
  roots := #[`IP.Control]

lean_lib «Tools.SVParser» where
  roots := #[`Tools.SVParser]
  -- The `«Tools.SVParser»:shared` dynlib is a required native dep of
  -- consumers whose `verilog!` macro imports Tools.SVParser.Macro
  -- (e.g. Sparkle.Verification.CounterProps).  Since this branch's
  -- umbrella pulls in RoundtripProof→EmitSem, that .so's object code
  -- references Sparkle.IR.{Optimize,Semantics,…} symbols, which must
  -- be recorded NEEDED against the per-module Sparkle dynlibs — same
  -- as the IP libs.  (Kept minimal: RoundtripProof was ALSO removed
  -- from the Tools.SVParser umbrella, but Lower→Optimize alone still
  -- pulls Optimize specializations, so the link args are required.)
  -- Uses the SVParser-specific variant that survives a HARD link
  -- (the IP libs' args name two files Lake never builds, tolerated
  -- only by the interpreter's soft load).
  moreLinkArgs := sparkleSVParserLinkArgs

-- `#verify_elab` — the Signal↔IR link (see Tools/VerifyElab.lean)
lean_lib «Tools.VerifyElab» where
  roots := #[`Tools.VerifyElab]

-- The GENERAL Signal↔IR theorem over the deep circuit grammar
lean_lib «Tools.ConcatNorm» where
  roots := #[`Tools.ConcatNorm]

lean_lib «Tools.ConeFold» where
  roots := #[`Tools.ConeFold]

lean_lib «Tools.ConeFoldSlices» where
  roots := #[`Tools.ConeFoldSlices]

lean_lib «Tools.ConeFoldProbes» where
  roots := #[`Tools.ConeFoldProbes]

lean_lib «Tools.ConeFoldOpt» where
  roots := #[`Tools.ConeFoldOpt]

lean_lib «Tools.ConeFoldMem» where
  roots := #[`Tools.ConeFoldMem]

lean_lib «Tools.ConeFoldRT» where
  roots := #[`Tools.ConeFoldRT]

lean_lib «Tools.DeepElab» where
  roots := #[`Tools.DeepElab]

lean_lib «Tools.CertifiedRoundtrip» where
  roots := #[`Tools.CertifiedRoundtrip]

lean_lib «Tools.CertifyShared» where
  roots := #[`Tools.CertifyShared]

lean_lib «Tools.VerifiedBlock» where
  roots := #[`Tools.VerifiedBlock]

lean_lib «Tools.VerifiedState» where
  roots := #[`Tools.VerifiedState]

lean_lib «Tools.VerifiedCircuit» where
  roots := #[`Tools.VerifiedCircuit]

lean_lib «Tools.VerifiedSource» where
  roots := #[`Tools.VerifiedSource]

lean_lib «Tools.ReflectSource» where
  roots := #[`Tools.ReflectSource]

lean_lib «Tools.ApplicativeLowering» where
  roots := #[`Tools.ApplicativeLowering]

lean_lib «Tools.ShippingBuilderSoundness» where
  roots := #[`Tools.ShippingBuilderSoundness]

lean_lib «Tools.ShippingScalarSoundness» where
  roots := #[`Tools.ShippingScalarSoundness]

lean_lib «Tools.ShippingAllocationSoundness» where
  roots := #[`Tools.ShippingAllocationSoundness]

lean_lib «Tools.ShippingBindingsSoundness» where
  roots := #[`Tools.ShippingBindingsSoundness]

lean_lib «Tools.ShippingCacheSoundness» where
  roots := #[`Tools.ShippingCacheSoundness]

lean_lib «Tools.ShippingTranslateSoundness» where
  roots := #[`Tools.ShippingTranslateSoundness]

lean_lib «Tools.ShippingEntrySoundness» where
  roots := #[`Tools.ShippingEntrySoundness]

lean_lib «Tools.ShippingOptSoundness» where
  roots := #[`Tools.ShippingOptSoundness]

lean_lib «Tools.ShippingPrintSoundness» where
  roots := #[`Tools.ShippingPrintSoundness]

lean_lib «Tools.ShippingModulePrintSoundness» where
  roots := #[`Tools.ShippingModulePrintSoundness]

lean_lib «Tools.ShippingPrintEntrySoundness» where
  roots := #[`Tools.ShippingPrintEntrySoundness]

lean_lib «Tools.ShippingSVBridge» where
  roots := #[`Tools.ShippingSVBridge]

lean_lib «Tools.ShippingPendingSoundness» where
  roots := #[`Tools.ShippingPendingSoundness]

lean_lib «Tools.ShippingAssignmentOrder» where
  roots := #[`Tools.ShippingAssignmentOrder]

lean_lib «Tools.ShippingTranslationOrder» where
  roots := #[`Tools.ShippingTranslationOrder]

lean_lib «Tools.ShippingSyntaxSoundness» where
  roots := #[`Tools.ShippingSyntaxSoundness]

lean_lib «Tools.ShippingMuxLoweringSoundness» where
  roots := #[`Tools.ShippingMuxLoweringSoundness]

lean_lib «Tools.ShippingMuxRecursionSoundness» where
  roots := #[`Tools.ShippingMuxRecursionSoundness]

lean_lib «Tools.ShippingMuxTypeSoundness» where
  roots := #[`Tools.ShippingMuxTypeSoundness]

lean_lib «Tools.ShippingBoolSourceSoundness» where
  roots := #[`Tools.ShippingBoolSourceSoundness]

lean_lib «Tools.ShippingCompareLoweringSoundness» where
  roots := #[`Tools.ShippingCompareLoweringSoundness]

lean_lib «Tools.ShippingBoolLiteralSoundness» where
  roots := #[`Tools.ShippingBoolLiteralSoundness]

lean_lib «Tools.ShippingBoolMuxSoundness» where
  roots := #[`Tools.ShippingBoolMuxSoundness]

lean_lib «Tools.ShippingMixedInvariant» where
  roots := #[`Tools.ShippingMixedInvariant]

lean_lib «Tools.ShippingMixedLiteralSoundness» where
  roots := #[`Tools.ShippingMixedLiteralSoundness]

lean_lib «Tools.ShippingMixedBinarySoundness» where
  roots := #[`Tools.ShippingMixedBinarySoundness]

lean_lib «Tools.ShippingMixedRecursion» where
  roots := #[`Tools.ShippingMixedRecursion]

lean_lib «Tools.ShippingContractEntrySoundness» where
  roots := #[`Tools.ShippingContractEntrySoundness]

lean_lib «Tools.ShippingUnifiedRecursion» where
  roots := #[`Tools.ShippingUnifiedRecursion]

lean_lib «Tools.ShippingUnifiedProtection» where
  roots := #[`Tools.ShippingUnifiedProtection]

lean_lib «Tools.ShippingUnifiedEntrySoundness» where
  roots := #[`Tools.ShippingUnifiedEntrySoundness]

lean_lib «Tools.ShippingUnifiedExecutionSoundness» where
  roots := #[`Tools.ShippingUnifiedExecutionSoundness]

lean_lib «Tools.ShippingSeqOptSoundness» where
  roots := #[`Tools.ShippingSeqOptSoundness]

lean_lib «Tools.ShippingSeqSVSoundness» where
  roots := #[`Tools.ShippingSeqSVSoundness]

lean_lib «Tools.ShippingMemorySoundness» where
  roots := #[`Tools.ShippingMemorySoundness]

lean_lib «Tools.ShippingMemoryEntrySoundness» where
  roots := #[`Tools.ShippingMemoryEntrySoundness]

lean_lib «Tools.ShippingHierarchySoundness» where
  roots := #[`Tools.ShippingHierarchySoundness]

lean_lib «Tools.ShippingHierOpen» where
  roots := #[`Tools.ShippingHierOpen]

lean_lib «Tools.ShippingHierSVSoundness» where
  roots := #[`Tools.ShippingHierSVSoundness]

lean_lib «Tools.ShippingHierOptSoundness» where
  roots := #[`Tools.ShippingHierOptSoundness]

lean_lib «Tools.ShippingLinkCtx» where
  roots := #[`Tools.ShippingLinkCtx]

lean_lib «Tools.ShippingInstanceEntrySoundness» where
  roots := #[`Tools.ShippingInstanceEntrySoundness]

lean_lib «Tools.ShippingInstanceLeaf» where
  roots := #[`Tools.ShippingInstanceLeaf]

lean_lib «Tools.ShippingHierTermSoundness» where
  roots := #[`Tools.ShippingHierTermSoundness]

lean_lib «Tools.ShippingCoreSoundness» where
  roots := #[`Tools.ShippingCoreSoundness]

lean_lib «Tools.ShippingInlineSoundness» where
  roots := #[`Tools.ShippingInlineSoundness]

lean_lib «Tools.ShippingMachineSource» where
  roots := #[`Tools.ShippingMachineSource]

lean_lib «Tools.ShippingMachineTrace» where
  roots := #[`Tools.ShippingMachineTrace]

lean_lib «Tools.ShippingMachineClose» where
  roots := #[`Tools.ShippingMachineClose]

lean_lib «Tools.ShippingMachineInst» where
  roots := #[`Tools.ShippingMachineInst]

lean_lib «Tools.ShippingMachineEntry» where
  roots := #[`Tools.ShippingMachineEntry]

lean_lib «Tools.ShippingMachineRef» where
  roots := #[`Tools.ShippingMachineRef]

lean_lib «Tools.ShippingMachineDenote» where
  roots := #[`Tools.ShippingMachineDenote]

lean_lib «Tools.ShippingMachineAuto» where
  roots := #[`Tools.ShippingMachineAuto]

lean_lib «Tools.ShippingMachineFuse» where
  roots := #[`Tools.ShippingMachineFuse]

lean_lib «Tools.ShippingMachineNest» where
  roots := #[`Tools.ShippingMachineNest]

lean_lib «Tools.ShippingMachineCausal» where
  roots := #[`Tools.ShippingMachineCausal]

lean_lib «Tools.ShippingMachineCausalCtx» where
  roots := #[`Tools.ShippingMachineCausalCtx]

lean_lib «Tools.ShippingMachineMemCausal» where
  roots := #[`Tools.ShippingMachineMemCausal]

lean_lib «Tools.ShippingLoopFusion» where
  roots := #[`Tools.ShippingLoopFusion]

lean_lib «Tools.ShippingMachineFuseGen» where
  roots := #[`Tools.ShippingMachineFuseGen]

lean_lib «Tools.ShippingGateChild» where
  roots := #[`Tools.ShippingGateChild]

lean_lib «Tools.ShippingGateChildCommand» where
  roots := #[`Tools.ShippingGateChildCommand]

lean_lib «Tools.ShippingHierState» where
  roots := #[`Tools.ShippingHierState]

lean_lib «Tools.ShippingMemComboSoundness» where
  roots := #[`Tools.ShippingMemComboSoundness]

lean_lib «Tools.ShippingMachineInstG» where
  roots := #[`Tools.ShippingMachineInstG]

lean_lib «Tools.ShippingMachineSeqLinked» where
  roots := #[`Tools.ShippingMachineSeqLinked]

lean_lib «Tools.ShippingHierMem» where
  roots := #[`Tools.ShippingHierMem]

lean_lib «Tools.ShippingMachineComposedT» where
  roots := #[`Tools.ShippingMachineComposedT]

lean_lib «Tools.ShippingMachineLinkedT» where
  roots := #[`Tools.ShippingMachineLinkedT]

lean_lib «Tools.ShippingMachineCallsLinkedTN» where
  roots := #[`Tools.ShippingMachineCallsLinkedTN]

lean_lib «Tools.ShippingMachineDepth» where
  roots := #[`Tools.ShippingMachineDepth]

lean_lib «Tools.ShippingMachineLinkedTG» where
  roots := #[`Tools.ShippingMachineLinkedTG]

lean_lib «Tools.ShippingMachineShipsW» where
  roots := #[`Tools.ShippingMachineShipsW]

lean_lib «Tools.ShippingMachineLoopL» where
  roots := #[`Tools.ShippingMachineLoopL]

lean_lib «Tools.ShippingMachineShipsComb» where
  roots := #[`Tools.ShippingMachineShipsComb]

lean_lib «Tools.ShippingHierOptLinked» where
  roots := #[`Tools.ShippingHierOptLinked]

lean_lib «Tools.ShippingHierOptRun» where
  roots := #[`Tools.ShippingHierOptRun]

lean_lib «Tools.ShippingHierOptRunH» where
  roots := #[`Tools.ShippingHierOptRunH]

lean_lib «Tools.ShippingHierTyped» where
  roots := #[`Tools.ShippingHierTyped]

lean_lib «Tools.ShippingHierPremises» where
  roots := #[`Tools.ShippingHierPremises]

lean_lib «Tools.ShippingHierPremisesBase» where
  roots := #[`Tools.ShippingHierPremisesBase]

lean_lib «Tools.ShippingHierShipsSV» where
  roots := #[`Tools.ShippingHierShipsSV]


lean_lib «Tools.ShippingDesignSVLeaf» where
  roots := #[`Tools.ShippingDesignSVLeaf]

lean_lib «Tools.ShippingDesignSV» where
  roots := #[`Tools.ShippingDesignSV]

lean_lib «Tools.ShippingDesignSVMem» where
  roots := #[`Tools.ShippingDesignSVMem]

lean_lib «Tools.ShippingChildInv» where
  roots := #[`Tools.ShippingChildInv]

lean_lib «Tools.ShippingChildKeeps» where
  roots := #[`Tools.ShippingChildKeeps]

lean_lib «Tools.ShippingChildHarness» where
  roots := #[`Tools.ShippingChildHarness]

lean_lib «Tools.ShippingChildVC» where
  roots := #[`Tools.ShippingChildVC]

lean_lib «Tools.ShippingChildHelpers» where
  roots := #[`Tools.ShippingChildHelpers]

lean_lib «Tools.ShippingChildTranslate» where
  roots := #[`Tools.ShippingChildTranslate]

lean_lib «Tools.ShippingChildFallback» where
  roots := #[`Tools.ShippingChildFallback]

lean_lib «Tools.ShippingChildLegacy» where
  roots := #[`Tools.ShippingChildLegacy]

lean_lib «Tools.ShippingChildBody» where
  roots := #[`Tools.ShippingChildBody]

lean_lib «Tools.ShippingUnifiedSpine» where
  roots := #[`Tools.ShippingUnifiedSpine]

lean_lib «Tools.ShippingSpineOrder» where
  roots := #[`Tools.ShippingSpineOrder]

lean_lib «Tools.ShippingClosedOrder» where
  roots := #[`Tools.ShippingClosedOrder]

lean_lib «Tools.ShippingTopoBody» where
  roots := #[`Tools.ShippingTopoBody]

lean_lib «Tools.ShippingTopoChecks» where
  roots := #[`Tools.ShippingTopoChecks]

lean_lib «Tools.ShippingTopoLinked» where
  roots := #[`Tools.ShippingTopoLinked]

lean_lib «Tools.ShippingCloseInstsSome» where
  roots := #[`Tools.ShippingCloseInstsSome]

lean_lib «Tools.ShippingCloseChecks» where
  roots := #[`Tools.ShippingCloseChecks]

lean_lib «Tools.ShippingCloseMachineFacts» where
  roots := #[`Tools.ShippingCloseMachineFacts]

lean_lib «Tools.ShippingTransitionFields» where
  roots := #[`Tools.ShippingTransitionFields]

lean_lib «Tools.ShippingRankNames» where
  roots := #[`Tools.ShippingRankNames]

lean_lib «Tools.ShippingCallsRank» where
  roots := #[`Tools.ShippingCallsRank]

lean_lib «Tools.ShippingRankRun» where
  roots := #[`Tools.ShippingRankRun]

lean_lib «Tools.ShippingCallsShape» where
  roots := #[`Tools.ShippingCallsShape]

lean_lib «Tools.ShippingHarnessClosed» where
  roots := #[`Tools.ShippingHarnessClosed]

lean_lib «Tools.ShippingMergeClosed» where
  roots := #[`Tools.ShippingMergeClosed]

lean_lib «Tools.ShippingTransitionClosed» where
  roots := #[`Tools.ShippingTransitionClosed]

lean_lib «Tools.ShippingGateChildComb» where
  roots := #[`Tools.ShippingGateChildComb]

lean_lib «Tools.ShippingInstStmt» where
  roots := #[`Tools.ShippingInstStmt]

lean_lib «Tools.ShippingKidsComb» where
  roots := #[`Tools.ShippingKidsComb]

lean_lib «Tools.ShippingDesignWith» where
  roots := #[`Tools.ShippingDesignWith]

lean_lib «Tools.ShippingCallsParent» where
  roots := #[`Tools.ShippingCallsParent]

lean_lib «Tools.ShippingCallsStmts» where
  roots := #[`Tools.ShippingCallsStmts]

lean_lib «Tools.ShippingCallsAssembly» where
  roots := #[`Tools.ShippingCallsAssembly]

lean_lib «Tools.ShippingCallsRun» where
  roots := #[`Tools.ShippingCallsRun]

lean_lib «Tools.ShippingCallsSame» where
  roots := #[`Tools.ShippingCallsSame]

lean_lib «Tools.ShippingCallsGate» where
  roots := #[`Tools.ShippingCallsGate]

lean_lib «Tools.ShippingTopoLinkedG» where
  roots := #[`Tools.ShippingTopoLinkedG]

lean_lib «Tools.ShippingRankG» where
  roots := #[`Tools.ShippingRankG]

lean_lib «Tools.ShippingCloseChecksG» where
  roots := #[`Tools.ShippingCloseChecksG]

lean_lib «Tools.ShippingCallGroups» where
  roots := #[`Tools.ShippingCallGroups]

lean_lib «Tools.ShippingInstStmtG» where
  roots := #[`Tools.ShippingInstStmtG]

lean_lib «Tools.ShippingInstNames» where
  roots := #[`Tools.ShippingInstNames]

lean_lib «Tools.ShippingConnsG» where
  roots := #[`Tools.ShippingConnsG]

lean_lib «Tools.ShippingCallsStmtsG» where
  roots := #[`Tools.ShippingCallsStmtsG]

lean_lib «Tools.ShippingCallsAssemblyG» where
  roots := #[`Tools.ShippingCallsAssemblyG]

lean_lib «Tools.ShippingCallsRunG» where
  roots := #[`Tools.ShippingCallsRunG]

lean_lib «Tools.ShippingMachineChildComb» where
  roots := #[`Tools.ShippingMachineChildComb]

lean_lib «Tools.ShippingMachineChildRun» where
  roots := #[`Tools.ShippingMachineChildRun]

lean_lib «Tools.ShippingMachineClosesAtGen» where
  roots := #[`Tools.ShippingMachineClosesAtGen]

lean_lib «Tools.ShippingCallsClose» where
  roots := #[`Tools.ShippingCallsClose]

lean_lib «Tools.ShippingClosesSplit» where
  roots := #[`Tools.ShippingClosesSplit]

lean_lib «Tools.ShippingMachineCloses» where
  roots := #[`Tools.ShippingMachineCloses]

lean_lib «Tools.ShippingMachineClosesData» where
  roots := #[`Tools.ShippingMachineClosesData]

lean_lib «Tools.ShippingMachineClosesGen» where
  roots := #[`Tools.ShippingMachineClosesGen]

lean_lib «Tools.ShippingHarnessSpine» where
  roots := #[`Tools.ShippingHarnessSpine]

lean_lib «Tools.ShippingCloseLetsRun» where
  roots := #[`Tools.ShippingCloseLetsRun]

lean_lib «Tools.ShippingCloseLetsSplit» where
  roots := #[`Tools.ShippingCloseLetsSplit]

lean_lib «Tools.ShippingReflectCtx» where
  roots := #[`Tools.ShippingReflectCtx]

lean_lib «Tools.ShippingChildRun» where
  roots := #[`Tools.ShippingChildRun]

lean_lib «Tools.ShippingChildServe» where
  roots := #[`Tools.ShippingChildServe]

lean_lib «Tools.ShippingMachineTraceX» where
  roots := #[`Tools.ShippingMachineTraceX]

lean_lib «Tools.ShippingMachineCallsLinkedTR» where
  roots := #[`Tools.ShippingMachineCallsLinkedTR]

lean_lib «Tools.ShippingMachineSeqLinkedR» where
  roots := #[`Tools.ShippingMachineSeqLinkedR]

lean_lib «Tools.ShippingMachineSeqCommandR» where
  roots := #[`Tools.ShippingMachineSeqCommandR]

lean_lib «Tools.ShippingMachineCallsLinkedTG» where
  roots := #[`Tools.ShippingMachineCallsLinkedTG]

lean_lib «Tools.ShippingMachineGateMemCommand» where
  roots := #[`Tools.ShippingMachineGateMemCommand]

lean_lib «Tools.ShippingMachineCallsLinkedTNR» where
  roots := #[`Tools.ShippingMachineCallsLinkedTNR]

lean_lib «Tools.ShippingMachineDepthCommandR» where
  roots := #[`Tools.ShippingMachineDepthCommandR]

lean_lib «Tools.ShippingMachineComposeR» where
  roots := #[`Tools.ShippingMachineComposeR]

lean_lib «Tools.ShippingMachineComposeRCommand» where
  roots := #[`Tools.ShippingMachineComposeRCommand]

lean_lib «Tools.ShippingMachineDepthRunR» where
  roots := #[`Tools.ShippingMachineDepthRunR]

lean_lib «Tools.ShippingMachineDepthHR» where
  roots := #[`Tools.ShippingMachineDepthHR]

lean_lib «Tools.ShippingMachineNestR» where
  roots := #[`Tools.ShippingMachineNestR]

lean_lib «Tools.ShippingMachineTeleNestR» where
  roots := #[`Tools.ShippingMachineTeleNestR]

lean_lib «Tools.ShippingDesignSVBounds» where
  roots := #[`Tools.ShippingDesignSVBounds]

lean_lib «Tools.ShippingDesignSVBack» where
  roots := #[`Tools.ShippingDesignSVBack]

lean_lib «Tools.ShippingShipsDesignSV» where
  roots := #[`Tools.ShippingShipsDesignSV]

lean_lib «Tools.ShippingShipsDesignSVAll» where
  roots := #[`Tools.ShippingShipsDesignSVAll]

lean_lib «Tools.ShippingShipsDesignSVCommand» where
  roots := #[`Tools.ShippingShipsDesignSVCommand]

lean_lib «Tools.ShippingHierSVRunH» where
  roots := #[`Tools.ShippingHierSVRunH]

lean_lib «Tools.ShippingMachineDepthH» where
  roots := #[`Tools.ShippingMachineDepthH]

lean_lib «Tools.ShippingPremiseEval» where
  roots := #[`Tools.ShippingPremiseEval]

lean_lib «Tools.ShippingMachineShipsHier» where
  roots := #[`Tools.ShippingMachineShipsHier]

lean_lib «Tools.ShippingMachineShipsHierCommand» where
  roots := #[`Tools.ShippingMachineShipsHierCommand]

lean_lib «Tools.ShippingMachineShipsHierH» where
  roots := #[`Tools.ShippingMachineShipsHierH]

lean_lib «Tools.ShippingMachineShipsHierHCommand» where
  roots := #[`Tools.ShippingMachineShipsHierHCommand]

lean_lib «Tools.ShippingHierSVRun» where
  roots := #[`Tools.ShippingHierSVRun]

lean_lib «Tools.ShippingMachineDepthChild» where
  roots := #[`Tools.ShippingMachineDepthChild]

lean_lib «Tools.ShippingMachineDepthRun» where
  roots := #[`Tools.ShippingMachineDepthRun]

lean_lib «Tools.ShippingMachineDepthCommand» where
  roots := #[`Tools.ShippingMachineDepthCommand]

lean_lib «Tools.ShippingMachineShipsDepth» where
  roots := #[`Tools.ShippingMachineShipsDepth]

lean_lib «Tools.ShippingHierMono» where
  roots := #[`Tools.ShippingHierMono]

lean_lib «Tools.ShippingHierStateG» where
  roots := #[`Tools.ShippingHierStateG]

lean_lib «Tools.ShippingMachineSeqCommand» where
  roots := #[`Tools.ShippingMachineSeqCommand]

lean_lib «Tools.ShippingMachineCallsLinkedT» where
  roots := #[`Tools.ShippingMachineCallsLinkedT]

lean_lib «Tools.ShippingMachineSeqInst» where
  roots := #[`Tools.ShippingMachineSeqInst]

lean_lib «Tools.ShippingMachineSeqChild» where
  roots := #[`Tools.ShippingMachineSeqChild]

lean_lib «Tools.ShippingMachineCleanup» where
  roots := #[`Tools.ShippingMachineCleanup]

lean_lib «Tools.ShippingMachineMemLinked» where
  roots := #[`Tools.ShippingMachineMemLinked]

lean_lib «Tools.ShippingMachineMemCommand» where
  roots := #[`Tools.ShippingMachineMemCommand]

lean_lib «Tools.ShippingSignOps» where
  roots := #[`Tools.ShippingSignOps]

lean_lib «Tools.ShippingMachineTele» where
  roots := #[`Tools.ShippingMachineTele]

lean_lib «Tools.ShippingMachineTeleNest» where
  roots := #[`Tools.ShippingMachineTeleNest]

lean_lib «Tools.ShippingMachineLoop» where
  roots := #[`Tools.ShippingMachineLoop]

lean_lib «Tools.ShippingMachineLinked» where
  roots := #[`Tools.ShippingMachineLinked]

lean_lib «Tools.ShippingMachineCompose» where
  roots := #[`Tools.ShippingMachineCompose]

lean_lib «Tools.ShippingMachineChild» where
  roots := #[`Tools.ShippingMachineChild]

lean_lib «Tools.ShippingMachineLinkedCommand» where
  roots := #[`Tools.ShippingMachineLinkedCommand]

lean_lib «Tools.ShippingMachineCommand» where
  roots := #[`Tools.ShippingMachineCommand]

lean_lib «Tools.ShippingPipelineSoundness» where
  roots := #[`Tools.ShippingPipelineSoundness]

lean_lib «Tools.ShippingRefineSoundness» where
  roots := #[`Tools.ShippingRefineSoundness]

lean_lib «Tools.ShippingMachineShipping» where
  roots := #[`Tools.ShippingMachineShipping]

lean_lib «Tools.ShippingMemSVSoundness» where
  roots := #[`Tools.ShippingMemSVSoundness]

lean_lib «Tools.ShippingRegisterSoundness» where
  roots := #[`Tools.ShippingRegisterSoundness]

lean_lib «Tools.ShippingUnifiedInvariant» where
  roots := #[`Tools.ShippingUnifiedInvariant]

lean_lib «Tools.ShippingUnifiedCache» where
  roots := #[`Tools.ShippingUnifiedCache]

lean_lib «Tools.ShippingUnifiedMeaning» where
  roots := #[`Tools.ShippingUnifiedMeaning]

lean_lib «Tools.ShippingUnifiedSource» where
  roots := #[`Tools.ShippingUnifiedSource]

lean_lib «Tools.ShippingVectorMuxSoundness» where
  roots := #[`Tools.ShippingVectorMuxSoundness]

lean_lib «Tools.ShippingVectorMuxRecursion» where
  roots := #[`Tools.ShippingVectorMuxRecursion]

lean_lib «Tools.ShippingMixedOutputSoundness» where
  roots := #[`Tools.ShippingMixedOutputSoundness]

lean_lib «Tools.ShippingMixedInputSoundness» where
  roots := #[`Tools.ShippingMixedInputSoundness]

lean_lib «Tools.ShippingMixedEntrySoundness» where
  roots := #[`Tools.ShippingMixedEntrySoundness]

lean_lib «Tools.ShippingMixedGateSoundness» where
  roots := #[`Tools.ShippingMixedGateSoundness]

lean_lib «Tools.ShippingMixedPostSoundness» where
  roots := #[`Tools.ShippingMixedPostSoundness]

lean_lib «Tools.ShippingMixedSourceBridge» where
  roots := #[`Tools.ShippingMixedSourceBridge]

lean_lib «Tools.ShippingMixedExecutionSoundness» where
  roots := #[`Tools.ShippingMixedExecutionSoundness]

lean_lib «Tools.ShippingMixedOrderSoundness» where
  roots := #[`Tools.ShippingMixedOrderSoundness]

lean_lib «Tools.ShippingMixedForwardSoundness» where
  roots := #[`Tools.ShippingMixedForwardSoundness]

lean_lib «Tools.ShippingMixedBindingSoundness» where
  roots := #[`Tools.ShippingMixedBindingSoundness]

lean_lib «Tools.ShippingMixedDeclSoundness» where
  roots := #[`Tools.ShippingMixedDeclSoundness]

lean_lib «Tools.ShippingMixedPrintSoundness» where
  roots := #[`Tools.ShippingMixedPrintSoundness]

lean_lib «Tools.ShippingControlOptSoundness» where
  roots := #[`Tools.ShippingControlOptSoundness]

lean_lib «Tools.ShippingTypedPostSoundness» where
  roots := #[`Tools.ShippingTypedPostSoundness]

lean_lib «Tools.ShippingTypedExprSoundness» where
  roots := #[`Tools.ShippingTypedExprSoundness]

lean_lib «Tools.ShippingExecutionSoundness» where
  roots := #[`Tools.ShippingExecutionSoundness]

lean_lib «Tools.ShippingDeltaSemantics» where
  roots := #[`Tools.ShippingDeltaSemantics]

lean_lib «Tools.ShippingSettledSoundness» where
  roots := #[`Tools.ShippingSettledSoundness]

lean_lib «Tools.ShippingModuleNames» where
  roots := #[`Tools.ShippingModuleNames]

lean_lib «Tools.ShippingNameBinding» where
  roots := #[`Tools.ShippingNameBinding]

lean_lib «Tools.ShippingDeclWidths» where
  roots := #[`Tools.ShippingDeclWidths]

lean_lib «Tools.ShippingPostSoundness» where
  roots := #[`Tools.ShippingPostSoundness]

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

-- CUDA backend Layer 2: emit a `.cu` and syntax-check it with a host C++
-- compiler (no nvcc / no GPU).  Skips cleanly when no compiler is present.
-- Layer 1 (emitter type-check + shape) is `Tests.TestCudaSim` under `lake
-- test`; the opt-in nvcc + GPU run is documented in `docs/CudaSim.md`.
lean_exe «cuda-sim-test» where
  root := `Tests.Drivers.CudaSimTestMain
  supportInterpreter := true

-- CUDA intra backend Layer 3: co-simulate the emitted PE-per-thread kernel
-- against the CSim CPU reference (host side of the same __host__ __device__
-- functions), cycle-exact.  Emission always runs; the compile+run half needs
-- nvcc + a GPU and is gated on SPARKLE_CUDA=1 (skips cleanly otherwise).
lean_exe «cuda-intra-cosim» where
  root := `Tests.Drivers.CudaIntraCosimMain
  supportInterpreter := true

-- SMT bridge Layer 2: emit BMC queries (always), run z3 + replay
-- counterexamples on the CSim C reference when z3/gcc are present
-- (skips cleanly otherwise).  Layer 1 is Tests.TestSmt under lake test.
lean_exe «smt-bmc-test» where
  root := `Tests.Drivers.SmtBmcTestMain
  supportInterpreter := true

-- XiangShan-scale SVParser survey: parse → lower → re-emit over a directory
-- of .sv files, cataloguing failure classes (bench/xiangshan/README.md).
lean_exe «sv-roundtrip» where
  root := `Tests.Drivers.SvRoundtripMain
  supportInterpreter := true

-- Certified-trace census at production scale: which fraction of a
-- corpus do the M4 theorems actually cover (same decidable checkers
-- the capstones consume).
lean_exe «sv-cert-census» where
  root := `Tests.Drivers.SvCertCensusMain
  supportInterpreter := true

-- Phase-2 three-way co-sim: iverilog(original)=golden vs iverilog(roundtrip)
-- vs Sparkle CSim JIT, over baked deterministic vectors.
lean_exe «sv-cosim» where
  root := `Tests.Drivers.SvCosimMain
  supportInterpreter := true

-- sv-to-dsl: survey how much ingested RTL prints back as circuit-DSL
-- source (the reporting half of verilog → IR → lean₄; the proof half is
-- `#verify_dsl_roundtrip`).
lean_exe «sv-to-dsl» where
  root := `Tests.Drivers.SvToDslMain
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

-- Ch14 quoting engine: circuit vs pure-data reference (Signal.val co-sim,
-- incl. both position-limit clamp hits) + 3 synth wrappers at build time.
lean_exe «hft-quote-test» where
  root := `Tests.Drivers.HFTQuoteTestMain
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

-- Regression guard for Issue #107: a `let`-bound stateful
-- @[hardware_module] inside `circuit do` must emit exactly one
-- instance per source instantiation (was E = I·(D+1)).  The
-- asserts run at elaboration time, so `lake build` of this
-- target IS the test.
lean_exe «issue107-letbound-instance-dup-test» where
  root := `Tests.Drivers.Issue107LetBoundInstanceDupMain
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

lean_exe «ecdsa-sign-demo-test» where
  root := `Tests.Drivers.EcdsaSignDemoTestMain
  supportInterpreter := true

lean_exe «tx-policy-test» where
  root := `Tests.Drivers.TxPolicyTestMain
  supportInterpreter := true

lean_exe «keccak256-sponge-test» where
  root := `Tests.Drivers.Keccak256SpongeTestMain
  supportInterpreter := true

-- JIT co-sim: real-cycle validation of the sponge FSM (the block-loop
-- handshake timing the pure-Lean Signal.val interpreter can't reach —
-- see issue #95).  Lowers via #sim → CSim.toCJIT → native, then drives
-- the actual hardware cycle-by-cycle and reads the digest out.
lean_exe «keccak256-sponge-jit-test» where
  root := `Tests.Drivers.Keccak256SpongeJITTestMain
  supportInterpreter := true

-- Fixed-point control datapaths (IIR biquad / PID / LQR).  Each driver runs the
-- cycle-by-cycle sim; the `#synthesizeVerilog` checks live in the test modules
-- and run at `lake build` time.
lean_exe «control-iir-test» where
  root := `Tests.Drivers.ControlIIRBiquadTestMain
  supportInterpreter := true

lean_exe «control-pid-test» where
  root := `Tests.Drivers.ControlPIDTestMain
  supportInterpreter := true

lean_exe «control-lqr-test» where
  root := `Tests.Drivers.ControlLQRTestMain
  supportInterpreter := true

lean_exe «control-precision-sweep» where
  root := `Tests.Drivers.ControlPrecisionSweepTestMain
  supportInterpreter := true

lean_exe «control-observer-test» where
  root := `Tests.Drivers.ControlObserverTestMain
  supportInterpreter := true

lean_exe «control-jit-test» where
  root := `Tests.Drivers.ControlJITTestMain
  supportInterpreter := true

-- Structural lint over emitted RTL (undeclared wires, pinned register /
-- instance counts).  Guards the miscompile class that Lean-side checks and
-- `#synthesizeVerilog` both miss; the run_meta checks fail `lake build`.
lean_exe «rtl-structure-test» where
  root := `Tests.Drivers.RtlStructureTestMain
  supportInterpreter := true

lean_exe «policy-sign-demo-test» where
  root := `Tests.Drivers.PolicySignDemoTestMain
  supportInterpreter := true

lean_exe «ecdsa-sign-small-sim» where
  root := `Tests.Drivers.EcdsaSignSmallSim
  supportInterpreter := true

lean_exe «ecdsa-sign-small-jit» where
  root := `Tests.Drivers.EcdsaSignSmallJIT
  supportInterpreter := true

lean_exe «policy-sign-demo-m2-test» where
  root := `Tests.Drivers.PolicySignDemoM2TestMain
  supportInterpreter := true

lean_exe «ctap2-data-test» where
  root := `Tests.Drivers.CTAP2DataTestMain
  supportInterpreter := true

lean_exe «fido2-demo-test» where
  root := `Tests.Drivers.Fido2DemoTestMain
  supportInterpreter := true

lean_exe «p256-point-jac-test» where
  root := `Tests.Drivers.P256PointJacTestMain
  supportInterpreter := true

lean_exe «p256-point-op-hw-test» where
  root := `Tests.Drivers.P256PointOpHWTestMain
  supportInterpreter := true

lean_exe «p256-scalar-mul-hw-test» where
  root := `Tests.Drivers.P256ScalarMulHWTestMain
  supportInterpreter := true

lean_exe «p256-order-hw-test» where
  root := `Tests.Drivers.P256OrderHWTestMain
  supportInterpreter := true

lean_exe «p256-ecdsa-hw-test» where
  root := `Tests.Drivers.P256ECDSAHWTestMain
  supportInterpreter := true

lean_exe «p256-sign-core-test» where
  root := `Tests.Drivers.P256SignDemoTestMain
  supportInterpreter := true

lean_exe «sha256-stream-test» where
  root := `Tests.Drivers.SHA256StreamTestMain
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


lean_exe «ecdsa-sign-small-jit-dbg» where
  root := `Tests.Drivers.EcdsaSignSmallJITDbg
  supportInterpreter := true

lean_exe «mem-jit-test» where
  root := `Tests.Drivers.MemJITTest
  supportInterpreter := true

lean_exe «rf-jit-test» where
  root := `Tests.Drivers.RfJITTest
  supportInterpreter := true

lean_exe «alu-lite-jit» where
  root := `Tests.Drivers.AluLiteJIT
  supportInterpreter := true

lean_exe «add-jit» where
  root := `Tests.Drivers.AddJIT
  supportInterpreter := true

lean_exe «mul-jit» where
  root := `Tests.Drivers.MulJIT
  supportInterpreter := true

lean_exe «pd-jit» where
  root := `Tests.Drivers.PdJIT
  supportInterpreter := true

lean_exe «addpt-jit» where
  root := `Tests.Drivers.AddPtJIT
  supportInterpreter := true

lean_exe «ladder-jit» where
  root := `Tests.Drivers.LadderJIT
  supportInterpreter := true

lean_exe «dblip-jit» where
  root := `Tests.Drivers.DblIPJIT
  supportInterpreter := true

lean_exe «addip-jit» where
  root := `Tests.Drivers.AddIPJIT
  supportInterpreter := true

lean_exe «exp-jit» where
  root := `Tests.Drivers.ExpJIT
  supportInterpreter := true

lean_exe «sign-jit» where
  root := `Tests.Drivers.SignJIT
  supportInterpreter := true

lean_exe «signcore-jit» where
  root := `Tests.Drivers.SignCoreJIT
  supportInterpreter := true

lean_exe «signdemo-jit» where
  root := `Tests.Drivers.SignDemoJIT
  supportInterpreter := true

lean_exe «sha256stream-jit» where
  root := `Tests.Drivers.Sha256StreamJIT
  supportInterpreter := true

lean_exe «hmac-jit» where
  root := `Tests.Drivers.HmacJIT
  supportInterpreter := true

lean_exe «rfc6979-jit» where
  root := `Tests.Drivers.Rfc6979JIT
  supportInterpreter := true

lean_exe «keccak-sponge-jit» where
  root := `Tests.Drivers.KeccakSpongeJIT
  supportInterpreter := true

lean_exe «keccakf-jit» where
  root := `Tests.Drivers.KeccakFJIT
  supportInterpreter := true

lean_exe «signz-small-jit» where
  root := `Tests.Drivers.SignZSmallJIT
  supportInterpreter := true

lean_exe «signmsg-small-jit» where
  root := `Tests.Drivers.SignMsgSmallJIT
  supportInterpreter := true

lean_exe «signmsg-demo-jit» where
  root := `Tests.Drivers.SignMsgDemoJIT
  supportInterpreter := true

lean_exe «signz-demo-jit» where
  root := `Tests.Drivers.SignZDemoJIT
  supportInterpreter := true

lean_exe «mulmodser-jit» where
  root := `Tests.Drivers.MulModSerJIT
  supportInterpreter := true

lean_lib «Tools.ShippingSeqChildIface» where
  roots := #[`Tools.ShippingSeqChildIface]

lean_lib «Tools.ShippingCallsSeqKids» where
  roots := #[`Tools.ShippingCallsSeqKids]

lean_lib «Tools.ShippingMachineClosesAtGenG» where
  roots := #[`Tools.ShippingMachineClosesAtGenG]

lean_lib «Tools.ShippingLegacySemCalc» where
  roots := #[`Tools.ShippingLegacySemCalc]

lean_lib «Tools.ShippingLegacySemInline» where
  roots := #[`Tools.ShippingLegacySemInline]

lean_lib «Tools.ShippingLegacySemContract» where
  roots := #[`Tools.ShippingLegacySemContract]

lean_lib «Tools.ShippingReaderTerm» where
  roots := #[`Tools.ShippingReaderTerm]

lean_lib «Tools.ShippingReaderInputs» where
  roots := #[`Tools.ShippingReaderInputs]

lean_lib «Tools.ShippingReaderMachine» where
  roots := #[`Tools.ShippingReaderMachine]

lean_lib «Tools.ShippingDesignWithG» where
  roots := #[`Tools.ShippingDesignWithG]

lean_lib «Tools.ShippingCallsKidsD» where
  roots := #[`Tools.ShippingCallsKidsD]

lean_lib «Tools.ShippingClosedKinds» where
  roots := #[`Tools.ShippingClosedKinds]

lean_lib «Tools.ShippingKidsChildIface» where
  roots := #[`Tools.ShippingKidsChildIface]

lean_lib «Tools.ShippingChildIfaceGen» where
  roots := #[`Tools.ShippingChildIfaceGen]

lean_lib «Tools.ShippingReaderComplete» where
  roots := #[`Tools.ShippingReaderComplete]

lean_lib «Tools.ShippingReaderNodes2» where
  roots := #[`Tools.ShippingReaderNodes2]

lean_lib «Tools.ShippingLegacySemDispatch» where
  roots := #[`Tools.ShippingLegacySemDispatch]

lean_lib «Tools.ShippingNameSep» where
  roots := #[`Tools.ShippingNameSep]

lean_lib «Tools.ShippingReaderKinds» where
  roots := #[`Tools.ShippingReaderKinds]

lean_lib «Tools.ShippingReaderComplete2» where
  roots := #[`Tools.ShippingReaderComplete2]

lean_lib «Tools.ShippingLegacySemBody» where
  roots := #[`Tools.ShippingLegacySemBody]

lean_lib «Tools.ShippingLegacySemShim» where
  roots := #[`Tools.ShippingLegacySemShim]

lean_lib «Tools.ShippingLegacySemWalk1» where
  roots := #[`Tools.ShippingLegacySemWalk1]

lean_lib «Tools.ShippingLegacySemUnfold» where
  roots := #[`Tools.ShippingLegacySemUnfold]

lean_lib «Tools.ShippingLegacySemWalk2» where
  roots := #[`Tools.ShippingLegacySemWalk2]

lean_lib «Tools.ShippingLegacySemTrace» where
  roots := #[`Tools.ShippingLegacySemTrace]

lean_lib «Tools.ShippingChecksDerived» where
  roots := #[`Tools.ShippingChecksDerived]

lean_lib «Tools.ShippingLegacySemWalk3» where
  roots := #[`Tools.ShippingLegacySemWalk3]

lean_lib «Tools.ShippingLegacySemWalk4» where
  roots := #[`Tools.ShippingLegacySemWalk4]

lean_lib «Tools.ShippingLegacySemSteps» where
  roots := #[`Tools.ShippingLegacySemSteps]

lean_lib «Tools.ShippingLegacySemUnfoldWalk» where
  roots := #[`Tools.ShippingLegacySemUnfoldWalk]

lean_lib «Tools.ShippingLegacySemChain» where
  roots := #[`Tools.ShippingLegacySemChain]

lean_lib «Tools.ShippingLegacySemBodyPlain» where
  roots := #[`Tools.ShippingLegacySemBodyPlain]

lean_lib «Tools.ShippingChecksDerived2» where
  roots := #[`Tools.ShippingChecksDerived2]

lean_lib «Tools.ShippingChecksDerived3» where
  roots := #[`Tools.ShippingChecksDerived3]

lean_lib «Tools.ShippingChecksPacked» where
  roots := #[`Tools.ShippingChecksPacked]

lean_lib «Tools.ShippingLegacySemSteps2» where
  roots := #[`Tools.ShippingLegacySemSteps2]

lean_lib «Tools.ShippingChecksRun» where
  roots := #[`Tools.ShippingChecksRun]

lean_lib «Tools.ShippingChecksRun2» where
  roots := #[`Tools.ShippingChecksRun2]

lean_lib «Tools.ShippingLegacySemSuffix» where
  roots := #[`Tools.ShippingLegacySemSuffix]

lean_lib «Tools.ShippingLegacySemPre» where
  roots := #[`Tools.ShippingLegacySemPre]

lean_lib «Tools.ShippingLegacySemInstance» where
  roots := #[`Tools.ShippingLegacySemInstance]

lean_lib «Tools.ShippingChecksDepth» where
  roots := #[`Tools.ShippingChecksDepth]

lean_lib «Tools.ShippingChecksCore» where
  roots := #[`Tools.ShippingChecksCore]

lean_lib «Tools.ShippingFinalGoal» where
  roots := #[`Tools.ShippingFinalGoal]

lean_lib «Tools.ShippingFinalGoalCommand» where
  roots := #[`Tools.ShippingFinalGoalCommand]

lean_lib «Tools.ShippingLegacySemEntry» where
  roots := #[`Tools.ShippingLegacySemEntry]

lean_lib «Tools.ShippingLegacySemHarness» where
  roots := #[`Tools.ShippingLegacySemHarness]

lean_lib «Tools.ShippingUnifiedProtectionLeaves» where
  roots := #[`Tools.ShippingUnifiedProtectionLeaves]

lean_lib «Tools.ShippingLegacySemOrder» where
  roots := #[`Tools.ShippingLegacySemOrder]

lean_lib «Tools.ShippingLegacySemEntryWalk» where
  roots := #[`Tools.ShippingLegacySemEntryWalk]

lean_lib «Tools.ShippingLegacySemLeafAt» where
  roots := #[`Tools.ShippingLegacySemLeafAt]

lean_lib «Tools.ShippingLegacySemHarnessAt» where
  roots := #[`Tools.ShippingLegacySemHarnessAt]

lean_lib «Tools.ShippingLegacySemRunIn» where
  roots := #[`Tools.ShippingLegacySemRunIn]

lean_lib «Tools.ShippingLegacySemLeaf» where
  roots := #[`Tools.ShippingLegacySemLeaf]

lean_lib «Tools.ShippingLegacySemMemo» where
  roots := #[`Tools.ShippingLegacySemMemo]

lean_lib «Tools.ShippingLegacySemRunInCalc» where
  roots := #[`Tools.ShippingLegacySemRunInCalc]

lean_lib «Tools.ShippingLegacySemLeaves» where
  roots := #[`Tools.ShippingLegacySemLeaves]

lean_lib «Tools.ShippingLegacySemBinder» where
  roots := #[`Tools.ShippingLegacySemBinder]

lean_lib «Tools.ShippingLegacySemSignalFrame» where
  roots := #[`Tools.ShippingLegacySemSignalFrame]

lean_lib «Tools.ShippingLegacySemEntryIn» where
  roots := #[`Tools.ShippingLegacySemEntryIn]

lean_lib «Tools.ShippingLegacySemEntryOne» where
  roots := #[`Tools.ShippingLegacySemEntryOne]

lean_lib «Tools.ShippingLegacySemFVarArm» where
  roots := #[`Tools.ShippingLegacySemFVarArm]

lean_lib «Tools.ShippingShipsNoOuts» where
  roots := #[`Tools.ShippingShipsNoOuts]

lean_lib «Tools.ShippingShipsNoOutsCommand» where
  roots := #[`Tools.ShippingShipsNoOutsCommand]

lean_lib «Tools.ShippingChecksMasked» where
  roots := #[`Tools.ShippingChecksMasked]

lean_lib «Tools.ShippingReaderApp» where
  roots := #[`Tools.ShippingReaderApp]

lean_lib «Tools.ShippingChecksGate» where
  roots := #[`Tools.ShippingChecksGate]

lean_lib «Tools.ShippingChecksShipsHier» where
  roots := #[`Tools.ShippingChecksShipsHier]

lean_lib «Tools.ShippingChecksRaw» where
  roots := #[`Tools.ShippingChecksRaw]

lean_lib «Tools.ShippingChildIfaceTy» where
  roots := #[`Tools.ShippingChildIfaceTy]

lean_lib «Tools.ShippingChecksExtract» where
  roots := #[`Tools.ShippingChecksExtract]

lean_lib «Tools.ShippingLinkedFresh» where
  roots := #[`Tools.ShippingLinkedFresh]

lean_lib «Tools.ShippingClosedPorts» where
  roots := #[`Tools.ShippingClosedPorts]

lean_lib «Tools.ShippingOutsExtractedParts» where
  roots := #[`Tools.ShippingOutsExtractedParts]

lean_lib «Tools.ShippingChecksOuts» where
  roots := #[`Tools.ShippingChecksOuts]

lean_lib «Tools.ShippingTransitionPortTys» where
  roots := #[`Tools.ShippingTransitionPortTys]

lean_lib «Tools.ShippingInstWidthsParts» where
  roots := #[`Tools.ShippingInstWidthsParts]

lean_lib «Tools.ShippingChecksWidths» where
  roots := #[`Tools.ShippingChecksWidths]

lean_lib «Tools.ShippingShipsHierSame» where
  roots := #[`Tools.ShippingShipsHierSame]

lean_lib «Tools.ShippingCallWidths» where
  roots := #[`Tools.ShippingCallWidths]

lean_lib «Tools.ShippingGuardsSound» where
  roots := #[`Tools.ShippingGuardsSound]

lean_lib «Tools.ShippingShipsHierFree» where
  roots := #[`Tools.ShippingShipsHierFree]

lean_lib «Tools.ShippingChecksRunFacts» where
  roots := #[`Tools.ShippingChecksRunFacts]

lean_lib «Tools.ShippingChecksDepthGate» where
  roots := #[`Tools.ShippingChecksDepthGate]

lean_lib «Tools.ShippingChecksCoreGate» where
  roots := #[`Tools.ShippingChecksCoreGate]

lean_lib «Tools.ShippingShipsFree» where
  roots := #[`Tools.ShippingShipsFree]

lean_lib «Tools.ShippingShipsFreeCommand» where
  roots := #[`Tools.ShippingShipsFreeCommand]

lean_lib «Tools.ShippingClosedMasked» where
  roots := #[`Tools.ShippingClosedMasked]

lean_lib «Tools.ShippingChecksMaskedLeaf» where
  roots := #[`Tools.ShippingChecksMaskedLeaf]

lean_lib «Tools.ShippingShipsFreeMasked» where
  roots := #[`Tools.ShippingShipsFreeMasked]

lean_lib «Tools.ShippingShipsFreeMaskedCommand» where
  roots := #[`Tools.ShippingShipsFreeMaskedCommand]

lean_lib «Tools.ShippingChecksDesign» where
  roots := #[`Tools.ShippingChecksDesign]

lean_lib «Tools.ShippingWidthTables» where
  roots := #[`Tools.ShippingWidthTables]

lean_lib «Tools.ShippingNamesStable» where
  roots := #[`Tools.ShippingNamesStable]

lean_lib «Tools.ShippingNamesNext» where
  roots := #[`Tools.ShippingNamesNext]

lean_lib «Tools.ShippingSeqCheckTyped» where
  roots := #[`Tools.ShippingSeqCheckTyped]

lean_lib «Tools.ShippingNamesClk» where
  roots := #[`Tools.ShippingNamesClk]

lean_lib «Tools.ShippingTextTyped» where
  roots := #[`Tools.ShippingTextTyped]

lean_lib «Tools.ShippingCloseMachineTyped» where
  roots := #[`Tools.ShippingCloseMachineTyped]

lean_lib «Tools.ShippingCoreWidth» where
  roots := #[`Tools.ShippingCoreWidth]

lean_lib «Tools.ShippingTransitionTyped» where
  roots := #[`Tools.ShippingTransitionTyped]

lean_lib «Tools.ShippingClosedTransitionTyped» where
  roots := #[`Tools.ShippingClosedTransitionTyped]

lean_lib «Tools.ShippingClosedTyped» where
  roots := #[`Tools.ShippingClosedTyped]

lean_lib «Tools.ShippingPrintGuard» where
  roots := #[`Tools.ShippingPrintGuard]

lean_lib «Tools.ShippingTextShipped» where
  roots := #[`Tools.ShippingTextShipped]

lean_lib «Tools.ShippingNoDesign» where
  roots := #[`Tools.ShippingNoDesign]

lean_lib «Tools.ShippingNoDesignCommand» where
  roots := #[`Tools.ShippingNoDesignCommand]

lean_lib «Tools.ShippingLeafTyped» where
  roots := #[`Tools.ShippingLeafTyped]

lean_lib «Tools.ShippingKidsPassLeaf» where
  roots := #[`Tools.ShippingKidsPassLeaf]

lean_lib «Tools.ShippingPortsMatchRaw» where
  roots := #[`Tools.ShippingPortsMatchRaw]

lean_lib «Tools.ShippingDesignWriter» where
  roots := #[`Tools.ShippingDesignWriter]

lean_lib «Tools.ShippingDesignWriterRun» where
  roots := #[`Tools.ShippingDesignWriterRun]

lean_lib «Tools.ShippingNoKids» where
  roots := #[`Tools.ShippingNoKids]

lean_lib «Tools.ShippingNoKidsCommand» where
  roots := #[`Tools.ShippingNoKidsCommand]

lean_lib «Tools.ShippingOptimizePorts» where
  roots := #[`Tools.ShippingOptimizePorts]

lean_lib «Tools.ShippingPortsMatchShipped» where
  roots := #[`Tools.ShippingPortsMatchShipped]

lean_lib «Tools.ShippingPortWidthsPure» where
  roots := #[`Tools.ShippingPortWidthsPure]

lean_lib «Tools.ShippingLeafPorts» where
  roots := #[`Tools.ShippingLeafPorts]

lean_lib «Tools.ShippingCoreClk» where
  roots := #[`Tools.ShippingCoreClk]

lean_lib «Tools.ShippingPortsMatchRawLeaf» where
  roots := #[`Tools.ShippingPortsMatchRawLeaf]

lean_lib «Tools.ShippingCallCast» where
  roots := #[`Tools.ShippingCallCast]

lean_lib «Tools.ShippingLegacySemThrows» where
  roots := #[`Tools.ShippingLegacySemThrows]

lean_lib «Tools.ShippingLegacySemBinderBound» where
  roots := #[`Tools.ShippingLegacySemBinderBound]

lean_lib «Tools.ShippingLegacySemEntryBound» where
  roots := #[`Tools.ShippingLegacySemEntryBound]

lean_lib «Tools.ShippingLegacySemHarnessLeaf» where
  roots := #[`Tools.ShippingLegacySemHarnessLeaf]

lean_lib «Tools.ShippingLegacySemBinderList» where
  roots := #[`Tools.ShippingLegacySemBinderList]

lean_lib «Tools.ShippingLegacySemEntryList» where
  roots := #[`Tools.ShippingLegacySemEntryList]

lean_lib «Tools.ShippingLegacySemTelescopeN» where
  roots := #[`Tools.ShippingLegacySemTelescopeN]

lean_lib «Tools.ShippingLegacySemLeafHandled» where
  roots := #[`Tools.ShippingLegacySemLeafHandled]

lean_lib «Tools.ShippingLegacySemBinderListD» where
  roots := #[`Tools.ShippingLegacySemBinderListD]

lean_lib «Tools.ShippingLegacySemEntryListD» where
  roots := #[`Tools.ShippingLegacySemEntryListD]

lean_lib «Tools.ShippingLegacySemBeta» where
  roots := #[`Tools.ShippingLegacySemBeta]

lean_lib «Tools.ShippingLegacySemTelescopeLams» where
  roots := #[`Tools.ShippingLegacySemTelescopeLams]

lean_lib «Tools.ShippingLegacySemInputAt» where
  roots := #[`Tools.ShippingLegacySemInputAt]

lean_lib «Tools.ShippingLegacySemProj» where
  roots := #[`Tools.ShippingLegacySemProj]

lean_lib «Tools.ShippingLegacySemPacked» where
  roots := #[`Tools.ShippingLegacySemPacked]

lean_lib «Tools.ShippingLegacySemFst» where
  roots := #[`Tools.ShippingLegacySemFst]

lean_lib «Tools.ShippingLegacySemFstArm» where
  roots := #[`Tools.ShippingLegacySemFstArm]

lean_lib «Tools.ShippingLegacySemSliceEmit» where
  roots := #[`Tools.ShippingLegacySemSliceEmit]

lean_lib «Tools.ShippingLegacySemFstEntry» where
  roots := #[`Tools.ShippingLegacySemFstEntry]

lean_lib «Tools.ShippingLegacySemTupleEntry» where
  roots := #[`Tools.ShippingLegacySemTupleEntry]

lean_lib «Tools.ShippingLegacySemPackedField» where
  roots := #[`Tools.ShippingLegacySemPackedField]

lean_lib «Tools.ShippingMemoLaws» where
  roots := #[`Tools.ShippingMemoLaws]

lean_lib «Tools.ShippingMemoInv» where
  roots := #[`Tools.ShippingMemoInv]

lean_lib «Tools.ShippingLegacySemMemoWalk» where
  roots := #[`Tools.ShippingLegacySemMemoWalk]

lean_lib «Tools.ShippingMemoLawsWith» where
  roots := #[`Tools.ShippingMemoLawsWith]

lean_lib «Tools.ShippingLegacySemMemoOuter» where
  roots := #[`Tools.ShippingLegacySemMemoOuter]

lean_lib «Tools.ShippingPortsMatchShippedLeaf» where
  roots := #[`Tools.ShippingPortsMatchShippedLeaf]

lean_lib «Tools.ShippingNoPorts» where
  roots := #[`Tools.ShippingNoPorts]

lean_lib «Tools.ShippingNoPortsCommand» where
  roots := #[`Tools.ShippingNoPortsCommand]

lean_lib «Tools.ShippingCallShadow» where
  roots := #[`Tools.ShippingCallShadow]

lean_lib «Tools.ShippingCallWidthsStrict» where
  roots := #[`Tools.ShippingCallWidthsStrict]

lean_lib «Tools.ShippingHierGateAny» where
  roots := #[`Tools.ShippingHierGateAny]

lean_lib «Tools.ShippingCombKidText» where
  roots := #[`Tools.ShippingCombKidText]

lean_lib «Tools.ShippingPortsMatchRawLeafAny» where
  roots := #[`Tools.ShippingPortsMatchRawLeafAny]

lean_lib «Tools.ShippingInstSignature» where
  roots := #[`Tools.ShippingInstSignature]

lean_lib «Tools.ShippingReaderResultKind» where
  roots := #[`Tools.ShippingReaderResultKind]

lean_lib «Tools.ShippingMachineShapeUnfold» where
  roots := #[`Tools.ShippingMachineShapeUnfold]

lean_lib «Tools.ShippingMachineShapeTail» where
  roots := #[`Tools.ShippingMachineShapeTail]

lean_lib «Tools.ShippingShapeDecomp» where
  roots := #[`Tools.ShippingShapeDecomp]

lean_lib «Tools.ShippingCallWidthsDeclared» where
  roots := #[`Tools.ShippingCallWidthsDeclared]

lean_lib «Tools.ShippingReaderLenOk» where
  roots := #[`Tools.ShippingReaderLenOk]

lean_lib «Tools.ShippingR5Check» where
  roots := #[`Tools.ShippingR5Check]

lean_lib «Tools.ShippingCallWidthsEntry» where
  roots := #[`Tools.ShippingCallWidthsEntry]

lean_lib «Tools.ShippingReaderLenOkReserve» where
  roots := #[`Tools.ShippingReaderLenOkReserve]

lean_lib «Tools.ShippingOneOutClose» where
  roots := #[`Tools.ShippingOneOutClose]

lean_lib «Tools.ShippingOneOutFacts» where
  roots := #[`Tools.ShippingOneOutFacts]

lean_lib «Tools.ShippingOneOutHead» where
  roots := #[`Tools.ShippingOneOutHead]

lean_lib «Tools.ShippingOneOutSameRun» where
  roots := #[`Tools.ShippingOneOutSameRun]

lean_lib «Tools.ShippingOneOutCommand» where
  roots := #[`Tools.ShippingOneOutCommand]

lean_lib «Tools.ShippingTypedWidthOk» where
  roots := #[`Tools.ShippingTypedWidthOk]

lean_lib «Tools.ShippingGatePorts» where
  roots := #[`Tools.ShippingGatePorts]

lean_lib «Tools.ShippingOneOutConns» where
  roots := #[`Tools.ShippingOneOutConns]

lean_lib «Tools.ShippingOneOutFullCommand» where
  roots := #[`Tools.ShippingOneOutFullCommand]

lean_lib «Tools.ShippingOneOutGenCommand» where
  roots := #[`Tools.ShippingOneOutGenCommand]

lean_lib «Tools.ShippingLeafOneOut» where
  roots := #[`Tools.ShippingLeafOneOut]

lean_lib «Tools.ShippingLeafOneOutGen» where
  roots := #[`Tools.ShippingLeafOneOutGen]

lean_lib «Tools.ShippingOneOutAnyGenCommand» where
  roots := #[`Tools.ShippingOneOutAnyGenCommand]

lean_lib «Tools.ShippingChildMapCongr» where
  roots := #[`Tools.ShippingChildMapCongr]

lean_lib «Tools.ShippingKidsSelf» where
  roots := #[`Tools.ShippingKidsSelf]

lean_lib «Tools.ShippingCallsChildPorts» where
  roots := #[`Tools.ShippingCallsChildPorts]

lean_lib «Tools.ShippingKidFacts» where
  roots := #[`Tools.ShippingKidFacts]

lean_lib «Tools.ShippingOneOutKid» where
  roots := #[`Tools.ShippingOneOutKid]

lean_lib «Tools.ShippingBoundaryClose» where
  roots := #[`Tools.ShippingBoundaryClose]

lean_lib «Tools.ShippingLeafKidFacts» where
  roots := #[`Tools.ShippingLeafKidFacts]

lean_lib «Tools.ShippingNoPortsKidsCommand» where
  roots := #[`Tools.ShippingNoPortsKidsCommand]

lean_lib «Tools.ShippingCallsPortsG» where
  roots := #[`Tools.ShippingCallsPortsG]

lean_lib «Tools.ShippingGenKid» where
  roots := #[`Tools.ShippingGenKid]

lean_lib «Tools.ShippingOneOutKidDepth» where
  roots := #[`Tools.ShippingOneOutKidDepth]

lean_lib «Tools.ShippingNoPortsDeepCommand» where
  roots := #[`Tools.ShippingNoPortsDeepCommand]

lean_lib «Tools.ShippingMemKidCore» where
  roots := #[`Tools.ShippingMemKidCore]

lean_lib «Tools.ShippingMemKidPorts» where
  roots := #[`Tools.ShippingMemKidPorts]

lean_lib «Tools.ShippingMemKidFacts» where
  roots := #[`Tools.ShippingMemKidFacts]

lean_lib «Tools.ShippingCallsRunFinal» where
  roots := #[`Tools.ShippingCallsRunFinal]

lean_lib «Tools.ShippingCallsKidsS» where
  roots := #[`Tools.ShippingCallsKidsS]

lean_lib «Tools.ShippingCallsKidsSGen» where
  roots := #[`Tools.ShippingCallsKidsSGen]

lean_lib «Tools.ShippingMemOnly» where
  roots := #[`Tools.ShippingMemOnly]

lean_lib «Tools.ShippingMemClosesRun» where
  roots := #[`Tools.ShippingMemClosesRun]

lean_lib «Tools.ShippingMemClosesKids» where
  roots := #[`Tools.ShippingMemClosesKids]

lean_lib «Tools.ShippingMemClosesKidsT» where
  roots := #[`Tools.ShippingMemClosesKidsT]

lean_lib «Tools.ShippingGateChildIfaceP» where
  roots := #[`Tools.ShippingGateChildIfaceP]

lean_lib «Tools.ShippingMemOnlyAtAll» where
  roots := #[`Tools.ShippingMemOnlyAtAll]

lean_lib «Tools.ShippingMemOnlyCloses» where
  roots := #[`Tools.ShippingMemOnlyCloses]

lean_lib «Tools.ShippingCoreFromM» where
  roots := #[`Tools.ShippingCoreFromM]

lean_lib «Tools.ShippingCoreFromMPorts» where
  roots := #[`Tools.ShippingCoreFromMPorts]

lean_lib «Tools.ShippingSlotlessClk» where
  roots := #[`Tools.ShippingSlotlessClk]

lean_lib «Tools.ShippingSlotlessKidFacts» where
  roots := #[`Tools.ShippingSlotlessKidFacts]

lean_lib «Tools.ShippingNoPortsSlotlessCommand» where
  roots := #[`Tools.ShippingNoPortsSlotlessCommand]

lean_lib «Tools.ShippingMemTransport» where
  roots := #[`Tools.ShippingMemTransport]

lean_lib «Tools.ShippingLeafEntry» where
  roots := #[`Tools.ShippingLeafEntry]

lean_lib «Tools.ShippingLeafEntryBnd» where
  roots := #[`Tools.ShippingLeafEntryBnd]

lean_lib «Tools.ShippingNoPortsMemCommand» where
  roots := #[`Tools.ShippingNoPortsMemCommand]
lean_lib «Tools.ShippingGuardsLeaf» where
  roots := #[`Tools.ShippingGuardsLeaf]

lean_lib «Tools.ShippingCacheCoherent» where
  roots := #[`Tools.ShippingCacheCoherent]

lean_lib «Tools.ShippingLeafEntryCommand» where
  roots := #[`Tools.ShippingLeafEntryCommand]

lean_lib «Tools.ShippingMergeKeeps» where
  roots := #[`Tools.ShippingMergeKeeps]

lean_lib «Tools.ShippingMergeKeepsBridge» where
  roots := #[`Tools.ShippingMergeKeepsBridge]

lean_lib «Tools.ShippingMergeKeepsCheck» where
  roots := #[`Tools.ShippingMergeKeepsCheck]

lean_lib «Tools.ShippingMergeKeepsLeaf» where
  roots := #[`Tools.ShippingMergeKeepsLeaf]

lean_lib «Tools.ShippingNoPortsMemSeqCommand» where
  roots := #[`Tools.ShippingNoPortsMemSeqCommand]

lean_lib «Tools.ShippingKid» where
  roots := #[`Tools.ShippingKid]

lean_lib «Tools.ShippingLeafDesign» where
  roots := #[`Tools.ShippingLeafDesign]

lean_lib «Tools.ShippingLeafDesignCommand» where
  roots := #[`Tools.ShippingLeafDesignCommand]

lean_lib «Tools.ShippingModuleName» where
  roots := #[`Tools.ShippingModuleName]

lean_lib «Tools.ShippingNameDischarge» where
  roots := #[`Tools.ShippingNameDischarge]

lean_lib «Tools.ShippingMemOnlyNames» where
  roots := #[`Tools.ShippingMemOnlyNames]

lean_lib «Tools.ShippingClosesNames» where
  roots := #[`Tools.ShippingClosesNames]

lean_lib «Tools.ShippingCacheCoherentRun» where
  roots := #[`Tools.ShippingCacheCoherentRun]

lean_lib «Tools.ShippingCacheCoherentClose» where
  roots := #[`Tools.ShippingCacheCoherentClose]

lean_lib «Tools.ShippingNameMode» where
  roots := #[`Tools.ShippingNameMode]

lean_lib «Tools.ShippingMemSeqNames» where
  roots := #[`Tools.ShippingMemSeqNames]

lean_lib «Tools.ShippingCacheCoherentCert» where
  roots := #[`Tools.ShippingCacheCoherentCert]

lean_lib «Tools.ShippingCacheCoherentData» where
  roots := #[`Tools.ShippingCacheCoherentData]

lean_lib «Tools.ShippingLeafSweepCommand» where
  roots := #[`Tools.ShippingLeafSweepCommand]

lean_lib «Tools.ShippingCacheCoherentVia» where
  roots := #[`Tools.ShippingCacheCoherentVia]

lean_lib «Tools.ShippingLeafSweepExpect» where
  roots := #[`Tools.ShippingLeafSweepExpect]

lean_lib «Tools.ShippingCombLeafDesign» where
  roots := #[`Tools.ShippingCombLeafDesign]

lean_lib «Tools.ShippingCombLeafCommand» where
  roots := #[`Tools.ShippingCombLeafCommand]

lean_lib «Tools.ShippingWalkStill» where
  roots := #[`Tools.ShippingWalkStill]

lean_lib «Tools.ShippingCastMerge» where
  roots := #[`Tools.ShippingCastMerge]

lean_lib «Tools.ShippingCombLeafShape» where
  roots := #[`Tools.ShippingCombLeafShape]

lean_lib «Tools.ShippingCombLeafClosedCommand» where
  roots := #[`Tools.ShippingCombLeafClosedCommand]

lean_lib «Tools.ShippingHarnessStill» where
  roots := #[`Tools.ShippingHarnessStill]

lean_lib «Tools.ShippingCombLeafClosedExpect» where
  roots := #[`Tools.ShippingCombLeafClosedExpect]

lean_lib «Tools.ShippingDesignCoverage» where
  roots := #[`Tools.ShippingDesignCoverage]

lean_lib «Tools.ShippingCacheCoherentOuter» where
  roots := #[`Tools.ShippingCacheCoherentOuter]

lean_lib «Tools.ShippingDetReduce» where
  roots := #[`Tools.ShippingDetReduce]

lean_lib «Tools.ShippingGateDesign» where
  roots := #[`Tools.ShippingGateDesign]

lean_lib «Tools.ShippingGateDesignCommand» where
  roots := #[`Tools.ShippingGateDesignCommand]

lean_lib «Tools.ShippingNoRepeat» where
  roots := #[`Tools.ShippingNoRepeat]

lean_lib «Tools.ShippingGateSource» where
  roots := #[`Tools.ShippingGateSource]

lean_lib «Tools.ShippingGateSourceCommand» where
  roots := #[`Tools.ShippingGateSourceCommand]

lean_lib «Tools.ShippingHierRunTotal» where
  roots := #[`Tools.ShippingHierRunTotal]

lean_lib «Tools.ShippingCorpusSweep» where
  roots := #[`Tools.ShippingCorpusSweep]

lean_lib «Tools.ShippingWalkGrow» where
  roots := #[`Tools.ShippingWalkGrow]

lean_lib «Tools.ShippingInstanceTag» where
  roots := #[`Tools.ShippingInstanceTag]

lean_lib «Tools.ShippingWalkStillMore» where
  roots := #[`Tools.ShippingWalkStillMore]

lean_lib «Tools.ShippingFragCensus» where
  roots := #[`Tools.ShippingFragCensus]

lean_lib «Tools.ShippingEntryOkCommand» where
  roots := #[`Tools.ShippingEntryOkCommand]

lean_lib «Tools.ShippingMachineLoopCausal» where
  roots := #[`Tools.ShippingMachineLoopCausal]

lean_lib «Tools.ShippingEntryOkWide» where
  roots := #[`Tools.ShippingEntryOkWide]

lean_lib «Tools.ShippingMachineRan» where
  roots := #[`Tools.ShippingMachineRan]

lean_lib «Tools.ShippingMachineLoopJoint» where
  roots := #[`Tools.ShippingMachineLoopJoint]

lean_lib «Tools.ShippingMachineLoopCausalCommand» where
  roots := #[`Tools.ShippingMachineLoopCausalCommand]

lean_lib «Tools.ShippingMachineDepthMemKidCommand» where
  roots := #[`Tools.ShippingMachineDepthMemKidCommand]

lean_lib «Tools.ShippingKidsChildIfaceM» where
  roots := #[`Tools.ShippingKidsChildIfaceM]

lean_lib «Tools.ShippingMachineDepthMemKidRunCommand» where
  roots := #[`Tools.ShippingMachineDepthMemKidRunCommand]

lean_lib «Tools.ShippingMemNamesP» where
  roots := #[`Tools.ShippingMemNamesP]

lean_lib «Tools.ShippingKidFactsT» where
  roots := #[`Tools.ShippingKidFactsT]

lean_lib «Tools.ShippingCallSelf» where
  roots := #[`Tools.ShippingCallSelf]

lean_lib «Tools.ShippingGenKidT» where
  roots := #[`Tools.ShippingGenKidT]

lean_lib «Tools.ShippingGenKidM» where
  roots := #[`Tools.ShippingGenKidM]

lean_lib «Tools.ShippingBndOnly» where
  roots := #[`Tools.ShippingBndOnly]

lean_lib «Tools.ShippingMemKidTags» where
  roots := #[`Tools.ShippingMemKidTags]

lean_lib «Tools.ShippingNoPortsMemKidCommand» where
  roots := #[`Tools.ShippingNoPortsMemKidCommand]

lean_lib «Tools.ShippingNoPortsMemKidSweep» where
  roots := #[`Tools.ShippingNoPortsMemKidSweep]

lean_lib «Tools.ShippingMachineRanBase» where
  roots := #[`Tools.ShippingMachineRanBase]

lean_lib «Tools.ShippingKidFactsRan» where
  roots := #[`Tools.ShippingKidFactsRan]

lean_lib «Tools.ShippingMachineSeqLinkedRan» where
  roots := #[`Tools.ShippingMachineSeqLinkedRan]

lean_lib «Tools.ShippingOutermost» where
  roots := #[`Tools.ShippingOutermost]

lean_lib «Tools.ShippingOutermostCommand» where
  roots := #[`Tools.ShippingOutermostCommand]

lean_lib «Tools.ShippingOutermostCoverage» where
  roots := #[`Tools.ShippingOutermostCoverage]

lean_lib «Tools.ShippingReaderProjChain» where
  roots := #[`Tools.ShippingReaderProjChain]

lean_lib «Tools.ShippingReaderProjChainShadow» where
  roots := #[`Tools.ShippingReaderProjChainShadow]

lean_lib «Tools.ShippingReaderProjChainFold» where
  roots := #[`Tools.ShippingReaderProjChainFold]

lean_lib «Tools.ShippingReaderMatcherArity» where
  roots := #[`Tools.ShippingReaderMatcherArity]

lean_lib «Tools.ShippingReaderMatcherArityUnique» where
  roots := #[`Tools.ShippingReaderMatcherArityUnique]

lean_lib «Tools.ShippingReaderSweepCommon» where
  roots := #[`Tools.ShippingReaderSweepCommon]

lean_lib «Tools.ShippingReaderMatcherArityShadow» where
  roots := #[`Tools.ShippingReaderMatcherArityShadow]

lean_lib «Tools.ShippingReaderInstTy» where
  roots := #[`Tools.ShippingReaderInstTy]

lean_lib «Tools.ShippingReaderInstTyShadow» where
  roots := #[`Tools.ShippingReaderInstTyShadow]

lean_lib «Tools.ShippingReaderBoolMap» where
  roots := #[`Tools.ShippingReaderBoolMap]

lean_lib «Tools.ShippingReaderBoolMapLeaf» where
  roots := #[`Tools.ShippingReaderBoolMapLeaf]

lean_lib «Tools.ShippingReaderBoolMapShadow» where
  roots := #[`Tools.ShippingReaderBoolMapShadow]

-- A tagged instance member through the real JIT loader (Lean FFI), alone
lean_exe «tagged-jit-e2e-test» where
  root := `Tests.Drivers.TaggedJitE2EMain
  supportInterpreter := true

lean_lib «Tools.ShippingReaderProjChainReal» where
  roots := #[`Tools.ShippingReaderProjChainReal]

lean_lib «Tools.ShippingReaderProjChainResult» where
  roots := #[`Tools.ShippingReaderProjChainResult]

lean_lib «Tools.ShippingReaderProjChainArm» where
  roots := #[`Tools.ShippingReaderProjChainArm]

lean_lib «Tools.ShippingReaderRawNodeArm» where
  roots := #[`Tools.ShippingReaderRawNodeArm]

lean_lib «Tools.ShippingSparseCasesTac» where
  roots := #[`Tools.ShippingSparseCasesTac]

lean_lib «Tools.ShippingReaderMatcherArityArray» where
  roots := #[`Tools.ShippingReaderMatcherArityArray]

lean_lib «Tools.ShippingReaderMatcherArityReal» where
  roots := #[`Tools.ShippingReaderMatcherArityReal]

lean_lib «Tools.ShippingReaderRawNodeCanon» where
  roots := #[`Tools.ShippingReaderRawNodeCanon]

lean_lib «Tools.ShippingReaderMatcherArityOldShadow» where
  roots := #[`Tools.ShippingReaderMatcherArityOldShadow]

lean_lib «Tools.ShippingGateParentRuns» where
  roots := #[`Tools.ShippingGateParentRuns]

lean_lib «Tools.ShippingGateParentTail» where
  roots := #[`Tools.ShippingGateParentTail]

lean_lib «Tools.ShippingGateParentPost» where
  roots := #[`Tools.ShippingGateParentPost]

lean_lib «Tools.ShippingGateParentRun» where
  roots := #[`Tools.ShippingGateParentRun]

lean_lib «Tools.ShippingGateDefines» where
  roots := #[`Tools.ShippingGateDefines]

lean_lib «Tools.ShippingGateParentRunG» where
  roots := #[`Tools.ShippingGateParentRunG]

lean_lib «Tools.ShippingGateConeLeafRuns» where
  roots := #[`Tools.ShippingGateConeLeafRuns]

lean_lib «Tools.ShippingGateConeLeafContract» where
  roots := #[`Tools.ShippingGateConeLeafContract]

lean_lib «Tools.ShippingGateConeW» where
  roots := #[`Tools.ShippingGateConeW]

lean_lib «Tools.ShippingGateConeRun» where
  roots := #[`Tools.ShippingGateConeRun]

lean_lib «Tools.ShippingGateConeTag» where
  roots := #[`Tools.ShippingGateConeTag]

lean_lib «Tools.ShippingFirstGateChild» where
  roots := #[`Tools.ShippingFirstGateChild]

lean_lib «Tools.ShippingFirstGateKid» where
  roots := #[`Tools.ShippingFirstGateKid]

lean_lib «Tools.ShippingGateConeEntry» where
  roots := #[`Tools.ShippingGateConeEntry]

lean_lib «Tools.ShippingGateConeCompare» where
  roots := #[`Tools.ShippingGateConeCompare]

lean_lib «Tools.ShippingGateConeRunC» where
  roots := #[`Tools.ShippingGateConeRunC]

lean_lib «Tools.ShippingGateConeBoolNot» where
  roots := #[`Tools.ShippingGateConeBoolNot]

lean_lib «Tools.ShippingGateConeBoolBin» where
  roots := #[`Tools.ShippingGateConeBoolBin]

lean_lib «Tools.ShippingGateConeBoolEq» where
  roots := #[`Tools.ShippingGateConeBoolEq]

lean_lib «Tools.ShippingGateConeMux» where
  roots := #[`Tools.ShippingGateConeMux]

lean_lib «Tools.ShippingGateConeVecMux» where
  roots := #[`Tools.ShippingGateConeVecMux]

lean_lib «Tools.ShippingGateConeRunC6» where
  roots := #[`Tools.ShippingGateConeRunC6]

lean_lib «Tools.ShippingGateConeEntryC» where
  roots := #[`Tools.ShippingGateConeEntryC]

lean_lib «Tools.ShippingGateConeInstArgsW» where
  roots := #[`Tools.ShippingGateConeInstArgsW]

lean_lib «Tools.ShippingGateConeNested» where
  roots := #[`Tools.ShippingGateConeNested]

lean_lib «Tools.ShippingGateDesignLift» where
  roots := #[`Tools.ShippingGateDesignLift]

lean_lib «Tools.ShippingRefineNoRst» where
  roots := #[`Tools.ShippingRefineNoRst]

lean_lib «Tools.ShippingHierOptRunHNoRst» where
  roots := #[`Tools.ShippingHierOptRunHNoRst]

lean_lib «Tools.ShippingGateOptComb» where
  roots := #[`Tools.ShippingGateOptComb]
lean_lib «Tools.ShippingGateDesignWalk» where
  roots := #[`Tools.ShippingGateDesignWalk]

lean_lib «Tools.ShippingGateDesignRun» where
  roots := #[`Tools.ShippingGateDesignRun]

lean_lib «Tools.ShippingGateDesignPost» where
  roots := #[`Tools.ShippingGateDesignPost]

lean_lib «Tools.ShippingCIdent» where
  roots := #[`Tools.ShippingCIdent]

lean_lib «Tools.ShippingInstArmGrow» where
  roots := #[`Tools.ShippingInstArmGrow]

lean_lib «Tools.ShippingGateOutPort» where
  roots := #[`Tools.ShippingGateOutPort]

lean_lib «Tools.ShippingGateCombSide» where
  roots := #[`Tools.ShippingGateCombSide]

lean_lib «Tools.ShippingGateNamesWalk» where
  roots := #[`Tools.ShippingGateNamesWalk]

lean_lib «Tools.ShippingGateNamesFinal» where
  roots := #[`Tools.ShippingGateNamesFinal]

lean_lib «Tools.ShippingFirstGateKidText» where
  roots := #[`Tools.ShippingFirstGateKidText]

lean_lib «Tools.ShippingGateTypedWalk» where
  roots := #[`Tools.ShippingGateTypedWalk]

lean_lib «Tools.ShippingFirstGatePorts» where
  roots := #[`Tools.ShippingFirstGatePorts]

lean_lib «Tools.ShippingGateTypedFinal» where
  roots := #[`Tools.ShippingGateTypedFinal]

lean_lib «Tools.ShippingGateDesignAll» where
  roots := #[`Tools.ShippingGateDesignAll]
lean_lib «Tools.ShippingReaderOutsInv» where
  roots := #[`Tools.ShippingReaderOutsInv]

lean_lib «Tools.ShippingReaderOutsMemOnly» where
  roots := #[`Tools.ShippingReaderOutsMemOnly]
lean_lib «Tools.ShippingInstanceMeaningP» where
  roots := #[`Tools.ShippingInstanceMeaningP]

lean_lib «Tools.ShippingReaderMemOnlyCloses» where
  roots := #[`Tools.ShippingReaderMemOnlyCloses]

lean_lib «Tools.ShippingReaderOutNames» where
  roots := #[`Tools.ShippingReaderOutNames]
lean_lib «Tools.ShippingGateConeLeafContractE» where
  roots := #[`Tools.ShippingGateConeLeafContractE]

lean_lib «Tools.ShippingGateKid» where
  roots := #[`Tools.ShippingGateKid]

lean_lib «Tools.ShippingGateCoverage» where
  roots := #[`Tools.ShippingGateCoverage]
lean_lib «Tools.ShippingGateWalkE» where
  roots := #[`Tools.ShippingGateWalkE]

lean_lib «Tools.ShippingGateTypedFinalI» where
  roots := #[`Tools.ShippingGateTypedFinalI]

lean_lib «Tools.ReaderFuelGeneric» where
  roots := #[`Tools.ReaderFuelGeneric]
lean_lib «Tools.ShippingReaderFuelDefs» where
  roots := #[`Tools.ShippingReaderFuelDefs]

lean_lib «Tools.ShippingReaderFuelKleene» where
  roots := #[`Tools.ShippingReaderFuelKleene]

lean_lib «Tools.ShippingReaderFuelEval» where
  roots := #[`Tools.ShippingReaderFuelEval]
lean_lib «Tools.ShippingReaderFuelShape» where
  roots := #[`Tools.ShippingReaderFuelShape]

lean_lib «Tools.ShippingReaderFuelDriver» where
  roots := #[`Tools.ShippingReaderFuelDriver]
lean_lib «Tools.ShippingReaderFuelRun» where
  roots := #[`Tools.ShippingReaderFuelRun]

lean_lib «Tools.ShippingReaderFuelR5» where
  roots := #[`Tools.ShippingReaderFuelR5]

lean_lib «Tools.ShippingReaderFuelOldEq» where
  roots := #[`Tools.ShippingReaderFuelOldEq]

lean_lib «Tools.ShippingReaderFuelVerbatim» where
  roots := #[`Tools.ShippingReaderFuelVerbatim]

lean_lib «Tools.ShippingReaderFuelDriverComplete» where
  roots := #[`Tools.ShippingReaderFuelDriverComplete]
lean_lib «Tools.ShippingReaderFuelShapeR5» where
  roots := #[`Tools.ShippingReaderFuelShapeR5]

lean_lib «Tools.ShippingCallWidthsEntryF» where
  roots := #[`Tools.ShippingCallWidthsEntryF]

lean_lib «Tools.ShippingReaderFuelShapeEval» where
  roots := #[`Tools.ShippingReaderFuelShapeEval]
lean_lib «Tools.ShippingReaderFuelDriverResume» where
  roots := #[`Tools.ShippingReaderFuelDriverResume]
lean_lib «Tools.ShippingCallWidthsEntryFH» where
  roots := #[`Tools.ShippingCallWidthsEntryFH]

lean_lib «Tools.ShippingReaderFuelR1» where
  roots := #[`Tools.ShippingReaderFuelR1]

lean_lib «Tools.ShippingReaderFuelShapeR1» where
  roots := #[`Tools.ShippingReaderFuelShapeR1]

lean_lib «Tools.ShippingCallWidthsEntryFR1» where
  roots := #[`Tools.ShippingCallWidthsEntryFR1]

lean_lib «Tools.ShippingReaderFuelProv» where
  roots := #[`Tools.ShippingReaderFuelProv]

lean_lib «Tools.ShippingReaderFuelShapeProv» where
  roots := #[`Tools.ShippingReaderFuelShapeProv]

lean_lib «Tools.ShippingCallWidthsEntryFM» where
  roots := #[`Tools.ShippingCallWidthsEntryFM]

lean_lib «Tools.ShippingReaderFuelResumeEval» where
  roots := #[`Tools.ShippingReaderFuelResumeEval]

lean_lib «Tools.ShippingMemDispatch» where
  roots := #[`Tools.ShippingMemDispatch]
lean_lib «Tools.ShippingCallWidthsChildReal» where
  roots := #[`Tools.ShippingCallWidthsChildReal]

lean_lib «Tools.ShippingCallWidthsStructLink» where
  roots := #[`Tools.ShippingCallWidthsStructLink]

lean_lib «Tools.ShippingCallWidthsStructExist» where
  roots := #[`Tools.ShippingCallWidthsStructExist]

lean_lib «Tools.ShippingCallWidthsStructRes» where
  roots := #[`Tools.ShippingCallWidthsStructRes]

lean_lib «Tools.ShippingCallWidthsTagObl» where
  roots := #[`Tools.ShippingCallWidthsTagObl]

lean_lib «Tools.ShippingInstTagged» where
  roots := #[`Tools.ShippingInstTagged]

lean_lib «Tools.ShippingInstSubstModel» where
  roots := #[`Tools.ShippingInstSubstModel]

lean_lib «Tools.ShippingEnvRead» where
  roots := #[`Tools.ShippingEnvRead]

lean_lib «Tools.ShippingEnvLocal» where
  roots := #[`Tools.ShippingEnvLocal]

lean_lib «Tools.ShippingEnvLocalP5S» where
  roots := #[`Tools.ShippingEnvLocalP5S]

lean_lib «Tools.ShippingKidsMixedC» where
  roots := #[`Tools.ShippingKidsMixedC]

lean_lib «Tools.ShippingGateKidFactsT» where
  roots := #[`Tools.ShippingGateKidFactsT]

lean_lib «Tools.ShippingInlCand» where
  roots := #[`Tools.ShippingInlCand]

lean_lib «Tools.ShippingInlTypeFacts» where
  roots := #[`Tools.ShippingInlTypeFacts]

lean_lib «Tools.ShippingInlTypeReads» where
  roots := #[`Tools.ShippingInlTypeReads]

lean_lib «Tools.ShippingP5Forall» where
  roots := #[`Tools.ShippingP5Forall]

lean_lib «Tools.ShippingKidsTyped» where
  roots := #[`Tools.ShippingKidsTyped]

lean_lib «Tools.ShippingNoPortsTyped» where
  roots := #[`Tools.ShippingNoPortsTyped]

lean_lib «Tools.ShippingNoPortsTypedI» where
  roots := #[`Tools.ShippingNoPortsTypedI]

lean_lib «Tools.ShippingNoPortsTypedB» where
  roots := #[`Tools.ShippingNoPortsTypedB]

lean_lib «Tools.ShippingGateTypedCommand» where
  roots := #[`Tools.ShippingGateTypedCommand]

lean_lib «Tools.ShippingWireNamesRun» where
  roots := #[`Tools.ShippingWireNamesRun]

lean_lib «Tools.ShippingGateCert» where
  roots := #[`Tools.ShippingGateCert]

lean_lib «Tools.ShippingGateCertCommand» where
  roots := #[`Tools.ShippingGateCertCommand]

lean_lib «Tools.ShippingKidsResetSat» where
  roots := #[`Tools.ShippingKidsResetSat]

lean_lib «Tools.ShippingChildBndInit» where
  roots := #[`Tools.ShippingChildBndInit]

lean_lib «Tools.ShippingChildBndCore» where
  roots := #[`Tools.ShippingChildBndCore]

lean_lib «Tools.ShippingGateCert2» where
  roots := #[`Tools.ShippingGateCert2]

lean_lib «Tools.ShippingGateCert2Command» where
  roots := #[`Tools.ShippingGateCert2Command]

lean_lib «Tools.ShippingComposedGW» where
  roots := #[`Tools.ShippingComposedGW]

lean_lib «Tools.ShippingNoPortsTypedBW» where
  roots := #[`Tools.ShippingNoPortsTypedBW]

lean_lib «Tools.ShippingGateTypedCommandW» where
  roots := #[`Tools.ShippingGateTypedCommandW]

lean_lib «Tools.ShippingSatInputs» where
  roots := #[`Tools.ShippingSatInputs]

lean_lib «Tools.ShippingInputWiresRun» where
  roots := #[`Tools.ShippingInputWiresRun]

lean_lib «Tools.ShippingSatAssembly» where
  roots := #[`Tools.ShippingSatAssembly]

lean_lib «Tools.ShippingSatCert» where
  roots := #[`Tools.ShippingSatCert]

lean_lib «Tools.ShippingSatCert2Command» where
  roots := #[`Tools.ShippingSatCert2Command]

lean_lib «Tools.ShippingChildBalance» where
  roots := #[`Tools.ShippingChildBalance]

lean_lib «Tools.ShippingHeapModel» where
  roots := #[`Tools.ShippingHeapModel]

lean_lib «Tools.ShippingHeapProvenance» where
  roots := #[`Tools.ShippingHeapProvenance]

lean_lib «Tools.ShippingHierOptRunS» where
  roots := #[`Tools.ShippingHierOptRunS]

lean_lib «Tools.ShippingNonzeroInitWidths» where
  roots := #[`Tools.ShippingNonzeroInitWidths]

lean_lib «Tools.ShippingNoPortsTypedBS» where
  roots := #[`Tools.ShippingNoPortsTypedBS]

lean_lib «Tools.ShippingSlotRegsRun» where
  roots := #[`Tools.ShippingSlotRegsRun]

lean_lib «Tools.ShippingSatAssemblyS» where
  roots := #[`Tools.ShippingSatAssemblyS]

lean_lib «Tools.ShippingSatCertS» where
  roots := #[`Tools.ShippingSatCertS]

lean_lib «Tools.ShippingSatCertSCommand» where
  roots := #[`Tools.ShippingSatCertSCommand]

lean_lib «Tools.ShippingChildInvA» where
  roots := #[`Tools.ShippingChildInvA]

lean_lib «Tools.ShippingMachineShipsS» where
  roots := #[`Tools.ShippingMachineShipsS]

lean_lib «Tools.ShippingOkMsgGoal» where
  roots := #[`Tools.ShippingOkMsgGoal]

lean_lib «Tools.ShippingMachineShipsSW» where
  roots := #[`Tools.ShippingMachineShipsSW]

lean_lib «Tools.ShippingLeafSat» where
  roots := #[`Tools.ShippingLeafSat]

lean_lib «Tools.ShippingLeafSatDesign» where
  roots := #[`Tools.ShippingLeafSatDesign]

lean_lib «Tools.ShippingChildFresh» where
  roots := #[`Tools.ShippingChildFresh]

lean_lib «Tools.ShippingLeafFive» where
  roots := #[`Tools.ShippingLeafFive]

lean_lib «Tools.ShippingChildVCA» where
  roots := #[`Tools.ShippingChildVCA]

lean_lib «Tools.ShippingChildVertA» where
  roots := #[`Tools.ShippingChildVertA]

lean_lib «Tools.ShippingChildPathA» where
  roots := #[`Tools.ShippingChildPathA]

lean_lib «Tools.ShippingChildCacheA» where
  roots := #[`Tools.ShippingChildCacheA]

lean_lib «Tools.ShippingLeafInputWidths» where
  roots := #[`Tools.ShippingLeafInputWidths]

lean_lib «Tools.ShippingLeafDesignClosedCommand» where
  roots := #[`Tools.ShippingLeafDesignClosedCommand]
