/-
  JIT FFI Module

  Provides Lean bindings to load and interact with compiled CppSim
  shared libraries (.dylib/.so) via dlopen/dlsym. Enables JIT-accelerated
  simulation (~1M cycles/sec vs ~5K cycles/sec interpreted).

  Usage:
    let handle ← JIT.compileAndLoad "path/to/generated_jit.cpp"
    JIT.setMem handle 0 0 0x00000013  -- load firmware
    JIT.eval handle                    -- evaluate combinational
    JIT.tick handle                    -- advance clock
    let pc ← JIT.getWire handle 0     -- read pcReg
    JIT.destroy handle                 -- cleanup (also runs on finalize)
-/

namespace Sparkle.Core.JIT

/-- Opaque handle to a loaded JIT shared library -/
opaque JITHandle.nonemptyType : NonemptyType
def JITHandle : Type := JITHandle.nonemptyType.type
instance : Nonempty JITHandle := JITHandle.nonemptyType.property

/-- Load a compiled JIT shared library (.dylib/.so) -/
@[extern "sparkle_jit_load"]
opaque JIT.load (path : @& String) : IO JITHandle

/-- Evaluate combinational logic (compute next state) -/
@[extern "sparkle_jit_eval"]
opaque JIT.eval (h : @& JITHandle) : IO Unit

/-- Advance clock (apply next state to registers) -/
@[extern "sparkle_jit_tick"]
opaque JIT.tick (h : @& JITHandle) : IO Unit

/-- Reset all registers to initial values -/
@[extern "sparkle_jit_reset"]
opaque JIT.reset (h : @& JITHandle) : IO Unit

/-- Destroy the simulation instance (also runs automatically on finalize) -/
@[extern "sparkle_jit_destroy"]
opaque JIT.destroy (h : @& JITHandle) : IO Unit

/-- Set an input port by index -/
@[extern "sparkle_jit_set_input"]
opaque JIT.setInput (h : @& JITHandle) (portIdx : UInt32) (value : UInt64) : IO Unit

/-- Get an output port value by index -/
@[extern "sparkle_jit_get_output"]
opaque JIT.getOutput (h : @& JITHandle) (portIdx : UInt32) : IO UInt64

/-- Get an internal wire value by index (_gen_* named wires) -/
@[extern "sparkle_jit_get_wire"]
opaque JIT.getWire (h : @& JITHandle) (wireIdx : UInt32) : IO UInt64

/-- Set a memory word by memory index and address -/
@[extern "sparkle_jit_set_mem"]
opaque JIT.setMem (h : @& JITHandle) (memIdx : UInt32) (addr : UInt32) (data : UInt32) : IO Unit

/-- Get a memory word by memory index and address -/
@[extern "sparkle_jit_get_mem"]
opaque JIT.getMem (h : @& JITHandle) (memIdx : UInt32) (addr : UInt32) : IO UInt32

/-- Fill a range of memory words with a value (bulk write) -/
@[extern "sparkle_jit_memset_word"]
opaque JIT.memsetWord (h : @& JITHandle) (memIdx : UInt32) (addr : UInt32) (val : UInt32) (count : UInt32) : IO Unit

/-- Take a full snapshot of the simulation state (registers + memories).
    Returns an opaque pointer (as UInt64) that can be passed to restore/freeSnapshot. -/
@[extern "sparkle_jit_snapshot"]
opaque JIT.snapshot (h : @& JITHandle) : IO UInt64

/-- Restore simulation state from a snapshot taken by JIT.snapshot. -/
@[extern "sparkle_jit_restore"]
opaque JIT.restore (h : @& JITHandle) (snap : UInt64) : IO Unit

/-- Free a snapshot created by JIT.snapshot. Must be called to avoid memory leaks. -/
@[extern "sparkle_jit_free_snapshot"]
opaque JIT.freeSnapshot (h : @& JITHandle) (snap : UInt64) : IO Unit

/-- Get the name of a wire by index (for discovery) -/
@[extern "sparkle_jit_wire_name"]
opaque JIT.wireName (h : @& JITHandle) (wireIdx : UInt32) : IO String

/-- Get the total number of observable wires -/
@[extern "sparkle_jit_num_wires"]
opaque JIT.numWires (h : @& JITHandle) : IO UInt32

/-- Find a wire index by name, returns none if not found -/
def JIT.findWire (h : JITHandle) (name : String) : IO (Option UInt32) := do
  let n ← JIT.numWires h
  for i in [:n.toNat] do
    let wireName ← JIT.wireName h i.toUInt32
    if wireName == name then return some i.toUInt32
  return none

/-- Set a register value by index (writes current state, not _next) -/
@[extern "sparkle_jit_set_reg"]
opaque JIT.setReg (h : @& JITHandle) (regIdx : UInt32) (value : UInt64) : IO Unit

/-- Get a register value by index -/
@[extern "sparkle_jit_get_reg"]
opaque JIT.getReg (h : @& JITHandle) (regIdx : UInt32) : IO UInt64

/-- Get the name of a register by index (for discovery) -/
@[extern "sparkle_jit_reg_name"]
opaque JIT.regName (h : @& JITHandle) (regIdx : UInt32) : IO String

/-- Get the total number of registers -/
@[extern "sparkle_jit_num_regs"]
opaque JIT.numRegs (h : @& JITHandle) : IO UInt32

/-- Find a register index by name, returns none if not found -/
def JIT.findReg (h : JITHandle) (name : String) : IO (Option UInt32) := do
  let n ← JIT.numRegs h
  for i in [:n.toNat] do
    let rn ← JIT.regName h i.toUInt32
    if rn == name then return some i.toUInt32
  return none

/-- Compile a JIT .cpp file to a shared library, with hash-based caching -/
def JIT.compile (cppPath : String) (cacheDir : String := ".lake/build/jit_cache") : IO String := do
  -- Read source, compute hash for caching
  let source ← IO.FS.readFile cppPath
  let hash := toString (Hashable.hash source)
  let dylibExt := if System.Platform.isOSX then ".dylib" else ".so"
  let dylibPath := s!"{cacheDir}/{hash}{dylibExt}"
  -- Check cache
  if ← System.FilePath.pathExists dylibPath then return dylibPath
  -- Compile
  IO.FS.createDirAll cacheDir
  let cppDir := (System.FilePath.mk cppPath).parent.getD "."
  let result ← IO.Process.output {
    cmd := "c++"
    args := #["-shared", "-fPIC", "-O2", "-std=c++17",
              "-I", cppDir.toString,
              "-o", dylibPath, cppPath]
  }
  if result.exitCode != 0 then
    throw (IO.userError s!"JIT compilation failed:\n{result.stderr}")
  return dylibPath

/-- Compile and load a JIT module in one step -/
def JIT.compileAndLoad (cppPath : String) : IO JITHandle := do
  let dylibPath ← JIT.compile cppPath
  JIT.load dylibPath

end Sparkle.Core.JIT
