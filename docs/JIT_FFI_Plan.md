# JIT FFI Plan: Native-Speed Simulation via Dynamic Compilation

## Overview

Replace the interpreted `loopMemo` simulation path with a JIT-compiled native path that synthesizes C++ from Signal IR, compiles it to a shared library, and calls it via Lean FFI. Expected speedup: 200-1000x (from ~5K cycles/sec to ~3.6M cycles/sec).

## Architecture

```
Signal.loop body
  → synthesize IR (existing Elab.lean)
  → optimize (existing IR passes)
  → emit C++ with extern "C" wrappers (extend CppSim.lean)
  → compile .dylib (c++ -shared -fPIC -O2)
  → dlopen / dlsym (sparkle_jit.c FFI)
  → call eval/tick per timestep from Lean
```

## 1. C++ Shared Library Generation

Extend `Sparkle/Backend/CppSim.lean` to emit a standalone `.cpp` file with `extern "C"` wrappers:

```cpp
// Generated jit_module.cpp
#include <cstdint>
#include <cstring>

struct State { /* ... register fields from Module ... */ };

static State* g_state = nullptr;

extern "C" {
  void* jit_create() {
    g_state = new State();
    jit_reset();
    return g_state;
  }

  void jit_destroy(void* ctx) {
    delete static_cast<State*>(ctx);
  }

  void jit_reset(void* ctx) {
    auto* s = static_cast<State*>(ctx);
    // Initialize all registers to their reset values
  }

  void jit_eval(void* ctx) {
    auto* s = static_cast<State*>(ctx);
    // Combinational logic (from Module.eval)
  }

  void jit_tick(void* ctx) {
    auto* s = static_cast<State*>(ctx);
    // Sequential logic: copy next-state to current-state
  }

  void jit_set_input(void* ctx, uint32_t port_idx, uint64_t value) {
    // Set input port by index (from Module.inputs list)
  }

  uint64_t jit_get_output(void* ctx, uint32_t port_idx) {
    // Get output port by index (from Module.outputs list)
  }
}
```

Port index mapping derived from `Module.inputs` and `Module.outputs` lists.

## 2. Background Compilation

```lean
def compileJIT (cppSource : String) : IO FilePath := do
  let hash := toString (hash cppSource)
  let cacheDir := ".lake/build/jit_cache"
  let dylibPath := cacheDir / s!"{hash}.dylib"
  if ← dylibPath.pathExists then return dylibPath
  IO.FS.createDirAll cacheDir
  let cppPath := cacheDir / s!"{hash}.cpp"
  IO.FS.writeFile cppPath cppSource
  let result ← IO.Process.output {
    cmd := "c++"
    args := #["-shared", "-fPIC", "-O2", "-std=c++17",
              "-o", dylibPath.toString, cppPath.toString]
  }
  if result.exitCode != 0 then
    throw (IO.userError s!"JIT compilation failed: {result.stderr}")
  return dylibPath
```

### Cache invalidation

- Hash-based: regenerate when C++ source changes
- Cache directory: `.lake/build/jit_cache/<hash>.dylib`
- Old cache entries can be cleaned by `lake clean`

## 3. Lean FFI Bindings

### New file: `c_src/sparkle_jit.c`

```c
#include <lean/lean.h>
#include <dlfcn.h>

// Opaque handle wrapping dlopen'd library + function pointers
typedef struct {
  void* lib_handle;
  void* ctx;
  void  (*fn_eval)(void*);
  void  (*fn_tick)(void*);
  void  (*fn_reset)(void*);
  void  (*fn_set_input)(void*, uint32_t, uint64_t);
  uint64_t (*fn_get_output)(void*, uint32_t);
} JITHandle;

// lean_external_class for ref-counted JITHandle
static void jit_handle_finalize(void* p) {
  JITHandle* h = (JITHandle*)p;
  if (h->ctx) {
    // call jit_destroy if available
    typedef void (*destroy_fn)(void*);
    destroy_fn fn = (destroy_fn)dlsym(h->lib_handle, "jit_destroy");
    if (fn) fn(h->ctx);
  }
  if (h->lib_handle) dlclose(h->lib_handle);
  free(h);
}

// @[extern "sparkle_jit_load"]
// opaque JIT.load (path : @& String) : IO JITHandle
lean_obj_res sparkle_jit_load(b_lean_obj_arg path, lean_obj_arg w) {
  const char* p = lean_string_cstr(path);
  void* lib = dlopen(p, RTLD_NOW);
  if (!lib) { /* return IO.Error */ }

  JITHandle* h = calloc(1, sizeof(JITHandle));
  h->lib_handle = lib;
  h->fn_eval = dlsym(lib, "jit_eval");
  h->fn_tick = dlsym(lib, "jit_tick");
  h->fn_reset = dlsym(lib, "jit_reset");
  h->fn_set_input = dlsym(lib, "jit_set_input");
  h->fn_get_output = dlsym(lib, "jit_get_output");

  // Create context
  typedef void* (*create_fn)(void);
  create_fn fn_create = dlsym(lib, "jit_create");
  h->ctx = fn_create();

  // Wrap in lean_external_object
  // ...
  return lean_io_result_mk_ok(lean_alloc_external(..., h));
}
```

### New file: `Sparkle/Core/JIT.lean`

```lean
opaque JITHandle : Type

@[extern "sparkle_jit_load"]
opaque JIT.load (path : @& String) : IO JITHandle

@[extern "sparkle_jit_eval"]
opaque JIT.eval (h : @& JITHandle) : IO Unit

@[extern "sparkle_jit_tick"]
opaque JIT.tick (h : @& JITHandle) : IO Unit

@[extern "sparkle_jit_reset"]
opaque JIT.reset (h : @& JITHandle) : IO Unit

@[extern "sparkle_jit_set_input"]
opaque JIT.setInput (h : @& JITHandle) (portIdx : UInt32) (value : UInt64) : IO Unit

@[extern "sparkle_jit_get_output"]
opaque JIT.getOutput (h : @& JITHandle) (portIdx : UInt32) : IO UInt64
```

### lakefile.lean addition

```lean
extern_lib «sparkle_jit» pkg := do
  let srcPath := pkg.dir / "c_src" / "sparkle_jit.c"
  let oFile := pkg.irRelDir / "c_src" / "sparkle_jit.o"
  buildO oFile srcPath #["-I", (← getLeanIncludeDir).toString, "-fPIC"] "cc"
```

## 4. Integration with loopMemo

### New combinator: `loopMemoJIT`

```lean
partial def loopMemoJIT [Inhabited α] (body : Signal dom α → Signal dom α)
    : IO (Signal dom α) := do
  -- Step 1: Synthesize IR from body
  let ir ← synthesizeModule body
  -- Step 2: Emit C++ source
  let cppSource := emitCppJIT ir
  -- Step 3: Compile to .dylib
  let dylibPath ← compileJIT cppSource
  -- Step 4: Load via FFI
  let handle ← JIT.load dylibPath.toString
  -- Step 5: Return Signal that calls JIT per timestep
  let stateRef ← IO.mkRef (default : α)
  return ⟨fun t => unsafe
    JIT.eval handle
    JIT.tick handle
    -- Extract outputs into α
    ...
  ⟩
```

### Fallback behavior

```lean
partial def loopMemoAuto [Inhabited α] (body : Signal dom α → Signal dom α)
    : IO (Signal dom α) := do
  try
    loopMemoJIT body
  catch _ =>
    -- Fall back to interpreted loopMemo
    Signal.loopMemo body
```

## 5. Key References

| File | Purpose |
|------|---------|
| `Sparkle/Backend/CppSim.lean` | C++ class generation (eval/tick/reset methods) |
| `c_src/sparkle_barrier.c` | Existing C FFI pattern (`@[extern]`, Lean object lifecycle) |
| `lakefile.lean:12-18` | `extern_lib` compilation pattern |
| `Sparkle/Core/Signal.lean:572-607` | `loopMemoImpl` (hook point for JIT) |
| `verilator/tb_cppsim.cpp` | Usage example of generated CppSim class |

## 6. Performance Expectations

| Metric | Interpreted (`loopMemo`) | JIT (`loopMemoJIT`) | Verilator |
|--------|--------------------------|---------------------|-----------|
| Cycles/sec | ~5,000 | ~1M-3.6M | ~3.6M |
| Startup time | Instant | 2-5s (compile) | N/A (pre-compiled) |
| Flexibility | Full Lean interop | IO-based only | External process |

## 7. Open Questions

1. **State marshalling**: How to efficiently convert between Lean `α` tuples and flat C++ arrays? Consider generating Lean marshalling code alongside C++.
2. **Sub-module support**: Nested `Signal.loop` creates sub-modules — should JIT flatten or preserve module hierarchy?
3. **Memory ports**: `Signal.memory`/`memoryComboRead` need special handling for RAM arrays in C++ state.
4. **Incremental compilation**: Worth caching object files and only relinking when wrapper changes?
5. **Platform support**: `dlopen` is POSIX — need `LoadLibrary` wrapper for Windows support?
