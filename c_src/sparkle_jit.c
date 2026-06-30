/*
 * JIT FFI bindings for Sparkle CSim
 *
 * Provides dlopen/dlsym wrappers to load compiled CSim shared libraries
 * from Lean.  Uses lean_external_class for reference-counted opaque handles
 * with automatic cleanup (vtable->destroy + dlclose on finalization).
 *
 * The loaded shared library exports exactly ONE C symbol:
 *
 *     const JitVTable* jit_vtable(void);
 *
 * which returns a pointer to a `JitVTable` struct whose members are
 * pointers into static functions inside that same .so.  All operations
 * (create / destroy / eval / tick / …) are dispatched through this
 * vtable — there are no other extern symbols in the .so.
 *
 * Why a vtable instead of one-symbol-per-op:
 *   Glibc's dlopen has historically collapsed multiple distinct .so
 *   files onto a single handle when the build-time and host-time glibc
 *   disagree on `GLIBC_ABI_*` symbol versions (Sparkle Issue #70).
 *   When that happens, calling `dlsym(h, "jit_eval")` on the second
 *   handle returns the first .so's `jit_eval`, so the per-handle ctx
 *   pointer ends up dispatching into the wrong .so's code.
 *
 *   By exporting only `jit_vtable` (and copying the function pointers
 *   into the per-handle JITHandle), each handle holds its own typed
 *   pointer set.  Even if two paths somehow shared a glibc handle, the
 *   trampolines themselves are static — there is no external name to
 *   collide.
 */

#include <lean/lean.h>

/* `leanc` builds with `-fvisibility=hidden` and `LEAN_EXPORT` is a no-op
   outside libleanshared, so these @[extern] symbols would be hidden.
   `precompileModules` loads this as a *shared* library at compile time
   and must resolve them dynamically — force default visibility. */
#pragma GCC visibility push(default)

/* Declare dlopen/dlsym/dlclose/dlerror manually to avoid dlfcn.h
   (Lean's bundled clang uses -nostdinc which excludes system headers) */
#define RTLD_NOW 2
#define LM_ID_NEWLM (-1L)  /* glibc: request a fresh link-map namespace */
typedef long Lmid_t;
extern void* dlopen(const char* path, int mode);
extern void* dlmopen(Lmid_t lmid, const char* path, int mode);
extern void* dlsym(void* handle, const char* symbol);
extern int   dlclose(void* handle);
extern char* dlerror(void);

extern void* calloc(unsigned long count, unsigned long size);
extern void  free(void* ptr);
extern int   snprintf(char* buf, unsigned long size, const char* fmt, ...);

/* ---- JIT vtable schema (must match Sparkle/Backend/CSim.lean) ---- */
typedef struct JitVTable {
    void* (*create)(void);
    void  (*destroy)(void* ctx);
    void  (*reset)(void* ctx);
    void  (*eval)(void* ctx);
    void  (*tick)(void* ctx);
    void  (*eval_tick)(void* ctx);
    void  (*set_input)(void* ctx, uint32_t idx, uint64_t val);
    uint64_t (*get_output)(void* ctx, uint32_t idx);
    uint64_t (*get_wire)(void* ctx, uint32_t idx);
    void  (*set_mem)(void* ctx, uint32_t mem_idx, uint32_t addr, uint32_t data);
    uint32_t (*get_mem)(void* ctx, uint32_t mem_idx, uint32_t addr);
    void  (*memset_word)(void* ctx, uint32_t mem_idx, uint32_t addr, uint32_t val, uint32_t count);
    const char* (*wire_name)(uint32_t idx);
    uint32_t (*num_wires)(void);
    void  (*set_reg)(void* ctx, uint32_t reg_idx, uint64_t val);
    uint64_t (*get_reg)(void* ctx, uint32_t reg_idx);
    const char* (*reg_name)(uint32_t idx);
    uint32_t (*num_regs)(void);
    void* (*snapshot)(void* ctx);
    void  (*restore)(void* ctx, void* snap);
    void  (*free_snapshot)(void* snap);
} JitVTable;

typedef struct {
    void* lib;              /* dlopen handle */
    void* ctx;              /* vtable->create() result */
    const JitVTable* vt;    /* function-pointer table inside the .so */
} JITHandle;

static lean_external_class* g_jit_class = NULL;

static void jit_finalizer(void* p) {
    JITHandle* h = (JITHandle*)p;
    if (h->ctx && h->vt && h->vt->destroy) h->vt->destroy(h->ctx);
    if (h->lib) dlclose(h->lib);
    free(h);
}

static void jit_foreach(void* p, b_lean_obj_arg f) {
    (void)p; (void)f;
}

static inline void ensure_jit_class(void) {
    if (g_jit_class == NULL) {
        g_jit_class = lean_register_external_class(jit_finalizer, jit_foreach);
    }
}

static inline JITHandle* get_handle(b_lean_obj_arg obj) {
    return (JITHandle*)lean_get_external_data(obj);
}

/* Helper: make IO error result */
static lean_obj_res mk_io_error(const char* msg) {
    lean_obj_res err_str = lean_mk_string(msg);
    lean_obj_res io_err = lean_alloc_ctor(7, 1, 0);  /* IO.Error.userError */
    lean_ctor_set(io_err, 0, err_str);
    lean_obj_res result = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(result, 0, io_err);
    lean_ctor_set(result, 1, lean_io_mk_world());
    return result;
}

/* Helper: make IO ok result */
static lean_obj_res mk_io_ok(lean_obj_res val) {
    lean_obj_res result = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result, 0, val);
    lean_ctor_set(result, 1, lean_io_mk_world());
    return result;
}

extern int strcmp(const char* a, const char* b);
extern unsigned long strlen(const char* s);
extern void* memcpy(void* dst, const void* src, unsigned long n);

/* The multi-handle dlopen collision detector used to live here.
 * Under the new vtable-only export model it is no longer needed:
 * even if glibc collapses two different .so paths onto the same
 * `lib` handle (Issue #70), each `JITHandle` still holds its own
 * `vt` pointer set, so dispatch goes to the correct file's
 * static helpers.  The compiler `dlmopen` path above also
 * prevents the collapse from happening in the first place on
 * platforms where it works.  We therefore no longer emit a
 * warning.  See c_src/sparkle_jit.c history for the previous
 * detector implementation.
 */

/* sparkle_jit_load : @& String → IO JITHandle
 *
 * Strategy: prefer `dlmopen(LM_ID_NEWLM, ...)` to allocate a fresh
 * link-map namespace per JIT module.  That defeats the silent
 * multi-handle collapse (Issue #70) at the source — with a fresh
 * namespace, glibc cannot dedupe two different .so files onto one
 * handle even when their libc dependency would normally let it.
 *
 * If dlmopen fails (e.g. host-vs-build glibc PRIVATE-symbol skew
 * that surfaces when the new namespace has to reload libc fresh),
 * fall back to plain dlopen.  The vtable-only export model means
 * dispatch is still correct in that case: each `JITHandle` holds
 * its own pointer set, copied from the vtable returned by the
 * (collapsed) library, so trampoline pointers can't be confused
 * across handles even if `lib` is shared.  Because of that we no
 * longer emit a warning for the dlopen-collapse case — it is
 * not a correctness hazard under the vtable model.
 */
LEAN_EXPORT lean_obj_res sparkle_jit_load(b_lean_obj_arg path, lean_obj_arg w) {
    (void)w;
    const char* cpath = lean_string_cstr(path);

    void* lib = dlmopen(LM_ID_NEWLM, cpath, RTLD_NOW);
    if (!lib) {
        /* Clear stale dlerror from the failed dlmopen attempt. */
        (void)dlerror();
        lib = dlopen(cpath, RTLD_NOW);
    }
    if (!lib) {
        char buf[1024];
        snprintf(buf, sizeof(buf), "JIT: dl(m)open failed: %s", dlerror());
        return mk_io_error(buf);
    }

    /* Resolve THE ONLY external symbol: jit_vtable */
    typedef const JitVTable* (*vtable_fn)(void);
    vtable_fn get_vtable = (vtable_fn)dlsym(lib, "jit_vtable");
    if (!get_vtable) {
        char buf[1024];
        snprintf(buf, sizeof(buf),
            "JIT: jit_vtable symbol not found: %s", dlerror());
        dlclose(lib);
        return mk_io_error(buf);
    }

    const JitVTable* vt = get_vtable();
    if (!vt || !vt->create) {
        dlclose(lib);
        return mk_io_error("JIT: jit_vtable() returned NULL or vtable missing 'create'");
    }

    JITHandle* h = (JITHandle*)calloc(1, sizeof(JITHandle));
    h->lib = lib;
    h->vt = vt;
    h->ctx = vt->create();
    if (!h->ctx) {
        dlclose(lib);
        free(h);
        return mk_io_error("JIT: vtable->create() returned NULL");
    }

    ensure_jit_class();
    lean_obj_res ext = lean_alloc_external(g_jit_class, h);
    return mk_io_ok(ext);
}

/* sparkle_jit_eval : @& JITHandle → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_eval(b_lean_obj_arg handle, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->vt && h->vt->eval) h->vt->eval(h->ctx);
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_tick : @& JITHandle → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_tick(b_lean_obj_arg handle, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->vt && h->vt->tick) h->vt->tick(h->ctx);
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_eval_tick : @& JITHandle → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_eval_tick(b_lean_obj_arg handle, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->vt && h->vt->eval_tick) h->vt->eval_tick(h->ctx);
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_reset : @& JITHandle → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_reset(b_lean_obj_arg handle, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->vt && h->vt->reset) h->vt->reset(h->ctx);
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_destroy : @& JITHandle → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_destroy(b_lean_obj_arg handle, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->ctx && h->vt && h->vt->destroy) {
        h->vt->destroy(h->ctx);
        h->ctx = NULL;
    }
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_set_input : @& JITHandle → UInt32 → UInt64 → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_set_input(
    b_lean_obj_arg handle, uint32_t idx, uint64_t val, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->vt && h->vt->set_input) h->vt->set_input(h->ctx, idx, val);
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_get_output : @& JITHandle → UInt32 → IO UInt64 */
LEAN_EXPORT lean_obj_res sparkle_jit_get_output(
    b_lean_obj_arg handle, uint32_t idx, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    uint64_t val = (h->vt && h->vt->get_output) ? h->vt->get_output(h->ctx, idx) : 0;
    return mk_io_ok(lean_box_uint64(val));
}

/* sparkle_jit_get_wire : @& JITHandle → UInt32 → IO UInt64 */
LEAN_EXPORT lean_obj_res sparkle_jit_get_wire(
    b_lean_obj_arg handle, uint32_t idx, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    uint64_t val = (h->vt && h->vt->get_wire) ? h->vt->get_wire(h->ctx, idx) : 0;
    return mk_io_ok(lean_box_uint64(val));
}

/* sparkle_jit_set_mem : @& JITHandle → UInt32 → UInt32 → UInt32 → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_set_mem(
    b_lean_obj_arg handle, uint32_t mem_idx, uint32_t addr, uint32_t data,
    lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->vt && h->vt->set_mem) h->vt->set_mem(h->ctx, mem_idx, addr, data);
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_get_mem : @& JITHandle → UInt32 → UInt32 → IO UInt32 */
LEAN_EXPORT lean_obj_res sparkle_jit_get_mem(
    b_lean_obj_arg handle, uint32_t mem_idx, uint32_t addr, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    uint32_t val = (h->vt && h->vt->get_mem) ? h->vt->get_mem(h->ctx, mem_idx, addr) : 0;
    return mk_io_ok(lean_box_uint32(val));
}

/* sparkle_jit_memset_word : @& JITHandle → UInt32 → UInt32 → UInt32 → UInt32 → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_memset_word(
    b_lean_obj_arg handle, uint32_t mem_idx, uint32_t addr, uint32_t val,
    uint32_t count, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->vt && h->vt->memset_word) h->vt->memset_word(h->ctx, mem_idx, addr, val, count);
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_wire_name : @& JITHandle → UInt32 → IO String */
LEAN_EXPORT lean_obj_res sparkle_jit_wire_name(
    b_lean_obj_arg handle, uint32_t idx, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    const char* name = (h->vt && h->vt->wire_name) ? h->vt->wire_name(idx) : "";
    return mk_io_ok(lean_mk_string(name));
}

/* sparkle_jit_num_wires : @& JITHandle → IO UInt32 */
LEAN_EXPORT lean_obj_res sparkle_jit_num_wires(
    b_lean_obj_arg handle, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    uint32_t n = (h->vt && h->vt->num_wires) ? h->vt->num_wires() : 0;
    return mk_io_ok(lean_box_uint32(n));
}

/* sparkle_jit_set_reg : @& JITHandle → UInt32 → UInt64 → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_set_reg(
    b_lean_obj_arg handle, uint32_t idx, uint64_t val, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->vt && h->vt->set_reg) h->vt->set_reg(h->ctx, idx, val);
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_get_reg : @& JITHandle → UInt32 → IO UInt64 */
LEAN_EXPORT lean_obj_res sparkle_jit_get_reg(
    b_lean_obj_arg handle, uint32_t idx, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    uint64_t val = (h->vt && h->vt->get_reg) ? h->vt->get_reg(h->ctx, idx) : 0;
    return mk_io_ok(lean_box_uint64(val));
}

/* sparkle_jit_reg_name : @& JITHandle → UInt32 → IO String */
LEAN_EXPORT lean_obj_res sparkle_jit_reg_name(
    b_lean_obj_arg handle, uint32_t idx, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    const char* name = (h->vt && h->vt->reg_name) ? h->vt->reg_name(idx) : "";
    return mk_io_ok(lean_mk_string(name));
}

/* sparkle_jit_num_regs : @& JITHandle → IO UInt32 */
LEAN_EXPORT lean_obj_res sparkle_jit_num_regs(
    b_lean_obj_arg handle, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    uint32_t n = (h->vt && h->vt->num_regs) ? h->vt->num_regs() : 0;
    return mk_io_ok(lean_box_uint32(n));
}

/* sparkle_jit_snapshot : @& JITHandle → IO UInt64 */
LEAN_EXPORT lean_obj_res sparkle_jit_snapshot(
    b_lean_obj_arg handle, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    void* snap = (h->vt && h->vt->snapshot) ? h->vt->snapshot(h->ctx) : NULL;
    return mk_io_ok(lean_box_uint64((uint64_t)snap));
}

/* sparkle_jit_restore : @& JITHandle → UInt64 → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_restore(
    b_lean_obj_arg handle, uint64_t snap, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->vt && h->vt->restore && snap) h->vt->restore(h->ctx, (void*)snap);
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_free_snapshot : @& JITHandle → UInt64 → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_free_snapshot(
    b_lean_obj_arg handle, uint64_t snap, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->vt && h->vt->free_snapshot && snap) h->vt->free_snapshot((void*)snap);
    return mk_io_ok(lean_box(0));
}

/* ========================================================================
 * CDC Multi-Domain Runner (Phase 4)
 *
 * Loads cdc_runner.so/.dylib via dlopen and calls cdc_run() to execute
 * two JIT domains on separate threads with a lock-free SPSC queue.
 *
 * The CDC runner is a separate C++ shared library because sparkle_jit.c
 * is compiled under Lean's -nostdinc.
 * ======================================================================== */

typedef struct {
    void* ctx;
    void  (*eval_tick)(void*);
    void  (*set_input)(void*, uint32_t, uint64_t);
    uint64_t (*get_output)(void*, uint32_t);
    void* (*snapshot)(void*);
    void  (*restore)(void*, void*);
    void  (*free_snapshot)(void*);
} CDCJITVtable;

typedef struct {
    uint64_t messages_sent;
    uint64_t messages_received;
    uint64_t rollback_count;
    double   elapsed_ms;
    int      success;
} CDCRunResult;

typedef CDCRunResult (*cdc_run_fn)(
    CDCJITVtable*, CDCJITVtable*,
    uint64_t, uint64_t,
    uint32_t, uint32_t,
    uint32_t, uint32_t);

static void* g_cdc_runner_lib = NULL;
static cdc_run_fn g_cdc_run = NULL;

static int ensure_cdc_runner(void) {
    if (g_cdc_run) return 1;

    const char* names[] = {
        "./cdc_runner.so",
        "./c_src/cdc/cdc_runner.so",
        "cdc_runner.so",
        "./cdc_runner.dylib",
        "./c_src/cdc/cdc_runner.dylib",
        "cdc_runner.dylib",
        NULL
    };
    for (int i = 0; names[i]; i++) {
        g_cdc_runner_lib = dlopen(names[i], RTLD_NOW);
        if (g_cdc_runner_lib) break;
    }
    if (!g_cdc_runner_lib) return 0;

    g_cdc_run = (cdc_run_fn)dlsym(g_cdc_runner_lib, "cdc_run");
    if (!g_cdc_run) {
        dlclose(g_cdc_runner_lib);
        g_cdc_runner_lib = NULL;
        return 0;
    }
    return 1;
}

static void fill_vtable(CDCJITVtable* vt, JITHandle* h) {
    vt->ctx           = h->ctx;
    vt->eval_tick     = (h->vt) ? h->vt->eval_tick : NULL;
    vt->set_input     = (h->vt) ? h->vt->set_input : NULL;
    vt->get_output    = (h->vt) ? h->vt->get_output : NULL;
    vt->snapshot      = (h->vt) ? h->vt->snapshot : NULL;
    vt->restore       = (h->vt) ? h->vt->restore : NULL;
    vt->free_snapshot = (h->vt) ? h->vt->free_snapshot : NULL;
}

LEAN_EXPORT lean_obj_res sparkle_jit_run_cdc(
    b_lean_obj_arg handle_a, b_lean_obj_arg handle_b,
    uint64_t cycles_a, uint64_t cycles_b,
    uint32_t out_port_a, uint32_t in_port_b,
    lean_obj_arg w)
{
    (void)w;

    if (!ensure_cdc_runner()) {
        return mk_io_error("CDC: failed to load cdc_runner shared library. "
                           "Build it with: make -C c_src/cdc cdc_runner.so");
    }

    JITHandle* ha = get_handle(handle_a);
    JITHandle* hb = get_handle(handle_b);

    CDCJITVtable vt_a, vt_b;
    fill_vtable(&vt_a, ha);
    fill_vtable(&vt_b, hb);

    CDCRunResult res = g_cdc_run(&vt_a, &vt_b,
                                  cycles_a, cycles_b,
                                  out_port_a, in_port_b,
                                  2, 1000);

    if (!res.success) {
        return mk_io_error("CDC: cdc_run failed");
    }

    lean_obj_res v_sent = lean_box_uint64(res.messages_sent);
    lean_obj_res v_recv = lean_box_uint64(res.messages_received);
    lean_obj_res v_rb   = lean_box_uint64(res.rollback_count);

    lean_obj_res inner = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(inner, 0, v_recv);
    lean_ctor_set(inner, 1, v_rb);

    lean_obj_res outer = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(outer, 0, v_sent);
    lean_ctor_set(outer, 1, inner);

    return mk_io_ok(outer);
}

#pragma GCC visibility pop
