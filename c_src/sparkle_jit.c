/*
 * JIT FFI bindings for Sparkle CppSim
 *
 * Provides dlopen/dlsym wrappers to load compiled CppSim shared libraries
 * from Lean. Uses lean_external_class for reference-counted opaque handles
 * with automatic cleanup (jit_destroy + dlclose on finalization).
 *
 * The loaded shared library must export extern "C" functions:
 *   jit_create, jit_destroy, jit_reset, jit_eval, jit_tick, jit_eval_tick,
 *   jit_set_input, jit_get_output, jit_get_wire,
 *   jit_set_mem, jit_get_mem, jit_memset_word,
 *   jit_set_reg, jit_get_reg, jit_reg_name, jit_num_regs,
 *   jit_snapshot, jit_restore, jit_free_snapshot
 */

#include <lean/lean.h>

/* Declare dlopen/dlsym/dlclose/dlerror manually to avoid dlfcn.h
   (Lean's bundled clang uses -nostdinc which excludes system headers) */
#define RTLD_NOW 2
extern void* dlopen(const char* path, int mode);
extern void* dlsym(void* handle, const char* symbol);
extern int   dlclose(void* handle);
extern char* dlerror(void);

extern void* calloc(unsigned long count, unsigned long size);
extern void  free(void* ptr);
extern int   snprintf(char* buf, unsigned long size, const char* fmt, ...);

typedef struct {
    void* lib;              /* dlopen handle */
    void* ctx;              /* jit_create() result */
    void  (*eval)(void*);
    void  (*tick)(void*);
    void  (*eval_tick)(void*);
    void  (*reset)(void*);
    void  (*set_input)(void*, uint32_t, uint64_t);
    uint64_t (*get_output)(void*, uint32_t);
    uint64_t (*get_wire)(void*, uint32_t);
    void  (*set_mem)(void*, uint32_t, uint32_t, uint32_t);
    uint32_t (*get_mem)(void*, uint32_t, uint32_t);
    void  (*memset_word)(void*, uint32_t, uint32_t, uint32_t, uint32_t);
    void  (*destroy)(void*);
    const char* (*wire_name)(uint32_t);
    uint32_t (*num_wires)(void);
    void     (*set_reg)(void*, uint32_t, uint64_t);
    uint64_t (*get_reg)(void*, uint32_t);
    const char* (*reg_name)(uint32_t);
    uint32_t (*num_regs)(void);
    void* (*snapshot)(void*);
    void  (*restore)(void*, void*);
    void  (*free_snapshot)(void*);
} JITHandle;

static lean_external_class* g_jit_class = NULL;

static void jit_finalizer(void* p) {
    JITHandle* h = (JITHandle*)p;
    if (h->ctx && h->destroy) h->destroy(h->ctx);
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
    /* IO.Error.userError (String) */
    lean_obj_res io_err = lean_alloc_ctor(7, 1, 0);  /* IO.Error.userError */
    lean_ctor_set(io_err, 0, err_str);
    /* EStateM.Result.error */
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

/* sparkle_jit_load : @& String → IO JITHandle */
LEAN_EXPORT lean_obj_res sparkle_jit_load(b_lean_obj_arg path, lean_obj_arg w) {
    (void)w;
    const char* cpath = lean_string_cstr(path);

    void* lib = dlopen(cpath, RTLD_NOW);
    if (!lib) {
        char buf[1024];
        snprintf(buf, sizeof(buf), "JIT: dlopen failed: %s", dlerror());
        return mk_io_error(buf);
    }

    JITHandle* h = (JITHandle*)calloc(1, sizeof(JITHandle));
    h->lib = lib;

    /* Load function pointers */
    h->destroy    = (void(*)(void*))dlsym(lib, "jit_destroy");
    h->eval       = (void(*)(void*))dlsym(lib, "jit_eval");
    h->tick       = (void(*)(void*))dlsym(lib, "jit_tick");
    h->eval_tick  = (void(*)(void*))dlsym(lib, "jit_eval_tick");
    h->reset      = (void(*)(void*))dlsym(lib, "jit_reset");
    h->set_input  = (void(*)(void*, uint32_t, uint64_t))dlsym(lib, "jit_set_input");
    h->get_output = (uint64_t(*)(void*, uint32_t))dlsym(lib, "jit_get_output");
    h->get_wire   = (uint64_t(*)(void*, uint32_t))dlsym(lib, "jit_get_wire");
    h->set_mem    = (void(*)(void*, uint32_t, uint32_t, uint32_t))dlsym(lib, "jit_set_mem");
    h->get_mem    = (uint32_t(*)(void*, uint32_t, uint32_t))dlsym(lib, "jit_get_mem");
    h->memset_word = (void(*)(void*, uint32_t, uint32_t, uint32_t, uint32_t))dlsym(lib, "jit_memset_word");
    h->wire_name  = (const char*(*)(uint32_t))dlsym(lib, "jit_wire_name");
    h->num_wires  = (uint32_t(*)(void))dlsym(lib, "jit_num_wires");
    h->set_reg    = (void(*)(void*, uint32_t, uint64_t))dlsym(lib, "jit_set_reg");
    h->get_reg    = (uint64_t(*)(void*, uint32_t))dlsym(lib, "jit_get_reg");
    h->reg_name   = (const char*(*)(uint32_t))dlsym(lib, "jit_reg_name");
    h->num_regs   = (uint32_t(*)(void))dlsym(lib, "jit_num_regs");
    h->snapshot      = (void*(*)(void*))dlsym(lib, "jit_snapshot");
    h->restore       = (void(*)(void*, void*))dlsym(lib, "jit_restore");
    h->free_snapshot = (void(*)(void*))dlsym(lib, "jit_free_snapshot");

    /* Create the simulation instance */
    void* (*create)(void) = (void*(*)(void))dlsym(lib, "jit_create");
    if (!create) {
        dlclose(lib);
        free(h);
        return mk_io_error("JIT: jit_create symbol not found");
    }
    h->ctx = create();
    if (!h->ctx) {
        dlclose(lib);
        free(h);
        return mk_io_error("JIT: jit_create returned NULL");
    }

    ensure_jit_class();
    lean_obj_res ext = lean_alloc_external(g_jit_class, h);
    return mk_io_ok(ext);
}

/* sparkle_jit_eval : @& JITHandle → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_eval(b_lean_obj_arg handle, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->eval) h->eval(h->ctx);
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_tick : @& JITHandle → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_tick(b_lean_obj_arg handle, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->tick) h->tick(h->ctx);
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_eval_tick : @& JITHandle → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_eval_tick(b_lean_obj_arg handle, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->eval_tick) h->eval_tick(h->ctx);
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_reset : @& JITHandle → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_reset(b_lean_obj_arg handle, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->reset) h->reset(h->ctx);
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_destroy : @& JITHandle → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_destroy(b_lean_obj_arg handle, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->ctx && h->destroy) {
        h->destroy(h->ctx);
        h->ctx = NULL;
    }
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_set_input : @& JITHandle → UInt32 → UInt64 → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_set_input(
    b_lean_obj_arg handle, uint32_t idx, uint64_t val, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->set_input) h->set_input(h->ctx, idx, val);
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_get_output : @& JITHandle → UInt32 → IO UInt64 */
LEAN_EXPORT lean_obj_res sparkle_jit_get_output(
    b_lean_obj_arg handle, uint32_t idx, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    uint64_t val = h->get_output ? h->get_output(h->ctx, idx) : 0;
    return mk_io_ok(lean_box_uint64(val));
}

/* sparkle_jit_get_wire : @& JITHandle → UInt32 → IO UInt64 */
LEAN_EXPORT lean_obj_res sparkle_jit_get_wire(
    b_lean_obj_arg handle, uint32_t idx, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    uint64_t val = h->get_wire ? h->get_wire(h->ctx, idx) : 0;
    return mk_io_ok(lean_box_uint64(val));
}

/* sparkle_jit_set_mem : @& JITHandle → UInt32 → UInt32 → UInt32 → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_set_mem(
    b_lean_obj_arg handle, uint32_t mem_idx, uint32_t addr, uint32_t data,
    lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->set_mem) h->set_mem(h->ctx, mem_idx, addr, data);
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_get_mem : @& JITHandle → UInt32 → UInt32 → IO UInt32 */
LEAN_EXPORT lean_obj_res sparkle_jit_get_mem(
    b_lean_obj_arg handle, uint32_t mem_idx, uint32_t addr, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    uint32_t val = h->get_mem ? h->get_mem(h->ctx, mem_idx, addr) : 0;
    return mk_io_ok(lean_box_uint32(val));
}

/* sparkle_jit_memset_word : @& JITHandle → UInt32 → UInt32 → UInt32 → UInt32 → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_memset_word(
    b_lean_obj_arg handle, uint32_t mem_idx, uint32_t addr, uint32_t val,
    uint32_t count, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->memset_word) h->memset_word(h->ctx, mem_idx, addr, val, count);
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_wire_name : @& JITHandle → UInt32 → IO String */
LEAN_EXPORT lean_obj_res sparkle_jit_wire_name(
    b_lean_obj_arg handle, uint32_t idx, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    const char* name = h->wire_name ? h->wire_name(idx) : "";
    return mk_io_ok(lean_mk_string(name));
}

/* sparkle_jit_num_wires : @& JITHandle → IO UInt32 */
LEAN_EXPORT lean_obj_res sparkle_jit_num_wires(
    b_lean_obj_arg handle, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    uint32_t n = h->num_wires ? h->num_wires() : 0;
    return mk_io_ok(lean_box_uint32(n));
}

/* sparkle_jit_set_reg : @& JITHandle → UInt32 → UInt64 → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_set_reg(
    b_lean_obj_arg handle, uint32_t idx, uint64_t val, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->set_reg) h->set_reg(h->ctx, idx, val);
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_get_reg : @& JITHandle → UInt32 → IO UInt64 */
LEAN_EXPORT lean_obj_res sparkle_jit_get_reg(
    b_lean_obj_arg handle, uint32_t idx, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    uint64_t val = h->get_reg ? h->get_reg(h->ctx, idx) : 0;
    return mk_io_ok(lean_box_uint64(val));
}

/* sparkle_jit_reg_name : @& JITHandle → UInt32 → IO String */
LEAN_EXPORT lean_obj_res sparkle_jit_reg_name(
    b_lean_obj_arg handle, uint32_t idx, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    const char* name = h->reg_name ? h->reg_name(idx) : "";
    return mk_io_ok(lean_mk_string(name));
}

/* sparkle_jit_num_regs : @& JITHandle → IO UInt32 */
LEAN_EXPORT lean_obj_res sparkle_jit_num_regs(
    b_lean_obj_arg handle, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    uint32_t n = h->num_regs ? h->num_regs() : 0;
    return mk_io_ok(lean_box_uint32(n));
}

/* sparkle_jit_snapshot : @& JITHandle → IO UInt64 */
LEAN_EXPORT lean_obj_res sparkle_jit_snapshot(
    b_lean_obj_arg handle, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    void* snap = (h->snapshot) ? h->snapshot(h->ctx) : NULL;
    return mk_io_ok(lean_box_uint64((uint64_t)snap));
}

/* sparkle_jit_restore : @& JITHandle → UInt64 → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_restore(
    b_lean_obj_arg handle, uint64_t snap, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->restore && snap) h->restore(h->ctx, (void*)snap);
    return mk_io_ok(lean_box(0));
}

/* sparkle_jit_free_snapshot : @& JITHandle → UInt64 → IO Unit */
LEAN_EXPORT lean_obj_res sparkle_jit_free_snapshot(
    b_lean_obj_arg handle, uint64_t snap, lean_obj_arg w) {
    (void)w;
    JITHandle* h = get_handle(handle);
    if (h->free_snapshot && snap) h->free_snapshot((void*)snap);
    return mk_io_ok(lean_box(0));
}

/* ========================================================================
 * CDC Multi-Domain Runner (Phase 4)
 *
 * Loads cdc_runner.so/.dylib via dlopen and calls cdc_run() to execute
 * two JIT domains on separate threads with a lock-free SPSC queue.
 *
 * The CDC runner is a separate C++20 shared library because sparkle_jit.c
 * is compiled under Lean's -nostdinc (no <atomic>, <thread>, etc.).
 * ======================================================================== */

/* CDCJITVtable — must match cdc_runner.hpp */
typedef struct {
    void* ctx;
    void  (*eval_tick)(void*);
    void  (*set_input)(void*, uint32_t, uint64_t);
    uint64_t (*get_output)(void*, uint32_t);
    void* (*snapshot)(void*);
    void  (*restore)(void*, void*);
    void  (*free_snapshot)(void*);
} CDCJITVtable;

/* CDCRunResult — must match cdc_runner.hpp */
typedef struct {
    uint64_t messages_sent;
    uint64_t messages_received;
    uint64_t rollback_count;
    double   elapsed_ms;
    int      success;
} CDCRunResult;

/* Function pointer type for cdc_run */
typedef CDCRunResult (*cdc_run_fn)(
    CDCJITVtable*, CDCJITVtable*,
    uint64_t, uint64_t,
    uint32_t, uint32_t,
    uint32_t, uint32_t);

/* Cached dlopen handle for cdc_runner shared library */
static void* g_cdc_runner_lib = NULL;
static cdc_run_fn g_cdc_run = NULL;

static int ensure_cdc_runner(void) {
    if (g_cdc_run) return 1;

    /* Try platform-specific names */
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

/* Fill CDCJITVtable from JITHandle */
static void fill_vtable(CDCJITVtable* vt, JITHandle* h) {
    vt->ctx           = h->ctx;
    vt->eval_tick     = h->eval_tick;
    vt->set_input     = h->set_input;
    vt->get_output    = h->get_output;
    vt->snapshot      = h->snapshot;
    vt->restore       = h->restore;
    vt->free_snapshot = h->free_snapshot;
}

/*
 * sparkle_jit_run_cdc :
 *   @& JITHandle → @& JITHandle →
 *   UInt64 → UInt64 → UInt32 → UInt32 →
 *   IO (UInt64 × UInt64 × UInt64)
 *
 * Returns (messages_sent, messages_received, rollback_count).
 *
 * Parameters:
 *   handle_a  — JIT handle for domain A (producer / fast clock)
 *   handle_b  — JIT handle for domain B (consumer / slow clock)
 *   cycles_a  — number of eval_tick cycles for domain A
 *   cycles_b  — number of eval_tick cycles for domain B
 *   out_port_a — output port index to read from domain A
 *   in_port_b  — input port index to write to domain B
 */
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

    /* send_interval=2 (every other A-cycle), snapshot_interval=1000 */
    CDCRunResult res = g_cdc_run(&vt_a, &vt_b,
                                  cycles_a, cycles_b,
                                  out_port_a, in_port_b,
                                  2, 1000);

    if (!res.success) {
        return mk_io_error("CDC: cdc_run failed");
    }

    /* Return (sent, received, rollbacks) as a Lean tuple (Prod) */
    lean_obj_res v_sent = lean_box_uint64(res.messages_sent);
    lean_obj_res v_recv = lean_box_uint64(res.messages_received);
    lean_obj_res v_rb   = lean_box_uint64(res.rollback_count);

    /* Build (received, rollbacks) */
    lean_obj_res inner = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(inner, 0, v_recv);
    lean_ctor_set(inner, 1, v_rb);

    /* Build (sent, (received, rollbacks)) */
    lean_obj_res outer = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(outer, 0, v_sent);
    lean_ctor_set(outer, 1, inner);

    return mk_io_ok(outer);
}
