#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <chrono>
#include <dlfcn.h>

// CSim JIT ABI: the .so exports a single symbol `jit_vtable()` returning a
// pointer to a struct of function pointers (Issue #70 — one symbol avoids
// the multi-handle dlsym collision that the old per-symbol ABI hit).  We
// only need create / reset / eval_tick for the throughput loop.
struct JitVTable {
    void* (*create)(void);
    void  (*destroy)(void*);
    void  (*reset)(void*);
    void  (*eval)(void*);
    void  (*tick)(void*);
    void  (*eval_tick)(void*);
    // remaining fields (set_input/get_output/...) are unused here; we index
    // only the leading members, which are ABI-stable by struct layout.
};
typedef const JitVTable* (*vtable_fn)(void);

int main(int argc, char** argv) {
    uint64_t N = argc > 1 ? strtoull(argv[1],0,10) : 10000000;
    const char* so = argc > 2 ? argv[2] : "/tmp/litex_jit.so";
    void* lib = dlopen(so, RTLD_LAZY);
    if (!lib) { fprintf(stderr, "dlopen: %s\n", dlerror()); return 1; }
    auto get = (vtable_fn)dlsym(lib, "jit_vtable");
    if (!get) { fprintf(stderr, "no jit_vtable: %s\n", dlerror()); return 1; }
    const JitVTable* vt = get();
    void* ctx = vt->create();
    vt->reset(ctx);
    auto t0 = std::chrono::high_resolution_clock::now();
    for (uint64_t i = 0; i < N; i++) vt->eval_tick(ctx);
    auto t1 = std::chrono::high_resolution_clock::now();
    double ms = std::chrono::duration<double,std::milli>(t1-t0).count();
    printf("%.2f", N/ms/1000.0);
    vt->destroy(ctx); dlclose(lib); return 0;
}
