// JIT side of bench/gate/run.sh: load the CSim .so, put the firmware in
// the ROM, run N cycles.  With `trace` every UART byte is printed with
// the cycle it left on; without it the loop is only eval_tick, which is
// what the instruction counter measures.
//   harness_jit <jit.so> <rom.hex> <cycles> [trace]
// ROM_IDX / IN_READY / OUT_DATA / OUT_VALID come from jit_map.h, which
// run.sh derives from the generated C (the vtable has no name lookup
// for memories or ports).
#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <dlfcn.h>
#include "jit_map.h"

struct VT {
    void* (*create)(); void (*destroy)(void*);
    void (*reset)(void*); void (*eval)(void*);
    void (*tick)(void*); void (*eval_tick)(void*);
    void (*set_input)(void*, uint32_t, uint64_t);
    uint64_t (*get_output)(void*, uint32_t);
    uint64_t (*get_wire)(void*, uint32_t);
    void (*set_mem)(void*, uint32_t, uint32_t, uint32_t);
};

int main(int argc, char** argv) {
    if (argc < 4) { fprintf(stderr, "usage: %s <jit.so> <rom.hex> <cycles> [trace]\n", argv[0]); return 2; }
    void* lib = dlopen(argv[1], RTLD_NOW);
    if (!lib) { fprintf(stderr, "dlopen: %s\n", dlerror()); return 2; }
    auto get = (const VT* (*)())dlsym(lib, "jit_vtable");
    if (!get) { fprintf(stderr, "no jit_vtable in %s\n", argv[1]); return 2; }
    const VT* vt = get();
    void* ctx = vt->create();
    vt->reset(ctx);
    FILE* f = fopen(argv[2], "r");
    if (!f) { perror(argv[2]); return 2; }
    unsigned w; uint32_t a = 0;
    while (fscanf(f, "%x", &w) == 1) vt->set_mem(ctx, ROM_IDX, a++, w);
    fclose(f);
    vt->set_input(ctx, IN_READY, 1);
    uint64_t n = strtoull(argv[3], 0, 10);
    if (argc > 4 && !strcmp(argv[4], "trace")) {
        for (uint64_t c = 0; c < n; c++) {
            vt->eval_tick(ctx);
            if (vt->get_output(ctx, OUT_VALID))
                printf("%llu %02x\n", (unsigned long long)c, (unsigned)vt->get_output(ctx, OUT_DATA));
        }
    } else {
        for (uint64_t c = 0; c < n; c++) vt->eval_tick(ctx);
    }
    vt->destroy(ctx);
    return 0;
}
