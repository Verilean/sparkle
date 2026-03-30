#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <chrono>
#include <dlfcn.h>
typedef void*(*fn0)(); typedef void(*fn1)(void*);
struct MulticoreResult { uint64_t total_cycles; double elapsed_ms; double mcycles_per_sec; int success; };
typedef MulticoreResult(*mc_fn)(void*,int,uint64_t,int);

int main(int argc, char** argv) {
    uint64_t N = argc > 1 ? strtoull(argv[1],0,10) : 10000000;
    const char* jit_so = argc > 2 ? argv[2] : "/tmp/hier_jit.so";
    const char* runner_so = argc > 3 ? argv[3] : "/tmp/mc_runner.so";

    void* jit = dlopen(jit_so, RTLD_LAZY);
    if (!jit) { fprintf(stderr, "JIT: %s\n", dlerror()); return 1; }
    auto create=(fn0)dlsym(jit,"jit_create");
    auto destroy=(fn1)dlsym(jit,"jit_destroy");
    auto reset=(fn1)dlsym(jit,"jit_reset");
    auto et=(fn1)dlsym(jit,"jit_eval_tick");

    // 1-core
    void* ctx=create(); reset(ctx);
    auto t0=std::chrono::high_resolution_clock::now();
    for(uint64_t c=0;c<N;c++) et(ctx);
    auto t1=std::chrono::high_resolution_clock::now();
    double ms1=std::chrono::duration<double,std::milli>(t1-t0).count();
    printf("1-core:     %.2fM cyc/s\n", N/ms1/1000.0);
    destroy(ctx);

    // 8-core sequential
    void* cores[8];
    for(int i=0;i<8;i++){cores[i]=create();reset(cores[i]);}
    t0=std::chrono::high_resolution_clock::now();
    for(uint64_t c=0;c<N;c++) for(int i=0;i<8;i++) et(cores[i]);
    t1=std::chrono::high_resolution_clock::now();
    double ms8=std::chrono::duration<double,std::milli>(t1-t0).count();
    printf("8-seq:      %.2fM per-core cyc/s\n", N/ms8/1000.0);
    for(int i=0;i<8;i++) destroy(cores[i]);

    // 8-core parallel
    void* runner = dlopen(runner_so, RTLD_LAZY);
    if (runner) {
        auto mc_run=(mc_fn)dlsym(runner,"multicore_run");
        if (mc_run) {
            auto r=mc_run(jit, 8, N, 10000);
            printf("8-parallel: %.2fM per-core cyc/s (%.1fx vs seq)\n",
                   r.mcycles_per_sec, r.mcycles_per_sec/(N/ms8/1000.0));
        }
        dlclose(runner);
    } else {
        fprintf(stderr, "Runner: %s\n", dlerror());
    }
    dlclose(jit);
    return 0;
}
