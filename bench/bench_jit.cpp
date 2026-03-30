#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <chrono>
#include <dlfcn.h>
typedef void*(*fn0)(); typedef void(*fn1)(void*);
int main(int argc, char** argv) {
    uint64_t N = argc > 1 ? strtoull(argv[1],0,10) : 10000000;
    const char* so = argc > 2 ? argv[2] : "/tmp/litex_jit.so";
    void* lib = dlopen(so, RTLD_LAZY);
    if (!lib) { fprintf(stderr, "dlopen: %s\n", dlerror()); return 1; }
    auto c=(fn0)dlsym(lib,"jit_create"); auto d=(fn1)dlsym(lib,"jit_destroy");
    auto r=(fn1)dlsym(lib,"jit_reset"); auto e=(fn1)dlsym(lib,"jit_eval_tick");
    void* ctx=c(); r(ctx);
    auto t0=std::chrono::high_resolution_clock::now();
    for(uint64_t i=0;i<N;i++) e(ctx);
    auto t1=std::chrono::high_resolution_clock::now();
    double ms=std::chrono::duration<double,std::milli>(t1-t0).count();
    printf("%.2f", N/ms/1000.0);
    d(ctx); dlclose(lib); return 0;
}
