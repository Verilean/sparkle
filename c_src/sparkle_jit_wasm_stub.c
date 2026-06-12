/*
 * sparkle_jit_wasm_stub.c — WASM-side stub for Sparkle's JIT externs.
 *
 * The native JIT (c_src/sparkle_jit.c) opens compiled C++ shared
 * libraries via dlopen + dlsym at run time.  Neither dlopen nor the
 * underlying file-on-disk-then-mmap trick exists inside the
 * xeus-lean WASM sandbox, so the native sources can't be linked
 * straight into xlean.wasm.
 *
 * Instead, we link THIS file in place of `sparkle_jit.c` for the
 * WASM target.  Every Sparkle `@[extern "sparkle_jit_*"]` declaration
 * resolves to a stub that throws a clear, actionable IO error
 * explaining that JIT execution requires the native toolchain.
 *
 * Notebook cells that only use `#synthesizeVerilog`, `#showVerilog`,
 * pure `Signal.atTime` simulation, the `circuit do` macro, etc.
 * remain fully functional under WASM — those paths don't touch the
 * JIT externs at all.
 */

#include <lean/lean.h>

extern int snprintf(char* buf, unsigned long size, const char* fmt, ...);

/* ------------------------------------------------------------------
   Shared error-builder.  Every JIT stub funnels through here so the
   diagnostic text is uniform.

   Lean's IO error layout is `Except.error <ε> : Except ε α` packed
   as a tagged object (ctor 1 = .error, 0 = .ok).  For an
   `IO α := EIO IO.Error α`, the error payload is a `String`.
   ------------------------------------------------------------------ */
static lean_obj_res sparkle_jit_wasm_unsupported(const char* fn_name) {
    char buf[512];
    snprintf(buf, sizeof(buf),
             "Sparkle.Core.JIT.%s is not available in the WASM kernel.\n"
             "  JIT execution loads a compiled shared library via dlopen,\n"
             "  which the xeus-lean WASM sandbox does not provide.\n"
             "  Use #synthesizeVerilog / #showVerilog for synthesis, or\n"
             "  run the JIT path from a native `lake exe` build.",
             fn_name);
    lean_object* msg = lean_mk_string(buf);
    lean_object* err = lean_alloc_ctor(18, 1, 0); /* IO.Error.userError */
    lean_ctor_set(err, 0, msg);
    lean_object* tagged = lean_alloc_ctor(1, 1, 0); /* Except.error */
    lean_ctor_set(tagged, 0, err);
    return lean_io_result_mk_error(tagged);
}

/* The `JITHandle` Lean type is `NonemptyType`, so we never actually
   need a real handle — every stub fails before we'd dereference one.
   The functions still need to type-check at the C ABI: argument refs
   must be decremented before returning. */

/* ------------------------------------------------------------------
   IO α stubs — every JIT.* declared `IO α` in Sparkle/Core/JIT.lean.
   ------------------------------------------------------------------ */

LEAN_EXPORT lean_obj_res sparkle_jit_load(b_lean_obj_arg path) {
    (void)path; /* borrowed, no dec */
    return sparkle_jit_wasm_unsupported("JIT.load");
}

LEAN_EXPORT lean_obj_res sparkle_jit_eval(b_lean_obj_arg h) {
    (void)h;
    return sparkle_jit_wasm_unsupported("JIT.eval");
}

LEAN_EXPORT lean_obj_res sparkle_jit_tick(b_lean_obj_arg h) {
    (void)h;
    return sparkle_jit_wasm_unsupported("JIT.tick");
}

LEAN_EXPORT lean_obj_res sparkle_jit_eval_tick(b_lean_obj_arg h) {
    (void)h;
    return sparkle_jit_wasm_unsupported("JIT.evalTick");
}

LEAN_EXPORT lean_obj_res sparkle_jit_reset(b_lean_obj_arg h) {
    (void)h;
    return sparkle_jit_wasm_unsupported("JIT.reset");
}

LEAN_EXPORT lean_obj_res sparkle_jit_destroy(b_lean_obj_arg h) {
    (void)h;
    return sparkle_jit_wasm_unsupported("JIT.destroy");
}

LEAN_EXPORT lean_obj_res sparkle_jit_set_input(b_lean_obj_arg h,
                                                uint32_t portIdx,
                                                uint64_t value) {
    (void)h; (void)portIdx; (void)value;
    return sparkle_jit_wasm_unsupported("JIT.setInput");
}

LEAN_EXPORT lean_obj_res sparkle_jit_get_output(b_lean_obj_arg h,
                                                 uint32_t portIdx) {
    (void)h; (void)portIdx;
    return sparkle_jit_wasm_unsupported("JIT.getOutput");
}

LEAN_EXPORT lean_obj_res sparkle_jit_get_wire(b_lean_obj_arg h,
                                               uint32_t wireIdx) {
    (void)h; (void)wireIdx;
    return sparkle_jit_wasm_unsupported("JIT.getWire");
}

LEAN_EXPORT lean_obj_res sparkle_jit_set_mem(b_lean_obj_arg h,
                                              uint32_t memIdx,
                                              uint32_t addr,
                                              uint32_t data) {
    (void)h; (void)memIdx; (void)addr; (void)data;
    return sparkle_jit_wasm_unsupported("JIT.setMem");
}

LEAN_EXPORT lean_obj_res sparkle_jit_get_mem(b_lean_obj_arg h,
                                              uint32_t memIdx,
                                              uint32_t addr) {
    (void)h; (void)memIdx; (void)addr;
    return sparkle_jit_wasm_unsupported("JIT.getMem");
}

LEAN_EXPORT lean_obj_res sparkle_jit_memset_word(b_lean_obj_arg h,
                                                  uint32_t memIdx,
                                                  uint32_t addr,
                                                  uint32_t val,
                                                  uint32_t count) {
    (void)h; (void)memIdx; (void)addr; (void)val; (void)count;
    return sparkle_jit_wasm_unsupported("JIT.memsetWord");
}

LEAN_EXPORT lean_obj_res sparkle_jit_snapshot(b_lean_obj_arg h) {
    (void)h;
    return sparkle_jit_wasm_unsupported("JIT.snapshot");
}

LEAN_EXPORT lean_obj_res sparkle_jit_restore(b_lean_obj_arg h, uint64_t snap) {
    (void)h; (void)snap;
    return sparkle_jit_wasm_unsupported("JIT.restore");
}

LEAN_EXPORT lean_obj_res sparkle_jit_free_snapshot(b_lean_obj_arg h, uint64_t snap) {
    (void)h; (void)snap;
    return sparkle_jit_wasm_unsupported("JIT.freeSnapshot");
}

LEAN_EXPORT lean_obj_res sparkle_jit_wire_name(b_lean_obj_arg h, uint32_t wireIdx) {
    (void)h; (void)wireIdx;
    return sparkle_jit_wasm_unsupported("JIT.wireName");
}

LEAN_EXPORT lean_obj_res sparkle_jit_num_wires(b_lean_obj_arg h) {
    (void)h;
    return sparkle_jit_wasm_unsupported("JIT.numWires");
}

LEAN_EXPORT lean_obj_res sparkle_jit_set_reg(b_lean_obj_arg h,
                                              uint32_t regIdx,
                                              uint64_t value) {
    (void)h; (void)regIdx; (void)value;
    return sparkle_jit_wasm_unsupported("JIT.setReg");
}

LEAN_EXPORT lean_obj_res sparkle_jit_get_reg(b_lean_obj_arg h, uint32_t regIdx) {
    (void)h; (void)regIdx;
    return sparkle_jit_wasm_unsupported("JIT.getReg");
}

LEAN_EXPORT lean_obj_res sparkle_jit_reg_name(b_lean_obj_arg h, uint32_t regIdx) {
    (void)h; (void)regIdx;
    return sparkle_jit_wasm_unsupported("JIT.regName");
}

LEAN_EXPORT lean_obj_res sparkle_jit_num_regs(b_lean_obj_arg h) {
    (void)h;
    return sparkle_jit_wasm_unsupported("JIT.numRegs");
}

LEAN_EXPORT lean_obj_res sparkle_jit_run_cdc(b_lean_obj_arg ha,
                                              b_lean_obj_arg hb,
                                              uint64_t cyclesA,
                                              uint64_t cyclesB,
                                              uint32_t outPortA,
                                              uint32_t inPortB) {
    (void)ha; (void)hb; (void)cyclesA; (void)cyclesB; (void)outPortA; (void)inPortB;
    return sparkle_jit_wasm_unsupported("JIT.runCDC");
}
