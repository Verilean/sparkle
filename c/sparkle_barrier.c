#include <lean/lean.h>

/*
 * Cache reader for Signal DSL memoization.
 * Reads arr[t] from an IO.Ref, entirely in C to prevent LICM hoisting.
 *
 * One-element LRU cache: during each timestep evaluation, ~56+ calls
 * request the same (ref, t) pair. The LRU avoids redundant IORef reads.
 *
 * Parameters (after type erasure):
 *   ref      : @& IO.Ref (Array α) — borrowed IORef
 *   t        : @& Nat              — borrowed timestep
 *   fallback : α                   — owned fallback value
 */
static lean_object* g_lru_ref = NULL;
static size_t       g_lru_t   = (size_t)-1;
static lean_object* g_lru_val = NULL;

LEAN_EXPORT lean_obj_res sparkle_cache_get(
    b_lean_obj_arg ref, b_lean_obj_arg t_obj, lean_obj_arg fallback) {
    size_t t = lean_unbox(t_obj);

    /* LRU hit: same ref and same t → return cached value */
    if (ref == g_lru_ref && t == g_lru_t && g_lru_val != NULL) {
        lean_inc(g_lru_val);
        lean_dec(fallback);
        return g_lru_val;
    }

    lean_obj_res arr = lean_st_ref_get(ref);
    size_t sz = lean_array_size(arr);

    if (t < sz) {
        lean_obj_res val = lean_array_uget(arr, t);
        lean_inc(val);
        lean_dec(arr);
        lean_dec(fallback);

        /* Update LRU cache */
        if (g_lru_val != NULL) lean_dec(g_lru_val);
        g_lru_ref = (lean_object*)ref;  /* borrowed — valid while loopMemo closure lives */
        g_lru_t   = t;
        g_lru_val = val;
        lean_inc(g_lru_val);  /* keep extra ref for cache */

        return val;
    } else {
        lean_dec(arr);
        return fallback;
    }
}

/*
 * Signal evaluator for memoization loop body.
 * Evaluates `signal_val(t)` inside an IO action so the Lean compiler
 * cannot reorder it relative to other IO operations (like cacheRef.swap).
 *
 * Without this, the compiler moves `inner.val i` (a pure expression)
 * AFTER `cacheRef.swap #[]`, causing the cache to be empty during
 * evaluation. This wrapper makes the evaluation an IO action with
 * proper sequencing.
 *
 * Parameters (after type erasure):
 *   signal_val : @& (Nat → α) — borrowed signal function
 *   t          : @& Nat       — borrowed timestep
 *   world      : IO.RealWorld — IO state
 * Returns: EStateM.Result (ok: value, world)
 */
LEAN_EXPORT lean_obj_res sparkle_eval_at(
    b_lean_obj_arg signal_val, b_lean_obj_arg t, lean_obj_arg world) {
    lean_dec(world);
    /* Evaluate signal_val(t) */
    lean_inc(signal_val);
    lean_inc(t);
    lean_obj_res val = lean_apply_1(signal_val, t);

    /* Return IO ok result: EStateM.Result.ok val world */
    lean_obj_res result = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result, 0, val);
    lean_ctor_set(result, 1, lean_io_mk_world());
    return result;
}
