# Sparkle Compiler — Performance & Profiling Notes

This doc captures what we learned chasing the
`#synthesizeVerilog rxFramer` timeout, how to reproduce
the measurements, and how to diagnose similar regressions
in the future.  It is intentionally long on numbers and
short on theory so a future maintainer can pattern-match.

---

## The bottom line

The Sparkle synth pipeline (`translateExprToWire` and its
~10 sibling handlers in `Sparkle/Compiler/Elab.lean`) walks
a Lean `Expr` and emits Verilog assignments.  When a
sub-expression appears N times in the surface syntax, a
naïve walk re-translates it N times — and because each
recursion fires `Lean.Meta.whnf` / typeclass dispatch /
`unfoldDefinition?` chains as side effects of *handler
logic* (not the Meta calls themselves), the per-call cost
grows from "a few µs of bookkeeping" to "tens of ms of
typeclass churn".

**Two cache leaks were live until June 2026** that turned
this from a theoretical concern into a 180-second timeout:

1. The Expr cache was *read* on entry but *written* only
   from one fall-through arm.  Every early-intercept
   handler (Signal `HAdd`/`HSub`/..., `OfNat` literal,
   `HAppend`) returned its wire directly without populating
   the cache.  Hit rate sat at **0 %**.

2. `RxOut.dmac (rxFramer …)` was routed to
   `synthesizeCombinational RxOut.dmac` (the structure
   field accessor was treated as a hardware module),
   leading to *"requires 6 args, but got 2"*.

The fix landed in `119817c` + `7da1e58`:

- Split into a thin caching shim wrapping the inner impl
  so every successful translate populates the cache.
- Detect projections via `env.getProjectionStructureName?`
  and inline them.

On the `acc4` probe (4 × repeated `(a+b+c+d)`):

```
BEFORE: 1 giant unshared assign,           runtime ~820 ms (Lean startup-dominated)
AFTER:  1 shared sub-expression + 4 refs,  runtime ~800 ms
        wire count: 0 → 1 named wire
```

On the `rxFramer` Ethernet probe (single-output projection):

```
BEFORE: 180 s timeout, cache hit rate 0 %
AFTER:  ~1 s fast-fail (different downstream bug),
        cache hit rate 20 % (1 273 hits / 6 358 calls)
```

The "fast-fail" is itself progress — the cache let us
*reach* the next blocker, which is the
`RxOut.mk`-construction-not-reduced issue documented in
TODO.md C5.b.

---

## Was it really a typeclass problem?

**No — at least not directly.**  The natural hypothesis
("Lean's `outParam`-driven typeclass resolution is the
culprit") was wrong in the literal sense.  Direct counters
on `Lean.Meta.inferType` / `Lean.Meta.whnf` /
`Lean.Meta.unfoldDefinition?` show they each cost
~2 µs/call:

```
Meta inferType:  1887 calls /     4 ms   (cache miss path only)
Meta whnf:          0 calls /     0 ms
Meta unfoldDef?:    0 calls /     0 ms
```

The actual cost lives in `translateExprToWire` itself —
specifically in how often the same sub-expression is
re-walked.  The handler-level profile shows:

```
handleTupleProjections:  2549 calls / 189 532 ms   (~74  ms / call inclusive)
handleDefinitionUnfold:   903 calls /  22 934 ms   (~25  ms / call inclusive)
handleMux:               1285 calls /   3 169 ms   (~2.5 ms / call inclusive)
handleCircuitMonad:      2965 calls /     758 ms   (~256 µs / call inclusive)
```

These are **inclusive** times.  A 74 ms `handleTupleProjections`
call recursively walks ~tens of thousands of sub-expressions,
each of which would re-fire its own handler chain without
caching.  The cache wrapper attacks this by short-circuiting
the second-through-Nth identical walks.

That said, typeclass dispatch *is* the underlying expense:
each handler-internal `inferType` / `whnf` is mostly
unification of `Signal dom α` types, and Lean 4's `outParam`
resolution does fire `whnf` on every search step.  The cache
makes this irrelevant by avoiding the calls in the first
place.

---

## How to reproduce the measurements

### 1. Enable the profile log

The compiler ships an `SPARKLE_PROFILE` env hook.  When set
to `1`, `translateExprToWire` writes a per-handler tick log
to `/tmp/sparkle-profile.log` every 10 000 calls.

```bash
rm -f /tmp/sparkle-profile.log
SPARKLE_PROFILE=1 timeout 180 lake env lean path/to/probe.lean \
  > /tmp/probe.out 2>&1
tail -30 /tmp/sparkle-profile.log
```

A tick line looks like:

```
[profile] tick 10000 (cache hits 1273, typeCache hits=1746 miss=1887)
  Meta whnf:       0 calls / 0 ms
  Meta inferType:  1887 calls / 4 ms
  Meta unfoldDef?: 0 calls / 0 ms
  handleErrorPatterns:    2967 calls /     3 ms
  handleCircuitMonad:     2965 calls /   758 ms
  handleTupleProjections: 2549 calls / 189532 ms   ← hot
  handleApplicative:      1285 calls /     0 ms
  handleBitVecOps:        1285 calls /     7 ms
  handleRegister:         1285 calls /     3 ms
  handleMux:              1285 calls /  3169 ms
  handleMemory:            907 calls /     1 ms
  handleLoop:              906 calls /     0 ms
  handleDefinitionUnfold:  903 calls / 22934 ms   ← hot
```

The two things to look at:

- **`cache hits` / total calls** — a ratio under ~10 % on a
  multi-output circuit usually means a handler is returning
  without writing back to the cache.  Investigate which
  handler.
- **Per-handler `inclusive ms / calls`** — anything above
  ~10 ms / call is suspect.  Walk that handler's recursion
  and look for missing cache writes, redundant `whnf`s, or
  un-bounded `unfoldDefinition?` chains.

### 2. Cache-effectiveness probe (`acc4`)

```lean
-- /tmp/acc4.lean
import Sparkle ; import Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal

def acc4 (a b c d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  (a + b + c + d) + (a + b + c + d) + (a + b + c + d) + (a + b + c + d)

#synthesizeVerilog acc4
```

Run, then `grep assign` the output:

- **Cache effective**: one `_tmp_op_a_N` assignment, then a
  single `out = (_tmp_op_a_N + _tmp_op_a_N + …)`.
- **Cache broken**: the `(a+b+c+d)` chain repeats verbatim
  inside the `out` assignment.

### 3. End-to-end timing

```bash
for i in 1 2 3; do
  t0=$(date +%s%N)
  lake env lean /tmp/probe.lean > /dev/null 2>&1
  t1=$(date +%s%N)
  echo "run$i: $(( (t1-t0)/1000000 ))ms"
done
```

Most of the ~800 ms baseline is Lean startup + import
processing — synth cost only dominates once probes get
into the multi-second range (Ethernet `rxFramer`,
PicoRV32 SoC, etc.).

---

## Where to look in the code

| Symbol                                 | Location                       | What to check                                    |
|----------------------------------------|--------------------------------|--------------------------------------------------|
| `translateExprToWire`                  | `Sparkle/Compiler/Elab.lean`   | Caching shim around `Impl`                       |
| `translateExprToWireImpl`              | same file                      | Inner impl — must NOT write to cache directly    |
| `sparkleCallCounter` / `sparkleCacheHits` | same file                  | Profile counters; tick log every 10 000 calls    |
| `sparkleHandlerCalls` / `sparkleHandlerMs` | same file                 | Per-handler inclusive timings (11 handlers)      |
| `handleDefinitionUnfold`               | same file, ~L1777              | Inlines / sub-module synthesis dispatch          |
| `handleTupleProjections`               | same file                      | `Prod.fst` / `Prod.snd` and structure fields     |
| `splitReturnLeaves`                    | same file                      | Pre-reduces ρ-generic record returns at synth entry |
| `openRecordInputs`                     | same file                      | Pre-unpacks record-typed parameters              |
| `cachedInferType`                      | same file                      | Expr-keyed `inferType` memoisation               |

If you add a new handler arm, **always return through the
shim** — don't bypass `translateExprToWire` with a direct
`emitAssign` and `return`.  The shim is what populates the
Expr cache; bypassing it re-introduces the leak that took
180 s to manifest.

---

## What still doesn't work

- **Multi-output record return** (e.g. `rxFramer` returning
  `RxOut dom`).  The cache wrapper unblocked the
  single-output projection path in ~1 s wall-clock, but the
  underlying `(rxFramer …).dmac` end-to-end still fails
  because `unfoldDefinition?` peels one layer and leaves a
  `RxOut.mk` constructor whose record fields haven't been
  reduced to `Signal.mk` wires.  See TODO.md C5.b for the
  next-round fix candidates.

- **`@[reducible] instance` chains in user code** — when an
  instance head expands at typeclass resolution time, the
  result is invisible to the Expr cache (different fvar
  IDs each time).  If a user writes
  `@[reducible] instance : HAdd (MyT α) (MyT α) (MyT α) := …`
  expect cache hit rates to drop on that type.  Workaround:
  drop the `@[reducible]` and rely on `@[default_instance]`
  instead.

- **`Date.now()` / wall-clock measurement inside the
  compiler** — not available in the Lean runtime as used
  by `lake env lean`.  Use `IO.monoMsNow` (we do) or shell
  `date +%s%N` for outer wall-clock.
