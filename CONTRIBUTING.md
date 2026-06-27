# Contributing to Sparkle

Thanks for adding to the Sparkle IP catalog!  This file lays
out the bare minimum a new contribution needs to land cleanly
and stay green in CI.

## Quick checklist for "I added a new IP"

If you've written `IP/<Family>/<Name>.lean` and want it on the
main branch, you need **all** of the following.  Skipping any
of these means the IP isn't actually covered — `lake build`
passing is type-checking, not behaviour.

1. **Pure-data spec** (oracle)
2. **Sim test** that compares HW vs spec cycle-by-cycle
3. **`#synthesizeVerilog` check** in the test file
4. **`lakefile.lean` entries** for the lib + the test exe
5. **`.github/workflows/ip-tests.yml` matrix entry**
6. **(optional) `Tests/AllTests.lean` import** if the test
   should also run inside the `lake exe test` release gate

Each step is detailed below.  See `IP/Bus/CANHW.lean` +
`Tests/IP/Bus/CANHWTest.lean` for a small, complete example.

---

## 1. Pure-data spec (the oracle)

A new HW IP is only "done" when there's something to compare
its cycle-by-cycle behaviour against.  The cleanest way is a
pure-data Lean function that mirrors the spec:

```lean
-- IP/Crypto/MyCipher.lean
namespace Sparkle.IP.Crypto.MyCipher

/-- Pure-data encryption — the reference semantics. -/
def encrypt (key : BitVec 128) (block : BitVec 128) : BitVec 128 :=
  -- … plain Lean, no Signal types …

/-- Signal-DSL HW version — must produce the same output. -/
def encryptHW {dom : DomainConfig}
    (key : Signal dom (BitVec 128))
    (block : Signal dom (BitVec 128)) :
    Signal dom (BitVec 128) :=
  circuit do
    -- … the actual hardware … --
```

If the IP is **inherently** byte-stream-shaped (a UART, a
parser, a network protocol) the oracle can be a pure
`List UInt8 → List UInt8` function and the sim test feeds
both with the same stimulus.  See `IP/Net/Memcached.lean`
(pure parser + KV store) ↔ `IP/Net/MemcachedHW.lean`
(Signal-DSL BRAM-backed engine).

## 2. Sim test (cycle-accurate)

A `Tests/IP/<Family>/<Name>Test.lean` file with a `def main :
IO Unit` that:

1. Drives the HW `Signal.circuit do` with a known input stream.
2. Samples the output cycle-by-cycle via `.val t`.
3. Asserts every output matches the pure-data oracle's
   prediction for the same input.

```lean
-- Tests/IP/Crypto/MyCipherTest.lean
import IP.Crypto.MyCipher

namespace Sparkle.Tests.IP.Crypto.MyCipherTest

def main : IO Unit := do
  let key   : Signal defaultDomain (BitVec 128) := Signal.pure 0xdeadbeef…#128
  let block : Signal defaultDomain (BitVec 128) := Signal.pure 0xcafe…#128
  let hw    := encryptHW key block
  -- HW engine takes N cycles; sample at cycle N.
  let got      := hw.val 10
  let expected := encrypt 0xdeadbeef…#128 0xcafe…#128
  if got = expected then IO.println "  ✓ HW matches oracle"
  else
    IO.println s!"  ✗ mismatch: got=0x{Nat.toDigits 16 got.toNat |>.toString.toLower}"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.MyCipherTest
```

Plus a one-line driver under `Tests/Drivers/`:

```lean
-- Tests/Drivers/MyCipherTestMain.lean
import Tests.IP.Crypto.MyCipherTest

def main : IO Unit := Sparkle.Tests.IP.Crypto.MyCipherTest.main
```

## 3. `#synthesizeVerilog` check

Inside the same test file, add a synthesis check.  The synth
elaborator is **separate from the Lean type checker** — a `def`
that type-checks can still fail to compile to Verilog.  Without
this check, sim-pass / synth-fail regressions slip past.

```lean
section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.MyCipher

private def synth_encryptHW
    (key : Signal defaultDomain (BitVec 128))
    (block : Signal defaultDomain (BitVec 128)) :
    Signal defaultDomain (BitVec 128) :=
  encryptHW key block

#synthesizeVerilog synth_encryptHW

end SynthesisChecks
```

If `#synthesizeVerilog` fails, scan for the patterns in the
"Synth elaborator gotchas" note (see your auto-memory) —
the most common ones are `(fun b => !b)` Bool lifts,
`(· != ·)` comparisons, and tuple returns from `circuit do`.

The synth check runs at **`lake build` time** of the test
module, so it's automatically covered once you wire the test
into `lakefile.lean` (next step).

## 4. `lakefile.lean` entries

Two changes:

```lean
-- (a) make sure the IP family lib's `roots` covers your file
lean_lib «IP.Crypto» where
  roots := #[`IP.Crypto]   -- already there for most families

-- (b) add the test executable
lean_exe «my-cipher-test» where
  root := `Tests.Drivers.MyCipherTestMain
  supportInterpreter := true
```

`supportInterpreter := true` is required so the test driver can
evaluate `Signal.val t` via the native FFI sim path.

## 5. `.github/workflows/ip-tests.yml`

Add the test executable to the matrix:

```yaml
matrix:
  exe:
    # … existing entries …
    - my-cipher-test     # under the right topic group
```

The CI workflow runs each entry as `lake exe <name>` in its own
parallel shard.  Without this, `lake build` will still
type-check your test, but the cycle-by-cycle assertions never
actually execute in CI — DSL changes that break your IP's
runtime semantics won't be caught.

Verify the matrix list matches `lakefile.lean`'s
`lean_exe` entries (minus the bins / docs / traces — see the
yaml's comment for the explicit skip list).

## 6. (optional) `Tests/AllTests.lean`

If the test is fast (< 1s) and you want it as part of the
release-gate `lake exe test`, add an import and a call:

```lean
import Tests.IP.Crypto.MyCipherTest

-- in `def main : IO UInt32 := do`
Sparkle.Tests.IP.Crypto.MyCipherTest.main
IO.println ""
```

For slow tests (BitVec 128 sim, long FSM horizons) **don't**
add them to AllTests — they'll bloat the release-gate wall
clock.  The per-IP CI matrix is enough.

---

## What NOT to do

* Don't commit IP code without a sim test.  "Builds clean"
  proves type-checking; it doesn't prove the HW does what
  the docstring claims.
* Don't skip `#synthesizeVerilog`.  Sim-correct but
  synth-broken IPs accumulate silently and surface as a
  giant pile of work when someone tries to actually flash
  an FPGA.
* Don't add an IP and forget the CI matrix entry.  The
  current cohort took six months and revealed that 26 test
  files were never running in CI because nobody plugged
  them in.  The matrix is the single source of truth — if
  it's not there, the test isn't running.

## Common synth-elaborator gotchas

These patterns sim-pass but break `#synthesizeVerilog`:

| Pattern                                | Fix                                                   |
| -------------------------------------- | ----------------------------------------------------- |
| `sig.map (fun _ => true)`              | drop or use `Signal.pure true`                        |
| `sig.map (fun b => if b then a else b)`| `Signal.mux sig (Signal.pure a) (Signal.pure b)`      |
| `(· != ·) <$> a <*> b`                 | `(fun a b => !(a == b)) <$> a <*> b`                  |
| `Bool.not <$> sig`                     | `(fun b => !b) <$> sig`                               |
| `return (a, b)` from `circuit do`      | wrap in a `structure` with `HasDomain` (see Ethernet.RxOut) |
| `Signal.map identity-lambda inner`     | pass `inner` directly                                 |

When `#synthesizeVerilog` fails, set
`set_option trace.sparkle.compiler true` to see which
expression the elaborator gets stuck on, then check the
table above.

The elaborator also has a runtime cap (`SPARKLE_TRANSLATE_LIMIT`,
default 500k) — if your IP hits it, the error message names
the deepest hint so you can grep the trace.

## When something is genuinely blocked

If you find a bug in Sparkle itself (Compiler/Elab, Core/Signal,
Core/CircuitMonad), please open an issue with:

* The failing IP (minimal repro if possible).
* `SPARKLE_PROFILE=1` output of `/tmp/sparkle-profile.log`.
* Any trace excerpts that show the failure point.

The Compiler bug class is small but bites hard — see
`project_memcached_status.md` in the maintainer's auto-memory
for an example of how to debug a synth hang end-to-end.

---

Welcome aboard.
