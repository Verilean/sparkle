
# Chapter 1b — Your First Sparkle Project

Up to here we've been writing chapter cells inside the Sparkle
repo.  When you start your own design, you'll want a stand-alone
project that **imports Sparkle** as a Lake dependency.

This chapter walks through that layout end-to-end.  The canonical
reference is `docs/reference/How_To_Use.md`; this is the
tutorial-friendly version.

## Project tree

A typical Sparkle project looks like:

```
my-blinky/
├── lakefile.toml         ← Lake build manifest
├── lean-toolchain        ← matches Sparkle's toolchain
├── Main.lean             ← `def main` (executable entry point)
├── MyBlinky.lean         ← library root (re-exports submodules)
└── MyBlinky/
    └── Counter.lean      ← your library code
```

Three of those files contain real content:
`lakefile.toml`, `lean-toolchain`, and your library code.  The
others are nearly empty by convention.

## Step 1 — match Sparkle's `lean-toolchain`

Sparkle is compiled with a specific Lean version.  Your project
must use the same one or imports break.  Copy Sparkle's toolchain
value into your project's `lean-toolchain`:

```bash
curl -s https://raw.githubusercontent.com/Verilean/sparkle/main/lean-toolchain \
  > lean-toolchain
```

## Step 2 — declare Sparkle as a dependency

`lakefile.toml` (recommended for new projects):

```toml
name = "my-blinky"
defaultTargets = ["MyBlinky"]

[[require]]
name = "sparkle"
git = "https://github.com/Verilean/sparkle.git"
rev = "main"   # for reproducibility, pin a commit sha

[[lean_lib]]
name = "MyBlinky"

[[lean_exe]]
name = "blinky"
root = "Main"
```

Or `lakefile.lean` (older flavour, equally valid):

```text
import Lake
open Lake DSL

package «my-blinky» where

require sparkle from git
  "https://github.com/Verilean/sparkle.git" @ "main"

@[default_target]
lean_lib «MyBlinky» where

lean_exe «blinky» where
  root := `Main
```

## Step 3 — write your library

`MyBlinky/Counter.lean` — the library code.  Note the `import
Sparkle` at the top: that's the whole DSL in one line.

```text
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace MyBlinky.Counter

/-- A 4-bit counter that increments every cycle. -/
def blinky {dom : DomainConfig} : Signal dom (BitVec 4) :=
  circuit do
    let count ← Signal.reg 0#4
    count <~ count + 1#4
    return count

end MyBlinky.Counter
```

`MyBlinky.lean` — library root, re-exports submodules:

```text
import MyBlinky.Counter
```

`Main.lean` — executable entry, runs a tiny simulation:

```text
import MyBlinky

open Sparkle.Core.Domain Sparkle.Core.Signal
open MyBlinky.Counter

def main : IO Unit := do
  let trace := (blinky (dom := defaultDomain)).sample 16
  IO.println s!"blinky 16 cycles: {trace}"
```

## Step 4 — build and run

```bash
lake update    # fetch Sparkle
lake build     # compile your project
lake exe blinky
```

Expected output:

```
blinky 16 cycles: #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
```

## What's actually buildable here

We can't `lake new` from inside a Jupyter notebook, but we can
exercise **the code** that would live in `MyBlinky/Counter.lean`
and `Main.lean`, right here in this notebook.  The next cells
mirror those files line-for-line and prove that the design
compiles and simulates the way Step 4 expects.

```lean
import Sparkle
import Display

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Notebooks.Ch01b

```
The library code (would live in `MyBlinky/Counter.lean`):

```lean
/-- A 4-bit counter that increments every cycle. -/
def blinky {dom : DomainConfig} : Signal dom (BitVec 4) :=
  circuit do
    let count ← Signal.reg 0#4
    count <~ count + 1#4
    return count

```
The Main entry point (would live in `Main.lean`).  Sample 16
cycles and check the trace matches what `lake exe blinky` would
print.  Because BitVec wraps at width 4, after the first 16
cycles the counter rolls over.

```lean
def blinkyTrace : List (BitVec 4) :=
  (blinky (dom := defaultDomain)).sample 16

-- Defining the trace typechecks (proves the design is well-typed),
-- but actually evaluating `.sample` requires a JIT-linked native
-- helper that is only available under `lake exe`.  In a notebook
-- with the xeus-lean kernel, that linkage is in place — the cell
-- below works there.  Under plain `lake build` we can only
-- typecheck.

```
```lean
-- (Notebook only; commented out for `lake build` compatibility.)
-- #eval blinkyTrace

end Notebooks.Ch01b

```

### Try the shell commands inline

These cells use the `#bash` magic the xeus-lean kernel exposes
(it runs the argument under `bash -c` and dumps the output back
to the cell).  Outside the kernel they fall through to a Sparkle
shim that just prints what *would* run, so `lake build` stays
green either way.

```lean
#bash "lake --version"
```

```lean
#bash "curl -s https://raw.githubusercontent.com/Verilean/sparkle/main/lean-toolchain"
```

In a real project directory, the full Step 4 build cycle would
be a one-liner:

```lean
#bash "cd /path/to/my-blinky && lake update && lake build && lake exe blinky"
```

(Replace `/path/to/my-blinky` with your project root before
running.)

## Pinning Sparkle to a fixed commit

Production projects pin Sparkle to a specific commit so the
build is reproducible:

```toml
[[require]]
name = "sparkle"
git = "https://github.com/Verilean/sparkle.git"
rev = "abc123def..."   # full sha, or a tag like v0.5.0
```

`lake update` rewrites `lake-manifest.json` with the resolved
commits — commit that file alongside your `lakefile.toml`.

## More

- **Detailed reference**: `docs/reference/How_To_Use.md` covers
  the full Lake API: multiple libraries, executable targets,
  custom build steps, and how to add other dependencies.
- **CI**: see `.github/workflows/build.yml` in Sparkle for a
  reusable Lake-based GitHub Actions workflow.
