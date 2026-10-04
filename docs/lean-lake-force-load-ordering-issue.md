# Interpreter/LSP force-loads a non-precompiled lib's shared library before its precompiled dependencies → undefined-symbol load failure

## Summary

When a **precompiled** `lean_lib` (`precompileModules := true`) contains a module
that imports a **non-precompiled** `lean_lib`, the interpreter / language server
force-loads the non-precompiled lib's *monolithic* shared library (via
`--load-dynlib`, as reported by `lake setup-file`) **at interpreter startup —
before** the precompiled dependency's per-module dynlibs are loaded through the
olean import mechanism.

The monolithic `.so` carries unresolved references to the precompiled lib's
compiled symbols — in particular compiler-generated cross-module closures such
as `…_map___redArg___lam__0` and module initializers such as
`initialize_<Pkg>_<RootModule>`. Because nothing has loaded the precompiled
lib yet, `dlopen` fails:

```
error loading library .../libpkg_NonPrecompiled.so:
  undefined symbol: lp_pkg_Dep_Foo_map___redArg___lam__0
```

A plain `lake build` and `lake env lean <file>` both succeed (they load the
precompiled dependency's per-module dynlibs in import order). Only the
force-load path (LSP / `lake setup-file`) fails, which makes it look like a
"works on the command line, broken in the editor" mystery.

## Environment

- Lean / Lake: `leanprover/lean4:v4.28.0`
- OS: Linux (x86_64, glibc), GNU `ld`
- Trigger: a recent code change that caused a generic `Signal.map`-style
  function to be referenced **cross-module** by the non-precompiled lib (the
  compiler then emits a shared `___redArg___lam__0` closure symbol in the
  precompiled lib that the non-precompiled lib's `.so` references).

## Observed (real project)

`lake setup-file` for a precompiled module that imports a non-precompiled lib
returns this `--load-dynlib` set (order significant):

```
.lake/build/c_src/libpkg_barrier.so        # extern_lib
.lake/build/c_src/libpkg_jit.so            # extern_lib
.lake/build/lib/libpkg_IP_x2eFoo.so        # NON-precompiled lib, monolithic
.lake/build/lib/libpkg_IP_x2eBar.so        # NON-precompiled lib, monolithic
```

Note what is **absent**: the precompiled dependency's dynlibs
(`libpkg_Dep.so` / `.lake/build/lib/lean/pkg_Dep_*.so`). Those are loaded later,
via olean imports, *after* the monolithic libs above are already force-loaded.

`nm -D` on the force-loaded monolithic shows the unresolved references:

```
U lp_pkg_Dep_Core_Signal_Signal_map___redArg___lam__0
U initialize_pkg_Dep                      # the dependency's ROOT-module init
```

Reproducing the load order by hand (Lean runtime preloaded, `RTLD_GLOBAL`):

```python
# A) force-load the monolithic first (what the editor does)  -> FAILS
load("libpkg_IP_x2eFoo.so")
#   -> undefined symbol: lp_pkg_Dep_Core_Signal_Signal_map___redArg___lam__0

# B) load the precompiled dependency's per-module .so first   -> OK
load("lib/lean/pkg_Dep_Core_Signal.so"); ... ; load("lib/lean/pkg_Dep.so")
load("libpkg_IP_x2eFoo.so")              # now resolves
```

So the libraries are individually fine; the **only** problem is that the
force-load happens before the precompiled dependency is in scope.

## Minimal reproduction

```
loadorder/
  lean-toolchain          # leanprover/lean4:v4.28.0
  lakefile.lean
  LibA.lean               # precompiled dependency
  LibB/Use.lean           # NON-precompiled, references LibA's generic map
  Open.lean               # precompiled module that imports LibB (the "opened" file)
```

`LibA.lean` (precompiled) — a generic higher-order function whose inner lambda
the compiler lifts into a shared `___redArg___lam__0` symbol:

```lean
namespace LibA
structure Wrap (α : Type) where
  val : Nat → α
def Wrap.map {α β : Type} (f : α → β) (w : Wrap α) : Wrap β :=
  ⟨fun t => f (w.val t)⟩
def mk {α : Type} (x : α) : Wrap α := ⟨fun _ => x⟩
end LibA
```

`LibB/Use.lean` (NOT precompiled) — references `LibA.Wrap.map` cross-module:

```lean
import LibA
namespace LibB
def doubled : LibA.Wrap Nat := (LibA.mk 21).map (· * 2)
def sample : Nat := doubled.val 0
end LibB
```

`Open.lean` (precompiled, the file the editor opens) — a *compiled* def that
references LibB, so the interpreter must load LibB's native code:

```lean
import LibB
namespace OpenMod
def usesLibB (n : Nat) : Nat := LibB.sample + n
end OpenMod
```

`lakefile.lean`:

```lean
import Lake
open Lake DSL
package loadorder
lean_lib LibA where
  precompileModules := true        -- per-module dynlibs, loaded via imports
lean_lib LibB where                 -- monolithic .so, force-loaded
@[default_target] lean_lib Open where
  precompileModules := true
```

After `lake build`, `LibB`'s monolithic `.so` references LibA's cross-module
closure as an undefined symbol:

```
$ nm -D .lake/build/lib/libloadorder_LibB.so | grep ' U .*LibA'
  U lp_loadorder_LibA_Wrap_map___redArg___lam__0
  U initialize_loadorder_LibA
```

and `dlopen`-ing it before LibA is loaded fails with exactly those symbols
(`lp_loadorder_LibA_…___redArg___lam__0`, then `initialize_loadorder_LibA`).
The complementary direction — that loading the dependency first resolves the
references — is shown verified end-to-end in the real-project section above
(case B), where loading the precompiled dependency before the monolithic
succeeds.

Note: in this toy project `lake setup-file Open.lean` did not by itself place
`LibB` into the `--load-dynlib` set, so the *automatic* force-load that the LSP
performs in the real project was not reproduced in the toy via `setup-file` —
only the underlying symbol/ordering dependency was. Identifying the precise
Lake condition that promotes a non-precompiled lib into the force-load set is
part of what this issue asks the maintainers to confirm; the real-project
`setup-file` output above is direct evidence that it does happen.

## Expected

The force-load `--load-dynlib` set produced for a precompiled module should
include (and load *before* the non-precompiled libs) the dynlibs of any
precompiled libraries those non-precompiled libs depend on — i.e. the load
order should respect the dependency DAG, the same way the olean import path
does. Equivalently, force-loading should be deferred so that precompiled
dependencies loaded via imports are already in scope.

## Root cause (analysis)

Two interacting facts:

1. A `precompileModules` lib's native code is loaded **per-module via olean
   imports**, in dependency order, with global scope — so cross-module symbols
   resolve naturally. It is *not* placed in the `--load-dynlib` set.
2. A non-precompiled lib in the import closure of a precompiled module is loaded
   as a single **monolithic** `.so` via `--load-dynlib`, **eagerly at startup**,
   before any imports are processed.

When (2) references symbols defined by (1), the eager force-load happens before
(1) is in scope → unresolved symbols. The monolithic also references the
dependency's *root-module* initializer (`initialize_<Pkg>_<Root>`), so even a
partial per-module dependency does not suffice; effectively the whole
dependency must be loaded first.

## Workaround (what we currently do)

Make each non-precompiled lib's monolithic `.so` record `DT_NEEDED` entries on
the precompiled dependency's **per-module** dynlibs (NOT the aggregate
`lib<Dep>.so`, which is a second full copy and double-registers environment
extensions — `'…hardwareModuleAttr' has already been used`), via
`moreLinkArgs` with an `$ORIGIN/lean` rpath:

```lean
lean_lib NonPrecompiled where
  moreLinkArgs := #["-L", "./.lake/build/lib/lean", "-Wl,--no-as-needed"]
    ++ <one "-l:pkg_Dep_*.so" per per-module dynlib of the dependency>
    ++ #["-Wl,--as-needed", "-Wl,-rpath,$ORIGIN/lean"]
```

This makes the dynamic loader pull the (deduplicated) per-module dependency
dynlibs in automatically whenever the monolithic is dlopen'd, regardless of
`--load-dynlib` order. It works but is brittle: it hardcodes the dependency's
module list, is GNU-ld specific (`--no-as-needed`/`$ORIGIN`), and must be
repeated per non-precompiled lib.
