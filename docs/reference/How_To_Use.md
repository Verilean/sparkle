# How to import and use Sparkle in your project/directory

```
my_project/
├── lakefile.toml
├── lean-toolchain
├── Main.lean              ← executable entry point (has `def main`)
├── MyProject.lean         ← library root (re-exports submodules)
└── MyProject/
    └── Basic.lean         ← your library code
```
## Step 1 — Check your lean-toolchain

```bash
# Check Sparkle's toolchain
curl -s https://raw.githubusercontent.com/Verilean/sparkle/main/lean-toolchain

# Copy that value into your own project's lean-toolchain file
```

## Step 2 — Add Sparkle as a dependency
```haskell
import Lake
open Lake DSL

package «my_project» where
  -- your package options

require sparkle from git
  "https://github.com/Verilean/sparkle.git" @ "main"
  -- For reproducibility, pin to a commit instead:
  -- "https://github.com/Verilean/sparkle.git" @ "abc123..."

@[default_target]
lean_lib «MyProject» where
  -- your library options

```

or in lakefile.toml

```toml
name = "my_project"
defaultTargets = ["myproject-exe"]

[[require]]
name = "sample"              # must match upstream package name
git = "https://github.com/Verilean/sparkle.git"
rev = "main"

[[lean_lib]]
name = "MyProject"

[[lean_exe]]
name = "myproject-exe"
root = "Main"
supportInterpreter = true    # needed if you use elaboration-time metaprograms like #synthesizeVerilog
```

MyProject/Basic.lean

```haskell
import Sample              -- or: import Sparkle, depending on upstream's lean_lib name

open Sparkle.Core.Signal
open Sparkle.Core.Domain

def myCounter : Signal Domain (BitVec 8) :=
  Signal.register 0#8 ((· + 1#8) <$> myCounter)

def greet : String := "counter built"
```

MyProject.lean
```haskell
import MyProject.Basic
```

Main.lean
```haskell
import MyProject

def main : IO Unit := do
  IO.println MyProject.Basic.greet
```

## Step 3 — Fetch and build

build and run all lean file in myproject
```bash
lake update       # clones sample into .lake/packages/, writes lake-manifest.json
lake build        # builds upstream + your lib + your exe
lake exe myproject-exe
```

run specific lean file
```bash
lake env lean --run Scratch.lean
```


## Step 4 — Import in your .lean files

```haskell
import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Signal
open Sparkle.Core.Domain

def myCounter : Signal Domain (BitVec 8) :=
  Signal.register 0#8 ((· + 1) <$> myCounter)

#synthesizeVerilog myCounter
```

## Common pitfalls
- unknown module Sample → the name in [[require]] doesn't match upstream's package name, or upstream's lean_lib is named something else. Check .lake/packages/<pkg>/lakefile.{lean,toml}.-
- .olean version mismatch → lean-toolchain differs from upstream's. Copy theirs verbatim.
- lake exe myproject-exe says "unknown executable" → the [[lean_exe]] name doesn't match what you're invoking, or you forgot root = "Main" so Lake can't find def main.
- C compiler errors during lake build → upstream has native code; install a working cc/clang and (on macOS) Xcode command line tools.