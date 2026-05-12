
# Chapter 1 — Lean 4 for HDL Authors

The Sparkle DSL is embedded in Lean 4.  You don't need to learn
Lean as a general-purpose language to use Sparkle — you need a
handful of constructs.  This chapter is **only** that handful.

If you already know Haskell or another ML-family language, most of
this will look familiar, but treat it as the rules-of-the-road for
Sparkle code.  We deliberately do **not** introduce Functor /
Applicative / Monad theory; the only place those words appear in
this chapter is a 30-line sidebar at the end.

```lean
namespace Notebooks.Ch01

```
## 1.1 Definitions: `def`

`def` introduces a named value.  Lean infers the type if you don't
annotate it; for tutorial clarity we annotate.

```lean
def answer : Nat := 42

#eval answer

```
A `def` can take parameters.  The arrow `→` separates argument
types and the result type.

```lean
def addOne (n : Nat) : Nat := n + 1

#eval addOne 5

```
Multi-argument: just chain arrows.

```lean
def plus (a b : Nat) : Nat := a + b

#eval plus 3 4

```
## 1.2 Anonymous functions: `fun`

`fun x => body` is a lambda.  We use it when an HDL combinator
expects a function, e.g. `Signal.map`.

```lean
def double : Nat → Nat := fun n => n * 2

#eval double 7

```
## 1.3 Local bindings: `let`

`let x := expr; body` introduces a local name.  In a single-line
expression you can skip the `;`.

```lean
def shifted (n : Nat) : Nat :=
  let k := n + 10
  k * 2

#eval shifted 3

```
## 1.4 Conditionals: `if … then … else`

`if c then a else b` works for **plain values**, where `c : Bool`
(or any `Decidable` proposition).

⚠️  **HDL warning.**  When `c` is a `Signal dom Bool`, you must use
`Signal.mux c a b` instead — `if` doesn't synthesise to hardware.
Chapter 2 covers this in detail.

```lean
def signOf (n : Int) : String :=
  if n < 0 then "negative" else if n == 0 then "zero" else "positive"

#eval signOf 0
#eval signOf (-3)
#eval signOf 7

```
## 1.5 Pattern matching: `match`

`match` deconstructs a value by case.  We use it on plain Lean
values like `Bool`, `Option`, or our own `inductive` types.

⚠️  Same HDL warning: don't `match` on a `Signal` value.  Sparkle
erases the match before synthesis.  Use `Signal.mux` or `hw_cond`.

```lean
def describe : Bool → String
  | true  => "on"
  | false => "off"

#eval describe true
#eval describe false

```
## 1.6 Records: `structure`

A `structure` is a named record.  Sparkle uses `structure`-like
declarations heavily for module I/O via the `declare_signal_state`
macro (Chapter 4).

```lean
structure Point where
  x : Int
  y : Int
  deriving Repr

def origin : Point := { x := 0, y := 0 }
def p1     : Point := { x := 3, y := 4 }

#eval origin
#eval p1.x
#eval p1.y

```
## 1.7 BitVec literals

Sparkle wires carry `BitVec n` values: `n` bits of unsigned data
(signed is just an interpretation).  Write a literal as
`value#n`.

```lean
def w1 : BitVec 8  := 0xFF#8
def w2 : BitVec 16 := 0x1234#16
def w3 : BitVec 32 := 42#32

#eval w1
#eval w2
#eval w3

```
BitVec arithmetic uses regular operators.  Width is preserved;
overflow wraps modulo `2^n`.

```lean
#eval (w1 + 1#8)        -- 0xFF + 1 wraps to 0x00
#eval (w2 &&& 0x00FF#16) -- bitwise AND keeps low byte
#eval (w3 <<< 4#32)      -- shift left

```
## 1.8 `Bool`

Plain `Bool` is what `Signal dom Bool` carries on a single-bit
wire.  Operators `&&`, `||`, `!` work on `Bool`; the
corresponding `Signal dom Bool` operators (Chapter 2) use `&&&`,
`|||`, `~~~`.

```lean
#eval true && false
#eval true || false
#eval !true

```
## 1.9 `do`-notation as sequencing

`do` blocks let us sequence operations that return values in a
"context" — most importantly `IO` (for printing), and Sparkle's
own `Signal.circuit do` (introduced in Chapter 3) for declaring
registered logic in an imperative style.

```lean
def greet : IO Unit := do
  IO.println "Hello,"
  IO.println "Sparkle!"

```
We won't run `greet` in a `#eval` cell because xeus-lean handles
`IO` slightly differently, but its shape — `do` with `IO.println`
statements separated by newlines — is the pattern you'll see in
the chapter demos.

## 1.10 Namespaces

`namespace N ... end N` groups definitions under a name.  Outside
the namespace you write `N.thing`; inside it you write `thing`.
Sparkle's standard library lives under `Sparkle.Core`, etc.

## 1.11 Equality and `decide`

For propositions Lean can mechanically check, `decide` proves
them.  We use this in later chapters to verify circuit
equivalences over small input spaces.  `native_decide` is the
compiled-evaluator variant — much faster for non-trivial searches.

```lean
example : 1 + 1 = 2 := by decide
example : (0xFF#8 + 1#8) = 0#8 := by native_decide

```
## 1.12 Sidebar — about `<$>`, `<*>`, `pure`

Sparkle's `Signal dom α` is a [Functor and a Monad].  Three
consequences you'll occasionally see in the codebase:

1. `f <$> sig` lifts a plain function `f : α → β` into a wire
   transformation `Signal dom α → Signal dom β`.
2. `f <$> sigA <*> sigB` does the same for a 2-argument function.
3. `pure v` (or `Signal.pure v`) lifts a plain value into a
   constant signal.

**You won't use any of those in this course.**  Sparkle defines
`+`, `-`, `*`, `&&&`, `|||`, `^^^`, `<<<`, `>>>`, `===`, `~~~`
directly on `Signal dom (BitVec n)` (and on `Signal dom Bool`),
and `Signal.circuit do` hides register lifting entirely.  A
counter is just

```text
Signal.circuit do
  let count ← Signal.reg 0#8
  count <~ count + 1#8
  return count
```

— no `<$>`, no `<*>`, no `pure`.  If you ever read IP code that
does use them, that's the explicit form.  The course uses the
operator form throughout.

[Functor and a Monad]: in the Lean stdlib sense.  We don't need
the laws here.

end Notebooks.Ch01
