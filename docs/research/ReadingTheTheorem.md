# What `#ved_u1 delay8` proves, and what it does not

This page reads one theorem from start to end: the theorem that `#ved_u1` builds for the
smallest circuit, an 8-bit register. Everything shown below is printed by a file you can run:

```bash
lake build Tools.VedU1Entry
lake env lean docs/research/examples/Delay8.lean ; echo "exit $?"
```

The outputs quoted on this page are pinned in that file with `#guard_msgs`, so the file fails if
they change.

## 1. The circuit

```lean
def delay8 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 0#8 x
```

`delay8 x` is `x` delayed by one clock cycle: at cycle 0 it is the initial value `0`, at cycle
`t + 1` it is the value `x` had at cycle `t`.

## 2. What the command returns

`#ved_u1 delay8` does three things in one command. It synthesises `delay8` once, as
`#synthesizeVerilog` would. It builds a proof about the module that synthesis returned. Lean's
kernel then checks that proof. It prints:

```text
VED U1 OK delay8.ved_u1: [Classical.choice, Quot.sound, propext]
{ name := "delay8",
  inputs := [{ name := "_gen_x", ty := bitVector 8 }, { name := "clk", ty := bit }, { name := "rst", ty := bit }],
  outputs := [{ name := "out", ty := bitVector 8 }],
  wires := [{ name := "_gen_x", ty := bitVector 8 }, { name := "_gen_out", ty := bitVector 8 }],
  body := [register "_gen_out" "clk" ("rst", synchronous) (ref "_gen_x") 0,
           assign "out" (ref "_gen_out")],
  … }
```

(Shortened: namespaces and empty fields removed.) The second part is the returned module in
Sparkle's IR. It has the data input `_gen_x` (your `x`), a clock, a reset, one 8-bit register
`_gen_out` that starts at 0 and loads `_gen_x`, and the output `out`. The theorem is about this
module; `#ved_write_checked` writes the SystemVerilog file from it.

## 3. The statement

```lean
#check delay8.ved_u1
-- delay8.ved_u1 : Tools.VedU1Contract.U1Stmt delay8.ved_contract delay8.ved_mod delay8
```

The statement has three arguments:

| Argument | What it is |
|---|---|
| `delay8.ved_contract` | the port table: `x` is the input port `_gen_x` (8 bits), the result is the output port `out` (8 bits), the clock is `clk`, the reset `rst` |
| `delay8.ved_mod` | the module shown in section 2, exactly as synthesis returned it |
| `delay8` | **your** definition, not a copy |

`U1Stmt` is five parts joined by `∧` (`#print U1Stmt`):

```lean
fun c m f => CorrStmt c ∧ ShapeStmt c m ∧ WidthStmt c m ∧ OrderStmt m ∧ OutputsStmt c m f
```

Read for `delay8`, they say:

| Part | For `delay8` it says | Proved by |
|---|---|---|
| `CorrStmt` | the port table matches the type of `delay8`: one input, one output, names distinct and not `clk`/`rst`, widths positive | `decide` |
| `ShapeStmt` | the module's inputs are `_gen_x` (8 bits), `clk`, `rst` in that order, its output is `out`, its one register starts at 0 on that clock and reset, and there are no memories and no sub-modules | `decide` |
| `WidthStmt` | wire names are distinct, `_gen_x` is declared 8 bits wide, the register has a scalar wire | `decide` |
| `OrderStmt` | the body can be ordered so that every wire is written before it is read | `decide` |
| `OutputsStmt` | **the behaviour**, see below | a generated proof, checked by the kernel |

## 4. The behaviour part, in plain words

For `delay8`, `OutputsStmt` says:

> Take **any** input stream for `_gen_x` in which every value fits in 8 bits, hold `rst` at 0, and
> leave `clk` free. Start the module with its register at 0 and run it for any number of
> cycles K. Then the run does not fail, and at every cycle t < K the port `out` carries the value
> that `delay8` (applied to the same input, as a `Signal`) has at cycle t.

Since `delay8` is a one-cycle delay, this means: `out` is 0 at cycle 0, and `out` at cycle `t + 1` is the
input of cycle `t`. That fact is not written into the statement by hand. The statement compares the
module with `delay8` itself, and the one-cycle delay follows from the definition. The tutorial file
`docs/research/examples/tutorial/Ex6_OwnLemma.lean` derives it from `delay8.ved_u1` in about
fifteen lines:

```lean
theorem delay8_ir (ins : Nat → String → Nat)
    (hok : InputsOk delay8.ved_contract delay8.ved_mod ins) (K t : Nat) (ht : t + 1 < K) :
    ∃ envs, runModule … delay8.ved_mod.body … K (st0 delay8.ved_contract delay8.ved_mod) … = some envs ∧
      ∃ env, envs[t + 1]? = some env ∧ env "out" = ins t "_gen_x"
```

"The module's output at cycle t+1 is its input at cycle t", proved from the accepted theorem with
the standard axioms only.

`#print axioms delay8.ved_u1` lists `propext`, `Classical.choice` and `Quot.sound`: Lean's
standard axioms. That means no `sorry` and no extra assumption was used.

## 5. What it does not say

| Not covered | Why it matters |
|---|---|
| **Cycles with reset asserted.** `rst` is held at 0 for the whole run. | What the register does when reset rises is outside the statement. |
| **Other starting states.** The run starts from the declared initial value 0. | A register that powers up with another value is not covered. |
| **Inputs wider than 8 bits.** Only streams whose values fit the declared width. | The IR stores numbers; out-of-range values are excluded by assumption. |
| **The optimiser.** The statement is about the module synthesis returned. | If an optimisation pass runs afterwards, its output is not covered (with `#ved_write_checked` the files are written from the checked module). |
| **The SystemVerilog text.** The meaning used is Sparkle's IR semantics (`Sparkle/IR/Semantics.lean`). | Whether the printed `.sv` file means the same to a simulator or a synthesis tool is not proved. |
| **Timing, the FPGA or chip.** | Clock frequency, glitches, the board: nothing physical. |
| **Other circuits.** | The theorem is about `delay8` only. A circuit the entry refuses gets no claim, and a refusal is not a counterexample. |
| **The compiler in general.** | This is a proof for one compilation result, not a theorem that the compiler is correct for every input ([CompilerGeneralTheorem.md](CompilerGeneralTheorem.md)). |

## 6. Where next

- The same theorem with more background, and how mutated modules are refused:
  [tutorial chapter 7c](../tutorial/md/Ch07c_VerifiedSynthesis.md).
- The exact Lean statements of every entry: [appendix A](appendix/A-Statements.md).
- Writing circuits whose proofs go through: [ProofFriendlyCircuits.md](ProofFriendlyCircuits.md).
