# Chapter 7c — Synthesis With a Proof Attached: `#ved_u1`

Chapter 5 turned a Sparkle declaration into Verilog with
`#synthesizeVerilog`.  In that chapter you trust the compiler: nothing
checks that the module it built computes what your declaration says.
Chapter 7 proved two *Lean functions* equal, but the compiler was not part
of that proof.

This chapter covers a command that closes that gap for small designs:

```text
#ved_u1 delay8
```

It compiles `delay8` the same way `#synthesizeVerilog` does.  It returns
the IR module **only together with a kernel-checked theorem**.  The theorem
says that the module's outputs equal the declaration's Signal outputs at
every cycle.  It covers every input stream whose values fit their widths,
with reset held at 0, and every arrangement of the body that assigns each
wire before reading it (§7c.2, §7c.4).  It is a statement about the IR
module, not about the printed Verilog.  If no such theorem can be built,
the command refuses and returns nothing.

> **Status.**
>
> - The command lives in `Tools/VedU1Entry.lean` and
>   `Tools/VedU1Deep.lean`.  These are library targets of the Sparkle
>   repository, not part of the default build or the `Sparkle` umbrella.
>   You use them with `import Tools.VedU1Entry` inside the repository.
> - The slice is deliberately small: one output, no memories, no
>   instances.  The automatic proof covers register-free bodies,
>   one-register delays, and (with `#ved_u1_deep`) one register whose
>   current value is the output.
> - Everything outside that scope is *refused*, never accepted with a
>   weaker claim.

The command blocks below are shown as `text` because they need the VED
tools.  The real, CI-checked versions are in `Tests/Ved/U1EntryCheck.lean`
and `Tests/Ved/U1DeepCheck.lean`.  §7c.4 has a cell you can run with plain
`import Sparkle`.

## 7c.1 Running it

A one-register delay of an 8-bit input:

```text
import Tools.VedU1Entry

open Sparkle.Core.Domain Sparkle.Core.Signal

def delay8 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 0#8 x

#ved_u1 delay8
```

The command prints the theorem's name and its axioms, then the module:

```text
VED U1 OK delay8.ved_u1: [Classical.choice, Quot.sound, propext]
{ name := "delay8",
  inputs := [{ name := "_gen_x", ty := bitVector 8 },
             { name := "clk", ty := bit }, { name := "rst", ty := bit }],
  outputs := [{ name := "out", ty := bitVector 8 }],
  wires := [{ name := "_gen_x", ty := bitVector 8 },
            { name := "_gen_out", ty := bitVector 8 }],
  body := [register "_gen_out" "clk" ("rst", synchronous) (ref "_gen_x") 0,
           assign "out" (ref "_gen_out")],
  ... }
```

(The output is abbreviated here.  The exact text is pinned with
`#guard_msgs` in `Tests/Ved/U1EntryCheck.lean`.)

After an accepted run, five constants exist next to your declaration:

| Constant | What it is |
|---|---|
| `delay8.ved_mod` | the module `synthesizeCombinational` returned, as a closed term |
| `delay8.ved_contract` | the port correspondence: which module port is which binder or output |
| `delay8.ved_outs` | the output ports |
| `delay8.ved_body` | one well-ordered arrangement of the body (proof data only, see §7c.4) |
| `delay8.ved_u1` | the theorem |

The theorem is stated about **your** constant, not about a copy:

```text
open Tools.VedU1Contract in
example : U1Stmt delay8.ved_contract delay8.ved_mod delay8 := delay8.ved_u1
```

There is no rule by name that forbids reusing a proof.  What the entry
checks is the type: the theorem it adds must have exactly the expected
statement `U1Stmt f.ved_contract f.ved_mod f`, and the kernel checks the
proof against that type.  `Tests/Ved/U1EntryCheck.lean` records the two
cases separately:

- **An old proof is refused.** Passing `delay8b.ved_u1` (or
  `delay8k.ved_u1`) as the proof for `delay8` is refused at `[proof]`.
  That theorem talks about `delay8b`'s own module and contract, so its type
  is not `delay8`'s statement (`ctlProofB`, `ctlProofK`).
- **A new proof of a same-meaning artifact is accepted.** `delay8b`'s
  module is a different artifact with the same meaning.  Checking it
  against `delay8`'s statement with a freshly generated proof is accepted
  (`ctlArtB`).  The IR contract has no "module name = declaration name"
  condition.

That the entry returns the module of its *own* synthesis run is a property
of `#ved_u1` (it passes that module to the checker unchanged), not of the
statement.

## 7c.2 What the theorem says

`U1Stmt c m f` is a conjunction of five parts (`Tools/VedU1Contract.lean`):

| Part | Meaning | How it is proved |
|---|---|---|
| `CorrStmt c` | The port table read from `f`'s **type** matches the contract: one name per binder and per output, and all names distinct and different from `clk`/`rst`. | `decide` |
| `ShapeStmt c m` | The module's inputs are the table's ports in binder order with their widths, then `clk` and `rst`.  Its outputs are the table's outputs.  There are no memories and no instances. | `decide` |
| `WidthStmt c m` | Wire names are distinct.  Every data input has a wire declaration of its port's width.  Every register has a scalar wire declaration. | `decide` |
| `OrderStmt m` | The body is a well-formed netlist with an order in which every wire is assigned before it is read (§7c.4). | `decide` on the arrangement `ved_body` |
| `OutputsStmt c m f` | The behaviour statement below. | generated script, checked by the kernel |

The behaviour part, slightly simplified:

```text
∀ input streams ins,
  InputsOk c m ins →                -- every data input fits its width; reset held at 0
  ∀ K,                              -- run K cycles from the initial state st0
    runModule … b … K (st0 c m) … = some envs ∧
    ∀ t < K, ∀ output o,
      envs[t] o = (f applied to the input signals of ins) at cycle t, observed at o
```

Some points to read carefully:

- **Inputs.**
  - Any input stream is covered, as long as each value fits its declared
    width.
  - The clock's value is left free: it is quantified, not fixed.
  - The reset is held at 0.  Runs with reset asserted are outside the
    statement.
- **Initial state.** `st0` starts every register at its declared initial
  value.
- **The run.** `runModule` is the IR semantics in `Sparkle/IR/Semantics.lean`.
  It is a total Lean function, so the kernel can evaluate it.
- **The right-hand side.** It is computed from `f` itself (`srcOf c f`): the
  declaration is applied to the input signals, then its output is read at
  cycle `t`.
- **The body `b`.** It ranges over every well-ordered arrangement of the
  module body.  §7c.4 explains why.

## 7c.3 What the command does, step by step

`#ved_u1 f` returns the module only if every step below succeeds:

1. **Read the table.** It reads the port table from `f`'s type.  A
   declaration with more than one output is refused here, before synthesis
   (`[multi-output]`).
2. **Synthesise once.** It calls `synthesizeCombinational f`, the same
   function `#synthesizeVerilog` calls, exactly once.
3. **Register the artifact.** It registers the module as `f.ved_mod`.  It
   then checks that this closed term evaluates back to the very value
   synthesis returned (`[artifact]`).
4. **Find an order.** It looks for a well-ordered arrangement of the body
   and checks it with `OrderOk` (`[order]`).
5. **State the theorem.** It builds the expected statement
   `U1Stmt f.ved_contract f.ved_mod f` (`[type]`).
6. **Prove it.** It elaborates a generated proof script against that
   statement (`[proof]`).  Errors are never turned into `sorry`.
7. **Kernel check.** It adds the theorem to the kernel synchronously, then
   re-reads the stored type and compares it with step 5 (`[kernel]`,
   `[type]`).
8. **Strict audit.** It runs the strict audit (`[audit]`).  The audit
   accepts only `propext`, `Classical.choice` and `Quot.sound`.  It
   rejects `native_decide` (`Lean.ofReduceBool`) and any other axiom.

When a step fails:

- **The report.** Failures are reported as `VED U1 REFUSED f [stage]: …`.
  Inside the checker (steps 3–8), any other exception is reported as
  `[checker]`.  Not every failure takes this form: an interrupt is never
  caught, and a heartbeat or recursion-limit error raised while reading the
  table or during synthesis propagates as its own error.
- **The rollback.** The checker saves the elaboration state when it starts,
  which is after synthesis.  On a failure it restores that state.  The
  constants it added (`ved_mod`, `ved_contract`, `ved_outs`, `ved_body`,
  `ved_u1`, and anything a failed kernel step left) and its messages
  disappear.  Constants that existed before are not deleted; the state just
  goes back to the checker's start.
- **What is not restored.** Anything synthesis did before the checker
  started: the environment before `synthesizeCombinational`, `IO.Ref`s and
  caches, and files.

The proof script is **untrusted**.  The kernel and the audit are what make
the result trustworthy, not the script generator.

## 7c.4 Why statement order does not matter

A circuit is a set of wires driven at the same time.  The order in which
the assignments are written down carries no meaning.  In Verilog,

```text
assign c = b;
assign b = a;
```

is the same circuit as the two lines swapped.

Sparkle's IR semantics, however, evaluates the body **once, top to
bottom** (`evalAssigns`).  When a wire is read before its assignment, the
read sees the value from the starting environment.  You can see this with
plain `import Sparkle`:

```lean
import Sparkle

open Sparkle.IR.AST Sparkle.IR.Semantics

namespace Notebooks.Ch07c

/-- Start: input `a` is 5, every other wire 0. -/
def env0 : Env := fun n => if n = "a" then 5 else 0

/-- Every name is 8 bits wide. -/
def we8 : WEnv := fun _ => 8

/-- `b := a; c := b`: each wire is assigned before it is read. -/
def fwd : List Stmt := [.assign "b" (.ref "a"), .assign "c" (.ref "b")]

/-- The same two assignments, swapped. -/
def bwd : List Stmt := [.assign "c" (.ref "b"), .assign "b" (.ref "a")]

-- one top-to-bottom pass: `c` is 5 in one order, 0 in the other
#guard (evalAssigns we8 (fun _ _ => 0) fwd env0).map (· "c") == some 5
#guard (evalAssigns we8 (fun _ _ => 0) bwd env0).map (· "c") == some 0

-- `woCheck` tells the two apart: only `fwd` assigns before reading
#guard Sparkle.IR.Reorder.woCheck [] fwd
#guard !Sparkle.IR.Reorder.woCheck [] bwd

```

Sparkle's compiler does emit bodies like `bwd` for some `circuit do`
blocks.  An example is the accumulator `accK9` in
`Tests/Ved/U1DeepCheck.lean`:

```text
_tmp_op_a_2 := _tmp_loop_body_7[7:0]   -- read here
...
_tmp_loop_body_7 := _tmp_a_5           -- assigned here
out := _tmp_op_a_2
```

As continuous assignments, these lines mean the same in any order:
swapping two `assign` statements does not change a netlist.  (This is a
remark about statement order only.  U1 says nothing about the correctness
of the Verilog that is printed for this design.)  A theorem about the IR
body *in its printed order*, read with the one-pass `evalAssigns`, would be
false here although the order of the assignments carries no meaning.  So
the U1 statement is about the body as a netlist, not about one listing of
it:

- **The well-ordered arrangements.**
  - `WO [] b` holds when `b` assigns every wire before reading it.
  - `OutputsStmt` speaks about **every** permutation `b` of the body with
    `WO [] b`.
- **They all agree.** `runModule_perm` (`Sparkle/IR/ReorderInvariance.lean`)
  proves that all such arrangements give the same run.  So the statement
  does not depend on which one you pick.
- **One arrangement must exist.** `OrderStmt` requires it, checked in the
  kernel by `OrderOk`.  `OrderOk` also rules out bodies that have no
  order-free meaning:
  - a combinational cycle;
  - an assignment that reads its own target;
  - a read of a name that is neither an input, a register, nor assigned;
  - an output with no driver;
  - an assignment to an input;
  - a name that is both assigned and a register output;
  - duplicate register or memory names.

  With these rules, the starting value of the environment never stands in
  for a missing driver.
- **The module is not reordered.** The arrangement the checker found is
  stored as proof data (`f.ved_body`).  The module you get back is exactly
  what synthesis returned.  If no arrangement exists, the command refuses
  with `[order]`.
- **The in-order reading is still available.** When the printed order is
  already well-ordered, `outputs_body` gives the in-order statement over
  `m.body` itself.

## 7c.5 How the proof is built

Both commands prove `OutputsStmt` in the same three moves:

1. **Pick the checked arrangement.**
   `outputs_of_order b0 (h : OrderOk m b0 = true)` reduces the statement
   over *every* well-ordered arrangement to the one arrangement `b0 =
   f.ved_body`.
2. **Induct over cycles.** `outputs_of_step` turns the claim for all `K`
   cycles into an induction.  You supply an invariant `R` between the
   module's register state and the cycle number, and prove two things:
   - `R` holds at cycle 0 for `st0`;
   - one `stepModule` of `b0` from a state satisfying `R` produces the
     right outputs for that cycle and a next state that satisfies `R`
     again.

   The time direction (`runModule` counts cycles down; streams count up)
   is handled once inside `outputs_of_step` (`seedFwd_time`).
3. **Prove one symbolic cycle.** The module's syntax is fixed, but the
   step is not a closed computation: the inputs `ins`, the cycle `s`, the
   state `st` and the memories are all universally quantified.  The
   generated script unfolds `stepModule` on the fixed body with `simp`,
   which leaves arithmetic over those variables, and closes it with the
   input-width bounds and `omega`.

The two commands differ in where the invariant and the per-cycle facts
come from:

- **`#ved_u1`** builds the script itself.  It covers register-free bodies
  (the invariant is just `True`) and one-register delays (the invariant
  is "the register holds the declaration's output at the current
  cycle").
- **`#ved_u1_deep`** reuses what `#verify_elab_deep` already proved about
  the declaration (see `docs/VED-MAIN-INTRO.md`):

  ```text
  #verify_elab_deep accK9
  #ved_u1_deep accK9
  ```

  - **The facts it uses.** It uses only the standard-axiom facts
    `_deep_trace`, `_deep_next`, `_deep_inits` and `_deep_out`.  These
    relate the Signal to the reified circuit `Cdo`.
  - **The invariant.** "The module's register equals `Cdo.irState` at the
    same cycle."
  - **What it does not use.** `#verify_elab_deep`'s IR replay theorems
    (`_deep_signal_run`, `_deep_regstep`, …) rely on `native_decide`, and
    are not used.  The strict audit would reject them anyway.

## 7c.6 How we know it is not vacuous

An accepted run is only interesting if wrong modules are refused.
`Tests/Ved/U1EntryCheck.lean` feeds the checker the real declaration
together with a **mutated** module.  Each mutation must be refused at the
named stage, and none of the names the checker registers (`ved_mod`,
`ved_contract`, `ved_outs`, `ved_body`, `ved_u1` for that run) may be left
in the environment:

| Mutation of `delay8`'s module | Refused at |
|---|---|
| register initial value 0 → 5 | `[proof]` |
| output reads the input instead of the register | `[proof]` |
| output port widened to 9 bits | `[proof]` |
| register fed from a constant | `[proof]` |
| output's driver removed | `[order]` |
| an assignment to the data input added | `[order]` |
| `ident8`'s module put into `delay8`'s statement | `[proof]` |

For some of these, the test also proves in the kernel that the statement is
**false**, not just that the script gave up.  For example, the identity
does not implement the delay:

```text
theorem ident_not_delay : ¬ U1Stmt delay8.ved_contract delay8.ved_mod ident8
```

The witness is an input of 1 at every cycle.  At cycle 0 the register
gives 0 but the identity gives 1.

`Tests/Ved/U1DeepCheck.lean` does the same for the deep route.  It also
checks that the accepted theorem's dependency closure contains no
`native_decide` auxiliary.  And it confirms that `accK9`'s body, in its
printed order, is *not* well-ordered:

```text
example : Sparkle.IR.Reorder.woCheck [] accK9.ved_mod.body = false := by decide
```

The theorem is accepted all the same, by §7c.4.

## 7c.7 What it does not claim

- **The artifact.** The guarantee is about the module
  `synthesizeCombinational` returned.  The Verilog that
  `#synthesizeVerilog` prints goes through `optimizeModule` and the
  printer, and is not covered.  Neither is the C simulator.
- **Scope.**
  - One output; multi-output declarations are refused.
  - No memories and no instances.
  - Runs with reset held at 0.
- **Coverage.** This is a minimal entry.  It is not a claim that the IP
  library is verified.

## 7c.8 Running the checks yourself

```bash
lake build Tests.Ved.U1ContractCheck   # the statement, toy instances, order controls
lake build Tests.Ved.U1EntryCheck      # #ved_u1 runs and mutation controls
lake build Tests.Ved.U1DeepCheck       # #ved_u1_deep on accK9 / natInit5
```

CI builds the same targets in `.github/workflows/ved.yml`.  The design
notes are in `docs/VED-U1-MAIN.md`.

```lean
end Notebooks.Ch07c
```
