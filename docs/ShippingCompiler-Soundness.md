# Existing compiler: success implies semantic preservation

The target agreed on 2026-09-24 is the existing compiler's successful domain:

```
shippingCompile source = success ir
  → source and ir agree for every admissible input trace and observation time
```

This is a target specification, not an existing Lean theorem. Compilation may
refuse inputs. A theorem about `Source.compile` alone, a corpus of successful
proofs, or a wrapper requiring replay as an argument does not establish it.
Do not silently shrink the target to programs the new reflector understands.

## Actual boundary

`Sparkle/Compiler/Elab.lean` implements synthesis in `MetaM`, with partial
recursive handlers, a Lean environment/local context, mutable expression and
module caches, compiler mappings and a circuit builder. Thus an equation about
a pure `compile : Source → Except Error IR` does not yet describe this program.
The proof model must account for successful executions and their environments,
or the implementation must be refactored to a proved core with a checked shell.
Any remaining checked shell must be named explicitly.

| Existing entry/stage | Required connection |
|---|---|
| `synthesizeCombinationalCore` | Lean source denotation, elaborated-expression transformations, input/output packing and emitted body/design |
| `translateExprToWire` and handlers | Valid variable/cache-to-wire relation, widths, fresh names and preservation by emitted statement suffixes |
| `Module.finalize` | Restore natural statement order from builder prepend order |
| `synthesizeCombinational` | Core followed by `dropZeroWidthModule/Design` and normally `mergeDuplicates/Design` |
| `synthesizeCombinationalWithParameters` | Retained symbolic dimensions and specialization, plus the same cleanup passes |
| `synthesizeHierarchical*` | Closed design semantics and instance connections, not open `.inst` no-ops |

`SPARKLE_NO_REGDEDUP` selects a real alternate successful path. Both paths need
coverage. Source initialization, sampled reset, port packing, memory behavior
and admissible input widths must be explicit in the eventual theorem. Existing
IR semantics has unsupported symbolic expressions and open instance semantics;
successful synthesis of those forms is not evidence that this model covers them.
The Verilog printer is a later preservation obligation, outside this first IR target.

## First obstruction, reproduced and fixed

The old `handleApplicative` identified the outer operator of a lambda and
applied it to the input wires in positional order. It did not preserve the
lambda's operand order, repeated arguments, constants or expression nesting.
The real shipping entry accepted `Signal.ap (Signal.map (fun x y => y - x) a) b`.
At width 8, inputs 3 and 10 yielded source 7 and IR 249. This directly refutes
the desired theorem for that implementation; more proof automation cannot fix it.

The handler now collects the applicative spine, binds each scalar argument to
the corresponding translated input wire, beta-applies the actual function,
and lowers its body while all binders remain in scope. It no longer guesses a
binary left fold from the head operator. Existing scalar lowering is reused.

`Tools.ApplicativeLowering.Arguments.correct` and `map_start` prove the source
rule for arbitrary heterogeneous argument spines, functions and times, with
standard axioms only. **They do not prove the MetaM reader or scalar lowering.**
The implementation follows that rule, but connecting it to the compiler's state
simulation invariant remains the next proof obligation.

`Tests/Compiler/ApplicativeSemanticsTest.lean` invokes the shipping compiler
on nine cases and checks all 4-bit input combinations (including a 4-argument
case), with an 8-bit concatenation result and a Bool comparison result. It tests
actual emitted IR values, including mandatory cleanup passes. Tests are evidence
and regression protection; they are not the universal compiler theorem.

## Actual builder: first general simulation step

`Tools/ShippingBuilderSoundness.lean` proves `emitAssign_sound` about the actual
`CircuitM.emitAssign`, not a second builder. For arbitrary builder state, width
environment, memories and input environment, executing the finalized prefix
followed by the emitted assignment produces exactly the evaluated RHS at the
destination and preserves every other wire. `emitAssign_body` connects builder
prepend order to finalized execution order; `emitAssign_preserves_live` states
the frame condition for a destination disjoint from live source bindings.
These theorems use standard axioms only. RHS evaluation and name freshness are
explicit LOCAL obligations, not a whole-circuit replay assumption.

## Next proof boundary

Establish the scalar translator's invariant: mapped source values agree with
wire values, cached results remain valid, widths agree, newly allocated wires
do not overwrite live bindings, and executing the emitted statement suffix
preserves existing values and produces the source value. First prove the pure
builder/primitive steps and connect those SAME operations to the shipping path.
The assignment-emission step is now proved; name allocation, primitive RHS
lowering and cache validity remain. Then lift through scoped lambdas, lets and
application using the rule above.
Sequential handlers require a temporal state relation in addition to this
combinational invariant. No replay hypothesis may stand in for these obligations.
