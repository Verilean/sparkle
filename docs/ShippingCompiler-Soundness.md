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

General theorem checks are the primary acceptance criterion. Re-running crc16
certification is not a prerequisite for a general lemma and cannot discharge
its hypotheses. Use it at implementation-impact checkpoints (such as changing
the shipping allocator) or for performance measurements, rather than after
every proof-only change. Report regression status separately from proof progress.

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

`Tools/ShippingScalarSoundness.lean` now discharges the RHS premise for six
canonical same-width BitVec functions: add, sub, mul, and, or, xor. The
`Binary.registry` theorem pins their mapping in the actual shipping operator
registry; `rhs_correct` proves their real IR expression semantics for arbitrary
widths (including zero), operand values, names and environments. `emit_correct`
composes that fact with actual `CircuitM.emitAssign`; callers supply operand
values/widths and prefix execution, not a proof of the emitted RHS.

`BindingsAgree` states the source-value/wire correspondence. A fresh destination
preserves it, and first-wins list extension uses the same Boolean comparison as
the shipping `CompilerState.varMap`. `emit_local` composes emission with the
scoped binding extension. These are general theorems with standard axioms only.
Tests instantiate the actual builder at arbitrary width, check the six shipping
compilations on edge values, and pin counterexamples to dropping width/freshness
hypotheses.

**Remaining boundary:** none of these theorems establishes that the MetaM
translator always provides the required widths, values and fresh names.
Canonical `BitVec.add` is covered; recognizing an overloaded `HAdd.hAdd` with
its actual instance is not proved by identifying the operator name. The local
map relation does not cover `lookupVar`'s persistent IO fallback. Its lifecycle,
the expression cache and changes of local scope still need a simulation proof.
The generic relation can describe cached keys, but this does not yet prove
correctness of the shipping cache implementation.

Establish the scalar translator's invariant: mapped source values agree with
wire values, cached results remain valid, widths agree, newly allocated wires
do not overwrite live bindings, and executing the emitted statement suffix
preserves existing values and produces the source value. First prove the pure
builder/primitive steps and connect those SAME operations to the shipping path.
Assignment emission, six canonical primitive RHSs and local binding extension
are now proved. Name allocation and its composition are covered below; remaining
primitives, source recognition and cache validity remain. Then lift through scoped lambdas, lets and
application using the rule above.
Sequential handlers require a temporal state relation in addition to this
combinational invariant. No replay hypothesis may stand in for these obligations.

## Total allocation and the reservation invariant

`Sparkle/IR/FreshNames.lean` proves that numeric suffixes are injective (using
decimal-digit decoding), and that `used.size + 1` consecutive candidates cannot
all occur in a set of `used.size` names. `seek` is structurally recursive in this
bound; `seek_exists` proves success for any starting index. Thus `freshSuffix`'s
computational default is unreachable. The cardinality/list argument is erased
proof code: runtime still uses HashSet lookup and stops at the first free suffix.

The shipping `CircuitM.freshName` now uses this search in both branches. Stable
names retain the `nextSuffix` cache; unnamed temporaries search from `counter`
and advance it beyond the chosen index. Normal names are preserved. The old
unnamed branch did not check reservations: reserving `_tmp_x_0` and then calling
`freshName "x" false` returned `_tmp_x_0` again. It now returns `_tmp_x_1`.
This was reproduced at the public builder API; reachability of that reservation
pattern from a user circuit was NOT established and no shipping-circuit bug is
claimed from this example alone.

`CircuitM.freshName_spec` universally proves freshness, exact reservation-set
insertion and unchanged module. `makeWire_spec` proves the typed wire addition
and preservation of executable statements. These concern the functions actually
called by the compiler, not reference copies.

`Tools/ShippingAllocationSoundness.lean` defines `Reserved`: every live binding
points to a reserved name. It proves preservation under allocation and scoped
binding extension, and composes allocation with `Binary.emit_correct`.
`allocate_emit_correct` no longer assumes destination freshness: the actual
allocator supplies it. Operand widths/values and the entry reservation invariant
remain explicit. This does not yet prove that every MetaM handler, persistent
fallback or expression-cache update maintains that invariant.

`FreshNameSoundnessTest` checks reserved temporary/name collisions, decimal
boundaries, sanitization/hygiene, the actual `CompilerM.makeWire` wrapper and
10,000 consecutive same-base allocations. All new general theorems are audited
for standard axioms only. The test does not stand in for a complexity proof.

The next concrete cache boundary is now inventoried in `Elab.lean`: the
persistent fvar map is written in `handleLoop`, and cleared/restored at synthesis
scope boundaries. The per-module expression cache is written both by the
`translateExprToWire` wrapper and by the top-level output-leaf loop. Both write
sites, local-map shadowing and nested-module save/restore must be covered; a
proof about only the main cache wrapper would miss a successful path.
