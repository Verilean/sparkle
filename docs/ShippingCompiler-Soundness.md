# Existing compiler: success implies semantic preservation

For resuming work in Claude Code, start with [CompCert-Handoff.md](CompCert-Handoff.md).

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
map relation alone did not cover the former persistent IO fallback. The later
state-backed lookup rules below close that local connection. Expression-cache
validity and preservation by all handlers still need a simulation proof.
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

The concrete cache boundary is inventoried in `Elab.lean`: the persistent fvar
map is written in `handleLoop`; it now lives in the synthesis's `CircuitState`
and starts empty in `CircuitM.init`. The per-module expression cache is written both by the
`translateExprToWire` wrapper and by the top-level output-leaf loop. Both write
sites, local-map shadowing and nested-module save/restore must be covered; a
proof about only the main cache wrapper would miss a successful path.

## Scoped/persistent binding rules (2026-09-24)

`Tools/ShippingBindingsSoundness.lean` keeps local and persistent valuations
separate. Its `Valid` relation requires value agreement and reserved names in
both maps, including persistent entries hidden by a local binding. The table
operations are the existing `List.lookup` and `Std.HashMap Name String.insert`.
`Valid.enter`, `insert_persistent`, `allocate_write` and `restore` prove their
transition rules. `scope_allocate_restore` composes entering a local scope,
actual fresh allocation and a wire write, and proves both the inner AND original
outer relations afterwards. It protects older local bindings too, by retaining
the original invariant alongside the inner one. Merely validating the inner
visible lookup is insufficient; the test proves a counterexample with the SAME
source valuations before and after restoration.

`Valid.allocate_emit` additionally composes this stronger invariant with the
actual allocator and assignment emitter for the six canonical binary operators.
It proves prefix execution, the new result value and preservation of both maps;
freshness follows from reservations rather than being assumed by the caller.

`withVarMapping_run` is an exact equation for the existing compiler action.
Originally, `visible` was only a pure model of the local-first rule: an external
IO.Ref snapshot was not connected. This boundary has now been removed from the
implementation rather than postulating `LawfulMonad MetaM` or IO laws.

`CircuitState.sourceBindings` holds the table as builder-only metadata (it is
absent from the emitted IR). `CircuitM.lookupSourceBinding` and
`bindSourceVariable` are pure operations used by the actual compiler wrappers.
`lookupVar_run` and `bindSourceVariable_run` prove their exact MetaM result
expressions for arbitrary states, both lookup branches included.
`Valid.lookupVar` connects a hit to the source valuation and reserved wire;
`Valid.bindSourceVariable` proves the registration transition. The allocator's
metadata-preservation theorem connects `Valid.allocate_write_state` to the table
in the resulting actual state. These require the entry value/reservation
invariant, not an external IO snapshot or a whole-circuit replay premise.

`handleLoop` now uses the state-backed registration. Each synthesis constructs
its own `CircuitM.init`; `init_sourceBindings` proves its table empty. The global
wire-binding ref and its clear/save/restore code are gone. Parent and child
actions therefore receive separate tables, including after child failure.
Focused runtime tests cover those integration paths, local priority, repeated
fallback after allocation/emission, and a subsequent fresh synthesis. They are
regressions, not proofs of the full recursive MetaM synthesizer or exception
semantics. The other global caches (including fvar-to-expression and width
caches) are unchanged. Expression-cache key semantics, context stability and
lifecycle remain separate obligations.

The next cache proof must cover open expressions: the shipping eligibility test
excludes `e.isFVar`, not all expressions containing free variables. Therefore
"the expression key is unchanged" alone does not prove a hit remains valid
across scope changes. Establish stability of the bindings used by cached
expressions (or revise the implementation if that invariant fails), metadata
stripping in the fallback lookup, both insertion sites and preservation of the
cached wire's value/width/reservation. This is an outstanding proof obligation,
not a measured miscompile.

## Expression cache (2026-09-25)

`Tools/ShippingCacheSoundness.lean` takes the first step of that obligation.

What the soundness rests on is the KEY, not the expression. The eligibility
test `!isNamed && !e.isFVar && !isTopLevel` is reproduced verbatim as
`cacheable`, and `cacheable_open_application` proves the sharp form of the
concern: an application containing a free variable IS cacheable. So "cached
expressions are closed" is false and cannot be the argument.

The argument that does work: every scoped binder enters through
`CompilerM.withLocalDecl`, i.e. `Lean.Meta.withLocalDeclD`, which mints a fresh
`FVarId` per entry, and `ExprStructMap` keys on `ExprStructEq`, whose `BEq` is
the structural `Expr.equal` distinguishing `fvar` by id. An expression
mentioning a binder from an exited scope is therefore a DIFFERENT key from the
same shape under a new binder, so a stale hit cannot occur silently. Two
runtime checks in the test pin this: three successive `withLocalDeclD` entries
give distinct ids, and two structurally identical bodies built in different
scopes compare unequal. They are checks of the MetaM implementation, not
proofs; `Expr.equal` is `opaque`, so nothing in the file unfolds it.

Proved, with standard axioms only: `Valid.hit` (a hit returns a wire carrying
the key's source value), `Valid.hit_stripped` (the `consumeMData` fallback
lookup, under an explicit hypothesis that stripping preserves the denotation),
`Valid.hit_congr` (a structurally equal key, under `KeyFaithful`),
`Valid.insert` (the shim's write-back), `Valid.reserve` (allocation may extend
the reserved set), `valid_empty` / `valid_at_synthesis_start` (each synthesis
begins in the invariant, since the ref starts empty) and `Valid.write_fresh`
(emitting to a fresh name cannot disturb a cached entry, because
`CacheReserved` says every cached wire is already reserved).

Two obligations are explicit hypotheses rather than hidden:

- `KeyFaithful` — structurally equal keys denote the same source value. This is
  where the fresh-binder argument is consumed.
- `InsertSpec` — the lookup behaviour of `insert`. Normally this is
  `Std.HashMap.get?_insert`, but that lemma needs `EquivBEq`/`LawfulHashable`,
  and **core provides no `EquivBEq ExprStructEq` instance** (`#synth` fails,
  checked in the test) precisely because `Expr.equal` is opaque. Assuming a
  lawful key here would have been unsound bookkeeping, so the required equation
  is stated instead. The test logs a NOTE if core ever gains the instance.

Still open for the cache, and not claimed: the second insertion site (the
top-level output-leaf loop) and the top-level bypass interact with per-leaf
translation; width and reservation of a cached wire across composition units;
and that every handler actually maintains `Valid` — these theorems are
transition rules, like the binding rules above, not a proof that the recursive
MetaM synthesizer preserves them.

### Reducing the hypotheses (2026-09-25, second pass)

The first pass left two hypotheses. Both have now been narrowed, and one is
gone as a hypothesis about hash maps.

**Correction (2026-09-25).** An earlier version of this section, and the commit
message of `bf3d4a5`, claimed `InsertSpec` had been "discharged". That was
wrong and is withdrawn. `insertSpec_of_lawful` is a general lemma about lawful
keys, but `Valid.insert` — the theorem the compiler's write-back would actually
use — still takes `spec : InsertSpec cache key wire` as a parameter. No caller
can supply it for the shipping key, so nothing was removed from the trusted
surface: a generic lemma that the actual theorem does not consume is not a
discharged hypothesis. The count of unproven premises on the real cache path
was unchanged by that commit.

**`KeyFaithful` is split by owner.** It was one hypothesis mixing two unrelated
claims:

- `KeySound` — structurally equal keys are equal expressions. A statement about
  `Expr.equal` only. `keyFaithful_of_keySound` proves it suffices, so the open
  obligation is now this single syntactic fact rather than a claim quantified
  over all source valuations.
- `StableBetween` — between the insert and the hit, neither the environment at
  the cached wire nor the source valuation of the key moved. A statement about
  the COMPILER's scoping, not about `Expr`. `hit_across` proves the reuse step
  from it, and `stableBetween_refl` covers the within-one-environment case.

Separating them matters because `Valid` is indexed by a single environment
whereas the cache spans a whole synthesis: key soundness alone never justifies
"insert here, read there". That step is `hit_across`, and its premise is now
explicit.

**`KeySound` is not provable for the current key, and this is a design fact.**
Reducing it lands on `Expr.equal`, which is `opaque` (an `@[extern]` C
function); the goal can only be closed by `sorry` (checked). It is therefore
not a proof obligation that more effort discharges — the key must change.

**The rejected shortcut.** Making the comparison return `false` on `mdata` is
unsound as a design, not merely weak: it is irreflexive, so `EquivBEq` fails
and with it every HashMap lemma, including the one just proved. Verified.

### Key specification (2026-09-25, third pass)

Before any more conditional lemmas: fix WHAT the cache is keyed on. The
findings above constrain this more than the earlier plan admitted.

**Requirement.** `Valid.insert` must apply to the real table without an
external `InsertSpec`. That needs `EquivBEq` and `LawfulHashable` for the key
type, which needs a `BEq` that is reflexive, symmetric, transitive and
hash-compatible. `KeySound` additionally needs it antisymmetric (equal keys ⇒
equal `Expr`).

**What is ruled out, with reasons measured rather than argued.**

| Candidate key | Verdict |
|---|---|
| `ExprStructEq` (the current one, `Expr.equal`) | `opaque` extern; no `EquivBEq` in core, `KeySound` reduces to the opaque constant and can only be closed by `sorry` |
| Delegate `mdata` to core's `BEq KVMap` | UNSOUND: `KVMap.eqv` is `subset ∧ subset`, so `{a↦1,b↦2} == {b↦2,a↦1}` is `true` while the entry lists differ (measured). `KeySound` would be FALSE |
| Return `false` on `mdata` | Irreflexive, so `EquivBEq` fails and every HashMap lemma is lost (measured) |
| `toString`/format projection | Lawful `BEq` for free, but injectivity on `Expr` is not provable, so `KeySound` fails |
| Derive `DecidableEq Expr` outright | Blocked: `Syntax` is nested-inductive (`Array Syntax`), `deriving` refuses; `Level` additionally carries a `computed_field` |

**The specification that survives.** Key on a structural equality `exprEq`
written in Lean, with:

- `Level` — hand-written; `computed_field` blocks deriving. Feasibility proved:
  `levEq a b = true ↔ a = b` with `[propext, Quot.sound]`.
- `Literal`, `BinderInfo` — derive cleanly.
- `Name`, `FVarId`, `MVarId` — core instances suffice.
- `mdata` — compared as VALUES on the entry list (never via `KVMap.eqv`), and
  `DataValue.ofSyntax` is the one case that cannot be decided structurally.
  Since `Syntax` cannot be derived, the specification must either treat any key
  containing `ofSyntax` metadata as NON-CACHEABLE, or carry `Syntax` equality
  as an explicitly named axiom. The first keeps the axiom count at zero and is
  the recommendation.

**Consequence for the eligibility test.** Excluding `ofSyntax`-bearing keys
changes `cacheable`, hence which lookups hit. That is a change to the shipping
compiler and is governed by the re-translation conditions below.

### Hit-rate changes in BOTH directions

The earlier text only considered misses replacing hits. A key change can also
make hits INCREASE, and that direction is the dangerous one:

- **More hits.** `Expr.equal` distinguishes binder names and annotations that a
  coarser structural comparison might identify. Any key that equates two
  expressions the current one separates will REUSE a wire where the shipping
  compiler emits two. If the two expressions denote different values, that is a
  miscompile introduced by the proof work. So the key must be at least as fine
  as `Expr.equal` on cacheable expressions — which is exactly `KeySound`, and
  is why `KeySound` cannot be dropped in favour of "it only misses more".
- **Fewer hits.** Covered by the re-translation conditions (value agreement, no
  observable duplication, no non-idempotent handler, cost).

Neither direction is currently proved. Until the key is fixed and `KeySound`
holds for it, a key change is not a neutral refactor in either direction.

### Plan: connect the real comparison, key, lookup and insert

The goal is that the operations the compiler ACTUALLY performs are the ones the
theorems are about. Equivalence with the opaque comparison must be proved, not
assumed — "we wrote a structural twin" is not itself an argument.

1. **Leaf equalities.** `Level` needs a hand-written structural equality with a
   `levEq a b = true ↔ a = b` proof: it carries a `computed_field`, so
   `deriving` fails. Done as a feasibility check — the proof goes through with
   `[propext, Quot.sound]` only. `Literal` and `BinderInfo` derive cleanly.
   `Name`, `FVarId`, `MVarId` already have what is needed.
2. **`mdata`.** `MData = KVMap` and `DataValue` reaches `Syntax`, whose
   `DecidableEq` does not derive (`SourceInfo` blocks it).

   **Delegating to core's `BEq KVMap` is NOT available**, and the reason is
   decisive rather than a matter of proof effort: `KVMap.eqv` is
   `subset m₁ m₂ && subset m₂ m₁`, so it identifies maps that differ in
   STORAGE ORDER. Measured: with `d1 = {a↦1, b↦2}` and `d2 = {b↦2, a↦1}`,
   `d1 == d2` is `true` while `d1.entries == d2.entries` is `false`. A key
   comparison built on it would therefore equate `mdata d1 e` with
   `mdata d2 e`, making `KeySound` (equal keys ⇒ equal `Expr`) FALSE, not
   merely unproven. Any `mdata` case must compare the entry lists as values.
3. **`exprEq` and its characterisation.** A structural comparison over the
   twelve constructors plus `exprEq_iff`. Mechanical given (1) and (2); the
   `stripMaskK` work on the certified-roundtrip side is the precedent for the
   shape.
4. **Make it the key.** Define the cache key as a wrapper whose `BEq` is
   `exprEq` with `LawfulBEq`, derive `EquivBEq`/`LawfulHashable`, and
   instantiate `insertSpec_of_lawful`. This discharges `InsertSpec` at the real
   table and makes `KeySound` provable, because the comparison is no longer
   opaque.
5. **Equivalence with the shipping behaviour.** Changing the key changes which
   lookups hit. Two options, and the choice must be recorded rather than
   glossed: either prove `exprEq = Expr.equal` (impossible while the latter is
   opaque, so it would need a core-level axiom or an upstream lemma), or accept
   that `exprEq` may MISS where `Expr.equal` would hit and prove that a miss is
   harmless. The second is the honest route and needs the re-translation
   condition below.

### If a miss replaces a hit: the re-translation condition

Both the `mdata`-exclusion variant and any conservative `exprEq` turn some hits
into misses. A miss re-runs the handler chain, which EMITS AGAIN. That is only
harmless under a condition that must be stated, because it is not obvious:

- **Value agreement.** The freshly translated wire carries the same source
  value as the one already cached. This is what makes the extra wire redundant
  rather than wrong.
- **No observable duplication.** Re-emission adds an assign and consumes a
  fresh name. The emitted module therefore differs from the cached-hit module
  by duplicated combinational definitions. For semantics this is benign only
  because the duplicates are pure and separately named — a statement about the
  IR, provable from the existing well-ordering/freshness invariants, but NOT
  yet proved.
- **Effectful handlers are excluded.** Any handler whose re-execution is not
  idempotent (memory statements, register declarations, sub-module instances)
  must not be reached by the re-translation. The memory path already has its
  own dedupe keyed on IR shape, which is evidence the concern is real: the
  expression cache is not the only mechanism preventing duplicate BRAMs.
- **Termination/cost.** Misses multiply work; the existing
  `SPARKLE_TRANSLATE_LIMIT` backstop bounds it but a systematic miss regression
  would be a performance fault, to be measured rather than assumed away.

Until those are proved, excluding `mdata` from caching is a change to the
shipping compiler's output, not a neutral refactor, and it is not taken here.

## Applying the general theorem to crc16

The desired application is: check successful shipping compilation (and any
explicit admissibility conditions), then apply the general preservation theorem.
It must not invoke a circuit-specific semantic replay proof. No such complete
shipping success theorem exists yet. Source inspection of `crc16CcittHW` and
`crc16Step` identifies the following coverage obligations; this table is not an
execution trace or an exhaustiveness proof for the handlers they invoke.

| crc16 construct / compiler stage | General proof status |
|---|---|
| map/application, BitVec AND/XOR | Source application rule and canonical scalar RHS rules proved; actual recognition and dispatch still open |
| local bindings, wire allocation | Actual allocation/emission and scoped binding rules proved; cache hit/insert rules proved (2026-09-25) under explicit key hypotheses; global source/width invariant still open |
| pure constants, concat, shift, equality, Bool not, mux | Their shipping handler preservation still needs connecting/proving |
| register init `0xFFFF`, update, feedback, start/valid mux | Temporal simulation of the shipping stateful path remains open |
| helper unfolding, output record packing, Bool/BitVec ports | Source recognition and interface correspondence remain open |
| zero-width cleanup and register deduplication | Composition with the shipping success theorem remains open |

The current bounded frontend and crc16's per-instance certificates do not close
these rows. Generic theorem/axiom checks are the primary criterion. For the
state-storage change, synthesis and scope regressions check integration; they
do not discharge additional rows of the general proof.
