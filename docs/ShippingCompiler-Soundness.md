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

## Formal shape of success and preservation (2026-09-25)

`Tools/ShippingTranslateSoundness.lean` fixes how "the existing compiler, when
it succeeds, preserves meaning" is stated, and proves two branches of the real
translator in that shape. It checks the METHOD on the actual code; it is not a
reduction of the target.

### Decisions, each forced by a measured fact

| Decision | Forcing fact |
|---|---|
| **Success** is `Returns m ctx s a s'`: some MetaM/Core environment and world in which the real `CompilerM` action returns `a` with builder state `s'`. Theorems are `Returns … → Q`, so they hold in every environment. | `IO` in this toolchain is the exposed `EST` monad, so `Returns.bind/pure/liftMetaM/throw/get/set` are proved by definitional unfolding, with no `LawfulMonad MetaM` (the obstacle recorded in the handoff). |
| **MetaM queries are oracles**: the result is unconstrained, only the builder state is. What the IR depends on must be computed purely or be a named assumption. | `Returns.liftMetaM` is all that can be said about `inferType`/`whnf`. |
| **Branches are plain definitions parametrised by the recursive call** (`TranslateFn`); the shipping translator passes itself. | The translator is a `mutual` block of `partial def`s; `#print translateExprToWire` shows `opaque`: no equations, nothing provable. |
| **The knot must become a fuel-bounded fixpoint** (`fuelFix`). | `fuelFix_spec` (proved) discharges the recursion hypothesis by induction on fuel; fuel 0 throws, so `Returns.throw` makes it vacuous. Fuel exhaustion is a compile error, like the existing `SPARKLE_TRANSLATE_LIMIT`. |
| **Source semantics** `Denotes ρ e n x` is a big-step relation on the `Lean.Expr` the compiler consumes, defined only for canonical LIBRARY instances. | Each clause is tied to the library by `rfl` (`library_add … library_xor`, `library_pure`, `library_ofNat_literal`), so it is not a free-standing specification. |
| **CompCert-style statement**: if the source has a defined meaning and the compiler succeeds, the result wire carries it. | Coverage (success ⇒ defined meaning) is separate and open; see below. |

### The miscompile this exposed

The operator path dispatched on the METHOD name and ignored the INSTANCE. With a
user instance `HAdd (Signal dom (BitVec 8)) …` whose `+` is subtraction, the
source gives 3 + 10 = 249 and the compiler reported success emitting an adder
(RTL 13). Two sites did this: the Signal intercept and the `primitiveRegistry`
path (`→ primitive HAdd.hAdd`), which caught the application again after the
first fix. Both now require the instance to be a listed library instance
(`canonicalSignalBinInsts`, `canonicalScalarMethodInsts`, including the INNER
instance of core's generic wrappers such as `instHAdd _ BitVec.instAdd`); an
unlisted instance is refused ("Cannot instantiate HAdd.hAdd"). The first version
of the table missed the Signal unary instances (`~~~` on `Signal Bool` and on
`Signal (BitVec n)`, `-` on `Signal (BitVec n)`): `lake test` failed on the
YOLOv8 SPPF/C2f controllers and `FPGABench`, and they were added. Under the
semantics decision this bug is exactly a table row with no `library_*` lemma.

### What is proved (standard axioms only)

- `translateCanonicalSignalBinary_sound`: the Signal×Signal branch of the
  SHIPPING operator lowering, for `+ - * &&& ||| ^^^` at every literal width,
  given a `translate` satisfying `Spec` (the recursion hypothesis).
- `translateSignalPureLiteral_sound`: `Signal.pure` of a `BitVec` literal, a leaf
  (no recursion hypothesis). Constants such as `a + 3#8` reach the translator
  this way: the elaborator coerces `3#8` to `Signal.pure (BitVec.ofNat 8 3)` and
  picks the Signal×Signal instance.
- Supporting: `makeWire_returns`, `emitAssign_returns`, `evalExpr_const_lt`,
  `bitVecLitValue?_lt`, `WidthsAgree.mono`, `fuelFix_spec`, `spec_of_never`.

Both branches are the code that runs. `translateCanonicalSignalBinary` and
`translateSignalPureLiteral?` were extracted from `translateExprToWireImpl`
without changing behaviour, except that the width and literal value are now read
purely from the instance/literal when possible. That is what makes the proof
oracle-free. Output was compared with the original compiler on the operator and
literal probes (including `300#8`, which falls back to the oracle path): it is
byte-identical.

### Existing proofs used

| Existing result | Used for |
|---|---|
| `CircuitM.makeWire_spec` (Builder) | the result wire is fresh, then reserved; statements unchanged; declaration added |
| `emitAssign_sound` (ShippingBuilderSoundness) | the emitted assignment extends execution by exactly its RHS value |
| `Binary.rhs_correct` (ShippingScalarSoundness) | the IR operator computes the `BitVec` operation at width `n` |
| `Binary` / `Binary.apply` (ShippingScalarSoundness) | the operator vocabulary the semantics and the table share |

### Premises that remain (none is the preservation claim itself)

1. **The recursion hypothesis** `Spec translate …` in the operator theorem.
   `fuelFix_spec` discharges it once (a) the shipping knot is `fuelFix step N`
   rather than `partial`, and (b) every branch of `step` is proved. Both are
   open; (b) is the bulk of the work. A step spec covers every successful
   branch, so unproved handlers block the unconditional theorem.
2. **Defined source meaning** (`Denotes ρ e n x`). Coverage — success implies
   `Denotes` — is open. For the operator branch it needs the operands' widths to
   equal the instance width, which Lean typing guarantees but the proof cannot
   see. It needs either a typing argument or a compiler-side width check.
3. **`WidthsAgree we s1`** on the final state: satisfiable by taking `we` from
   the final module; the knot-level theorem must instantiate it.
4. **Source bindings.** `Spec` does not yet carry the binding invariant, so the
   `fvar` leaf (lookup of an input wire) is not a proved branch. The existing
   `Valid.lookupVar` supplies it once `Spec` is extended.
5. **Declaration ↔ `Denotes`.** Each clause agrees with the library by `rfl`, but
   the link from a user declaration's body to its Lean value (reflection) is not
   formalised here.
6. **Coverage of the two branches.** Only canonical `BitVec` instances with a
   LITERAL width and literals below `2^w` take the oracle-free path. `Bool`
   instances, shifts, the mixed Signal×BitVec branch, symbolic widths and
   out-of-range literals take the unchanged oracle path and are not covered.
7. **Mutable `IO.Ref` state.** Its contents are not modelled. Any ref whose
   content affects the IR — the expression cache, `sparkleTypeCache` (widths),
   `sparkleWireWidthCache`, the loop/wire-canon caches — must become pure state
   (as `sourceBindings` did in `9935dfe`) before the knot-level theorem.
   Profiling and limit refs only log or throw, which partial correctness
   tolerates.

## End-to-end theorem for a fragment of the real translator (2026-09-25)

`translateExprToWire_sound` (Tools/ShippingTranslateSoundness.lean, standard
axioms only) is about the SHIPPING entry `translateExprToWire`. For every
expression built from **inputs, `BitVec` literals under `Signal.pure`, and the
canonical library operators `+ - * &&& ||| ^^^`, in any combination and at any
literal width**, it says: if the expression has a meaning (`Denotes`) and the
translation succeeds, the returned wire carries that meaning at that width. The
state invariant `Inv` (statements evaluate, bindings, translation record) is
preserved, and every previously reserved wire keeps its value. **No recursion
hypothesis remains.**

### What had to change on the actual path, and why it is still the same compiler

1. **The knot is an ordinary definition.** The translator block now takes its
   recursive entry as a section `variable`, so the handler bodies are textually
   unchanged, and the entry is `translateExprToWire := translateFuelFix
   translateStep translateFuelLimit`. It is non-partial, so it has equations.
   Every recursive call, including those from the `partial` fallback handlers,
   goes through the fuel. A `partial` entry could not have worked: it is opaque,
   so a theorem about the fixpoint would not transfer to it. Fuel exhaustion
   (depth 2^20) is a compile error, like the existing `SPARKLE_TRANSLATE_LIMIT`.
2. **A proved core is tried first.** `translateCore` handles an `fvar` bound by
   `lookupVar`, a `Signal.pure` literal, and a canonical operator with literal
   width; anything else returns `none` and reaches the unchanged handler chain.
   For the three shapes, the core runs the same code the chain ran before.
3. **The expression cache is consulted, and each hit is validated.** Bypassing
   the cache changed 84/163 corpus files (α-equivalent: only wire numbers
   shifted, because a second translation allocated and `mergeDuplicates` later
   removed the copy). So the core path looks up the same `IO.Ref` cache, but
   accepts a hit only if a PURE record (`CircuitState.translateRecord`, wire →
   the expression the core produced it for) holds a structurally identical
   expression, decided by `exprDecEq`. This sidesteps the earlier cache problem
   (`KeySound`, `InsertSpec`): the opaque `Expr.equal` only proposes a
   candidate, and the pure data decides. Recording `fvar` results is excluded:
   they reuse an existing wire, and recording them overwrote what the wire was
   made for (found through the one remaining α-equivalent file).
4. **`exprDecEq`** (Sparkle/Compiler/ExprDecEq.lean) is a `Decidable (a = b)`
   for `Lean.Expr` written in Lean. It has a pointer fast path at every node
   (`withPtrEqDecEq`), a hand-written `Syntax` equality (a nested inductive
   `deriving` refuses) and a hand-written `Level` equality (`computed_field`).
   A tree walk without the fast path unfolded DAGs: Keccak256Sponge went from
   3.3 s to 54 s.

**Output identity, measured.** All 163 files that synthesize Verilog (297
modules) were run before and after. The final compiler's output is
**byte-identical on 163/163**. Corpus time is 207 s against 197 s (+5%). The
heaviest regressed files carry ~+2 s each (validation), down from +50 s.

### Existing proofs used by the end-to-end theorem

| Existing result | Where |
|---|---|
| `CircuitM.makeWire_spec`, `makeWire_sourceBindings` (Builder) | fresh result wire; bindings untouched |
| `emitAssign_sound` (ShippingBuilderSoundness) | an emitted assignment extends execution by exactly its RHS |
| `Binary.rhs_correct` (ShippingScalarSoundness) | the IR operator computes the `BitVec` operation |
| `lookupVar_run`, `visible` (ShippingBindingsSoundness) | the `fvar` leaf: the real lookup, local-first then persistent |
| `Returns.*`, `library_*` (this file, earlier) | success rules; semantics tied to the library by `rfl` |

New, all standard axioms: `Denotes.det`, `Inv.transfer(_except)`,
`RecordOk.insert`, `translateFuelFix_spec`, the three branch theorems,
`translateStep_core`, `translateStepWith_spec`, `exprDecEq`, `synEq_iff`,
`levEq_iff`. The regression test also goes through the actual synthesis entry
(`synthesizeCombinational`). It fails on the pre-fix compiler (negative
control) and passes on the fixed one, and the canonical `+` synthesizes to IR
that evaluates to the source value.

### Open, and kept separate from the theorem

Items 1–3 were discharged at the synthesis entry for the fragment's
declarations on 2026-09-25; see the next section. What remains of each is
stated there.

1. **Correspondence with the user's declaration.** Was: `Denotes` is a relation
   on the `Lean.Expr`; the step to the declaration's Lean value was missing.
2. **Coverage of the success region.** Was: "success ⇒ `Denotes`" open.
3. **The entry invariant.** Was: `Inv` and `WidthsAgree` not established by
   `synthesizeCombinationalCore`.
4. **The fragment.** Every other handler is the unchanged `partial` fallback:
   mixed Signal×BitVec operators, `Bool` instances, shifts, comparisons, mux,
   registers and time, memories, hierarchy, symbolic widths.
5. **After translation.** `dropZeroWidth`, `mergeDuplicates`, the printer, and
   the Verilog semantics.

## Synthesis entry: `Inv`, `WidthsAgree` and `Denotes` discharged (2026-09-25)

`Tools/ShippingEntrySoundness.lean` (standard axioms only, audited in
`Tests/Compiler/ShippingEntrySoundnessTest.lean`). The theorem is about the
REAL entry `synthesizeCombinationalCore declName [] false`, i.e. the step of
`#synthesizeVerilog` before post-processing.

**Correction (2026-09-25, second pass).** The first version of this section
claimed the entry was "connected to the user's declaration without premises".
That was not true. Its theorem said `∃ ci, CertifiedOutcome ci M` with
`MReturns`, which closes over contexts and worlds, so `ci` was not tied to the
run that produced `M`. Nothing applied it to a real declaration either; the
test checked the quotation, `rfl` and sample evaluations separately. Fixed as
follows:

* **The run and the constant it read.** Runs are stated in fixed contexts and
  state references (`RunsTo m mctx mref cctx cref w a w'`).
  `synthesizeCombinationalCore_reads`: a successful run executes
  `getConstInfo declName` IN THE SAME contexts and references (worlds
  `w1 → w2`), returning `ci`, and then runs `synthesizeFromConst … ci` from
  `w2` to the result.
* **Post-read processing as a function of `ci`.** `synthesizeFromConst`
  (shipping code) is everything after the read. The real entry calls it with
  the result of `getConstInfo`, and `synthesizeFromConst_sound` proves
  `CertifiedOutcome ci M` for it. `synthesizeCombinationalCore_sound`
  combines the two: `∃ ci w1 w2, RunsTo (getConstInfo declName) … w1 ci w2 ∧
  CertifiedOutcome ci M`.
* **Applied to a real declaration.** `fragA_ir_correct` (in the test module)
  holds for ANY successful run of `synthesizeCombinationalCore ``fragA` whose
  environment satisfies `EnvDefines … ``fragA fragAValue`. It gives two
  distinct input ports `pa ≠ pb`, and for every domain, all signals `a b` and
  every cycle `t`, the IR drives `out` with `(fragA a b).val t`. Here
  `fragAValue` is `fragA`'s value read from the environment
  (`#def_decl_value`), and `fragAValue = quoteDecl … feA` is proved by `rfl`.

What remains assumed is exactly one statement about Lean's environment:
`EnvDefines mctx mref cctx cref declName v`, "in the run's contexts every
`getConstInfo declName` returns a definition with value `v`". It cannot be
derived in the logic, because the Core state sits behind an `ST.Ref` whose
operations are opaque. It is a hypothesis of the corollary, not hidden.
`fragAValue` comes from the same `getConstInfo` at elaboration time.

Main theorems:

* `synthesizeCombinationalCore_sound`: see above; `CertifiedOutcome ci M`
  means `certifiedShape? ci = some (bs, body)` implies `Preserves bs body M`
  (distinct input ports, and for all binder values, if the instantiated body
  `Denotes` `x`, then `evalAssigns (weOf M) mems M.body initial = some env`
  with `env "out" = x`).
* `fragmentDecl_sound` / `fragmentDecl_sound_signal` (entry, same-run `ci`),
  `outcome_quote` (for a constant quoting `fe`, no `Denotes` premise),
  `fragmentDecl_of_env` (with `EnvDefines`), and `fragA_ir_correct`.

### Premises that disappeared from the entry theorem

| Premise of `translateExprToWire_sound` | How it is now derived |
|---|---|
| `Inv ctx ρ we mems initial s0 env0` at the leaf call | From the entry's own construction: `CircuitM.init` (empty body, record, bindings), the binder walk `bindCertifiedInputs` (fresh wire per `Signal` binder, reader-scoped binding found by the real `lookupVar` path, input port), the valuation `rhoOf` of the binder values, and `env0 = initial` (`bindCertifiedInputs_returns`, `rhoOf_some`) |
| `WidthsAgree we s1` | `we := weOf M`, the widths READ OFF the returned module's wires. Holds because wire names stay distinct: `WiresOk` is now part of `Grows` and carried through every translator branch (`widthsAgree_weOf`) |
| `Denotes ρ e n x` | For `quoteDecl … fe`: the gate accepts it (`certifiedShape_quote`), the entry's instantiated body is the quotation over its fvars (`instFVars_quoteBody`), and it denotes `evalFE` (`denotes_quote`); `evalFE` is the library meaning by `rfl` (`denoteFE_val`) |
| (implicit) the leaf call happens, with that state, and `out` is driven by it | `emitLeaves_single`, `finishSynth_returns`, and the MetaM success rules `MReturns.bind/pure/throw/try_finally/ite` through the entry's profiling, depth bookkeeping and `try … finally` |

### What changed in the shipping entry, and why it is still the same compiler

1. The entry was a `partial def` inside the translator's `partial` block: to
   the kernel an `opaque`. It is now an ordinary definition
   `synthesizeCombinationalCoreWith (translate)`, moved before the block with
   `splitReturnLeaves`, `openRecordInputs`, `stripMemoizeWrappers` (which never
   used the translator). `synthesizeCombinationalCore` after the block passes
   the real translator.
2. The binder walk (`bindInputsLegacy` / `bindInputPort`), the leaf loop
   (`emitLeaves`, explicit recursion instead of a `for` with `mut`) and the
   module finish (`finishSynth`, `addClockResetIfSequential`) are plain
   definitions shared by both front ends.
3. For the certified shape — `DomainConfig` and `Signal dom (BitVec n)`
   binders over a body of binders, `Signal.pure` literals and canonical
   operators at one literal width — the front end is pure: `certifiedShape?`,
   fresh fvars checked distinct, `instFVars` (a pure twin of the `extern`
   `instantiateRev`), and the single leaf `out`. The legacy front end
   (`openRecordInputs`, `stripMemoizeWrappers`, `lambdaTelescope`,
   `splitReturnLeaves`) is `partial` or `extern`-based; on this shape it
   computes the same thing. Checked: the test compares both front ends on real
   declarations (identical `Module`, identical Verilog); the corpus is
   byte-identical.
4. New refusals (both measured never to fire on the corpus): a leaf's port name
   that is already a name of the module (its `assign` would overwrite that
   wire), and non-distinct fresh fvars.
5. `canonicalSignalBitVecWidth` tests the `Bool` instances by an explicit list
   (`canonicalSignalBoolInsts`) instead of `toString.endsWith "Bool"`; same
   result on the table, but the suffix test does not reduce in proofs.

### What remains (named)

1. **`EnvDefines`.** The constant is the one the run read (proved), but that
   the run's environment defines the declaration as elaborated is the
   hypothesis `EnvDefines` (the Core state is behind an opaque `ST.Ref`).
   `fragAValue` is taken from the same `getConstInfo` at elaboration time.
2. **Post-processing** is now included (next section): the theorems reach the
   IR `synthesizeCombinational` returns.
3. **Coverage beyond quotations.** "Gate accepted ⇒ a meaning exists" is proved
   for quotations of `FExpr` (`+ - * &&& ||| ^^^`, literals, inputs). The gate
   also accepts canonical shifts (the translator core lowers them), but
   `Denotes` has no shift clause, so for shifts `Preserves` holds vacuously:
   on the certified front end, NOT proved. Declarations outside the gate take
   the legacy front end and are not covered.
4. **Verilog.** The IR semantics is `evalAssigns`; printing and Verilog
   semantics are separate.

## Post-processing: `dropZeroWidthModule` and `mergeDuplicates` (2026-09-25)

`Tools/ShippingPostSoundness.lean` (standard axioms only, audited). The
theorems now reach the IR returned by `synthesizeCombinational`, which is what
`#synthesizeVerilog` compiles: the entry, then `dropZeroWidthModule`, then
`mergeDuplicates` (skipped when `SPARKLE_NO_REGDEDUP` is set; both branches are
covered).

* `synthesizeCombinational_reads`: a run of `synthesizeCombinational` runs the
  entry in the SAME contexts and state references, and returns
  `dropZeroWidthModule M` or `mergeDuplicates (dropZeroWidthModule M)`.
* `dropZeroWidth_entry`: on a module with the entry's shape at width `n > 0`,
  the pass changes no statement, and the widths read off are unchanged.
* `mergeDuplicates_sound`: on a combinational module the pass yields the SAME
  environment under the module's declared widths, with the same ports.
* `postprocess_sound`: the two composed in call order.
* `synthesizeCombinational_fragment` and, in the test, `fragA_ir_correct`: for
  any successful run of `synthesizeCombinational ``fragA` whose environment
  satisfies `EnvDefines … ``fragA fragAValue`, the RETURNED module drives `out`
  with `(fragA a b).val t` on every input and cycle.

### Premises, and where they come from

| Needed by | Premise | Derived from |
|---|---|---|
| `dropZeroWidthModule` | Wire names distinct; `out` not a wire; every statement assigns a const or op-of-refs to a declared width-`n` wire, or is `out := w`; `outputs = [out : n]` | `PostReady M n`, read off the entry's construction. The translator now carries `Emits n` (prepended statements have that shape; outputs unchanged) through every branch. The output port's type is the leaf wire's declared type, width `n` because `weOf M w = n` |
| `dropZeroWidthModule` | `n > 0` | A property of the declaration (`decide` for `fragA`). At `n = 0` the pass does drop the `out` assignment, so the exact statement would be false |
| `mergeDuplicates` | Body is combinational (only `assign`) | `PostReady` |
| `mergeDuplicates` | The merge is value- and width-preserving | Checked, not assumed (below) |

### What changed in the compiler, and why

Rather than prove the current implementation directly, the result-checking
approach is used: the merge is an untrusted proposal, and on a combinational
body only a result accepted by `validateMerge`, a pure checker proved sound in
general (`validateMerge_sound`), is kept. Statement by statement, the checker
requires:

* the new statement assigns the same name;
* every reference the old statement makes to a name the body assigns points at
  an EARLIER statement;
* the new right-hand side equals the old one with references renamed through
  the accepted merges; OR it is a reference to an earlier representative whose
  canonical right-hand side is equal, with the same declared width.

If the check fails, the module is returned unchanged. Bodies with registers,
memories or instances keep the unchecked merge, outside the fragment.
Measured: the corpus is byte-identical (163/163), so the checker never rejects.
A test (`dupLit`) exercises a real merge on a certified-shape module and checks
that it is accepted. The width condition is new: the old signature ignored
declared widths, so two wires with equal right-hand sides but different
declared widths could have been merged, which changes an enclosing
concatenation. The corpus has no such case. A hand-built IR regression
(`widthMismatch` in the test) pins the rejection side: the unchecked proposal
merges an 8-bit and a 16-bit wire and changes `out` from 65537 to 257 at
`x = 1`; the checker rejects it, and the shipped `mergeDuplicates` returns the
module unchanged. This is not a demonstration from a user circuit.

`synthesizeCombinational` was a `partial def` in the translator block; it is
now an ordinary definition `synthesizeCombinationalWith`, like the entry.

### Scope of the guarantee

The guarantee is about evaluating the statement list (`evalAssigns` on the
body) under the declared widths, plus ports. `mergeDuplicates` also rewrites
`assertions`; neither the checker nor the theorems cover that. The fragment's
modules have no assertions, so nothing is lost for them. This is NOT a claim
of semantic preservation for whole arbitrary combinational modules.

### What remains

* `EnvDefines`, as before.
* **Width 0 is an open item inside the success region.** The theorems need
  `n > 0`. A width-0 declaration of the fragment still synthesizes, and
  `dropZeroWidthModule` removes its `out` assignment, so "what synthesizes is
  equivalent" is not yet met there. Still to decide: either a specification
  under which dropping a zero-width output keeps the meaning, or an explicit
  refusal.
* Registers, memories and instances are outside the fragment; their merge path
  is unchecked.
* Verilog printing and Verilog semantics.

## Toward the printed Verilog: the optimizer and the printer (2026-09-25)

`#synthesizeVerilog` prints `verilogOf M = toVerilog (checkedOptimize M)`,
where `M` is `synthesizeCombinational`'s module. There was one more stage
between the post-processed IR and the text: the IR optimizer `optimizeModule`
(constant/alias propagation, CSE, dead code, single-use inlining; it also
inserts `& mask` so that Verilog's context-width arithmetic matches the IR's
per-node masking).

### The optimizer: result-checked

`Sparkle/IR/OptCheck.lean`, proved in `Tools/ShippingOptSoundness.lean`. As
with the merge, the optimizer's output is an untrusted proposal:

* `checkedOptimize m`: if `m`'s body has the simple shape (every statement
  an `assign` of a constant, a reference, or one of `+ - * & | ^` on two
  references), the optimised module is kept only if `optCheck` accepts it;
  otherwise `m` is printed unoptimised. Other modules get `optimizeModule`
  unchanged.
* `optCheck m o`: requires the same ports, and every output normalising to the
  same expression in both modules. Normalisation inlines each assignment's
  normal form into later uses, only when the wire's declared width equals the
  expression's width. It drops `e & (2^w-1)` when `e` has width `w` and reads
  only inputs. The optimised side trusts only inputs declared with the same
  width in both modules.
* `optCheck_sound`: an accepted `o` evaluates, and every output has the same
  value, for every input assignment whose values fit the declared input
  widths. `checkedOptimize_sound`: the same for whatever `checkedOptimize`
  returns on a simple-shaped module.
* Measured: the corpus is byte-identical (163/163). On `fragA`, `fragC` and
  `fragD` the real optimizer's result is accepted. A test pins the rejection of
  a hand-built wrong "optimisation".

`printedModule_fragment` (in `Tools/ShippingPostSoundness.lean`) and
`fragA_printed_correct` (test): for any successful run of
`synthesizeCombinational` on a quoted fragment declaration, under
`EnvDefines`, the module `checkedOptimize M` (exactly what `toVerilog`
receives) drives `out` with the Lean meaning on every input and cycle. The
premises of `checkedOptimize_sound` are derived, not assumed:

* **Simple shape:** the translator's emitted shape IS `simpleRhs`. It survives
  `dropZeroWidthModule` (body unchanged) and an accepted merge (each new
  statement is a renamed old one or a reference; `validateStep_shape`).
* **Input bounds:** the entry now proves that the module's inputs are exactly
  the binder ports, declared at width `n`. The translator records that inputs
  are unchanged, and no clock/reset is added for an assign-only body.

### The printer: made total

`emitExpr` and `exprWidthV` in `Sparkle/Backend/Verilog.lean` were `partial`.
They are now ordinary definitions with the same code: `attach` in the concat
case, and a named match giving the termination proof. The corpus is
byte-identical.

### Shipping printer bridge: expression and assignment text (2026-09-25)

`Tools/ShippingPrintSoundness.lean` now proves byte equality, without a
parser oracle, between the shipping printer and a renderer over the existing
SV AST for fitting nonnegative constants, references and arbitrarily nested
`+ - * & | ^` expressions. This includes the optimizer's mask expressions.

* `emitExpr_render`: `emitAstExpr` succeeds and rendering that SAME tree
  equals the shipping `emitExpr` string.
* `printedExpr_semantics`: composes this with `emit_sem_evalSV`; it retains
  the explicit `sf4Check` and bounded-environment hypotheses. These are NOT
  yet derived at the declaration entry.
* `emitStmt_render` / `emitBody_render`: the same for assignment statements
  and their body text, with the shipping printer's blank-line separator.
* `acceptedOptimizer_body_render`: a successful shipping `optCheck` itself
  supplies the expression-shape premise for every statement of the accepted
  optimized body. It does not cover the fallback arm merely by naming it.

The proof/test modules are registered in Lake and `Tests.AllTests`. The test
audits the seven bridge/shape theorems for standard axioms only, exercises a
nested masked expression, and checks rejection of unsupported rendering forms.
No compiler, optimizer, or printer behavior changed in this step.

**Review of proposed option A:** retaining an optimizer result only after a
forward-fragment check is sensible, but the fallback's check must be proved
before claiming all returned modules satisfy it. Do not add an unproved check
premise to the source-to-text theorem. The proposed binder-character condition
`[A-Za-z0-9_$]` is insufficient for valid unescaped SV identifiers: e.g. `1bad`
and `module` are sanitize-fixed but not ordinary legal identifiers. The lexical
contract must address the first character, keywords, module/port/wire names,
and name collisions. Sanitize stability and lexical validity are separate.
The existing lexer has a subset keyword list; it must not be advertised as a
complete SystemVerilog keyword specification.

Next, in order:

1. Prove rendering of module headers, ports and wire declarations, and compose
   with assignment-body rendering to relate `toVerilog` to `emitAstModule`.
   Preserve the original module-name comment and distinguish zero-width ports
   (the two emitters do not currently print identical type syntax there).
2. Establish the lexical contract for the source fragment and generated names.
   Until then byte equality is NOT a theorem that an SV tool parses the string.
3. Derive `assignsCheck` and its width/environment conditions for the fallback,
   then strengthen optimizer acceptance and prove both returned branches meet
   those conditions. Avoid importing proof-only `Tools` dependencies into the
   shipping IR layer; factor the executable checker if needed.
4. Compose the existing declaration theorem with the module rendering and SV
   evaluation theorems. Any trusted rendering-to-grammar interpretation must
   remain explicit, distinct from the proved byte equalities.

### Still open on this path

* **Text ↔ SV semantics (next).** Relate `toVerilog (checkedOptimize M)` to
  the existing SV-subset semantics (`evalSV`, `emit_sem_assigns` in
  `Tools/SVParser/EmitSem.lean`, which relate the IR to an SV AST).
  Remaining: the printed string is the rendering of that SV AST, the width
  conditions `assignsCheck` needs, and the output-port width environment.
  The SV grammar (that tools read the rendered text as that AST) will remain
  the trusted step.
* Width 0, `EnvDefines`, registers/memories/instances, as before.

## Applying the general theorem to crc16

The desired application is: check successful shipping compilation (and any
explicit admissibility conditions), then apply the general preservation theorem.
It must not invoke a circuit-specific semantic replay proof. No such complete
shipping success theorem exists yet. Source inspection of `crc16CcittHW` and
`crc16Step` identifies the following coverage obligations; this table is not an
execution trace or an exhaustiveness proof for the handlers they invoke.

| crc16 construct / compiler stage | General proof status |
|---|---|
| map/application, BitVec AND/XOR | Source application rule and canonical scalar RHS rules proved. Canonical Signal×Signal operators, literals and inputs: end-to-end theorem for the ACTUAL entry `translateExprToWire`, recursion discharged (2026-09-25); recognition instance-checked. Other dispatch still the unproved fallback |
| local bindings, wire allocation | Actual allocation/emission and scoped binding rules proved; cache hit/insert rules proved (2026-09-25) under explicit key hypotheses; global source/width invariant still open |
| pure constants, concat, shift, equality, Bool not, mux | `Signal.pure` of a `BitVec` literal proved as a leaf branch of the actual translator (2026-09-25); concat, shift, equality, Bool not and mux still open |
| register init `0xFFFF`, update, feedback, start/valid mux | Temporal simulation of the shipping stateful path remains open |
| helper unfolding, output record packing, Bool/BitVec ports | Source recognition and interface correspondence remain open |
| zero-width cleanup and register deduplication | Composition with the shipping success theorem remains open |

The current bounded frontend and crc16's per-instance certificates do not close
these rows. Generic theorem/axiom checks are the primary criterion. For the
state-storage change, synthesis and scope regressions check integration; they
do not discharge additional rows of the general proof.
