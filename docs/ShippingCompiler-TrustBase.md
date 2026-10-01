# Shipping compiler: the retained trust base

The CompCert-style theorems in `Tools/Shipping*` prove the compiled
artifacts against the source `Signal` semantics. This file states, in
one place, everything the final claim RETAINS rather than proves —
each item with its precise formal location, why it is retained, and
what would discharge it. Nothing here is hidden inside a proof; every
boundary is either a hypothesis of a theorem or a runtime gate in the
test suite.

## 1. The Lean kernel and the three standard axioms

Every theorem is checked by the Lean 4 kernel and audited (in the test
suite, via `collectAxioms`) to use only `propext`,
`Classical.choice` and `Quot.sound`. `sorryAx`, `ofReduceBool` /
`native_decide` and custom axioms are rejected by the audits.

## 2. `EnvDefines` — what the run's environment says a name means

`Tools.ShippingEntrySoundness.EnvDefines mctx mref cctx cref declName v`
says: every `getConstInfo declName` in THIS meta context returns a
definition whose value is `v`. Every entry endpoint takes it as a
hypothesis. It is retained because the theorems live over the actual
`MetaM` run: the connection between a `Name` and the Lean term the
elaborator holds for it is a fact about the runtime environment, not
about any function we can compute on. Discharging it would mean
reflecting Lean's environment into the logic; retaining it keeps the
statement honest: *if* the environment defines the declaration as the
quoted source, the compiled module means that source.

## 3. Runtime-gated decidable premises

Several theorems take decidable premises that the test suite evaluates
on the real pipeline artifacts and enforces with `throwError` gates:

- `seqOptCheck m o = true` — the sequential rename-equivalence checker
  (optimizer output and sequential merge), gated per certified register
  shape in `Tests/Compiler/ShippingRegisterSoundnessTest.lean`.
- `seqCheck`, width agreement, `semFragCheck`, `bodyImage`,
  `bodyReorderCheck`, fragment membership of the parsed-back body —
  the emitted-SV and parsed-bytes chains, gated in the same file (the
  parse gates run the REAL parser on the REAL printed bytes).
- Post-processing identity on the certified memory shapes
  (`Tests/Compiler/ShippingMemorySoundnessTest.lean`).
- The byte-level pinning gates for the memory and hierarchy canonical
  shapes, and the sub-module-equals-standalone-compile gate
  (`Tests/Compiler/ShippingHierarchySoundnessTest.lean`).

The division of labour is deliberate: theorems quantify over any
artifacts satisfying the premise; the gates pin that the premise holds
for what the pipeline actually produced in this build. A gate failure
fails `Tests.AllTests`.

## 4. The byte → AST direction of the printed text

For sequential modules the byte-level connection runs in the PARSE
direction (`Tools/ShippingSeqSVSoundness.lean`,
`seq_run_to_parsed`): the module the shipping parser reads back from
the printed Verilog is proved trace-equal to the checked module. The
parser/lowering step itself (bytes → SV AST → IR) is the retained
base, exactly as in the corpus roundtrip validation (Test 68). A
render-direction proof for sequential text is blocked on the SV AST:
`SVSensitivity` cannot carry the asynchronous reset's compound
sensitivity list. Combinational modules additionally have the render
direction (`printedModule_render`).

The M4 emitted-SV semantics layer (`certified_forward_trace`) covers
assigns, registers and combinationally-read memories; SYNC-read
memories (the certified `Signal.memory` shape) are outside `seqCheck`
today — for them the byte-level story currently ends at the
post-processing identity gates plus the IR endpoints.

## 5. The linked meaning of module instances

`Tools.ShippingHierarchySoundness.evalAssignsH` DEFINES what an
instance means: the child's outputs are the standard evaluation of its
own body on the connection-fed environment. The shipped `runModule`
keeps the open-module view (instance outputs free). The definition is
exercised against the real compiled parent/child pair and the child is
gated to be its own certified standalone compile, but the
correspondence of `evalAssignsH` to Verilog module instantiation is
part of the retained base until the SV layers become
hierarchy-aware.

## 6. Boundaries the S6 entry work will add (design note)

Proving the parent's entry theorem for the instance-emitting path will
need two further boundary predicates, mirroring `EnvDefines`:

- (LANDED) `SubSynthDefines mn mc dc`
  (Tools/ShippingInstanceEntrySoundness.lean): every nested child
  synthesis of `mn` the run performs returns exactly `(mc, dc)` — the
  hierarchical mirror of `EnvDefines`, stated over `MReturns` of the
  precise `Rec.synthesizeCombinational` call the arm makes. One
  sibling boundary lands with it: `HardwareTagged mn` (every
  environment the arm reads designates `mn` as `@[hardware_module]`).
  The former third boundary `InstanceCacheEmpty` is GONE: the arm now
  honours a single-out cache hit only when the builder's own
  `translateRecord` says the cached wire was produced for this very
  expression (`instHitValid`, the same validation
  `cacheLookupValidated` applies to the expression cache), so at a
  root call — empty record — no hit is possible whatever the mutable
  cache holds (`instHit_empty`), and inside cones a hit is sound by
  the existing `Records` invariant. Every lowering through the arm
  records its result wire, so a repeat of the same call still dedupes
  (suite-gated byte parity). The
  parent-level `getEnv` that picks the run's gate predicate is exposed
  by `synthesizeCombinationalCore_reads`, so the entry endpoint's tag
  boundary is an `EnvDefines`-style `RunsTo` fact at the entry's own
  contexts. One further retained premise: the parent declaration's
  TYPE is one scalar Signal (`mixedGateResultScalar`; `EnvDefines`
  pins only the value) — the test suite checks it holds for the real
  declaration.
- (LANDED) Cone leaves (Tools/ShippingInstanceLeaf.lean,
  Tools/ShippingHierTermSoundness.lean). An instance call inside a
  certified cone is lowered below the entry fuel, so its child pin is
  `SubSynthDefinesAll mn mc dc` — the `SubSynthDefines` statement at
  EVERY recursion fuel. The linked semantics needs two further
  premises, both about the pinned child rather than the run:
  `HierCtx.children mc.name = some (mc, cwe)` (the child table the
  contract is stated against contains the pinned module under its
  name — the suite checks `d.modules` concretely; proving the
  registration from the run is open) and `ChildCorrect mn mc cwe out`
  (the pinned child's body computes the `ChildSem` source function on
  any environment carrying the packed arguments — a statement about
  one fixed module, proved outright for the test child by
  `childAdd_correct`; in general it is the child's own certified
  endpoint). No cache premise is needed on either validated cache
  path. What the linked statement MEANS is still §5's definition
  (`evalAssignsH`, one level deep).
- (RESOLVED, width linkage) `evalAssignsH` passes full values across
  instance connections, so it is only faithful to module
  instantiation when every connection joins equal widths. That is no
  longer a premise: the arms check it before emitting
  (`instLinkCheck`), and the contracts conclude it (`Linked`,
  `InstsLinked`). What remains trusted is that the checked widths are
  the widths the SV printer declares — the declared port/wire types
  the check reads are the same `Module` fields the printer emits.
- (LANDED, hierarchy at the SV layer) The printed-text statements for
  hierarchical parents are stated in the open-module view under the
  ORACLE SEEDING: instance-output wires carry the values the linked
  semantics gives them, and `Consistent` says those values are each
  child's evaluation on what its instance reads. What is trusted is
  therefore unchanged from the flat layers (the SV semantics of the
  assign fragment, the parser) plus §5's reading of an instantiation
  as "outputs equal the child's function of the connected inputs" —
  now used in its order-free form (`Consistent`), not only as the
  sequential fold `evalAssignsH`. The optimizer on instance-bearing
  modules is covered by translation validation, not by
  `checkedOptimize` itself (which does not check there): the
  capstone takes the decidable gates `optCheck` on the
  interface-extracted pair, `instsKept` and `connAgreeOk` as
  premises, and the suite evaluates them on the real modules. As
  with the sequential shapes, an optimizer change that broke a gate
  would fail the suite, not silently ship.
- (LANDED) The projection arm's boundaries
  (Tools/ShippingInstanceEntrySoundness.lean), for a parent
  `field (child args…)` over a multi-output child:
  `ProjEnvDefines pn structName cn` (every environment the arm reads
  says: `pn` is not itself tagged, it is a projection of `structName`,
  and the record call's head `cn` is tagged), `ProjFieldDefines pn
  structName fieldName` (the arm's field-name resolution
  `projFieldName?` — projection info, the structure's constructor
  binders — returns `fieldName`), and `OutCacheEmpty` (every read of
  the multi-output port map comes back empty; morally the depth-0
  reset again). `SubSynthDefines` is reused for the child. The suite
  checks the static facts (`getProjectionStructureName?`,
  `projFieldName?`, untagged projection) on the real declarations.
  The arm's call key is computed by `instCallKey`, which restores the
  saved builder state after canonicalizing, so the canonicalizer is
  NOT in the trust base of the contract (the key only indexes the
  port map, which the boundary says is empty).
- (RESOLVED) The instance caches (`sparkleSubInstanceOutputs`,
  `sparkleSingleOutInstanceCache`) are `IO.Ref`s but are RESET at
  depth 0 of every top-level synthesis (Issue #67,
  Sparkle/Compiler/Elab.lean:2589) — they are per-synth dedupe, not
  session history. A certified lowering that skips them is therefore
  byte-identical for canonical single-call shapes; no cache premise is
  needed.
- (RESOLVED) The gate/environment obstacle: `mixedCertifiedShape?` now
  takes an `isInst : Lean.Expr → Bool` parameter (default
  `fun _ => false`), the real dispatch passes `instancePredicate env`
  (a `getEnv` read: head constant tagged `@[hardware_module]`), and
  `synthesizeCombinationalCore_reads` exposes the run's predicate
  existentially. Every OLD family's acceptance is
  predicate-independent, so their gate lemmas are stated
  `∀ isInst, mixedCertifiedShape? … isInst = some …` and the entry
  wrappers take that ∀-form premise — structural consumers
  (`mixedShape_positive` etc.) instantiate it at the default
  predicate and stay untouched. The instance family's own acceptance
  WILL depend on the run's predicate; its future wrapper carries the
  per-run predicate boundary instead of the ∀-form.

## 7. What is NOT retained

For the certified shapes, the following are proved, not assumed: the
translation of the quoted source (the family monoliths), the
elaboration semantics of the emitted module (`stepModule`/`runModule`
against the source streams), zero-width cleanup and (where gated)
merge/optimize behaviour, the rename-equivalence of the optimizer's
sequential output, the emitted SV objects' cycle semantics, and the
trace of the parsed-back text.
