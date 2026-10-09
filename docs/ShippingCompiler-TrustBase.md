# Shipping compiler: the retained trust base

The CompCert-style theorems in `Tools/Shipping*` prove compiled artifacts
against the source `Signal` semantics. This file states, in one place,
everything the claim RETAINS rather than proves: what is assumed, where
it enters formally, and what would discharge it. Nothing here is hidden
inside a proof — every item is a hypothesis of a theorem, a gate the test
suite evaluates, a definition that carries meaning, or an explicit
statement that something is outside every theorem.

Read it together with
[ShippingCompiler-Coverage.md](ShippingCompiler-Coverage.md), which says
WHICH compiles the theorems apply to. The short version: the theorems
are conditional on a syntactic gate, and on the measured corpus most
real designs do not pass it (§7).

## 1. The logical base

Every theorem is checked by the Lean 4 kernel and audited in the test
suite (`collectAxioms`) to depend only on `propext`, `Classical.choice`
and `Quot.sound`. `sorryAx`, `ofReduceBool` / `native_decide` and custom
axioms are rejected by the audits.

## 2. Run-environment boundaries

The theorems are stated over the ACTUAL `MetaM` run of the compiler
(`RunsTo`, `MReturns`). What a run reads from Lean's environment or from
mutable references cannot be derived inside the logic, so each such read
that a proof depends on is a named hypothesis. All of them have the same
form: *every* read of that kind in this run returns the stated value.

| Boundary | Says | Used by |
| --- | --- | --- |
| `EnvDefines … declName v` | every `getConstInfo declName` of the run returns a definition whose value is `v` | every entry endpoint |
| `EntryDefines … declName v` | the constant the entry hands on — `entryConst` of the declaration and the environment the run reads — is a definition with value `v`. For a gate-accepted declaration this IS `EnvDefines` (`EntryDefines.of_env`); for an unfolded one it is `EnvDefines` plus what the run's environment unfolds the value to (`EntryDefines.of_inline`) | `_of_entry` endpoints (helper-structured declarations) |
| `MachineDefines … declName shape` | the entry constant of the declaration — `entryConst` of the declaration and the environment the run reads — is refused by both shape gates and IS the machine `shape` (`machineShape?`, with the structure facts — field accessors, constructors and field kinds: `structEnv` — of the environment the run reads). The suite computes the same `machineShape?` on the real declaration and compares binders, layout and (reflected) body | machine endpoints (`synthesizeCombinationalCore_machine_sound`, `mThree_execution`, `lin_execution`) |
| `MachineCloses … declName shape` | every machine synthesis of `shape` in this run ties the `let` ports to their fields (`closeLets` accepts the transition module the run compiled: the operand wires are found, declared at the ports' widths, and the statements are in dependency order), so the run does not fall back to the legacy route. PROVED for a shape without `let`s (`machineCloses_of_noLets`); for a shape with `let`s the suite runs the real `synthesizeMachineCertified` and checks it returns a module | machine endpoints of shapes with `let`s (`lin_execution`) |
| the declaration's type is one scalar Signal (`mixedGateResultScalar`) | `EnvDefines` pins the value, not the type; the suite checks it on the real declaration | instance and cone endpoints |
| tag fact at the entry (`RunsTo getEnv … → isHardwareModule e mn`) | the environment the gate predicate is built from tags the child | instance, projection and cone endpoints |
| `HardwareTagged mn` | every environment the instance arm reads tags `mn` | instance contracts |
| `SubSynthDefines mn mc dc` | the nested child synthesis the arm performs returns `(mc, dc)` | root instance contracts |
| `SubSynthDefinesAll mn mc dc` | the same at every recursion fuel (inside a cone the arm runs below the entry fuel) | cone-leaf contract |
| `ProjEnvDefines pn structName cn` | the projection function is not itself tagged, is a projection of `structName`, and the record call's head is tagged | projection contract |
| `ProjFieldDefines pn structName field` | the arm's field-name resolution returns `field` | projection contract |
| `OutCacheEmpty` | every read of the multi-output port map comes back empty | projection contract |

Not boundaries any more: the single-out instance cache (a hit is honoured
only when the builder's own `translateRecord` names the same expression,
so no premise about the mutable cache is needed), and the expression
cache (validated the same way since S2). `OutCacheEmpty` is stronger
than what the projection arm needs — it only queries the keys of the
call at hand — and is false when the child itself instantiates
multi-output modules; narrowing it to those keys is open.

## 2b. Applying the general theorems to a real compile: what remains

Each shipping theorem quantifies over every run of the compiler; using it
on a particular compile leaves exactly these, per kind (the measurement
reports them in separate fields, `Tools.ShippingPremiseEval.Verdict`):

| Kind | What | Status on a real compile |
| --- | --- | --- |
| module premises | the route's bundled checker (`shipsHierCheck`, `shipsHierHCheck`), the child bound (`kidsMaskedN`, `kidsMasked`/`kidsMem`, `hierTyped`), boundary facts (`extendsAwayB`, `noInstOfB`, `kidsComb`) | EVALUATED on the run's modules; each checker has a soundness lemma (`…_sound`). The evaluation is a run of the checker on the compile's output, not a kernel proof about that particular run |
| derived facts | the core body's linked well-formedness (`linkedOk_eq` from `MachineWired`), a memory call's instance is the built memory module (`MachineWired`, from the compiler's own `memSelf` check, `find_memModule`), the shipped module keeps the inputs (`checkedOptimize_inputs`) | PROVED from the run (`RunsTo`) — no premise; memory instances are cross-checked by the evaluator, and a memory-reads-only parent needs no run boundary (`TRACE:NOTREQUIRED`); its remaining memory-route conditions are `kidsMem` (evaluated) and `ResetM` (use condition) |
| run boundaries | `MachineRun` / `MachineRunN` / `GateRun` (an instance's module is a run of its child's entry), `SubSynthDefines` | PREMISES. The measurement TRACES them by compiling the child again and comparing modules (`TRACE:MATCHED`) — a measurement, not a proof. With calls of several different children the call–instance correspondence is not reconstructed (`TRACE:UNTRACED`) |
| use conditions | inputs within the declared and emitted widths, the children starting at reset (`Reset1`/`ResetM`/`ResetNk`), start registers within widths | the CALLER's obligations: statements about the environment the circuit runs in, not about the compile |
| reflection | `MachineDefines` / `MachineCloses` / `EntryDefines` (the declaration's value is the reified source) | checked per declaration by the endpoint generator's kernel `rfl`s (§6e); Stage 3 (proving the shape reader) would reduce it to the reflection principle |
| printer | the SystemVerilog text of the emitted objects | trusted (§6c) |
| children's text | the children's own emitted Verilog under the parent (the parent's Verilog runs against an ORACLE for the children's outputs) | not connected except one-level `flatKS` (`design_sv_run`) |

**Deriving the run boundary (investigation, 2026-10-09).** The child
modules a parent's compile uses come from `sparkleChildSynth` — an `IO.Ref`
holding the entry function (it breaks the mutual recursion between the
front end and the entry) — memoised in `sparkleChildCache`. Two facts are
missing in the logic: which function the ref holds, and that the cache holds
only results of real child runs. A design that would DERIVE `MachineRun` /
`GateRun` from the parent's `RunsTo`: (1) a run-environment boundary of the
existing form for the ref (`ChildSynthIs`: every read of `sparkleChildSynth`
returns the real `Rec.synthesizeCombinational`), discharged once per
session the way `EnvDefines` is; (2) a state invariant `CacheSound` (every
cache entry `(c, r)` is the result of a run of the child entry on `c`),
proved preserved by each write of the cache (the only writer is the
memoised entry, which stores the result it just computed); (3) a
`RunsTo` decomposition through `mapM` and the memoised call. Then the
boundary becomes a theorem about the parent's run, leaving the ref's
content as the single boundary.

**Call level DERIVED (2026-10-09).** `Tools/ShippingChildSynth.lean`.
`ChildSynthIs ctx`: every read of `sparkleChildSynth` in the parent's
contexts returns a function whose runs on a declaration `c` return results
of the real entry `synthesizeCombinational c` in the same contexts. It packs
(1) the ref's content, (2) the equation of the memoised child entry
`Rec.synthesizeCombinational` and (3) the soundness of its cache
`sparkleChildCache` into ONE session-level boundary, because none of the
three is a theorem in the logic: `Rec.synthesizeCombinational` is a
`partial def` (an opaque constant), and the ref and the cache are `IO.Ref`s
whose contents across worlds are opaque — `CacheSound` cannot be proved
separately, only assumed. From it, `machine_children_real` DERIVES for the
module and design the parent's real core entry returned (under its
`MachineDefines` / `MachineCloses`): they are `CloseCalls` of the transition
with children that are, CALL BY CALL, the built memory module or a
real-entry result on the call's declaration (`ChildrenReal`), through
`closeInstsM_runs` / `closeInstsGM_runs` / `synthesizeMachineCertified_runs`
(the `RunsTo` decompositions keep the contexts). Kernel-checked, standard
axioms (`Tests/Compiler/ShippingChildSynthTest.lean`).

**What stands between that and the boundary premises.** The generated
premises `BoundaryOf c` / `BoundaryOfN c` are predicates of `(m, dsn)`
alone, and `InstOfCall body mc k` does NOT bind the call index: `connsG`
reads only the outputs' field names, so the `k` of `∃ e ∈ outs, e.1 = k` is
free. Hence `BoundaryOf c` asks EVERY instance module of the body to be a
run of `c` — FALSE for a parent with two different sequential children
(`mixD1`) or with a sequential child and a memory call. The evaluator now
evaluates the premise as stated, over every instance (`TRACE:MISMATCH`, not
applying; previously `UNTRACED` for several children, and a memory
instance next to one sequential child was not looked at). The binding of a
call to its instance exists only in the run: on the general closing
`closeInstsG` CHECKS `moduleByName d.modules c.1.name = some c.1` for every
child (`closeInstsG_names`), so the instance whose output wires are call
`k`'s ports (`portNames[nIn + k]`) is `children[k].1`; but the port names
come from the run's fresh variables and wire cache, not from `(m, dsn)`. The
exact boundary must therefore be stated inside the run's existential (with
`MachineWired`'s names) and derived there from `ChildSynthIs`.

**Instance level DERIVED for the composed theorem (2026-10-09).**
`closeInstsG_serves` (`Tools/ShippingChildServe.lean`): on the general
closing, an instance statement one of whose output connections is call
`k`'s port has as its module (resolved by name) `children[k].1` — from the
closing's own checks (distinct port names, every child resolving to
itself). `synthesizeMachineCertified_soundX` (the one-cycle proof,
generalized with a fact `X` of the run's binder ids and wire cache, proved
beside `MachineWired` from `machPorts … = t.inputs`; the old theorem is its
`X = True` instance) and `Tools/ShippingMachineTraceX.lean` carry `X` through
the endpoint's layers with the SAME ids (`machine_traceX`,
`machine_ref_traceX`, `machine_endpointX`, `MachineTraceLBX`), instantiated by
`ServedReal` — the instance serving call `k` is the built memory module or
a real-entry result on `k`'s declaration — under `ChildSynthIs`
(`synthesizeCombinationalCore_machine_soundR`,
`machine_trace_lets_of_streamBR`). `machine_linkedT_callsR`
(`Tools/ShippingMachineCallsLinkedTR.lean`) composes a parent with memory
and sequential children from it: its per-call premise is the CHILD's own
theorem for runs of its entry (`SeqFactsR`) and the children's reflection
facts in the parent's contexts; no premise about the parent's instances
(`InstOfCall` / `BoundaryOf` do not occur). `machine_linkedT` was split into
`machine_linkedT_of` (explicit ids) so the binding is not lost to a second
existential.

**Through the shipping chain, depth 0 (2026-10-09).** `machine_ships_hier`'s
run boundary `Bnd` takes the run's contexts (`CtxBnd`; the existing
boundaries are `ctxFree`), and `compose` instantiates it at the shipping
theorem's own context binders, so `ships_design_svN`/`_all` are unchanged.
`#machine_design_svR0 f` (`Tools/ShippingMachineSeqCommandR.lean`) builds
`f.machine_composedTR` (the `R` endpoint heads of
`Tools/ShippingMachineSeqLinkedR.lean` + `machine_linkedT_callsR`; per call the
child's `c.seq_child_run` on any run of its entry), `f.machine_ships_hierR`
(its `Bnd`: `ChildSynthIs` ∧ the children's reflection facts, in the run's
contexts) and the source → closed emitted texts endpoint
`f.machine_design_svR0` (existence ∧ every closed run). Kernel-checked on
`parent` (one sequential child), `chained` (the same child twice), `two`
(two DIFFERENT sequential children) and `seqMem` (a sequential child next to
a memory read); their types mention `ChildSynthIs`, `MachineDefines`,
`MachineCloses`, `designCheck`, `outsCheck`, and none of `BoundaryOf`,
`InstOfCall`, `MachineRun`, `GateRun`, `MachineRunN`; their decidable
premises hold on the shipped designs; for `two` / `seqMem` the old
premise is MISMATCH (`Tests/Compiler/ShippingChildBoundaryTest.lean`). A
parent mixing sequential and memory calls needed a child bound accepting
both: `kidsMixed` (instance by instance `kidsMasked` or `kidsMem`, invariant
`mixInv`, `mixKS_boundedIn`, `reset1_mixInv`) replaces `kidsMasked` on the
sequential route (it is implied by `kidsMasked`: no parent is lost).
What the boundary IS now: `ChildSynthIs ctx` — every read of
`sparkleChildSynth` returns a function each of whose runs on `c` returns a
result of `synthesizeCombinational c` in the same contexts. That ASSUMES
the child's returned module is a result of the real entry (the ref's content,
the memoised child entry's equation AND its cache's soundness), not merely
that the ref points at the right function: it is a moved boundary, not a
proved `CacheSound`. To close it later: make the child entry total (fuel)
or state `CacheSound` as an explicit invariant of the cache across the
writes of `Rec.synthesizeCombinational`, and the ref's content as the only
assumption.

**At depth (2026-10-09).** `machine_linkedT_callsRN`
(`Tools/ShippingMachineCallsLinkedTNR.lean`; `machine_linkedTG` split into
`machine_linkedTG_of`) and `#machine_design_svNR f n`
(`Tools/ShippingMachineDepthCommandR.lean`): the per-child premise is a
predicate of the CHILD — for a child without calls its reflection facts (its
instance is then a `MachineRun`), for a child with calls that every run of its
entry in the parent's contexts satisfies its depth conditions (`MachineRunN`:
its reflection, its own boundary, `ExtendsAway`, `NoInstOf` — a statement
over the child's runs, true of a deterministic entry, where the old
`BoundaryOfN` was a statement over the parent's instances and false for
different children). Kernel-checked: `mixD1` (two DIFFERENT children, one
with calls) at depth 1, `grandH` at depth 1, `topD2` at depth 2. Below the
top level the children's OWN boundaries are still the generated old ones:
`midH.machineBoundN0` is the combinational `BndH` (its `rcH` call through the
one-output closing, whose instance level is not derived), and `topD2`'s
grandchild level keeps `mid2.machineBoundN1`'s `BoundaryOfN` (exact there —
one child kind — but not derived); the test checks this by unfolding those
definitions. **One-output closing (2026-10-09).** `closeInsts` did not check that a
child resolves by its name in the merged design to itself (`designWith`
keeps the FIRST module of a name, which may be a sibling's or a grandchild's),
so its instance level could not be derived from the run. It now CHECKS it,
as `closeInstsG` does (`Sparkle/IR/Machine.lean`). Effect on the success
domain: a one-output parent whose child's name resolves to another module
is no longer certified (falls back to the legacy route) — such a parent's
instance computed a module other than its call's child. Measured: the full
test suite (`Tests.AllTests`, 806 jobs, every certified one-output parent's
endpoint regenerated) — no parent lost; the corpus is not re-measured (the
full-corpus run stays stopped). `closeInsts_serves`
(`Tools/ShippingChildServe.lean`): the instance that is call `k`'s statement
(`CallStmt`) has module `children[k].1`. This is the check plus its lemma,
then (same day) the derived boundary of the combinational route:
`ServedReal` gained the one-output clause (`ServedReal1`, from
`closeInsts_serves`); `machine_linked` split into `machine_linked_of`;
`machine_linked_callsR` (`Tools/ShippingMachineComposeR.lean`) discharges each
call's `ChildFn` from the run witness `ServedReal` gives and the child's own
theorem on that run, concluding `ComposedH` with the trivial calls' premise;
`machine_ships_hierH` / `ships_design_svH(_all)` take a run boundary `Bnd`
(existing endpoints: `True`); `#machine_design_svHR f`
(`Tools/ShippingMachineComposeRCommand.lean`) — kernel-checked for `caller`
and `midH`, boundary `ChildSynthIs` ∧ the children's `EntryDefines`, types
free of `GateRun` / `MachineRun` / `BoundH` / `BndH` / `ChildFn` (checked
through the generated definitions). Only the `data_ext` endpoint head has its
R twin (nested / tele heads: not yet).

**Below the top level, from the actual run (2026-10-10).** The depth
variant no longer assumes that every run of a child's entry satisfies
`MachineRunN`. `machineRunNC_of_real` (`Tools/ShippingMachineDepthRunR.lean`)
derives `MachineRunNC` (`MachineRunN` with the child's boundary in the run's
contexts) from the run the parent's compile USED — the witness `ServedReal`
now carries together with that run's design's consistency with the
parent's — : the core run under it (`synthesizeCombinational_design`: the
full entry changes only the modules named after the top), the child's own
closing (`closeInsts_acyclic` / `closeInstsG_acyclic`: neither the child's
module nor its design instantiates it) and the parent's closing (every module
of the child's design resolves in the parent's design to itself) give
`ExtendsAway` and `NoInstOf`; the child's boundary is again `ChildSynthIs`
and reflection facts — facts of the contexts only, so the actual run needs
no identification. A child with one-output calls reaches depth 0 through
`composedN0_of_HR` (`Tools/ShippingMachineDepthHR.lean`; `kidsComb` of its
run from its closing, `BoundH` trivial). `#machine_design_svNR` now builds
the children's derived theorems recursively (`generateRunOfR`,
`generateCombN0R`); for `mixD1`, `grandH` and `topD2` the endpoint's types,
UNFOLDED through the generated definitions, contain no `BoundaryOf`,
`BoundaryOfN`, `InstOfCall`, `BndH`, `BoundH`, `GateRun`, `MachineRun`,
`MachineRunN(C)`: their boundary is `ChildSynthIs` and the reflection facts
of every descendant (the grandchild `rcH`'s `EntryDefines` among them).
The compiler's closings check more for this (`Sparkle/IR/Machine.lean`,
`MachineInstG.lean`): no instance of the module being closed in it or in its
design (`noInstOfB`); on the one-output closing, every module of a child's
design resolves to itself, and the children are combinational, local and
wired (`kidsCombB`). Each new check rejects only compiles whose certified
route would have wired or composed incorrectly; a rejected closing returns
`none` and the entry takes the legacy route. Measured on `Tests.AllTests`
(811 jobs, no certified parent lost) and by
`Tests/Compiler/ShippingCloseInstsCheckTest.lean` on `caller`'s real
transition and child: the actual design accepted with the instance being the
child; a different module under the child's name rejected; an identical one
accepted; a design module instantiating the closed module rejected; a child
with a register rejected by `kidsCombB`. The corpus is not re-measured.

**Depth is an upper bound (2026-10-10).** `composedNWn_of_H` /
`composedNn_of_HR` (`Tools/ShippingMachineDepthHR.lean`): a parent whose
children are combinational runs the same at every depth — at depth `n` an
assignment-only child steps by its assignments (`KSn_assigns_step`), so its
outputs are those of the combinational step (`runModuleTG_KSn_of_H`).
`generateRunOfR` lifts such a child to the depth its parent uses (no longer
depth 0 only). Kernel-checked: `grandH` at depth 2 (midH deeper than it
needs), `mixD1` at 2, `topD2` at 3, and `mixDeep` at 2 — a deep branch
`mid2 → midH → rcH`, a shallow `midH → rcH` and a leaf `cnt` under one
parent; `mixDeep` at depth 1 is refused (its deep branch is too shallow).

**Nested and tele endpoint heads (2026-10-10).** `machine_traceL_of_nested_extR`
(`Tools/ShippingMachineNestR.lean`) and `machine_traceL_of_tele_extR`
(`Tools/ShippingMachineTeleNestR.lean`): the heads' own proofs, the stream
lemma replaced by `machine_trace_lets_of_streamBR`. `#machine_design_svHR`
picks the head of the declaration's endpoint (`headsOf`). Kernel-checked and
audited unfolded: `callerNested`, `callerLN` (nested), `hftByte` (tele, its
child the real `httpGetByte`), `callerMix` (two different combinational
children), `callerTwice`, `callerD`, `callerL`; decidable premises true on
every shipped design.

**What the new closing checks cost (2026-10-10, measured).** Only conjuncts
were added to the closings' acceptance; when a closing accepts, its output is
unchanged. The checks fall in two kinds. Miswiring prevention: every child
(and every module of a child's design) resolves by its name to itself, and
nothing in the closed module or its design instantiates the module being
closed — a rejection there is a compile whose instance would have computed
another module. Proof alignment: `kidsCombB` on the one-output closing (its
children combinational, local, wired) — what that closing's composition
takes of its children; it can only shrink the certified route, so it is not
counted as generality. Measured with the closing of 12e84834 against the
current one on the same inputs (`scripts/shipping-coverage/closing_compare.lean`):
all 28 machine declarations with calls of the test modules imported by
`ShippingChildBoundaryTest` (11 one-output, 17 general closings) are accepted
by both — nothing moved to the legacy route. A one-output call of a
SEQUENTIAL child (`useCtr1`) was never certified: the old closing refuses its
instance (`instStmt`: no clock/reset child), so the machine route returns
`none` and the real entry succeeds on the legacy route
(`ShippingCloseInstsCheckTest`); the legacy route's output is not covered by
the certified theorems. The corpus is not re-measured. Still to connect: the derived boundary recursively below the
top level (`MachineRunN` with a context-dependent boundary), the depth-`n`
variant's remaining items (`MachineRunN`; its `ExtendsAway` /
`NoInstOf` remain evaluated checks on the child's run), and the
one-output closing `closeInsts`, which does not check that a child resolves
to itself (its instance level is not derived).

## 3. Premises about a linked child

The hierarchical statements speak about a parent whose instance
statements are executed against a table of children. Three premises are
about that table, not about the run:

- `children mc.name = some (mc, cwe)`: the table holds the pinned child
  under its module name. The suite checks `d.modules` on the real
  compiles; deriving the registration from the run is open, and needs a
  no-collision fact about module names (they come from declaration
  names).
- `ChildCorrect mn mc cwe out`: the pinned child's body computes the
  child's source function. A statement about one fixed module — proved
  outright for the test child; in general it is the child's own
  certified endpoint.
- `ChildOutsBounded children mems`: each child output fits its port
  width. Likewise a fact about fixed modules.

## 4. Decidable gates evaluated by the suite

Several theorems take decidable premises about the pipeline's artifacts.
The division of labour is deliberate: a theorem quantifies over any
artifacts satisfying the premise; a `throwError` gate in the suite
evaluates the premise on what the pipeline actually produced in this
build. A gate failure fails `Tests.AllTests`.

| Gate | Validates | Evaluated on |
| --- | --- | --- |
| `seqOptCheck m o` | the sequential merge and the optimizer on assign/register bodies | every certified register shape |
| `optCheck (openFlat m …) (openFlat o …)`, `instsKept`, `connAgreeOk` | the optimizer on instance-bearing bodies (interface extraction) | three hierarchical parents |
| `seqCheck` / `seqCheckM`, width agreement | the emitted-SV semantic layer applies | register, memory and hierarchical capstones |
| `semFragCheck`, `bodyImage`, `bodyReorderCheck`, fragment membership of the parsed body | the parsed-back text is the checked module up to reordering; the gates run the REAL parser on the REAL printed bytes | the same capstones |
| `linkedWF`, `instOutWidthsOk` | the linked/open bridge applies; instance outputs sit at their port widths | hierarchical capstones |
| post-processing identity (`mFull.body = mr.body`) | cleanup and merge leave the certified body unchanged | memory shapes, hierarchical parent |
| byte parity with the legacy front end | the certified front end emits exactly what the legacy one does | every family, including instances, projections, cones and pipelines |
| pinned child modules (`cm == childModule`) | the literal module a premise names IS the compiled child, name included | hierarchy tests |

`checkedOptimize` itself only checks assignment-only bodies whose
right-hand sides are all of a known shape (`simpleBody`): there the
optimised module ships only if the proved checker accepts it, and the
unoptimised input ships otherwise — which is always the case for a body
containing a part-select or a concatenation of two wires, since the
checker's normal form covers neither. On an assignment-only body with
an unknown right-hand side (a wider concatenation, a general slice
operand), and on
memories and instances the shipping pipeline keeps the optimizer's
output unchecked at run time. For those shapes the validation is exactly
the gates above: an optimizer change that broke one would fail the suite
rather than silently ship, but a compile the suite never ran is not
checked. On ASSIGN + REGISTER modules IN THE NORMAL FORMS
(`RefineCheck.seqGate` and `refineCheck m m`: every output and next
value normalises over the inputs and registers) both the duplicate merge
of the full entry (`mergeChecked`) and the optimizer (`checkedOptimize`)
are checked at run time by `refineCheck`, proved sound
(`refineCheck_transfer`): the merged / optimised module ships only if
accepted, the unmerged / unoptimised one otherwise. For these modules the
printed text is therefore a proved refinement of the core module in EVERY
compile, not only the suite's. A sequential module outside the normal
forms (legacy modules whose assigns reference wires defined later, forms
the normaliser does not know) keeps the unchecked passes, so the gate
changes no emitted text there.

## 5. Definitions that carry the meaning

The theorems relate these definitions. They are specifications, not
theorems, and reading them is part of trusting the claim.

- The source: `Signal`, its operators, and `Signal.val` at a cycle.
- The front-end unfolding: `inlineDefs` / `userInliner` (delta-beta of
  user definitions, projection of a constructor, zeta in front of it,
  `<$>`/`<*>` at the library's Signal instances as `Signal.map`/
  `Signal.ap`, literal `Nat` sums folded — `8 + 4` in a type argument
  becomes `12`) and the choice `entryConst`. The theorems do not reason about the unfolding — they
  speak about the value the entry constant HAS. That this value means
  what the declaration means is Lean's own delta/beta, and it is checked
  per declaration by the kernel: the test theorems identify the
  declaration, helpers and all, with the denotation of the quoted
  unfolded term by `rfl` (`useSel_library`, `oddParity_library`,
  `rcon_library`). Which definitions are
  unfolded (`userDefinition?`) only decides which declarations reach a
  certified front end; a wrong choice there cannot make a theorem false.
- The normal forms of the machine route: `machNorm` (other spellings of
  accepted hardware rewritten to the accepted one) and `kernelNat`, which
  reads the value of a constant computed in Lean with the kernel's own
  reduction (`Lean.Kernel.whnf` on a closed `Nat` term). Like the
  unfolding, they are not reasoned about: the theorems speak about the
  transition the run computed. That the normalised transition means what
  the declaration AS WRITTEN means is checked per declaration by the
  kernel — the generated endpoint compares the written body with the
  terms read off the normalised one (`f.machine_writes`,
  `f.machine_result`), and a constant with its literal by evaluating
  both. A wrong rewrite or a wrong value therefore cannot make a theorem
  false; without the endpoint of a declaration, its module rests on the
  rewrite rules being right, as with every dispatch arm.
- The IR semantics: `evalExpr`, `evalAssigns`, `stepModule`,
  `runModule` (`Sparkle/IR/Semantics.lean`). Instance statements are
  no-ops here: the open-module view.
- The linked meaning of an instance: `evalAssignsH` — the child's
  outputs are the standard evaluation of its body on the
  connection-fed environment, one level deep — and its order-free form
  `Consistent` (each instance's outputs equal its child's evaluation on
  what the instance reads). That this is what a SystemVerilog module
  instantiation means is retained. Its width side condition is no
  longer retained: every emitted instance is checked, and proved, to
  join equal widths (`instLinkCheck`, `Linked`, `InstsLinked`).
- The syntax view `view` (`Tools/ShippingUnifiedMeaning.lean`): which
  Lean expression counts as which operator node. It maps the
  applicative form `Signal.ap (Signal.map (fun x y => op x y) a) b` to
  the node of `op` on `a` and `b` — the pointwise reading of `<$>`/`<*>`
  on `Signal`; the kernel `rfl` bridge of each declaration checks that
  reading against the library's definitions. Likewise a `Signal.map`
  whose function is `BitVec.extractLsb' start len` is the slice node,
  with `BitVec.extractLsb'` itself as its meaning (`fc_library`), and
  `a ++ b` at the library's Signal instance is the concatenation node,
  with `BitVec` append as its meaning (`cSwap_library`).
- The emitted-SV semantics (`Tools/SVParser/EmitSem.lean`): continuous
  assignments, the always-block register shape, memories. An
  independent reading of the SystemVerilog subset the printer emits.
- The reader: the shipping parser and lowering
  (`Tools/SVParser/Parser.lean`, `Lower.lean`). The byte-level
  statements run in the PARSE direction — the module read back from
  the printed text is proved trace-equal to the checked module — so the
  parser is trusted as a reader of text. Combinational modules also
  have the render direction (`printedModule_render`); for sequential
  text it is blocked on the SV AST, whose sensitivity lists cannot
  carry an asynchronous reset.

## 6. What the hierarchical statements do and do not say

For a hierarchical parent the printed-text statements are in the
open-module view under the ORACLE SEEDING: instance-output wires start
at the values the linked semantics gives them, and `Consistent` says
those values are the children's. This is a statement about the PARENT
module's text. Not yet covered: the design-level text (children printed
alongside the parent), children that are themselves sequential (the
bridge is combinational; the per-cycle linked run `runH` is proved only
at the IR level), and children that themselves instantiate.

## 6b. What the machine statements do and do not say

A machine endpoint is about the module `synthesizeCombinationalCore`
returns (the raw module), run by the IR semantics with RESET LOW from a
state in which the registers hold the slots' values: every cycle's output
port (`out`, or one port per field of a structure result) is the source
declaration's value at that time. Reset behaviour itself
is not modelled (as for the single-register family): the registers'
reset VALUES and reset KIND (synchronous in `defaultDomain`,
asynchronous for a domain binder) are emitted by `closeMachine` and
checked on the emitted module by the suite, not proved against a source
semantics of reset. The unfolding and the reading of the transition
(`userInliner`, `machineShape?`) are not reasoned about either: the
theorems speak about the shape the run computed (`MachineDefines`), and
that this transition means what the SOURCE means is proved per
declaration by the kernel — the source's state recurrence
(`circuit_state`) against the evaluation of the quoted term; for a shape
with hardware `let`s the declaration also proves that the source's own
`let` values satisfy the transition's `let` equations (`LetsHold`).
For a GENERATED endpoint (`#machine_endpoint f`, `f.machine_sound`) the
same holds with nothing written by hand, and nothing added to the base:
the command's reader of the body (`unq`) and its construction of the
data are not trusted — the kernel checks that the body is the quotation
of the terms (`f.machine_body`), evaluates the one Boolean that decides
every side condition (`f.machine_ok`; by reduction, not `native_decide`),
and checks by `Eq.refl` that the declaration's own reset values, pending
writes and result are the terms' (`f.machine_inits`, `f.machine_writes`,
`f.machine_result`, `f.machine_source`). A declaration with sub-machines
goes through `machine_trace_of_nested` instead: the same checks, with the
enclosing body written over the tuple of the sub-machines' results and
each sub-machine's body over the enclosing handles (both read off the
declaration and checked by the kernel: the declaration IS that body on
the loops, `f.machine_source`); the generic fact that the loops together
are the flattened machine's state stream is proved (`fused_state`,
ShippingMachineFuse), not assumed. A declaration whose body CALLS a
combinational `@[hardware_module]` is a machine whose transition reads the
call's output as an input and whose emitted module ties that input to an
INSTANCE of the child (`closeInsts`); its `f.machine_sound` is stated with
the inputs at the calls' positions being the calls themselves over the
state loop (`MachineTraceWith`), and the kernel checks per call that the
call is pointwise in the state (`f.machine_inst_k`). What this theorem
takes as a hypothesis — the seed constraint at the call's position — is
that the instance's output wire carries the call's value at every cycle;
the flat semantics the theorem is stated in treats an instance as a no-op
(the open-module view of `Sparkle.IR.Semantics`). Discharging that
hypothesis for the real module is the child's own theorem (its module
computes its source function) composed through the linked semantics
(`evalAssignsH`, S6 `linked_open`). For machine modules the composition is
now PROVED generically (`Tools.ShippingMachineCompose.machine_linked`: the
linked run, each instance evaluated by the module its name resolves to in
the shipped design, seeded with the declaration's own inputs, shows the
source — given that each call's module computes a function `F k` of its
argument ports and the source's call is `F k` of its arguments), and the
child side is proved for combinational machine-route children
(`Tools.ShippingMachineChild.childFn_of_trace`, `childFn_full`). It is
generated per declaration (`#machine_linked f` → `f.machine_linked`,
`#machine_child c` → `c.machine_child`); two premises remain stated rather
than proved: the design's child module is
the child's own full-entry run (the child synthesizer is an opaque
`IO.Ref`, as S6's `SubSynthDefines`), and the run-module gate
`dropZeroWidthModule raw = raw` of the child.
This gap is not cosmetic: the open-module theorems cannot see WHICH wires an
instance connects, and a real miscompile lived there — `closeInstsM` found
the call's output and argument wires by BINDER position, so in a
domain-polymorphic declaration (the domain binder has no port) the instance
was wired one position off. It is fixed (the offset now counts ports;
regression `callerD` in ShippingMachineInstTest checks the instance drives
its own `_gen_inst` wire and reads only its argument wires); the entry
theorem now quantifies over the offset, and the linked composition is what
will rule out this class for good.
Declarations are added with
synchronous kernel checking and the theorem's axioms are audited, so a
failed check cannot leave a constant behind. The command also runs the
machine synthesis once and requires that it ties the `let`s — evidence
for the boundary `MachineCloses` in the environment of the check, not a
proof of it for another run. The
optimizer and the printer after the core entry ARE composed for machine
modules, up to the emitted-Verilog semantics: `f.machine_ships`
(`machine_ships_full`) states the same conclusion for the module the full
entry returns after `optimizeModule` and for its emitted Verilog
(`EmitSem.runModuleSV`), under gates that are decidable facts about the
modules of the run — `refineCheck raw b` (cleanup and duplicate merge),
`refineCheck b o` (optimizer), the reset port, the output ports,
`EmitSem.seqCheck` and its width agreement. `refineCheck` is proved sound
(`refineCheck_transfer`); the gates are evaluated by the suite on thirteen
declarations and by `scripts/shipping-coverage/pipeline.sh` on the corpus
(107 of 113 hold). Since the compiler checks the merge and the
optimizer itself (`mergeChecked`, `checkedOptimize`; `machine_ships_checked`),
`f.machine_ships` no longer needs `refineCheck` as a premise: what remains
are structural facts about the run's modules (no zero-width wire, the
assign + register shape, the normal forms of the core and merged modules
— `refineCheck m m`, the condition under which the compiler's gate binds
— the reset and output ports) and the emitted-Verilog check of the printed
module; they hold for 107 of 113
machine-route declarations. The module parsed back from the printed bytes
is not covered for machine modules.

**From the wiring (2026-10-08).** `f.machine_ships_wired`
(`Tools.ShippingMachineShipsW.machine_ships_wired`) discharges the
structural gates for a register machine from its WIRED endpoint
(`machine_traceL_of_data`): the zero-width cleanup is the identity
(`MachineWired`), a body with a register is merged only if `refineCheck`
accepts it (`mergeChecked_nonAssign`), an assign + register body is
optimized only if `refineCheck` accepts it (`checkedOptimize_seqOk`), the
reset and output ports are facts. Its premises are only the emitted-Verilog
check of the printed module (`EmitSem.seqCheck` and width agreement) and
that the body is not of the simple combinational shape. The generator emits
it for every register machine proved by `machine_trace_of_data`,
`_of_loop`, `_of_regs`, `_of_nested` or `_of_tele_ext` on the declaration
itself (their wired forms `machine_traceL_of_data`,
`Tools.ShippingMachineLoopL`, `machine_traceL_of_tele_ext` take the same
arguments); after a sign-normalisation / fusion transport too (the
theorem is built for the rewritten value and moved to the declaration's
source by the same `Eq.mpr` as `f.machine_sound`); not for instances. It is optional — a failure leaves
`f.machine_sound`/`f.machine_ships` as they were. Suite: 13 of 13
`circuit do` declarations, 8 of 8 hand-written loops, 5 of 5 sub-machine
nests, 3 of 4 telescopes. Corpus (partial: 38 of 184 files before the run
was stopped for memory): 27 of 84 endpoints.

**Combinational machines (2026-10-08).** `f.machine_ships_comb`
(`Tools.ShippingMachineShipsComb.machine_ships_comb`) is the same for a
machine without slots or calls: its module is assignments only (a
`MachineWired` clause), the full entry's merge is the self-validating
`mergeDuplicates` (the same environment), `checkedOptimize` keeps the
optimizer's output only when `optCheck` accepts it (the same outputs), and
the emitted Verilog runs as the module (`seq_run_to_sv`). Its statement
(`MachineShipsComb`) seeds every cycle with the inputs and the reset name
low (`seedR`: a combinational module has no reset port). Remaining premises:
the shipped body is of the simple shape and the emitted-Verilog check.
Suite: 4 of 4, and 6 of 6 sign-normalised (transported) endpoints.

**The optimizer on instance-bearing modules, checked at compile time
(2026-10-08).** `checkedOptimize` used to pass an instance-bearing module's
optimizer output to the printer UNCHECKED (the optimizer inlines connection
values into instance ports: `decoderPipeline` 530 → 175 statements). Now,
where the extracted interface is in the normal forms (`hierBinds`), the
output has its connections named again (`Sparkle.IR.HierCheck.deinline`)
and is kept only if `hierRefineCheck` accepts it: the same instance
statements both ways (`instsKept`), every connection validated or untouched
(`connAgreeOk`), and `refineCheck` on the extracted pair (`openFlat`:
instances dropped, instance-driven wires as inputs, instance-read wires as
outputs); else the module ships unoptimised. Measured (gold62): every
status identical; 21 output files differ, every difference an instance
connection that reads a named wire again (`assign w = …;` plus its `logic`
declaration). The check also requires that `o` drives no extracted input,
and the extraction classifies registers as driven (`drivesOf`).
PROVED (`Tools.ShippingHierOptRun.hierRefineCheck_linked`): when the check
accepts, every run of the STATEFUL linked semantics of the module
(`runModuleTG`, any child step `KS` that reads the parent only through its
input connections) has a run of the shipped module from the same state with
the same outputs — the linked run is an open run of the extracted module
(`linked_open_run`, from `linked_openKG`), `refineCheck_transfer` carries it
to the extracted optimized module, and that open run is a linked run of the
optimized module with the children stepping as before (`open_linked_run`,
from `linked_consistentKG` and `runModuleTG_of_open`). Premises: the
design's (linked-well-formed bodies, distinct instance names, no instance
reading its own output, the instance-driven wires among the extracted
inputs — evaluated on four real modules in
`Tests/Compiler/ShippingHierOptRunTest.lean`), inputs fitting their widths
with reset low, instance outputs and start register values fitting their
widths.

**Machines with instances, to the shipped module (2026-10-08).**
`Tools.ShippingMachineShipsHier.machine_ships_hier` carries a composed
theorem (the core module's stateful linked run shows the source) through the
full entry — the cleanup is the identity, and the checked merge is the
identity on an instance-bearing body (`mergeChecked_inst`: its validator
keeps assignments as assignments, `refineCheck` rejects instance
statements) — and the optimizer (`hierRefineCheck_linked`): the SHIPPED
module's stateful linked run shows the source. Its module premises are one
checker, `shipsHierCheck` (`Tools/ShippingHierPremisesBase.lean`, proved sound:
`shipsHierCheck_sound`); the core body's linked well-formedness is derived
from the wiring (`linkedOk_eq`). It is general in the child
step `KS`, the children's reset and the run boundary; `composedG_of_T`
instantiates it with the one-level composed theorem (`runModuleT` is
`runModuleTG flatKS` on memory-free bodies). Generated by
`#machine_ships_hier f` (`Tools/ShippingMachineShipsHierCommand.lean`) as
`f.machine_ships_hier`: 5 of 5 suite machines with sequential children
(`parent`, `chained`, `engineOnce`, `twinCalls`, `mesh2x2`), 3 of 3 suite
memory parents (`composedG_of_Tmem`, reset = memories and read latches
zero) and the corpus memory parent `quantModule` (H.264), their module
premises (the optimizer check binds, linked-well-formed bodies, distinct
instance names, no instance reading its own output, instance-driven wires
extracted, instance-output widths, a reset port) evaluated on the real
modules. Remaining premises: the run boundary per sequential child
(`BoundaryOf`, as for the composed theorem), inputs and start values within
their widths, and the children's outputs within their ports' widths — for
sequential children a decidable check (`kidsMasked`: no memory, every output
port assigned once by a self-masked expression no wider than the port;
`flatKS_boundedIn`), evaluated on the real modules; for memory children
the check `kidsMem` (every child the built memory module, no connection
naming its read latch) with the read-latch invariant `memInv` (zero at
reset, `resetM_inv`; a combinational read and a latched read are masked at
the data width; `memKS_boundedIn`). Found on the way: `deinline` named a
connection wire before EVERY instance reading it (two memory instances
sharing a write-enable wire got two assignments of it, which the linked
semantics' well-formedness rejects); it now names a wire once. The shipped module's EMITTED VERILOG: `Tools.ShippingHierSVRun.linked_sv_run`
— a stateful linked run of a module is the run of its emitted Verilog
(`runModuleSV`) from the oracle seeding, its instance outputs at each cycle
the values its children drove (`linked_open_runG`, then `seq_run_to_svI`),
under the emitted-SV check and width agreement of the shipped module
(evaluated on the five real shipped modules); `linked_sv_of_run` derives
the oracle seeding's bound from decidable facts of the shipped module (its
children's bound check, instance-output widths, instance-driven wires
extracted and no wider than emitted — evaluated on all eight shipped
machines with children) and the inputs and start state within the emitter's
widths. And the DESIGN:
`design_sv_run` — along that run (one-level children, `flatKS`), the
emitted Verilog of every instance's child, fed at each cycle with the run's
values on its input connections, runs to environments whose output ports
carry exactly the oracle values the parent's emitted Verilog was given
(`child_run_of_linked` + `seq_run_to_sv`): the emitted texts of parent and
children, connected, run as the linked run. The children's emitted-SV
premises are evaluated on the real children. OPEN: the boundedness
premises of the SV seedings (instance outputs, connection-fed child inputs)
discharged from widths, transported endpoints, depth > 1.

**Stateful composition with children (2026-10-08).** For a machine whose
calls are memory reads and/or sequential machine children (`closeInstsG`),
`f.machine_composedT` states the STATEFUL linked run (`runModuleT`,
`runModuleTG` at depth `n`: each instance steps its own child module with
its own registers and memories) of the emitted module. Its premises beyond
the machine endpoint's: (1) the run boundary per sequential child
(`BoundaryOf`: the module an instance of its calls resolves to is a run of
the full entry on the child — the child synthesizer is an `IO.Ref`, opaque
in the logic, as `SubSynthDefines`); memory children need none (the compiler
builds the memory module and checks that its name finds it); (2) the
children start from RESET (memories and sync-read latches zero, registers at
their reset values: `ResetN`); (3) the top seed holds reset and clock low.
Proved, not assumed: that the instance's connections feed the child exactly
its argument wires (`connsG`, `seq_inst_run`), the child's module at the
full entry (zero-width cleanup kept — now PROVED for every machine module,
with or without instances, so the run-module gate `dropZeroWidthModule raw =
raw` above is discharged; the merge is `refineCheck`-accepted or absent —
`mergeChecked` no longer ships an unchecked merge), and that the merged
design finds every child module and every module of a child's design as
itself (checked by the compiler with the IR's decidable equality). Children
that themselves have children are covered by the depth-`n` theorems up to
the links listed in the TODO (F6).

**Children with children (depth, 2026-10-08).** `#machine_composedN f n`
(`Tools/ShippingMachineDepthCommand.lean`) composes a machine whose
sequential children have children of their own: a child with calls holds at
depth `n + 1` from its own composed theorem at depth `n`
(`seqChildRunN_of_composed`), under the hierarchical run boundary
`MachineRunN` (the instance's module is the full entry's post-processing of
a core run of the child whose design the parent's extends away from the
child's own name, which no module instantiates); `#machine_ships_hierN f n`
carries it to the shipped module (`machine_ships_hier` with `KSn`, the
children's bound from the decidable `kidsMaskedN`, `KSn_boundedIn`).
`grand → mid → cnt`: composed and shipped at depth 1, its module premises
evaluated. COMBINATIONAL children inside a sequential child
(`Tools/ShippingMachineDepthH.lean`, the Keccak sponge's shape: `wKeccakF`
calls the round-constant table), three parts kept apart:
  - *General lemmas (proved).* For grandchildren that are assignments only,
    local and fully wired (the checker `kidsComb`), the child's
    combinational linked run IS its depth-0 `flatKS` run
    (`runModuleTG_flat_of_H`), so `composedNW0_of_H` / `composedN0_of_H`
    give the child's `ComposedNW 0` from its composed theorem under the
    boundary `BndH R f d = BoundH ∧ kidsComb`. `BoundH` is stated by the
    actual call–instance correspondence: under the module's wiring
    (`MachineWired`, which `machine_linked` and the gate composition now
    carry with the same ids) only the instance serving call `k` (`CallStmt`)
    must satisfy `R k`; `BoundH_of_each` is the sufficient condition without
    the wiring, exact for calls of one child. The child body's linked
    well-formedness is derived from its wiring (`linkedOk_eq`), not assumed.
    `MachineWired`'s port clause is unconditional (closeInsts too), so
    `calls_ports` / `seqChildRunN_of_composed` no longer need call groups.
  - *Small example, premises evaluated (`Tests/Compiler/ShippingMachineDepthHTest.lean`,
    `grandH → midH → rcH`).* `grandH.machine_ships_hierN1` is generated, and
    every premise it states is evaluated on the real compile
    (`Tools.ShippingPremiseEval.evalShipsHierSeq`): `shipsHierCheck` and
    `kidsMaskedN` hold; the boundary is traced — `midH`'s instance module is
    the post-processing of a core run of `midH` (`MachineRunN`, the modules
    compared), `ExtendsAway` / `NoInstOf` hold (`extendsAwayB`,
    `noInstOfB`), `rcH`'s instance module in `midH`'s design is `rcH`'s
    full-entry run, `kidsComb` holds; the parent's emitted-Verilog premises
    of `shipped_sv` hold. Remaining premises, listed not evaluated: the
    reflection boundary (`MachineDefines`/`MachineCloses` of `grandH`,
    `midH`; `EntryDefines` of `rcH`), the children starting at reset
    (`ResetNk`), inputs and start registers within their widths; the
    sub-synthesis boundary itself (the compiler's child synthesis is an
    `IO.Ref`, so `MachineRunN`/`GateRun` stay premises — traced, not
    proved). A rejected premise is reported, not counted (`grand` at depth
    0: `NOPREM`, and its depth-0 theorem is not generated).
  - *Real Keccak sponge: not completed.* Generation inside the measurement
    exceeded the 1500 s per-file limit; an unbounded run was stopped for
    memory. UNMEASURED.
  Remaining: memory children below depth 1, combinational grandchildren
  below depth 1, the precise `BoundH` evaluated for calls of several
  children (only its one-child sufficient condition is evaluated), the
  children's emitted Verilog at depth ≥ 1.

**Machines with combinational children, to the shipped module
(2026-10-08).** For a machine whose calls are one-output combinational
children (`closeInsts`; the gate compiles the child, or the machine route
without slots), the composed theorem `f.machine_composed` states the
combinational linked run `runModuleH` of the core module, given that each
call's module is its child's full-entry run (`GateRun` / `MachineRun`).
`Tools.ShippingMachineShipsHierH.machine_ships_hierH` carries it through the
full entry and the optimizer: `hierRefineCheck_linkedH` (the instance gate
over `runModuleH`; it needs each child to compute from its input ports,
`kidsLocal`) — the SHIPPED module's linked run shows the source, under the
same per-call premise. The extracted inputs of the optimizer check (the
instance-driven wires) must fit their widths; a gate-compiled child drives
its output by an alias (`out = _gen_out`, a mux over its inputs), which the
syntactic mask check `kidsMasked` cannot see, so the bound comes from a
WIDTH-TYPED run instead (`Tools/ShippingHierTyped.lean`): every assignment
reads no output port and has the width of what it writes, each child output
is assigned once by an expression no wider than the port, instance inputs
read parent wires no wider than the child's ports and outputs drive wires at
least as wide — then every value of the linked run off the output ports
fits its declared width (`evalAssigns_typed`, `evalAssignsH_typed`,
`runModuleH_typed`; register updates are masked) and the extracted inputs
fit (`fitX_of_typed`). The check `hierTyped` is decidable; on the real
modules only the output-port aliases fail the plain `bodyWidthOk` (output
ports are not declared wires). Generated by `#machine_ships_hierH f`
(`Tools/ShippingMachineShipsHierHCommand.lean`): the six suite machines
(`callerL`, `callerLN`, `caller`, `callerTwice`, `callerNested`, `callerD`),
module premises evaluated, every optimizer output accepted. MEASURED on the
corpus (the 11 files holding the gold64 `machine_composed` declarations):
26 of 26 machines with combinational children reach the shipped module,
their module premises (the optimizer check binds, linked-well-formed,
distinct instance names, `kidsLocal`, no self-read, instance-driven wires
extracted, `hierTyped`, a reset port) evaluated true on all 26 — the
crypto wrappers (`wKeccakF`, SHA-512 block), the network byte machines
(ARP, ICMP, HTTP, IPv4, HFT strategy), PCIe HFT and the iverilog tops.
The shipped module's EMITTED VERILOG:
`Tools.ShippingHierSVRunH.linked_sv_of_runH` — a combinational child is
the stateless step `combKS` (its assignments on the connection-fed
environment), a `runModuleH` run with local children IS a `runModuleTG
combKS` run with the same environments (`runModuleTG_of_H`: `runModuleH`
feeds a child every connection, the stateful step only the inputs, and a
local child's outputs cannot tell), so `linked_sv_run` applies, its oracle
seeding bounded by the width-typed run; its premises (the shipped module
width-typed with local children, instance-driven wires extracted and no
wider than emitted, the instance/assign/register fragment, the
emitted-Verilog check, width agreement) evaluated on the six suite
machines and in the corpus measurement (`sv*` tags): all 26 corpus
machines satisfy every premise to the emitted Verilog. 10 of them (ARP /
ICMP / IPv4 responders, PCIe HFT, `wKeccakF`) were first rejected by the
emitted-Verilog check: `(x << 8) & mask` with `x` as wide as the node shifts
bits out, and the literal-shift rule `SF4.bitwiseShl` demands no overflow
(its parent's context may be wider). New rule `SF4.bitwiseShlW`: when the
bitwise sibling is EXACTLY as wide as `x` (amount no wider), the parent's
context is the shift's own width, so the emitted text cuts the shifted-out
bits where the IR's mask does — proved in `emit_sem`, admitted by
`shlSideOK`. The compiler does not run `seqCheck`, so no output changes. The
same rule closes the corpus' remaining emitted-Verilog rejections of the
register-machine pipeline measurement (`pipeline.sh`; the PCIe / TCP /
Ethernet parsers, NAL stream, dividers — 22 declarations rejected in
gold52): re-measured on their 8 files, none fails the emitted-Verilog
check any more.

**Loop children and transported parents (2026-10-08).** A sequential
child proved by `machine_trace_of_loop` / `_of_regs` (a `Signal.loop`, the
issue-107 toggle) gets its `seq_child_run` from the wired twin of that head
(same conclusion form as `machine_traceL_of_data`). `machine_ships_hier`
takes the wired endpoint for the cleanup facts only, with its own source,
so a TRANSPORTED parent (fused / sign-normalised source; the composed
theorem is already transported) ships too: `loopParent` and the fused
memory parent `withMemory` in `Tests/Compiler/ShippingMachineSeqLoopTest.lean`.

**The whole design's emitted texts, at any depth (2026-10-09).**
`Tools.ShippingDesignSV`. `DesignSV C n o seed T s envs` is a RELATION on
the emitted texts (it embeds no IR run): `o`'s text runs from the oracle
seeding built from `envs` to `envs`; every instance resolves in the design
`C` (`Resolved`); every connection joins a parent wire and a child port of
the same emitted width (`PortsMatch`); and each instance's child — looked up
in `C`, from the instance's OWN state `s.kids iname`, fed at each cycle with
that cycle's values on its input connections (`connSeed`) — runs to
environments whose output ports carry the values of the wires the instance
drives at the same cycle (`Supplies`): at depth 0 the child's own text, the
child FLAT (`seqStmtOk`: no instance, so no output left to an oracle); at
depth `n + 1`, `DesignSV C n` of the child. A design deeper than `n` cannot
satisfy it (its depth-0 leaves would have instances).
`design_sv_runN ms n` (C = `childMap ms`): an IR linked run at depth `n`
(`runModuleTG (KSn C n)`), the decidable `designCheck C n` (each level's
emitted-text checks, linked well-formedness, distinct instance names, no
self-read, `PortsMatch`, every instance resolved; leaves flat and accepted)
and the width premises `SVBounds` give `DesignSV` with the SAME
environments. `child_runKS_of_linked` is the generic step (any local child
step; `child_run_of_linked` was its `flatKS` case). Exactly what it is: a
FORWARD SIMULATION — the IR run is a closed run of the texts. It does NOT
say the connected texts admit no other run: uniqueness (the relation
determines `envs` from the seed and the states) is not proved. It is
expected from the linked order — each instance's inputs are computed before
its outputs are read (`linkedWF`, no self-read), the parent's text and each
child's text are deterministic functions — but that argument is open.
Measured: `designCheck` holds on the shipped designs of `grandH` (depth 1),
`topD2 → mid2 → midH → rcH` (depth 2, `topD2.machine_ships_hierN2`) and
`mixD1` (two different sequential children), and is rejected one level
shallower. The evaluator's `SVCHILD:CHECKED` means exactly this: the
structural `designCheck` holds, so the CONDITIONAL forward theorem
`design_sv_runN` applies given `SVBounds`; `SVBounds` is not derived and the
link from the source theorem to `DesignSV` is not made — it is not a
complete closed statement and is never counted as one (the depth-0
sequential route is `KSn _ 0 = flatKS`; the combinational route through
`runModuleTG_flat_of_H` when `kidsComb` holds). The memory route's step is
ALSO `flatKS` (`composedG_of_Tmem`, `memKS_boundedIn`); its memory
children's TEXTS are now connected too (memory leaves, below). What still stands between
`grandH` and a closed SV statement: (1) `SVBounds` — each level's seeding
and start state within its emitted widths along the IR run (a run premise;
its parts: the instance outputs within the emitted widths, the children's
inputs from the parent's wires, the start registers of every instance);
(2) the run boundaries (`MachineRunN`, `GateRun`: traced, not proved);
(3) the reflection boundary; (4) the use conditions (inputs, reset);
(5) the printer. Uniqueness of the closed run is a separate open item.

**Source → the closed emitted texts (2026-10-09).** The width premises are
DERIVED (`Tools/ShippingDesignSVBounds.lean`, `svBounds_of_checks`), for any
finite depth, from `designCheck` alone plus the use conditions — the top
seeding within the emitted widths (inputs), the start state within them, and
every instance's start state within its own (`InvN`). No step assumes the
bound it proves: inside each cycle the fold follows the linked order
(`evalAssignsKG_envBound`: an assignment's value fits its target by
`seqCheck` + `sf4_bounded`, an instance's outputs fit the driven wires by
`PortsMatch` because its inputs were already bounded), a child's step is
bounded by induction on the depth (`KSn_stepBound`, `moduleStepBound`;
leaves by `emit_sem_assigns` and masked register updates), and the run
cycle by cycle (`runModuleTG_envBound`). `ships_design_svN`
(`Tools/ShippingShipsDesignSV.lean`) composes the shipping theorem's own run
(same design `D`, same shipped module `checkedOptimize b`, same seeding
`seedIn b ins`) with `svBounds_of_checks` and `design_sv_runN`;
`#machine_design_svN f n` instantiates it: `grandH.machine_design_svN1` and
`topD2.machine_design_svN2` are kernel-checked (standard axioms), for every
run of the compiler, every input sequence and every length. Their exact
premises: the real full entry's run (`RunsTo`), the reflection boundary
(`MachineDefines`, `MachineCloses`), the module checker `shipsHierCheck`,
the design checker `designCheck`, the child bound `kidsMaskedN`, the run
boundary `machineBoundN{n}` (child core runs: traced, not proved), and the
use conditions (source inputs on the seed, reset low, start registers at
their reset values, children at reset `ResetNk`, inputs within the declared
and emitted widths, start state and instance states within their widths);
conclusion: `DesignSV` of the shipped design with those environments, whose
output ports carry the source's values. Stages recorded apart by the
evaluator: `SVCHILD:CHECKED` (structure checked only), `SVCHILD:SOURCE`
(the kernel-checked endpoint above exists). The depth-0 route
(`#machine_design_sv0`: `machine_ships_hier` has `KS = flatKS = KSn _ 0`;
the theorem's own reset / boundary / bound read off its proof term) and the
combinational route (`ships_design_svH`, `#machine_design_svH`: the
`runModuleH` run is the depth-0 `flatKS` run under `kidsComb` on the shipped
body, `runModuleTG_flat_of_H`) have endpoints too: `parent.machine_design_sv0`,
`caller.machine_design_svH`. Memory parents: see the memory leaves below. Still not
claimed: the run boundary as a theorem, `mixD1`'s call–instance
correspondence (traced: UNTRACED).

**Memory leaves (2026-10-09).** `Tools/ShippingDesignSVLeaf.lean`,
`Tools/ShippingDesignSVMem.lean`. A depth-0 child of `DesignSV` runs as
`LeafRun`: without a synchronously-read memory its text runs by
`runModuleSV` (combinational reads are its `.reads` steps, `seqCheck`); with
one, by `runModuleSVM`, the read latches among its sequential drivers
(`seqCheckM`, `mem_run_to_sv` / `forward_trace_mem_inv`). `leafCheck`
(assign / register / memory statements, memory write operands plain
references, checker and emitter widths agreeing on the names the IR step
consults — `leafNames`: a plain-reference operand consults no width — and
the emitted-text check of its kind) gives the four facts every design
theorem uses: `leaf_forward` (IR run ⇒ text run), `leaf_backward` (text run
⇒ IR run), `leaf_stepBound` (one step within the emitted widths) and
`leaf_outs` (outputs within their widths in ANY text run). No width
condition is placed on the memory contents or the initial memory: every read
is masked at the data width (`comboReadsSV`, read latches), and a read port's
target is at least that wide (`readPortsCheck`: `emitAssigns_readsOK`), so
`evalAssignsSV_written` bounds every assigned or combinationally-read name
whatever the inputs and the memory hold. `outsCheck`'s leaf predicate is
`outsLeaf` (each output assigned or a combinational read target; it extends
`outsAssigned`); a synchronous read latch driving an output DIRECTLY is not
covered (`outsLeaf` false, so not AT-MOST-ONE). The read latch's start value
is part of the instance's start state (`InvN`: within its width).
`leafCheck_memModule` / `outsLeaf_memModule`: the built memory module
`memModule cb aw dw` passes both for EVERY read kind and widths, and
`designCheck_memKids`: a parent whose instances are all built memory modules
has `designCheck 0` = its own `textCheckI`, and `outsCheck 0`. The forward
(`design_sv_runN`), bounds (`KSn_stepBound`), backward (`design_sv_backN`)
and all-runs (`design_sv_all`) theorems use the leaf facts at depth 0, so the
memory parents' generated endpoints apply: `memCounter`, `twoMems`,
`mixedMems` (combinational AND synchronous children), `memWide` (aw 6 /
dw 16), `syncNarrow` (aw 3 / dw 5) are `SVCHILD:SOURCE` and
`CLOSED:AT-MOST-ONE` with `designCheck` and `outsCheck` evaluated true on the
shipped module (`Tests/Compiler/ShippingDesignSVMemTest.lean`; a false
premise is never counted: SOURCE is derived from `designCheck`, not from the
endpoint's existence). The memory module's IR run, its emitted text's run
and an independent reference model agree over multi-cycle read/write
schedules (7 read-kind/width pairs, past an address wrap). Kept rejected:
non-reference write operands, a read target narrower than the data, a leaf
mixing combinational and synchronous reads, an instance in a leaf; `outsLeaf`
rejects an unwritten output and a latch-driven output.

**The closed run is unique: backward simulation (2026-10-09).**
`Tools/ShippingDesignSVBack.lean`. `design_sv_backN ms n`: under
`designCheck` and `outsCheck` (every child, at every level, assigns each of
its output ports), from a seeding and states within the emitted widths
(top seed, start state, `InvN`), EVERY closed run of the emitted texts
(`DesignSV … envs`) is the IR linked run (`runModuleTG (KSn _ n) … = some
envs`). No bound is assumed of the solution: the texts' semantics masks
every assignment at its target's declared width (`evalAssignsSV`), so a
child's assigned outputs are within their widths whatever its inputs
(`runModuleSV_assigned`); the parent's instance-output wires carry exactly
those values (`Supplies`, `PortsMatch`); then every environment of the
parent's text is within its widths (`runModuleSV_bounded`), the text runs
as the IR open run (`forward_trace_invI`), each child's text as its IR run
(depth induction), and the open run with the children supplying their
outputs is the linked run (`runModuleTG_of_childRuns`). Hence
`design_sv_unique` (two closed runs from the same seeding and states are the
same list of environments — every name, not only the ports: the text's run
is a function of its seeding) and `design_sv_all` (what one closed run shows
— the source's values, from `ships_design_svN` — every closed run shows).
Uniqueness alone says AT MOST ONE: that a closed run EXISTS is the forward
theorem's, given a successful IR run and its premises — in the endpoints,
the source shipping theorem's run. The generated endpoints
(`#machine_design_svN` / `_sv0` / `_svH`, now built on
`ships_design_svN_all` / `ships_design_svH_all`) state both, with
`outsCheck` explicit: a closed run showing the source exists, AND every
closed run from the same seeding and states shows it. The evaluator's
`CLOSED:AT-MOST-ONE` (designCheck + outsCheck hold) is that structural
guarantee under the seeding / state width preconditions — not a discharge
of the run boundary or the use conditions, and separate from
`SVCHILD:SOURCE` and the traces (grandH, topD2, parent, caller).

## 6c. The printer (the CompCert framing, F3)

CompCert's guarantee ends at its assembly AST; the printer that turns it
into text is trusted. Sparkle's guarantee is framed the same way, with the
FORWARD direction primary:

- **Proved (forward):** the shipped module's emitted SystemVerilog objects
  — the continuous assignments, register always-blocks and memory writes
  `EmitSem.emitAssigns` / `emitRegs` / `emitMemWrites` build from the
  shipped IR — run under the SV semantics (`runModuleSV`) as the source
  (`seq_run_to_sv`, `machine_ships*`, `linked_sv_run`, `design_sv_run`).
  This needs no parser.
- **Trusted (printer):** that the bytes `Sparkle.Backend.Verilog.toVerilog`
  / `toVerilogDesign` print are the SystemVerilog those objects denote —
  the module header, declarations, and the printing of each object. It is
  the analogue of CompCert's assembly printer.
- **Validated (parse-back), not trusted:** where the suite runs it, the
  printed bytes are read back by the shipping parser and the result is
  checked against the shipped module (`semFragCheck`, `bodyImage`,
  `bodyReorderCheck`, §4), and for those modules the parsed-back text is
  proved trace-equal to the checked module. This direction trusts the
  reader instead of the printer; it is a validation of the printer on the
  checked corpus, not the primary claim.

A verified printer with a proven inverse on the emitted sub-language would
remove the printer from this list; it is not planned.

## 6d. `partial def`s on the shipping path (F4 audit, 2026-10-08)

A `partial def` has no unfolding equations, so no theorem can look inside
one. Each that a compile of a certified or machine-route declaration
reaches is covered as follows — none is relied on unchecked:

| `partial def`s | Where | Covered by |
| --- | --- | --- |
| `machConv`, `machNested`, `machChain`, `machLoopBody`, `machLoopRoot`, `machInstance(S)`, `machLiftScalarN`, `machBoolMap`, `machNorm` (Elab); `rootFloat`, `zetaAll`, `projChain`, `prodMatcherArity?` (MachRawSurface); `packTupleInputs` (MachTupleIn) | reading a declaration into a machine shape | the boundary `MachineDefines` (§2) and, per declaration, the kernel `Eq.refl` checks of the generated endpoint against the declaration's own value (`machine_body`, `machine_writes`, `machine_result`, `machine_source`) — translation validation |
| `passM`, `iota`, `reduceHead`, `betaAll`, `listLit?`, `relevantClosure`, `headBetaM` (MachRecUnfold), `canonHardwareExpr`, `stripMemoizeWrappers`, `openRecordInputs`, `splitReturnLeaves` (Elab) | the front end's unfolding / normalisation | the same per-declaration kernel checks (`EntryDefines`/`MachineDefines` name the result; the endpoint's `rfl`s tie it to the declaration) |
| `optimizeExpr`, `substituteExpr`, `resolveSlice`, `inferWidth`, … (Optimize); `canonExpr` (RegDedup) | the optimizer and the duplicate merge | compile-time result checks: `optCheck`, `refineCheck`, `hierRefineCheck`, `validateMerge` (proved sound); an unchecked result only where no gate binds, and the shipping theorems then require the gate (§4) |
| the mutual `synthesizeCombinational` (child synthesis with `sparkleChildCache`) | a child compiled inside a parent's synthesis | the run boundary per child (`SubSynthDefines`, `BoundaryOf`, §2–3); the theorems are about the total top-level `synthesizeCombinational` |
| `translateExprToWireImpl` and the `handle*` arms | the legacy front end | outside every theorem (§7); the certified knot is the total fuel-bounded `translateExprToWire` |
| `emitDimExpr` and the printer (Backend/Verilog) | bytes | trusted printer (§6c) |
| the parser / lowering (`Tools/SVParser`) | reading bytes back | validation only (§6c) |
| `Type.evaluate`, `specializeType/Expr` | parameterized synthesis | outside every theorem (§7) |

## 6e. Universality (F1, stage 1 — decided 2026-10-08)

CompCert's theorem is universal over Clight ASTs; the text-to-AST step is
validated per program. Sparkle's claim is framed the same way:

- **Universal (proved once):** the compiler-correctness theorems quantify
  over EVERY reified source (`MachineData` with `d.ok`; the unified `Term`
  of the gate route) and over EVERY run of the real compiler
  (`RunsTo (synthesizeCombinationalCore …)`, `RunsTo (synthesizeCombinational …)`):
  `machine_trace_of_data` / `_of_loop` / `_of_regs` / `_of_nested` /
  `_of_tele_ext` / `_of_comb`, `machine_ships_wired`, `machine_ships_comb`,
  `machine_ships_hier`, `translateExprToWire_sound`,
  `execution_source_of_env`.
- **Per declaration (validated reflection):** that the declaration's Lean
  value IS the reified source — the kernel `Eq.refl` checks the endpoint
  generator emits (`machine_body`, `machine_writes`, `machine_result`,
  `machine_source`, …) and the boundary `MachineDefines` / `EntryDefines`
  (§2). This is the analogue of CompCert's validated parser; the generator
  that produces these checks is unverified meta-code, but every check it
  emits is checked by the kernel.
- **Monitored:** a successful compile without a kernel-checked endpoint
  would be outside the claim. The corpus measurement counts them
  (`scripts/shipping-coverage/endpoints.sh`). Numbers carry their scope:
  - gold53 (run.sh pass 1): legacy-only 0 of 391 real declarations; every
    machine-route declaration with an endpoint.
  - gold64 (compiler at `a97e608`, endpoint tools at `68c7fb0`,
    2026-10-08): 367 of 367 machine-route declarations IN THE FILES THAT
    FINISHED have a kernel-checked endpoint (327 real corpus); 8 files did
    not finish within the 1500 s per-file limit and are UNMEASURED, not
    counted: `Tests/AllTests.lean`, `IP/Video/H264/MP4EncoderSynth.lean`,
    `Tests/Compiler/ShippingMachineCommandTest.lean`,
    `Tests/IP/Crypto/{EcdsaSignDemo,P256SignDemo,PolicySignDemoM2,PolicySignDemo}Test.lean`,
    `Tests/IP/USB/Fido2DemoTest.lean`. Of the 367, 185 reach the emitted
    Verilog from the wiring (`machine_ships_wired`), 44 as combinational
    machines (`machine_ships_comb`). Machines with children: 18 of 21
    `machine_ships_hier` GENERATED in gold64 (the 3 others transported
    endpoints, generated since); at that revision generation was counted,
    not the premises.
  - Focused re-measurements after gold64 (the 11 files holding the
    `machine_composed` declarations, `b1a3a19` and earlier): 26 of 26
    machines with combinational children have `machine_ships_hierH`
    generated, their premises true and the parent's emitted-Verilog
    premises true. The Keccak sponge files (`Tests/IP/Crypto/Keccak256Sponge{,JIT}Test.lean`)
    did not finish (timeout at 1500 s, then an unbounded run stopped for
    memory): UNMEASURED.
  - From `endpoints.sh` after this revision, every shipping theorem of a
    machine with instances is recorded field by field
    (`Tools.ShippingPremiseEval.measure`, details in `premise_items.txt`):
    `GEN:OK` / `GEN:EXISTS` (already generated: generation skipped, the
    premises still evaluated) / `GEN:FAIL`; `MOD:PREM` / `MOD:NOPREM:<which>`
    / `MOD:UNKNOWN:<which>`; `TRACE:MATCHED` / `TRACE:UNTRACED` /
    `TRACE:MISMATCH` (run boundaries measured, not proved) /
    `TRACE:NOTREQUIRED` (the route needs no run boundary beyond facts
    derived from the run: memory reads); `SV:PARENT` / `SV:NO` (the
    parent's emitted Verilog); `SVCHILD:OPEN`. A theorem counts as APPLYING
    GIVEN ITS RUN-BOUNDARY PREMISES only with `MOD:PREM` and
    `TRACE:MATCHED`/`NOTREQUIRED` — a matching trace measures those premises,
    it does not discharge them; an empty or unevaluated verdict is never
    success. The depth-0 route (sequential children: `Reset1`/`kidsMasked`;
    memory reads only: `ResetM`/`kidsMem`) is one function, `hierRoute`,
    used by the generator and the evaluator alike, so the bound evaluated is
    the bound of the theorem generated. Files that do not finish are
    listed as unmeasured with their exit status.

Stage 3 (planned) strengthens the reflection: the shape readers
(`machineShape?` and its `partial` helpers, §6d) rewritten total and
proved — `read succeeds ⇒ the declaration's expression is quote(shape)
∧ d.ok` — leaving only the reflection principle (a constant's value is its
expression) per declaration.

## 7. What is outside every theorem

- **Compiles on the legacy route.** Every compile goes one of three ways,
  and the guarantee differs by route and by stage:

  | route | taken when | theorem | stage reached |
  | --- | --- | --- | --- |
  | certified gate | `certifiedShape?` / `mixedCertifiedShape?` accepts | `translateExprToWire_sound`, `execution_source_of_env`, the S3–S7 families | core RTL; shipped / emitted text per family (S7) |
  | machine route | the declaration reads as a `MachineShape` (circuit do, loops, registers, calls) | `f.machine_sound` (generated per declaration, kernel-checked) | core module trace; `machine_ships_wired` / `_comb` to the emitted Verilog; with instances `machine_ships_hier` / `H` / `N` to the shipped module, `shipped_sv` / `linked_sv_of_runH` to the parent's emitted Verilog under evaluated premises |
  | legacy | neither | none | — |

  On the measured corpus the legacy route is taken by 0 of 391 real
  declarations (gold53); the earlier statement here that "most real
  designs" compile outside every theorem predates the machine route and is
  withdrawn. What remains outside is (i) a compile on the legacy route,
  (ii) a machine-route declaration whose endpoint was not generated or whose
  file was not measured (§6e), (iii) a shipping theorem whose premises do
  not hold on the run (`NOPREM`), and (iv) the stages listed as open per
  route (§6b: children's emitted Verilog at depth ≥ 1 and for combinational
  children; memory children and combinational grandchildren below depth 1).
- **Legacy handlers reached from a certified compile.** A certified
  family's theorem covers its own quoted shape. A nested child
  synthesis is covered only through the child-side premises of §3.
- **Symbolic-width synthesis** (`#synthesizeParameterizedVerilog`) and
  specialization of parameterized designs.
- **Other back ends**: the C simulation, JIT and CUDA emitters, and
  the SystemVerilog import path as a front end.
- **A width-generic `@[hardware_module]`** is compiled once at a
  fallback width. Instantiating it at another width is refused by the
  width-linkage check (it used to miscompile); it is not specialized.

## 8. What is NOT retained

For the certified shapes the following are proved, not assumed: the
translation of the quoted source, including both validated caches; the
elaboration semantics of the emitted module against the source streams;
zero-width cleanup; the width linkage of every emitted instance; and,
where the gates of §4 hold, the merge and the optimizer, the emitted SV
objects' cycle semantics, and the trace of the parsed-back text.
