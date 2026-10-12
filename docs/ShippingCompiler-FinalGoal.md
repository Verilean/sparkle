# The final goal, its dependency graph, and who works on what

Fixed 2026-10-12 (base commit `9a9f812f`, branch `poc/roundtrip-proof`).
This file states the goal and the open dependencies. **It proves nothing**:
a goal definition is not a result. Status of each item is in
`ShippingCompiler-GeneralTheorem-Audit.md` §0; this file is the plan that
table is measured against.

## 1. The goal

> For every Signal-DSL source and every successful run of the real entry on
> it returning a design `D`: (1) the top module's outputs are, cycle by
> cycle, the source streams' values; (2) for every finite `T` a closed SV
> execution of length `T` exists from an admissible start; (3) every such
> execution has those outputs. The domain is every input the entry accepts
> today — not a subset.

### 1.1 What "for every source" means formally (corrected 2026-10-12)

An earlier version of this section said a Lean theorem "cannot" relate a
value expression to the function it denotes. That was an over-claim. Two
different things must be kept apart:

- **Possible in principle, and the way to state the goal:** a relation
  between source SYNTAX and meaning can be defined inside Lean — a deep
  embedding `S` of the source language with an evaluation `S.eval`, or a
  relation `Denotes : Lean.Expr → Meaning → Prop` defined by rules. A theorem
  can then quantify over every source in `S` (or every `e` with
  `Denotes e m`).
- **Not defined in the current base** (a missing definition, not an
  impossibility): such an `S` exists only for gate terms (`Term`, `quote`,
  `Tools/ShippingUnifiedSource`) and machines (`MachineData`: packed term +
  layout). For the syntax only the legacy route accepts there is none
  (work item SEM0).
- **What stays outside the kernel:** that a particular Lean CONSTANT `f`
  (a function of the meta-language) equals `S.eval s` for the syntax `s` the
  compiler read from `f`'s value. The kernel can check this per constant
  (`rfl` / a generated proof), but "for every constant in every environment"
  is a statement about the elaborator's environment, not a Lean proposition
  over a deep embedding. This is the reflection step.

So the goal is the conjunction of:

- **(GT) the general theorem, over deep sources.** For every source `s` of
  the deep embedding and every run of the entry on a declaration whose value
  is the quotation of `s`: (1)–(3) with `S.eval s` as the source.
  Quantified over all of `S`; no per-declaration data.
- **(GR) the reflection step, per declaration.** `f = S.eval s`, by `rfl` /
  a generated proof. Per declaration by nature; not a gap PROVIDED the proof
  exists for every accepted declaration.
- **(GC) coverage.** For every value `v` the entry accepts, `v` is the
  quotation of some `s` (G3a/G3b: reader soundness, data checks), AND the
  generator of the GR proof succeeds and terminates on it (G3c). G3c does
  NOT follow automatically from G3a + G3b: it also needs the generator's own
  totality and termination on every accepted input, which is a statement
  about a meta-program and is tracked separately (measured per corpus until
  it is a theorem about a total function).

### 1.2 The formal target with today's types

The shape of GT already exists per declaration:
`Tools.ShippingShipsDesignSVAll.ships_design_svH_all` /
`ships_design_svN_all` conclude, for a `MachineData d`, existence of a run
`runModuleH … T st0 mems = some envsO` with `envsO[j] o.name = (src …)[k] j`,
and that every SV run agrees. The target is that conclusion with:

- `d`, `src`, `ext` not parameters but *functions of the deep source*
  (`src = S.eval s`), for ALL `s`;
- premises restricted to: use conditions (input / start-state bounds,
  `rst = 0`, reset values), reflection (`EntryDefines` / `MachineDefines` of
  the declarations read), the runtime laws (`ChildBnd`, G5, conditional);
- NOT premises: `MachineClosesAt`, `designCheck`, `outsCheck`,
  `shipsHier(H)Check`, `kids*`, per-call source facts, name-separation
  facts, data checks (`ok`, `letsOk`, `letsAliasOk`, `callsOk`).

`Tools/ShippingFinalGoal.lean` holds this as `def … : Prop` for the routes
that have a deep source today (the machine route), so progress is "which
premises of the generated endpoints are gone" checked against a fixed type;
the legacy route's target is added when SEM0 exists (it is NOT postponed
for the machine route).

## 2. Dependency graph

```
                 GT ∧ GC  (final)
                    │
   ┌────────────────┼──────────────────────────┐
   │                │                          │
 machine route    legacy route             coverage
   │                │                          │
   ├─ CLOSE         ├─ SEM0 (deep source       ├─ G3a reader ⇒ quote image
   │   ├─ A (lets)  │    for legacy syntax)    ├─ G3b data checks hold of
   │   │   done     ├─ G2a contract            │     every reader output
   │   ├─ B1 done   ├─ G2b handlers meet it    └─ G3c generator total
   │   ├─ B2 done (no-call kids)                    (needs a+b AND the
   │   │                                             generator's totality)
   │   └─ B3 done (kids with registers; see audit §0)
   ├─ G1 output checks derived from the run (needs CLOSE's body facts)
   ├─ N1 names (independent; premise of every closed endpoint)
   ├─ G4a fuel monotone (independent)
   └─ G5 runtime laws (conditional by design; no dependency)
```

Dependencies that constrain parallel work:

- **B3 ← B2**: a child with calls is closed by `closeInstsG`; the child
  interface B2 fixes (`ChildIfaceG`) is what B3 must produce.
- **G1 ← CLOSE**: the checks are about the closed body; they use the same
  body facts (`closeMachine_body`, statement classification) B2 assembles.
  G1 starts after B2's assembly lands, on the machine route first.
- **G2 ← SEM0**: no legacy theorem can be stated before a deep source for
  legacy-accepted syntax exists. G2's first unit may use the existing
  `Meaning` layer where a legacy handler handles `Term`-quoted syntax.
- **G3b ← A, B**: "the data checks hold of every reader output" is exactly
  the premises A/B1/B2 take (`letsOk`, `callsOk`, …) and can only be stated
  against their final form.
- **N1** is independent of all three lines (pure `Name.toString` facts) —
  assigned to the first worker that frees up.
- **G3a** and **G2a** are independent of B2 and of each other.

## 3. Open items

| ID | Statement to prove (types) | Allowed premises | Files (owner) | Depends on | Accepted when |
|---|---|---|---|---|---|
| B2 | `MachineClosesAt … declName d.shape` for parents whose calls have several outputs or sequential children; via `closeInstsG_of_facts : … → (closeInstsG … (closeMachine lay t', d)).isSome` | the run's facts; child interface from the child's OWN run; data checks per declaration (G3b) ; N1 name facts | `Tools/Shipping*G.lean`, `ShippingCallGroups`, `ShippingInstNames` (integrator) | — | `parent` (child `cnt`) has a closed SV endpoint without `MachineClosesAt`; then `mixD1`, `grandH`, `topD2`, `mid2`, R0 parents |
| B3 | child interface for a machine child that has calls (non-empty design, instances in the body) | same | integrator, after B2 | B2 | `grand` (child `mid` calls `cnt`) closed |
| G3a | `reader v = some shape → shape.body = quote … term ∧ v = lambda-telescope of it` for `mixedGatePeel` / `machineShape?` | reflection only | `Tools/ShippingReader*.lean` (worker A) | — | one induction over the reader's recursion covering every node kind it accepts; the per-declaration `hbody`/`peel` premises of endpoints become consequences |
| G3b | `reader v = some shape → d.ok ∧ d.letsOk ∧ d.callsOk …` or a counter-example with the precise failing check | reflection only | worker A after G3a | A, B2 | each data check is a theorem or a recorded real refusal |
| SEM0 | a deep embedding + `eval` for the syntax the legacy translator accepts beyond `Term` | — (a definition; must agree with `Term.eval` on `quote`'s image, proved) | `Tools/ShippingLegacySem*.lean` (worker B) | — | defined, agreement lemma proved |
| G2a | the legacy step's simulation contract in `Contract`'s form | — | worker B | SEM0 for non-`Term` syntax | stated over existing types; composes with `unified_fuel_contract` |
| G2b | every legacy handler meets G2a | runtime laws | worker B | G2a | one theorem about `translateFallback`, handlers as cases; real fallback declarations get source endpoints |
| G1 | `designCheck`, `outsCheck`, `shipsHier(H)Check`, `kids*` hold of every machine-route output | the run | unassigned (next free worker) | B2 assembly | the checks leave the endpoints' premises |
| N1 | `Name.toString` separation facts used by closed endpoints | none | unassigned (next free worker) | — | name premises leave the closed endpoints |
| G4a | fuel monotonicity | none | unassigned | — | proved |
| G5 | runtime laws | — | stays conditional | — | not claimed |

## 4. Working rules

- **Workers** (max 3): integrator + B2; worker A (G3); worker B (SEM0/G2).
  Each in its own worktree on a branch (`par/g3-reader`, `par/g2-legacy`),
  new files only, base `9a9f812f`. Shared definitions, `lakefile.lean` and
  compiler files change only through the integrator, who announces the
  change to the workers.
- **Verification queue**: workers never start Lean. They hand over modules
  to build; the integrator runs them one at a time through
  `scripts/shipping-coverage/cgrun.sh` (3 GiB cap, swap 0, one job), on a
  frozen snapshot, and ties the result to a commit hash. A failure goes back
  to the worker; nothing is integrated unbuilt. `Tests.AllTests` runs at
  integration points only.
- **No** `sorry`, new axiom, `native_decide`, renamed-conclusion premise, or
  narrowing of what the entry accepts.
- **Progress** = open items of §3 closed, or premises removed from the
  generated endpoints (`scripts/shipping-coverage/endpoint_premises.lean`),
  not test counts.

## 5. Measurements (verification cost)

From the run records under `~/sparkle-work/runs/` (2026-10-12, B2 units):
single-module builds took 1–25 s wall time, cgroup peak 0.25–0.65 GiB of the
3 GiB cap, no `high` / `max` / OOM events, no timeouts; the queue was idle
between builds. Full `Tests.AllTests` (868 jobs) is the only long run. So
for unit work the rate-limiting step is **writing proofs**, not CPU or the
one-job queue: parallel authorship helps; a second concurrent Lean job would
not, and is not introduced. (Host: 4 cores, 7.8 GiB, ≈6.3 GiB available.)
To be re-measured at the first `AllTests` integration run.

## 6. Status log

- 2026-10-12, `704d44d5`. B2 closed for machine children without calls
  (`parent`, `chained`: closed depth SV endpoints). B3 next (integrator).
  G2: contract layer integrated, conditional on `ReachesInline`; worker B on a
  reproduction test for the unvalidated legacy cache and the dispatch walk.
  G3a: worker A's strict term reader (`readTerm_sound`) failed its first build
  (13 errors), returned with the log; finding to be confirmed by a run: the
  compiler's gate recognisers match some positions with wildcards, so
  "recogniser accepts ⟹ body is a quotation" is false as stated.
  `Tests.AllTests` 881 jobs green at `ffad8424` (8 s incremental, peak 0.42 GiB).
- 2026-10-12, `0aeb3e45`, `Tests.AllTests` 892 jobs green. B3 closed for
  children with registers (`grand`, `grandH`, `mixD1` without any closing
  premise; `topD2` keeps `mid2`'s). G3a: strict reader sound (18 kinds) and
  complete (11); reads 44 / 44 measured machine bodies; the wildcard gap of
  the compiler's recognisers confirmed by a run. G2: the legacy cache
  rollback defect reproduced with an injected fault. Workers: A on N1 (name
  separation), then `KindsOK` and completeness of the added kinds; B on a
  natural trigger for the cache defect, a reviewable fix patch, and the
  dispatch walk. Open decisions for the user: applying a compiler fix for the
  cache rollback; making the strict reader part of route acceptance.
- 2026-10-12, `3a291ec6`, `Tests.AllTests` 895 jobs green. N1: first-level
  name premises PROVED (11 closed parents keep only the child's reflection).
  G1: first unit (leaf machines' instance-only checks from every run) and an
  inventory of what is derivable / needs one optimizer lemma / is a real gap
  (the emitted-text checks). G3a: 18-kind reader complete, `KindsOK`
  unconditional. G2: five handler walks, the true statement of the unfold
  handler (inline attempt OR sub-module path); three walk files returned.
- 2026-10-12, `484a1267` (`Tests.AllTests` 936 jobs green on the tree of
  `627b5763`; `484a1267` adds one built module). **G1, first check removed
  from a real run:** `parent` and `chained` have depth SV endpoints without
  the `outsCheck` antecedent, generated per declaration (`#machine_no_outs`);
  the kernel-checked goal gap of `parent` (`#machine_goal_gap`) is three
  not-allowed premises: `shipsHierCheck`, `designCheck`, `kidsMaskedN`.
  `grandH` is refused with the reason (its child has calls). `kidsMaskedN`
  is BLOCKED on main: the checked merge may turn an output's defining slice
  into an alias, which `outMasked` rejects (`docs/parallel/G1-masked.md`); a
  guarded merge is being verified on the isolated branch `fix/merge-guards`
  (not merged; needs the user's word). **N1:** every generated closing keeps
  only reflections as premises; arbitrary `Name`s stay open (printing is not
  injective). **G2 (branch `fix/cache-rollback` only, not merged):** cache
  rollback fix verified in isolation; `useDbl_output` is a statement about a
  real fallback declaration with reflection premises and three outcomes
  (memo hit, the output carries `x + x`, input skipped) — the two side
  outcomes are not excluded. **G3:** strict reader is shadow-only by ruling;
  `app*` kinds read by levels (sound; completeness open); a well-typed
  wildcard counter-example exists, so recogniser acceptance does not imply a
  quotation. Rows B2/B3/N1 of §3 are superseded by this log: B2 done for
  children without calls, B3 done for children with registers (`topD2`
  keeps `mid2`'s closing), N1 done for generated names.
- 2026-10-12 (end), main `fdfb25f1`, `Tests.AllTests` 951 jobs green. Three
  ISOLATED branches carry everything below that changes the compiler; none is
  merged (each needs the user's word).
  **G1.** `shipsHierCheck` has eight conjuncts, none on emitted text. On main:
  conjuncts 3, 5, 6, 7, 8 and the gate half of 1 are derived from the core
  run (`Tools/ShippingChecks{Raw,Outs,Widths}`, `ShippingLinkedFresh`,
  `ShippingCallWidths`; instances on `parent` in `ChecksRawTest`), with two
  per-child facts taken from the real child's run (port names; the call
  width, a decidable data condition per parent/child pair). The rest of 1
  (`refineCheck` on the extracted interface) and 2, 4 (post-pass) are NOT
  derivable on main, so no endpoint on main lost the premise: the gap of
  `parent` is still shipsHierCheck, designCheck, kidsMaskedN. Measured on 29
  real instance parents: every conjunct holds on all 29.
  FINDINGS: (A) the width of a call port against the child's field is
  checked by no compiler pass; (B) `checkedOptimize`'s last `else o` ships
  the optimizer's output unchecked for an instance module on which
  `hierBinds` is false (taken 0 times on the 29).
  Branch `fix/opt-fallback-build` (`f6e6dded`, AllTests 960 green there):
  the input module is returned when the gate holds and the check does not
  bind, `deinline` is guarded (instance names distinct; a design-free
  linked-order check); neither guard fires on the 29. There
  `machine_ships_hierC_free` and the GENERATED depth SV endpoints of `parent`
  and `chained` have no `shipsHierCheck` and no `outsCheck`; their
  kernel-checked gap is exactly designCheck and kidsMaskedN. Branch
  `fix/merge-guards-build` (`8e24967d`) removes kidsMaskedN separately.
  **G2** (all on `fix/cache-rollback`, `d160afd4`, AllTests 970 green there).
  Census: the real entry returns through the legacy arm on 90 Signal-valued
  definitions of the imported IP modules — 45 structure projections, 39
  `Signal.fst` chains over one packed input, 6 others; every one has a domain
  binder. `proj_entry_output` (generic; observable premises fit 45 of 45)
  and `tuple_entry_output` (fit 39 of 39; 1768 slice steps equal the
  type-derived bounds) conclude `MemoHit ∨ out carries the input / the slice
  of the packed input`, under reflection and oracle premises that quantify
  over every run (the census observes one run each), and for the tuple class
  two per-node premises about the run. Real instances: `SHA256Out.done`,
  `SoCState.fetchPC`. `MemoHit` stays a disjunct (needs a law about the
  memo's contents: user decision). FINDING (C): `getWireWidth` reads a global
  width cache before the builder state; a stale smaller width would select
  wrong slice bits silently.
- 2026-10-12 (later), main unchanged (`9e07028d` + this note). On the isolated
  branch `fix/opt-fallback-build` (`b00fcb4e`, AllTests 999 green there; NOT
  merged) the generated depth SV endpoints of `parent` and `chained` went
  from three not-allowed premises to: `designCheck` only (masked-output guard
  ported), then to `portsMatchB` and `kidsPass` (the emitted-text check and
  the width tables of the SHIPPED module are derived from the run, through a
  print guard with fallback: the optimizer's candidate is kept only if a
  Sparkle-side copy of the text check accepts it; the copy is proved equal to
  the proof-side check; the raw module is proved to pass from every run). All
  guards fire on 0 of the 30 measured declarations. Left there: port matching
  (argument widths of a call are compared by nothing; a decidable data
  condition `callArgsOk` is stated) and the children's own checks (a leaf
  child's merged module has no print guard).
  FINDING (D), confirmed in the source: the HIERARCHICAL commands do not
  print the artifact the endpoints speak about. `toVerilogDesign`
  (`Sparkle/Backend/Verilog.lean:499`) emits every module of a design through
  `Optimize.optimizeModule` directly — no check, no fallback — and is what
  `#synthesizeVerilogDesign`, `#writeVerilogDesign` and `#sim` call
  (`Elab.lean` 8991, 9001, 9144, 9209; `#sim` optimizes the design once more
  before). Only the single-module commands print `checkedOptimize module`
  (`verilogOf`, `Elab.lean:8828`). The design endpoints conclude about
  `checkedOptimize b` with the children as the design's unoptimized modules.
  So for a hierarchical design the proved statement and the printed text are
  about different modules; which artifact is THE output is a decision for
  the user (the ruling "the real print call and the theorem must use the
  same selected artifact" applies).
- Finding D measured (`Tests/Compiler/PrintArtifactCensusTest`, logs only, on
  main): 37 real declarations (29 with an instance, 8 without). The top
  module of the hierarchical design equals the single-module entry's module
  on 37 of 37, and the two designs have the same modules on 37 of 37. But the
  module the design commands PRINT for the top (`optimizeModule b`) equals
  the endpoints' module (`checkedOptimize b`) on 5 of 37, and the emitted
  text is equal on the same 5 only (e.g. `parent`: 890 against 964
  characters; the checked route names the instance connections again, the
  design route does not; `rcH`, instance-free: the checked route returned the
  unoptimized module, the design route printed the optimized one). Of 39
  child modules the unchecked optimizer changes 33 (and their text), whereas
  the endpoints take children unoptimized; it agrees with `checkedOptimize`
  on 15 of the 39. The optimizer is idempotent on every module of only 5 of
  the 37 designs (`#sim` applies it twice).
