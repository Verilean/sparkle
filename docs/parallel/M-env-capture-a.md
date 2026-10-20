# Environment capture, variant (a): ONE entry, every declaration captures its own read

Branch `fix/env-capture-a` from poc `80745d94`. **WRITTEN, NOT BUILT. Nothing
was compiled or run** (worker M never starts Lean; the integrator builds).
"READ" = read in the tree; "PREDICTED" = expected from reading; "MEASURED" =
what a test of §8 will show once the integrator runs it. Earlier records:
`docs/parallel/ENV-audit.md`, `docs/parallel/ENV-capture-proposal.md` (branch
`fix/inst-arm-env-build`), `docs/parallel/verification-env-capture-isolated.md`,
`docs/parallel/B-slotless-parents-2.md`, `docs/parallel/open-rulings-2026-10-14.md`.

Ruling implemented (reviewer, 2026-10-14, second message, item 3): do variant
(a) — the re-base — in isolation, fix the run connection of the existing
files, integrate into the real commands; end the two-entry state; every
declaration's entry (nested children included) captures its own read; do not
overlook `projFieldName?`; do not claim all-input equivalence with the old
entry from measurements; no environment-constancy axiom.

## 0. Design

### (a) The entry and the translator

    def translateInstanceOrFallback (env : Environment) (rec : TranslateFn) : TranslateFn
    def translateFallback (env : Environment) (rec : TranslateFn) : TranslateFn
    def translateStep (env : Environment) : TranslateFn → TranslateFn :=
      translateStepWith (translateFallback env)
    def translateExprToWire (env : Environment) (e) (hint := "wire") (isTopLevel := false)
        (isNamed := false) : CompilerM String :=
      translateFuelFix (translateStep env) translateFuelLimit e hint isTopLevel isNamed
    def synthesizeCombinationalCoreWith (translate : Environment → TranslateFn) …
      -- … let env ← getEnv
      --   synthesizeFromConst (translate env) logProf … (entryConst … (instancePredicate env) …)
      --     (instancePredicate env)
    def synthesizeCombinationalCore :=
      synthesizeCombinationalCoreWith (fun env e h t n => translateExprToWire env e h t n)

The arm no longer reads: `instArmEnv` and its `let env ← …` line are gone; the
arm's three tests are on its parameter. There is no second arm, no
`entryTranslate`, no `…E` definition: one translator, indexed by the value the
entry read. `synthesizeCombinationalWithParameters` moved out of the `Rec`
block (it applied the entry to the block's translator PARAMETER, which is not
a function of an environment); the closed aliases `handleMux`, … take `env`.

**The proofs' literal translator** becomes `fun e h t n => translateExprToWire
tenv e h t n`. The form chosen for the 76-file problem, and why:

| candidate | what it costs | verdict |
|---|---|---|
| a `CompilerState` field read by the arm | Fact B of the proposal: a side condition in the proofs generic in the context; and the harness builds the context from nothing, so the harness terms change anyway | rejected |
| keep `translateStep` / `translateFallback` closed and wrap only the last arm at the step | 358 + 14 mentions untouched, but every fuel induction needs a rewrite lemma per use (`translateStepE env rec e = translateStep rec e` off `.other`): hand work at ~340 sites | rejected: more hand edits |
| **thread `env` through the four names, bind it by a section variable** | every occurrence changes by ONE token rule; theorems gain an implicit binder only where their statement mentions the translator | **chosen** |

Counts (`grep` at `80745d94`, code only, term positions): `translateExprToWire`
303, `translateStep` 341, `translateFallback` 353,
`translateInstanceOrFallback` 14, entry applications 15 + 22, in 138 files of
`Tools/` + `Tests/`; 31 occurrences are items of `unfold` / `simp only […]`
lists and are left. The binder: `variable {tenv : Lean.Environment}` once per
file (109 files); Lean includes it in exactly the theorems whose STATEMENT
mentions it, as an implicit argument, so every positional application
elaborates as before.

Definitions that mention the translator are of two kinds, treated differently
(the matrix that decided it: `MachineClosesAt` occurs in 129 entry-level
statements, `MachineCloses` in 83 — statements about a run of
`synthesizeCombinationalCore`, where the environment is the run's own read and
cannot be named):

* **class I** — statements about MetaM runs used at the entry level
  (`BodyRel`, `TranslateRel`, `HarnessRel`, `FallbackRel`, `MachineCloses`,
  `MachineClosesAt`, `MachineClosesAtC`, `MachineClosesAtS`,
  `MachineKeepsCoherent`, `LetsClose`, `CallsClose`, `CallsPure`,
  `HarnessStill`, `HarnessProv`, `MemoSound`, the six fields of
  `ArmObligations`): the body gets a leading IMPLICIT `∀ {tenv :
  Lean.Environment},`. Their parameter lists do not change, so every statement
  that only NAMES them is textually unchanged — the generated endpoints
  included — and every application of a hypothesis of such a type elaborates
  as before (the environment is found from the run it is applied to). Only the
  proofs that INTRODUCE such a statement name the binder (`intro tenv …`, `fun
  {tenv} … =>`).
  `MachineRan` and `CoreVia` say "the run performed a machine synthesis": the
  environment is EXISTENTIAL there (`∃ (tenv : Lean.Environment) (b : Bool) …`).
* **class II** — CompilerM-level definitions (never used in an entry-level
  statement): an explicit first parameter `(tenv : Lean.Environment)`, `X` →
  `X tenv` at every use. The closure computed by the script: `LeafContract`,
  `ReachesInline`, `ReachesUnfold`, `ReachesAt`, `ReachesUnfoldAt`,
  `HarnessRun`, `HarnessSound`, `LegacyEntryReduces`, `InputSkipped`,
  `TupleNode`, `SubChain`, `HandlerCase`, `LeafDom`, `LegacyArm`, `LegacyDom`,
  `FstChainLeaf`, `TopNode`; by hand `PlainHead` (below).

**The tag predicates.** `HardwareTagged mn` and `ProjEnvDefines …` keep their
statement: "in every environment a `getEnv` run returns …" (`instArmEnv` WAS
`getEnv`; the definition now says so). The arm tests its parameter, so the
five harness theorems that step through the arm
(`synthesizeMixedCertified_instance{,1,N,G,Proj}_sound`), their five
dispatchers, `inst_leaf_contract`, `inst_leaf_fuel` and the two cone theorems
take one more hypothesis, `(henvT : MReturns getEnv tenv)` — the translator's
environment IS a read — which the entry-level callers discharge with the
bridge's `henv.mreturns`. Consequence: `InstancePreserves` (5 forms) and every
entry-level statement and S6 capstone that carries `HardwareTagged` are
UNCHANGED, premise for premise. (`htagAll : HardwareTagged ``childAdd` in the
capstones is now derivable from their `tag` premise at the entry's read; it is
left in place — dropping a premise of a capstone is the reviewer's call.)
`HierConePreserves` exposes the environment it is about: `∃ tenv, MReturns
getEnv tenv ∧ …` (its leaf contracts are contracts of the translator over that
value); its parameters are unchanged.
`PlainHead tenv mn` is two conjuncts: plain in `tenv` (what the arm tests) AND
in every read (what the legacy handler `handleDefinitionUnfold` tests on its
own reads, R7/R8).

### (b) Nested children

`synthesizeChild n` = memo lookup, else `synthesizeCombinational n` =
`synthesizeCombinationalWith (fun env … => translateExprToWire env …) n` =
the SAME entry function: its own `getConstInfo` (R1) and `getEnv` (R2), its
own `translate env`. So a child's body is translated over the CHILD entry's
read; the parent's value is never handed down. READ: `childSynthEntry` →
`sparkleChildSynth` → `synthesizeChild` are untouched. The child memo is
keyed by name as before; `RealChild` (a run of `synthesizeCombinational c`)
and `ChildBnd` mention only closed entry terms and are untouched. That the
parent's and the child's reads are the same VALUE in real runs is the audit's
reading (ENV-audit §5), not a theorem; no proof of this unit needs them
equal (class I statements are for every environment; a child's facts enter
through `RealChild`).

### (c) Every remaining environment read on a synthesis path

| read (ENV-audit numbering) | captured? | why | who depends on its value |
|---|---|---|---|
| R1, R2 entry (`getConstInfo`, `getEnv`) | this IS the capture | — | the bridge lemmas expose both |
| R3 machine arm `getEnv` in `synthesizeFromConst` | no | not on a gate parent's path; `MachineDefines` already quantifies over this second read (`envR'`) | `MachineDefines` (unchanged) |
| R4 instance arm | **yes** (removed: the parameter) | the unit | `htag tenv henvT`, `PlainHead tenv`, `instanceArm_grow` |
| R5 `projFieldName?` (projection arm; `getEnv`, `getConstInfoInduct`, `getConstInfoCtor`, a telescope) | **no** | it does not decide instance-or-legacy; capturing only its first line would leave three MetaM reads; rewriting it over `env.find?` could change what it accepts | the EXISTING premise `ProjFieldDefines pn structName fieldName` (every run of `projFieldName? pn structName` returns `some fieldName`) of `synthesizeMixedCertified_instanceProj_sound`. OBLIGATION, stated: a lemma that derives `ProjFieldDefines` from the entry's read would need "the environment `projFieldName?` reads equals `tenv`" — no built or planned lemma needs it (`gate_parent_run` is for single-output roots and cones; a projection parent's run lemma WOULD) |
| R6–R8 `Rec.handleDefinitionUnfold` | no | inside the `partial` block; threading `env` there changes every `Rec.*` term | `PlainHead`'s second conjunct (unchanged content). A planned lemma for a legacy-route parent with a tagged callee would need R7 = the entry's read |
| R9 type-width inference, R10 structure layout, R11 constructor field count | no | oracles of the legacy handlers | the existing oracle premises (`InfersBits`, …); nothing compares them with `tenv` |
| R12 `kernelNat` | captured since before (inside `structEnv env`) | — | — |
| Lean `Meta` operations (`whnf`, `inferType`, …) | no | not expressible | oracle premises |

### (d) What can change in the compiler's behaviour

By construction the arm now tests on the entry's read where it tested on a
later read. If the two reads were different values the observable differences
would be exactly:

1. a callee tagged at the later read and not at the entry's: old arm
   instantiates, new arm hands over to the legacy translator (whose
   `handleDefinitionUnfold` reads again and may still instantiate);
2. the reverse: old arm legacy, new arm instantiates — and then agrees with
   the mixed gate, which accepted the body under the entry's read;
3. the same two for the projection arm's `getProjectionStructureName?` and
   the record head's tag;
4. nothing else: no other code path takes `env`.

That the reads are equal in real runs is BY AUDIT (ENV-audit: no writer of
`Core.State.env` found on a synthesis path; transitive closure of the Lean
operations not established). **No equivalence with the old entry for all
inputs is claimed.** The integration criteria of §8 are measured comparisons
on listed declarations.

## 1. The compiler change (`Sparkle/Compiler/Elab.lean`, +81 −49)

As (a). Removed: `instArmEnv`, the arm's read, `Rec.synthesizeCombinationalWithParameters`.
Changed signatures: `translateInstanceOrFallback`, `translateFallback`,
`translateStep`, `translateExprToWire`, `synthesizeCombinationalCoreWith`,
`synthesizeCombinationalWith`, the twelve closed aliases. Unchanged names and
types: `synthesizeCombinationalCore`, `synthesizeCombinational`,
`synthesizeChild`, `synthesizeCombinationalWithParameters`,
`synthesizeHierarchical*`, every command, every harness, `synthesizeFromConst`.

## 2. The re-base

`scripts/env-capture/rebase.py` (run once on the tree after the compiler
commit; it refuses a tree that already has the identifier `tenv`). Its report:

    class I body: 17            class II header: 18        class II use: 149
    entry application: 15       entry application, constant translator: 22
    name position (left): 31    program binder: 32
    translateExprToWire: 303    translateFallback: 353     translateInstanceOrFallback: 14
    translateStep: 341          variable line: 107         files changed: 147

(That run still had `CoreVia` in the class I list and `HierConePreserves` in
the class II closure; both were then redone by hand — existential, inside —
and the committed script lists them under hand, so a rerun reports 16 / 17 and
correspondingly fewer class II uses.)

After the hand edits, against `80745d94`: the compiler; `Tools/` 145 re-based
files + the consumer; `Tests/` 40 re-based files + 2 target-only tests;
`scripts/shipping-coverage/closing_compare.lean`; three new scripts.

### Hand edits (each written out in the diff; grouped)

| group | where | what |
|---|---|---|
| bridge statements | `synthesizeCombinationalCore_reads`, `core_reads_val`, `core_reads_val0`, `core_reads_inv`, `outer_reset_reaches` | the translator's `tenv` → the statement's own `envR` (5) |
| generic bridge | `outer_reset_reaches_with` | `{translate : Lean.Environment → TranslateFn}`, conclusion `synthesizeFromConst (translate envR) …` |
| `core_keeps` | `ShippingChildKeeps.lean` | `hbody : ∀ {tenv}, D < limit → …`; the restated entry text names its own `env` |
| existential runs | `machine_run_of_core`, `core_closeInsts`, `coreVia0_of`, `mixDeep_closes_outermost`, `MachineRan`, `CoreVia` | `∃ (tenv : Lean.Environment) …` first; provers `⟨_, …⟩` (6); destructurings `obtain ⟨_, …⟩` by asserted regex: `machine_run_of_core` 33, `core_closeInsts` 6, `MachineRan` 12, `hvia` 1, `coreVia0_of` 1 |
| premises for every environment | `coreVia0_of.hclose`, `machineRan_outermost.hclose`, `ranAt_outermost.hclose`, `entryOk_machine.hout`, `machineCloses_noCalls_iff` (right-hand side), `tuple_entry_output_outer` (`plainF`, `plainS`, `hchain`), `useDbl_output_outer` (`hplain`, `hnosub`) | a leading `∀ {tenv : Lean.Environment}` (implicit first, so `fun …` providers and `h args` uses elaborate unchanged) |
| class I provers | 22 theorems (`bodyRel`, `harnessRel_of`, `fallbackRel_of_legacy`, `translateRel_of_fallback`, `machineClosesAt_of_closes`, `…_of_pure`, `…_of_gateKids`, `…_of_seqKids`, `…_of_kidsD`, `…_of_kidsD_again`, `…_of_kidsDM`, `…_of_det`, `MachineClosesAtC.of_closes`, `machineClosesAtC_of_S`, `MachineClosesAtS.of_closes`, `machineClosesAtS_of_kids`, `machineCloses_of_noLets`, `machineCloses_iff` ×3, `machineCloses_noCalls_iff` ×2, `harnessStill_frag`, `harnessStill_all`) | `intro tenv …` / `fun {tenv} … =>` |
| `ArmObligations` | `ShippingMemoInv.lean` | six fields `∀ {tenv : Lean.Environment} (b : Bool) …` |
| the arm | the five `synthesizeMixedCertified_instance*_sound`, `inst_leaf_contract`, `arm_to_shim` | the three lines that stepped through the read are replaced by `change Returns (if isHardwareModule tenv mn = true then _ else _) _ _ _ _ at tr` and the tag at `tenv` (`htag tenv henvT` / `hpenv tenv henvT` / `hplain.1`) |
| `henvT` | 14 theorem headers, 21 call sites | see (a) |
| tag predicates | `HardwareTagged`, `ProjEnvDefines`, `PlainHead` (+45 uses, `hplain.2 env henvM` in `unfoldSpec_plain`), `HierConePreserves` (+3 test destructurings, 4 `inst_leaf_fuel` calls) | see (a) |
| consumer | `Tools/ShippingInstArmGrow.lean` | re-pointed at the one arm; the three duplicated invariant lemmas of the proposal deleted |

Tests that RUN the translator (32 `run_cmd` / `def`): `let tenv ←
Lean.getEnv` as the first statement; a test's own translator handed to the
entry becomes `(fun _ => tr)` (22). One declaration is excluded
(`oldTryInline`: a local binder named `translateExprToWire`).

Generators: `Tools/ShippingMachineCommand.lean` `generateCore` (the one
quotation of the translator in `Tools/*Command*.lean`) gets the program
binder. No generator refers positionally (`mkConst` + `mkAppN`) to a theorem
that gained the binder (searched: every `` ``name `` / `@name` of the 373
declarations whose statement mentions `tenv`; the hits are three tests that
`inferType` a constant — `harness_closed`, `transition_fields`,
`transition_spine` — and one name list).

## 3. Statement changes (old → new)

Everything not listed keeps its statement up to `translateExprToWire e h t n`
→ `translateExprToWire tenv e h t n` (and `(translateStep tenv)`,
`(translateFallback tenv)`, `translateInstanceOrFallback tenv`) with `{tenv :
Lean.Environment}` implicit.

1. Bridges (5 + 1): `… RunsTo (synthesizeFromConst (fun e h t n =>
   translateExprToWire e h t n) …)` → `… translateExprToWire envR e h t n …`,
   `envR` the statement's existing read. This is the fact the unit is for:
   the SAME `envR` in the translator and in `instancePredicate envR`.
2. Class I definitions: body `∀ (b : Bool) …` → `∀ {tenv : Lean.Environment},
   ∀ (b : Bool) …` (15 definitions, 6 structure fields). `MachineRan`,
   `CoreVia`: `∃ (b : Bool) …` → `∃ (tenv : Lean.Environment) (b : Bool) …`.
3. Class II definitions (18): one more explicit first parameter.
4. `HardwareTagged`, `ProjEnvDefines`: `MReturns instArmEnv env` → `MReturns
   (Lean.getEnv : MetaM Lean.Environment) env` (the same proposition).
5. `PlainHead mn` → `PlainHead tenv mn` := (plain in `tenv`) ∧ (the old
   statement). STRONGER premise by one conjunct, in the `LegacySem` family
   (35 theorems, none an endpoint).
6. `HierConePreserves …` := `∃ tenv, MReturns getEnv tenv ∧ (old body with the
   leaves' contracts over `tenv`)`.
7. `+ (henvT : MReturns getEnv tenv)`: `synthesizeMixedCertified_instance_sound`,
   `…instance1…`, `…instanceN…`, `…instanceG…`, `…instanceProj…`, the five
   `synthesizeFromConst_instance*_sound`, `synthesizeMixedCertified_hierCone_sound`,
   `synthesizeFromConst_hierCone_sound`, `inst_leaf_contract`, `inst_leaf_fuel`.
8. `∃ (tenv : Lean.Environment)` first in the conclusion: `machine_run_of_core`,
   `core_closeInsts`, `coreVia0_of`, `mixDeep_closes_outermost`.
9. `∀ {tenv : Lean.Environment}` first in a premise: `core_keeps.hbody`,
   `coreVia0_of.hclose`, `machineRan_outermost.hclose`,
   `ranAt_outermost.hclose`, `entryOk_machine.hout`,
   `tuple_entry_output_outer.{plainF,plainS,hchain}`,
   `useDbl_output_outer.{hplain,hnosub}`; `machineCloses_noCalls_iff`'s
   right-hand side.
10. `outer_reset_reaches_with`: the translator is `Lean.Environment →
    TranslateFn`.

**Endpoints.** PREDICTED: no generated endpoint (`machine_sound`,
`machine_design_*`, `machine_ships_*`, `gate_*`, `entry_ok`, …) gains or loses
a premise or changes its conclusion: those that name class I definitions are
textually identical; those whose statement mentions the translator gain the
implicit `{tenv}` (the renaming). The S6 capstones are unchanged. This is
what §8 (iii) measures; I could not enumerate the generated statements by
reading (they exist only after the generators run).

## 4. Proved / by audit / measured

| | status |
|---|---|
| the instance arm tests the entry's read | by construction (the definition) |
| the bridge lemmas give the same `envR` in translator and predicate | PROOF, written, not built |
| every existing theorem holds for the translator of every environment | PROOF (the re-base), written, not built |
| a child's entry captures its own read | by construction (READ) |
| two reads of one synthesis are equal | BY AUDIT only |
| the one entry returns what the old one returned | MEASURED on the declarations of §8 (i), (ii); not claimed beyond |

## 5. The consumer (`Tools/ShippingInstArmGrow.lean`)

Re-pointed: `spine_tag`, `spineRoot_tag` (pure), `armCont`, `armCont_keepsC`,
`instanceArm_grow`, `instanceArm_grow_of_root` are statements about
`translateInstanceOrFallback env rec` — the arm the commands run. Of the five
next statements of ENV-capture-proposal §6:

1. `instanceN_stepE` — IS the built `instanceN_step` now (it concludes
   `translateStepWith (translateFallback tenv) rec (instEN …) … =
   translateInstanceOrFallback tenv rec (instEN …) …`). Nothing to write.
2. the world-level bridge with the same `envR` in translator and predicate —
   IS `core_reads_val` / `core_reads_val0` / `core_reads_inv` now.
3. the mixed harness shell in `WG` — NOT written. Exact statement:

       theorem mixedHarness_grow (hB : ∀ L', BodyRel L') (hLg : ∀ L', LegacyRel L') (hD : D ≠ 0)
           {tenv : Lean.Environment} {b : Bool} {declName bs body} {P}
           (hr : RunsTo (synthesizeMixedCertified (fun e h t n => translateExprToWire tenv e h t n)
             (profLogIO b) declName bs body) mctx mref cctx cref w (m, d) w')
           (hw : InvV L w) (hd : L.dval w = D) (hp : P (L.val w)) :
           ∃ ids cache returned st w1 w2,
             RunsTo (translateExprToWire tenv (instFVars (ids.map .fvar).toArray 0 body) "out" false true
               (prepared context) (prepared state)) mctx mref cctx cref w1 (returned, st) w2 ∧
             InvV L w1 ∧ L.dval w1 = D ∧ Sub (L.val w) (L.val w1) ∧ Sub (L.val w2) (L.val w') ∧
             m = (addClockResetIfSequential st.module).finalize

   (the `bind_S` / `emitLeaves_S` / `finishSynth_world` steps of
   `Tools/ShippingHarnessStill.lean` with `WG.ofKeeps` and `translateRel`).
4. the S6 shape tail over `armCont` (the tail of
   `synthesizeMixedCertified_instanceN_sound` from `Returns (armCont rec mn y
   …)` with `(mc, dc) := y`) — NOT written.
5. the two full-entry facts (`dropZeroWidthModule`, `mergeChecked` on a body
   with an instance) — NOT written.

`gate_parent_run` (statement in ENV-capture-proposal §6, now about
`synthesizeCombinational f`, the entry of the commands) and the `parentMix`
cone induction are NOT written. The chain stops at `instanceArm_grow_of_root`.

## 6. Build order

1. `Sparkle` (the compiler commit).
2. `Tools/` in the order of the commits (each family imports only earlier
   ones; computed from the import graph): translator-level soundness →
   `ShippingLegacySem*` → the world level (`ShippingChildInv` and everything
   above it) → generators.
3. `Tests.AllTests`; then the target-only tests of §8.
4. `Tools.ShippingInstArmGrow` (new library; `#print axioms spine_tag`,
   `instanceArm_grow`).

`lakefile.lean` (NOT edited by me), to add:

    lean_lib «Tools.ShippingInstArmGrow» where
      roots := #[`Tools.ShippingInstArmGrow]

`Tests/Compiler/EnvCaptureDigestProbe.lean` and
`Tests/Compiler/EndpointStatementAudit.lean` are target-only (`lake build
Tests.Compiler.EnvCaptureDigestProbe`); nothing to add to `Tests/AllTests.lean`.

## 7. Risks, in the order I expect them

1. **`variable {tenv}` inclusion.** A theorem whose PROOF mentions `tenv` but
   whose statement does not gets "unknown identifier" — the script reported
   8, all bound by hand (`intro tenv`); a miss shows as that error at that
   line. Fix: bind it (`intro tenv` / an explicit binder).
2. **Implicit `∀ {tenv}` in class I bodies.** Tactic provers I did not find
   (an `intro b w …` on such a goal binds `tenv` as `b`): the error is a type
   mismatch a few lines later. Fix: `intro tenv b w …`. Term provers: `fun
   {tenv} b … =>`. A provider `fun a b => …` for a premise `∀ {tenv} (a) (b),
   …` relies on Lean's implicit lambda; if it does not fire, `fun {tenv} a b
   => …`.
3. **The arm proofs** (7 sites): `change Returns (if … then _ else _) _ _ _ _
   at tr` must see through the `match` on the head (the old proofs did it by
   `Returns.bind`); if `change` fails, `dsimp only at tr` before it.
4. **Existential reorderings**: an `obtain ⟨…⟩` of `machine_run_of_core` /
   `MachineRan` / `core_closeInsts` in a form my regexes did not match (they
   matched 33 / 12 / 6; `grep` shows no other spelling).
5. **`henvT` threading**: a caller of the 14 theorems I did not see (searched
   `Tools/` and `Tests/`).
6. Tests that inspect a statement's shape by `inferType`
   (`ShippingMachineClosesTest` 239, 301; `ShippingReflectCtxTest` 100):
   the constants gained an implicit binder; if they count binders, the count
   is +1.
7. `Sparkle/Compiler/Elab.lean`: the arm's `do if … then … else match …`
   layout (the `let env ← …` line removed from an existing `do`); the type
   ascription of `translateStep`.
8. The derived simulation driver (`gate_parents_sim.py` asserts on the
   template; `@parentUse defaultDomain …` assumes the implicit domain is the
   first argument).

## 8. Integration criteria (the integrator runs them on poc AND on the candidate)

| | what | file | PREDICTED |
|---|---|---|---|
| (i) | digests of `synthesizeCombinational f` for the eight gate parents, the two legacy controls, 15 named hierarchy / machine / memory declarations and the first 30 tagged test declarations by name | `Tests/Compiler/EnvCaptureDigestProbe.lean` (builds on both trees) | `diff` of the `ENVCAPTURE DIGEST` lines: EMPTY |
| (ii) | writer simulation of the eight gate parents: `#writeVerilogDesign` text under iverilog against the source function | `scripts/shipping-coverage/gate_parents_sim.sh` (+ `.py`, derived at run time from the tree's `module_name_sim`) | eight lines `GATEPARENTSIM <decl>: command==source T x-cycles=0` on both trees |
| (iii) | endpoint statement audit: per endpoint theorem of the AllTests environment — binders, `Lean.Environment` binders, premise heads with multiplicity, conclusion head, whether it mentions the translator, hash of the statement | `Tests/Compiler/EndpointStatementAudit.lean` (builds on both trees) | lines with `translator=F`: IDENTICAL, hash included. Lines with `translator=T`: `binders` +1 and `env` +1 (or equal counts when the binder is inside a premise), hash differs, premises and conclusion heads equal. Anything else is a finding |
| (iv) | `Tests.AllTests`; census 134 / 133; the pin tests; `SlotlessParentProbeTest`'s eight `SLOTLESSPARENT RESULT` lines against poc's; `nested_let_sim.sh`, `subinst_key_sim.sh`, `writer_sim.sh` (hierarchy code changed: sims apply) | existing | unchanged |

## 9. Open after this unit

* `gate_parent_run` for `parentUse` / `wrapAdd` / `wrapPick` (items 3–5 of §5)
  and the cone (`parentMix`).
* The redundant `htagAll` premise of the S6 capstones (derivable now).
* R5 (`projFieldName?`), R6–R8: obligations stated in (c), not discharged.
* A theorem that two reads of one synthesis are equal: none, by the ruling.

## 10. Could not be determined by reading

* Whether every tactic prover of a class I statement was found (risk 2).
* Whether `change … at tr` reduces the arm's `match` (risk 3).
* Whether Lean's implicit-lambda insertion fires at every provider of a
  generalised premise.
* The generated endpoint statements (they are produced at build time).
* Whether `vc` walks the arm without the read exactly as before
  (`translateInstanceOrFallback_keepsC`, `armCont_keepsC`).
