# M4 parametric / symbolic entry: investigation and freeze (rev4; rev2 answered R1-R3 on 7c297d5f, rev3 answers the remaining R3 on 2030997a, rev4 adds §11 on top of the approved 8acc71dd; rev5 (§13) corrects the I5b plan, fixes PosPlus and separates the open links, on top of 3682b80b)

- **Issue:** `sparkle-gen4-parametric-supply`.
- **Status:** investigation + freeze of types and plan. No Lean, no build, no production edit. rev2 changes: §1.5, §3.2, §4 (I2, I5, new I5a/I5b), new §8 (response to R1-R3), new §9 (complete telescope and suppliers). rev1 text that was withdrawn is listed in §8, not silently removed.
- **rev3 changes:** only §9.1 (complete signatures, no ellipsis/etc./copy-later), §9.3 U5, §10, new §8 R3-rev3. §4 rows I1, I3, I4 are superseded where §9.1 differs (I1 is pure gate facts, I4 is out of the unit).
- **rev4 changes:** only the new §11 (P4 survey, I3c, I4, §9.2 complete types and suppliers) and §12 (what the reviewer is asked to approve). §1-§10 are unchanged; where §11 replaces a §9.2/§9.3 entry it says so. Docs only; no Lean, no build. rev4 `file:line` are at 8acc71dd (branch `kjob/g4par-r4`) unless a SHA/branch is named.
- **Base:** HEAD d0ddc50b (branch `kjob/g4par-d0ddc50b`). All `file:line` below are at d0ddc50b unless a SHA/branch is named.
- **What this document is not:** it proves nothing and does not complete the parametric part of FG.
  Statements marked PROPOSED are types for the reviewer to accept; none is accepted yet.
- **Wording.** "This survey did not find X" means the sources listed were read and X was not there. It does not say X is impossible or not derivable.

## 1. Difference from the default entry (real functions, sources, full result type)

### 1.1 The two entry functions
| | default | parametric |
|---|---|---|
| function | `synthesizeCombinational := synthesizeCombinationalWith (fun env e h t n => translateExprToWire env e h t n)` (Sparkle/Compiler/Elab.lean:8920) | `synthesizeCombinationalWithParameters (declName : Name) (parameters : List (String × Nat))` (:8940-8953) |
| body | `synthesizeCombinationalWith` (:5592-5606) | calls `synthesizeCombinationalCoreWith … declName parameters true` (:8943-8944), then the same post-processing text |
| core | `synthesizeCombinationalCoreWith translate declName [] false` (:5594) | the same core with `parameters` and `symbolicMode := true`; `certifiedFrontEnd` is its default `true` |
| full result type | `MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)` | the same type |

`synthesizeCombinationalCoreWith` is `(translate : Lean.Environment → TranslateFn) (declName : Name) (parameters : List (String × Nat)) (symbolicMode : Bool) (certifiedFrontEnd : Bool := true) : MetaM (Module × Design)` (:5423-5426).

Post-processing is identical text in both: `dropZeroWidthModule` on the top module and on the top module inside `D`, then (unless `SPARKLE_NO_REGDEDUP` is set) `RefineCheck.mergeChecked` on both (:5602-5606 and :8948-8953). So `b ∈ {dropZeroWidth raw, mergeChecked (dropZeroWidth raw)}` is the same relation for both entries (as in `T1Stmt`, scripts/gen2/GEN2_DEFS.lean.txt:347-357).

### 1.2 What the flags change (complete list found by reading Elab.lean)
| # | place | effect when `symbolicMode = true` or `parameters ≠ []` |
|---|---|---|
| a | core prologue :5427-5435 | symbolic only: duplicate parameter name → `throwError`; default value `0` → `throwError`. Both run BEFORE the depth check and before any state change. |
| b | `certifiedShape?` :2316-2319, `mixedCertifiedShape?` :2874-2880, `machineShape?` :5072-5076 | each returns `none` when `symbolicMode || !parameters.isEmpty` |
| c | `entryConst` :5272-5282 | guard `certifiedFrontEnd && !symbolicMode && parameters.isEmpty` fails, so the entry constant is `ci` as read (no inlining) |
| d | `synthesizeFromConst` :5312 | machine attempt only when `certifiedFrontEnd && !symbolicMode && parameters.isEmpty`, else `machine? = none` |
| e | memo `sparkleSubModuleCache` :5334-5338 and :5387-5389 | read and write only `if !symbolicMode`; a symbolic run neither reads nor inserts its memo entry |
| f | legacy tail :5361-5373 | symbolic: each requested parameter must be a top-level `Nat` binder of the lambda telescope, else `throwError` |
| g | `bindInputsLegacy` :2115-2151 | a binder whose name is a requested parameter becomes `addParameter name default` + `withDimVarMapping fvarId (.parameter name)` (no port); in symbolic mode every `Signal` binder becomes an input port without the fallback `try` |
| h | `entryCompilerState symbolicMode` :2925-2927 → `CompilerState.symbolicMode` (:62) | `inferHWTypeWithDimensionsStep` (:694-720) switches from the concrete `inferHWType` to `extractDimExpr`-based widths with `DimExpr` (`hwTypeFromDim`); `withDimVarMapping` (:120-126) |
| i | `finishSynth` :2218-2232 | symbolic: `throwError` if the module body contains any `.register`, `.memory` or `.inst`; `throwError` if a requested parameter is not in `module.parameters`. Then, as in default, `ModuleNameCheck.check` and `(addClockResetIfSequential module).finalize` (:2200) |

### 1.3 Where `parameters ≠ []` with `symbolicMode = false` comes from
This survey did not find a caller. The only core callers are :5594 (`[] false`) and :8943 (`parameters true`); every `Tests/` call found with `grep synthesizeCombinationalCore` passes `[] false`. Both guards are written with `||`, so the pair `(parameters ≠ [], false)` behaves like symbolic for the gates and the machine route. It is outside FG's two entries and outside this freeze (recorded as P0 for the census).

### 1.4 Children in the parametric entry
`translate` calls children through `childSynthEntry` (:5616-5624) = `sparkleChildSynth` = `synthesizeChild` (:8929-8934) = the DEFAULT entry `synthesizeCombinational` with `[] false`, memoised in `sparkleChildCache`. So a child of a parametric top is a default-entry result; the flags do not propagate (this is also the reading of docs/parallel/A-cache-coherence-2.md:92 at par/gen3-induct). The depth-0 clear of `sparkleChildCache` (:5536-5541) is the same.
- **Not found:** whether a successful symbolic run can have a non-empty `D.modules` (a child synthesised and then inlined into `raw`), because `finishSynth` forbids `.inst` in `raw` (:2222-2227) but this survey did not read `D` handling in the translator. This is probe P1 (§5).

### 1.5 Generated result: full type and shape of a symbolic success
`(raw, D) : Module × Design` with, by §1.2 (i), `raw.body` having no `.register`/`.memory`/`.inst` (checked at :2222-2227 on the module BEFORE `addClockResetIfSequential`). **WITHDRAWN from rev1:** "so no clk/rst input". `addClockResetIfSequential` (:2200-2210) is the identity on a module without `.register`/`.memory`; it never removes an input, so any `clk`/`rst` input already present in `module.inputs` stays. Whether a symbolic-mode run can have such an input (e.g. a user `Signal` binder named `clk`, or a translator arm that declares one) was not read by this survey: recorded as probe P3, `raw.parameters` containing every requested name (`Parameter` has `name` and `defaultValue`, Sparkle/IR/AST.lean:328), and widths that may be `DimExpr` over those parameters. The consumer that gives it a concrete meaning is `Sparkle.IR.Specialize.specializeDesign (design : Design) (bindings : List (String × Nat)) : Except String Design` (Sparkle/IR/Specialize.lean:145): it requires the top module to be present, every declared parameter bound exactly once and no unknown binding (:36-48 `validateBindings`), and removes `parameters`.
Existing evidence on this route: the coverage table says "Not covered by S0–S2 endpoint" (docs/ShippingCompiler-Coverage.md:28), the trust base says symbolic-width synthesis "stays outside" (docs/ShippingCompiler-TrustBase.md:663-665), and the only Lean facts found are name validation `hierarchical_parameters_names` (Tools/ShippingModuleNames.lean:26-30) and a verbatim legacy-tail copy used for the machine split (Tools/ShippingMachineOutcomeA.lean:51-100, parameterised by `symbolicMode`).

## 2. When the machine route is invalid, and the real dispatch

Machine route taken (default entry) needs: `certifiedFrontEnd`, `¬symbolicMode`, `parameters = []`, `certifiedShape?`/`mixedCertifiedShape?` = none on `ci`, `machineShape? = some shape` on the entry constant, and `synthesizeMachineCertified … = some` (:5288-5323; the `MachineCloses` condition, Tools/ShippingMachineEntry.lean:2363).

| condition making the machine route unavailable | dispatch that follows (real code) |
|---|---|
| `symbolicMode` or `parameters ≠ []` (parametric entry) | gates off (:2319, :2880) → machine off (:5312) → NO memo read (:5334) → legacy tail with symbolic binders (:5339-5391) → `finishSynth` symbolic checks → post-processing. Route 7 of ROUTE_CENSUS.md. The top is always the legacy tail. |
| `certifiedFrontEnd = false` | the same, except that the memo is read/written when `¬symbolicMode`. Only tests pass `false` (this survey did not find a shipping caller). |
| `machineShape? = none` (default entry) | memo (:5334-5338), else legacy tail (:5339-5391), which writes the memo (:5387-5389) |
| `machineShape? = some` but synthesis `none` (route 4) | the same as the row above; the machine attempt ran first and its world effects stay (Tools/ShippingMachineOutcomeA.lean:106-112 `synthesizeFromConst_machine_splitA`) |
| a gate accepts `ci` (routes 1/2) | gate result, memo insert. In the parametric entry gates are off, so a gate-shaped declaration compiled with parameters goes to the legacy tail, not to the gate. |

**Consequence for FG.** FG's second disjunct (scripts/gen2/GENERAL_SPEC.md:91) is a run of the legacy tail in symbolic mode at the top, with children from the default entry. Every route-3 theorem (T1, `MachineTaken`) is about the first disjunct only; none of its premises can hold for the second disjunct, because `MachineTaken` needs `machineShape?` not to be disabled.

## 3. Common interface with the default-entry theorems (PROPOSED types)

### 3.1 What the default-entry statements assume
- FG conclusion (GENERAL_SPEC.md:93): `∃ p n, Pk declName = some p ∧ TopShips p n declName b raw D`, with `TopShips` (GEN2_DEFS.lean.txt:273-298) fixed to a machine package `p : Pkg ι dom` (`p.d.shape`, `p.d.ss` registers, `ResetNk`, `runModuleTG`, `"clk"`/`"rst"` equations).
- The symbolic-run raw body has no `.register`/`.memory`/`.inst` (§1.5). **WITHDRAWN from rev1:** "so no `Pkg` exists for it". `Pkg.comb` (Tools/ShippingGen2CombPkg.lean, slotless call-free package, step 1) exists, so whether a `Pkg` can describe a symbolic top is not decided here; this survey did not read whether `Pkg.comb` applies after specialization. `TopShips` as written is stated for machine packages (`p.d.ss`, `ResetNk`, `"clk"`/`"rst"` equations); whether it or a new conclusion is the right one for the second disjunct is open (§9 U3). This is a type observation, not a claim that a theorem is impossible. It is why FG's second disjunct needs its own conclusion that the first disjunct's conclusion also implies.
- A child interface already exists for combinational modules: `CombChildRunN` (GEN2_DEFS.lean.txt:60-74) with the data `(bsC, outsC, S)` of A-COMB, and the route-indexed `T1Hyp` proposal (ROUTE_CENSUS.md:106-108: "ONE common semantic child interface ... route-specific PRODUCERS").

### 3.2 PROPOSED shared interface (types only; to be put in a new file, e.g. `Tools/ShippingGen4EntryIface.lean`)
```lean
/-- What a top-level success promises, whatever the route. Fields are the A-COMB data. -/
structure TopIface where
  bsIn   : List (Name × MixedGateBinder)          -- input binders (as ChildShips: q.d.bsIn.take kD)
  outs   : List OutField
  S      : (Nat → List Nat) → List (Nat → Nat)     -- source semantics, as CombChildRunN
  seq    : Bool                                    -- sequential (machine) or combinational

/-- Machine-route top: the existing conclusion, packaged. -/
def MachineTopShips (p : Pkg ι dom) (n : Nat) (declName : Name) (b raw : Module) (D : Design) : Prop :=
  TopShips p n declName b raw D            -- unchanged text (GEN2_DEFS.lean.txt:273)

/-- Parametric top. Two separate notions (R2): LEGAL binding = what `validateBindings` accepts; SUCCESS = what
    `specializeDesign` returns `.ok` for. The ∀-quantifier ranges over legal bindings and SUCCESS is a hypothesis
    or a separate obligation (§4 I5b), never an assumed consequence of legality. -/
def LegalBinding (D : Design) (θ : List (String × Nat)) : Prop :=
  -- exactly the checks of Specialize.validateBindings on `D.modules` (names are design-global):
  -- declared parameter names of ALL modules have no duplicates inside one module; θ has no duplicate names;
  -- every θ name is declared by some module; every value ≠ 0; every declared name is bound.
  Sparkle.IR.Specialize.validateBindings D.modules θ = .ok ()     -- `validateBindings` is `private`: see §9 U1

def ParamTopShips (b : Module) (D : Design) (SrcAt : List (String × Nat) → TopIface) : Prop :=
  ∀ θ, LegalBinding (D.addModule b) θ →
    ∀ D', Sparkle.IR.Specialize.specializeDesign (D.addModule b) θ = .ok D' →      -- success is a HYPOTHESIS here
      ∃ b', D'.findModule b.name = some b' ∧ CombTopRunN (childMap D'.modules) D' b' (SrcAt θ)

/-- Separate supply obligation (target kept, not shrunk): for every θ with all values > 0 AND names matching, does
    `specializeDesign` return `.ok`? Not known; rev1's "iff" is withdrawn (§8 R2). -/
def SpecSuccessAllPositive (b : Module) (D : Design) : Prop :=
  ∀ θ, LegalBinding (D.addModule b) θ → ∃ D', Sparkle.IR.Specialize.specializeDesign (D.addModule b) θ = .ok D'

/-- FG's per-route conclusion: sum of the two, see §9 U2 (not yet defined). -/
def EntryShips … : Prop := …
```
Open details that are a reviewer choice and not decided here: (i) whether `θ` ranges over all positive bindings or only those the run's `parameters` defaults generate (the module declares the names, the defaults are metadata: Specialize.lean:131-134); (ii) whether `CombTopRunN` is `CombChildRunN` (reuse, with `"clk"/"rst"` absent) at depth 0 or a new definition. Reuse is preferred because a parametric top can then also be a child (§3.3).

### 3.3 Link to M3/M4 consumers
A parametric module could be a child only if some other entry calls it; the shipping children path calls the default entry (§1.4), so the parametric result is never cached or served as a child (no `ShipsRes` for it is needed). This survey did not find a call of `synthesizeCombinationalWithParameters` from inside the translator. Confirming this is I4 below.

## 4. Proof plan for the general guarantee (not corpus-by-corpus)

A fixed parameter list on a corpus example is an instance, not the guarantee. Acceptance of this issue requires the following statements to be proved ∀ declaration (under the same kind of per-declaration premise `ReflectsAll` already names) and ∀ θ, with the premises listed.

| step | statement (PROPOSED, informal types) | premises | status |
|---|---|---|---|
| I1 | `synthesizeFromConst … parameters symbolicMode=true … ci = legacyTail …` (the four gates and the machine and memo guards reduce, §1.2 b-e) | none beyond the definition | independent, can start after approval |
| I2 | `finishSynth` symbolic, restricted to what the code guarantees (R1): on `.ok (M, D)`, `finalCircuitState.module.body` (before `addClockResetIfSequential`) has no `.register/.memory/.inst`, `∀ p ∈ requested, p ∈ module.parameters`, and `ModuleNameCheck.check` holds; `M.body = module.finalize.body` because `addClockResetIfSequential` is the identity when there is no `.register`/`.memory` (only the `.inst`-free body is known, which makes the identity case apply). NOT stated: any property of `M.inputs` regarding clk/rst. A clk/rst-absence conjunct is a separate PROPOSED obligation I2b that needs P3 (a source of `clk`/`rst` inputs in symbolic mode) or an added hypothesis | none | independent
| I3 | core wrapper: the prologue throws exactly on duplicate/zero; otherwise the run equals the depth-gated body with `symbolicMode := true`; nested depth restoring as in `synthesizeCombinationalCore_reads` (Tools/ShippingEntrySoundness.lean:1090) | `Laws`, `Start` | independent (re-uses `RunsTo`, `peel_bind` tactics of EntrySoundness:1100-1115) |
| I4 | `WithParameters` post-processing: `(b, raw)` relation equals the default's (§1.1), and no translator path calls `synthesizeCombinationalWithParameters` | none | independent (a text/defeq check plus a grep-level census, labelled as such) |
| I5a | `specializeDesign` facts that hold without success claims: if `.ok D'` then `validateBindings` held and the top module is present (the code order, Specialize.lean:145-150); the result module list is `modules.mapM specializeModuleUnchecked` so it has the same names in the same order, `parameters = []`; `moduleByName`/`childMap` commutation on `.ok` results | none | independent (pure IR); `validateBindings` is `private` so the statement either unfolds it by a local copy checked by `rfl` or needs a visibility change (§9 U1, shared file, reviewer/user) |
| I5b | SUCCESS, separate obligation: conditions under which `specializeDesign` is `.ok`. Known failure sources even for all-positive legal θ: `DimExpr.evaluate` subtraction underflow, division/modulo by zero, `clog2 0` (Sparkle/IR/Type.lean:68-93); `requirePositive` zero width (Specialize.lean:59-61); slice `hi < lo` (:88-92). Validation also checks the WHOLE design's name set and zero values, not "top parameters in order": `validateBindings` takes the union of parameter names over `design.modules` (:36-48), so rev1's `θ.map Fst = b.parameters.map name` is neither implied by nor equivalent to legality. FG target kept: "success for all-positive θ" is NOT dropped; it needs either a proof about the produced `DimExpr`s of a symbolic run (not designed; depends on the translator) or an explicit supplied premise on the declaration, reported as conditional | none yet | NOT supplied; survey of which `DimExpr` forms the symbolic translator emits has not been done (probe P4) |
| S1 | PARAMETRIC SOURCE: define `SrcAt θ` = the declaration's value with each requested `Nat` binder instantiated by `θ`, as a `TopIface`. Per-declaration premise, same kind as G3-DECL | per declaration | needs a design choice (§6) |
| S2 | symbolic translator contract: `LegacyDom` (Tools/ShippingLegacySemContract.lean:264) extended with a `DimExpr` environment so that a translation in symbolic mode, then `evalDim θ`, agrees with the translation of the instantiated term | S1; the legacy contract is itself conditional (gap G2, ROUTE_CENSUS.md:22) | waits for the legacy route work (M4 sibling) |
| S3 | commutation: running `specializeDesign … θ (raw, D)` gives the run of the source at θ (`CombChildRunN`) | I5, S2 | independent of M3, depends on S2 |
| S4 | assembly: from the run of `synthesizeCombinationalWithParameters`, with I1-I4 and S3, conclude `ParamTopShips` for every valid θ | all above | waits for S2 and for the route producers for the children if P1 finds child modules in `D` |
| S5 | FG disjunction: `EntryShips` for both disjuncts | M3 (first disjunct), S4 (second) | waits for the route producer (M3) |

**Not accepted as completion:** a `ParamTopShips` instance for a fixed `θ`, a corpus test, a conditional S4 with S2 left as a premise without being reported as such, or a statement made vacuous by a `SrcAt` that is unsatisfiable (every step needs a concrete satisfying instance, listed separately from the general statement).

## 5. Independent work now vs. waiting for the route producer (M3)

**Independent of M3, can start once this freeze is approved** (new files only, no edit of shared definitions):
- I1, I2, I3, I4, I5 above (new file `Tools/ShippingGen4ParamEntry.lean` and a test with `#print axioms`).
- Probes, each a read-only measurement reported as such:
  - P0: census of callers/uses of `(parameters ≠ [], symbolicMode = false)` (expected none, §1.3).
  - P1: whether `D.modules` of a successful symbolic run can be non-empty, and whether the translator can emit a child inside a symbolic top (reads the translator's instance arms, `translateInstanceOrFallback`).
  - P3: whether a symbolic-mode successful run can contain input ports named `clk`/`rst` (reads `bindInputsLegacy` and `translate*` arms that call `addInput`), for I2b.
  - P4: which `DimExpr` constructors (`sub`, `div`, `mod`, `clog2`) the symbolic translator emits, for I5b.
  - P2: the list of corpus declarations that use `#synthesizeParameterizedVerilog` / `*WithParameters` (Tests/VerilogTests.lean:45, :52; Sparkle/Compiler/Elab.lean:9047-9056, 9189-9200, 9238-9252), used only to choose non-vacuity instances.

**Waits:**
- S2/S3/S4: the legacy-route semantic contract (the sibling M4 route issue) and the dimension extension of it.
- S5: the route producer of M3 (`T1Stmt`, the route-indexed `T1Hyp` amendment, which is itself UNAPPLIED per ROUTE_CENSUS.md:106-110).
- The common interface §3.2: compatible with the A-COMB `CombChildRunN`; final text is fixed once the route-indexed `T1Hyp` is accepted.

## 6. Decisions needed from the reviewer (not from the user at this stage)
1. Is `ParamTopShips` quantified over all positive θ (§3.2 (i))? Recommended: yes, since a corpus-fixed θ is not the guarantee.
2. Is `SrcAt` a per-declaration premise (like G3-DECL) or derived? Recommended: premise first, reported as conditional row by row.
3. Do I1-I5 go to one new file? Recommended: yes.
No new law, TRUSTED boundary, FG change or shared-definition edit is proposed. If S2 turns out to need the legacy contract to be strengthened or `GenWF` changed, that goes to a decision document before any work on it.

## 7. Mutants
No mutant is part of this freeze. When later units add mutants, they are rejections by signature/defeq of the checked statement, not semantic counterexamples, and will be labelled so.

## 8. Response to changes_requested (reviewer on 7c297d5f)

**R1 (I2 / clk,rst / "no Pkg").** Accepted. Withdrawn: (a) "no register/memory/inst, so no clk/rst input" (§1.5, I2): `addClockResetIfSequential` only ADDS ports and is the identity on non-sequential modules, so it does not exclude pre-existing ones; (b) "no Pkg exists" (§3.1): `Pkg.comb` exists. I2 is now limited to the guaranteed form (§4 I2); clk/rst absence is a separate I2b that waits for P3. Consequence: `CombChildRunN`'s conjuncts `"clk" ∉ inputs`, `"rst" ∉ inputs` (GEN2_DEFS.lean.txt:66-67) are NOT supplied for a symbolic top by this survey; they stay a named open obligation.

**R2 (I5 iff).** Accepted. Withdrawn: "`specializeDesign` succeeds iff validation passes" and the order-equality binding premise. Now: LegalBinding (= `validateBindings` ok; design-wide name set; nonzero values) is separated from SUCCESS; the list of post-validation failure sources is in §4 I5b with file:line. `ParamTopShips` takes success as a hypothesis. **FG is not shrunk:** the target "every positive binding specializes successfully and runs as the source" remains, split into `SpecSuccessAllPositive` (§3.2, I5b: unsupplied) and `ParamTopShips`. If I5b turns out to need a premise on the declaration, it will be reported as conditional, and if it cannot be met for some declarations the matter goes to a decision document, not into a quiet restriction.

**R3 (complete telescopes, undefined names).** Done in §9: every name used in §3.2 is listed with its definition site or marked UNDEFINED, with its supplier. Independent dispatch/shape part (I1, I3, I4, I5a, I2-restricted) is separated from the semantic interface (SrcAt, CombTopRunN, EntryShips, S1-S5), which is UNDESIGNED and not frozen. Partial evaluate/specialize kernel connection: no supplier (§9 U4).

**R3 continued (rev3, on 2030997a).** Accepted: rev2 named the statements but left I1 as an ellipsis with copy-at-implementation, I2-I5a as prose. §9.1 now gives each of I1, I2, I3a, I3b, I5a as a Lean signature with all binders, the Run/Returns boundary (`RunsTo`), and the conclusion; I3 is split into prologue (I3a), body after prologue/depth/finally-peeling (I3b) and the unfrozen depth/cache balance (I3c); I5a states what `moduleByName`/`childMap` of `D'.modules` is compared with (those of `design.modules`, by module name). The first unit is narrowed (I4 moved out). Nothing here has been elaborated by Lean yet. §9.2 stays undesigned, as accepted.

## 9. Complete types and suppliers (R3)

### 9.1 Frozen (dispatch / shape; independent of M3; PROPOSED for approval)
Five statements (I1, I2, I3a, I3b, I5a), written as Lean signatures with every binder and the conclusion. All names resolve at d0ddc50b (checked by reading, not by build; the build of the signatures is the first implementation step and any elaboration error found then goes back to the reviewer as a text correction, not a silent change). They go in the new file `Tools/ShippingGen4ParamEntry.lean`, which starts with
```lean
import Tools.ShippingEntrySoundness   -- RunsTo (:937), RunsTo.bind/ite/try_finally
import Tools.ShippingMachineLinked    -- childMap (:341); if not transitively available, add this import

namespace Tools.ShippingGen4ParamEntry
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder
open Tools.ShippingEntrySoundness
```
**Run/Returns boundary.** `RunsTo m mctx mref cctx cref w a w'` (ShippingEntrySoundness:937) means `m mctx mref cctx cref w = EST.Out.ok a w'`: the run RETURNS `a`. A throw is `EST.Out.error`, so no `RunsTo` holds. "Returns" is used only in that sense.

**I1 — the gates and the entry constant under symbolic mode or non-empty parameters (pure functions; no run).** Four conclusions about `certifiedShape?` (Elab:2316), `mixedCertifiedShape?` (:2874), `machineShape?` (:5072), `entryConst` (:5272), each with the guard `symbolicMode || !parameters.isEmpty` that the source tests:
```lean
theorem certifiedShape_off (symbolicMode : Bool) (parameters : List (String × Nat))
    (ci : ConstantInfo) (h : (symbolicMode || !parameters.isEmpty) = true) :
    certifiedShape? symbolicMode parameters ci = none

theorem mixedCertifiedShape_off (symbolicMode : Bool) (parameters : List (String × Nat))
    (ci : ConstantInfo) (isInst : Lean.Expr → Bool)
    (h : (symbolicMode || !parameters.isEmpty) = true) :
    mixedCertifiedShape? symbolicMode parameters ci isInst = none

theorem machineShape_off (symbolicMode : Bool) (parameters : List (String × Nat))
    (ci : ConstantInfo) (senv : StructEnv) (allowInsts : Bool)
    (h : (symbolicMode || !parameters.isEmpty) = true) :
    machineShape? symbolicMode parameters ci senv allowInsts = none

theorem entryConst_off (certifiedFrontEnd symbolicMode : Bool) (parameters : List (String × Nat))
    (ci : ConstantInfo) (isInst : Lean.Expr → Bool) (inl : Lean.Expr → Lean.Expr)
    (projs : StructEnv) (h : (symbolicMode || !parameters.isEmpty) = true) :
    entryConst certifiedFrontEnd symbolicMode parameters ci isInst inl projs = ci
```
(`entryConst_off`: the source's `if` has `!symbolicMode && parameters.isEmpty` as a conjunct, so under `h` it takes the `else ci` branch.) The use of these in a run — "the `machine?` guard at :5312 is false and the memo read at :5334 is skipped" — is NOT a separate Lean statement in this freeze; it is read off the run in I3b by unfolding `synthesizeFromConst`. No equation "synthesizeFromConst = legacyTail" is frozen (that needs a local specification of the tail, §9.3 U1/U4).

**I2 — `finishSynth` in symbolic mode (restricted to what the code guarantees, R1).** Argument list of `finishSynth` (Elab:2218): `(declName : Name) (parameters : List (String × Nat)) (symbolicMode : Bool) (finalCircuitState : CircuitState)`; `CircuitState` has fields `module`, `design` (Builder:21-24).
```lean
theorem finishSynth_symbolic {declName : Name} {parameters : List (String × Nat)}
    {fcs : CircuitState} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design}
    (h : RunsTo (finishSynth declName parameters true fcs) mctx mref cctx cref w (M, D) w') :
    (fcs.module.body.any fun stmt => match stmt with
        | .register .. | .memory .. | .inst .. => true
        | _ => false) = false
    ∧ (∀ p ∈ parameters, ∃ q ∈ fcs.module.parameters, q.name = p.1)
    ∧ Sparkle.IR.ModuleNameCheck.check (fcs.module :: fcs.design.modules) = true
    ∧ M = fcs.module.finalize
    ∧ D = fcs.design
```
`M = fcs.module.finalize` follows because the first conjunct gives no `.register`/`.memory`, so `addClockResetIfSequential` (Elab:2200) is the identity. Not stated: any property of `M.inputs` about `clk`/`rst` (I2b, needs P3). `Sparkle.IR.Builder.CircuitState` is reachable through `open Sparkle.IR.Builder`.

**I3 — the core wrapper, split into three parts.** The function is `synthesizeCombinationalCoreWith (translate : Lean.Environment → TranslateFn) (declName : Name) (parameters : List (String × Nat)) (symbolicMode : Bool) (certifiedFrontEnd : Bool := true) : MetaM (Module × Design)` (Elab:5423). Let
```lean
def Tsyn : Lean.Environment → TranslateFn := fun env e hn t n => translateExprToWire env e hn t n
def dupParams (parameters : List (String × Nat)) : Bool :=
  parameters.any fun (name, _) => (parameters.filter fun (other, _) => other == name).length > 1
def zeroParam (parameters : List (String × Nat)) : Bool :=
  parameters.any fun (_, v) => v == 0
```
(`dupParams` and `zeroParam` are the two tests of the prologue, Elab:5427-5433; they are new local `def`s stated in the same form as the source, and the equality with the source text is checked by the proof of I3a, not by `rfl` on a printed text.)

*I3a — PROLOGUE only (before the depth check and before any state change):*
```lean
theorem core_symbolic_prologue {translate : Lean.Environment → TranslateFn} {declName : Name}
    {parameters : List (String × Nat)} {cfe : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design}
    (h : RunsTo (synthesizeCombinationalCoreWith translate declName parameters true cfe)
      mctx mref cctx cref w (M, D) w') :
    dupParams parameters = false ∧ zeroParam parameters = false

theorem core_symbolic_prologue_throws {translate : Lean.Environment → TranslateFn} {declName : Name}
    {parameters : List (String × Nat)} {cfe : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    (h : (dupParams parameters || zeroParam parameters) = true)
    (r : Sparkle.IR.AST.Module × Design) (w' : Void IO.RealWorld) :
    ¬ RunsTo (synthesizeCombinationalCoreWith translate declName parameters true cfe)
      mctx mref cctx cref w r w'
```
*I3b — BODY after the prologue and the depth check (symbolic):* a returning run reads `ci` with `getConstInfo declName` and the environment `envR`, then runs `synthesizeFromConst` on that same `ci` (the entry constant is `ci` by `entryConst_off`) with the symbolic flags. This is the analogue of `synthesizeCombinationalCore_reads` (ShippingEntrySoundness:1090) with `parameters` and `true`:
```lean
theorem core_symbolic_reads {declName : Name} {parameters : List (String × Nat)}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design}
    (h : RunsTo (synthesizeCombinationalCoreWith Tsyn declName parameters true true)
      mctx mref cctx cref w (M, D) w') :
    ∃ (logProf : String → IO Unit) (envR : Environment) (ci : ConstantInfo)
      (w1 w2 w3 w4 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      RunsTo (synthesizeFromConst (Tsyn envR) logProf declName parameters true true ci
        (instancePredicate envR)) mctx mref cctx cref w3 (M, D) w4
```
(The existing theorem states `translateExprToWire envR e h t n` through a lambda; `Tsyn envR` unfolds to the same term.) The `finally` of the wrapper (`sparkleSynthDepth.modify (· - 1)` and the nested-cache restores, Elab:5577-5586) and the depth check (:5465) are inside the proof of I3b (peeled by `RunsTo.try_finally`); the balance of `sparkleSynthDepth` and the restoration of the caches are **I3c: NOT frozen**, no statement is fixed for them (they are statements about `IO.Ref` contents between `w` and `w'`, not designed here).

**I5a — `specializeDesign`, facts that do not mention success of the width evaluation beyond `.ok`.** `specializeDesign (design : Design) (bindings : Bindings) : Except String Design` (Specialize:145), `Bindings = List (String × Nat)`, `moduleByName (ms : List Module) (mn : String) : Option Module = ms.find? (·.name == mn)` (Machine:359), `childMap (ms : List Module) : String → Option (Module × WEnv)` (ShippingMachineLinked:341). The comparison in the commutation conjuncts is between the INPUT design `design` and the OUTPUT design `D'`, by module name and with `parameters` cleared:
```lean
theorem specializeDesign_ok_facts {design D' : Design} {bindings : Sparkle.IR.Specialize.Bindings}
    (h : Sparkle.IR.Specialize.specializeDesign design bindings = .ok D') :
    (design.findModule design.topModule).isSome = true
    ∧ D'.topModule = design.topModule
    ∧ D'.modules.map (·.name) = design.modules.map (·.name)
    ∧ (∀ m ∈ D'.modules, m.parameters = [])
    ∧ (∀ mn : String,
        (Sparkle.IR.Machine.moduleByName D'.modules mn).map (·.name)
          = (Sparkle.IR.Machine.moduleByName design.modules mn).map (·.name))
    ∧ (∀ mn : String,
        (Tools.ShippingMachineLinked.childMap D'.modules mn).map (fun c => c.1.name)
          = (Tools.ShippingMachineLinked.childMap design.modules mn).map (fun c => c.1.name))
```
The last two conjuncts compare `moduleByName`/`childMap` of the specialized module list `D'.modules` with those of the unspecialized `design.modules`, on the module NAME only (a specialized module's ports differ, and `childMap`'s second component `declWidth` of the specialized module is not compared). The proof uses that the module list is `design.modules.mapM (specializeModuleUnchecked · bindings)` and that `specializeModuleUnchecked` keeps `name` (record update `{ hardwareModule with … }`); `specializeModuleUnchecked` and `validateBindings` are `private`, so the proof destructs the `Except` bind and does not unfold them. Consequently NOT in I5a (they need `validateBindings`, §9.3 U1): "bindings are duplicate-free", "bindings are nonzero", "every declared name is bound".

**Not in the approval unit:** I4 (post-processing equality; it is a text/defeq fact between two bodies, and the reviewer already noted that text equality is not an equivalence proof — it will be restated with the semantic interface), I5b, S1-S5.

### 9.2 Not defined (semantic interface; UNDESIGNED)
| name | where used | status | supplier |
|---|---|---|---|
| `TopIface` | §3.2 | fields `bsIn/outs/S/seq` are sketches; `seq` unused by `CombChildRunN`; no theorem consumes it | undesigned (U2) |
| `CombTopRunN` | `ParamTopShips` | NOT DEFINED. Intended: `CombChildRunN (children) D' n b' bsC outsC S` with depth n and `(bsC,outsC,S)` from `SrcAt θ`. Missing: `n` (depth), `bsC` for `.domain` binders, `ResetN` start | undesigned (U2) |
| `SrcAt` | `ParamTopShips` | NOT DEFINED: "declaration's value with each parameter binder instantiated" has no definition, no supplier, no satisfiability evidence | undesigned (S1, U2) |
| `EntryShips`, `Route` | §3.2 | NOT DEFINED (`…` placeholders in rev1) | M3 route work + U2 |
| `TopShips` unchanged | `MachineTopShips` | defined (GEN2_DEFS.lean.txt:273) | exists |
| `LegalBinding` | §3.2 | defined via `validateBindings`, which is `private` (Specialize.lean:36) | U1 |
| `childMap`, `CombChildRunN`, `ResetN`, `RunOn` | | defined (ShippingMachineLinked:341, GEN2_DEFS:60, ShippingMachineDepth:52,27) | exist |

### 9.3 Open items
- U1: `validateBindings` is private; Lean statements about it need a local equivalent checked against the source or a visibility edit in `Sparkle/IR/Specialize.lean` (shared/production file: a visibility change is a request to the reviewer, not done here).
- U2: design of `TopIface/CombTopRunN/SrcAt/EntryShips`. Not designed in this freeze; no implementation until designed and approved.
- U3: which conclusion type a symbolic top gets (new definition vs `Pkg.comb`-based `TopShips`).
- U4: partial evaluation / specialization kernel connection: this survey did not find a definition connecting `specializeDesign` output to `runModuleTG`/`RunOn` semantics or to the source-level instantiation. Unsupplied.
- U5: RESOLVED in rev3 by §9.1 (full signatures). Remaining: elaboration of those signatures at the first build; if a name does not resolve, that is reported as a text correction.

## 10. Revised decisions for the reviewer
Replaces §6 items 1-3: (1) approve §9.1 as the only implementable unit now (I1, I2-restricted, I3a, I3b, I5a; I4 is moved out, I3c is not frozen); (2) §9.2/§9.3 stay unapproved, designed next after P3/P4; (3) U1 visibility: approve a local copy or request the edit.

## 11. rev4: P4 survey, I3c, I4, and the semantic interface (§9.2)

Base for this section: 8acc71dd. I1/I2/I3a/I3b/I5a are built and approved at that SHA (scoped approval; not the Issue). Everything below is PROPOSED. Words: "this survey did not find X" means the listed sources were read and X was not there; it never says X is impossible or not derivable. A "mutant" in this repository is a rejection by signature/defeq of the checked statement, not a semantic counterexample.

### 11.1 P4: which `DimExpr` forms a symbolic run can hand to `specializeDesign`, and what `.ok` needs

**Sources read.** `DimExpr` constructors, `mk*` smart constructors and `evaluate` (Sparkle/IR/Type.lean:20-32, 43-62, 68-93, `hwTypeFromDim` :200-203); the only producer, `extractDimExprStep` (Sparkle/Compiler/Elab.lean:632-687); the other places that build a `DimExpr` (Elab:709, :858 `makeSliceFromStartLength`, :864-880 `lowerZeroExtendWire`; callers of `extractDimExpr` at :5889-5890, :5901, :7222-7233, :7578-7591); the consumers of a `DimExpr` in `specializeDesign` (Sparkle/IR/Specialize.lean:56-64 `specializeType`, :73-91 `specializeExpr` `sliceDim`, :111-130, :145-150). `grep` over `Sparkle/` and `Tools/` for `DimExpr`, `bitVectorDim`, `clog2`, `log2` outside Elab/Type/Specialize found uses only in the backends (Verilog.lean:53 emits `$clog2`; CSim.lean:102,112 reject), the optimizer passes (which pass `sliceDim` through unchanged) and ReorderInvariance/RegDedup (structural).

**Constructors the translator can emit (file:line).**
| constructor | emitted by | how |
|---|---|---|
| `literal` | `extractDimExprStep` :636 (`.lit (.natVal v)`); `mkAdd/mkSub/mkMul` constant folding Type.lean:43-62; `makeSliceFromStartLength` :858 (`.literal 1`) | closed constants |
| `parameter` | `extractDimExprStep` :637-645 via `dimVarMap`, filled by `bindInputsLegacy` :2115-2128 (`.parameter binderName`) | a retained `Nat` binder; an `fvar` not in the map throws (:641-645) |
| `add` | `mkAdd` through `Nat.add`, `Nat.succ`, `HAdd` (:657, :665-666, :674); Prod width :709; `makeSliceFromStartLength` :858 | |
| `sub` | `mkSub` through `Nat.sub`, `HSub` (:658, :675); `makeSliceFromStartLength` :858 (`(start+len) - 1`) | both user-written subtraction AND the translator's own slice bound |
| `mul` | `mkMul` through `Nat.mul`, `HMul` (:659, :676) | |
| `div`, `mod`, `pow`, `min`, `max` | `extractDimExprStep` :660-664, :677-679 (raw constructors, no smart folding) | user-written `/ % ^ min max` in a width |
| `clog2` | **this survey did not find a translator path that emits it.** Only Type.lean (definition, `evaluate`, `toString`) and the Verilog backend mention it. Source forms outside the list (e.g. `Nat.log2`) hit the `Unsupported symbolic hardware dimension` `throwError` (:683-687), i.e. the symbolic run FAILS; it is outside the success scope | |

Where a `DimExpr` reaches the specializer: (a) a port/wire type `.bitVectorDim d` (made by `hwTypeFromDim`, Type.lean:200-203, only when `d` is not a `.literal`) → `specializeType` :60-62; (b) a `sliceDim` bound pair → `specializeExpr` :84-89. A `.literal` width is concrete (`hwTypeFromWidth`) and is never evaluated, so a literal 0 is not rejected by `requirePositive`.

**The checks that can make `specializeDesign` return `.error` after `validateBindings` passed** (Specialize.lean + Type.lean:68-93): (E1) `.sub` underflow, (E2) `.div`/`.mod` with divisor evaluating to 0, (E3) `.clog2 0`, (E4) `requirePositive`: a `.bitVectorDim` evaluating to 0 (:49-51, :62), (E5) `sliceDim` with `hi < lo` after evaluation (:87-88). `pow`, `add`, `mul`, `min`, `max` have no error branch in `evaluate` (:77-90).

**Partition.** Let `θ` be a legal binding with every value `≥ 1` and `e` a `DimExpr` the translator produced.
1. **Provable for all-positive θ (no declaration premise), by structural induction on `e`** — class `Pos⁺`: `e` is built only from `parameter`, `literal c` with `c ≥ 1`, `add`, `mul`, `pow`, `min`, `max`, where every leaf evaluates `≥ 1`. Then `evaluate θ e` is `.ok v` with `v ≥ 1` (no error branch is reachable: E1-E3 need `sub/div/mod/clog2`; E4 needs `v = 0`, but `add/mul/min/max/pow` of `≥ 1` values are `≥ 1`). For a slice from `extractLsb' start len` whose `start ∈ Pos⁺ ∪ {literal 0}` and `len ∈ Pos⁺`: the translator's bound is `hi = (start + len) - 1` (:858): `start + len ≥ 1`, so no underflow (E1), and `hi ≥ lo = start`, so E5 does not fire. (This is a statement about the `DimExpr` values; the induction is not designed or proved here.)
2. **Needs a premise on the declaration (CONDITIONAL):** any width containing a user-written `sub`, `div` or `mod` (or a `min/max/pow/add/mul` that has one inside): the translator keeps them as `.sub/.div/.mod` nodes, and the specializer's behavior depends on θ. Code-reading example (not run): `BitVec (n - 1)` with retained `n` gives a wire of type `.bitVectorDim (.sub (.parameter "n") (.literal 1))`; the legal binding `n ↦ 1` evaluates it to 0 and `specializeType` throws via `requirePositive` (E4). Likewise `n - 5` at `n ↦ 1` throws underflow (E1), where the source `Nat` subtraction would truncate to 0. In both the specializer fails closed. So for such a declaration `SpecSuccessAllPositive` (§3.2) is FALSE as stated, by reading; the true form is `∀ θ in a region R_decl, ok`, with R_decl a premise (for `n - 1` as a width: `n ≥ 2`). This is a statement about which θ succeed, not a counterexample to `ParamTopShips` (which takes success as a hypothesis, §3.2).
3. **Not found:** a supply path for (a) the symbolic run's `D.modules` carrying parameter-bearing child modules with their own widths (probe P1, still not read); (b) a derivation that a `Pos⁺` width stays `Pos⁺` after the zero-width/merge post-processing (§11.3); (c) `clog2` (not emitted, so no case).

**Consequence for FG; nothing is dropped.** The target "all-positive θ ⇒ specialization succeeds" is KEPT in §3.2 as `SpecSuccessAllPositive`. rev4 refines the status of I5b into two obligations:
- **I5b-pos (supplied class):** for a declaration whose emitted widths and slice bounds are all in `Pos⁺`, `SpecSuccessAllPositive` holds. Statement shape (types in §11.5): `PosPlus b D → SpecSuccessAllPositive b D`, where `PosPlus` is a decidable predicate on the module/design (every `.bitVectorDim d` and `.sliceDim _ hi lo` has `d` / `hi` / `lo` in the shapes above).
- **I5b-cond (conditional class):** for any other declaration the success region is a premise `Region b D R` and the claim is `∀ θ legal, R θ → ok`. This is a CONDITIONAL guarantee and every report that cites it must say so.
Whether I5b-cond is a reduction of the guarantee the user approved depends on reading FG (GENERAL_SPEC.md:88-100, :478-483 says only "the parametric quantification" is fixed in M4); the decision material is `scripts/gen4/PARAMETRIC_SPECSUCCESS_DECISION.md`. The freeze does NOT choose; no implementation of I5b-cond starts before the decision.

### 11.2 I3c: depth balance and nested-cache restoration (full types)

**What the wrapper does (Elab:5464-5586).** Read `depth` (:5464); if `depth ≥ sparkleSynthDepthLimit` throw (:5465-5466); save 7 side maps (depth `0`: `{}`; else the ref contents) (:5479-5535); depth `0` clears the type/sub-module/child/side caches, else resets only the side maps (:5536-5560); `sparkleSynthDepth.set (depth+1)` (:5561); `try doSynth finally { depth.modify (·-1); if depth ≠ 0 then restore the 7 side maps }` (:5574-5586). In symbolic mode the prologue (`throwError` on duplicate/zero) runs BEFORE all of this (:5427-5435, I3a).

**What the existing development gives, and for which flags.** Every lemma below is stated for the DEFAULT flags `[] false` (verified by reading the statements); none is stated for `parameters`/`true`.
| need | existing statement (file:line) | usable for symbolic? |
|---|---|---|
| finally: depth back to `D`, 7 maps set | `fin_triple`, Tools/ShippingChildKeeps.lean:344-372 — a `Triple` from `J L (D+1)` to `J L D` for the `finally` text; it does not mention `parameters`/`symbolicMode` | **yes, as is** (the `finally` block is the same text) |
| core keeps `J L D` given the body keeps `J L (D+1)` | `core_keeps`, ShippingChildKeeps.lean:385 (`synthesizeCombinationalCore declName [] false`) | pattern only: the `unfold … simp only [Bool.false_eq_true, ↓reduceIte]` step removes the `if symbolicMode` prologue, which for `true` is a real prefix (I3a) |
| the body at depth `D` for the default flags | `body_keeps`, Tools/ShippingChildBody.lean:142-150 (`synthesizeFromConst … declName [] false true ci isInst`); uses `bindInputsLegacy_keepsC` which is stated for `bindInputsLegacy [] false` (:76-84) | **no**: needs a symbolic copy. This survey found keeps lemmas for `extractDimExpr` (Tools/ShippingChildHelpers.lean:102-103; ShippingChildLegacyHelpersA.lean:121-122) but did not find one for `CompilerM.addParameter` or `withDimVarMapping` (`grep` over Tools/: no hit); they are `CompilerM` state operations with no `IO.Ref` write (Elab:119-126, :298-306), so a keeps lemma for them would be a state-only proof, not a new law |
| outermost balance for every outcome | `core_triple0`/`core_balance`, Tools/ShippingChildBalance.lean:211, :315 (`Out0 L` → `Out0 L`, also on exceptions; `Out0` :103) | pattern + the symbolic body lemma; the proof walks the same prefix |
| outermost core from `JQ O.quiet 0` to `JQC O 0` | `core0_tripleAC`, Tools/ShippingChildDepthC.lean:218 (premise `hbodyC`) | same: needs `hbodyC` for the symbolic body |
| LimitStmt (depth limit throws, no run) | scripts/gen2/T1_CONNECT_FREEZE.md:38-43 (`LimitStmt`, discharged by the prefix of `core_tripleAC`) | statement is for `[] false`; the symbolic analogue is needed only if a symbolic run can be started at depth ≥ limit, which this survey did not find (no caller below the outermost, §11.3) |
| equality of the 7 side maps' CONTENTS between `w` and `w'` | **this survey did not find a lemma.** `RefLaws` (Tools/ShippingChildInv.lean:333-420) tracks only three values (child cache `val`, synthesis ref `sval`, depth `dval`); the seven maps are written through `Framed.sideSet` and appear in `J` only through the three values (`fin_triple` :344 states nothing about their contents) | not needed for the outermost symbolic run (below) |

**Scope decision (a proposal, reviewer may reject).** A symbolic run is started only by commands (Elab:9056, :9127) and tests (Tests/VerilogTests.lean:45,52; Tests/TestCppSim.lean:146), i.e. OUTERMOST (depth 0); its children use the default entry (§1.4). At depth 0 the `finally`'s `if depth != 0` (:5579) is false, so no restoration of the 7 maps happens for the top run, and the nested-restoration equality (last row) is not a premise of any parametric statement. It stays needed ONLY for the default entry's nested runs, which are M3's. So I3c freezes depth `D = 0` for the world facts and `D` general for the `J`-keeping statement.

**Frozen types (names new, in `Tools/ShippingGen4ParamEntry.lean`'s successor file, see §12).** `Tsyn`, `profLogIO`, `J`, `ChildKeeps`, `Keeps`, `Out0`, `StartV`, `RefLaws` as in Tools/ShippingChildInv.lean and ShippingChildBalance.lean. Variables: `mctx mref cctx cref` as in those files.
```lean
-- (I3c-body) the symbolic body keeps the invariant, given the child entry does.  Supplier: a copy of body_keeps
-- (ShippingChildBody:142) with bindInputsLegacy_keepsC generalised to (parameters, symbolicMode); STOP rule: if a
-- primitive needs a new RefLaws field, report and do not add a law.
theorem body_symbolic_keeps (L : RefLaws mref cref) (D : Nat) (hC : ChildKeeps L D)
    (b : Bool) (declName : Name) (parameters : List (String × Nat))
    (ci : ConstantInfo) (isInst : Lean.Expr → Bool) {tenv : Lean.Environment} :
    Keeps mctx mref cctx cref (J L D)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName parameters true true ci isInst)

-- (I3c-keeps) the core wrapper keeps J at depth D given the body keeps it at D+1 (core_keeps, ShippingChildKeeps:385)
theorem core_symbolic_keeps (L : RefLaws mref cref) (D : Nat) (declName : Name)
    (parameters : List (String × Nat)) (hA0 : D = 0 → L.aux {})
    (hbody : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (J L (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName parameters true true ci isInst)) :
    Keeps mctx mref cctx cref (J L D)
      (synthesizeCombinationalCoreWith Tsyn declName parameters true true)

-- (I3c-worlds) connection to I3b at depth 0: the worlds w3 (body start) and w4 (body end) of core_symbolic_reads
-- have the invariant at depth 1, and the end world has it at depth 0.
theorem core_symbolic_worlds (L : RefLaws mref cref) (hA : L.aux {}) {declName : Name}
    {parameters : List (String × Nat)} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design}
    (hw : Out0 L w)
    (hbody : ∀ {tenv : Lean.Environment} (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (J L 1)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName parameters true true ci isInst))
    (h : RunsTo (synthesizeCombinationalCoreWith Tsyn declName parameters true true)
      mctx mref cctx cref w (M, D) w') :
    ∃ (logProf : String → IO Unit) (envR : Environment) (ci : ConstantInfo)
      (w1 w2 w3 w4 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      RunsTo (synthesizeFromConst (Tsyn envR) logProf declName parameters true true ci
        (instancePredicate envR)) mctx mref cctx cref w3 (M, D) w4 ∧
      J L 1 w3 ∧ J L 1 w4 ∧ J L 0 w'

-- (I3c-balance) outermost balance on every outcome, for any witness (core_balance, ShippingChildBalance:315)
theorem core_symbolic_balance (L : RefLaws mref cref) (declName : Name)
    (parameters : List (String × Nat)) {w : Void IO.RealWorld}
    (hs : StartV L w) (hq : L.quiet w) (hd : L.dval w = 0) :
    Out0 L (endW mctx mref cctx cref
      (synthesizeCombinationalCoreWith Tsyn declName parameters true true) w) ∧
    ErrOk mctx mref cctx cref
      (synthesizeCombinationalCoreWith Tsyn declName parameters true true) w
```
(`core_symbolic_worlds` states `J L 1 w3`: `J` also needs `CacheInv` of the CLEARED cache, which the clear establishes (`tripleO_clear`, ShippingChildBalance:182); `w1,w2,w5,w6` are existential as in I3b because I3b's conclusion does not constrain them. The prologue's `throwError`s are exceptions in the class `OkExc`: that is the `.str`/`.fmt` message form `tripleO_throwErr` already handles.)

**Not frozen / not claimed:** the 7-map content equality `w → w'` for a NESTED symbolic run; a symbolic run at depth ≥ 1; `LimitStmt` for symbolic flags.

### 11.3 I4: post-processing, restated as a semantic interface

**Why rev3 moved I4 out.** A text equality between the two entries' post-processing (§1.1) is a fact about two programs, not an equivalence proof of the produced module (the reviewer's point). rev4 therefore splits I4 into a STRUCTURE part and a SEMANTIC part and says what each does and does not give.

**I4-struct (decomposition; the analogue of an existing theorem).** For the default entry, Tools/ShippingDesignWriterRun.lean:69-100 (`synthesizeCombinational_designTop`) already states: a returning run of the full entry is a returning run of the core followed by `M' = dropZeroWidthModule M ∨ M' = mergeChecked (dropZeroWidthModule M)`, `D'.topModule = D.topModule`, and `D'.modules = D.modules` when no module of `D` is named `M.name`. The parametric entry has the same post-processing text (Elab:8940-8953 vs :5592-5606), so the same statement is proposed, with the symbolic core:
```lean
theorem synthesizeCombinationalWithParameters_designTop {declName : Name}
    {parameters : List (String × Nat)} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design}
    (h : RunsTo (synthesizeCombinationalWithParameters declName parameters)
      mctx mref cctx cref w (M', D') w') :
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCoreWith Tsyn declName parameters true true)
        mctx mref cctx cref w (M, D) w1 ∧
      (M' = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        M' = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      D'.topModule = D.topModule ∧
      ((∀ x ∈ D.modules, x.name ≠ M.name) → D'.modules = D.modules)
```
It says WHICH `b` can come out of WHICH `raw`. It does not say that `b` behaves like `raw`.

**I4-sem (the interface-level transfer; this is what the consumer needs).** `ParamTopShips` (§3.2) is a statement about `b` and `D`, the post-processed pair. The translator contract S2 (§4) is about `raw`. The bridge must be an interface statement, not a text one:
```lean
-- TopIface, CombTopRunN: §11.5.  raw/b/Dr/D as in I4-struct.
def PostTransfer (raw b : Sparkle.IR.AST.Module) (Dr D : Design) (I : TopIface) : Prop :=
  ∀ (θ : List (String × Nat)) (Dr' D' : Design),
    Sparkle.IR.Specialize.specializeDesign (Dr.addModule raw) θ = .ok Dr' →
    Sparkle.IR.Specialize.specializeDesign (D.addModule b) θ = .ok D' →
    ∀ (n : Nat) (raw' : Sparkle.IR.AST.Module), Dr'.findModule raw.name = some raw' →
      CombTopRunN Dr' n raw' I →
      ∃ b', D'.findModule b.name = some b' ∧ CombTopRunN D' n b' I
```
`PostTransfer` is a PROPOSITION to be proved per post-processing outcome, not an assumption: it follows from soundness of `dropZeroWidthModule` and `mergeChecked` for symbolic modules. Existing results: `dropZW_name` (Tools/ShippingMachineDepthRun.lean:98) and `dropZeroWidth_name` (ShippingGateChildComb.lean:131) give `b.name = raw.name`; soundness of the two passes is stated in Tools/ShippingPostSoundness.lean (`dropZeroWidth_entry` :519) and in the `mergeChecked_*` lemmas (e.g. Tools/ShippingCombKidText.lean:198, ShippingChecksDerived2.lean:243) for the module shapes of the default routes. **This survey did not find** a soundness statement of these passes for a module whose widths are `.bitVectorDim` or that contains `.sliceDim` (the optimizer passes carry `sliceDim` through, e.g. Sparkle/IR/Optimize.lean:235, :351, :629, but no theorem was found about it), and the specialize-then-run composition has no kernel definition (U4). Status: UNSUPPLIED; the reviewer's remark (text equality is not equivalence) is applied by making `PostTransfer` the only thing S4 may cite, never I4-struct alone.

**I4-census (not a proof).** The claim "the translator does not call `synthesizeCombinationalWithParameters`" has two supports of different kinds, and neither is a Lean theorem about the translator:
- *Census:* `grep -rn synthesizeCombinationalWithParameters` over the repository `*.lean` finds the definition (Elab:8940), command elaborators (Elab:9056, :9127), `Tests/VerilogTests.lean:45,52` and `Tests/TestCppSim.lean:146`; none is inside the translator block (which ends before :8917).
- *Lean's declaration order:* a constant's body can only mention constants that already exist when it is added, and `translateExprToWire`/`synthesizeChild` (:8929) are defined before :8940. This is a metatheoretic argument, not checked by this repository. A kernel-level check (the constant-closure of `translateExprToWire`/`synthesizeChild` does not contain the name) would use the `Tests/Gen4/ParamEntryCheck.lean` closure detector, which does not follow `opaque`/`partial` bodies (logged as untracked at 8acc71dd); so even that check would be partial.
Both are recorded as evidence, not as I4. The proof-relevant consequence is the §11.2 scope decision (outermost only).

### 11.4 Status of I1-I5 after rev4
| item | status |
|---|---|
| I1, I2, I3a, I3b, I5a | built and scoped-approved at 8acc71dd |
| I3c (body, keeps, worlds, balance) | frozen by §11.2 for approval; implementation may need a symbolic copy of `bindInputsLegacy_keepsC` |
| I4-struct | frozen by §11.3 for approval; analogue exists for the default entry |
| I4-sem (`PostTransfer`) | statement frozen (§11.3, §11.5); UNSUPPLIED (soundness of the passes on symbolic modules, U4) |
| I5b-pos / I5b-cond | statements in §11.5; supply of I5b-pos: structural induction over `DimExpr`, pure, independent; I5b-cond: waits on the decision document |

### 11.5 §9.2 completed: the semantic interface (full types) and the supplier table

**Design principles.** (1) Reuse the A-COMB interface instead of a new one (§3.2 preference). (2) `SrcAt` is a per-declaration premise of the same kind as G3 (`ReflectsAll`), reported as conditional. (3) The top-level conclusion for the second disjunct of FG is NOT the machine `TopShips` (it needs `p.d.ss`, `ResetNk`, `"clk"`/`"rst"` equations; §3.1). It is `ParamTopShips`, defined over `CombTopRunN`. (4) Nothing in FG, `T1Hyp`, `GenWF` or a shared definition changes; this is the "parametric quantification" that GENERAL_SPEC.md:478-483 assigns to M4.

```lean
-- Imports/opens: as §9.1 plus Tools.ShippingGen2Defs (CombChildRunN), Tools.ShippingMachineDepth (ResetN, RunOn).
-- The interface DATA of A-COMB (GEN2_DEFS.lean.txt:60-74): the `seq` field of the rev1 sketch is dropped (unused).
structure TopIface where
  bsC   : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)
  outsC : List Sparkle.IR.Machine.OutField
  S     : (Nat → List Nat) → List (Nat → Nat)

/-- The source at a binding: per declaration.  A PREMISE of the same kind as G3, not a derived object. -/
abbrev SrcAt := List (String × Nat) → TopIface

/-- A parametric top at depth n, after specialization.  Reuse of the A-COMB combinational child run. -/
def CombTopRunN (D' : Design) (n : Nat) (b' : Sparkle.IR.AST.Module) (I : TopIface) : Prop :=
  CombChildRunN (Tools.ShippingMachineLinked.childMap D'.modules) D' n b' I.bsC I.outsC I.S

/-- LegalBinding: §3.2, via validateBindings (private: §9.3 U1; the local specification is checked against the
    function by kernel unfolding of the total definition, as I5a does for specializeModuleUnchecked). -/
def LegalBinding (D : Design) (θ : List (String × Nat)) : Prop := …  -- text of §3.2, unchanged

def SpecOk (D : Design) (θ : List (String × Nat)) : Prop :=
  ∃ D', Sparkle.IR.Specialize.specializeDesign D θ = .ok D'

/-- The guarantee for the parametric disjunct.  Success is a HYPOTHESIS here (§3.2), not an assumed consequence
    of legality.  `n` is existential, as in `TopShips` (`∃ p n`). -/
def ParamTopShips (b : Sparkle.IR.AST.Module) (D : Design) (SrcAt : SrcAt) : Prop :=
  ∀ θ, LegalBinding (D.addModule b) θ →
    ∀ D', Sparkle.IR.Specialize.specializeDesign (D.addModule b) θ = .ok D' →
      ∃ n b', D'.findModule b.name = some b' ∧ CombTopRunN D' n b' (SrcAt θ)

/-- Separate supply obligation, KEPT (not shrunk): §3.2 SpecSuccessAllPositive, with its class split of §11.1. -/
def SpecSuccessAllPositive (b : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∀ θ, LegalBinding (D.addModule b) θ → SpecOk (D.addModule b) θ

def PosPlus (b : Sparkle.IR.AST.Module) (D : Design) : Prop := …   -- decidable, §11.1 class 1; fixed at implementation
                                                                    -- as a Bool function over ports/wires/sliceDim
def Region (b : Sparkle.IR.AST.Module) (D : Design) (R : List (String × Nat) → Prop) : Prop :=
  ∀ θ, LegalBinding (D.addModule b) θ → R θ → SpecOk (D.addModule b) θ      -- I5b-cond (decision pending)

/-- FG for the two entries, as ONE statement with the parametric quantification (GENERAL_SPEC §M4 deliverable).
    The first conjunct is FG's default part exactly as written (the T1Stmt conclusion); the second replaces the
    conclusion of FG's second disjunct by ParamTopShips. -/
def EntryShips (L : Laws mref cref) (SrcAtOf : Name → List (String × Nat) → SrcAt) : Prop :=
  (∀ declName mctx cctx w b D w' (raw : Module),
      <default-entry hypotheses of FG, GENERAL_SPEC.md:88-93> → ∃ p n, Pk declName = some p ∧ TopShips p n declName b raw D) ∧
  (∀ declName parameters mctx cctx w b D w',
      Start L mctx cctx w →
      RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D) w' →
      ReflectsAll L declName parameters →
      ParamTopShips b D (SrcAtOf declName parameters))
```
`EntryShips` above is the schema to be elaborated in the assembly unit (the `<…>` stands for GENERAL_SPEC.md:88-93 verbatim and is the only placeholder left in §9.2; it is not frozen for implementation here). The obligations S1-S5 become:
| id | exact statement | premises | supplier |
|---|---|---|---|
| S1 | `SrcAtOf declName parameters : SrcAt` is defined for a reached declaration | per declaration (G3-like) | **unsupplied** (no definition of "the declaration instantiated at θ" found) |
| S2 | translator contract: for the run's `raw` and the module after specialization, `evalDim θ` of the symbolic translation equals the translation of the instantiated term; type: `∀ θ …, specializeDesign (Dr.addModule raw) θ = .ok Dr' → ∃ n raw', Dr'.findModule raw.name = some raw' ∧ CombTopRunN Dr' n raw' (SrcAt θ)` | S1; legacy contract (gap G2, ROUTE_CENSUS.md:22); U4 | **dependency pending**: legacy route issue; and the specialize/evaluate kernel link (U4) |
| S3 | the commutation: from S2 (at `raw`) and `PostTransfer raw b Dr D (SrcAt θ)` conclude the `b`-statement; type = `ParamTopShips b D SrcAt` from S2, `synthesizeCombinationalWithParameters_designTop` and `PostTransfer` | S2, I4-struct, I4-sem | pending (I4-sem unsupplied) |
| S4 | assembly: `ParamTopShips` for every successful run | I1-I3c, I5a, S3, `Start` | pending S3 |
| S5 | `EntryShips` | S4 and M3's first disjunct (T1) | pending M3 route producer and the gate/fallback producer |

**Supplier table (existing / writable now / waiting / unsupplied).**
| name | status | supplier / source |
|---|---|---|
| `CombChildRunN`, `ResetN`, `RunOn`, `childMap`, `moduleByName` | existing | GEN2_DEFS.lean.txt:60-74; Tools/ShippingMachineDepth.lean:27,52; ShippingMachineLinked.lean:341; Machine.lean:359 |
| `TopShips` (default) | existing, being revised by S2 R-G | Tools/ShippingGen2Defs.lean:273; revision `kjob/g2tc-s2` fa84af5d (TOP_CONTRACT_REVISION.md, TOP_CTRL_FREEZE.md); see "Alignment" below |
| `TopIface`, `SrcAt`, `CombTopRunN`, `SpecOk` | writable now (definitions only; no claim) | new file, depends on nothing unbuilt |
| `LegalBinding` | writable now as a local specification, kernel-checked against `validateBindings`'s total definition (as I5a did) | §9.3 U1; no visibility edit |
| `PosPlus`, I5b-pos | writable now (pure `DimExpr`/IR induction), independent of M3 | §11.1 |
| `Region`, I5b-cond | waits for the decision document | PARAMETRIC_SPECSUCCESS_DECISION.md |
| I3c-keeps/-worlds/-balance, `body_symbolic_keeps` | writable now, may stop at a missing keeps lemma (§11.2 STOP rule) | ShippingChildKeeps/Balance/Body patterns |
| I4-struct | writable now | analogue ShippingDesignWriterRun.lean:69 |
| I4-sem (`PostTransfer`) | unsupplied | post-processing soundness on symbolic modules not found (§11.3) |
| `SrcAtOf` (S1) | unsupplied | no definition found |
| S2 | waits on the legacy-route (G2) work and on U4 | ROUTE_CENSUS.md:22 |
| S3, S4 | wait on S2/I4-sem | |
| `EntryShips`, S5 | wait on the M3 route producer, the M4 gate/fallback producer (routes 1, 2, 4, 5 in ROUTE_CENSUS.md) | the gate/fallback producers are the sibling M4 issues; parametric is route 7 and routes there only to the legacy tail (§2) |

**Alignment with S2 R-G (`sparkle-gen2-top-contract`, review; `kjob/g2tc-s2` fa84af5d).** R-G changes only the machine `TopShips` antecedents: `("rst" ∈ b.inputs.map (·.name) → ∀ t, ins t "rst" = 0)` and the same for `"clk"` (TOP_CONTRACT_REVISION.md §2; `kjob/g2tc-s2:scripts/gen2/GEN2_DEFS.lean.txt:292-293`), making the top contract informative for clock-free modules. Consequences for this freeze: (1) `ParamTopShips` is not built on machine `TopShips` and so is unaffected by R-G, which is why §11.5 does not depend on whether R-G lands; (2) the clock-free half of FG's FIRST disjunct is where R-G matters, and a symbolic top, being clock-free-or-not undecided (probe P3, I2b), is deliberately NOT forced into `TopShips`; (3) `CombChildRunN` requires `"clk" ∉ inputs ∧ "rst" ∉ inputs` (GEN2_DEFS.lean.txt:66-67), which for a symbolic top is exactly the unsupplied I2b: if probe P3 finds a symbolic top that can have a `clk`/`rst` input, `CombTopRunN` would not hold for it and the right conclusion would be an R-G-style guarded variant of the run; this is recorded as an open design branch (U3), not decided; (4) if R-G or a later shared revision changes `CombChildRunN`, `CombTopRunN` follows by definition (it is `CombChildRunN`), and S2/S3 must be re-read.

### 11.6 Not claimed in rev4
- No statement of §11 has been elaborated by Lean; signatures were written from the cited sources by reading (any elaboration error found at implementation time is returned as a text correction).
- The P4 partition is a reading of the code; the `BitVec (n - 1)` failure at `n ↦ 1` is a code-reading example, not a run.
- That the DimExpr induction (class `Pos⁺`) is provable is a plan, not a result.
- Nothing here shows that `SrcAt` is satisfiable for any declaration, that S2 is provable, or that `PostTransfer` holds.
- Not changed: FG, `Laws`, `T1Hyp`, `GenWF`, any TRUSTED boundary, any shared or production file.

## 12. What the reviewer is asked to decide on rev4
1. Approve for implementation (new files only, with a Check): §11.2 (I3c body/keeps/worlds/balance), §11.3 I4-struct, and the pure definitions of §11.5 (`TopIface`, `SrcAt`, `CombTopRunN`, `SpecOk`, `LegalBinding` as a kernel-checked local specification), plus I5b-pos (`PosPlus` and `PosPlus → SpecSuccessAllPositive`).
2. The outermost-only scope of I3c (§11.2) and the definition of `EntryShips` as a two-conjunct statement (§11.5).
3. Note, no approval requested: I5b-cond and the choice of `Region` are with the user (decision document); I4-sem, S1-S5 are not frozen for implementation.

## 13. rev5: what was built, the corrected I5b plan, PosPlus in full, and the open links one per row

Base: 3682b80b (kjob/g4par-r6; implementation of §11.2 / §11.3 / §11.5 pure definitions). Words: "this survey did not find X" means the listed sources were read and X was not there; it never says X is impossible or not derivable. A "mutant" here is a rejection by signature/defeq of the checked statement, not a semantic counterexample. Nothing in this section changes FG, `Laws`, `T1Hyp`, `T1HypND`, `GenWF`, a TRUSTED boundary, or a shared/production file.

### 13.1 Built in a pod at 3682b80b (clean issue-linked build is the coder's; not yet done)
Files: `Tools/ShippingGen4ParamIface.lean`, `Tools/ShippingGen4ParamKeeps.lean`, check `Tests/Gen4/ParamIfaceCheck.lean` (TYPE = isDefEq to an independent copy; MUTANT = signature/defeq rejections; AXIOMS; CLOSURE with explicit `thmInfo.value`/`defnInfo.value` fetch, opaque bodies logged as untracked, proof-only direct and other-namespace-helper negative fixtures and clean controls). Pod build `kjob lake build Tests.Gen4.ParamIfaceCheck` exit 0 before the commit (a pod build, not a clean issue-linked build).
| item | statement | what it is NOT |
|---|---|---|
| I4-struct `synthesizeCombinationalWithParameters_designTop` | a returning run of the parametric entry is a returning run of `synthesizeCombinationalCoreWith Tsyn declName parameters true true` followed by `dropZeroWidthModule` (or `mergeChecked` of it); `D'.topModule = D.topModule`; `D'.modules = D.modules` when no module of `D` is named `M.name` | not an equivalence of `b` and `raw` (that is `PostTransfer`, unsupplied) |
| I3c `body_symbolic_keeps` | the symbolic `synthesizeFromConst` keeps `J L D`, given `ChildKeeps L D`; proved by the same `vc` walk as `body_keeps` with `bindInputsLegacy_sym_keepsC` (parameters, symbolicMode general); no new `RefLaws` field was needed | for the `RefLaws` witness only |
| I3c `core_symbolic_keeps` | the symbolic core keeps `J L D` given the body keeps `J L (D+1)`; the prologue (duplicate/zero throws, per-parameter loop) is handled by `Triple.forIn_list` and `throwErr` | |
| I3c `core_symbolic_triple0`, `core_symbolic_balance` | from `Out0` / `StartV`+quiet+depth 0: every outcome ends in `Out0`, exception in the class | outermost only; `RefLaws` witness |
| I3c `core_symbolic_worlds` | the peeled run of I3b, with `J L 1 w3`, `J L 1 w4`, `J L 0 w'` (proved by pushing the invariant through each `RunsTo` step: `RunsTo_bind_inv`) | premises `Out0 L w` and the depth-1 body keeps; not linked to a `Start` of FG (row F1) |
| definitions `TopIface`, `SrcAt`, `CombTopRunN`, `LegalBinding`, `SpecOk`, `ParamTopShips`, `SpecSuccessAllPositive`, `PostTransfer` | as §11.5, with `LegalBinding D θ` literally `validateBindings D.modules θ = .ok ()` (the private function named by its mangled constant; checked by `specializeDesign_ok_legal`: a successful specialization is legal) | definitions only: no claim that `SrcAt` is satisfiable, `PostTransfer` holds, or any specialization succeeds |
Correction found while writing the definitions: `specializeDesign` checks that the top module is present BEFORE `validateBindings` (Specialize.lean:146-148), so "every legal binding specializes" cannot be stated without a premise on the top module. `SpecSuccessAllPositive` now carries `((D.addModule b).findModule (D.addModule b).topModule).isSome = true →` (rev4 §11.5 omitted it; the definition is the only place affected, no theorem used it).
Not claimed: nested symbolic run, depth ≥ 1, `LimitStmt` for symbolic flags, equality of the seven side-map contents between `w` and `w'`.

### 13.2 I5b: the plan of rev4 was not sufficient; two layers, only the first is writable
Facts (file:line): `DimExpr.evaluate` is `partial def` (Sparkle/IR/Type.lean:68); `specializeType` is `partial def` (Specialize.lean:56) and `specializeExpr` is `partial def` (:75). The Check log at 3682b80b lists `Sparkle.IR.Specialize.specializeExpr` and `Sparkle.IR.Specialize.specializeType` among the constants whose bodies are not visible to the closure detector (opaque, type only). `specializeStmt`, `specializeModuleUnchecked`, `specializeDesign` are total but call these. I5a worked because it only used the bind structure of the total functions and never inspected a result of a partial call.
- **Layer A (model).** A total, structural model `evalM : List (String × Nat) → DimExpr → Except String Nat` (and models of `specializeType`, `specializeExpr` over `Expr`) copied from the source text. A structural induction on `DimExpr` can prove statements about the MODEL: for `PosDim e` and a binding with all values ≥ 1 that binds every parameter of `e`, `evalM θ e = .ok v` with `v ≥ 1`. This is a plan, not a result; nothing of Layer A is written.
- **Layer B (bridge).** `DimExpr.evaluate θ e = evalM θ e` (and the same for `specializeType`/`specializeExpr`). **This survey did not find a supply path.** The only routes it can name need a decision that is not in the approved scope: a production edit that makes the three functions total/structural (production edit: not allowed in this work), or a new law/TRUSTED boundary stating the equation (not approved). Neither is proposed here.
- **Consequence.** The rev4 statement `PosPlus b D → SpecSuccessAllPositive b D` about the PRODUCTION `specializeDesign` is withdrawn as an implementable unit. What can be implemented without a new assumption is only Layer A, a statement about the model, and it must be reported as such. I5b-pos, as a statement about `specializeDesign`, is UNSUPPLIED until Layer B has a supplier.

### 13.3 `PosPlus`, in full (all positions the specializer visits), and the separate premises
`PosPlus` is a `Prop` (not claimed decidable). Positions are exactly the ones `specializeModuleUnchecked` / `specializeStmt` / `specializeExpr` / `specializeType` visit (Specialize.lean:56-130).
```lean
-- value class of one dimension: evaluates, and to a value ≥ 1, for every binding with values ≥ 1 that binds its parameters
def PosDim : DimExpr → Prop
  | .literal c => 0 < c
  | .parameter _ => True
  | .add a b | .mul a b | .pow a b | .min a b | .max a b => PosDim a ∧ PosDim b
  | .sub .. | .div .. | .mod .. | .clog2 _ => False        -- conservative: these are the E1-E3 sources (§11.1)
def NonNegDim (e : DimExpr) : Prop := e = .literal 0 ∨ PosDim e
-- the slice bound pair the translator builds (Elab:856-859, used at :5894, :7227, :7583): hi = (start + len) - 1, lo = start
def SliceOK (hi lo : DimExpr) : Prop :=
  ∃ s l, lo = s ∧ hi = DimExpr.mkSub (DimExpr.mkAdd s l) (.literal 1) ∧ NonNegDim s ∧ PosDim l
def PosType : HWType → Prop
  | .bit | .bitVector _ => True
  | .bitVectorDim d => PosDim d
  | .array _ e => PosType e                                   -- specializeType recurses into the element type
def PosExpr : Expr → Prop
  | .const .. | .ref _ => True
  | .op _ args | .concat args => ∀ a ∈ args, PosExpr a
  | .slice e .. => PosExpr e                                   -- concrete bounds are not evaluated
  | .sliceDim e hi lo => PosExpr e ∧ SliceOK hi lo
  | .index a i => PosExpr a ∧ PosExpr i
def PosStmt : Stmt → Prop                                      -- the constructors specializeStmt visits
  | .assign _ rhs => PosExpr rhs
  | .register _ _ _ input _ => PosExpr input
  | .memory (writeAddr := wa) (writeData := wd) (writeEnable := we) (readAddr := ra) .. =>
      PosExpr wa ∧ PosExpr wd ∧ PosExpr we ∧ PosExpr ra       -- extraWrites / extraReads are NOT visited by specializeStmt (:94-108)
  | .inst _ _ conns => ∀ c ∈ conns, PosExpr c.2
def PosModule (m : Module) : Prop :=
  (∀ p ∈ m.inputs ++ m.outputs ++ m.wires, PosType p.ty) ∧ (∀ s ∈ m.body, PosStmt s) ∧ (∀ a ∈ m.assertions, PosExpr a.2)
def PosPlus (b : Module) (D : Design) : Prop := ∀ m ∈ (D.addModule b).modules, PosModule m
```
This is a CLASS, deliberately narrower than "all that succeed" (it excludes every width with `-`, `/`, `%` or `clog2` even when some θ succeed, and the exclusion of the translator's own `(start + len) - 1` is handled by the dedicated `SliceOK`). It does not claim the rest fail.
Premises that `PosPlus` does NOT provide and that Layer A needs, each on its own line:
1. **Parameter lookup exists.** Every `.parameter n` occurring in any dimension of any module of `D.addModule b` has `n` declared by some module of that design (`n ∈ modules.flatMap (·.parameters.map (·.name))`). `validateBindings` then requires every declared name to be bound (Specialize.lean:42-45), so `bindings.lookup n` is `some`. This survey did not establish that the translator only emits declared names in children's dimensions (the symbolic top declares them through `addParameter`; whether a child module can mention a parent's name was not read: probe P1).
2. **Legal binding.** `LegalBinding` (all θ values ≠ 0, no duplicates, every θ name declared, every declared name bound); positivity of the values comes from here, not from `PosPlus`.
3. **Top module present** in `D.addModule b` (§13.1 correction).
4. **Every expression the specializer visits is inside `PosPlus`'s scope**, including all modules (children too), array element types, assertions, and all statement kinds; the `.memory` extra ports are not visited by the specializer, so a `.sliceDim` there would be left symbolic: this is a different defect and is excluded by a separate premise "no `.sliceDim`/`.bitVectorDim` in `extraWrites`/`extraReads`" (I2 gives no `.memory` for the symbolic top only, not for child modules).
5. **`SliceOK` ties the bound pair to the translator's construction.** E5 (`hi < lo`) cannot fire for `lo = s`, `hi = (s + l) - 1` with `PosDim l`; for a slice not built by `makeSliceFromStartLength` no claim is made.

### 13.4 Open links, one per row (none of these is discharged by §13.1)
| id | link | what is missing | status |
|---|---|---|---|
| F1 | FG connection (outermost start) | `Start L mctx cctx w` is `AdmCtx L.O.quiet mctx cctx ∧ JQC L.O 0 w` over `Laws` (Tools/ShippingGen2Defs.lean:52-53); I3c is proved for a `RefLaws` witness and `Out0`/`StartV`. This survey did not find a lemma from `Start` to `Out0` of a `RefLaws` witness, nor a symbolic version of the A-framework walk (`core0_tripleAC`, ShippingChildDepthC.lean:218). Outermost depth 0 comes from `Start`; a symbolic run is FG-applicable only after this link | unsupplied |
| F1b | `EntryShips` shape | first conjunct `<default-entry hypotheses of FG>` is still a placeholder; `ReflectsAll` (G3) for the parametric route is not defined; `CombTopRunN` is NOT approved as the final conclusion of every parametric FG case (only as the interface for the cases where it holds) | unsupplied / not approved |
| F2 | clock/reset names | `CombChildRunN` needs `"clk" ∉ inputs ∧ "rst" ∉ inputs` (GEN2_DEFS:66-67). A Signal binder is turned into an input port named after the binder (`bindInputPort`, Elab:2104-2108), so a symbolic top may have an input named `clk`/`rst`; `addClockResetIfSequential` does not remove existing inputs. Probe P3 (I2b) was not run | unsupplied; if such a top is reachable the conclusion needs a guarded variant (open branch U3) |
| F3 | real source | `SrcAt`/`SrcAtOf` (S1) has no definition linking `ci.value` of the run (the `ci` of I3b) with each retained `Nat` binder instantiated to θ and the `(bsC, outsC, S)` data; no satisfiability evidence for any declaration | unsupplied |
| F4a | raw-side specialization success | `S2` is stated at `Dr.addModule raw`: the success `specializeDesign (Dr.addModule raw) θ = .ok Dr'` is a hypothesis of `PostTransfer`; its supply is the translator contract (G2, ROUTE_CENSUS.md:22) | pending legacy route |
| F4b | post-side specialization success | `ParamTopShips` takes `specializeDesign (D.addModule b) θ = .ok D'` as a hypothesis. To use S2 (at `raw`) the proof needs the direction "post-side success ⇒ raw-side success" (and the dimension correspondence between `raw` and `dropZeroWidth`/`mergeChecked` output). This survey did not find such a lemma | unsupplied |
| F5 | `DimExpr.evaluate`/`specializeType`/`specializeExpr` are `partial` | Layer B of §13.2 | unsupplied |
| F6 | `PostTransfer` | soundness of `dropZeroWidthModule`/`mergeChecked` on modules with `.bitVectorDim`/`.sliceDim` (§11.3) | unsupplied |
Dependencies on M3: F1b and S5 wait for the M3 route producer; F2-F6 and S1-S4 do not depend on M3 except through the legacy route (F4a).

### 13.5 Decisions asked on rev5
1. Approve for the record the built units of §13.1 (pod build; the clean build is the coder's), including the corrected `SpecSuccessAllPositive`.
2. Confirm that I5b-pos about the production `specializeDesign` is withdrawn (§13.2) and that only Layer A (a statement about a total model, reported as such) may be implemented without a new boundary; or reject Layer A as not worth a model.
3. Confirm the full `PosPlus` and its separate premises (§13.3).
4. No approval requested: F1-F6 (each is a separate supply obligation), the choice between conditional/unconditional parametric success (user: `scripts/gen4/PARAMETRIC_SPECSUCCESS_DECISION.md`).
