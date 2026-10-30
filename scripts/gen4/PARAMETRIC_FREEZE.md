# M4 parametric / symbolic entry: investigation and freeze (rev3; rev2 answered R1-R3 on 7c297d5f, rev3 answers the remaining R3 on 2030997a)

- **Issue:** `sparkle-gen4-parametric-supply`.
- **Status:** investigation + freeze of types and plan. No Lean, no build, no production edit. rev2 changes: §1.5, §3.2, §4 (I2, I5, new I5a/I5b), new §8 (response to R1-R3), new §9 (complete telescope and suppliers). rev1 text that was withdrawn is listed in §8, not silently removed.
- **rev3 changes:** only §9.1 (complete signatures, no ellipsis/etc./copy-later), §9.3 U5, §10, new §8 R3-rev3. §4 rows I1, I3, I4 are superseded where §9.1 differs (I1 is pure gate facts, I4 is out of the unit).
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
