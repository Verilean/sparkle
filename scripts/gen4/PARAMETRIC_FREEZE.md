# M4 parametric / symbolic entry: investigation and freeze (rev1, for review)

- **Issue:** `sparkle-gen4-parametric-supply`.
- **Status:** investigation + freeze of types and plan. No Lean, no build, no production edit.
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
`(raw, D) : Module × Design` with, by §1.2 (i), `raw.body` having no `.register`/`.memory`/`.inst` (so `addClockResetIfSequential` adds no clk/rst: this follows from reading :2200, to be confirmed by the I2 theorem), `raw.parameters` containing every requested name (`Parameter` has `name` and `defaultValue`, Sparkle/IR/AST.lean:328), and widths that may be `DimExpr` over those parameters. The consumer that gives it a concrete meaning is `Sparkle.IR.Specialize.specializeDesign (design : Design) (bindings : List (String × Nat)) : Except String Design` (Sparkle/IR/Specialize.lean:145): it requires the top module to be present, every declared parameter bound exactly once and no unknown binding (:36-48 `validateBindings`), and removes `parameters`.
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
- The parametric top has no register, memory or instance (§1.5), so no `Pkg` exists for it and `TopShips` is the wrong conclusion for it. This is a type finding, not a claim that a theorem is impossible. It is why FG's second disjunct needs its own conclusion that the first disjunct's conclusion also implies.
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

/-- Parametric top: for EVERY valid binding θ of the module's own parameters, the specialised design runs as the source
    instantiated at θ. `SrcAt` is the declaration's meaning at θ (G3-style premise, per declaration, see §4 step S1). -/
def ParamTopShips (declName : Name) (parameters : List (String × Nat)) (b : Module) (D : Design)
    (SrcAt : List (String × Nat) → TopIface) : Prop :=
  ∀ θ : List (String × Nat), θ.map Prod.fst = b.parameters.map (·.name) → (∀ x ∈ θ, 0 < x.2) →
    ∃ D', Sparkle.IR.Specialize.specializeDesign (D.addModule b) θ = .ok D' ∧
      ∃ b', D'.findModule b.name = some b' ∧
        CombTopRunN (childMap D'.modules) D' b' (SrcAt θ)

/-- FG's per-route conclusion (the first disjunct is today's TopShips, the second is ParamTopShips). -/
def EntryShips (route : Route) … : Prop := …    -- sum over MachineTopShips / ParamTopShips
```
Open details that are a reviewer choice and not decided here: (i) whether `θ` ranges over all positive bindings or only those the run's `parameters` defaults generate (the module declares the names, the defaults are metadata: Specialize.lean:131-134); (ii) whether `CombTopRunN` is `CombChildRunN` (reuse, with `"clk"/"rst"` absent) at depth 0 or a new definition. Reuse is preferred because a parametric top can then also be a child (§3.3).

### 3.3 Link to M3/M4 consumers
A parametric module could be a child only if some other entry calls it; the shipping children path calls the default entry (§1.4), so the parametric result is never cached or served as a child (no `ShipsRes` for it is needed). This survey did not find a call of `synthesizeCombinationalWithParameters` from inside the translator. Confirming this is I4 below.

## 4. Proof plan for the general guarantee (not corpus-by-corpus)

A fixed parameter list on a corpus example is an instance, not the guarantee. Acceptance of this issue requires the following statements to be proved ∀ declaration (under the same kind of per-declaration premise `ReflectsAll` already names) and ∀ θ, with the premises listed.

| step | statement (PROPOSED, informal types) | premises | status |
|---|---|---|---|
| I1 | `synthesizeFromConst … parameters symbolicMode=true … ci = legacyTail …` (the four gates and the machine and memo guards reduce, §1.2 b-e) | none beyond the definition | independent, can start after approval |
| I2 | `finishSynth` symbolic: result `(M, D)` has no `.register/.memory/.inst`, `∀ p ∈ requested, p ∈ M.parameters`, names ok, `M.inputs` has no clk/rst | none | independent |
| I3 | core wrapper: the prologue throws exactly on duplicate/zero; otherwise the run equals the depth-gated body with `symbolicMode := true`; nested depth restoring as in `synthesizeCombinationalCore_reads` (Tools/ShippingEntrySoundness.lean:1090) | `Laws`, `Start` | independent (re-uses `RunsTo`, `peel_bind` tactics of EntrySoundness:1100-1115) |
| I4 | `WithParameters` post-processing: `(b, raw)` relation equals the default's (§1.1), and no translator path calls `synthesizeCombinationalWithParameters` | none | independent (a text/defeq check plus a grep-level census, labelled as such) |
| I5 | `Specialize` facts: `specializeDesign` succeeds iff validation passes; it commutes with `moduleByName`/`childMap`; width evaluation `evalDim θ` is total on `DimExpr` over declared parameters | none | independent (pure IR, no meta level) |
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
