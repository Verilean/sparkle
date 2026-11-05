# SHAPE_FREEZE: which design `specializeDesign` reads, and its relation to the core output

Status: FREEZE of the statements, before the proof. Base f9f61145 (par/fpost). Issue sparkle-gen4-parametric-supply.
Sources read: PARAM_INV_ESTIMATE.md §5 (shape), PARAM_LEGAL_STUDY.md §2/§4(5), `synthesizeHierarchicalWithParameters`
(Sparkle/Compiler/Elab.lean:9126), `finishSynth` (Elab.lean:2218), `finishSynth_symbolic`
(Tools/ShippingGen4ParamEntry.lean:112), `fpost_run` (Tools/ShippingGen4FPost.lean:51), `specializeDesign`/`validateBindings`
(Sparkle/IR/Specialize.lean), `ModuleNameCheck.check`.

## 1. Which design

Three candidates, by reading:

* core design `D`: `finishSynth` returns `(module.finalize, finalCircuitState.design)`; the top module is NOT added to
  `D` by the core (`finishSynth_symbolic`: `D = fcs.design`, `M = fcs.module.finalize`). `specializeDesign` never sees `D`
  alone.
* `D.addModule b`: the design `ParamTopShips` / `SpecSuccessAllPositive` quantify over (with `(b, D)` the entry's output).
* the design the command elaborators specialize: `design' := if D'.modules.any (·.name == M'.name) then D' else
  D'.addModule M'` (`synthesizeHierarchicalWithParameters`, Elab.lean:9128; the writers pass `design'` to
  `specializeDesign`). With `(M', D')` the entry's output.

So the design read is `SpecDesign M' D'`, which equals `D'.addModule M'` exactly when no module of `D'` is named `M'.name`
(the collision case reads `D'` itself, and then `D'.addModule M'` is NOT what is specialized).
`ModuleNameCheck.check` (run inside `finishSynth`) does not exclude a same-named module in `D` (it compares sanitized names
after `eraseDups`), so the no-collision case is NOT derived here: it is F-top's goal (PARAM_INV_ESTIMATE §5), kept as an
explicit hypothesis `NoTopCollision` of the statements that need it. It is not a new ledger premise: it is a conclusion
owed by F-top, and nothing is assumed about it.

## 2. The exact Lean statements (names in `Tools.ShippingGen4Shape`)

```lean
/-- `design'` of `synthesizeHierarchicalWithParameters` (Elab.lean:9128). -/
def SpecDesign (M : Sparkle.IR.AST.Module) (D : Design) : Design :=
  if D.modules.any (·.name == M.name) then D else D.addModule M

/-- legality depends on the modules only through `(name, parameters)` position by position. -/
theorem legalBinding_congr {D₁ D₂ : Design} {θ : List (String × Nat)}
    (hp : D₁.modules.map (·.parameters) = D₂.modules.map (·.parameters))
    (hn : D₁.modules.map (·.name) = D₂.modules.map (·.name)) :
    LegalBinding D₁ θ ↔ LegalBinding D₂ θ

theorem specDesign_eq_addModule {M : Module} {D : Design} :
    SpecDesign M D = D.addModule M ↔ ¬ D.modules.any (·.name == M.name) = true ... (see §2.1)

theorem shape_run {declName parameters mctx mref cctx cref w w' M' D'}
    (h : RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (M', D') w') :
    ∃ (M : Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCoreWith Tsyn declName parameters true true) mctx mref cctx cref w (M, D) w1 ∧
      (SpecDesign M' D').topModule = D.topModule ∧
      (SpecDesign M' D').modules.map (·.parameters) = (SpecDesign M D).modules.map (·.parameters) ∧
      (SpecDesign M' D').modules.map (·.name) = (SpecDesign M D).modules.map (·.name) ∧
      (∀ θ, LegalBinding (SpecDesign M' D') θ ↔ LegalBinding (SpecDesign M D) θ) ∧
      ((∀ x ∈ D.modules, x.name ≠ M.name) →
        SpecDesign M' D' = D'.addModule M' ∧ SpecDesign M D = D.addModule M)
```

§2.1: `specDesign_eq_addModule` is stated as `(∀ x ∈ D.modules, x.name ≠ M.name) → SpecDesign M D = D.addModule M`
(and the converse direction for the iff is dropped if it needs more than `by_cases`).

Reading: the assembly states `LegalBinding` for `SpecDesign M D` of the CORE output (which F-θ/F-top/F-kids describe, with
`D.modules = fcs.design.modules` and `M` the finalized top), and `shape_run` transfers it to the design the elaborator
specializes; under F-top's freshness it is `D'.addModule M'`, the form of `ParamTopShips`.

## 3. Subtraction table (ledger)

| Item | Effect now | Note |
|---|---|---|
| shape alone | FG -0 +0 / T1 -0 +0 | one of six parts (F-θ, F-top, F-kids, F-post, shape, assembly) |
| B.P-8 `LegalBinding D θ` | -1 only when all six parts are proved | counted at assembly |
| B.P-1 `AllPos θ` | -1 only when all six parts are proved | via `legalBinding_allPos` |
| new premises | +0 | `NoTopCollision` is F-top's conclusion, not assumed |

Accepted line unchanged: `台帳: FG 81 / T1 57（今回 FG -0 +0 / T1 -0 +0）`.

## 4. Premises

A real run of `synthesizeCombinationalWithParameters` (via `fpost_run`, which stops at the entry's own `bind`/`ite`/`pure`)
and existing definitions. Nothing past the `lambdaTelescope` of `synthesizeFromConst`, so no `LamTelescopeN`. No partial or
opaque function is unfolded. No new law, TRUSTED, compiler or shared-definition edit. `validateBindings` is the private
constant named by its mangled name as in `specValidateBindings`. No `sorry`/axiom/`native_decide`.

## 5. Check file

`Tests/Gen4/ShapeCheck.lean`: TYPE against §2 by structural `Expr ==`, mutants, `#print axioms` (standard three).

## 6. Record of attempts / failures

(none yet)
