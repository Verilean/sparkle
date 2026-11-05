# FPOST_FREEZE: F-post (post-processing keeps `parameters` and `name`)

Status: FREEZE of the statement, before the proof. Base 7c836d8a (kjob/rt180). Issue sparkle-gen4-parametric-supply.
Sources read: PARAM_LEGAL_STUDY.md §3-§4 (item 4), PARAM_INV_ESTIMATE.md §5, `validateBindings`
(Sparkle/IR/Specialize.lean:33), `legalBinding_covers` (Tools/ShippingGen4ParamBridgeLegal.lean:84),
`synthesizeCombinationalWithParameters` (Sparkle/Compiler/Elab.lean:8940),
`synthesizeCombinationalWithParameters_designTop` (Tools/ShippingGen4ParamIface.lean:27).

## 1. What the assembly needs

`LegalBinding D' θ` is `validateBindings D'.modules θ = .ok ()`. `validateBindings` reads, from the modules, only
`parameters` (names, via `.map (·.name)`), plus `name` inside an error message of clause (a). So its result on the
final design `D'` equals its result on the core design `D` as soon as the lists of modules agree on `(name, parameters)`
position by position. The assembly (F-θ + F-top + F-kids give facts about the core output `(M, D)`) needs:

* per module: `parameters` and `name` unchanged by each of the 4 post-processing functions
  (`dropZeroWidthModule`, `mergeDuplicates`, `mergeChecked`, and the `top` map of the entry);
* for the design: the final `D'.modules` is the core `D.modules` with only the top-named module replaced, so the list of
  `parameters` (and of `name`) of `D'.modules` equals that of `D.modules`, in the same order. Both inclusion directions of
  clauses (c) and (e) and duplicate-freeness of (a) then transfer.

## 2. The exact Lean statements (to be proved; names in `Tools.ShippingGen4FPost`)

```lean
theorem dropZW_parameters (m : Module) :
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).parameters = m.parameters
theorem mergeDuplicates_parameters (m : Module) :
    (Sparkle.IR.RegDedup.mergeDuplicates m).parameters = m.parameters
theorem mergeDuplicates_name (m : Module) :
    (Sparkle.IR.RegDedup.mergeDuplicates m).name = m.name
theorem mergeChecked_parameters (m : Module) :
    (Sparkle.IR.RefineCheck.mergeChecked m).parameters = m.parameters

/-- `f` keeps `(name, parameters)`  ⇒  mapping it on the top-named module keeps the module list's keys. -/
theorem topMap_keys (f : Module → Module) (N : String)
    (hn : ∀ x, (f x).name = x.name) (hp : ∀ x, (f x).parameters = x.parameters) (l : List Module) :
    (l.map fun x => if x.name == N then f x else x).map (·.parameters) = l.map (·.parameters) ∧
    (l.map fun x => if x.name == N then f x else x).map (·.name) = l.map (·.name)

theorem fpost_run {declName parameters mctx mref cctx cref w w' M' D'}
    (h : RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (M', D') w') :
    ∃ (M : Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCoreWith Tsyn declName parameters true true) mctx mref cctx cref w (M, D) w1 ∧
      M'.parameters = M.parameters ∧ M'.name = M.name ∧
      D'.modules.map (·.parameters) = D.modules.map (·.parameters) ∧
      D'.modules.map (·.name) = D.modules.map (·.name)
```

`fpost_run` is the form the assembly takes: `D` is the core's design, `(M, D)` is the core's output, and
`LegalBinding D' θ ↔ LegalBinding D θ`-style transfer needs only the last two lines. (If the transfer
`LegalBinding D θ → LegalBinding D' θ` from those two lines is also proved, it is recorded in §6 as a bonus; the
assembly may also read the clauses through `legalBinding_covers` shapes directly.)

## 3. Subtraction table (ledger)

| Item | Effect now | Note |
|---|---|---|
| F-post alone | FG -0 +0 / T1 -0 +0 | one of six parts (F-θ, F-top, F-kids, F-post, shape, assembly) |
| B.P-8 `LegalBinding D θ` | -1 only when all six parts are proved | counted at assembly, not here |
| B.P-1 `AllPos θ` | -1 only when all six parts are proved | via `legalBinding_allPos` (approved) |
| new premises | +0 | |

Accepted line unchanged: `台帳: FG 81 / T1 57（今回 FG -0 +0 / T1 -0 +0）`.

## 4. Premises

Only a real run of `synthesizeCombinationalWithParameters` (hence, by `..._designTop`'s own unfolding, of
`synthesizeCombinationalCoreWith Tsyn declName parameters true true`) and existing definitions. The per-module lemmas are
unconditional. No new law, no TRUSTED, no compiler or shared-definition edit, no `sorry`/axiom/`native_decide`.
No run inversion past the `bind`/`ite`/`pure` of the entry itself (no lambdaTelescope), so no `htele`.

## 5. Check file

`Tests/Gen4/FPostCheck.lean`: TYPE of each theorem against the text above (structural `Expr ==`, via `Lean.Expr` of the
elaborated statement), mutants/negative controls, `#print axioms` (standard three only).

## 6. Record of attempts / failures

* First build failed: `Module` is ambiguous with `Lean.Module` under `open Lean` (fixed by qualifying
  `Sparkle.IR.AST.Module`); the `neg` case of `topMap_keys` needed `Bool.false_eq_true`/`↓reduceIte` rather than `if_false`.
  No statement changed.
* `synthesizeCombinationalWithParameters_designTop` gives `D'.modules = D.modules` only under a name-disjointness
  premise, so `fpost_run` redoes the same `bind`/`ite`/`pure` unfolding and states the key-lists form instead (no premise).
* The optional transfer `LegalBinding D θ → LegalBinding D' θ` (via private `validateBindings`) is NOT proved here;
  the assembly can use the key-list equalities directly.
* Result: `Tools/ShippingGen4FPost.lean` and `Tests/Gen4/FPostCheck.lean` build (axioms: propext, Classical.choice,
  Quot.sound); TYPE checks are structural `Expr ==`, 4 mutants rejected.
