# FTHETA_FREEZE: F-θ (parameter names: no duplicates, nonzero, Nat binders of the declaration)

Status: FREEZE of the statement (rev1). Base kjob/rt180 7c836d8a. Nothing is accepted by this document.
Ledger: FG 83 / T1 57 (this unit: FG -0 +0 / T1 -0 +0).

## 1. What `LegalBinding` needs from θ (read from the tree)

`LegalBinding D θ := specValidateBindings D.modules θ = .ok ()` (Tools/ShippingGen4ParamIface.lean:91). Of the five
`validateBindings` clauses, the ones that are facts about θ alone are (b) θ has no duplicate names and (d) every θ value
is nonzero. These are exactly `core_symbolic_prologue` (Tools/ShippingGen4ParamEntry.lean:169):
`dupParams parameters = false ∧ zeroParam parameters = false` (already built, no premise beyond the run).
Clause (c) (every θ name is a declared parameter of some module) and (e) are facts about the output module; the
entry gives them in `finishSynth_symbolic` (`∀ p ∈ parameters, ∃ q ∈ fcs.module.parameters, q.name = p.1`), which
belongs to F-top, not F-θ.

The `foundNatBinder` loop in `synthesizeFromConst` (Sparkle/Compiler/Elab.lean:5361-5371) says each θ name is the
`userName` of a top-level lambda binder whose type `whnf`s to `Nat`. `validateBindings` has no clause that reads this,
so for the assembly of `LegalBinding` the Nat-binder fact is NOT needed; it is the "Nat binder" half of the F-θ
sentence in PARAM_INV_ESTIMATE.md §5 and is stated here because the brief asks for it.

## 2. The frozen statement

File: Tools/ShippingGen4FTheta.lean (new), namespace `Tools.ShippingGen4FTheta`.

```lean
theorem fTheta_natBinder
    {translate : Lean.Environment → TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Module} {D : Design}
    (htele : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) (fun _ _ _ => True))
    (hr : MReturns (synthesizeFromConst translate logProf declName parameters true cfe
      (.defnInfo dv) isInst) (M, D)) :
    ∃ (body0 : Lean.Expr) (mctx : Meta.Context) (xs : Array Lean.Expr),
      MReturns (openRecordInputs dv.value) body0 ∧
      ∀ p ∈ parameters, ∃ x ∈ xs, NatBinderAt mctx p.1 x

def NatBinderAt (mctx : Meta.Context) (nm : String) (x : Lean.Expr) : Prop :=
  ∃ (decl : LocalDecl) (t : Lean.Expr),
    MRunsIn x.fvarId!.getDecl mctx decl ∧ decl.userName.toString = nm ∧
    MRunsIn (Meta.whnf decl.type) mctx t ∧ t.isConstOf ``Nat = true
```
(`NatBinderAt` was introduced when the proof was written, to keep the type readable; the Check compares its value
structurally to the clause above, so the text is unchanged in meaning.)

plus the telescope-free half, restated for the assembly (already proved, `core_symbolic_prologue`):
`RunsTo (synthesizeCombinationalCoreWith translate declName parameters true cfe) … (M, D) … →
 dupParams parameters = false ∧ zeroParam parameters = false`.

## 3. Premises

* The run (`MReturns (synthesizeFromConst …)`; a `synthesizeCombinationalCoreWith`/`…WithParameters` run gives it by
  `core_symbolic_reads`).
* `htele`: the existing `TelescopeIn` shape (Tools/ShippingLegacySemEntryIn.lean) with the trivial property. It is a
  fact about Lean's `Meta` library (`lambdaTelescope` runs its continuation on some binders). `lambdaTelescopeImp.process`
  is an opaque worker (Tools/ShippingChildTeleLocalA.lean header), so the peel past the telescope cannot be derived
  from the run alone. This is the same premise every legacy-walk theorem in the tree takes; it is NOT a new law
  field and not a TRUSTED entry, but it is not discharged here. For a concrete declaration it comes from
  `telescopeIn_of_lam(s)`.
* No other premise. No compiler or shared-definition edit.

## 4. Subtraction table

| item | before | after F-θ proved | note |
|---|---|---|---|
| F-θ (this unit) alone | 0 | 0 | one of six parts (F-θ, F-top, F-kids, F-post, shape, assembly) |
| B.P-8 `LegalBinding D θ` | UN-C | UN-C | -1 only when all six are proved |
| B.P-1 `AllPos θ` | UN-C | UN-C | -1 only when all six are proved |
| new rows | | +0 | `htele` is an existing premise shape, but any consumer that has no concrete telescope fact inherits it |

Finding for the other parts: F-top, F-kids and (c)/(e) all sit behind the same telescope in `synthesizeFromConst`
(`finishSynth` is inside the continuation), so they need `htele` too. Whether that premise counts as a ledger row is
for the reviewer; this study does not decide it.

## 5. Failed attempts / notes
* BUILT: Tools/ShippingGen4FTheta.lean (`fTheta_natBinder`, with `inner_list`/`outer_list` loop inversions in `MRunsIn`)
  and Tests/Gen4/FThetaCheck.lean (structural `Expr ==` TYPE check, 5 mutants, 1 comparator control, axioms = propext,
  Classical.choice, Quot.sound). Both targets built with `kjob lake build`, exit 0. No sorry/native_decide.
* Failed attempt: deriving the Nat-binder fact (or any fact past `lambdaTelescope`) from the run alone. Cause:
  `lambdaTelescopeImp.process` is opaque (ShippingChildTeleLocalA.lean header), so a returning run does not yield a
  continuation run without a Meta-library premise; hence `htele` (existing `TelescopeIn` shape).
* Not covered: the `whnf` result is an oracle (the conclusion says what the run returned, not what Lean's `whnf` is).
  Check binder infos are not compared (`Expr ==` ignores them).
