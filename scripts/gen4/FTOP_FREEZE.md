# FTOP_FREEZE: F-top (the top module the symbolic entry returns, vs. the `D.addModule b` assembly)

Status: FREEZE of the statement (rev1). Base par/ftheta 9562f44c. Nothing is accepted by this document.
Ledger: FG 81 / T1 57 (this unit: FG -0 +0 / T1 -0 +0).

## 1. What `LegalBinding (D.addModule b) θ` needs from the top module (read from the tree)

`LegalBinding D θ := specValidateBindings D.modules θ = .ok ()`; `specValidateBindings` is `validateBindings`
(Sparkle/IR/Specialize.lean:33): (a) no module declares a duplicate parameter, (b) θ has no duplicate names,
(c) every θ name is a declared parameter of some module, (d) every θ value is nonzero, (e) every declared parameter of
every module is bound by θ.

* (b), (d): F-θ side (`core_symbolic_prologue`, done).
* (c) for the top module: `finishSynth_symbolic` (Tools/ShippingGen4ParamEntry.lean:112) gives it on the BUILDER module
  `fcs.module`, but only as a `RunsTo (finishSynth …)` statement about a `CircuitState` the caller never sees. F-top
  restates it about the module the entry RETURNS (`M = fcs.module.finalize`), reached from the
  `synthesizeFromConst` run past the `lambdaTelescope` (`htel`).
* The name check `ModuleNameCheck.check (fcs.module :: fcs.design.modules) = true` is a fact `finishSynth` gives; F-top
  transports it to `M :: D.modules` (the lists that `D.addModule b` assembles), as a Lean statement of the check
  already in the tree (`Sparkle.IR.ModuleNameCheck.check`, Sparkle/IR/ModuleNameCheck.lean:21; no new definition).

## 2. The frozen statements

File: Tools/ShippingGen4FTop.lean (new), namespace `Tools.ShippingGen4FTop`. Imports Tools.ShippingGen4FThetaTele.

```lean
/-- the symbolic-mode body test of `finishSynth` -/
def SeqFree (m : Sparkle.IR.AST.Module) : Prop :=
  (m.body.any fun stmt => match stmt with
    | .register .. | .memory .. | .inst .. => true
    | _ => false) = false

theorem fTop_finish (htel : LamTelescopeN)
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Module} {D : Design}
    (hr : MReturns (synthesizeFromConst translate logProf declName parameters true cfe
      (.defnInfo dv) isInst) (M, D)) :
    ∃ fcs : CircuitState,
      M = fcs.module.finalize ∧ D = fcs.design ∧
      Sparkle.IR.ModuleNameCheck.check (fcs.module :: fcs.design.modules) = true ∧
      (∀ p ∈ parameters, ∃ q ∈ fcs.module.parameters, q.name = p.1) ∧
      SeqFree fcs.module

theorem fTop_out (htel : LamTelescopeN) … (same hypotheses) :
    Sparkle.IR.ModuleNameCheck.check (M :: D.modules) = true ∧
    (∀ p ∈ parameters, ∃ q ∈ M.parameters, q.name = p.1) ∧
    SeqFree M
```

`fTop_out` is what the assembly consumes: (c) for the top module; the name check for the `M :: D.modules` list.
Both are read off the returned `(M, D)`; nothing is said about `fcs` beyond the existential.

## 3. Premises

* The run (`MReturns (synthesizeFromConst … true …)`; a `synthesizeCombinationalCoreWith` run gives it by
  `core_symbolic_reads`).
* `htel : LamTelescopeN` (ledger candidate N4-a), used through `telescopeIn_of_lamTelescopeN`. Nothing else: no new law,
  TRUSTED, compiler or shared-definition edit.

## 4. What F-top does NOT give (stated up front)

* `∀ x ∈ D.modules, x.name ≠ M.name` (the guard of `synthesizeCombinationalWithParameters_designTop`) is NOT a
  consequence of `ModuleNameCheck.check`: `checkNames` runs on `eraseDups` of the names, so "Repeated uses of the SAME
  raw name are allowed" (ModuleNameCheck.lean:15). Two modules of the same name pass `check` (the uniqueness test is
  `checkDesign`, applied elsewhere). So the brief's claim "the guard is vacuous when the name check holds" is not what
  `check` proves; see §6 for the control that shows it. The guard needs a fact about `fcs.design.modules` (no child
  has the top's name), which comes from the translator walk (F-kids), not from `finishSynth`.
* (e) for the top module (every `M.parameters` name is bound by θ) and (a) (no duplicate declaration): these hold
  by `bindInputsLegacy` / `addParameter`, i.e. they live inside the translator walk (F-kids side), not in `finishSynth`.
* `M.name = ModuleName.ofDecl declName`: the builder module's name after the opaque `translate` run is not known
  without a translator invariant.

## 5. Subtraction table

| item | before | after F-top proved | note |
|---|---|---|---|
| F-top (this unit) alone | 0 | 0 | one of six parts (F-θ, F-top, F-kids, F-post, shape, assembly) |
| B.P-8 `LegalBinding D θ` | UN-C | UN-C | -1 only when all six are proved |
| B.P-1 `AllPos θ` | UN-C | UN-C | -1 only when all six are proved |
| new rows | | +0 | premise `LamTelescopeN` is the reviewer-ruled N4-a, shared with F-θ |

## 6. Check plan and notes

Tests/Gen4/FTopCheck.lean: structural `Expr ==` TYPE check of `fTop_finish`, `fTop_out` against the text above;
mutants (drop a conjunct, `check` on `D.modules` alone, `∀ q ∈ M.parameters` swapped); control: a concrete pair of
equal-name modules passing `check` (the §4 finding); `#print axioms` (standard 3).

## 7. Failed attempts / notes
(none yet)
