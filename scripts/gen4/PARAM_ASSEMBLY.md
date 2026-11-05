# PARAM_ASSEMBLY: `LegalBinding (SpecDesign M' D') θ` (B.P-8) and `AllPos θ` (B.P-1) from a real parametric run

Status: built, awaiting reviewer. Base `af3468e4` (par/passm). Nothing here is accepted by this document.
Ledger: FG 75 / T1 57 (this unit: FG -0 +0 / T1 -0 +0). The subtraction is recorded by the coder after the reviewer approves.
No new assumption, no TRUSTED, no frozen text changed, no production edit, heartbeat limit unchanged (4M).

## 1. The parts build (base check)

`kjob lake build` of `Tests.Gen4.{FThetaCheck, FThetaTeleCheck, FTopCheck, FPostCheck, ShapeCheck, FKidsCheck, FKidsOblCheck,
ParamIfaceCheck, ParamLayerACheck}` on `af3468e4`: exit 0, 869 jobs. Nothing was broken; no repair commit.

## 2. What was added (new files only, plus the lakefile registration in the first commit)

`Tools/ShippingGen4ParamAssembly.lean` (namespace `Tools.ShippingGen4ParamAssembly`), `Tests/Gen4/ParamAssemblyCheck.lean`.

* `legal_of_facts`: the constructive direction of the private `validateBindings` (converse of `legal_facts`): the five clauses
  (a) no duplicate declaration per module, (b) θ names unique, (c) every θ name declared by some module, (d) θ values nonzero,
  (e) every declared name bound, give `LegalBinding D θ`. Helpers `filter_len_one`, `dupName_none`, `forIn_all_yield`.
* `sfc_defn`: a returning `synthesizeFromConst` run (symbolic mode) reads a `defnInfo` (the other arms throw), needed to apply F-top / F-θ
  to the `ConstantInfo` that `core_symbolic_reads` leaves abstract.
* `run_facts` (premises `MemoFamily` rev3, `MsgMvK`, `LamTelescopeN`, `AdmCtx`, the K start world `KWD .. 0 w`, the run): from the run of
  `synthesizeCombinationalWithParameters declName θ` returning `(M', D')`:
  * (b) `(θ.map (·.1)).Nodup` and (d) `AllPos θ`: `core_symbolic_prologue` (`dupParams`, `zeroParam`) on the core run that `fpost_run_top` exposes;
  * (c) `∀ p ∈ θ, ∃ q ∈ M'.parameters, q.name = p.1`: `fTop_out` (F-top) on the `synthesizeFromConst` run of `core_symbolic_reads`, then
    `M'.parameters = M0.parameters` (F-post, `fpost_run_top`);
  * (a), (e) for the top: `fKidsObl_params` (F-kids obligations (2)(3): `Nodup`, names ∈ θ) turned into a `lookup` by `lookup_some_of_mem_keys`;
  * (a), (e) for the other modules: `fKidsObl_noGuard` (every module of `D'` declares no parameter, no name guard).
* `Collides M' D' := ∃ x ∈ D'.modules, x.name = M'.name` and `legal_assembly`:
  * `AllPos θ`;
  * `¬ Collides → LegalBinding (SpecDesign M' D') θ` (`SpecDesign = D'.addModule M'`, `specDesign_eq_addModule`);
  * `Collides → (LegalBinding (SpecDesign M' D') θ ↔ θ = [])`.
* `legal_names_declared`: `LegalBinding D θ` implies clause (c) (needed for the collision case; `legal_facts` gives (d), (e) only).

## 3. The same-name top-child (FKIDS_FREEZE §7.9, Q-F3), connected

`fKidsObl_noGuard` says every module of `D'` is parameter-free, including one that collides with the top name; NameNoTop is not provable.
`SpecDesign M' D'` (Elab.lean:9126, the `design'` that `specializeDesign` is applied to) is `D'` in that case (the top `M'` is NOT added), so the
top's parameters are in no module of the specialized design. Consequences, as Lean statements:
* no collision: `SpecDesign = D'.addModule M'` (the `D.addModule b` of `ParamTopShips` / `SpecSuccessAllPositive`) and legality holds;
* collision: legality holds iff `θ = []`. For `θ ≠ []` the real command's `specializeDesign` cannot succeed (`specializeDesign_ok_legal`
  would give legality). So the collision case is not a hole of the assembly: it is a run on which B.P-8 is false and the specialization fails.
  A consumer that needs only the consequences of legality that hold in both cases (coverage, `AllPos`) gets them in both cases (`paramRoot_run`).
The D vs `D.addModule b` choice of Q-F3 is thus settled by `SpecDesign M' D'`; the two designs agree exactly when no child has the top's name.

## 4. The roots, and the binder difference

On this base there is no final FG root with a `LegalBinding` / `AllPos` binder: the gen5 final roots (R / G, ND chain, ...) are on other
branches, and the ledger registers B.P-8 / B.P-1 (Q-F3, §8.4) rather than binding them. The roots here are therefore built for the in-tree users of
ParamIface:91 and ParamLayerA:43, and they must be mapped to the FG root by the reviewer:
* `RootConcl M' D' θ e`: every declared parameter of every module of `SpecDesign M' D'` is bound by θ (`legalBinding_covers`), and an
  `ExprOK θ e` source specializes (`specExprM_ok`, needs `AllPos θ`).
* `paramRoot_old`: binders `h` (the run), `hL : LegalBinding (SpecDesign M' D') θ`, `hpos : AllPos θ`, `hok`.
* `paramRoot_run`: binders `M : MemoFamily O`, `hmsg : MsgMvK O`, `htel : LamTelescopeN`, `hA : AdmCtx`, `hw : KWD`, `h`, `hok`; same conclusion.

`Tests/Gen4/ParamAssemblyCheck.lean` compares the two types by one telescope walk, as `FThetaTeleCheck` / `CR4Check` do (old binders
instantiated by the same-named new fvar, types by `Expr ==`):

    PARAM-ASSEMBLY COUNTS: removed 2 [hL, hpos] (B.P-8, B.P-1), added 6 [O, M, hmsg, htel, hA, hw]
      (shared +1 [htel] / Start rows and carrier [O, hA, hw] / F-kids assumptions [M, hmsg]), changed 0, concl true, FG -0 +0 / T1 -0 +0 recorded

* removed = `hL`, `hpos` only; `LegalBinding` and `AllPos` are not in the type of `paramRoot_run` (the proof uses them).
* added: `htel : LamTelescopeN` is the shared +1 candidate N4-a (§12.17), counted once in the final FG. `M : MemoFamily` rev3 and `hmsg : MsgMvK`
  are the F-kids assumptions the brief allows; `MsgMvK` is a conditional leaf, not TRUSTED. `O : RefLawsAOps`, `hA : AdmCtx`, `hw : KWD` are the
  carrier and the Start rows (A.P-02 `AdmCtx`, C.RR-1 `hA`/`hw`) that a run needs; I classify them as existing rows, the reviewer should confirm.
* negative controls: self-comparison is empty; a root keeping `hL` is rejected (removed `[hpos]`); an extra non-row binder is rejected; a different
  conclusion is rejected; the reversed pair is rejected; the hypothesis detector finds `LegalBinding` / `AllPos` in `paramRoot_old`.
* hypotheses of `run_facts` / `legal_assembly` / `paramRoot_run` are exactly `MemoFamily`, `MsgMvK`, `LamTelescopeN`, `AdmCtx`, `KWD`, `RunsTo`
  (`paramRoot_run` also `ExprOK`); the closure reaches no `Laws` / `T1Hyp` / `T1HypND`; axioms: propext, Classical.choice, Quot.sound.

## 5. Ledger effect (not recorded; for the reviewer)

Per the reviewer rule, a row leaves only when the final theorem's binder disappears or is replaced by existing rows in Lean, and a conditional
result is not counted. The replacement here uses `MsgMvK` (conditional leaf) and `MemoFamily` rev3, and `LamTelescopeN` (+1 once). So this unit
records FG -0 +0 / T1 -0 +0. If the reviewer accepts the mapping of §4 to the final root and counts the F-kids assumptions as allowed, the
expected effect is B.P-8 -1 and B.P-1 -1 with +1 for N4-a at the final FG (net -1), which is the reviewer's call.

## 6. Not done / limits

* The roots of §4 are not the gen5 final root (not on this base); the structural comparison is for the in-tree users only.
* `legal_assembly` takes the run's own θ; legality for another θ' is not claimed.
* Collision with `θ ≠ []` is a failing command, not a legal binding: stated, not hidden.
* Success of specialization (B.P-5, `SpecSuccessAllPositive`) is not touched.
