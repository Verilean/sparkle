# DG-ACC freeze rev11 (issue `sparkle-gen5-dg-acc`): supply of `hev` / genData₀ / `hf` / `hK` from real definitions, survey, and the next unit A11

**FOR REVIEW (docs only; no Lean for A11 is written until this is approved).** Rev1-rev10 unchanged. Base: `kjob/g5ac-r20` 1e791651 (A10 approved; clean build `ac20v-1e791651`, exit 0, 728 jobs, TYPE 3 / MUT 5 (single 4 + compound 1) / AX 2). Header sync committed at e21942c8 (comment only): Tools/Check headers now cite the clean build `ac20v-1e791651`. DIFFERENCE recorded (freeze vs implementation): rev10 §2 proposed the compound mutant's conclusion in a `.map` form; the implementation uses the `isSome` form `(machineShape? false [] E (structEnv env₀)).isSome = true` together with `hev` weakened to the shape conjunct. The 4 single-change mutants are as frozen. All mutants are rejected by signature/defeq; none is a semantic counterexample.

Tags: `[S]` source read (this worktree, or the named branch via `git show` / `git grep`); `[B]` built in this lineage. Nothing below was elaborated.
Wording: "not supplied / no route found" = the candidate routes followed in this survey did not reach a supplier; never "impossible". Conditional results are INTERMEDIATE, never completion.

## 0. Survey: where `hev`, the success of `genData₀`, `hf`, `hK` would come from

| item | what was followed | result of this survey | owner |
|---|---|---|---|
| `hev : GDEvidence dataOf GD dOf env₀` for every `GD` element | DG-SEM's next unit U8 (`kjob/g5sm-u20:scripts/gen5/DG_SEM_FREEZE_P8.md` lines 46-51, 80-82 `[S]`, docs only, no Lean) proposes `structure GenData (dataOf) (E) (senv)` with fields `hshape : machineShape? false [] E senv = some d.shape`, `hdata : dataOf E senv d.shape = some d`, and a theorem `genData_evidence … : machineShape? false [] E senv = some g.d.shape ∧ dataOf E senv g.d.shape = some g.d` | if U8 is built as proposed, `GDEvidence dataOf (fun E => GenData dataOf E (structEnv env₀)) GenData.d env₀` would be `fun E g => genData_evidence (structEnv env₀) E g`. No built `GenData` was found in `kjob/g5ac-r20`, `kjob/g5do-r6`, `kjob/g5sm-u20`, `kjob/g5rt-r5`, `par/gen5-t2` by `git grep -E "structure GenData"` over `*.lean` (the candidate routes followed). Not supplied here | DG-SEM (U8) |
| success of `genData₀ E` (`= some g`) for the entry of a real run | nothing followed reaches a Lean definition of `genData₀` (kit field, abstract `Tools/ShippingGen5Acc.lean:36` `[B]`); only the proposal `def genData₀ (env₀) (E) : Option (GenData E (structEnv env₀))` in `par/gen5-t2:scripts/gen5/DGEN_FREEZE.md` (line 350 `[S]`, text) | not supplied by the routes followed; it is a coverage statement (`GenWF`, `dataOf` total on the run's entries) | DG-COVER, DG-DATAOF (names only) |
| `hf : DataSoundAt (dataOfAt lvl)` | `Tools.ShippingGen5DataOf.dataOfAt_sound (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape} {d : MachineData} (h : dataOfAt lvl E senv s = some d) : d.shape = s ∧ d.ok = true ∧ d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j)) (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧ d.initOk (initsOf d) = true` (`kjob/g5do-r6:Tools/ShippingGen5DataOf.lean:211` `[S]`) | its first 3 conjuncts are the body of `DataSoundAt (dataOfAt lvl)` up to implicit→explicit binders. Closes once `Tools.ShippingGen5DataOf` is importable; `kjob/g5do-r6` is not an ancestor of this branch, and merging is outside this Issue | DG-DATAOF (integration) |
| `hK : KitAgrees K f` for a real kit | `AssignKit` structure (`Tools/ShippingGen5Acc.lean:32-47` `[B]`); `git grep -E ": AssignKit"` over the same branches `[S]` | no `AssignKit` instance found in the branches followed. For a kit whose field `dataOf` is set to `f`, `KitAgrees K f` holds by A10's `kitAgrees_of_eq` with `rfl`; what is missing is the construction of the kit itself → **A11** (constructor from abstract parts) | DG-ACC (constructor), DG-SEM (`genSem` parts) |
| `genSem`, `genSem_local`, `genSem_decl`, `genSem_d`, `ordCallees`, `mem_ordCallees` for a real kit | DG-SEM U8 proposal (above) | not supplied (no Lean); they are taken as hypotheses of A11 | DG-SEM |
| L, C′, `ReachCover`, `ReadsSupplyAt`, `GenSFacts`, off-route, real run, M5, FG, S1 integration | unchanged from rev9 §0 | not supplied by the routes followed | other rows / owners |

## 1. Chosen unit: A11 the kit built from abstract parts, with `dataOf := f` (new file `Tools/ShippingGen5AccMkKit.lean`, imports `Tools.ShippingGen5AccGenDataEv`)

Reason: it is the only row closeable from names in this tree that makes the kit side of the `hf`/`hK` split concrete. A10 gave the kit field `genData₀_dataOf` from `GDEvidence` and `KitAgrees` from an equation; neither builds a kit. With a constructor whose `dataOf` field is the given `f` and whose `genData₀_dataOf` field is filled by A10, `hK` holds by `rfl` for every kit made this way, and `DataSound` of that kit follows from `hf` alone (A9). The remaining parts (`GD`, `dOf`, `genData₀`, `ordCallees`, `genSem`, and their four laws) are hypotheses; they are exactly what DG-SEM/DG-COVER must supply. No new law, no TRUSTED boundary, no shared-definition change; it is a definition plus three theorems.

```lean
namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}

def mkKit (f : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : ConstantInfo → Type) (dOf : {E : ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : ConstantInfo) → Option (GD E))
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence f GD dOf env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E),
      (∀ k ∈ ordCallees (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g) :
    AssignKit ι dom env₀ :=
  { dataOf := f, GD := GD, dOf := dOf, genData₀ := genData₀, ordCallees := ordCallees, genSem := genSem,
    mem_ordCallees := hmem,
    genData₀_dataOf := genData₀_dataOf_of_evidence f GD dOf genData₀ hev,
    genSem_local := hloc, genSem_decl := hdecl, genSem_d := hd }

theorem mkKit_dataOf (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) … : (mkKit f GD dOf genData₀ ordCallees genSem hmem hev hloc hdecl hd).dataOf = f := rfl

theorem mkKit_agrees … : KitAgrees (mkKit f GD dOf genData₀ ordCallees genSem hmem hev hloc hdecl hd) f

theorem mkKit_dataSound … (hf : DataSoundAt f) : DataSound (mkKit f GD dOf genData₀ ordCallees genSem hmem hev hloc hdecl hd)
```
In the three theorems the binders are written out in full in the Lean file, identical to those of `mkKit` (same names, same types, same implicitness: `ι dom env₀` implicit, the rest explicit as in `mkKit`); the `…` above only abbreviates this freeze document's text, not the Lean statement. Proof plan: `mkKit_dataOf := rfl`; `mkKit_agrees := kitAgrees_of_eq _ f rfl`; `mkKit_dataSound := dataSound_of_agree _ f hf (mkKit_agrees …)`.

Not claimed: a real `GD` / `genData₀` / `genSem`; `GenData`; `GenWF`; success of `genData₀`; `hf` for `dataOfAt lvl`; `hev` for a real run; L; C′; `ReachCover`; real run; M5; FG. Integration obligation (kept open): at the integration SHA instantiate the parts from DG-SEM's `GenData`/`genSem` and close `hev` (from `GenData.hshape/hdata`) and `hf` (from `dataOfAt_sound`). If DG-SEM's final field shapes differ, the hypotheses of `mkKit` are re-stated at integration.

## 2. Check plan (`Tests/Gen5/AccMkKitCheck.lean`, new)
Same requirements as A10. TYPE: independent `Expected…` for the `mkKit` TYPE and the three theorems (`checkExpected`, `Tests.Gen3.ExpectedType`), and the DEFINITION BODY of `mkKit` compared against an independently written structure literal (`dataOf := f` and `genData₀_dataOf` filled by `genData₀_dataOf_of_evidence`). MUTANT (signature/defeq rejection only; single and compound counted apart, numbers reported from the run): single: `mkKit` without `hev`; `mkKit` without `hloc`; `mkKit_agrees` stated for a different function `g`; `mkKit_dataSound` without `hf`; compound: `mkKit_dataSound` with `hf` weakened to `∀ E se s d, f E se s = some d → d.ok = true` and the kit replaced by the kit with `hev` dropped. CLOSURE: `closureReport` (unknown = fail, root self-judgement, helper value / helper type unknown controls + clean, `withoutModifyingEnv`; forbidden `sorryAx / ofReduceBool / trustCompiler`; expected suppliers fixed and reported as a union of roots (roots `mkKit`, `mkKit_dataOf`, `mkKit_agrees`, `mkKit_dataSound`; `genData₀_dataOf_of_evidence`, `kitAgrees_of_eq`, `dataSound_of_agree`, `AssignKit` as reached constants, distinguished from the roots); DataOf/SemGen units not reached). AXIOMS standard three only for the three theorems; no sorry in roots. Build one target at a time in the Pod (`-c 2`, incremental); the Lean commit stays `doing` ("clean build is the coder's").

## 3. Not claimed / decisions
DG-ACC, M5, FG are not complete. A11 needs no new law / TRUSTED / shared-definition change. Rows other Issues own (DG-DATAOF `dataOfAt_sound` integration, DG-READKINDS, DG-SEM `GenData`/`genSem`, DG-COVER success of `genData₀`) are named only. The survey wording is limited to the branches and greps listed above.
