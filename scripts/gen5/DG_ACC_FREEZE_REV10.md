# DG-ACC freeze rev10 (issue `sparkle-gen5-dg-acc`): supply of `hf` / `hK` for a real kit, survey, and the next unit A10

**FOR REVIEW (docs only; no Lean for A10 is written until this is approved).** Rev1-rev9 unchanged. Base: `kjob/g5ac-r18` 7076f718 (A9 approved; clean build `ac18v-7076f718`, exit 0, 727 jobs, TYPE 3 / MUT 6 (single 5 + compound 1) / AX 1). Header sync (build name; the "3 expected suppliers reached" of A9 is the union of the 3 roots, two of which (`DataSoundAt`, `KitAgrees`) are roots themselves, so it is NOT an independent proof-dependency assert) is committed at be1622a9 (comment/docs only; the only non-comment-line change is one Lean `--` comment inside the Check).

Tags: `[S]` source read (this worktree, or the named branch via `git show` / `git grep`); `[B]` built in this lineage. Nothing below was elaborated.
Wording: "not supplied / no route found" = the candidate routes followed in this survey did not reach a supplier; never "impossible". MUTANTs are rejections by signature / defeq, not semantic counterexamples. Conditional results are INTERMEDIATE, never completion.

## 0. Survey: where `hf : DataSoundAt f` and `hK : KitAgrees K f` would come from

| item | what was followed | result of this survey | owner |
|---|---|---|---|
| `hf` for `f := dataOfAt lvl` | `Tools.ShippingGen5DataOf.dataOfAt_sound (lvl : Lean.Expr → Nat) {E senv s d} (h : dataOfAt lvl E senv s = some d) : d.shape = s ∧ d.ok = true ∧ d.shape.body = quote … ∧ d.initOk (initsOf d) = true` (`kjob/g5do-r6:Tools/ShippingGen5DataOf.lean`, end of file `[S]`); its first 3 conjuncts are exactly the body of `DataSoundAt (dataOfAt lvl)` up to implicit→explicit binders | closes the row **once `Tools.ShippingGen5DataOf` is importable**. It is not in this tree (`ls Tools`; `kjob/g5do-r6` is not an ancestor of this branch). Importing needs an integration merge, which is outside this Issue and forbidden to this agent. Copying the file here would duplicate DG-DATAOF's code; not done | DG-DATAOF (integration) |
| `hK` for a real kit | `git grep AssignKit` over this tree, `kjob/g5do-r6`, `par/gen5-t2`, `kjob/g5env-*` outside `Tools/ShippingGen5Acc*` `[S]`: **no `AssignKit` instance and no `GenData`/`genSem` Lean exists** in the branches searched (`GenData` appears only in `scripts/gen5/DGEN_FREEZE.md` on `par/gen5-t2`, no Lean). `AssignKit.dataOf` is abstract (`Tools/ShippingGen5Acc.lean:33` `[B]`) | a real kit does not exist yet in the branches followed, so `KitAgrees K f` cannot be stated about it; for a kit whose field is built as `dataOf := f`, `KitAgrees K f` is `fun _ _ _ => rfl` (once the kit is built) | DG-SEM (`genSem`, `GenData`), DG-DATAOF |
| field `genData₀_dataOf` | DG-SEM's frozen `GenData E senv` carries `d`, `wf : GenWF d = true`, `hshape : machineShape? false [] E senv = some d.shape`, `hdata : dataOf E senv d.shape = some d` (`par/gen5-t2:scripts/gen5/DGEN_FREEZE.md:125-129` `[S]`) | the kit field `genData₀_dataOf` (`Tools/ShippingGen5Acc.lean:41` `[B]`) is the bind-form of `hshape`+`hdata`; the step from the structure fields to the kit field is pure and stated nowhere yet → **A10** | DG-ACC (glue only) |
| `genSem`, `genSem_local`, `genSem_decl`, `genSem_d`, `GenWF` (the `wf` field), `ordCallees`/`mem_ordCallees` instance | DG-SEM freeze (`GenData` / `genSem` have no Lean) | not supplied; names only | DG-SEM |
| L, C′, `ReachCover`, `ReadsSupplyAt`, `GenSFacts`, off-route, real run, M5, FG, S1 integration | unchanged from rev9 §0 | not supplied by the routes followed | other rows / owners |

## 1. Chosen unit: A10 `genData₀_dataOf` from `GenData`-shaped evidence (new file `Tools/ShippingGen5AccGenDataEv.lean`, imports `Tools.ShippingGen5AccDataAgree`)

Reason: of the rows above this is the only one closeable from names in this tree whose hypothesis is exactly what DG-SEM's frozen `GenData` carries, without importing anything not here. It is the glue that lets a DG-SEM `GenData` instance (its `hshape`, `hdata`) fill the kit field `genData₀_dataOf`, and it adds `KitAgrees` from a plain equation of the kit field. It does NOT build a kit, and does not supply `hf` / `hK` for a real kit. No new law, no TRUSTED boundary, no shared-definition change.

```lean
namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}

/-- What `GenData E senv` carries (fields `hshape`, `hdata`), stated for an abstract replacement-point type. -/
def GDEvidence (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : ConstantInfo → Type) (dOf : {E : ConstantInfo} → GD E → MachineData) (env₀ : Environment) : Prop :=
  ∀ (E : ConstantInfo) (g : GD E),
    machineShape? false [] E (structEnv env₀) = some (dOf g).shape ∧
    dataOf E (structEnv env₀) (dOf g).shape = some (dOf g)

/-- The kit field `genData₀_dataOf`, from the evidence. -/
theorem genData₀_dataOf_of_evidence
    (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : ConstantInfo → Type) (dOf : {E : ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : ConstantInfo) → Option (GD E))
    (hev : GDEvidence dataOf GD dOf env₀) :
    ∀ {E g}, genData₀ E = some g →
      ((machineShape? false [] E (structEnv env₀)).bind (dataOf E (structEnv env₀))) = some (dOf g)

/-- `KitAgrees` from the pointwise-function equation of the kit's field. -/
theorem kitAgrees_of_eq (K : AssignKit ι dom env₀)
    (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) (h : K.dataOf = f) : KitAgrees K f
```
(`machineShape?` as used in `Tools/ShippingGen5Acc.lean:42`; `autoImplicit false`. In `genData₀_dataOf_of_evidence` the implicit binders `{E g}` are the same as the kit field's, with `g : GD E`.)

Proof plan: first: `intro E g _; obtain ⟨h1, h2⟩ := hev E g; rw [h1]; exact h2` (`Option.bind` on `some`); second: `fun E se s => by rw [h]`.

Not claimed: a kit instance; `GenData` itself; `GenWF`; `genSem*`; `hf` / `hK` for any real function or kit; `K.dataOf = dataOfAt`; L; C′; `ReachCover`; real run; M5; FG. Integration obligation (kept open): at the integration SHA close `hf` from `dataOfAt_sound` and `hK` from the real kit's `dataOf` field, and `hev` from `GenData.hshape/hdata`.

## 2. Check plan (`Tests/Gen5/AccGenDataEvCheck.lean`, new)
Same requirements as A9. TYPE: independent `Expected…` for `GDEvidence` (body) and both theorems (`checkExpected`, `Tests.Gen3.ExpectedType`). MUTANT (signature/defeq rejection only; single and compound counted apart, numbers reported from the run): single: `GDEvidence` without the `hdata` conjunct; `GDEvidence` with `machineShape?` flag `true`; `kitAgrees_of_eq` with `h` removed; `genData₀_dataOf_of_evidence` without `hev`. Compound: `genData₀_dataOf_of_evidence` conclusion changed to `= none`-free `.map` form together with `hev` weakened to the shape conjunct. CLOSURE: `closureReport` (unknown = fail, root self-judgement, helper value / helper type unknown controls + clean, `withoutModifyingEnv`; forbidden `sorryAx / ofReduceBool / trustCompiler`; expected suppliers fixed and reported as a union of roots (roots `GDEvidence`, `genData₀_dataOf_of_evidence`, `kitAgrees_of_eq`; `KitAgrees`, `AssignKit` as reached constants, distinguished from the roots themselves); DataOf/SemGen units not reached). AXIOMS standard three only; no sorry in roots. Build one target at a time in the Pod (`-c 2`, incremental); the Lean commit stays `doing` ("clean build is the coder's").

## 3. Not claimed / decisions
DG-ACC, M5, FG are not complete. A10 needs no new law / TRUSTED / shared-definition change. Whether DG-SEM's final `GenData` keeps exactly `hshape` / `hdata` in this form is DG-SEM's; if it differs, `GDEvidence` is re-stated at integration.
