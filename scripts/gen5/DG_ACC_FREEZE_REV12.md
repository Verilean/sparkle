# DG-ACC freeze rev12 (issue `sparkle-gen5-dg-acc`): survey of real mkKit parts, and the next unit A12 (`ordCallees₀` + `hmem`)

**FOR REVIEW (docs only; no Lean for A12 is written until this is approved).** Rev1-rev11 unchanged. Base: `kjob/g5ac-r23` 50cc0c13 (A11 approved; clean build `ac23v-50cc0c13`, exit 0, 729 jobs). Header sync committed at b6bb9655 (comment only): Tools/Check headers of A11 now cite `ac23v-50cc0c13`.

Tags: `[S]` source read (this worktree, or the named branch via `git show` / `git grep`). Nothing below was elaborated or built.
Wording: "not supplied / no route found" = the candidate routes followed in this survey did not reach a supplier; never "impossible". Conditional results are INTERMEDIATE, never completion.

## 0. Survey: the parts of `mkKit` and what each route reached

| mkKit part | routes followed | result of this survey | owner |
|---|---|---|---|
| `GD`, `dOf`, `genSem`, `hloc`, `hdecl`, `hd` | `git grep -E "structure GenData\|def genSem \|def genData₀"` over `Tools/` of `kjob/g5sm-u20`, `kjob/g5cv-r13` `[S]`; `kjob/g5sm-u20:scripts/gen5/DG_SEM_FREEZE_P8.md` (docs) | no Lean `structure GenData` / `genSem` found in the branches followed (U8 is a freeze document only). `Tools/ShippingGen5SemGen.lean` here has `genSemGenE` (different shape: takes `GenIn`/`ExtB`/`ExtV`), not an `AssignKit.genSem` | DG-SEM (name only) |
| `genData₀` and its success | same grep; `kjob/g5cv-r13:Tools/ShippingGen5Cover.lean:92` has `structure GenWFRows (d : MachineData) : Prop` (rows, not `genData₀`) | no `genData₀` definition found by the routes followed | DG-COVER, DG-DATAOF (names only) |
| `hf : DataSoundAt f` for `f := dataOfAt lvl` | `Tools.ShippingGen5DataOf.dataOfAt_sound` on `kjob/g5do-r6` `[S]` | `git merge-base --is-ancestor kjob/g5do-r6 HEAD` = not an ancestor, so the lemma is not importable at this base; integration is DG-DATAOF's merge | DG-DATAOF (name only) |
| `hev : GDEvidence f GD dOf env₀` | depends on `GenData` fields (row 1) | not supplied (follows row 1) | DG-SEM |
| **`ordCallees` and `hmem`** | `AssignKit` fields `Tools/ShippingGen5Acc.lean:37-40` `[S]`: `ordCallees : (d : MachineData) → List (Fin d.shape.insts.length)`, `mem_ordCallees : ∀ d k, k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none`; `instOrigins.getD k .ord` / `.child?` already used in `Tools/ShippingGen2Defs.lean:103,219` `[S]` | **closeable now**: the spec of `ordCallees` is a decidable filter over `Fin n` that mentions only `MachineData.shape.insts`, `instOrigins`, `child?`, all in this lineage. No new law, no TRUSTED, no shared-definition change | DG-ACC |

## 1. Chosen unit: A12 a concrete `ordCallees₀` with `hmem` (new file `Tools/ShippingGen5AccOrdCallees.lean`, imports `Tools.ShippingGen5AccMkKit`)

Reason: it is the only part of `mkKit` for which a real (non-hypothetical) definition and its law can be written from existing names. Every other part waits on other Issues' definitions. It removes `ordCallees` and `hmem` from the integration obligation and gives a `mkKit` instance shape in which those two arguments are concrete.

```lean
namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)

def ordCallees₀ (d : MachineData) : List (Fin d.shape.insts.length) :=
  (List.finRange d.shape.insts.length).filter
    (fun k => ((d.shape.instOrigins.getD k .ord).child?).isNone)

theorem ordCallees₀_mem (d : MachineData) (k : Fin d.shape.insts.length) :
    k ∈ ordCallees₀ d ↔ (d.shape.instOrigins.getD k .ord).child? = none

theorem mkKit_ordCallees₀_dataSound {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    (f : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : ConstantInfo → Type) (dOf : {E : ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : ConstantInfo) → Option (GD E))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (hev : GDEvidence f GD dOf env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E),
      (∀ k ∈ ordCallees₀ (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g)
    (hf : DataSoundAt f) :
    DataSound (mkKit f GD dOf genData₀ ordCallees₀ genSem ordCallees₀_mem hev hloc hdecl hd)
```
Proof plan: `ordCallees₀_mem`: `simp [ordCallees₀, List.mem_filter, List.mem_finRange]` (`Option.isNone_iff_eq_none`); `mkKit_ordCallees₀_dataSound := mkKit_dataSound f GD dOf genData₀ ordCallees₀ genSem ordCallees₀_mem hev hloc hdecl hd hf`. The third declaration (def 1 + theorems 2 in total: `ordCallees₀`, `ordCallees₀_mem`, `mkKit_ordCallees₀_dataSound`) — `mkKit_ordCallees₀_dataSound` — is an instantiation (shows the concrete arguments are accepted by `mkKit`); if `simp` leaves a coercion goal (`Fin` to `Nat` in `getD`), the proof is adjusted without changing the statement. The `getD k` argument is elaborated exactly as in `AssignKit.mem_ordCallees` (same `Fin` coercion), so `ordCallees₀_mem` has the field's type up to that elaboration.

Not claimed: a real `GD` / `genData₀` / `genSem`; `GenData`; `GenWF`; success of `genData₀`; `hf` for `dataOfAt lvl`; `hev` for a real run; L; C′; `ReachCover`; real run; M5; FG. A12 only fixes `ordCallees` and `hmem`.

## 2. Check plan (`Tests/Gen5/AccOrdCalleesCheck.lean`, new), same requirements as A11
- **TYPE path (Pi/statement).** `ordCallees₀`: `(← getConstInfo ``ordCallees₀).type` defeq an independently written Pi type `(d : MachineData) → List (Fin d.shape.insts.length)`. `ordCallees₀_mem` and `mkKit_ordCallees₀_dataSound` through `checkExpected` against independently written `Expected…` propositions (not obtained from the Tools file). TYPE count = 3, reported from the run.
- **BODY path (value, separate count).** The value of `ordCallees₀` compared by defeq with an independently written `fun d => (List.finRange _).filter (fun k => …isNone)` (BODY = 1).
- **MUTANT** (signature/defeq rejection only; none is a semantic counterexample; single and compound counted apart from the run). single: (a) `ordCallees₀_mem` with `child? ≠ none` in place of `= none`; (b) `ordCallees₀_mem` with `→` only (drops `←`); (c) `mkKit_ordCallees₀_dataSound` without `hf`; (d) value mutant: filter on `.isSome` instead of `.isNone` (BODY path). compound: (e) `ordCallees₀_mem` with `child? ≠ none` AND `→` only. All are well-typed or modified Pi types.
- **CLOSURE**: `closureReport` as A11 (forbidden `sorryAx / ofReduceBool / trustCompiler`; unknown = fail; root self-judgement; helper value/type unknown controls + clean). Roots `ordCallees₀`, `ordCallees₀_mem`, `mkKit_ordCallees₀_dataSound`; expected suppliers fixed apart from roots: `mkKit_dataSound`, `mkKit`; DataOf/SemGen units not reached.
- **AXIOMS**: standard three only; no `sorry` in roots (walker-control fixtures under `withoutModifyingEnv` only).
- **Build**: one target at a time in the Pod (`-c 2`, incremental). Lean commit stays `doing` ("clean build is the coder's").

## 3. Decisions
No new law / TRUSTED / shared-definition change; no decision needed. DG-ACC, M5, FG are not complete. Rows owned by DG-DATAOF / DG-SEM / DG-COVER / DG-READKINDS are named only.
