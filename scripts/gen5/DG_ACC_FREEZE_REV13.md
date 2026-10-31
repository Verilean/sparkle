# DG-ACC freeze rev13 (issue `sparkle-gen5-dg-acc`): survey of real GD / hev / hf / laws / coverage, and the next unit A13 (`GDf`, `genDataF`, f-derived evidence and success)

**FOR REVIEW (docs only; no Lean for A13 is written until this is approved).** Rev1-rev12 unchanged. Base: `kjob/g5ac-r25` 86c45108 (A12 approved; clean build `ac25v-86c45108`, exit 0, 730 jobs; closure reported by that log: 6664 constants, the 7567 in the earlier note is corrected). Header sync committed at a2f51ea8 (comment only): A12 Tools/Check headers cite `ac25v-86c45108` and closure 6664.

Tags: `[S]` source read (this worktree, or a named branch via `git show` / `git grep`). Nothing below was elaborated or built.
Wording: "not supplied / no route found" = the candidate routes followed in this survey did not reach a supplier; never "impossible". Conditional results are INTERMEDIATE, never completion. Mutants are signature/defeq rejections, not semantic counterexamples.

## 0. Survey (rows; each: routes followed, result, owner)

| row | routes followed | result | owner |
|---|---|---|---|
| real `GD` = DG-SEM `GenData E (structEnv env₀)`, `dOf` | `git grep -E "structure GenData\|def genData₀\|def genSem "` over `Tools/` on `kjob/g5sm-u21`, `kjob/g5sm-u20`, `kjob/g5cv-r13` and every `kjob/g5do-*` branch `[S]` | no Lean `GenData` structure found; `kjob/g5sm-u20` ... `u21` carry docs (`scripts/gen5/DG_SEM_FREEZE_P8.md`) only | DG-SEM (name only) |
| `genSem` / `hloc` / `hdecl` / `hd` | `Tools/ShippingGen5SemGen.lean` here: `genSemGenE (X) (g : GenIn) (eb : ExtB ..) (ev : ExtV ..) : SrcSem` `[S]` | `GenIn` needs `wf : GenWF d = true` and the extension families `eb`/`ev` built from `Q`; no route found to a function with `AssignKit.genSem`'s type on this lineage | DG-SEM, DG-WFCOVER (names only) |
| `hf : DataSoundAt (dataOfAt lvl)` | `dataOfAt_sound` at `kjob/g5do-r6:Tools/ShippingGen5DataOf.lean:211` `[S]` | `git merge-base --is-ancestor kjob/g5do-r6 HEAD` = not an ancestor: not importable here; integration is DG-DATAOF's | DG-DATAOF (name only) |
| `hev : GDEvidence f GD dOf env₀` for the real `GenData` | needs `GenData.hshape/hdata` | not supplied (follows row 1) | DG-SEM |
| `hmem` / `ordCallees` | A12 | **done** (approved) | DG-ACC |
| success coverage of `genData₀` for real runs | `GenWFRows` at `kjob/g5cv-r13:Tools/ShippingGen5Cover.lean:92` | statement only; no `genData₀ E = some _` for a real `E` found | DG-COVER (name only) |
| **`hev` and success of `genData₀` for a GD built from `f` itself** | the definitions `GDEvidence`, `DataSoundAt`, `machineShape?`, `structEnv` in this lineage `[S]` | **closeable now** with existing names only: a replacement-point type whose elements carry exactly the evidence fields, and its `genData₀` | DG-ACC |

Honest scope of the last row: the GD is derived from `f`, not DG-SEM's `GenData`; it does not give `genSem` (so it cannot yet fill `mkKit`), and it is a different type from the eventual `GenData`. What it gives: the evidence row `hev` and the success characterization of a `genData₀` for a concrete `GD`, proved from `f` alone, so the integration only has to match fields (`hshape/hdata`) of the real `GenData`.

## 1. Chosen unit A13 (new file `Tools/ShippingGen5AccGDf.lean`, imports `Tools.ShippingGen5AccOrdCallees`)

Reason: it is the only remaining row (apart from the rows owned by other Issues) closable from existing names; it makes `hev` real (not hypothetical) and states exactly when `genData₀` succeeds, which is the data the coverage rows need.

```lean
namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)

def GDf (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Environment)
    (E : ConstantInfo) : Type :=
  { p : MachineShape × MachineData //
      machineShape? false [] E (structEnv env₀) = some p.1 ∧ f E (structEnv env₀) p.1 = some p.2 ∧ p.2.shape = p.1 }

def dOfF (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Environment)
    {E : ConstantInfo} (g : GDf f env₀ E) : MachineData := g.val.2

open Classical in
noncomputable def genDataF (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Environment)
    (E : ConstantInfo) : Option (GDf f env₀ E) :=
  if h : ∃ p : MachineShape × MachineData,
      machineShape? false [] E (structEnv env₀) = some p.1 ∧ f E (structEnv env₀) p.1 = some p.2 ∧ p.2.shape = p.1
  then some ⟨h.choose, h.choose_spec⟩ else none

theorem genDataF_evidence (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Environment) :
    GDEvidence f (GDf f env₀) (fun {E} g => dOfF f env₀ g) env₀

theorem genDataF_isSome_iff (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Environment)
    (E : ConstantInfo) :
    (genDataF f env₀ E).isSome = true ↔
      ∃ (s : MachineShape) (d : MachineData),
        machineShape? false [] E (structEnv env₀) = some s ∧ f E (structEnv env₀) s = some d ∧ d.shape = s

theorem genDataF_isSome_of_sound (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Environment)
    (hf : DataSoundAt f) (E : ConstantInfo) (s : MachineShape) (d : MachineData)
    (hs : machineShape? false [] E (structEnv env₀) = some s) (hd : f E (structEnv env₀) s = some d) :
    (genDataF f env₀ E).isSome = true
```
Proof plan: `genDataF_evidence`: intro E g; `g.property` gives `machineShape? .. = some g.val.1`, `f .. g.val.1 = some g.val.2`, `g.val.2.shape = g.val.1`; rewrite `dOf g = g.val.2`, `shape = g.val.1`. `isSome_iff`: unfold `genDataF`, `split`; the witness `⟨s, d⟩`. `isSome_of_sound`: `(hf E _ s d hd).1` gives `d.shape = s`, then `isSome_iff.2`. Uses classical choice only for `genDataF` (`Classical.choice` is in the standard axiom set).

Not claimed: DG-SEM `GenData`, `GenWF`, `genSem`, `hloc/hdecl/hd`, `hf` for `dataOfAt lvl`, success on a real run (`genDataF_isSome_of_sound` is conditional on `hs`, `hd`, `hf` hypotheses), L, C′, `ReachCover`, real run, M5, FG. DG-ACC is not complete.

## 2. Check plan (`Tests/Gen5/AccGDfCheck.lean`, new), same requirements as A12 (Expected written independently of the Tools file)
- **TYPE** (Pi/statement): `GDf` / `dOfF` / `genDataF` through `getConstInfo.type` vs independently written Pi types (3); the three theorems through `checkExpected` vs independent `Expected…` (3). TYPE count = 6 reported from the run.
- **BODY** (values, counted apart): the value of `GDf` (subtype body) vs an independently written lambda; `dOfF` value vs `fun _ _ _ g => g.val.2`. BODY = 2.
- **MUTANT** (signature/defeq rejection; not semantic counterexamples; single/compound counted apart, well-typed or modified Pi only): single: (a) `genDataF_isSome_iff` with `d.shape = s` dropped; (b) `genDataF_isSome_iff` direction `→` only; (c) `genDataF_isSome_of_sound` without `hf`; (d) `genDataF_evidence` with `dataOf := f` replaced by `fun _ _ _ => none` (modified statement). compound: (e) (a) AND (c). Count from the run.
- **CLOSURE**: `closureReport` as A12 (forbidden `sorryAx / ofReduceBool / trustCompiler`; unknown = fail; root self-judgement; helper value/type unknown controls + clean). Roots: `GDf`, `dOfF`, `genDataF`, three theorems; expected suppliers (distinct from roots): `GDEvidence`, `DataSoundAt`; DataOf/SemGen units not reached.
- **AXIOMS**: standard only (`propext`, `Classical.choice`, `Quot.sound`); no `sorry` in roots (walker fixtures under `withoutModifyingEnv` only).
- **Build**: one target at a time (`kjob lake build`, `-c 2`, incremental). Lean commit stays `doing` ("clean build is the coder's").

## 3. Decisions
No new law / TRUSTED / shared-definition or compiler change; no decision needed. DG-ACC, M5, FG are not complete. Rows owned by DG-DATAOF / DG-SEM / DG-COVER / DG-WFCOVER are named only.

## 4. Implementation record (A13, Lean written after approval)
Files: `Tools/ShippingGen5AccGDf.lean`, `Tests/Gen5/AccGDfCheck.lean`, two `lean_lib` entries in `lakefile.lean`. Types as in §1 (the Check compares them with independently written Expected). Pod incremental build exit 0 (Tools 728 jobs, Check 731 jobs): TYPE 6 / BODY 2 / MUTANT 5 (single 4 + compound 1; signature/defeq rejection, not semantic counterexamples) / AXIOMS standard only / CLOSURE 6472 constants, unknown 0, suppliers `GDEvidence`/`DataSoundAt` reached. Clean issue-linked build: the coder's.

Premises resolved by A13: `hev` for the f-derived `GDf` (`genDataF_evidence`, unconditional); success characterization of `genDataF` (`genDataF_isSome_iff`).
Premises introduced (hypotheses of `genDataF_isSome_of_sound`): `hf : DataSoundAt f`, shape witness `hs`, success of `f` (`hd`).
Still not supplied: real DG-SEM `GenData` (`GDf` is a different type), `genSem`/laws, `hf` for `dataOfAt lvl`, success of a real run, coverage, L, C', `ReachCover`, M5, FG, S1.
