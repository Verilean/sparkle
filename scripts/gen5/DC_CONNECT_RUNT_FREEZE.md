# DC-CONNECT next unit: freeze of U-RUNT (conditional run transport `childMap D'` → `childMap D` under `NoRawBelow`) (agent g5dc-r20, base `kjob/g5dc-r19` 716d342b = U-NORAW approved, build dc19v-716d342b exit 0, 750 jobs)
**Design only; no Lean in this commit.** "Unsupplied / no route on the candidate paths traced here" is a statement about THIS investigation (this tree), not impossibility. A "mutant" is a signature/defeq rejection of a well-typed changed statement, not a semantic counterexample. No new law/TRUSTED, no shared-definition/compiler edit, FG not narrowed, `GenWF` not strengthened, no `Post` adoption. The result is a lemma layer CONDITIONAL on `NoRawBelow` and on the lookup agreement `hlk`; it is NOT a completion of (a2.4) or of FG. This freeze takes the "U-RUNT" sketch of `DC_CONNECT_NORAW_FREEZE.md` §6 (which carried no approval) and gives it a full, newly-reviewable type; the sketch itself is superseded by §3 below.

## 1. Survey (real names, candidate paths traced)
| row | finding | status |
|---|---|---|
| (a2.4c) run transport `runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) mc.body seed T s = runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) mc.body seed T s` | Sources: `evalAssignsKG`/`stepModuleTG`/`runModuleTG` (`Tools/ShippingHierStateG.lean:34,57,67`) read `children` only at the `Stmt.inst` case (`children mn`) and pass it to `KS`; `KSn children 0 = flatKS` (ignores `children`), `KSn children (n+1) = succKS (KSn children n) children`, and `succKS KS children child cwe cin env s = stepModuleTG KS cwe children child.body (connEnvS cin env s.st) s` (`:114`, `:628`). `regNexts`/`memNexts` take no `children`. `NoRawBelow D rn (n+1) mc` (`Tools/ShippingGen5DCEntryR.lean:14`) gives, for the module `mc`: every instance `mn ≠ rn`, and for every instance whose `D`-lookup succeeds with `mc'`, `NoRawBelow D rn n mc'`. With `hlk : ∀ mn, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn` this gives `childMap D' mn = childMap D mn` at each instance of the body, and by induction on `n` the two `KSn` agree on every child reached. So a depth induction (generic list/step/run congruence, then the tower) should close it with existing text only. | **closable now** (U-RUNT below); first unit chosen |
| connect core `(raw, D)` to a `closeInsts` equation (needed to apply U-NORAW to a given run) | `Tools.ShippingParentDesignA.core_closeInstsA` (`Tools/ShippingParentDesignA.lean:152`) gives the equation for a core run of a machine `MachineRanA …` with `instFields = []`; `Tools.ShippingGen2OneOut` (`:310-316`) already consumes it (via `Tools.ShippingRanABridge.machineRanA_of_runJQC`) to get `NoInstOf raw.name raw.body ∧ ∀ g ∈ D.modules, …`. How the `(raw, D)` of the `PostEntry b raw D D'` / `TopShips` context of this Issue is the `(M, D)` of such a `MachineRanA`/`MachineTaken` was NOT traced in this investigation; it needs the `ran` hypothesis of that context, which the DC units so far do not carry. | not first: premise shape (`ran`) not traced here; "this investigation found no route inside the DC-CONNECT files" — not a claim of impossibility |
| (a3) `NoRawBelow … (checkedOptimize b)` ↔ `raw`, real `EntryWitness`, `ReflectsAll`, `TopShips` on `D'`, O3, `Post`, FG | unchanged from `DC_CONNECT_SUPPLY_SURVEY.md` §14 / `DC_CONNECT_RESETN_FREEZE.md` §1 | unsupplied / no route on the candidate paths traced here |

## 2. Why U-RUNT first
Its inputs are all existing definitions and the approved `NoRawBelow` (`Tools.ShippingGen5DCEntryR`), needs no owner, no `ran` premise and no new law/TRUSTED/shared-definition change (so no decision document). It is the only remaining row whose statement and proof route are both determined by text in this tree. It is independent of how `NoRawBelow` is supplied (U-NORAW) so it composes with it later; the composition (linking a given run's `(raw, D)` to the closing equation) is not done here.

## 3. Full types (no abbreviations)
New files only: `Tools/ShippingGen5DCEntryT.lean` (namespace `Tools.ShippingGen5DCEntryT`; `import Tools.ShippingGen5DCEntryS`; `set_option autoImplicit false`; no `open`), `Tests/Gen5/DCEntryTCheck.lean`, `lean_lib` additions in `lakefile.lean`. Names fully qualified; `Env`/`WEnv` are `Sparkle.IR.Semantics.Env`/`WEnv` (both `String → Nat`, `Sparkle/IR/Semantics.lean:42-43`), `MEnv` is `Sparkle.IR.Semantics.MEnv`.
```lean
theorem childMap_transport {D D' : Sparkle.IR.AST.Design} {rn : String}
    (hlk : ∀ mn : String, mn ≠ rn →
      Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn)
    (mn : String) (hne : mn ≠ rn) :
    Tools.ShippingMachineLinked.childMap D'.modules mn = Tools.ShippingMachineLinked.childMap D.modules mn

theorem stepModuleTG_congr {σ : Type}
    {KS KS' : Tools.ShippingHierStateG.KStep σ} {we : Sparkle.IR.Semantics.WEnv}
    {ch ch' : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {body : List Sparkle.IR.AST.Stmt}
    (hch : ∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → ch' mn = ch mn)
    (hKS : ∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body →
      ∀ (c : Sparkle.IR.AST.Module) (cwe : Sparkle.IR.Semantics.WEnv), ch mn = some (c, cwe) →
        ∀ (cin : List (String × Sparkle.IR.AST.Expr)) (env : Sparkle.IR.Semantics.Env) (s : σ),
          KS' c cwe cin env s = KS c cwe cin env s)
    (env0 : Sparkle.IR.Semantics.Env) (s : Tools.ShippingHierStateG.KState σ) :
    Tools.ShippingHierStateG.stepModuleTG KS' we ch' body env0 s =
      Tools.ShippingHierStateG.stepModuleTG KS we ch body env0 s

theorem runModuleTG_congr {σ : Type}
    {KS KS' : Tools.ShippingHierStateG.KStep σ} {we : Sparkle.IR.Semantics.WEnv}
    {ch ch' : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {body : List Sparkle.IR.AST.Stmt}
    (hch : ∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → ch' mn = ch mn)
    (hKS : ∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body →
      ∀ (c : Sparkle.IR.AST.Module) (cwe : Sparkle.IR.Semantics.WEnv), ch mn = some (c, cwe) →
        ∀ (cin : List (String × Sparkle.IR.AST.Expr)) (env : Sparkle.IR.Semantics.Env) (s : σ),
          KS' c cwe cin env s = KS c cwe cin env s)
    (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) :
    ∀ (T : Nat) (s : Tools.ShippingHierStateG.KState σ),
      Tools.ShippingHierStateG.runModuleTG KS' we ch' body seed T s =
        Tools.ShippingHierStateG.runModuleTG KS we ch body seed T s

theorem KSn_transport {D D' : Sparkle.IR.AST.Design} {rn : String}
    (hlk : ∀ mn : String, mn ≠ rn →
      Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn) :
    ∀ (n : Nat) (child : Sparkle.IR.AST.Module),
      Tools.ShippingGen5DCEntryR.NoRawBelow D rn n child →
      ∀ (cwe : Sparkle.IR.Semantics.WEnv) (cin : List (String × Sparkle.IR.AST.Expr))
        (env : Sparkle.IR.Semantics.Env) (s : Tools.ShippingHierStateG.KT n),
        Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D'.modules) n child cwe cin env s =
          Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D.modules) n child cwe cin env s

theorem runModuleTG_transport {D D' : Sparkle.IR.AST.Design} {rn : String}
    (hlk : ∀ mn : String, mn ≠ rn →
      Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn) :
    ∀ (n : Nat) (mc : Sparkle.IR.AST.Module) (we : Sparkle.IR.Semantics.WEnv)
      (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) (T : Nat)
      (s : Tools.ShippingHierStateG.KState (Tools.ShippingHierStateG.KT n)),
      Tools.ShippingGen5DCEntryR.NoRawBelow D rn (n + 1) mc →
      Tools.ShippingHierStateG.runModuleTG
          (Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D'.modules) n) we
          (Tools.ShippingMachineLinked.childMap D'.modules) mc.body seed T s =
        Tools.ShippingHierStateG.runModuleTG
          (Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D.modules) n) we
          (Tools.ShippingMachineLinked.childMap D.modules) mc.body seed T s
```
Source facts to be confirmed when the file is written (a mismatch is corrected in a docs commit and re-submitted; statements are not silently changed): `KStep σ := Module → WEnv → List (String × Expr) → Env → σ → Option (Env × σ)` (`ShippingHierStateG.lean:24`); `KState σ` fields `st mems kids`; `runModuleTG` takes `seed : Nat → (String → Nat) → Env`; `childMap ms mn = (moduleByName ms mn).map fun c => (c, declWidth c)` (`ShippingMachineLinked.lean:341`).

Proof routes (no new axioms). `childMap_transport`: `unfold childMap; rw [hlk mn hne]`. `stepModuleTG_congr`: unfold; first prove by induction on the statement list `l` the generalisation of `evalAssignsKG KS' we ch' kids mems l env acc = evalAssignsKG KS we ch kids mems l env acc` for any `l` whose `Stmt.inst` members satisfy `hch`/`hKS` (cases `assign`/`register`/`memory` by `simp only [evalAssignsKG]` + IH; `inst`: rewrite `hch`, then `cases ch mn`, then `hKS` for the `some` branch); the rest of `stepModuleTG` (`regNexts`, `memNexts`, `applyNexts`) mentions neither `KS` nor `children`. `runModuleTG_congr`: induction on `T` with `stepModuleTG_congr` and the IH. `KSn_transport`: induction on `n`. `n = 0`: `KSn _ 0 = flatKS` on both sides, `rfl`. `n+1`: unfold `KSn`/`succKS`, apply `stepModuleTG_congr` with `KS := KSn (childMap D.modules) n`, `KS' := KSn (childMap D'.modules) n`: `hch` from `childMap_transport` and the first conjunct of `NoRawBelow D rn (n+1) child` (`mn ≠ rn`); `hKS` from the IH, where `childMap D.modules mn = some (c, cwe)` unfolds to `moduleByName D.modules mn = some c'` (with `c = c'`) so the second conjunct gives `NoRawBelow D rn n c'`. `runModuleTG_transport`: `runModuleTG_congr` with `KS := KSn (childMap D.modules) n`, the same `hch`/`hKS` obtained as above from `NoRawBelow D rn (n+1) mc` and `KSn_transport n`. If a proof does not go through as stated, the statement is NOT changed (stop and report).

## 4. Check plan (`Tests/Gen5/DCEntryTCheck.lean`; same requirements as U-NORAW)
- **TYPE:** independent `Exp*` for the five theorems written from the prose of §3 (not copied from the source), compared by `Tests.Gen3.ExpectedType.checkExpected` under `withReducible`; self-comparison positive controls not counted and reported separately. **Source pins:** the CONSTANT TYPES of `Tools.ShippingHierStateG.stepModuleTG`, `runModuleTG`, `KSn` and `Tools.ShippingGen5DCEntryR.NoRawBelow` compared with independently written Expected types so a source drift is detected (`NoRawBelow` is a definition: pin its type, not its equations, equations having been pinned in U-RESETN).
- **MUTANT** (well-typed single change; signature/defeq rejection, NOT semantic counterexamples; any block change labelled and counted separately from single changes): `hlk` dropped; `mn ≠ rn` dropped in `hlk` (all mn); `NoRawBelow D rn (n+1) mc` replaced by `NoRawBelow D rn n mc`; replaced by `NoRawBelow D' rn (n+1) mc`; `NoRawBelow D rn (n+1) mc` dropped; `KSn … n` on the right replaced by `KSn … (n+1)`; `childMap D.modules` replaced by `childMap D'.modules` on the right (both sides equal); `mc.body` replaced by `mc.body.reverse` on one side; in `hKS`, `ch mn = some (c, cwe)` replaced by `ch' mn = some (c, cwe)`; `hch` conclusion `ch' mn = ch mn` replaced by `ch mn = ch mn`; `T`-quantifier fixed to `0`; `KS'` replaced by `KS` in `hKS` conclusion. In `childMap_transport`, `hne` dropped. Only the changes that elaborate are counted; those that do not elaborate are reported as not adopted. Counts are reported as measured, split single / block.
- **CONJ:** none (no conjunctive statement), stated as 0; a negative control for each source pin (a changed expected pin is rejected) is counted under SOURCE-PIN NEG, separately, and recorded in the header.
- **CLOSURE:** `DeclConnectCheck` walker (root judged itself; unknown name = FAIL); required names per root: `childMap_transport`: `childMap`, `moduleByName`; `stepModuleTG_congr`: `stepModuleTG`, `evalAssignsKG`; `runModuleTG_congr`: `runModuleTG`, `stepModuleTG_congr`; `KSn_transport`: `KSn`, `succKS`, `NoRawBelow`, `stepModuleTG_congr`, `childMap_transport`; `runModuleTG_transport`: `runModuleTG_congr`, `KSn_transport`, `NoRawBelow`. Positive/negative controls (an unreached required name detected; an extra clean root); unknown-name fixtures (type alone, value alone); intended name asserted; `withoutModifyingEnv`; afterwards the CURRENT env (`getEnv`) inspected for leaks.
- **AXIOMS:** `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`/`native_decide`.
- STATUS line lists NOT supplied: linking a given core run's `(raw, D)` to a `closeInsts` equation (and hence to `NoRawBelow`), (a3), (b1), (b2), (c4 import), (c5), (c6), (c7), real `EntryWitness`, `ReflectsAll`, `TopShips` on `D'`, O3, parametrised-route post-processing, `Post` adoption, FG.
- Builds are the coder's (clean issue-linked); an agent incremental build is labelled NOT clean, and a NOT BUILT header is used until then.

## 5. Not claimed
That any compiler/core run satisfies `NoRawBelow` or `hlk`; the link of `(raw, D)` to the closing equation (§1 row 2, not traced); `TopShips` on `D'`; O3 identification; `EntryWitness`/`ReflectsAll`; `Post` adoption; FG completion; M5. The Issue stays open.
