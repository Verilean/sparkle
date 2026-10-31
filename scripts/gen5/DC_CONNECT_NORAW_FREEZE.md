# DC-CONNECT next unit: freeze of U-NORAW (`NoRawBelow` from the closing's acyclicity facts) (agent g5dc-r18, base `kjob/g5dc-r17` 1c948e47 = U-RESETN approved, build dc17v-1c948e47 exit 0, 749 jobs)
**Design only; no Lean in this commit.** "Unsupplied / no route on the candidate paths traced here" is a statement about THIS investigation (this tree), not impossibility. A "mutant" is a signature/defeq rejection of a well-typed changed statement, not a semantic counterexample. No new law/TRUSTED, no shared-definition/compiler edit, FG not narrowed, `GenWF` not strengthened, no `Post` adoption. The result is a lemma layer conditional on a `closeInsts`/`closeInstsG` equation; it is NOT a completion of (a2.4) or of FG.

## 1. Survey after U-RESETN (real names, candidate paths traced)
| row | finding | status |
|---|---|---|
| (a2.4b) `NoRawBelow D rn n mc` | `Tools.ShippingHierMono.NoInstOf (t : String) (body : List Stmt) : Prop := ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → mn ≠ t` (`Tools/ShippingHierMono.lean:119`). `Tools.ShippingChildServe.closeInsts_acyclic` (`Tools/ShippingChildServe.lean:200`) from `Sparkle.IR.Machine.closeInsts … (m₀, d₀) = some (m, d)` gives `NoInstOf m.name m.body` and `∀ g ∈ d.modules, NoInstOf m.name g.body`; `closeInstsG_acyclic` (`:223`) gives the same two for `closeInstsG`. `NoRawBelow` is exactly what these two facts give by induction on the depth, because a successful `moduleByName d.modules mn = some mc'` puts `mc'` in `d.modules` (`List.find?` result is a member). The existing user is `Tools/ShippingGen2OneOut.lean:310-316`, which takes the same two facts for `raw.name` / `D` from `core_closeInstsA` (`Tools/ShippingParentDesignA.lean:152`). | **closable now** (U-NORAW below). This replaces "this investigation found no route" for the CLOSING equation; it does not link a given core run's `(raw, D)` to that equation (see §5). |
| (a2.4c) the `childMap`-dependent run `runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) mc.body seed T s = runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) mc.body seed T s` | `runModuleTG`/`stepModuleTG`/`evalAssignsKG` (`Tools/ShippingHierStateG.lean:34,57,67`) read `children` only at `Stmt.inst` lookups and through `KSn` (`flatKS` ignores `children`; `succKS (KSn k) children` runs the child with `stepModuleTG`); `regNexts`/`memNexts`/`comboReads` take no `children`. Under `NoRawBelow D rn (n+1) mc` and `hlk` (as in `resetN_transport`) an induction on `n` (KS-level, then step-level, then `T`) should close it. | **closable, NEXT unit** (not frozen here; listed in §6 with its intended types). Not first: it takes `NoRawBelow` as a premise and is independent of U-NORAW, so U-NORAW first only removes the "unsupplied" label. |
| real `EntryWitness` / `ReflectsAll`, (a3), (b1), (b2), (c4 import), (c5), (c6), (c7), parametrised-route post-processing | unchanged from `DC_CONNECT_SUPPLY_SURVEY.md` §14 / `DC_CONNECT_RESETN_FREEZE.md` §1 | unsupplied / no route on the candidate paths traced here |

## 2. Why U-NORAW first
It is the only candidate whose inputs are all existing text (`closeInsts_acyclic`, `closeInstsG_acyclic`, `NoInstOf`, `NoRawBelow`, `moduleByName`), needs no owner, and turns the stated residual (a2.4b) from "unsupplied" into a derivation from the closing equation that the compiler's `closeInsts` check provides. It does not need (a2.4c). No new law/TRUSTED/shared-definition change is needed, so no decision document.

## 3. Full types (no abbreviations)
New files only: `Tools/ShippingGen5DCEntryS.lean` (namespace `Tools.ShippingGen5DCEntryS`; `import Tools.ShippingGen5DCEntryR`, `import Tools.ShippingChildServe`; `set_option autoImplicit false`), `Tests/Gen5/DCEntrySCheck.lean`, `lean_lib` additions in `lakefile.lean`. Names fully qualified (`Module`/`Design` are `Sparkle.IR.AST.Module`/`Sparkle.IR.AST.Design`).
```lean
theorem noRawBelow_of_noInstOf {D : Sparkle.IR.AST.Design} {rn : String}
    (hD : ∀ g ∈ D.modules, Tools.ShippingHierMono.NoInstOf rn g.body) :
    ∀ (n : Nat) (mc : Sparkle.IR.AST.Module),
      Tools.ShippingHierMono.NoInstOf rn mc.body → Tools.ShippingGen5DCEntryR.NoRawBelow D rn n mc

theorem noRawBelow_of_closeInsts {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : List (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)}
    {m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : Sparkle.IR.Machine.closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)) :
    ∀ k : Nat, Tools.ShippingGen5DCEntryR.NoRawBelow d m.name k m

theorem noRawBelow_of_closeInstsG {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {fields : List String}
    {children : List (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)}
    {m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : Sparkle.IR.Machine.closeInstsG nIn kI n portNames insts fields children (m₀, d₀) = some (m, d)) :
    ∀ k : Nat, Tools.ShippingGen5DCEntryR.NoRawBelow d m.name k m
```
Source confirmed: `closeInsts`'s parameters are `(nIn kI n : Nat) (portNames : List String) (insts : List (List Nat)) (children : List (Module × Design)) (md : Module × Design) : Option (Module × Design)` (`Sparkle/IR/Machine.lean:396`); `closeInstsG` adds `(fields : List String)` before `children` (`Sparkle/IR/MachineInstG.lean:115`); the hypothesis shapes are those of the two `_acyclic` theorems. If a name or order differs when the file is written, the freeze is corrected in a docs commit and re-submitted; statements are not silently changed.

Proof route. `noRawBelow_of_noInstOf`: induction on `n`. `n = 0`: `NoRawBelow … 0 _ = True`, `trivial`. `n+1`: `unfold`/`show` the pair; first conjunct is the `NoInstOf rn mc.body` hypothesis; second: given `Stmt.inst mn iname conns ∈ mc.body` and `moduleByName D.modules mn = some mc'`, `List.mem_of_find?_eq_some` (`moduleByName ms mn = ms.find? (fun c => c.name == mn)`, `Sparkle/IR/Machine.lean:359`) gives `mc' ∈ D.modules`, so `hD mc' _ : NoInstOf rn mc'.body`, and the induction hypothesis gives `NoRawBelow D rn n mc'`. `noRawBelow_of_closeInsts`/`…G`: `obtain ⟨-, h1, h2, -⟩ := closeInsts_acyclic h` (resp. `⟨-, h1, h2⟩ := closeInstsG_acyclic h`), then `fun k => noRawBelow_of_noInstOf h2 k m h1`. If a proof does not go through as stated, the statement is NOT changed (stop and report).

## 4. Check plan (`Tests/Gen5/DCEntrySCheck.lean`; same requirements as U-RESETN)
- **TYPE:** independent `Exp*` for the three theorems written from the prose of §3, compared by `Tests.Gen3.ExpectedType.checkExpected` under `withReducible`; self-comparison positive controls not counted. No new definition, so no definition-equation pin; instead the check compares the CONSTANT TYPES of the two source theorems it relies on (`closeInsts_acyclic`, `closeInstsG_acyclic`) with independently written Expected statements, so a source drift is detected.
- **MUTANT** (well-typed single change; signature/defeq rejection, NOT semantic counterexamples; any block change labelled and counted separately from single changes): `hD` dropped in `noRawBelow_of_noInstOf`; the `NoInstOf rn mc.body` hypothesis dropped; `NoInstOf rn` replaced by `NoInstOf mc.name` in `hD`; `m.name` replaced by `m₀.name` in the `closeInsts` conclusion; `d` replaced by `d₀` in the conclusion; `= some (m, d)` replaced by `= some (m₀, d₀)`; `∀ k` replaced by `0 < k →`-free fixed depth `0`; `NoRawBelow` conclusion replaced by `NoInstOf m.name m.body` only; for `closeInstsG`, `fields` dropped is NOT well-typed and is not counted. Counts are reported as measured, split single / block.
- **CONJ:** none (no conjunctive statement); stated as 0, not omitted.
- **CLOSURE:** `DeclConnectCheck` walker (root judged itself; unknown name = FAIL); required names per root: `noRawBelow_of_noInstOf`: `NoRawBelow`, `NoInstOf`, `moduleByName`; `noRawBelow_of_closeInsts`: `closeInsts`, `closeInsts_acyclic`, `noRawBelow_of_noInstOf`; `noRawBelow_of_closeInstsG`: `closeInstsG`, `closeInstsG_acyclic`, `noRawBelow_of_noInstOf`. Positive/negative controls (an unreached required name detected; an extra clean root); unknown-name fixtures (type alone, value alone); intended name asserted; `withoutModifyingEnv`; afterwards the CURRENT env (`getEnv`) inspected for leaks.
- **AXIOMS:** `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`/`native_decide`.
- STATUS line lists NOT supplied: linking a core run's `(raw, D)` to the `closeInsts` equation, (a2.4c) run transport, (a3), (b1), (b2), (c4 import), (c5), (c6), (c7), real `EntryWitness`, `ReflectsAll`, parametrised-route post-processing, `Post` adoption, FG.
- Builds are the coder's (clean issue-linked); an agent incremental build is labelled NOT clean, and a NOT BUILT header is used until then.

## 5. Not claimed
That the `(raw, D)` returned by a given `synthesizeCombinationalCore` run satisfies a `closeInsts`/`closeInstsG` equation (this investigation did not trace that link in `oneOut_composedNW` (`Tools/ShippingGen2OneOut.lean:300-316`) or elsewhere beyond the use quoted in §1; it is an obligation of the composition, not claimed here); that `NoRawBelow` holds for the parametrised route; run transport; `TopShips` on `D'`; O3 identification; `EntryWitness`/`ReflectsAll`; `Post` adoption; FG completion; M5. The Issue stays open.

## 6. Next unit after U-NORAW (not frozen here; separate freeze): U-RUNT, intended types
```lean
theorem runModuleTG_transport {D D' : Sparkle.IR.AST.Design} {rn : String}
    (hlk : ∀ mn : String, mn ≠ rn →
      Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn) :
    ∀ (n : Nat) (mc : Sparkle.IR.AST.Module) (we : Sparkle.IR.Semantics.WEnv)
      (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) (T : Nat)
      (s : Tools.ShippingHierStateG.KState (Tools.ShippingHierStateG.KT n)),
      Tools.ShippingGen5DCEntryR.NoRawBelow D rn (n + 1) mc →
      Tools.ShippingHierStateG.runModuleTG (Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D'.modules) n) we
        (Tools.ShippingMachineLinked.childMap D'.modules) mc.body seed T s =
      Tools.ShippingHierStateG.runModuleTG (Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D.modules) n) we
        (Tools.ShippingMachineLinked.childMap D.modules) mc.body seed T s
```
(namespaces of `WEnv`/`Env` to be confirmed against the source when frozen; `mc` is the module whose body is run, so for `TopShips` it is `checkedOptimize b`, and relating `NoRawBelow … (checkedOptimize b)` to `raw` is the (a3) row, unsupplied.) This sketch is not a freeze and carries no approval.
