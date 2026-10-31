# DC-CONNECT next unit: freeze of U-CORENR (`NoRawBelow` and `hlk` for a REAL core run; real core → closing connection) (agent g5dc-r22, base `kjob/g5dc-r21` 0fcce4e7 = U-RUNT approved, build dc21v-0fcce4e7 exit 0, 751 jobs)
**Design only; no Lean in this commit.** "Unsupplied / no route on the candidate paths traced here" is a statement about THIS investigation (this tree), not impossibility. A "mutant" is a signature/defeq rejection of a well-typed changed statement, not a semantic counterexample. No new law/TRUSTED, no shared-definition/compiler edit, FG not narrowed, `GenWF` not strengthened, no `Post` adoption. The result is CONDITIONAL on `MachineDefines`, `MachineClosesAtA`, `Start`, and `insts ≠ []`/`instFields = []`; it is an intermediate result, not FG, not a supplied `EntryWitness`/`ReflectsAll`.
Header sync (comment only) was committed first: `Tools/ShippingGen5DCEntry{R,T}.lean`, `Tests/Gen5/DCEntryTCheck.lean` now cite build dc21v-0fcce4e7; counts read "TYPE 5 + self-comparison 5, SOURCE-PIN 4 / PIN-NEG 4, MUT 39" (the 10 TYPE OK lines are not 10 independent comparisons).

## 1. Survey (real names, candidate paths traced)
| row | finding | status |
|---|---|---|
| `hlk` (lookup agreement `D'` vs `D` at names `≠ rn`) | `Tools.ShippingGen5DCEntryN.postEntry_lookup_ne` (`Tools/ShippingGen5DCEntryN.lean:84`, approved, built): `PostEntry b raw D D' → mn ≠ raw.name → moduleByName D'.modules mn = moduleByName D.modules mn ∧ childMap D'.modules mn = childMap D.modules mn`. Its first conjunct, for all `mn`, is exactly `hlk` with `rn := raw.name`. | **closable now** from an existing approved lemma (theorem 2 below). Earlier notes call `hlk` "conditional input"; for `rn := raw.name` and a `PostEntry` it is a projection. |
| `NoRawBelow D raw.name k raw` from a real core run | Route traced: `Tools.ShippingServedRealA.machineRunJQC_of_closesA` (`Tools/ShippingServedRealA.lean:97`) from the run, `MachineDefines`, `MachineClosesAtA`, `JQ O.quiet 0 w` (from `Start`: `Start L mctx cctx w := AdmCtx L.O.quiet mctx cctx ∧ JQC L.O 0 w`, `JQC O n w := JQ O.quiet n w ∧ CacheInvA O (cv w)`) gives `MachineRunJQC O mctx cctx (0+1) declName shape raw D`; `Tools.ShippingRanABridge.machineRanA_of_runJQC` (`Tools/ShippingRanABridge.lean:38`, premises `O`, `hA`, `L.T`) gives `MachineRanA`; `Tools.ShippingParentDesignA.core_closeInstsA` (`Tools/ShippingParentDesignA.lean:152`, premises `d : MachineData`, `d.shape.insts ≠ []`, `d.shape.instFields = []`) gives `closeInsts … = some (raw, D)`; `Tools.ShippingChildServe.closeInsts_acyclic` and U-NORAW `noRawBelow_of_closeInsts` (approved) give `∀ k, NoRawBelow D raw.name k raw`. The same chain (without `Start`, with `MachineTaken` as a premise) is used by `oneOut_childShips` (`Tools/ShippingGen2OneOut.lean:310-316`) and the `JQ`-and-`MachineTaken` derivation by `Tools/ShippingGen2T1.lean:187,242`. The previous freezes said the `ran` premise was not traced; this survey traced it. | **closable now** (theorem 1 below), conditional on `MachineDefines`, `MachineClosesAtA`, `Start`, `insts ≠ []`, `instFields = []` |
| composition for the core module `raw` | `runModuleTG_transport` (U-RUNT, approved) at `mc := raw` with theorem 1 (depth `n+1`) and theorem 2 | **closable now** (theorem 3). Runs the body of `raw`, NOT of `checkedOptimize b`; relating the two is row (a3), not supplied. |
| leaf case (`insts = []`) | `core_closeInstsA` needs `insts ≠ []`; no route for `insts = []` traced here (`LeafStmt` has `p.d.shape.insts = []`; `NoRawBelow` from a leaf's `raw.body` having no `inst` statement was not traced) | not supplied on the candidate paths traced |
| `MachineDefines`, `MachineClosesAtA` themselves, `Start`, real `EntryWitness`/`ReflectsAll` | `MachineDefines` = `ReflectsAll` content (owner dg-env / dg-readkinds / M4); `Start` is part of `EntryWitness` | unsupplied (kept as premises) |
| (a3) `NoRawBelow … (checkedOptimize b)` ↔ `raw`; `TopShips` on `D'`; O3 (b1)(b2); (c4 import)(c5)(c6)(c7); parametrised-route post-processing; `Post`; FG | unchanged | unsupplied / no route on the candidate paths traced here |

## 2. Why U-CORENR first
It is the only remaining row whose inputs are all existing approved or built text, it replaces the two "unsupplied" labels (hlk, NoRawBelow for a real run) by derivations from a stated, entry-side premise set, and it is the first lemma to connect the real core run to the closing equation. It needs no owner, and no new law/TRUSTED/shared-definition change (so no decision document). The other candidates (`EntryWitness`/`ReflectsAll`, (a3), (b), (c4)–(c7)) have no route in this tree.

## 3. Full types (no abbreviations)
New files only: `Tools/ShippingGen5DCEntryU.lean` (namespace `Tools.ShippingGen5DCEntryU`; `import Tools.ShippingGen5DCEntryT`, `import Tools.ShippingGen5DCEntryN`, `import Tools.ShippingGen5DCEntryW`, `import Tools.ShippingParentDesignA`, `import Tools.ShippingRanABridge`, `import Tools.ShippingServedRealA`; `set_option autoImplicit false`), `Tests/Gen5/DCEntryUCheck.lean`, `lean_lib` additions in `lakefile.lean`. Names fully qualified; `Void IO.RealWorld` as in `EntryWitness`.
```lean
theorem noRawBelow_of_coreRun
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ []) (hf : d.shape.instFields = []) :
    ∀ k : Nat, Tools.ShippingGen5DCEntryR.NoRawBelow D raw.name k raw

theorem hlk_of_postEntry {b raw : Sparkle.IR.AST.Module} {D D' : Sparkle.IR.AST.Design}
    (h : Tools.ShippingGen5DCEntryD.PostEntry b raw D D') :
    ∀ mn : String, mn ≠ raw.name →
      Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn

theorem coreRun_transport
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Sparkle.IR.AST.Module} {D D' : Sparkle.IR.AST.Design}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : Tools.ShippingGen5DCEntryD.PostEntry b raw D D')
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ []) (hf : d.shape.instFields = [])
    (n : Nat) (we : Sparkle.IR.Semantics.WEnv)
    (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) (T : Nat)
    (s : Tools.ShippingHierStateG.KState (Tools.ShippingHierStateG.KT n)) :
    Tools.ShippingHierStateG.runModuleTG
        (Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D'.modules) n) we
        (Tools.ShippingMachineLinked.childMap D'.modules) raw.body seed T s =
      Tools.ShippingHierStateG.runModuleTG
        (Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D.modules) n) we
        (Tools.ShippingMachineLinked.childMap D.modules) raw.body seed T s
```
Source facts to confirm when the file is written (a mismatch is corrected in a docs commit and re-submitted; statements are not silently changed): `MachineData` is `Tools.ShippingMachineAuto.MachineData` (`Tools/ShippingMachineAuto.lean:172`) with field `shape`; the exact namespaces of `Laws`/`Start` (`Tools.ShippingGen2`), `MachineClosesAtA` (`Tools.ShippingChildRunAKids`), `MachineDefines` (`Tools.ShippingMachineEntry`); `core_closeInstsA`'s implicit `mctx cctx` and `c`.

Proof routes (no new axioms). Theorem 1: `obtain ⟨hA, hj0⟩ := hS`; `have taken := Tools.ShippingServedRealA.machineRunJQC_of_closesA L.O hA hr hdef hcl hj0.1 (Or.inl rfl)` (type `MachineRunJQC L.O mctx cctx (0+1) declName d.shape raw D`); `have ranA := Tools.ShippingRanABridge.machineRanA_of_runJQC L.O hA L.T taken`; `obtain ⟨_, _, _, _, _, _, _, _, hcl', _⟩ := Tools.ShippingParentDesignA.core_closeInstsA L.O d hins hf ranA` (the same destructuring as `Tools/ShippingGen2OneOut.lean:313`); then `noRawBelow_of_closeInsts hcl'`. Theorem 2: `fun mn hne => (Tools.ShippingGen5DCEntryN.postEntry_lookup_ne h hne).1`. Theorem 3: `Tools.ShippingGen5DCEntryT.runModuleTG_transport (hlk_of_postEntry hpost) n raw we seed T s (noRawBelow_of_coreRun d hS hr hdef hcl hins hf (n+1))`. If a proof does not go through as stated, the statement is NOT changed (stop and report).

## 4. Check plan (`Tests/Gen5/DCEntryUCheck.lean`; same requirements as U-RUNT)
- **TYPE:** independent `Exp*` for the three theorems written from the prose of §3 (not copied from the source), compared by `Tests.Gen3.ExpectedType.checkExpected` under `withReducible`; self-comparison positive controls not counted and reported separately. **Source pins:** constant types of `postEntry_lookup_ne`, `core_closeInstsA`, `machineRunJQC_of_closesA`, `machineRanA_of_runJQC`, `Start` compared with independently written Expected types so a source drift is detected; each with a negative control (a changed Expected pin is rejected), counted under SOURCE-PIN NEG.
- **MUTANT** (well-typed single change; signature/defeq rejection, NOT semantic counterexamples; block changes labelled and counted separately): theorem 1: `hS` dropped; `hdef` dropped; `hcl` dropped; `hins` dropped; `hf` dropped; `hf` replaced by `d.shape.instFields ≠ []`; `raw.name` replaced by `declName.toString`; `D` replaced by an unrelated design; `∀ k` replaced by fixed `0`; `RunsTo … [] false` replaced by `[] true`; `Start` replaced by `JQC L.O 0 w` alone. Theorem 2: `hne` dropped; `D'`/`D` swapped in the conclusion; `PostEntry b raw D D'` replaced by `PostEntry b raw D' D`. Theorem 3: `hpost` dropped; `hS` dropped; `hr` dropped; `raw.body` replaced by `(checkedOptimize b).body` on one side only (ill-typed? reported as measured); `childMap D.modules` replaced by `childMap D'.modules` on the right; `KSn … n` replaced by `n+1` (reported as not adopted if ill-typed). Only the changes that elaborate are counted; those that do not are reported as not adopted. Counts reported as measured, split single / block.
- **CONJ:** none, stated as 0.
- **CLOSURE:** `DeclConnectCheck` walker (root judged itself; unknown name = FAIL); required names per root: theorem 1: `machineRunJQC_of_closesA`, `machineRanA_of_runJQC`, `core_closeInstsA`, `noRawBelow_of_closeInsts`; theorem 2: `postEntry_lookup_ne`; theorem 3: `runModuleTG_transport`, `hlk_of_postEntry`, `noRawBelow_of_coreRun`. Forbidden: none beyond the ordinary core/opaque boundary leaves, which are reported. Positive/negative controls (an unreached required name detected; an extra clean root); unknown-name fixtures (type alone, value alone); intended name asserted; `withoutModifyingEnv`; afterwards the CURRENT env inspected for leaks. Note: theorem 1 reaches large existing machinery (`core_closeInstsA` proof); the walk is reported with its size, and any non-standard axiom reached would be a FAIL.
- **AXIOMS:** `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`/`native_decide`.
- STATUS line lists NOT supplied: `MachineDefines`/`MachineClosesAtA`/`Start` themselves (real `EntryWitness`/`ReflectsAll`), leaf case `insts = []`, (a3), `TopShips` on `D'`, O3 (b1)(b2), (c4 import)(c5)(c6)(c7), parametrised-route post-processing, `Post` adoption, FG.
- Builds are the coder's (clean issue-linked); an agent incremental build is labelled NOT clean, and a NOT BUILT header is used until then.

## 5. Not claimed
That any real run satisfies `MachineDefines`/`MachineClosesAtA`/`Start`; the leaf case; transport for `checkedOptimize b` (a3); `TopShips` on `D'`; O3; `EntryWitness`/`ReflectsAll`; `Post` adoption; FG completion; M5. The Issue stays open.
