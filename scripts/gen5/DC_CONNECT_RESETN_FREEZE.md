# DC-CONNECT next unit: freeze of U-RESETN (conditional `ResetNk` transport `D → D′`) (agent g5dc-r16, base `kjob/g5dc-r15` 135aa0ac = U-ENTRYW approved, build dc15v-135aa0ac exit 0, 751 jobs)
**Design only; no Lean in this commit.** "Unsupplied / this investigation found no route" is a statement about THIS investigation (this tree, `scripts/gen5/*`), not impossibility. A "mutant" is a signature/defeq rejection of a well-typed changed statement, not a semantic counterexample. No new law/TRUSTED, no shared-definition/compiler edit, FG not narrowed, `GenWF` not strengthened, no `Post` adoption. The result is CONDITIONAL on a premise (`NoRawBelow`) that nothing in this tree derives; it is an intermediate result, not a completion of (a2.4).

## 1. Row status after U-ENTRYW (real names)
| row | status |
|---|---|
| real `EntryWitness`, `ReflectsAll` | unsupplied / this investigation found no route (owners dg-acc / dg-sem / dg-dataof; `ReflectsAll` is a parameter of `EntryWitness`) |
| (a2.4a) `ResetNk n raw D kids ↔ ResetNk n raw D' kids` for `PostEntry b raw D D'`, GIVEN the name-distinctness premise below | **closable now** from `postEntry_lookup_ne` (`Tools/ShippingGen5DCEntryN.lean:84`) and the definitions of `ResetN` (`Tools/ShippingMachineDepth.lean:52`) and `ResetNk` (`Tools/ShippingMachineShipsDepth.lean:245`); chosen as U-RESETN |
| (a2.4b) the premise `NoRawBelow` itself (no instance reachable from `raw` through `D` is named `raw.name`) | unsupplied / this investigation found no route (no acyclicity / name-distinctness of `D.modules` read from the core run) |
| (a2.4c) the `childMap`-dependent run `runModuleTG (KSn (childMap D'.modules) n) … = runModuleTG (KSn (childMap D.modules) n) …` | not frozen here: needs an agreement-on-reachable-names lemma for `runModuleTG` that this investigation did not locate; unsupplied / no route found |
| (a3) post-processed top (`checkedOptimize b`) vs `raw`; (b1) arbitrary `raw′` with `PostT1`; (c4 import) `readMachine_rootFields`; (c5) reader/core tie; (c6) `hall`/`ReadsAt`; (c7) O2/DeclConnect rows, ConstValue | unchanged from `DC_CONNECT_SUPPLY_SURVEY.md` §14 and `DC_CONNECT_NEXT_UNIT_FREEZE.md` §2: unsupplied / no route found |
| (b2) restating O3 | reviewer/user decision (survey §8 (b2)); NOT opened here |
| parametrised-route post-processing | unsupplied (no `PostEntry`-style lemma for `synthesizeCombinationalWithParameters`) |

## 2. Why U-RESETN first
It is the only remaining row whose inputs are all existing approved text (`postEntry_lookup_ne`, `ResetN`, `ResetNk`, `PostEntry`). It turns the stated gap "ResetNk transport needs a premise" into one explicit, named, checkable hypothesis (`NoRawBelow`) instead of an unstated one. It does NOT derive that hypothesis, does not transport the run (a2.4c), does not give `TopShips` on `D'`. Whether the premise holds for the designs the core produces is open (a2.4b).

## 3. Full types (no abbreviations)
New files only: `Tools/ShippingGen5DCEntryR.lean` (namespace `Tools.ShippingGen5DCEntryR`; `import Tools.ShippingGen5DCEntryN`, `import Tools.ShippingMachineShipsDepth`; `set_option autoImplicit false`), `Tests/Gen5/DCEntryRCheck.lean`, `lean_lib` additions in `lakefile.lean`. `open Sparkle.IR.AST` is NOT used; names are fully qualified below (`Stmt.inst mn iname conns` is `Sparkle.IR.AST.Stmt.inst`).
```lean
/-- a STRONG sufficient condition: every instance statement of `mc` (also one whose lookup in `D` fails) has `mn ≠ rn`, recursively (to depth `k`, through `D`) for those whose lookup succeeds; at depth 0 nothing is read -/
def NoRawBelow (D : Sparkle.IR.AST.Design) (rn : String) : Nat → Sparkle.IR.AST.Module → Prop
  | 0, _ => True
  | k + 1, mc =>
    (∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc.body → mn ≠ rn) ∧
    (∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)) (mc' : Sparkle.IR.AST.Module),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc.body →
        Sparkle.IR.Machine.moduleByName D.modules mn = some mc' → NoRawBelow D rn k mc')

theorem resetN_transport {D D' : Sparkle.IR.AST.Design} {rn : String}
    (hlk : ∀ mn : String, mn ≠ rn →
      Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn) :
    ∀ (n : Nat) (mc : Sparkle.IR.AST.Module) (s : Tools.ShippingHierStateG.KT n),
      NoRawBelow D rn n mc →
      (Tools.ShippingMachineDepth.ResetN D n mc s ↔ Tools.ShippingMachineDepth.ResetN D' n mc s)

theorem resetNk_transport {b raw : Sparkle.IR.AST.Module} {D D' : Sparkle.IR.AST.Design}
    (h : Tools.ShippingGen5DCEntryD.PostEntry b raw D D') (n : Nat)
    (kids : String → Tools.ShippingHierStateG.KT n)
    (hno : NoRawBelow D raw.name (n + 1) raw) :
    Tools.ShippingMachineShipsDepth.ResetNk n raw D kids ↔ Tools.ShippingMachineShipsDepth.ResetNk n raw D' kids
```
Confirmed against the source: `Stmt.inst (moduleName instName : String) (connections : List (String × Expr))` (`Sparkle/IR/AST.lean:287-291`); `KT : Nat → Type` is in namespace `Tools.ShippingHierStateG` (`Tools/ShippingHierStateG.lean:623`). Whether `Expr` resolves to `Sparkle.IR.AST.Expr` in the Lean file is checked when the file is written; if any name differs the freeze is corrected in a docs commit and re-submitted, and statements are not silently changed.

Proof route. `resetN_transport`: induction on `n`. `unfold Tools.ShippingMachineDepth.ResetN`; the first three conjuncts do not mention `D`, so they are `Iff.rfl`. For `n = 0` the match gives `True`. For `k+1`: given `NoRawBelow D rn (k+1) mc = ⟨hnm, hrec⟩`, for each `Stmt.inst mn iname conns ∈ mc.body`, `hnm … : mn ≠ rn`, so `hlk mn` rewrites `moduleByName D'.modules mn` to `moduleByName D.modules mn`; the induction hypothesis at `k` on `mc'` with `hrec … : NoRawBelow D rn k mc'`. `resetNk_transport`: `PostEntry` gives `hlk` through `Tools.ShippingGen5DCEntryN.postEntry_lookup_ne h` (`.1`); unfold `ResetNk`; for an instance `Stmt.inst mc.name iname conns ∈ raw.body`, `hno.1` gives `mc.name ≠ raw.name`, rewrite the lookup, then `resetN_transport` on `n` with `hno.2` supplying `NoRawBelow D raw.name n mc`. If a proof does not go through as stated, the statement is NOT changed (stop and report).

## 4. Check plan (`Tests/Gen5/DCEntryRCheck.lean`; same requirements as U-ENTRYW)
- **TYPE:** independent `Exp*` for `resetN_transport` and `resetNk_transport` (and a definition-body check for `NoRawBelow` through the comparator on its two equations / `Iff` statements) written from the prose of §3, compared by `Tests.Gen3.ExpectedType.checkExpected` under `withReducible`; self-comparison positive controls not counted.
- **MUTANT** (well-typed single change; signature/defeq rejection, NOT semantic counterexamples; an ill-typed variant is NOT counted; any mutant that changes a block of components is labelled and counted as a block): `hlk` premise dropped (unconditional claim); `NoRawBelow D rn n mc` hypothesis dropped; `hno` at depth `n` instead of `n+1`; `↔` replaced by `→`; `D`/`D'` swapped in the conclusion; `mn ≠ rn` replaced by `mn = rn` in `NoRawBelow`; `raw.name` replaced by `b.name` in `hno`; `PostEntry b raw D D'` replaced by `PostEntry b raw D' D`.
- **CONJ:** each conjunct of the `NoRawBelow (k+1)` clause dropped (counted separately).
- **CLOSURE:** the `DeclConnectCheck` walker (root judged itself; unknown name = FAIL); required names per root: `resetN_transport`: `ResetN`, `NoRawBelow`, `moduleByName`; `resetNk_transport`: `ResetNk`, `PostEntry`, `postEntry_lookup_ne`, `NoRawBelow`. Positive/negative controls (unreached required name detected; extra clean); unknown-name fixtures with the TYPE alone and the VALUE alone mentioning an unknown name; intended name asserted; `withoutModifyingEnv`; afterwards the CURRENT env (`getEnv`) inspected for leaks.
- **AXIOMS:** `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`/`native_decide`; counts reported as measured with category and rule. Builds are the coder's (clean issue-linked); an agent incremental build is labelled NOT clean.
- STATUS line lists NOT supplied: (a2.4b) the `NoRawBelow` premise, (a2.4c) run transport, (a3), (b1), (b2), (c4 import), (c5), (c6), (c7), real `EntryWitness`, `ReflectsAll`, parametrised-route post-processing, `Post` adoption, FG.

## 5. Not claimed
That `NoRawBelow` holds for any design the compiler produces; `TopShips` on `D'`; the run transport; O3 identification; supply of an `EntryWitness`/`ReflectsAll`; `Post` adoption; FG completion; M5. The Issue stays open. No new law, TRUSTED boundary or shared-definition change is needed, so no decision document is required.

## 6. Reuse
`resetN_transport` takes the lookup agreement as a hypothesis (`hlk`). On integration, the lookup-agreement facts for names other than the top come from `postEntry_lookup_ne` here, and FB's `ppRel_lookup_other` (other-name lookup, NOT the own-name lookup) with the `PostEntry`/`PPRel` correspondence is the relevant reuse target; no change here.

## 7. Wording fixed (reviewer, 4927)
`NoRawBelow` is a strong sufficient condition: its first conjunct demands `mn ≠ rn` for EVERY `Stmt.inst` in `mc.body`, including instances whose lookup in `D` is unsuccessful. It is not claimed necessary. `NoRawBelow` and a real run are unsupplied; this unit is conditional and not an FG completion. The definition is pinned in the Check by its two equations (`NoRawBelow D rn 0 mc = True`, and the `k+1` clause) proved by `rfl` and compared with independently written Expected statements.
