# BOUNDARY-AUDIT freeze U4 (docs only; Lean follows after approval)

Issue: `sparkle-gen5-boundary-audit`. Branch `kjob/g5ba-r8`, base `01a2afbb` (U3 approved; build `ba7v-01a2afbb`, exit 0, 722 jobs). This file ADDS to
`BOUNDARY_AUDIT_FREEZE.md`, `_U2.md`, `_U3.md`; nothing there is withdrawn. "Not found" means only that this survey did not find a supplier or a route; it does not say a row is impossible
or underivable. Nothing here claims N1, G5, G7, M5, FG or Issue completion. No new TRUSTED boundary, law, compiler/shared-definition edit, FG narrowing or GenWF strengthening is proposed.
U2 §2 remains a past snapshot; the final audit must re-check each owner's latest supply.

## 1. Survey of the inputs U3 left unsupplied (existing lemmas, full names and types)

| input | candidate lemma in THIS tree | closes? |
|---|---|---|
| `hmem` / `MemTagsNamed sp` | `Tools.ShippingReaderFuelShapeProv.machineShapeF_tag_mem : machineShapeF n sm ps ci senv ai = some (some sp) → sp.insts[k]? = some e → sp.instOrigins[k]? = some (.mem combo aw dw) → e.1 = memChildName combo aw dw ∧ e.2.2 = MixedGateBinder.bits dw ∧ aw ≠ 0 ∧ dw ≠ 0`; `instOrigins_getD_eq`, `machineShapeF_instOrigins_length` (same file); `originAt` is `abbrev` in `Tools/ShippingKid.lean:114` (`instOrigins.getD k .ord`) | **Yes, as a conditional theorem**: for a shape that is the output of `machineShapeF`, `MemTagsNamed sp` follows. The remaining link `machineShape? … = some sp → ∃ n, machineShapeF n … = some (some sp)` (U3 §1 row (a)) is NOT closed |
| `GraphAgrees g Reach S` | `Tools.ShippingSrm15Graph.callees_graphOf : FirstOcc ds c d → callees (graphOf ds) c = some d.shape.instTagged` | Yes as a conditional (premise: for each reached `c`, `FirstOcc ds c d` and `S c = some d.shape`). That link of `ds` to `P`/`Reach` was not found. Candidate for U5 |
| `InClass g B top = true` | `Srm7Rank.InClass` is a decidable check; no lemma deriving it for the generated program | 未供給 / この調査で経路未発見 |
| `ReachSpans g top Reach` | none (the converse of `T1Hyp.closed`) | 未供給 / この調査で経路未発見 |
| (c) ordinary child name, (d) B3-B7, G5 joint satisfiability | as U3 §1/§2 | 未供給 / この調査で経路未発見 (unchanged) |

Other branches' approved parts (readkinds/cover/dataof/acc/dg-sem) are still not in this base (U3 §0); this unit imports none.

## 2. First implemented unit (U4) and why

**`memTagsNamed_of_machineShapeF`**. Why first: it is the only row whose statement closes completely from lemmas already in this tree (no new premise besides the `machineShapeF` equation), it turns U3's `hmem` premise
into a statement about the reader's total wrapper, and it is small enough that the type can be frozen exactly. It does not supply the `machineShape?` ↔ `machineShapeF` link; the reduced premise is named in §3.

File (new): `Tools/ShippingGen5NameKids4.lean`; check (new): `Tests/Gen5/NameKids4Check.lean`; two `lean_lib` entries. Imports: `Tools.ShippingGen5NameKids3`, `Tools.ShippingReaderFuelShapeProv`.
Namespace `Tools.ShippingGen5NameKids4`, `set_option autoImplicit false`. Opens: `Lean`, `Sparkle.Compiler.Elab`, `Tools.ShippingReaderFuelShapeProv`, `Tools.ShippingGen5NameKids2 (MemTagsNamed)`.

```
theorem memTagsNamed_of_machineShapeF {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeF n sm ps ci senv ai = some (some sp)) : MemTagsNamed sp

theorem hmem_of_machineShapeF {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hF : ∀ c, Reach c → ∀ sp, S c = some sp →
      ∃ (n : Nat) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo) (senv : StructEnv) (ai : Bool),
        machineShapeF n sm ps ci senv ai = some (some sp)) :
    ∀ c, Reach c → ∀ sp, S c = some sp → MemTagsNamed sp
```
2 theorems, 0 new definitions. The second is exactly the `hmem` binder of U3's `sepK_parent_all_reached` with `hF` as the (named, unsupplied) premise: every reached shape is a `machineShapeF` output. Proof plan (not frozen): first by `originAt` unfolding to `instOrigins.getD k .ord`,
`instOrigins_getD_eq` to turn `= .mem cb aw dw` into `instOrigins[k]? = some (.mem …)`, `machineShapeF_tag_mem` with `e := sp.insts[k]`; second by `memTagsNamed_of_machineShapeF`. If a statement must change when proved, it is recorded as an amendment here before the Lean commit is offered.

What U4 does NOT show: that the production `readMachine`'s `machineShape?` output is a `machineShapeF` output (`hF` is that premise; reader-bridge owner); `GraphAgrees`, `InClass`, `ReachSpans`; B3-B7; G5.

## 3. U4 checks (from §2, not from the implementation)
* Expected TYPEs: both theorems restated as independent `def Exp… : Prop` and compared with the comparator of `Tests.Gen5.NameKidsCheck` (`cmpTeleR`, `checkExpectedR`, `checkMutantR`): TYPE 2.
* Mutants (single well-typed change; rejection is by signature/defeq, NOT a semantic counterexample): (1) first theorem: `some (some sp)` → `some none`; (2) first: conclusion `MemTagsNamed sp` → `¬ MemTagsNamed sp`; (3) second: drop `Reach c →`; (4) second: `S c = some sp` → `S c = none` in the conclusion; (5) second: `∃ n` → `∀ n`. Plus 2 cross-statement controls (each theorem against the other's Expected). Counts reported as actual numbers with the rule in the header.
* Use-site `example`: `hmem_of_machineShapeF` output has the type of the `hmem` binder of `Tools.ShippingGen5NameKids3.sepK_parent_all_reached` (type check, not a semantic claim).
* Closure: U1-U3 walker (`reachWith`/`auditRoot`; fixtures `NameKidsFixture`): the 2 theorems as roots; negative n, clean 1, REACH n. AXIOMS: `[propext, Classical.choice, Quot.sound]` only; no `sorry`/`native_decide`/`axiom`.
* After the Lean commit the Issue stays `doing` and the note says "clean build は coder が実行". Builds are run one at a time with `kjob lake build`.

## 4. Not done
No merge of other branches; no compiler/shared-definition change; no change to built files; no new TRUSTED/law. Rows `GraphAgrees` (candidate U5), `InClass`, `ReachSpans`, (c), (d), G5: unchanged or 未供給 / この調査で経路未発見.
