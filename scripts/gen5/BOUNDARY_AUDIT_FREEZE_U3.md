# BOUNDARY-AUDIT freeze U3 (docs only; Lean follows after approval)

Issue: `sparkle-gen5-boundary-audit` (M5, N1 / G5 / G7 audit). Branch `kjob/g5ba-r6`, base `e363183a` (U2 approved; the header-only commit
`8c080496` records build `ba5v-e363183a`, exit 0, 688 jobs). This file ADDS to `BOUNDARY_AUDIT_FREEZE.md` (r1) and `BOUNDARY_AUDIT_FREEZE_U2.md`; nothing there is withdrawn.
"Not found" means only that this survey did not find a supplier or route; it does not say a row is impossible or underivable.
The §2 table of U2 is a past snapshot (its SHAs are the history at the time each was recorded); a final audit must re-check each owner's latest supply. This
unit re-checks only the four unsupplied rows below. Nothing here claims N1, G5, M5, FG or Issue completion. No new TRUSTED boundary, law, compiler/shared-definition
edit, FG narrowing or GenWF strengthening is proposed.

## 0. A fact that decides what can be built in this unit

The approved parts the Issue text names are NOT in the base of this branch: `git merge-base --is-ancestor` of the recorded SHAs against `e363183a`
gives "not an ancestor" for DG-READKINDS U5/U6/U8 (`4ac00d24`, `36318286`, `f86cbdd7`; on `kjob/g5rk-r10..r14`), DG-COVER (`3eb663df`, `72752f4c`, `8e01a9cf`; on `kjob/g5cv-r10..r12`),
DG-DATAOF row 6b (`2bdc9324`, `063056d6`; on `kjob/g5do-r6`), DG-ACC (`5aab73de`, `a88c3e9c`; on `kjob/g5ac-*`), DG-SEM `7c06a80f`. Only `144c3f1e` (runreads) and the S3
`Tools/ShippingGen3ChildPortWidths.lean` are in this tree. This unit does not merge or import those branches (merging is out of scope). A Lean file of this unit can therefore
import only what is in this tree; a row whose supplier lives only on those branches is listed as 未供給 *for this branch* and the supplier Issue is named. The consolidation of
those branches is the owners' / the user's merge, not decided here.

## 1. The four unsupplied rows: survey result

| row | what is needed (exact) | approved part that touches it | what this survey found | state for this branch |
|---|---|---|---|---|
| (a) `MemTagsNamed` of the real shape | `MemTagsNamed sp` for the `sp` of `MachineDefines` | DG-READKINDS U8 `machineDefines_of_readMachine` (`f86cbdd7`, branch only, conditional on `hall`): the shape is `readMachine`'s `machineShape? false [] entry senv` (MachineCommand.lean:~455), the PRODUCTION `partial` reader | in tree: `machineShapeF_tag_mem` gives the fact for `machineShapeF`'s output. The link `machineShape? … = some sp → ∃ n, machineShapeF n … = some (some sp)` was searched (`grep machineShapeF.*machineShape?`, `TwinCover`, `OldEq`): the only statements are conditional (`readF_agree_old` needs `OldEq`, `TwinCoverAt` OPEN). No theorem for this link was found | 未供給 (owner: sparkle-gen5-reader-bridge, `todo`). Not implemented here; a candidate conditional row is recorded in §5 |
| (b) graph / rank | `callees g c = some sp.instTagged` and `declRank g F c = some r` for EVERY reached `c`, not only the top | in tree: `Tools.ShippingSrm15Graph.graphOf`/`callees_graphOf` (graph read from a declaration list), `Srm7Rank.inClass_rank`, `rkOf_edge`; U2 `hself_of_rank` (one declaration at a time) | in tree there is no statement that a rank of the TOP gives a rank for every declaration reached through ordinary kids, and none that ties the graph to `T1Hyp`'s `P`/`Reach`. Supply of `InClass g B top` for the generated program and `GraphAgrees` (below): 経路未発見 | **closed conditionally by this unit (§3)**: rank propagation along ordinary edges (pure graph theorem) and `hself`/`sepK`/`parent` for every reached declaration, with the premises `GraphAgrees`, `ReachSpans`, `hmem` named |
| (c) ordinary child name (B7) | `RealChildA O c y → y.1.name = ofDecl c` for ordinary kids | `hname_of_iface` (Srm15Graph.lean:58) takes `ChildIfaceP (ofDecl c) …` as a premise; S3 `ChildPortWidths` is about the port WIDTHS of `argPorts` (Gen3ChildPortWidths.lean:50), not the module name; DG-READKINDS/COVER/DATAOF are about reads, coverage and dims | no unconditional theorem and no supplier Issue for the name of a served child was found | 未供給 / この調査で経路未発見 |
| (d) B3 `hparentD`, B4 `hdisjD`, B5 `hfresh`/`outHead`, B6 `nameIn` and `memNames` first conjunct, B7 | as in r1 §1.2 | none of the named approved parts states them (they are facts about child design contents `ChildIfaceP.desNames`, the `names` list, and output port names) | unchanged from r1 §1.2/§1.4 | 未供給 / この調査で経路未発見 |

Rows (a), (c), (d) are owned elsewhere or have no owner found; they are NOT re-implemented here. Overlap check: `sparkle-gen5-dg-readkinds`, `-dg-cover`, `-dg-dataof`, `-dg-acc`
own the read/coverage/dims/route statements; none of them states a rank, a graph agreement or `hself`. The graph/rank statements of §3 are in no other Issue's recorded list.

## 2. G5 joint satisfiability: still OPEN. What is needed (unchanged from U2 §4, one line per need)

Needed and not in tree: (1) a model or a TRUSTED statement linking `Heap σ` (`heapLaws_sat`) to the extern `ST.Ref`/`Void IO.RealWorld` — a user decision, not taken here; (2) `diag`/`excOk` for Lean's own exceptions, `frameQ`/`frame`
for `Meta` primitives, the four `T` telescope fields; (3) a quiet start world with `sv w = some synthesizeChild` (`Start.2`) and `InertUnfold` of the context callback (`Start.1`). No field was found unsatisfiable with `Start`; none was shown satisfiable. This unit adds nothing to G5.

## 3. First implemented unit: rank propagation and `hself`/`sepK`/`parent` for all reached declarations

**Why this one first.** It is the only unsupplied row whose every ingredient is in this tree (`Srm7Rank`, U2) and which no other Issue states; it removes the "one declaration at a time" gap of `hself_of_rank`
(which needs a rank of the very declaration whose shape is examined) and makes the remaining premises explicit and minimal (an `InClass` top, a graph that agrees with the shapes, a minimality statement for `Reach`, `MemTagsNamed` of each shape).

File (new): `Tools/ShippingGen5NameKids3.lean`; check file (new): `Tests/Gen5/NameKids3Check.lean`; two `lean_lib` entries (`Tools.ShippingGen5NameKids3`, `Tests.Gen5.NameKids3Check`).
Imports: `Tools.ShippingGen5NameKids2` only (core Lean has no `Relation.ReflTransGen`, as `Tools/ShippingStartWorldA2.lean:108` notes; the path relation is defined locally). Namespace `Tools.ShippingGen5NameKids3`, `set_option autoImplicit false`. Opens:
`Lean (Name)`, `Sparkle.Compiler.Elab (MachineShape)`, `Sparkle.Compiler.MachInstOrigin (InstOrigin)`, `Tools.ShippingSrm7Rank (CallGraph callees declRank InClass kidModName)`, `Tools.ShippingMemCloses (memKey)`,
`Tools.ShippingInstTagged (originAt)`, `Tools.ShippingGen5NameKids2 (MemTagsNamed kidNameAt)`. No `Laws`, no runtime, no compiler definition. `S : Name → Option MachineShape` stands for `fun c => (P c).map (·.d.shape)` of `T1Hyp` (use-site example in the Check, §4).

```
/-- an edge of the call graph through an ORDINARY (non-memory) call entry -/
def OrdEdge (g : CallGraph) (a b : Name) : Prop :=
  ∃ (ks : List (Name × InstOrigin)) (o : InstOrigin), callees g a = some ks ∧ (b, o) ∈ ks ∧ memKey o = none

/-- the graph carries exactly the reached declarations' tagged call entries -/
def GraphAgrees (g : CallGraph) (Reach : Name → Prop) (S : Name → Option MachineShape) : Prop :=
  ∀ c, Reach c → callees g c = (S c).map MachineShape.instTagged

/-- `T1Hyp.closed`, restated over `S` (same text as GEN2_DEFS `closed` with `S c = some sp` for `P c = some q`, `sp = q.d.shape`) -/
def ReachClosed (Reach : Name → Prop) (S : Name → Option MachineShape) : Prop :=
  ∀ c, Reach c → ∀ sp, S c = some sp → ∀ (k : Nat) (hk : k < sp.insts.length),
    (sp.instOrigins.getD k InstOrigin.ord).child? = none → Reach (sp.insts[k]'hk).1

/-- the reflexive-transitive closure of `OrdEdge g` from `top` -/
inductive OrdPath (g : CallGraph) (top : Name) : Name → Prop
  | refl : OrdPath g top top
  | step {a b : Name} : OrdPath g top a → OrdEdge g a b → OrdPath g top b

/-- every reached declaration is reachable from `top` through ordinary edges (the converse of `ReachClosed`; NOT supplied by this unit) -/
def ReachSpans (g : CallGraph) (top : Name) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → OrdPath g top c

theorem rank_of_ordEdge {g : CallGraph} {F r : Nat} {a b : Name}
    (hr : declRank g F a = some r) (he : OrdEdge g a b) :
    ∃ r', declRank g F b = some r' ∧ r' < r

theorem rank_of_reach {g : CallGraph} {F r : Nat} {top c : Name}
    (hr : declRank g F top = some r) (hc : OrdPath g top c) :
    ∃ r', declRank g F c = some r' ∧ r' ≤ r

theorem reach_of_ordEdges {g : CallGraph} {Reach : Name → Prop} {S : Name → Option MachineShape} {top c : Name}
    (hg : GraphAgrees g Reach S) (hcl : ReachClosed Reach S) (ht : Reach top)
    (hc : OrdPath g top c) : Reach c

theorem hself_all_reached {g : CallGraph} {B r : Nat} {top : Name} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hin : InClass g B top = true) (hg : GraphAgrees g Reach S) (hsp : ReachSpans g top Reach) :
    ∀ c, Reach c → ∀ sp, S c = some sp → ∀ (k : Nat) (hk : k < sp.insts.length),
      memKey (originAt sp k) = none → (sp.insts[k]'hk).1 ≠ c

theorem sepK_parent_all_reached {g : CallGraph} {B : Nat} {top : Name} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hin : InClass g B top = true) (hg : GraphAgrees g Reach S) (hsp : ReachSpans g top Reach)
    (hmem : ∀ c, Reach c → ∀ sp, S c = some sp → MemTagsNamed sp) :
    ∀ c, Reach c → ∀ sp, S c = some sp →
      (∀ (k : Nat) (hk : k < sp.insts.length) (k' : Nat) (hk' : k' < sp.insts.length),
        kidNameAt sp k = kidNameAt sp k' →
        (sp.insts[k]'hk).1 = (sp.insts[k']'hk').1 ∧ memKey (originAt sp k) = memKey (originAt sp k')) ∧
      (∀ (k : Nat), k < sp.insts.length → kidNameAt sp k ≠ Sparkle.IR.ModuleName.ofDecl c)
```
That is 5 theorems and 5 definitions (`OrdEdge`, `GraphAgrees`, `ReachClosed`, `OrdPath` (inductive), `ReachSpans`). `ReachClosed` is stated only so that `reach_of_ordEdges` can show the
inclusion `closure of top ⊆ Reach`; `hself_all_reached` and `sepK_parent_all_reached` do not use it.
Proof plan (not part of the frozen statements): `rank_of_ordEdge` by `rkOf_edge` on a member of `ks`, then `kidModName_of_none` and `rkOf_decl` (U2 private helper pattern; re-proved locally, no `private` import);
`rank_of_reach` by `OrdPath.rec` using `rank_of_ordEdge` with `r' < r` giving `≤`; `reach_of_ordEdges` by induction on the path: at an edge `a → b` with `Reach a`, `hg` gives `S a = some sp` and
`ks = sp.instTagged`, `instTagged_exists_idx` gives the index `k` with `(b,o) = (sp.insts[k].1, originAt sp k)`, `memKey o = none` gives `child? = none` (`InstOrigin` case split), then `hcl`;
`hself_all_reached` by `inClass_rank` for the rank of `top`, `rank_of_reach` (via `hsp`) for the rank of `c`, `hg` for `callees g c = some sp.instTagged`, then `hself_of_rank` (U2); `sepK_parent_all_reached` by `sepK_parent_of_supply` (U2). If a statement needs a change when proved, the change is recorded as an amendment to this file before the Lean commit is offered.

What the unit does NOT show: that the generated program's graph satisfies `GraphAgrees` for the `P` of FG (the graph is a premise; `graphOf`/`callees_graphOf` of Srm15Graph give it for a declaration list under `FirstOcc`, but the link of that list to `P` was not found);
that `InClass g B top` holds (a decidable check of the graph; its use on the generated program was not found); that `Reach` is minimal (`ReachSpans` is an unsupplied statement; the match of `Reach` with the translator's actual child calls is G-REACH);
`MemTagsNamed` of each reached shape (row (a)). So the premise list of FG's `closes` supply after this unit is: `InClass` top, `GraphAgrees`, `ReachSpans`, `hmem` (row (a)), B3-B7. It narrows no FG obligation and adds no TRUSTED row.

## 4. U3 checks (written from §3, not from the implementation)

* **Expected TYPEs** (`Tests/Gen5/NameKids3Check.lean`): each of the 5 theorems and 5 definition bodies (`OrdPath`: constructor types) of §3 restated as an independent `def Exp… : Prop` (and body) from the §3 text. The Expected props may name `OrdEdge`, `GraphAgrees`, `ReachClosed`,
  `OrdPath`, `ReachSpans` (bodies compared separately). The one reducible comparator of `Tests.Gen5.NameKidsCheck` (`cmpTeleR`, `checkExpectedR`, `checkMutantR`) for positives and mutants.
* **Mutants** (single change, well-typed; rejection is by signature/defeq, NOT a semantic counterexample): (1) `rank_of_ordEdge`: `r' < r` → `r < r'`; (2) same: `OrdEdge` → `declRank g F b = none` in the conclusion's first conjunct;
  (3) `rank_of_reach`: `r' ≤ r` → `r' < r`; (4) `reach_of_ordEdges`: drop `ht`; (5) same: drop `hcl`; (6) `hself_all_reached`: drop `hsp`; (7) same: `InClass … = true` → `= false`; (8) same: `memKey … = none` → `≠ none`; (9) same: `≠ c` → `= c`;
  (10) `sepK_parent_all_reached`: drop `hmem`; (11) same: drop the second conjunct; (12) same: `ofDecl c` → `ofMem true 0 0`; (13) `OrdEdge` body: `memKey o = none` → `memKey o ≠ none`; (14) `ReachSpans` body: `top c` swapped. Plus 2 cross-statement controls (`hself_all_reached` against `ExpRankOfReach`, `sepK_parent_all_reached` against `ExpHself`).
  Reported as MUTANT n; a mutant accepted by the comparator fails the run.
* **Use-site `example`s**: (i) `GraphAgrees`/`ReachClosed` instantiated with `S := fun c => (P c).map (fun q => q.d.shape)` for `P : Pkgs ι dom` of `Tools.ShippingGen2Defs`: `ReachClosed Reach S` unfolds to the type of `T1Hyp.closed` for that `P` (an `exact`-check on the field type, a type check, not a semantic claim);
  (ii) `hself_all_reached` yields, at `d.shape` of a `MachineData`, the `hself` binder shape of `hparent_of_kidNames`.
* **Closure** (U1/U2 walker `reachWith`/`auditRoot`: root-self judgement, unknown name fails, a synthesized root reaching an unknown name only through a helper's TYPE with the intended path asserted; the fixtures `Tests.Gen5.NameKidsFixture` reused): roots are the 5 theorems; counts reported as negative n, clean 1, REACH n (one per root), with the aggregation rule in the file header.
* **AXIOMS**: `#print axioms` of each theorem ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`, `native_decide`, `axiom`.
* Numbers in the report are actual counts per category with the rule next to them. Before commit, the Check build is run on the tree that is committed (`kjob lake build Tools.ShippingGen5NameKids3` then `kjob lake build Tests.Gen5.NameKids3Check`, one at a time). After the Lean commit the Issue stays `doing` and the note says "clean build は coder が実行".

## 5. Not implemented in this unit (candidates, each needs its own freeze)

* Row (a) conditional: `MemTagsNamed sp` from a named link `FuelCover : machineShape? sm ps ci senv ai = some sp → ∃ n, machineShapeF n sm ps ci senv ai = some (some sp)` and `machineShapeF_tag_mem`. This reduces (a) to `FuelCover` (the reader-bridge item); it supplies nothing by itself.
* Row (a)/(b) join with DG-READKINDS U8 and DG-DATAOF: possible only after those branches are in the base of the branch the Lean is written on.
* Rows (c), (d), G5: 未供給 / この調査で経路未発見; owners as in U2 §2.

## 6. What this freeze does not do
No change to any compiler, production or shared-definition file (`Tools/ShippingGen2Defs.lean`, T1Hyp, T1HypND, `Elab*.lean`), no change to any built file, no merge of other branches. No new TRUSTED boundary/law, no FG/guarantee change, no GenWF strengthening, no `sorry`/`axiom`/`native_decide`.
`ReachSpans` and `GraphAgrees` are premises of the new theorems, not new assumptions of FG. N1, M5, FG remain incomplete; this is not a final audit of the whole table.
