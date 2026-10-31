# DG-SEM freeze P8 — next unit U8 `GenData` / `GenData.toIn` / kit identification (docs only)

**FOR REVIEW — design only; no Lean edited, nothing elaborated in this commit.** Agent g5sm-u18, base `9150ffd7` (= P7 / U7 approved, build `smu17v-9150ffd7` exit 0, 718 jobs). Header sync of `Tools/ShippingGen5SemKitInv.lean` and `Tests/Gen5/SemKitInvCheck.lean` to that build is commit `92fce0fa` (comment only, no rebuild).
Everything below is a PROPOSAL until approved. No new TRUSTED boundary/law, no FG/guarantee change, no shared-definition/compiler edit (`Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean` untouched), no `GenWF` strengthening, no FG narrowing, no `sorry`/`axiom`/`native_decide`.
Marks: `[B]` = in this tree (read at `9150ffd7`); `[br:X@sha]` = another branch (NOT in this tree); `[N]` = new here.
Method: names and statement heads read with `git show` / `grep` / `Read`; nothing elaborated. "この調査で辿った候補経路では未供給" does not claim impossible. Audit = kernel types/values reachable from the roots, not opaque implementations or compiled code.

## 1. Sync (done, comment only)
Headers of the U7 Tools/Check files now say: built clean as `smu17v-9150ffd7`, exit 0, approved at `9150ffd7`. (`92fce0fa`.)

## 2. Survey: which of the real-kit rows `hsem / hd / hmem / hinv` close from existing names

P7's four kit-shaped premises, and the real source of each (real names, read not elaborated):

| premise | real source found | where | status |
|---|---|---|---|
| `hmem : ∀ d k, k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none` | field `AssignKit.mem_ordCallees` (identical statement) | `[br:g5ac-r20 Tools/ShippingGen5Acc.lean:45]` | DG-ACC's kit field; with `ordC := K.ordCallees` it is the premise verbatim. Closes by `K.mem_ordCallees` at integration. No DG-SEM work. |
| `hinv`, `Acc R X` part | 3rd conjunct (after witnesses `E g`) of `genS_some_inv K` | `[br:g5ac-r20 Acc.lean, genS_some_inv]` | DG-ACC owns it. |
| `hinv`, edge part `∀ k ∈ ordC (dOf gd), R ((dOf gd).shape.insts[k]).1 X` | `callEdge_of_ord K hE hg : ∀ k ∈ K.ordCallees (K.dOf g), CallEdge K X ((K.dOf g).shape.insts[k]).1`; `abbrev CallRel K := flip (CallEdge K)`, so `CallRel K c X` is defeq to `CallEdge K X c` | `[br:g5ac-r20]` | DG-ACC owns it; `hE`, `hg` come from conjuncts 1–2 of `genS_some_inv`. |
| `hinv`, equation part `s = genSemK G X gd` | 5th conjunct of `genS_some_inv K` (`s = K.genSem (genS K) X g`) | `[br:g5ac-r20]` | DG-ACC owns it. |
| `hsem : genSemK Q X gd = genSemVia GD toIn Q X gd` | **no built `GenData` / `toIn` found in any tree this survey read** (`git grep` for `structure GenData`, `toIn` over `kjob/g5ac-r20`, `kjob/g5do-r6`, `kjob/g5rt-r5`, and this tree: only the `GenData` proposal in `par/gen5-t2:scripts/gen5/DGEN_FREEZE.md` rev2 §2.1 and the pieces below) | – | **closes by `rfl` once `GenData`/`genSem` are DEFINED in the way `DGEN_FREEZE.md` rev2 §2.1 / `DG_SEM_FREEZE.md` §1 (line 50-56) already state** (`genSem := genSemI Q X g.toIn`). This definition is DG-SEM's own item (Issue title: "GenData, genSem per arm …"). |
| `hd : (toIn gd).d = dOf gd` | same | – | closes by `rfl` for `toIn` with `d := g.d` (same definition). |
| `GenData.toIn` fields `ok / bodyEq / init` | `dataOfAt_sound : dataOfAt lvl E senv s = some d → d.shape = s ∧ d.ok = true ∧ d.shape.body = quote d.dom (…) d.packed ∧ d.initOk (initsOf d) = true` `[br:g5do-r6 Tools/ShippingGen5DataOf.lean:211]`; `initsOf (d : MachineData) : HList (tys d.ss)` `[br:g5do-r6 Tools/ShippingGen5DataOfPure.lean:354]` | DG-DATAOF owns them | not importable here (not an ancestor; merging out of scope). Enter U8 as **explicit variables `initsOf` and the premise `DataOfSound`** (the statement of `dataOf_sound`, `DGEN_FREEZE.md` rev2 §2.1), NOT as a law: at integration `DataOfSound dataOf initsOf` is `dataOfAt_sound`-shaped (DG-DATAOF). Whether `dataOfAt_sound` matches `DataOfSound` for the real `dataOf` is not verified here. |
| `GenWF d = true` (the `wf` field) | `GenWF` `[B Tools/ShippingGen5SemGen.lean:58]` | DG-COVER (coverage) supplies *when it holds* for a real run | a `GenData` value carries it as a field; U8 supplies no value of `GenData`. |

Other Issues (DG-ACC, DG-DATAOF, DG-COVER, readertrace): named only, no state changed.

**Finding.** The two rows that P7 left as the "`GenData.toIn` identification" (`hsem`, `hd`) are the rows that close from names plus a *definition*: the definition of `GenData`/`toIn`/`genSem` itself. They are genuinely DG-SEM's (the Issue title lists `GenData`), they are closed by `rfl` once defined, and they need `initsOf` + `DataOfSound` only as variables. `hmem`/`hinv` need `AssignKit`/`genS` (DG-ACC lineage `kjob/g5ac-*`, not an ancestor here) → this survey's candidate routes give them only at integration (`K.mem_ordCallees`, `genS_some_inv`, `callEdge_of_ord`).

## 3. First unit and why: U8 = `GenData` + `toIn` + `genSem`, with `hsem`/`hd`/evidence as theorems
Reasons: (1) it is the only DG-SEM-owned row of the four whose source this survey found *buildable in this tree* (the others are DG-ACC kit fields); (2) it turns P7's `hsem`/`hd` from premises into proved statements (`rfl`) for a concrete `GD`, leaving only `hmem`/`hinv` (both DG-ACC) in the composed theorems; (3) it needs no `AssignKit`, no run, no real `dataOf`; (4) no new law: `DataOfSound` is a premise (a hypothesis in each theorem), `GenData` is a structure whose fields are exactly rev2 §2.1; (5) it is the object whose absence was the recurring "未供給" row in P6C/P6D/P6F/P7.

### 3.1 Complete types
New file `Tools/ShippingGen5SemGenData.lean`, namespace `Tools.ShippingGen5Sem`, `set_option autoImplicit false`, `import Tools.ShippingGen5SemKitInv`, same `open`s and `variable {ι : Type} {dom : ι → DomainConfig}` as `Tools/ShippingGen5SemKitInv.lean`. Lakefile: one `lean_lib` for it, one for its Check.

```lean
def DataOfSound (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (initsOf : (d : MachineData) → HList (tys d.ss)) : Prop :=
  ∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
    dataOf E senv s = some d →
    d.shape = s ∧ d.ok = true ∧
    d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.initOk (initsOf d) = true

structure GenData (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (E : ConstantInfo) (senv : StructEnv) where
  d      : MachineData
  wf     : GenWF d = true
  hshape : machineShape? false [] E senv = some d.shape
  hdata  : dataOf E senv d.shape = some d

def GenData.toIn {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf)
    {E : ConstantInfo} {senv : StructEnv} (g : GenData dataOf E senv) : GenIn :=
  ⟨g.d, g.wf, initsOf g.d, (hs E senv g.d.shape g.d g.hdata).2.1,
    (hs E senv g.d.shape g.d g.hdata).2.2.1, (hs E senv g.d.shape g.d g.hdata).2.2.2⟩

noncomputable def GenData.genSem {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf)
    (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} {senv : StructEnv}
    (g : GenData dataOf E senv) : SemPkg ι dom :=
  genSemI Q X (g.toIn hs)
```
(The `GenIn` field order is `d wf inits ok bodyEq init` `[B SemGen.lean:61-68]`.) `DataOfSound`, `GenData`, `GenData.toIn`, `GenData.genSem` are the only new `def`/`structure`; they are definitions, not laws.

Theorems (all five, complete types):
```lean
theorem genData_toIn_d {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf)
    {E : ConstantInfo} {senv : StructEnv} (g : GenData dataOf E senv) :
    (g.toIn hs).d = g.d

theorem genData_genSem_eq_via {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) (senv : StructEnv)
    (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E senv) :
    GenData.genSem hs Q X g =
      genSemVia (fun E => GenData dataOf E senv) (fun {E} g => GenData.toIn hs g) Q X g

theorem genData_evidence {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    (senv : StructEnv) (E : ConstantInfo) (g : GenData dataOf E senv) :
    machineShape? false [] E senv = some g.d.shape ∧ dataOf E senv g.d.shape = some g.d

theorem hunf_of_genData {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) (senv : StructEnv)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E senv), Acc R X ∧
        (∀ k ∈ ordC gd.d, R ((gd.d.shape.insts[k]).1) X) ∧ s = GenData.genSem hs G X gd) :
    ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y

theorem factsOf_all_of_genDataInv {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) (senv : StructEnv)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E senv), Acc R X ∧
        (∀ k ∈ ordC gd.d, R ((gd.d.shape.insts[k]).1) X) ∧ s = GenData.genSem hs G X gd) :
    ∀ (X : Name) (s : SemPkg ι dom), G X = some s → FactsOf s
```
Proof plan. `genData_toIn_d`, `genData_genSem_eq_via`: `rfl`. `genData_evidence`: `⟨g.hshape, g.hdata⟩`. `hunf_of_genData`: `hunf_of_kitInv (fun E => GenData dataOf E senv) (fun {E} g => GenData.toIn hs g) (fun {E} g => g.d) ordC (fun Q X {E} g => GenData.genSem hs Q X g) R G (fun Q X E g => genData_genSem_eq_via hs senv Q X g) (fun {E} g => genData_toIn_d hs g) hmem hinv` (argument order per `hunf_of_kitInv` `[B]`; `E` binder implicitness settled at first elaboration; a statement change is a stop, not a silent patch). `factsOf_all_of_genDataInv` likewise with `factsOf_all_of_kitInv [B]`.

**Delicate points (reported if they fail):** `quote`/`inputExpr`/`HList`/`tys`/`MachineShape`/`StructEnv` name resolution (same `open`s as `SemGen.lean`, plus `Sparkle.Compiler.Elab` for `machineShape?`, `StructEnv`); the implicit-binder shape of `toIn : {E} → GD E → GenIn` against `fun {E} g => …`; universe of the structure (`Type`).

### 3.2 Check (new `Tests/Gen5/GenDataCheck.lean`; Expected written from the sentences above, not from the implementation)
Same requirements as `SemKitInvCheck`:
- **TYPE**: the 5 theorems (+ `DataOfSound`, `GenData`, `GenData.toIn`, `GenData.genSem` by type) against independently written `Exp*` (`checkExpected`/`cmpTele`, reducible comparison; where only defeq holds this is stated).
- **MUTANT** (well-typed single changes only; rejection = signature/defeq, **not** a semantic counterexample; ill-typed proposals not counted; the Check prints the real count): `genData_toIn_d` conclusion `.d = g.d` → `.d = (g.toIn hs).d`-free variant `g.d = g.d` is NOT counted (trivial); counted: `genData_genSem_eq_via` RHS `genSemVia … Q X g` → `genSemVia … (fun _ => none) X g`; `genData_evidence` second conjunct `some g.d` → `some g`-free variant `= none`; `hunf_of_genData` edge `R c Y` → `R Y c`; `hinv` equation `GenData.genSem hs G X gd` → `GenData.genSem hs (fun _ => none) X gd`; `hmem` `= none` → `≠ none`; drop the `Acc R X` conjunct of `hinv` in `factsOf_all_of_genDataInv`; conclusion `FactsOf s` → `SrcCausal s`; `DataOfSound` conjunct `d.ok = true` → `d.ok = false`. Unused extra hypotheses (weaker) are NOT counted.
- **AXIOMS**: standard only. **sorry**: absent.
- **CLOSURE**: explicit walk (unknown name ⇒ `throwError`), controls: unknown root, forbidden roots (`sorryAx`, `Lean.ofReduceBool`) flagged by the root itself, unknown helper value (`Mv`), unknown helper type (`Mt`), clean fixture; positive and negative controls; fixtures inside `withoutModifyingEnv`.
- **REACH**: `hunf_of_genData` reaches `hunf_of_kitInv`, `genData_genSem_eq_via`, `genData_toIn_d`; `factsOf_all_of_genDataInv` reaches `factsOf_all_of_kitInv`; `GenData.toIn` reaches `DataOfSound`.

## 4. Not claimed
- No value of `GenData` is constructed; `GenWF d = true` for any real run (DG-COVER), `dataOf` and `initsOf` for the real compiler (DG-DATAOF `[br:g5do-r6]`), and `DataOfSound dataOf initsOf` for them are **not supplied**; `DataOfSound` is a hypothesis of each theorem. Whether `dataOfAt_sound` has exactly the shape of `DataOfSound` is not verified here (this survey read the statement only).
- `hmem` (`K.mem_ordCallees`) and `hinv` (`genS_some_inv`, `callEdge_of_ord`) for the real `AssignKit`/`genS` remain integration steps in the DG-ACC lineage (`kjob/g5ac-*`, not an ancestor; merge is out of scope). `K.genSem` is defeq to `GenData.genSem hs` only if the integrator defines the kit's `genSem` that way; U8 provides that definition, it does not force the kit.
- `CalleesCausal` for the real table, real run, M5, FG, `GenSFacts K` for a built kit: not supplied. SEM lineage is before S1; every claim is re-verified at the integration SHA.
- No new law / TRUSTED. If integration needs one (e.g. `DataOfSound` not derivable from `dataOfAt_sound`), a decision document is written then.
- Mutants are rejected by signature/defeq; they are not semantic counterexamples.
