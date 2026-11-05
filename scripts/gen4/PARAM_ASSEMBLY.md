# PARAM_ASSEMBLY: `LegalBinding (SpecDesign M' D') θ` (B.P-8) and `AllPos θ` (B.P-1) from a real parametric run

Status: built, awaiting reviewer. Base `af3468e4` (par/passm). Nothing here is accepted by this document.
Ledger: FG 75 / T1 57 (this unit: FG -0 +0 / T1 -0 +0). The subtraction is recorded by the coder after the reviewer approves.
No new assumption, no TRUSTED, no frozen text changed, no production edit, heartbeat limit unchanged (4M).

## 1. The parts build (base check)

`kjob lake build` of `Tests.Gen4.{FThetaCheck, FThetaTeleCheck, FTopCheck, FPostCheck, ShapeCheck, FKidsCheck, FKidsOblCheck,
ParamIfaceCheck, ParamLayerACheck}` on `af3468e4`: exit 0, 869 jobs. Nothing was broken; no repair commit.

## 2. What was added (new files only, plus the lakefile registration in the first commit)

`Tools/ShippingGen4ParamAssembly.lean` (namespace `Tools.ShippingGen4ParamAssembly`), `Tests/Gen4/ParamAssemblyCheck.lean`.

* `legal_of_facts`: the constructive direction of the private `validateBindings` (converse of `legal_facts`): the five clauses
  (a) no duplicate declaration per module, (b) θ names unique, (c) every θ name declared by some module, (d) θ values nonzero,
  (e) every declared name bound, give `LegalBinding D θ`. Helpers `filter_len_one`, `dupName_none`, `forIn_all_yield`.
* `sfc_defn`: a returning `synthesizeFromConst` run (symbolic mode) reads a `defnInfo` (the other arms throw), needed to apply F-top / F-θ
  to the `ConstantInfo` that `core_symbolic_reads` leaves abstract.
* `run_facts` (premises `MemoFamily` rev3, `MsgMvK`, `LamTelescopeN`, `AdmCtx`, the K start world `KWD .. 0 w`, the run): from the run of
  `synthesizeCombinationalWithParameters declName θ` returning `(M', D')`:
  * (b) `(θ.map (·.1)).Nodup` and (d) `AllPos θ`: `core_symbolic_prologue` (`dupParams`, `zeroParam`) on the core run that `fpost_run_top` exposes;
  * (c) `∀ p ∈ θ, ∃ q ∈ M'.parameters, q.name = p.1`: `fTop_out` (F-top) on the `synthesizeFromConst` run of `core_symbolic_reads`, then
    `M'.parameters = M0.parameters` (F-post, `fpost_run_top`);
  * (a), (e) for the top: `fKidsObl_params` (F-kids obligations (2)(3): `Nodup`, names ∈ θ) turned into a `lookup` by `lookup_some_of_mem_keys`;
  * (a), (e) for the other modules: `fKidsObl_noGuard` (every module of `D'` declares no parameter, no name guard).
* `Collides M' D' := ∃ x ∈ D'.modules, x.name = M'.name` and `legal_assembly`:
  * `AllPos θ`;
  * `¬ Collides → LegalBinding (SpecDesign M' D') θ` (`SpecDesign = D'.addModule M'`, `specDesign_eq_addModule`);
  * `Collides → (LegalBinding (SpecDesign M' D') θ ↔ θ = [])`.
* `legal_names_declared`: `LegalBinding D θ` implies clause (c) (needed for the collision case; `legal_facts` gives (d), (e) only).

## 3. The same-name top-child (FKIDS_FREEZE §7.9, Q-F3), connected

`fKidsObl_noGuard` says every module of `D'` is parameter-free, including one that collides with the top name; NameNoTop is not provable.
`SpecDesign M' D'` (Elab.lean:9126, the `design'` that `specializeDesign` is applied to) is `D'` in that case (the top `M'` is NOT added), so the
top's parameters are in no module of the specialized design. Consequences, as Lean statements:
* no collision: `SpecDesign = D'.addModule M'` (the `D.addModule b` of `ParamTopShips` / `SpecSuccessAllPositive`) and legality holds;
* collision: legality holds iff `θ = []`. For `θ ≠ []` the real command's `specializeDesign` cannot succeed (`specializeDesign_ok_legal`
  would give legality). So the collision case is not a hole of the assembly: it is a run on which B.P-8 is false and the specialization fails.
  A consumer that needs only the consequences of legality that hold in both cases (coverage, `AllPos`) gets them in both cases (`paramRoot_run`).
The D vs `D.addModule b` choice of Q-F3 is thus settled by `SpecDesign M' D'`; the two designs agree exactly when no child has the top's name.

## 4. The roots, and the binder difference

On this base there is no final FG root with a `LegalBinding` / `AllPos` binder: the gen5 final roots (R / G, ND chain, ...) are on other
branches, and the ledger registers B.P-8 / B.P-1 (Q-F3, §8.4) rather than binding them. The roots here are therefore built for the in-tree users of
ParamIface:91 and ParamLayerA:43, and they must be mapped to the FG root by the reviewer:
* `RootConcl M' D' θ e`: every declared parameter of every module of `SpecDesign M' D'` is bound by θ (`legalBinding_covers`), and an
  `ExprOK θ e` source specializes (`specExprM_ok`, needs `AllPos θ`).
* `paramRoot_old`: binders `h` (the run), `hL : LegalBinding (SpecDesign M' D') θ`, `hpos : AllPos θ`, `hok`.
* `paramRoot_run`: binders `M : MemoFamily O`, `hmsg : MsgMvK O`, `htel : LamTelescopeN`, `hA : AdmCtx`, `hw : KWD`, `h`, `hok`; same conclusion.

`Tests/Gen4/ParamAssemblyCheck.lean` compares the two types by one telescope walk, as `FThetaTeleCheck` / `CR4Check` do (old binders
instantiated by the same-named new fvar, types by `Expr ==`):

    PARAM-ASSEMBLY COUNTS: removed 2 [hL, hpos] (B.P-8, B.P-1), added 6 [O, M, hmsg, htel, hA, hw]
      (shared +1 [htel] / Start rows and carrier [O, hA, hw] / F-kids assumptions [M, hmsg]), changed 0, concl true, FG -0 +0 / T1 -0 +0 recorded

* removed = `hL`, `hpos` only; `LegalBinding` and `AllPos` are not in the type of `paramRoot_run` (the proof uses them).
* added: `htel : LamTelescopeN` is the shared +1 candidate N4-a (§12.17), counted once in the final FG. `M : MemoFamily` rev3 and `hmsg : MsgMvK`
  are the F-kids assumptions the brief allows; `MsgMvK` is a conditional leaf, not TRUSTED. `O : RefLawsAOps`, `hA : AdmCtx`, `hw : KWD` are the
  carrier and the Start rows (A.P-02 `AdmCtx`, C.RR-1 `hA`/`hw`) that a run needs; I classify them as existing rows, the reviewer should confirm.
* negative controls: self-comparison is empty; a root keeping `hL` is rejected (removed `[hpos]`); an extra non-row binder is rejected; a different
  conclusion is rejected; the reversed pair is rejected; the hypothesis detector finds `LegalBinding` / `AllPos` in `paramRoot_old`.
* hypotheses of `run_facts` / `legal_assembly` / `paramRoot_run` are exactly `MemoFamily`, `MsgMvK`, `LamTelescopeN`, `AdmCtx`, `KWD`, `RunsTo`
  (`paramRoot_run` also `ExprOK`); the closure reaches no `Laws` / `T1Hyp` / `T1HypND`; axioms: propext, Classical.choice, Quot.sound.

## 5. Ledger effect (not recorded; for the reviewer)

Per the reviewer rule, a row leaves only when the final theorem's binder disappears or is replaced by existing rows in Lean, and a conditional
result is not counted. The replacement here uses `MsgMvK` (conditional leaf) and `MemoFamily` rev3, and `LamTelescopeN` (+1 once). So this unit
records FG -0 +0 / T1 -0 +0. If the reviewer accepts the mapping of §4 to the final root and counts the F-kids assumptions as allowed, the
expected effect is B.P-8 -1 and B.P-1 -1 with +1 for N4-a at the final FG (net -1), which is the reviewer's call.

## 6. Not done / limits

* The roots of §4 are not the gen5 final root (not on this base); the structural comparison is for the in-tree users only.
* `legal_assembly` takes the run's own θ; legality for another θ' is not claimed.
* Collision with `θ ≠ []` is a failing command, not a legal binding: stated, not hidden.
* Success of specialization (B.P-5, `SpecSuccessAllPositive`) is not touched.

## Final: connection to the gen5 final statement (Issue sparkle-gen4-param-assembly, second step)

Status: built, awaiting reviewer. Nothing here is accepted by this document. No new assumption, no TRUSTED, no frozen text changed, no existing
file edited. Ledger: FG 75 / T1 57 (this unit: FG -0 +0 / T1 -0 +0). The subtraction is the reviewer's call.

Two branches, because the two lineages do not build together (§F.4):
* gen4 branch (this one): `Tools/ShippingGen4ParamFinal.lean`, `Tests/Gen4/ParamFinalCheck.lean` (`kjob lake build Tests.Gen4.ParamFinalCheck` exit 0).
* gen5 branch `kjob/passm2-g5scan` (= `par/sm1` 0fceecd7 merged, + `Tests/Gen5/ParamFinalScan.lean`, `kjob lake build` exit 0, 863 jobs).

### F.1 Where B.P-8 / B.P-1 appear in the gen5 final root (the scan)

`Tests/Gen5/ParamFinalScan.lean` walks the constants reachable from the TYPES (and definition values) of `FGLedgerPremisesStmtG` (13136 constants)
and `FGLedgerPremisesStmtH` (13486). Reached: none of `LegalBinding`, `AllPos`, `MemoFamily`, `MsgMvK`, `LamTelescopeN`. Positive controls: `Start`, `Laws`,
`synthesizeCombinationalWithParameters` are reached from H. So **B.P-8 and B.P-1 are not binders of G or H**: the ledger says so itself (Q-F3, §8.3: they
are registry rows, "UN-C", not hypotheses of the statement). The binders of H are `ι dom mref cref ReflectsAll Post lvl genData₀ CV L h_C_EN4 h_C_RK6 h_C_CV4`
(plus the inner hypotheses). The only place the final root meets the parametric route is `EntryWitness`: `Start L mctx cctx w ∧ (RunsTo (synthesizeCombinational ..) ∨
RunsTo (synthesizeCombinationalWithParameters declName parameters) ..) ∧ ReflectsAll ..`.
So "removing the binder from the final root" means: the parametric disjunct of the FG conclusion, once typed, is a statement over `L`, `Start` and the run; the row
version of that statement would carry `LegalBinding` and `AllPos` as obligations (as `ParamTopShips` does: `∀ θ, LegalBinding (D.addModule b) θ → ..`), and the run version does not.

### F.2 The row-form root over the FG binders

* `start_kwd`: `Start L mctx cctx w → AdmCtx L.O.quiet mctx cctx ∧ KWD L.O (fun _ _ => True) 0 w` (`Start = AdmCtx ∧ JQC`, `JQC ⊇ JQ = quiet ∧ sv ∧ dv`). No new assumption.
* `paramFinal_old {L} (hS : Start ..) (h : RunsTo (synthesizeCombinationalWithParameters ..) ..) (hL : LegalBinding (SpecDesign M' D') θ) (hpos : AllPos θ) (hok)` : `RootConcl`.
* `paramFinal_run {L} (M : MemoFamily L.O) (hmsg : MsgMvK L.O) (htel : LamTelescopeN) (hS : Start ..) (h : RunsTo ..) (hok)` : `RootConcl`.
`O`, `hA`, `hw` of `paramRoot_run` are no longer binders: `O := L.O`, and `hA`, `hw` come from `Start`.

### F.3 Crosswalk (premise of the assembly theorem → FG ledger)

| premise of `paramRoot_run` | FG ledger row | type match | bridge |
|---|---|---|---|
| `O : RefLawsAOps ..` | A.P-01 `L : Laws` (`L.O`, = T1L-01) | `L : Laws mref cref` is a binder of H (scan) and of `paramFinal_*`; `Laws`/`Start`/`AdmCtx`/`JQC` have equal type and value hashes in both environments (FINGERPRINT lines of the two Checks) | `O := L.O` (field) |
| `hA : AdmCtx O.quiet mctx cctx` | A.P-02 `Start` (1st conjunct of `EntryWitness`; merged: A.P-03, C.RR-1, B.F-2, D.E-11, D.D-6) | Check: conjunct 1 of `start_kwd` `==` type of `hA` at `O := L.O` | `(start_kwd hS).1` |
| `hw : KWD O (fun _ _ => True) 0 w` | A.P-02 `Start` (2nd conjunct, `JQC.1 = JQ`) | Check: conjunct 2 `==` type of `hw` at `O := L.O`; depth mutation 0→1 rejected | `(start_kwd hS).2` (`KW` with `P := True`) |
| the run `h` | A.P-04, 2nd disjunct of `EntryWitness` | canonical form of `h` (free variables renamed, `parameters`/`b`/`D` ↔ `θ`/`M'`/`D'`): hash 327093931 in both Checks | none |
| `hS : Start L mctx cctx w` | A.P-02 | canonical hash 1541700807 in both Checks | none |
| `M : MemoFamily O` (rev3) | **no row in the FG ledger 75.** It is M4.MEMO-01, a proposed FG row (+1 "when the K walk is accepted", KWALK_PLAN, MEMO_FAMILY_FREEZE §R7). Not reached from G/H. | — | not derivable from `L.T` (`RefLawsATele`) in the tree |
| `hmsg : MsgMvK O` | conditional leaf, no row (MEMO_FAMILY_FREEZE §R2.6) | not reached from G/H | none; stays conditional |
| `htel : LamTelescopeN` | N4-a (ledger §12.17), **new shared row, +1 once** | not reached from G/H | none |
| `ExprOK θ e` | the property of the source expression of the consumer, not a premise of the ledger; binder of the conclusion of `RootConcl` | — | — |

So the answer to "which premises are existing rows": O, hA, hw, the run and Start are existing (A.P-01, A.P-02, A.P-04) with equal types and a bridge lemma;
`LamTelescopeN` is N4-a (+1); `MemoFamily` is NOT an existing row of the 75 (M4.MEMO-01, pending); `MsgMvK` is the conditional leaf.

### F.4 What does not hold together: the gen4 chain does not build on the gen5 `Elab.lean`

Merging `par/sm1` (0fceecd7) into this lineage changes `Sparkle/Compiler/Elab.lean` (the `userInliner` / `MachRecUnfold` fuel: `userInlinerEWith`, `doSynth` fuel error, rt40-rt83).
`kjob lake build Tools.ShippingGen4ParamFinal` on the merge then fails: `Tools/ShippingGen4ParamEntry.lean:216` (whnf, 1600000 heartbeats) and
`Tools/ShippingGen4KWalkEntryCore.lean:229, 368` (whnf / isDefEq, 200000 heartbeats). Existing files were not repaired (rule). Hence a single theorem that has the gen5 final
statement and the parametric assembly in one environment does not exist yet; the gen4 side (`paramFinal_run`) and the gen5 side (G/H scan) are connected by the shared
`Laws` / `Start` / `RunsTo` definitions, whose fingerprints and canonical forms agree. Porting F-θ / F-top / F-kids / K walk to the gen5 `Elab` is separate work.

### F.5 Binder difference (Tests/Gen4/ParamFinalCheck.lean)

    PARAM-FINAL COUNTS: removed 2 [hL, hpos] (B.P-8, B.P-1), added 3 [M, hmsg, htel], changed 0, concl true; L (A.P-01) and hS : Start (A.P-02) shared; O, hA, hw not binders
    CROSSWALK: start_kwd conjuncts == types of hA / hw at O := L.O; premise head Start; depth-mutation and unrenamed controls rejected
    NEG: self empty, keep-hL rejected (removed [hpos]), extra binder rejected, other conclusion rejected, reversed rejected, free-carrier root (paramRoot_run, added 6) rejected
    HYPS: paramFinal_run binds exactly Start, MemoFamily, MsgMvK, LamTelescopeN, RunsTo, ExprOK; axioms propext, Classical.choice, Quot.sound; closure reaches no T1Hyp / T1HypND

### F.6 Net delta (not recorded; the basis for the reviewer)

| item | effect | basis |
|---|---|---|
| B.P-8 `LegalBinding` | -1 (registry row, UN-C) | binder `hL` removed (Check); not a binder of G/H (scan), so the row leaves when the typed parametric route is part of the final statement |
| B.P-1 `AllPos` | -1 (registry row, UN-C) | binder `hpos` removed (Check); `legalBinding_allPos` also gives it from B.P-8 |
| N4-a `LamTelescopeN` | +1 once (§12.17) | `htel` added, shared with F-θ / F-top / F-kids |
| M4.MEMO-01 `MemoFamily` | +1 pending (K-walk acceptance), **not in the reviewer's -2 +1** | `M` added; no row in FG 75 |
| `MsgMvK` | 0, conditional leaf | `hmsg` added |
| O, hA, hw | 0 | existing rows A.P-01 / A.P-02 through `start_kwd` |
| **net** | **-2 +1 = -1 with M4.MEMO-01 not counted; 0 when it is counted** | the ledger count stays FG 75 / T1 57 until the reviewer accepts F.4 and the mapping |

KWALK_PLAN already states the three conditional entries together (M4.MEMO-01 +1, B.P-8 -1, B.P-1 -1). The reviewer's forecast (-2, +1 N4-a, net -1) leaves MEMO-01 out.
