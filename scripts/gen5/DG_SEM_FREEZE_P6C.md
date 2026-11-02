# DG-SEM freeze P6c — supply survey for `hp / hq / GenIn / hord` and causality; first unit U6A (docs only)

**FOR REVIEW — design only; no Lean edited, nothing elaborated.** Agent g5sm-u8, base `680e1ff0` (= `7c06a80f` + comment-only header sync of U5E; U5E approved at `7c06a80f`, build `smu7v-7c06a80f`, exit 0, 749 jobs).
Everything is a PROPOSAL until approved. No new TRUSTED boundary/law, no FG/guarantee change, no shared-definition/compiler edit, no `GenWF` strengthening, no FG narrowing, no `sorry`/`axiom`/`native_decide`.
Marks: `[B]` = in this tree (read at `680e1ff0`); `[br:X@sha]` = read in branch `X` at that commit (NOT in this tree; the SEM lineage is before S1/DG-ACC/DG-DATAOF integration, so a re-check at the integration SHA is required); `[N]` = new here.
Method: names and statement heads were read from the branch text (`git show`/`git grep`); nothing was elaborated. "未供給 / この調査で経路未発見" means this survey did not find a route, not that none exists.

## 1. Header sync (done, comment-only, no rebuild)
`Tools/ShippingGen5SemExtPkg.lean` and `Tests/Gen5/SemExtPkgCheck.lean` headers now state: build `smu7v-7c06a80f` exit 0 (749 jobs), approved at `7c06a80f`, the S1 `callField_at` pattern fix is committed at `7c06a80f`; the "UNCOMMITTED local patch" wording is removed. Commit `680e1ff0`.

## 2. Supply table for the conditions of `genExtAtCall_of_genSem` (U5E) and of the facts
`P : Pkgs ι dom`, `K : AssignKit ι dom env₀` (DG-ACC's kit), `p q : Pkg ι dom`. "owner" = the issue that owns the row; a row owned elsewhere is NOT re-implemented here.

| # | condition (exact form) | route found (real names) | owner | status |
|---|---|---|---|---|
| 1 | `hp : p.toSem = genSemI (semOf P) X g` | `genP_generated : GenPGeneratedStmt K` `[br:g5ac-r8@5690f6de Tools/ShippingGen5AccGenP.lean]`: for `genP K hF X = some p`, `∃ E, entry₀ env₀ X = some E ∧ GeneratedAtK K (genP K hF) X E p`, with `GeneratedAtK K P X E p := ∃ g : K.GD E, p.toSem = K.genSem (semOf P) X g`. With `K.genSem := fun Q X gd => genSemI Q X (toIn gd)` (`genSemVia` `[B]`) this is `hp` with `g := toIn gd`. Kit fields `genSem_local/genSem_decl/genSem_d` ← `genSemI_local`, `genSemI_decl`, `genSemI_d` `[B]` (DG-SEM, built). | DG-ACC (`genP`, kit); kit instantiation = DG-ACC A6 (integration) | **条件付き**: needs `hF : GenSFacts K := ∀ X s, genS K X = some s → FactsOf s` (row 5, unsupplied), `GD`/`toIn` (row 3, `GenData.toIn` not found built in `g5do-r6`, `g5ac-r8`, `g5cv-r13`: 未供給) |
| 2 | `hq : P (p.d.shape.insts[k]'hk).1 = some q` | `genP_pkg : GenPPkgStmt K` `[br:g5ac-r8]` (`∀ c, Reach c → ∃ q, genP K hF c = some q ∧ q.decl = c ∧ DataOk q`, premises `hcl`, `hacc`, `hcov : ReachCover K Reach`, `hOk`) and `genP_closed : GenPClosedStmt K` (`Reach` is closed under ordinary callees: `Reach (q.d.shape.insts[k]).1` when `(q.d.shape.instOrigins.getD k .ord).child? = none`). `hacc` ← `acc_top_of_run`/`hacc_of_top_runs`/`accServed0_of_cover` `[br:g5ac-r8 AccReads/AccServed]`. | DG-ACC; `ReachCover` ← DG-COVER | **条件付き**: `hF` (row 5), `ReachCover`, `hOk`, `hacc` each a hypothesis there; not supplied by DG-SEM |
| 3a | `GenIn.ok / bodyEq / init` | `dataOfFrom_sound` / `dataOfAt_sound` `[br:g5do-r6@063056d6 Tools/ShippingGen5DataOf.lean:197,211]`: `dataOfFrom lvl E senv s tin fl = some d → d.shape = s ∧ d.ok = true ∧ d.shape.body = quote d.dom … ∧ d.initOk (initsOf d) = true` (so `inits := initsOf d`). | DG-DATAOF | 条件付き on `dataOfAt … = some d` (§11.2 rows 1-6,8 of DG-DATAOF: 未供給 per its note) |
| 3b | `GenIn.wf : GenWF d = true` | `genWF_iff : GenWF d = true ↔ RowA d = true ∧ RowB d = true ∧ RowC d = true` `[br:g5cv-r13 Cover.lean:86]`; U-D3 (`Cover3.lean:684`, RowA/B/C from invariants with premises `ShapeAgree`, `LetQuoteEq`, `LetsNoLoose`, …) and `rowC_of_reader_ok` `[br:g5cv-r13 Cover4.lean:54]` (`ShapeAgree d st → FullInv (kDOf d) st → LetQuoteEq d st → LetsNoLoose st → d.ok = true → ∀ k < d.shape.insts.length, ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true`). | DG-COVER (and DG-READERTRACE for the run-side premises) | **未供給 / interface premises named by DG-COVER**; reader-trace residue assigned to `sparkle-gen5-dg-readertrace` |
| 3c | `GenIn` as a structure from 3a+3b | `GenData.toIn` | DG-DATAOF / DG-SEM | **この調査で経路未発見**: no built `GenData`/`toIn` in the inspected branches (only a header remark in `T2Tie.lean`). A one-line constructor `⟨d, wf, initsOf d, ok, bodyEq, init⟩` is possible once 3a/3b exist; not designed here. |
| 4 | `hord : (originOf p.d k).child? = none` | Not a fact to supply but the call selection of the consumer: in T2-TIE it is the hypothesis `hord : (p.d.shape.instOrigins.getD k .ord).child? = none` of `callTie_of_served_oneOut_closing` `[B Tools/ShippingGen5T2OutTy.lean:59]`; `originOf d k := d.shape.instOrigins.getD k .ord` `[B SemGen.lean:24]` so the two are `rfl`-equal; on the kit side `AssignKit.mem_ordCallees : k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none` `[br:g5ac-r8]`; `InstOrigin.child? (.mem …) = some _`, others `none` `[B Sparkle/Compiler/MachInstOrigin.lean]`. | `sparkle-gen5-t2-tie` (consumer), `sparkle-gen5-dg-acc` (kit iff) | consumer-supplied; **nothing for DG-SEM to implement** |
| 5a | `GenFacts.causal` = `HCausalOf g.d dom (extOf Q g) (extBOf Q g)` (`Tools/ShippingSeqParentLemmas.lean:35` `[B]`) | **This unit's P6'** (§3). Needs `CalleesCausal Q g.d` and the memory-read causality. | **DG-SEM (this issue)** | designed here (U6A); **not implemented** |
| 5b | memory-read causality (`memRead` = `Signal.memoryComboRead` / `Signal.memory`) | Existing: `memState_congr`, `memory_val_succ` and the context forms `memoryComboRead_causal_ctx`, `memory_causal_ctx` `[B Tools/ShippingMachineMemCausal.lean:15,29,47]`. These are stated over `Ctx`/`CtxAgree`; a named lemma on `memRead cb A Dd E R` over plain signals (agreement of the four operands on `≤ t` ⇒ agreement of the read at `t`) was **not found** by this survey; the proof route from `memState_congr` is short (P4 §6 said "causality lemma not located"; this is the located material). | DG-SEM (this issue) | U6A lemma `memRead_causal` (§3) |
| 5c | `CalleesCausal Q g.d` for the real table | `genS_srcCausal_acc` (P10: `Acc` induction over `genS`) ← `genSemI_srcCausal` (P11) `[freeze DG_SEM_FREEZE.md §2.6; DGEN rev2 §2.1]` | DG-SEM (this issue) for P10/P11; `Acc` ← DG-ACC | **not designed in full here; not built** |
| 5d | `GenSFacts K` | `genFacts` (P11) discharges it from 5a + `GenFacts.ok/body_eq/init/writes/result/source` | DG-SEM (this issue) | **未供給**; it is the `hF` of rows 1 and 2, so rows 1 and 2 depend on 5a-5c |
| 6 | `CallOutRange p q k hk` (`houtTy`, `CallOutWidthAt`) | `callOutRange_of_widths` `[B T2Range.lean:162]`, `Pkg.src_range` `[B T2Range.lean:122]`; run-level inputs `houtTy`/`hW` | T2-TIE side (`sparkle-gen5-t2-tie`) | not in DG-SEM; not duplicated |
| 7 | `hnd` (callee output names `Nodup`) | derived inside U5E from `t2r_ok_outNames_nodup q.d q.ok` `[B]` | — | closed (U5E) |
| 8 | `hrow : FieldRowAt p k r.1` (T2-FIELD's field row) | one-output parent: `fieldRow_one_of_callStmt` `[B T2Tie.lean:178]`; group parent: the source comment says the group row (from `connsG` in `ServedGP`) is OPEN | `sparkle-gen5-t2-tie` / T2COVER | not a premise of U5E/U6A; listed because `CallField` is what `GenExtAtCall` quantifies over. 未供給 for group parents |

Reading of the table: the three conditions the brief calls `hp / hq / GenIn` all reduce, on the routes found, to (i) DG-ACC's `genP` machinery, which is conditional on `GenSFacts K`, and (ii) DG-DATAOF/DG-COVER for `GenIn`. `GenSFacts K` (row 5d) is produced by causality (5a-5c) plus the already-built `writes/result/source` side (P1-P3). Hence the causality chain is on the critical path of both `hp` and `hq` and is the only part of the table owned by this issue and not yet designed.

## 3. First unit to implement: U6A — `extCausal_of_genSem` (P6')
Reason: (1) it is owned here (no other issue lists it); (2) it is a pure statement over `GenIn`/`Q` (class I): no `dataOf`, no `Acc`, no real run, so it does not wait for DG-DATAOF/DG-COVER/DG-ACC; (3) it removes the `GenFacts.causal` field, which — with P11 — is what `GenSFacts` (rows 1, 2) needs; (4) it needs no `GenWF`: the stage argument below only uses that every read is pointwise at `t` or at earlier times.

New file `Tools/ShippingGen5SemCausal.lean`, namespace `Tools.ShippingGen5Sem`, `set_option autoImplicit false`, imports `Tools.ShippingGen5SemExt` (hence `SemCall`, `SemPkg`) and `Tools.ShippingMachineMemCausal`; same `open`s/variables as `Tools/ShippingGen5SemExt.lean` `[B]`: `{ι : Type} {dom : ι → DomainConfig}`. Lakefile: one `lean_lib` entry (and one for the Check).

### 3.1 Definitions — verbatim from DGEN rev2 `[br:par/gen5-t2 scripts/gen5/DGEN_FREEZE.md:184-192]`
```lean
def SrcCausal (s : SemPkg ι dom) : Prop :=
  ∀ (i : ι) (A A' : Nat → Signal (dom i) Bool) (B B' : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat),
    (∀ c, c ≤ t → (∀ j, (A j).val c = (A' j).val c) ∧ ∀ j n, (B j n).val c = (B' j n).val c) →
    (s.src i A B).map (fun f => f t) = (s.src i A' B').map (fun f => f t)

def CalleesCausal (Q : Name → Option (SemPkg ι dom)) (d : MachineData) : Prop :=
  ∀ k ∈ ordCallees d, ∀ s, Q (d.shape.insts[k]).1 = some s → SrcCausal s
```
(`SrcCausal`/`CalleesCausal` are not defined anywhere in this tree: `grep` over `Tools Tests` found no occurrence. They are definitions of a hypothesis, not a new law; their text is DGEN's.)

### 3.2 Theorems (complete types)
```lean
theorem memRead_causal {D : DomainConfig} {aw dw : Nat} (cb : Bool)
    (A A' : Signal D (BitVec aw)) (Dd Dd' : Signal D (BitVec dw)) (E E' : Signal D Bool) (R R' : Signal D (BitVec aw)) (t : Nat)
    (hA : ∀ c, c ≤ t → A.val c = A'.val c) (hD : ∀ c, c ≤ t → Dd.val c = Dd'.val c)
    (hE : ∀ c, c ≤ t → E.val c = E'.val c) (hR : ∀ c, c ≤ t → R.val c = R'.val c) :
    (Tools.ShippingMachineMemLinked.memRead cb A Dd E R).val t =
      (Tools.ShippingMachineMemLinked.memRead cb A' Dd' E' R').val t

theorem ExtStage_causal (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (hQ : CalleesCausal Q g.d) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S S' : Signal (dom i) (HList (tys g.d.ss))) (n : Nat) (t : Nat)
    (hS : ∀ c, c ≤ t → S.val c = S'.val c) :
    (∀ p, ((ExtStage Q g i bools bits S n).1 p).val t = ((ExtStage Q g i bools bits S' n).1 p).val t) ∧
    (∀ p w, ((ExtStage Q g i bools bits S n).2 p w).val t = ((ExtStage Q g i bools bits S' n).2 p w).val t)

theorem extCausal_of_genSem (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (hQ : CalleesCausal Q g.d) :
    Tools.ShippingSeqParentLemmas.HCausalOf g.d dom (extOf Q g) (extBOf Q g)
```
Proof plan. `memRead_causal`: case on `cb`; `memoryComboRead`/`memory` at `t` unfold to `memState` (`memory_val_succ` for the registered read at `t+1`), then `memState_congr` on times `< t` (operands agree there by `hX c (c ≤ t)`) and the read address at `t` (`hR`). `ExtStage_causal`: induction on `n`; base is `(bools, bits)` (identical on both sides). Step `n+1`: `callOut … n` — `insts[n]? = none` ⇒ unchanged; `.mem` ⇒ the new position is `memOut` whose four operands are `lsrcGet (lsrcAt g.d st.1 st.2 S) l _` and agree at every `c ≤ t` because `lsrcAt` at time `c` is `eval` of `typedVal … st.1 st.2 c (S.val c)` (reads `S.val c` and the stage-`n` families at `c`; use the IH at `c ≤ t`, with `hS` restricted to `≤ c`), then `memRead_causal`; other positions unchanged (`if p = kDOf g.d + n`). Non-`.mem` ⇒ `withCall … (calleeOut …)`; `calleeOut` at `t`: `Q c = none` ⇒ `0`; `some q` ⇒ `q.src i A B` with `A, B` the decoded `boolsOf/bitsOf (q.d.bsIn.take q.kD) (valsOf (lsrcAt …) args)`, which agree at every `c ≤ t` by the IH; `q` is an ordinary callee (`originOf g.d n` not `.mem` ⇒ `n ∈ ordCallees g.d` by definition of `ordCallees`), so `hQ` gives `SrcCausal q`, hence the `k'`-th output agrees at `t`. `extCausal_of_genSem`: unfold `HCausalOf`, `extOf`, `extBOf`, apply `ExtStage_causal` at `n := g.d.shape.insts.length`.
**Known delicate points (to be checked when implemented, reported if they fail):** the `h ▸` cast in `callOut`'s `.mem` branch (`dw = n`); `Fin`-indexed `ordCallees` membership from the non-`.mem` origin (`List.mem_filter`, `List.mem_finRange`); `valsOf`/`boolsOf`/`bitsOf` unfolding in the `SrcCausal` hypothesis form.

### 3.3 Check (new file `Tests/Gen5/SemCausalCheck.lean`, written from the sentences of §3.1-§3.2, not from the implementation)
- **TYPE**: each of `SrcCausal`/`CalleesCausal` (by body, independent `Exp` terms, same reducible comparer as `Tests/Gen5/SemExtCheck.lean`) and the three theorems (independent `Exp` statements; `HCausalOf` written out in its unfolded `∀`-form in the Exp, defeq-checked).
- **MUTANT** (well-typed single changes only; rejection is by signature/defeq, **not** a semantic counterexample): `memRead_causal` with `c ≤ t` replaced by `c < t` in `hR`; with `hR` dropped; `ExtStage_causal` with `hS` at `c < t`; with `hQ` dropped; `CalleesCausal` over all `k : Fin _` instead of `ordCallees` (different type); `SrcCausal` with `c ≤ t` ↔ `c < t`; conclusion conjunct dropped (`ExtStage_causal`'s `.2` conjunct; counted only where the statement has a conjunction).
- **AXIOMS**: standard only. **sorry**: absent.
- **CLOSURE**: the explicit walk of `Tests/Gen5/SemExtPkgCheck.lean` (unknown name ⇒ `throwError`): controls (1) unknown root, (2) forbidden root self-detected, (3) unknown helper value (message names the intended `Mv`), (4) unknown helper type (message names `Mt`), plus a clean control; fixtures only inside `withoutModifyingEnv`.
- **REACH**: `extCausal_of_genSem` reaches `ExtStage_causal`; `ExtStage_causal` reaches `memRead_causal` and `calleeOut`; `memRead_causal` reaches `memState_congr`.
- Numbers reported as real counts per category with the counting rule beside them. Builds: Pod `kjob lake build Tools.ShippingGen5SemCausal`, then `Tests.Gen5.SemCausalCheck`, one at a time; the clean focused build is the coder's; the built SHA goes into the header by a comment-only commit.

## 4. After U6A (not frozen here)
P10 `genS_srcCausal_acc` and P11 `genSemI_srcCausal` / `genFacts_gen` / `genFacts` need `SrcCausal (genSemI Q X g)` from `GenFacts.source`/`result` of the same construction (P1-P3, `Tools/ShippingGen5SemRef.lean`) — a separate, larger unit that will be re-frozen with a complete telescope before implementation. GenIn assembly (row 3c) waits for DG-DATAOF/DG-COVER.

## 5. Not claimed
- Not `hp`, `hq`, `GenIn`, `GenWF` coverage, `Acc`, `GenSFacts`, `CalleesCausal` for a real table, `CallOutRange`, M5, FG. No real run is supplied; U6A is conditional on `CalleesCausal Q g.d`.
- Rows read from other branches are not in this lineage; the SEM lineage is before S1/DG-ACC/DG-DATAOF integration, so the statements must be re-verified at the integration SHA.
- Statement heads in §2 were read, not elaborated; where a full type was not read it is not given.
