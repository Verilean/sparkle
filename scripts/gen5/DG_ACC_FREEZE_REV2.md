# DG-ACC freeze rev2 (issue `sparkle-gen5-dg-acc`): R1 read-world supply, R2 `hacc` for all of `Reach`

**FOR REVIEW (docs).** Rev1 (`DG_ACC_FREEZE_REV1.md`, cfd730c0) is kept unchanged; this file answers the two `changes_requested` items
of the review of cfd730c0 (R1, R2). Base: `kjob/g5ac-r2` cfd730c0. A1-A2 are not rebuilt.

Tags: `[S]` source read in this worktree; `[B]` built in the Pod (`kjob lake build`, exit 0); `[E]` elaborated and proved in a Pod-built
scratch file `Tools/ShippingGen5AccQ.lean` (**not committed**; its text is §B and §C below; build exit 0, 716 jobs).

Wording rule: "not found" means *this investigation found no supplier or route*, never "impossible". A MUTANT is a rejection of a changed,
well-typed statement by signature / defeq, **not** a semantic counterexample. Conditional results are INTERMEDIATE, never completion.

## 0. Summary

| review item | rev2 answer |
|---|---|
| R1 `MachineRouteAt` asks only `MachineDefinesR env₀`; `AccInvAt`/`AccServed0Stmt` carry no `ReadsAt` | The missing premise is exactly `ChainReadsAt`: `ReadsAt env₀` at the three worlds `w1 w2 w3` of the run's own chain (`RunReadsAt.chain`: after `coreHead`, `getConstInfo`, first `getEnv`). (a) It is stated as the exact proposition `ReadsSupplyAt env₀ L Reach` (§B.2) with the use lemma `machineDefines_at_chain` `[E]`. (b) For a quiet-strengthened `L'` (`QuietStrengthA L L' env₀`) `ReadsSupplyAt env₀ L' Reach` is **proved** from `QuietStrengthA` and the single primitive premise `GetEnvFrame` (DG-ENV) `[E]`; transport `accInvAt_readsAt`, `accInvAt_down` `[E]` (§B.3-B.4). No `ReadsSupplyAt` for a non-strengthened `L` is claimed. |
| R2 `acc_of_run` ⇒ all-`Reach` `hacc` does not follow (`AccIHAt` is a success-run implication) | `hacc` for every name of `Reach := ReachEdge K Top` is **not** taken from runs of those names. `Acc` of the tops comes from a successful outermost run of each top (`acc_top_of_run`, from `AccServed0Stmt` + `acc_of_run` at depth 1), and `Acc` flows down the static edges by `Acc.inv` (`acc_of_edge`, `acc_reach_of_top`); composed in `hacc_of_top_runs` `[E]` (§C). Supplier of the premise: a successful outermost run of each top, which is the hypothesis of the consumer's theorem, not a new fact. Remaining rows in §D. |
| A3 conditional package construction | **Implemented**, `Tools/ShippingGen5AccGenP.lean`, `Tests/Gen5/AccGenPCheck.lean` (§E). |
| A4 conditional induction skeleton | **Implemented**, `Tools/ShippingGen5AccInd.lean`, `Tests/Gen5/AccIndCheck.lean` (§E). |
| A5 (the supply of `AccServed0Stmt`, `AccKeepChildStmt`) | **Not implemented.** Types fixed in rev1 §F, now with the read-world premise of §B. |

## B. R1 — the read worlds

### B.1 What is missing, exactly
`MachineDefinesR env₀ mctx mref cctx cref c shape` (`Tools/ShippingGen5EnvR.lean:24`) is `MachineDefines` with the premises `ReadsAt env₀ cref w1`, `ReadsAt env₀ cref w5`, `ReadsAt env₀ cref w7`
at the read worlds of its three `RunsTo` hypotheses. `MachineRouteAt env₀ L Reach` (rev1 §B.2) only says `∃ shape, MachineDefinesR env₀ … ∧ MachineClosesAtA …`; to *use* it on the run of `X` one must discharge those
three premises at the worlds of **that** run. The run's worlds are `RunReadsAt.chain` (`Tools/ShippingGen5RunReads.lean:36-52`): `coreHead X : w → w1`, `getConstInfo X : w1 → w2`, `getEnv : w2 → w3` (returns `envR`),
`getEnv : w3 → w5` (returns `envR'`); so the premises are needed at `w1`, `w2`, `w3` (the binders `w1 w5 w7` of `MachineDefinesR` are instantiated to `w1 w2 w3`).
`AccInvAt K L Reach D w = JQC L.O D w ∧ CacheAcc K Reach (cv w)` and `AccServed0Stmt` mention no `ReadsAt` at any world, so nothing in rev1's types supplies them. Rev1's C.2 was therefore not connectable to a consumer that has
only `MachineDefinesR env₀`.

### B.2 The exact premise, and its use `[E]` (Lean, complete types)
`EnvQ` (`Tools/ShippingGen5EnvQ.lean`) cannot be imported here: it imports `T1ND` → `T2Tie`, which does not elaborate on this base (rev1 §B.0, `Tools/ShippingGen5T2Tie.lean:221`, not edited). `QuietStrengthA` and `AdmDownA` are therefore **textual copies**
of `QuietStrength`/`AdmDown` (EnvQ:38, :42); they were compared with the originals by reading, **not** by a mechanical comparison, because the original cannot be imported.

```lean
/-! ## R1 -/

/-- Copy of `Tools.ShippingGen5EnvQ.QuietStrength` (EnvQ cannot be imported on this base, freeze rev1 §B.0). -/
def QuietStrengthA (L L' : Laws mref cref) (e : Environment) : Prop :=
  ∀ w, L'.O.quiet w ↔ (L.O.quiet w ∧ ReadsAt e cref w)

/-- Copy of `Tools.ShippingGen5EnvQ.AdmDown`. -/
def AdmDownA (L L' : Laws mref cref) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L'.O.quiet mctx cctx → AdmCtx L.O.quiet mctx cctx

/-- The read worlds of the actual run chain (`RunReadsAt.chain`): the three worlds at which `MachineDefinesR` asks `ReadsAt`. -/
def ChainReadsAt (e : Environment) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (X : Name) (w : Void IO.RealWorld) : Prop :=
  ∀ (s : CoreSaved) (w1 w2 w3 w5 : Void IO.RealWorld) (ci : ConstantInfo) (envR envR' : Environment),
    RunsTo (coreHead X) mctx mref cctx cref w s w1 →
    RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
    ReadsAt e cref w1 ∧ ReadsAt e cref w2 ∧ ReadsAt e cref w3

/-- The exact supply proposition for the read worlds (R1 (a)): at the start `w` of a run of a reached name. -/
def ReadsSupplyAt (e : Environment) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ X, Reach X → ∀ (mctx : Meta.Context) (cctx : Core.Context) (w : Void IO.RealWorld),
    AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w → ChainReadsAt e mctx mref cctx cref X w

/-- Use: `MachineDefinesR` gives its three conjuncts at the chain's read worlds. -/
theorem machineDefines_at_chain {e : Environment} {mctx : Meta.Context} {cctx : Core.Context} {X : Name}
    {shape : MachineShape} {w : Void IO.RealWorld} (hD : MachineDefinesR e mctx mref cctx cref X shape)
    (hR : ChainReadsAt e mctx mref cctx cref X w) {s : CoreSaved} {w1 w2 w3 w5 : Void IO.RealWorld}
    {ci : ConstantInfo} {envR envR' : Environment}
    (h0 : RunsTo (coreHead X) mctx mref cctx cref w s w1)
    (h1 : RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2)
    (h2 : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3)
    (h3 : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5) :
    certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) = none ∧
    mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) (instancePredicate envR) = none ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) (structEnv envR') = some shape := by
  obtain ⟨r1, r2, r3⟩ := hR s w1 w2 w3 w5 ci envR envR' h0 h1 h2 h3
  exact hD w1 ci w2 w2 envR w3 w3 envR' w5 r1 r2 r3 h1 h2 h3

/-- (b) `AccInvAt` at a quiet-strengthened `L'` carries `ReadsAt`. -/
theorem accInvAt_readsAt {L L' : Laws mref cref} {e : Environment} (hq : QuietStrengthA L L' e)
    {Reach : Name → Prop} {D : Nat} {w : Void IO.RealWorld} (h : AccInvAt K L' Reach D w) : ReadsAt e cref w :=
  ((hq w).mp h.1.1.1).2

theorem jqA_down {L L' : Laws mref cref} {e : Environment} (hq : QuietStrengthA L L' e) {D : Nat}
    {w : Void IO.RealWorld} (h : JQ L'.O.quiet D w) : JQ L.O.quiet D w := by
  unfold JQ at h ⊢
  exact ⟨((hq w).mp h.1).1, h.2⟩

theorem realChildA_downA {L L' : Laws mref cref} {e : Environment} (hq : QuietStrengthA L L' e)
    (hd : AdmDownA L L') {c : Name} {r : Res} (h : RealChildA L'.O c r) : RealChildA L.O c r := by
  induction h with
  | run mctx cctx w w' adm _ synth quiet hr ih =>
    exact .run mctx cctx w w' (hd _ _ adm) (fun c' r' hc => ih c' r' hc) synth ((hq w).mp quiet).1 hr

theorem jqc_downA {L L' : Laws mref cref} {e : Environment} (hq : QuietStrengthA L L' e)
    (hd : AdmDownA L L') {D : Nat} {w : Void IO.RealWorld} (h : JQC L'.O D w) : JQC L.O D w :=
  ⟨jqA_down hq h.1, fun c r hc => realChildA_downA hq hd (h.2 c r hc)⟩

/-- Transport `L' → L` of the Acc invariant (needs `AdmDownA`, an OPEN premise of DG-ENV). -/
theorem accInvAt_down {L L' : Laws mref cref} {e : Environment} (hq : QuietStrengthA L L' e)
    (hd : AdmDownA L L') {Reach : Name → Prop} {D : Nat} {w : Void IO.RealWorld}
    (h : AccInvAt K L' Reach D w) : AccInvAt K L Reach D w :=
  ⟨jqc_downA hq hd h.1, h.2⟩

/-- The supply of the read worlds at the quiet-strengthened `L'`: from `QuietStrengthA` and the one primitive premise
`GetEnvFrame` (DG-ENV). The head world `w1` is quiet by RR1 (`coreHead_jqcA`), hence `ReadsAt`; `w2`, `w3` by the frame. -/
theorem readsSupply_of_quiet {L L' : Laws mref cref} {e : Environment} (hq : QuietStrengthA L L' e)
    (hg : ∀ (mctx : Meta.Context) (cctx : Core.Context), GetEnvFrame mctx mref cctx cref)
    (Reach : Name → Prop) : ReadsSupplyAt e L' Reach := by
  intro X _ mctx cctx w hA hjqc s w1 w2 w3 w5 ci envR envR' h0 h1 h2 h3
  have hj1 : JQC L'.O (dv w + 1) w1 :=
    Tools.ShippingGen5RunReads.coreHead_jqcA L'.O hA hjqc.1 (Or.inr hjqc.2) h0
  have r1 : ReadsAt e cref w1 := ((hq w1).mp hj1.1.1).2
  have r2 : ReadsAt e cref w2 :=
    Tools.ShippingGen5Env.ReadsAt.of_frame (envFrame_getConstInfo X (hg mctx cctx)) h1 r1
  exact ⟨r1, r2, Tools.ShippingGen5Env.ReadsAt.of_frame (hg mctx cctx) h2 r2⟩

/-! ## R2 -/

/-- Acc flows down the static edges (`Acc.inv`; `CallRel K c X = CallEdge K X c`). -/
theorem acc_of_edge {X c : Name} (h : Acc (CallRel K) X) (he : CallEdge K X c) : Acc (CallRel K) c :=
  h.inv he

theorem acc_reach_of_top {Top : Name → Prop} (hT : ∀ t, Top t → Acc (CallRel K) t) :
    ∀ c, ReachEdge K Top c → Acc (CallRel K) c := by
  intro c hc
  induction hc with
  | top ht => exact hT _ ht
  | edge _ he ih => exact acc_of_edge K ih he

/-- A successful outermost run of `t` gives `Acc t` (its served static callees are `Acc`, and `Acc.intro`). -/
theorem acc_top_of_run (L : Laws mref cref) (Reach : Name → Prop) (hS : AccServed0Stmt K L Reach)
    (hI : AccIHAt K L Reach 1) (hKI : AccChildKeeps K L Reach 1) {t : Name} (ht : Reach t)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {r : Res}
    (hSt : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalCore t [] false) mctx mref cctx cref w r w') :
    Acc (CallRel K) t := by
  have hdv : dv w = 0 := hSt.2.1.2.2
  have hIH : AccIHAt K L Reach (dv w + 1) := by rw [hdv]; exact hI
  have hKI' : AccChildKeeps K L Reach (dv w + 1) := by rw [hdv]; exact hKI
  have hsrv := hS t mctx cctx w w' r ht hSt.1 (by rw [hdv]; exact hSt.2) (Or.inl hdv) hIH hKI' hr
  exact Acc.intro t fun y hy => hsrv y hy

/-- `hacc` for every reached name from successful outermost runs of the tops (no run of the other reached names). -/
theorem hacc_of_top_runs (L : Laws mref cref) (Top : Name → Prop)
    (hLim : LimitStmt L) (hS : AccServed0Stmt K L (ReachEdge K Top)) (hKC : AccKeepChildStmt K L (ReachEdge K Top))
    (hrun : ∀ t, Top t → ∃ (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (r : Res),
      Start L mctx cctx w ∧ RunsTo (synthesizeCombinationalCore t [] false) mctx mref cctx cref w r w') :
    ∀ c, ReachEdge K Top c → Acc (CallRel K) c := by
  obtain ⟨hI, hKI⟩ := acc_of_run K L (ReachEdge K Top) hLim hS hKC 1 (Nat.le_refl 1)
  refine acc_reach_of_top K fun t ht => ?_
  obtain ⟨mctx, cctx, w, w', r, hSt, hr⟩ := hrun t ht
  exact acc_top_of_run K L (ReachEdge K Top) hS hI hKI (ReachEdge.top ht) hSt hr
```

### B.3 What (b) gives, and what it does not
* `readsSupply_of_quiet`: for a given `L'` with `QuietStrengthA L L' env₀`, and `GetEnvFrame mctx mref cctx cref` for the contexts used, `ReadsSupplyAt env₀ L' Reach` holds. The proof: RR1 (`coreHead_jqcA`, built `[S]`) gives `JQC L'.O (dv w + 1) w1`, hence
  `L'.O.quiet w1`, hence `ReadsAt env₀ cref w1` by `QuietStrengthA`; `w2` and `w3` by `ReadsAt.of_frame` with `envFrame_getConstInfo`/`GetEnvFrame` (DG-ENV E3, built). The start world needs only `JQC L'.O (dv w) w` and `AdmCtx L'.O.quiet mctx cctx`
  (`hjqc.2` is the `CacheInvA` half RR1 asks for; no cache disjunct is needed).
* **Premises of (b), all named and unsupplied here:** (1) `QuietStrengthA L L' env₀` — an `L'` whose `quiet` is `quiet ∧ ReadsAt env₀` is *given*, not built (DG-ENV's own status); (2) `GetEnvFrame` — "the bare read of the Core environment leaves the Core
  environment unchanged", a premise about the opaque `ST.Ref.get` (`Tools/ShippingEnvSnapshot.lean:62`); this investigation found no proof of it in the tree; (3) for `accInvAt_down` only, `AdmDownA L L'` (EnvQ's OPEN C-ADM new⇒old).
* **Not claimed:** `ReadsSupplyAt env₀ L Reach` for an `L` that is not quiet-strengthened (its start world has no `ReadsAt`; this investigation found no route to it); the supply of `MachineRouteAt`, `RunDataLink`, `OffRouteServes` (unchanged, rev1 §C.2-C.3);
  that the FG's `L` can be replaced by `L'` (a statement about DG-ENV's `EnvLawsQ`, not decided here; `accInvAt_down` gives only the state transport `AccInvAt K L' → AccInvAt K L`, not a transport of `AccServed0Stmt`).

### B.4 Consequence for C.2 / A5
A5's consumer is stated at `L'`: `AccServed0Stmt K L' Reach`, `AccKeepChildStmt K L' Reach`, with `MachineRouteAt env₀ L' Reach` (its `AdmCtx`/`MachineClosesAtA` at `L'.O`; `closesA_up` of EnvQ moves `MachineClosesAtA` old⇒new, not imported here) and `RunDataLink K L' Reach`.
In the run, `machineDefines_at_chain` discharges the three `ReadsAt` premises of `MachineDefinesR` at the chain worlds from `ReadsSupplyAt env₀ L' Reach` (`readsSupply_of_quiet`). If a consumer instead has the all-world `MachineDefines` (T1Hyp.defines), the premises are not needed (`machineDefinesR_of_defines`, EnvR R1).

## C. R2 — `hacc` for every name of `Reach`

### C.1 Why the rev1 row 5 did not follow
`AccIHAt K L Reach D` is "every *successful* run of `c` from an `AccInvAt D` world gives `Acc c`". `acc_of_run` proves `AccIHAt` at all `D ≥ 1`, but `hacc : ∀ c, Reach c → Acc (CallRel K) c` needs *a* successful run of each reached `c` from such a world, which nothing supplies
(rev1 §C.1 row 5 was an overreach).

### C.2 The replacement (proved `[E]`, types in §B.2's file text below `## R2`)
`CallRel K c X = CallEdge K X c` (`flip`), so `Acc X` says exactly "every static callee of `X` is `Acc`", and `Acc.inv` carries `Acc` along an edge. Hence `Acc` of the tops is enough, and runs of the other reached names are not used:
* `acc_of_edge : Acc (CallRel K) X → CallEdge K X c → Acc (CallRel K) c`;
* `acc_reach_of_top : (∀ t, Top t → Acc (CallRel K) t) → ∀ c, ReachEdge K Top c → Acc (CallRel K) c`;
* `acc_top_of_run`: `AccServed0Stmt K L Reach`, `AccIHAt K L Reach 1`, `AccChildKeeps K L Reach 1`, `Reach t`, `Start L mctx cctx w`, and a successful `synthesizeCombinationalCore t [] false` run from `w` give `Acc (CallRel K) t`
  (`Start` gives `dv w = 0`, `JQC L.O 0 w`, `AdmCtx`; the conclusion of `AccServed0Stmt` is the premise of `Acc.intro`);
* `hacc_of_top_runs`: with `LimitStmt L`, `AccServed0Stmt K L (ReachEdge K Top)`, `AccKeepChildStmt K L (ReachEdge K Top)` and, for every `t` with `Top t`, a successful outermost run of `t` from a `Start` world, `∀ c, ReachEdge K Top c → Acc (CallRel K) c`.

The premise "a successful outermost run of each top" is not a new FG/cache premise: it is the hypothesis of the consumer's theorem about the top it compiled (`Top := {X}` for the compiled `X`).

### C.3 Revised dependency order (rev1 §C.1, rows 3-5)
| # | piece | uses | mentions `genP`/`T1Hyp(genP)`? |
|---|---|---|---|
| 3 | `MachineRouteAt env₀ L' Reach`, `RunDataLink K L' Reach`, `ReadsSupplyAt env₀ L' Reach` (§B) | 0, 1 | no |
| 4 | `AccServed0Stmt K L' Reach`, `AccKeepChildStmt K L' Reach` (A5) | 3 | no |
| 5a | `acc_of_run` ⇒ `AccIHAt`, `AccChildKeeps` at `D ≥ 1` (built, A4) | 4, `LimitStmt` (`limitStmt_proved`) | no |
| 5b | `hacc_of_top_runs` ⇒ `hacc` on `ReachEdge K Top` (§C.2) | 5a, successful outermost run of each top | no |
| 6-8 | as rev1 (`genS_isSome_of_cover` with `ReachCover`, `GenSFacts`, `genP`, `genP_pkg`, `genP_closed`) | 5b | rows 8 only |

The order is acyclic: nothing in rows 3-5 mentions `genP`.

## D. Open rows after rev2 (this investigation found no supplier or route for these)
* `AccServed0Stmt`, `AccKeepChildStmt` (A5; M3's closing files, rev1 §F).
* `MachineRouteAt`, `RunDataLink`, `OffRouteServes` (rev1 §C.2-C.3); `ReachCover` (DG-COVER/ENV); `GenSFacts` (DG-FACTS/CAUSAL); the real kit (DG-SEM P4 `genSem_decl`/`genSem_d`, DG-DATAOF), recorded as kit fields.
* `QuietStrengthA`, `GetEnvFrame`, `AdmDownA` (§B.3).
* head-clear bridge (rev1 §D): holds only under the explicit `QuietStrength`/`hA` of `HeadAccStartStmt`; not proved here.
* A successful outermost run of each top: a hypothesis of the consumer, not produced here.

## E. A3 and A4 as implemented (Lean, new files; no shared or compiler file edited)

* **A3** `Tools/ShippingGen5AccGenP.lean`: `GenSFacts`, `genP`, `SemOfGenPStmt`, `GeneratedAtK`, `GenPGeneratedStmt`, `GenPDeclStmt`, `GenPDEdgesStmt`, `GenPPkgStmt`, `GenPClosedStmt`, and proofs `genP_eq_some`, `genP_eq_none`, `genP_some_inv`,
  `semOf_genP`, `genP_generated`, `genP_decl`, `genP_d_edges`, `genP_pkg`, `genP_closed`. Conditional on `GenSFacts K` (a named premise) and, for `genP_pkg`, on `hcl`/`hacc`/`ReachCover`/`hOk`. `genP_decl`/`genP_d_edges` use the kit fields `genSem_decl`/`genSem_d`.
* **A4** `Tools/ShippingGen5AccInd.lean`: the definitions of rev1 §B.2 (`AccInvAt`, `AccIHAt`, `AccBodyKeeps`, `AccChildKeeps`, `AccKeepChildStmt`, `AccServed0Stmt`, `AccIHAtStepStmt`, `AccOfRunStmt`) plus `AccKeepBodyStmt`, and proofs `stableA_accInvAt`, `accInvAt_sv`,
  `translate_keepsAcc_of_tele`, `accKeepBody` (the copy of `keepBody`: `AccChildKeeps D → AccBodyKeeps D`, **proved**, so `AccKeepChildStmt` needs no further body premise), `accIHAt_limit`, `accIHAt_step`, `acc_of_run`.
  `acc_of_run` is **conditional** on `LimitStmt` (proved elsewhere), `AccServed0Stmt`, `AccKeepChildStmt` (premises).
* **Checks** `Tests/Gen5/AccGenPCheck.lean`, `Tests/Gen5/AccIndCheck.lean`: TYPE (independent `Expected…`, `checkExpected` on definition values binder by binder; every theorem by an `example` against the independent statement; `T1Hyp.pkg`/`closed` field types at `P := genP K hF` in both directions),
  MUTANT (6 + 7, well-typed one-place changes; signature/defeq rejection, not semantic counterexamples), AXIOMS (standard three), CLOSURE (explicit-value walker of `AccCheck`, negative and clean controls re-run, no supplier-unit constant, 0 unknown).
* The rev1 base defect (`Tools/ShippingGen5T2Tie.lean:221`) is unchanged and still not this Issue's.

## F. Not claimed
DG-ACC is **not** done. `AccServed0Stmt`, `AccKeepChildStmt`, `MachineRouteAt`, `RunDataLink`, `OffRouteServes`, `ReachCover`, `GenSFacts`, `QuietStrengthA`, `GetEnvFrame`, `AdmDownA` have no producer in this investigation. The results hold at the kit and say nothing about DG-SEM's
`genSem` or DG-DATAOF's `dataOf` until A6. No change to FG, `T1Hyp`/`T1HypND`, a law, a TRUSTED boundary, or the compiler. §B-§C Lean text is a Pod-built scratch (not committed) pending review; A5 is not started.
