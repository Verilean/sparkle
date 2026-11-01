# DG-ACC / DG-ASSIGN / DG-GENP / DG-PKGASSIGN freeze rev1 (issue `sparkle-gen5-dg-acc`)

**FOR REVIEW (docs). Rev0 (`DG_ACC_FREEZE.md`, c5b9140c) is kept unchanged; this file answers its `changes_requested` (R1-R3, Q1-Q4).**
Base of this revision: `kjob/g5ac-r2` = c5b9140c + the A1-A2 commits below. Nothing in A3/A4/A5 is implemented; they are types only.

Tags: `[S]` source read in this worktree; `[B]` built (Pod `kjob lake build`, exit 0); `[F]` freeze text; `[E]` elaborated as a Pod-built scratch
(see §B.0; the scratch is NOT committed); `[M5]` = `git show par/gen5-t2:scripts/gen5/DGEN_FREEZE.md`; `[REACH]` = `git show kjob/g3rc-r2:scripts/gen3/REACH_FREEZE.md`
(rev0 0688aa13; the revision g3rc-r3 was not readable from this worktree, so §C uses rev0's S1/S3 and says where a newer text may differ);
`[SM4]` = `git show kjob/g5sm-aud:scripts/gen5/DG_SEM_FREEZE_P4.md` (30efb522); `[DO]` = `git show kjob/g5do-r3:scripts/gen5/DG_DATAOF_FREEZE.md`;
`[CV]` = `git show kjob/g5cv-r2:scripts/gen5/DG_COVER_FREEZE.md` (rev0 ec2fbda8).

Wording rule: "not found" means *this investigation found no supplier or route*, never "impossible". A MUTANT is a rejection of a changed, well-typed statement by
signature / defeq, **not** a semantic counterexample. Conditional results are INTERMEDIATE, never completion.

## 0. Summary of the changes against rev0

| rev0 item | rev1 |
|---|---|
| A1-A2 (pure kernel) | **Implemented and built** (§A): `Tools/ShippingGen5Acc.lean`, `Tests/Gen5/AccCheck.lean` |
| R1 `AccBodyKeeps` comment / unbound binders | **Fully defined; every binder typed** (§B); the whole of §B was elaborated `[E]` |
| R2 `T1Hyp(P:=genP).closed` used for reachability (cyclic with `genP_pkg ← hacc`) | **Withdrawn.** Reachability is `ReachEdge K Top` over the *reader data* (`dataOf₀`), supplier chain is acyclic (§C); off-route question fixed as a named, unsupplied premise |
| R3 `JQC` depth 0 ⇒ `CacheAcc` | **Not claimed.** The start is the world after the depth-0 head clear; bridge types in §D; `AccServedStmt` becomes `AccServed0Stmt` with the cache disjunct `dv w = 0 ∨ CacheAcc` (no new FG/cache premise) |
| Q1 `genSem_decl`/`genSem_d` | DG-SEM P4 provides them, exact types recorded (§E) |
| Q2 lemmas on the kit | made in A1; integration point recorded (§A.4) |
| Q3 additive copy | candidate (a), with the **exact supply type A5 must produce** fixed first (§C, §F) |
| Q4 top-level start | resolved by the `AccServed0Stmt` form (§B.3), not by a premise |

## A. A1-A2 as implemented

Commits on `kjob/g5ac-r2` (Lean): code `bfa8f81b`; header commits `e0c68a17`, `297e08e0` (restores `set_option autoImplicit false` that a header edit had dropped; rebuilt OK); rename `CoverAt→ReachCover` `fa4d6f1a`; header `567faeab` (comment-only: built SHA `fa4d6f1a`). Pod builds (`kjob lake build`, one target at a time):
`Tools.ShippingGen5Acc` exit 0; `Tests.Gen5.AccCheck` exit 0 (703 jobs), also after the rename. **Clean issue-linked build is the coder's; not yet run.**
New lean_lib entries only in `lakefile.lean`; no shared definition, no compiler file, no FG/law/TRUSTED change; no `sorry`/`axiom`/`native_decide` in the source.

### A.1 What is in `Tools/ShippingGen5Acc.lean` (namespace `Tools.ShippingGen5Acc`)
`entry₀`, `AssignKit` (fields: `dataOf GD dOf genData₀ ordCallees genSem` and spec fields `mem_ordCallees genData₀_dataOf genSem_local genSem_decl genSem_d`),
`dataOf₀`, `dataOf₀_of_genData₀`, `CallEdge`, `callEdge_of_ord`, `CallRel`, `genStep`, `genSAcc`, `genS`, `genSAcc_intro`, `genSAcc_irrel`, `genS_of_acc`, `genS_of_not_acc`,
`genS_step`, `genS_unfold` (locality: `genSem_local` with the callee-restricted table `Qx`), `genS_some_inv`, `CacheAcc`, `cacheAcc_insert`, `cacheAcc_empty`, `ReachEdge`,
`ReachCover` (rev0's `CoverAt`; renamed to avoid the clash with DG-COVER's `Tools.ShippingGen5Cover.CoverAt`), `genS_isSome_of_cover`. All classical splits; `Acc.rec` for `genSAcc`.
The kit field `genSem_decl`/`genSem_d` are included although A1-A2 do not use them (they are the §E request; `emptyKit` shows the set of spec fields is jointly inhabited).

### A.2 What `Tests/Gen5/AccCheck.lean` checks (Pod, exit 0)
* **TYPE** (11, `checkExpected` against independently written `Expected…` statements): `entry₀`, `CallEdge`, `CallRel`, `CacheAcc`, `ReachCover`, `callEdge_of_ord`, `genS_unfold`,
  `genS_some_inv`, `cacheAcc_insert`, `cacheAcc_empty`, `genS_isSome_of_cover`. **Four of them were accepted by `isDefEq`, not syntactically** (logged `GEN3 DEFEQ`):
  `CallRel` (expected is the lambda `fun c X => CallEdge K X c`, the definition is `flip (CallEdge K)`), and the conclusions of `callEdge_of_ord`, `genS_unfold`, `genS_some_inv`
  (the reason — a term in the `K.GD E`/`Fin` indexing or the decidability instance of the `if` — was not investigated). They are recorded as defeq-accepted, not as syntactic matches.
* **MUTANT** (8, `checkMutant`, well-typed one-place changes, rejected by signature/defeq only): `genS_unfold` without the strictness guard; `genS_unfold` with a callee-restricted table in the
  `genSem` argument; `genS_some_inv` with the empty table; `callEdge_of_ord` over every index; `CallEdge` without `child? = none`; `CacheAcc` without the `Reach c →` antecedent;
  `cacheAcc_insert` without its premise on the inserted key; `genS_isSome_of_cover` without `hcl`.
* **AXIOMS**: `Lean.collectAxioms` ⊆ {propext, Classical.choice, Quot.sound} for 22 declarations (and `emptyKit`, `emptyKit_genS`).
* **CLOSURE**: a separate walk that reads the explicit *value* of every `thmInfo`/`defnInfo`/`opaqueInfo` (not `ConstantInfo.value?`, which skips `opaqueInfo`) and the type of every constant.
  Result on 17 roots: 7567 constants (the walk goes through `entry₀` into the compiler's `Elab` definitions), no `sorryAx`/`ofReduceBool`/`trustCompiler`, no constant of the supplier units
  (`Tools.ShippingGen5DataOf*`, `Tools.ShippingGen5SemGen*`), 0 unknown. **Walker validation (controls)**: four negatives are flagged — forbidden constant directly in the root,
  through a helper of the same namespace, through a helper of another namespace (no prefix filter), through an `opaque` — and clean controls (a clean chain in this and another namespace) are
  not flagged; a root absent from the environment is reported as unknown (a `logInfo`), never skipped. The negatives are built with `addDecl` inside `withoutModifyingEnv`; no `sorry` text.
* **Non-vacuity of the spec fields**: `emptyKit` (`GD := Empty`, `genData₀ := none`) is an `AssignKit`; `emptyKit_genS : genS (emptyKit env₀) X = none`. This tests the statements,
  **not** DG-SEM's `genSem` or DG-DATAOF's `dataOf`.

### A.3 What A1-A2 do not give
`genS` is `none` wherever `Acc` fails or `genData₀`/strictness fails; nothing here says it is `some` on a real run. `genS_isSome_of_cover` needs `hacc` (A4), `hcl` (`ReachEdge.edge`), `ReachCover`
(DG-COVER/ENV; unsupplied). The kit fields are hypotheses; no owner's constant has replaced them.

### A.4 Integration point (Q2)
| lemma | here | at integration (A6) |
|---|---|---|
| `mem_ordCallees` | a kit **field** (proved by the owner's unit; `emptyKit` proves it for the filter form) | DG-SEM's `ordCallees` is the filter of `[SM4]` §1 (`(List.finRange _).filter fun k => (d.shape.instOrigins.getD k .ord).child? = none`): the field is `List.mem_filter`+`List.mem_finRange` |
| `genS_some_inv` | proved here directly at the kit | DG-SEM states `genS_some_inv_of_unfold` abstractly in `G` and `hunf`; this lemma is its instance at `G := genS K`, `hunf := genS_unfold`. **Single statement**: keep this unit's `genS_some_inv` as the exported one (it is already proved without DG-SEM) and have DG-SEM *use* it, or have this proof become the one-line application — decided when DG-SEM's lemma is built; no second statement is exported |
| `genSem_local` | kit field | replaced by DG-SEM's `genSemI_local` (congrArg through `toIn`, `[SM4]`) |
| `genSem_decl`, `genSem_d` | kit fields | replaced by DG-SEM's `genSemI_decl`/`genSemI_d` (§E) |
| `dataOf` | kit field | `Tools.ShippingGen5DataOf.dataOf` |

## B. R1 — A3/A4 as complete definitions (every binder typed)

### B.0 How this was checked
The text of §B.1-B.4 and §D.1 was put in an uncommitted scratch file, `import`ing `Tools.ShippingGen5Acc`, `Tools.ShippingGen5Env`/`EnvR`, `Tools.ShippingEntryReadsLinked`, `Tools.ShippingGen2T1`,
and built in the Pod (`kjob lake build`, exit 0, 714 jobs). The statements are `def … : Prop` (no proofs, no `sorry`); `genP`/`GeneratedAtK`/`AccInvAt`/… are the definitions themselves.
So these *types* elaborate; **no proof of A3/A4 was written or run**. The scratch is not part of the tree.

**Base defect found while doing this (not edited, not this Issue's).** `Tools/ShippingGen5T2Tie.lean:221` (`obtain ⟨-, q0, n, hq0, -, hCS⟩ := hS` on `hS : ShipsRes L P c r`) does not elaborate on this base:
`ShipsRes` has the third conjunct `InstClosed` (Defs:142-143, G-POST) and the pattern cannot split it (`rcases failed … is not an inductive datatype`). Hence any file importing
`Tools.ShippingGen5T2Tie` — through `Tools.ShippingGen5T2OutTy` → `Tools.ShippingGen5T1ND` → `Tools.ShippingGen5EnvQ` — does not build on this base. Rev0 §8 had A4 importing `Tools.ShippingGen5T1ND`;
rev1's A3/A4 avoid it (they need `Laws`/`Start`/`MachineClosesAtA` from Gen2/Gen2T1, `ReadsAt`/`MachineDefinesR` from `ShippingGen5Env`, `coreHead`/`envAt` from `ShippingEntryReadsLinked`). The EnvQ lemmas Q9/Q10 are *read* in §D, not imported.
Reported to the coder in the Issue note.

### B.1 The lean file preamble used for the check
`open Lean Meta Tools.ShippingEntrySoundness Sparkle.Compiler.Elab Tools.ShippingChildInv Tools.ShippingChildBndCore Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildFrontCP Tools.ShippingChildCacheA`,
`open Tools.ShippingChildRunAKids (MachineClosesAtA)`, `open Tools.ShippingMachineEntry (MachineDefines)`, `open Tools.ShippingGen2 Tools.ShippingGen5Sem Tools.ShippingGen5Acc`,
`open Tools.ShippingGen5Env (ReadsAt MachineDefinesR)`, `open Classical`;
`variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀) {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}`.

### B.2 The elaborated definitions and statements (`[E]`)
```lean
/-! ## A3 -/
def GenSFacts : Prop := ∀ X s, genS K X = some s → FactsOf s

noncomputable def genP (hF : GenSFacts K) (X : Name) : Option (Pkg ι dom) :=
  match h : genS K X with
  | some s => some (genPkg s (hF X s h))
  | none => none

def SemOfGenPStmt : Prop := ∀ (hF : GenSFacts K), semOf (genP K hF) = genS K

def GeneratedAtK (P : Pkgs ι dom) (X : Name) (E : ConstantInfo) (p : Pkg ι dom) : Prop :=
  ∃ g : K.GD E, p.toSem = K.genSem (semOf P) X g

def GenPGeneratedStmt : Prop :=
  ∀ (hF : GenSFacts K) {X : Name} {p : Pkg ι dom}, genP K hF X = some p →
    ∃ E, entry₀ env₀ X = some E ∧ GeneratedAtK K (genP K hF) X E p

def GenPDeclStmt : Prop := ∀ (hF : GenSFacts K) {X : Name} {p : Pkg ι dom}, genP K hF X = some p → p.decl = X

def GenPDEdgesStmt : Prop :=
  ∀ (hF : GenSFacts K) {X : Name} {p : Pkg ι dom}, genP K hF X = some p → ∃ d, dataOf₀ K X = some d ∧ p.d = d

def GenPPkgStmt : Prop :=
  ∀ (hF : GenSFacts K) {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c) (hacc : ∀ c, Reach c → Acc (CallRel K) c)
    (hcov : ReachCover K Reach) (hOk : ∀ c, Reach c → ∀ q, genP K hF c = some q → DataOk q),
    ∀ c, Reach c → ∃ q, genP K hF c = some q ∧ q.decl = c ∧ DataOk q

def GenPClosedStmt : Prop :=
  ∀ (hF : GenSFacts K) {Reach : Name → Prop} (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c),
    ∀ c, Reach c → ∀ q, genP K hF c = some q → ∀ k (hk : k < q.d.shape.insts.length),
      (q.d.shape.instOrigins.getD k .ord).child? = none → Reach (q.d.shape.insts[k]).1

/-! ## A4 -/
def AccInvAt (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) : Void IO.RealWorld → Prop :=
  fun w => JQC L.O D w ∧ CacheAcc K Reach (cv w)

def AccIHAt (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) : Prop :=
  ∀ c, Reach c → ∀ (mctx : Meta.Context) (cctx : Core.Context) (u u' : Void IO.RealWorld) (r : Res),
    AdmCtx L.O.quiet mctx cctx → AccInvAt K L Reach D u →
    RunsTo (synthesizeCombinational c) mctx mref cctx cref u r u' → Acc (CallRel K) c

def AccBodyKeeps (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
    ∀ (declName : Name) (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo) (isInst : Lean.Expr → Bool),
      Keeps mctx mref cctx cref (AccInvAt K L Reach D)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)

def AccChildKeeps (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) : Prop :=
  ChildSynthA L.O (AccInvAt K L Reach D)

def AccKeepChildStmt (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ D, 1 ≤ D → (D < sparkleSynthDepthLimit → AccBodyKeeps K L Reach (D + 1)) →
    AccIHAt K L Reach D → AccChildKeeps K L Reach D

def AccServed0Stmt (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ (X : Name) (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (r : Res),
    Reach X → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w → (dv w = 0 ∨ CacheAcc K Reach (cv w)) →
    AccIHAt K L Reach (dv w + 1) → AccChildKeeps K L Reach (dv w + 1) →
    RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w r w' →
    ∀ c, CallEdge K X c → Acc (CallRel K) c

def AccIHAtLimit (L : Laws mref cref) : Prop := LimitStmt L

def AccIHAtStepStmt (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  AccServed0Stmt K L Reach → ∀ (D : Nat), AccIHAt K L Reach (D + 1) → AccChildKeeps K L Reach (D + 1) → AccIHAt K L Reach D

def AccOfRunStmt (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  LimitStmt L → AccServed0Stmt K L Reach → AccKeepChildStmt K L Reach →
    ∀ D, 1 ≤ D → AccIHAt K L Reach D ∧ AccChildKeeps K L Reach D

/-! ## Route / data link (P-free) -/
def MachineRouteAt (env₀ : Environment) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
    ∃ shape : MachineShape, MachineDefinesR env₀ mctx mref cctx cref c shape ∧ MachineClosesAtA L.O mctx cctx c shape

def RunDataLink (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
    ∀ shape : MachineShape, MachineDefinesR env₀ mctx mref cctx cref c shape →
      ∃ d, dataOf₀ K c = some d ∧ d.shape = shape

def AccServedOfRoute (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  MachineRouteAt env₀ L Reach → RunDataLink K L Reach → AccServed0Stmt K L Reach

/-! ## R3 bridge types -/
def JQE (quiet : Void IO.RealWorld → Prop) (D : Nat) : Void IO.RealWorld → Prop :=
  fun w => JQ quiet D w ∧ cv w = {}

def HeadAccStartStmt (Reach : Name → Prop) : Prop :=
  ∀ {L L' : Laws mref cref} {mctx : Meta.Context} {cctx : Core.Context} {w₀ w1 : Void IO.RealWorld} {X : Name}
    {s : Tools.ShippingEntryReadsLinked.CoreSaved},
    (∀ w, L'.O.quiet w ↔ (L.O.quiet w ∧ ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w₀) cref w)) → AdmCtx L'.O.quiet mctx cctx →
    Start L mctx cctx w₀ →
    RunsTo (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref w₀ s w1 →
    AccInvAt K L' Reach 1 w1 ∧ ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w₀) cref w1
```

### B.3 Notes on these definitions
* **`AccBodyKeeps`** is `BodyKeepsInv` (Defs:174-180) with `InvAt L P Reach D` replaced by `AccInvAt K L Reach D` and nothing else (same binders: `mctx cctx`, `AdmCtx`, `declName tenv b ci isInst`, the same `synthesizeFromConst` term).
  `AccChildKeeps` is `ChildKeepsInv` with the same replacement; `AccKeepChildStmt` is `KeepChildStmt` (Defs:194-196) with the replacement. `AccIHAt` is `IHAt` (Defs:165-172) with the conclusion `Acc (CallRel K) c`.
* **`AccServed0Stmt` replaces rev0's `AccServedStmt`** and is the exact analogue of `ServedShips0Stmt` (T1:112-123): the start is `JQC L.O (dv w) w` with the cache disjunct
  `dv w = 0 ∨ CacheAcc K Reach (cv w)`, **not** `AccInvAt (dv w) w`. It has no `T1Hyp`/`Pkgs` argument (the conclusion is about the static edge relation `CallEdge K`, which only needs the reader data).
  The conclusion is about the static edges of `X`: `∀ c, CallEdge K X c → Acc (CallRel K) c`.
  *Use in the induction:* nested levels (`D ≥ 1`): the `AccIHAt D` hypothesis gives `AccInvAt D u`, so the start is `⟨u.1, Or.inr u.2⟩`; the outermost run: `Start L` gives `JQC L.O 0 w`, hence
  `dv w = 0` (`JQ`'s third field), so `Or.inl`. The outermost cache is therefore *not* assumed empty; the head clear (§D) is what produces the cache fact.
* **`AccOfRunStmt`** (the statement `acc_of_run` proves): `LimitStmt L → AccServed0Stmt K L Reach → AccKeepChildStmt K L Reach → ∀ D, 1 ≤ D → AccIHAt K L Reach D ∧ AccChildKeeps K L Reach D`.
  Proof shape (rev0 §5.3, unchanged): `ih_allPF`'s induction on `sparkleSynthDepthLimit - D`; base `accIHAt_limit` (`ihAt_limit`'s copy, from `LimitStmt`); step `accIHAt_step` assembles `Acc.intro c` from
  `AccServed0Stmt` (`CallRel K c' c = CallEdge K c c'`). `AccIHAtStepStmt` is the type of `accIHAt_step`.
* **A3 statements** (`GenPDeclStmt`, `GenPDEdgesStmt`, `GenPPkgStmt`, `GenPClosedStmt`, `SemOfGenPStmt`, `GenPGeneratedStmt`): `GenSFacts K` is the one named premise (owner DG-FACTS/DG-CAUSAL); `hcl`, `hacc`, `hcov`, `hOk` are
  typed as above. `GenPPkgStmt`'s conclusion is the type of `T1Hyp.pkg` at `P := genP K hF`; `GenPClosedStmt`'s is the type of `T1Hyp.closed` (checked by TYPE against the field types at implementation).
  `genP_decl` uses `genSem_decl` (§E), `genP_d_edges` uses `genSem_d` and `dataOf₀_of_genData₀` (built).
  `genP_closed` takes **only** `GenSFacts` and `hcl`: its proof is `genP_d_edges` + the definition of `CallEdge` (no `Acc`).

## C. R2 — the order in which the pieces are supplied (no cycle)

Rev0 §5.4 / §6 used `T1Hyp(P := genP).closed` to get `Reach c` of the served callee, while `genP_pkg` (which `T1Hyp.pkg` needs) depends on `hacc`, which is `acc_of_run`'s output. That is a cycle and is withdrawn.

### C.1 The dependency order (each line uses only earlier lines)
| # | piece | uses | does it mention `genP`/`T1Hyp(genP)`? |
|---|---|---|---|
| 0 | kit fields (`dataOf`, `genData₀`, `genSem`, …) | DG-DATAOF, DG-SEM | no |
| 1 | A1-A2: `CallEdge`, `genS`, `genS_unfold`, `CacheAcc`, `ReachEdge K Top` (`[B]`) | 0 | no |
| 2 | `Top` and `Reach := ReachEdge K Top`; `hcl` is the constructor `edge` | 1 | no |
| 3 | **run-level evidence for `AccServed0Stmt`** (A5): `MachineRouteAt env₀ L Reach` and `RunDataLink K L Reach` (below), the Acc analogues of M3's closing results (§F) | 0, 1 | **no** |
| 4 | `AccServed0Stmt K L Reach`, `AccKeepChildStmt K L Reach` | 3 | no |
| 5 | `acc_of_run` ⇒ `hacc : ∀ c, Reach c → Acc (CallRel K) c` | 4, `LimitStmt` (`limitStmt_proved` `[B]`) | no |
| 6 | `genS_isSome_of_cover` (needs `ReachCover` from DG-COVER/ENV and `hacc`, `hcl`) | 1, 5 | no |
| 7 | `GenSFacts K` | DG-FACTS/CAUSAL (their producers `genFacts`, `genS_srcCausal_acc` are stated over `genS` in DGEN/rev0 §4; not re-checked in this revision) | no |
| 8 | `genP`, `genP_pkg`, `genP_closed` ⇒ the `pkg`, `closed` fields of `T1Hyp`/`T1HypND` at `P := genP K hF` | 5, 6, 7 | now yes — nothing earlier depends on them |

The `defines`/`closes`/`dec` fields of `T1Hyp(genP)` are other units' (G3-SHAPE, G-CLOSES, G-CALLDEC) and are not supplied here.

### C.2 Why `MachineRouteAt` and `RunDataLink` replace `T1Hyp.defines/closes/closed` in step 3
M3's `servedShips0_proved` (Served:636-655) obtains `p`, `p.d.shape`, `MachineDefines`, `MachineClosesAtA` and the key match `hreach` from `T1Hyp(P)` of the *same* package `P`. For `P := genP`
that is circular (§C). The P-free forms, both in §B.2:
* `MachineRouteAt env₀ L Reach`: every reached name has *a* shape with `MachineDefinesR env₀ …` (DG-ENV D2, `Tools.ShippingGen5Env`: env₀-agreeing read worlds) and `MachineClosesAtA` — i.e. route 3 is taken
  and returns. It is the content of `defines`+`closes` without `P c = some q`. Supplier: G3-SHAPE/G-CLOSES in the P-free reading; **this investigation did not check whether their cited suppliers
  (`closes_of_data`, `memCallee_closesA`) are stated through `P` or through the reader data `d`**. Not supplied.
* `RunDataLink K L Reach`: the run's shape *is* the reader data's shape of `entry₀ env₀ c`: `MachineDefinesR env₀ … c shape → ∃ d, dataOf₀ K c = some d ∧ d.shape = shape`.
  Derivation sketch (not proved): `MachineDefinesR` gives `machineShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)) (structEnv envR') = some shape`;
  `ReadsAt env₀ cref` at the read worlds identifies `structEnv`/`instancePredicate`/`userInliner` with `env₀`'s and `ci` with `env₀.find? c` (`ci_of_readsAt`), so the entry is `entry₀ env₀ c` and
  `machineShape? … (structEnv env₀) = some shape`; DG-COVER supplies `dataOf E (structEnv env₀) shape = some d` (their `CoverAt`, `[CV]` §3; unsupplied); DG-DATAOF's `dataOf_sound` first conjunct gives `d.shape = shape`
  (`[DO]` §2.4). The P-ENV point (`structEnv envR` vs `structEnv envR'`) is DG-ENV's `SigEq` (`[CV]` §0), also unsupplied. **Neither mentions `genP`.**
* The static edge `X → c` (a `CallEdge`) is then `shape.insts[k].1 = c` with `child? = none` for *the run's own* `shape`, exactly the key the closing synthesises ([REACH] §2: `closeInstsGM` passes `(insts[k]).1` for `child? = none`; `closeInstsM` passes every `insts[k].1`).
  This is [REACH] S3 (`childrenShips_reached`) *over `K`*: where S3 takes `H : T1Hyp L P Reach DataOk` to get `closed` and `defines`, the K-form takes `RunDataLink` for `defines` and uses `ReachEdge.edge` for `closed`.
  If g3rc-r3 changed S1/S3, this text should be re-read against it; nothing here depends on rev0's `ReachFrom P Top` (the `P`-indexed relation), which would reintroduce the cycle for `P := genP`.

### C.3 The fallback / gate row, fixed
`MachineDefinesR` includes "both certified gates return `none` at the entry" and `MachineClosesAtA` excludes `none` at the machine synthesis. So `MachineRouteAt` is a statement about names **whose successful run is the machine route**.
For a reached name whose successful run goes through a certified gate or through the legacy fallback after the machine synthesis returns `none`, **this investigation found no supplier or route** for
"the run serves (by nested run or cache hit) every ordinary static callee of `dataOf₀`". Such a name does not satisfy `MachineRouteAt`, so `AccServed0Stmt`'s supply does not apply to it; `CallEdge K X c` can still hold for it
(its reader data exists whenever `machineShape?` is `some`), so the case is **not** vacuous. It is recorded as the named open row `OffRouteServes` (statement fixed in words: for `Reach` names not on route 3, every `CallEdge K X c` callee is `Acc`),
unsupplied, and is the same coverage question as `T1Hyp.closes` on `Reach` in M3 (route 4 is "not removed from FG", GENERAL_SPEC). It is not added as an FG premise here.

## D. R3 — the start world after the head clear, and the bridge

`JQC L.O 0 w` does not give `CacheAcc … (cv w)`: the cache may be non-empty (`CacheInvA` allows it). It is **not** claimed. What makes the cache fact true is the depth-0 *clear* in the entry's prefix.

### D.1 What exists (M3, `[S]`)
* `Tools/ShippingGen2ServedRun.lean:80` `core_reads_invAt0` (with `tripleInv_clear`, :56, `stableA_invAt`, `tripleInv_depthSet`): from `JQC L.O D w` and `hc : D = 0 ∨ CacheShips L P Reach (cv w)` and the core run, the prefix
  reaches `InvAt L P Reach (D + 1) w3` (D = 0: `tripleInv_clear` establishes both cache halves; D > 0: `InvAt D` is the stable invariant of the whole walk). `synthesizeFromConst_machine_invAt` (:178) and
  `machineRunInv_of_core0` (:221) carry it to the machine run's start world. All use only `L.O.cacheSet`, `cacheSetQ`, `depthSet`, the `StableA` frame, and `cacheShips_empty`.
* DG-ENV `Tools/ShippingGen5EnvQ.lean` (read, not imported, §B.0): `jq_start` (Q9): `Start L` + `QuietStrength` give `JQ L'.O.quiet 0 w₀`; `head_jqc_start` (Q10): `JQC L'.O 1 w1 ∧ ReadsAt (envAt cref w₀) cref w1` at the end `w1` of
  `coreHead X` (RR1 `coreHead_jqcA`, `Tools/ShippingGen5RunReads.lean:69`: the same head, `JQC` only — RR1's later `peelF` steps use `stableA_JQC`, which does **not** track `cv w = {}`).
  RunReads' header: "Not claimed: … `InvAt` at `w5`".

### D.2 What is needed (types; copies of the M3 items with `InvAt → AccInvAt`, `cacheShips_empty → cacheAcc_empty` `[B]`; no new law, no FG change)
```lean
-- stable (depends on cv, sv, dv, quiet only), copy of `stableA_invAt` (Connect:41)
theorem stableA_accInvAt (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) : StableA L.O.quiet (AccInvAt K L Reach D)
-- copy of `tripleInv_clear` (ServedRun:56): the clear establishes both cache halves; the Acc half by `cacheAcc_empty`
theorem tripleAcc_clear (L : Laws mref cref) (Reach : Name → Prop) {mctx cctx} (hA : AdmCtx L.O.quiet mctx cctx) (D : Nat)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQ L.O.quiet D) (sparkleChildCache.set {} : MetaM Unit) (fun _ => AccInvAt K L Reach D) R
-- copy of `tripleInv_depthSet`
-- copy of `core_reads_invAt0` (ServedRun:80), conclusion with `AccInvAt K L Reach (D + 1) w3`, hypotheses `JQC L.O D w`, `hc : D = 0 ∨ CacheAcc K Reach (cv w)`
-- copies of `synthesizeFromConst_machine_invAt` (:178), `machineRunInv_of_core0` (:221), `machineRunInv_of_closes0` (:284) into `AccMachineRun`
```
The linked-world form (the one that includes `AdmCtx`, `ReadsAt`, the quiet strengthening) is `HeadAccStartStmt` (§B.2, `[E]`): with `QuietStrength L L' (envAt cref w₀)` (inlined as `∀ w, L'.O.quiet w ↔ L.O.quiet w ∧ ReadsAt (envAt cref w₀) cref w`),
`AdmCtx L'.O.quiet mctx cctx`, `Start L mctx cctx w₀` and the `coreHead X` run `w₀ → w1`, conclude `AccInvAt K L' Reach 1 w1 ∧ ReadsAt (envAt cref w₀) cref w1`.
Proof design: `jq_start` (Q9) gives `JQ L'.O.quiet 0 w₀`; the head is RR1's walk with the post-clear invariant `JQE (quiet) D := JQ quiet D ∧ cv = {}` (a `StableA` predicate by the same `cv w' = cv w` frame as `stableA_JQC`)
— `tripleC_clear`'s own proof already derives `cv w' = {}` (`hk.1`) and `depthSet` frames the cache; then `cacheAcc_empty`. `ReadsAt` is Q10's second conjunct. No `Start L'`, no FG wrapper, `hA'` stays a premise as in Q10.
Equivalently one can use the M3 route (`core_reads_accInvAt0`, whose `w3` is the world after the same head); the choice is deferred to A5 (both are statements about the same run).

### D.3 What this does and does not give
It gives `AccInvAt (D+1)` at the world after the head, for D = 0 (empty cache) and for D > 0 (from the incoming `CacheAcc`), i.e. the start of the body. **Not supplied:** `CacheAcc` at the machine run's start `w5` and along the
children closing — the Acc copies of `synthesizeFromConst_machine_invAt` and of the closing lemmas (§F). No FG premise about the cache is added or needed.

## E. Q1-Q4

* **Q1 (DG-SEM).** `[SM4]` (30efb522, kjob/g5sm-aud:scripts/gen5/DG_SEM_FREEZE_P4.md, §1/§2) provides `genSemI_decl : ∀ Q X g, (genSemI Q X g).decl = X` and `genSemI_d : ∀ Q X g, (genSemI Q X g).d = g.d` in unit U4B and says the kit fields follow
  (`dOf g = g.d`). The exact types this unit requires (kit fields): `genSem_decl : ∀ Q X {E} (g : GD E), (genSem Q X g).decl = X`; `genSem_d : ∀ Q X {E} (g : GD E), (genSem Q X g).d = dOf g`; `genSem_local` as in §A. Premises on DG-SEM, unbuilt.
* **Q2.** §A.4.
* **Q3.** Candidate (a) (additive copy in new files) — §F gives the exact types A5 must produce; (b) generic transport is not possible without editing M3's `InvAt`-specific files (forbidden); (c) strengthening `CacheShips` is a shared-definition change (forbidden without user approval). No decision requested now; reversible (additive).
* **Q4.** Resolved by `AccServed0Stmt` (§B.3) and the head clear (§D); no FG/cache premise.

## F. A5 — the Acc supply (types fixed first; nothing implemented)

The statement A5 must produce is `AccServed0Stmt K L Reach` and `AccKeepChildStmt K L Reach` from `MachineRouteAt`, `RunDataLink`, `ReachEdge`. Items (M3 source → Acc counterpart; "size" is the M3 file's line count, an indication of the work, not an estimate):

| item | M3 source | Acc counterpart | needs |
|---|---|---|---|
| head / prefix | ServedRun:56-176 (`tripleInv_clear`, `core_reads_invAt0`) | `tripleAcc_clear`, `core_reads_accInvAt0` (§D.2) | `cacheAcc_empty` `[B]` |
| machine branch | ServedRun:178-241 (`synthesizeFromConst_machine_invAt`, `machineRunInv_of_core0/closes0`) | `AccMachineRun` (`∃ tenv b w9 w10, RunsTo (synthesizeMachineCertified …) … ∧ AccInvAt K L Reach n w9`) | `MachineRouteAt` |
| closings | ServedRun:342-460 (`ChildrenShipsI`, `closeInstsM_ships`, `closeInstsGM_ships`) | `ChildrenAccI` (per k: `child? = some y ∨ (RealChildA … ∧ (Reach (insts[k]).1 → Acc (CallRel K) (insts[k]).1))`) and the two closings at `AccInvAt` | `AccIHAt`, `AccChildKeeps` |
| nested child | KeepChild:292 (`synthesizeChild_tripleInv`), :255 (`cacheShips_insert`) | `synthesizeChild_tripleAcc` using `cacheAcc_insert` `[B]` | `AccIHAt` |
| key match | [REACH] S3 | `childrenAcc_reached`: with `RunDataLink` and `ReachEdge.edge`, `child? = none` ⇒ `Reach (insts[k]).1` ⇒ `Acc` | `RunDataLink` |
| keeps | KeepChild (387 lines), the body keep | `AccBodyKeeps`/`AccChildKeeps` from the above | the Acc closings |

M3 files involved: `ShippingGen2ServedRun.lean` (511 lines), `ShippingGen2Served.lean` (680, of which the Acc counterpart needs only the closing-level part, not `soundX`/trace), `ShippingGen2KeepChild.lean` (387). The `hord1`/G-ONEOUT-REACH premise of `soundX_ships_ran`
is not in the list: `AccServed0Stmt` concerns only `CallEdge` (`child? = none`) edges, so memory-origin entries synthesised by the one-output closing are keys outside `CallEdge`; whether any further premise appears in the proof is found at implementation.

## G. Audit plan for A3/A4 (when implemented; unchanged in kind from A1-A2)
TYPE: independent `Expected…` for every theorem of §B plus `GenPPkgStmt`/`GenPClosedStmt` against the *field types* of `T1Hyp.pkg`/`closed` at `P := genP K hF` (`example … := rfl`), and for the definitions `AccInvAt`, `AccIHAt`, `AccBodyKeeps`, `AccChildKeeps`, `AccServed0Stmt`
(each against `InvAt`/`IHAt`/`BodyKeepsInv`/`ChildKeepsInv`/`ServedShips0Stmt` with the stated replacement, not by unfolding). MUTANT (signature/defeq rejection only): `AccServed0Stmt` with `AccInvAt (dv w) w` start (rev0's form); without the `dv w = 0 ∨ …` disjunct;
`CallEdge` replaced by the unrestricted edge; `genP` ignoring `hF`; `genP_closed` without `child? = none`; `acc_of_run` without `LimitStmt`; `AccBodyKeeps` with `InvAt` (not `AccInvAt`). AXIOMS: standard three only. CLOSURE: explicit-value walker with the same
negative controls (direct / same-namespace / other-namespace / opaque) and clean controls as `AccCheck`; no supplier-unit constant; unknown constants reported. A concrete-kit non-vacuity witness for `genP` (`emptyKit`-style) is **not** planned to show anything about the real units.

## H. Units after this revision
| unit | content | state |
|---|---|---|
| A1, A2 | §A | **implemented, Pod-built, checked**; clean build = coder |
| A3 | `GenSFacts`, `genP`, `semOf_genP`, `GeneratedAtK`, `genP_generated`, `genP_decl`, `genP_d_edges`, `genP_pkg`, `genP_closed` (§B) | types elaborated `[E]`; **proofs not written**; needs `genSem_decl/_d` (kit fields) |
| A4 | `AccInvAt`, `AccIHAt`, `AccBodyKeeps`, `AccChildKeeps`, `AccKeepChildStmt`, `AccServed0Stmt`, `accIHAt_limit/_step`, `acc_of_run` | types elaborated `[E]`; proofs not written; conditional on `AccServed0Stmt`, `AccKeepChildStmt` (still premises) |
| A5 | §D, §F | types fixed; **unsupplied** |
| A6 | replace kit fields by owners' constants | waits (DG-SEM P4, DG-DATAOF built, DG-COVER) |

## I. Not claimed
* `acc_of_run`'s premises `AccServed0Stmt`, `AccKeepChildStmt`, and `MachineRouteAt`, `RunDataLink`, `OffRouteServes`, `ReachCover`, `GenSFacts`, `ReadsAt`-coverage have no producer in this investigation. DG-ACC is **not** done.
* The A1-A2 results hold at the kit; they say nothing about DG-SEM's `genSem` or DG-DATAOF's `dataOf` until A6.
* No Lean in §B/§D was proved or run beyond the signature-level elaboration of §B.0; no change to FG, `T1Hyp`/`T1HypND`, a law, a TRUSTED boundary, or the compiler. The base defect in `Tools/ShippingGen5T2Tie.lean` is reported, not fixed.
