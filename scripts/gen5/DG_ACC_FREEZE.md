# DG-ACC / DG-ASSIGN / DG-GENP / DG-PKGASSIGN freeze rev0 (issue `sparkle-gen5-dg-acc`)

**FOR REVIEW — design only. No Lean is edited or run in this revision.** Base: `kjob/g5sm-u3` 309a33a9 (par/gen3-combined 9d26005c
+ DG-SEM freeze rev3 fix a31d2297 + SEM U3 4ebc4067). Lean implementation starts only after this freeze is approved.

Tags: `[S]` = source read in this worktree; `[B]` = built (Pod `kjob lake build`, recorded in a file header); `[F]` = a freeze text, not built;
`[M5]` = `git show par/gen5-t2:scripts/gen5/DGEN_FREEZE.md` (rev2 c398021c); `[REACH]` = `git show kjob/g3rc-r2:scripts/gen3/REACH_FREEZE.md`
(rev0 0688aa13, design only); `[DO]` = `git show kjob/g5do-r2:scripts/gen5/DG_DATAOF_FREEZE.md` (rev1 8d20ae99; pure Lean 462ea73d unbuilt).

## 0. Scope, and what this document does NOT claim

Scope = DGEN rev2 §2.5 C1-C3 (DG-ASSIGN), C5-C6 (DG-GENP), the DG-ACC row, the DG-PKGASSIGN row ([M5] §4 table, lines 663-672; text 350-440).

* **Not supplied by this unit, ever:** `GenData`/`dataOf`/`dataOf_sound` (DG-DATAOF), `genSem`/`genSem_local`/`GenWF`/`GenIn`/`ordCallees`/
  `genFacts`/`genSem_srcCausal`/`GeneratedAt` (DG-SEM), `ShapeFuelBridge` (SRC-ARGW), `ReadsAt` coverage for real runs (DG-ENV C0), coverage of
  `genData₀` on real runs (DG-COVER/WFCOVER). They enter as **named parameters / premises** (§2, §3).
* **Not claimed:** `acc_of_run` is stated and its induction is *proved from* named premises (`AccServedStmt`, `AccKeepChildStmt`, `LimitStmt`).
  Until those two premises have producers, §5's result is **conditional/intermediate**, not "Acc supplied". "No supplier of `AccServedStmt` /
  `AccKeepChildStmt` was found in this investigation" is the status; impossibility is not claimed.
* Every MUTANT in §7 is a rejection by signature / defeq, **not** a semantic counterexample.
* No new law, TRUSTED boundary, FG/guarantee change, compiler/shared-definition edit (`Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`
  untouched), no coverage narrowing, no `GenWF` strengthening. All Lean is new files.

## 1. Ownership and pins (nothing below is re-defined here)

| name | owner | where it lives today | pin | status |
|---|---|---|---|---|
| `GenIn`, `GenWF`, `kDOf`, `valAtE`…`genSemGenE` | DG-SEM | `Tools/ShippingGen5SemGen.lean` `[B]` | 4ebc4067 | built (scoped); `GenIn` is NOT `GenData` |
| `SemPkg`, `FactsOf`, `Pkg.toSem`, `genPkg`, `semOf`, `toSem_genPkg` | DG-SEM | `Tools/ShippingGen5SemPkg.lean` `[B]` | g5smv-1cc605ef | built |
| `GenData E senv`, `genSem Q X g`, `genSem_local`, `ordCallees`, `SrcCausal`, `CalleesCausal`, `genFacts`, `genSem_srcCausal`, `GeneratedAt`, `genSem_decl`/`genSem_d` | DG-SEM (rev2 §2.1/§7, rev3 P11/P12 roadmap) | `scripts/gen5/DG_SEM_FREEZE_REV2.md` §2, `[M5]` §2.1 | — | **no Lean yet** (rev3 roadmap) |
| `dataOf`, `initsOf`, `dataOf_sound` | DG-DATAOF | `[DO]` §2.2/§2.4 | 8d20ae99 | freeze; pure part unbuilt |
| `GenWF`-coverage, `dataOf` totality on real runs | DG-COVER/WFCOVER | `kjob/g5cv-*` | — | in progress |
| `ReadsAt env₀ cref w` | DG-ENV | `Tools/ShippingGen5Env.lean:41` `[B]` | g5env2-6f966746 | built; C0 itself NOT supplied |
| `entryConst`, `machineShape?`, `structEnv`, `instancePredicate`, `userInliner` | compiler | `Sparkle/Compiler/Elab.lean:5272/5072/4394/5397/3387` | — | used, not edited |
| `T1Hyp`, `T1HypND`, `Pkgs`, `CacheShips`, `ShipsRes`, `InvAt`, `IHAt`, `ChildKeepsInv`, `KeepChildStmt` | M3 | `Tools/ShippingGen2Defs.lean`, `Tools/ShippingGen5T1ND.lean` `[B]` | 9d26005c | used, not edited |
| `LimitStmt`, `limitStmt_proved`, `ihAt_limit`, `ih_allPF` (shape to mirror) | M3 | `Tools/ShippingGen2T1.lean:100/127/150/190` `[B]` | 9d26005c | used |
| `cacheShips_insert` (shape to mirror) | M3 | `Tools/ShippingGen2KeepChild.lean:255` `[B]` | 9d26005c | mirrored |
| `ReachFrom`/`reachFrom_closed`/`reachFrom_least`, `childrenShips_reached` (S1/S3) | M3 G-REACH | `[REACH]` §3 | 0688aa13 | **design only, no Lean** |

## 2. The replacement-point kit (what is a parameter, and what it is replaced by)

DG-SEM's `genSem`/`GenData` and DG-DATAOF's `dataOf` do not exist as Lean yet. They are received as **fields of one structure**, each field the exact
type of the owner's DGEN/rev2 text. A field that is a *theorem* in the owner's unit (`genSem_local`, `genSem_d`, …) is a field here and is replaced by that
theorem. No field is a new law: each is a statement the owner's freeze says it proves.

```lean
namespace Tools.ShippingGen5Acc
open Lean Sparkle.Compiler.Elab Sparkle.IR.Machine Tools.ShippingGen2 Tools.ShippingGen5Sem
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}

/-- Replacement points. `GD E` is DG-DATAOF/DG-SEM's `GenData E (structEnv env₀)`; `dOf` its `.d`. -/
structure AssignKit (ι : Type) (dom : ι → Sparkle.Core.Domain.DomainConfig) (env₀ : Environment) where
  dataOf    : ConstantInfo → StructEnv → MachineShape → Option MachineData                         -- [DO] §2.2 `dataOf`
  GD        : ConstantInfo → Type                                                                  -- `GenData E (structEnv env₀)`
  dOf       : {E : ConstantInfo} → GD E → MachineData                                              -- `GenData.d`
  genData₀  : (E : ConstantInfo) → Option (GD E)                                                   -- [M5] C1
  ordCallees : (d : MachineData) → List (Fin d.shape.insts.length)                                 -- [M5] §2.1
  genSem    : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom -- [M5] §2.1
  /- spec fields (each is a theorem of the owner's unit; see §3 table) -/
  mem_ordCallees : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none
  genData₀_dataOf : ∀ {E g}, genData₀ E = some g →
      machineShape? false [] E (structEnv env₀) |>.bind (dataOf E (structEnv env₀)) = some (dOf g)   -- hshape+hdata of [M5] R7
  genSem_local : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E} (g : GD E),
      (∀ k ∈ ordCallees (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g                                                                 -- [M5] §2.1 (R8)
  genSem_decl : ∀ Q X {E} (g : GD E), (genSem Q X g).decl = X
  genSem_d    : ∀ Q X {E} (g : GD E), (genSem Q X g).d = dOf g
```
`SemPkg.decl`/`SemPkg.d` are the accessors of `Tools/ShippingGen5SemPkg.lean` `[B]`. `genSem_decl`/`genSem_d` are not stated in rev2 §2.1 by name;
for `genSemGenE` both are definitional (`decl := X`, `d := g.d`, SemGen.lean `[B]`), and the `.comb` arm is `[F]`. They are requested of DG-SEM in §9 Q1
(if DG-SEM does not provide them, DG-PKGASSIGN's `q.decl = c` and `closed` rows lose their supplier; the rest is unaffected).

`AssignKit` is a `structure` of data + theorems, with `genSem`'s output a `SemPkg`; it is `Type 1` (contains `Type`-valued `GD`). It is **only** a carrier:
no field's value is chosen here. At integration, `K := ⟨dataOf, fun E => GenData E (structEnv env₀), GenData.d, genData₀, ordCallees, genSem, …⟩`
and every theorem below is instantiated at that `K` by `exact`.

### 2.1 Replacement table (the substitution points)

| kit field | replaced by | substitution is | owner's unit / SHA |
|---|---|---|---|
| `dataOf` | `Tools.ShippingGen5DataOf.dataOf` | `rfl` (same type) | DG-DATAOF, 8d20ae99 (pure 462ea73d unbuilt) |
| `GD`, `dOf` | `fun E => GenData E (structEnv env₀)`, `GenData.d` | `rfl` | DG-SEM `[M5]` R7, unbuilt |
| `genData₀` | DG-SEM/DATAOF's `genData₀` (C1; its construction is DG-DATAOF/DG-COVER's, total `def`) | `rfl` | DG-DATAOF/SEM |
| `ordCallees` | `ordCallees` of `[M5]` §2.1 | `rfl` | DG-SEM |
| `genSem` | `genSem` of `[M5]` §2.1 / P11-P12 | `rfl` | DG-SEM, unbuilt |
| `mem_ordCallees` | a one-line lemma on the filter in `[M5]` §2.1 (`List.mem_filter`, `List.mem_finRange`) | proved when `ordCallees` exists | DG-SEM (or this unit, if DG-SEM prefers; Q2) |
| `genData₀_dataOf` | `GenData.hshape`/`hdata` (`[M5]` R7 fields) | by `GenData` fields | DG-DATAOF/SEM |
| `genSem_local` | rev2 §7 `genSemI_local`/`genSem_local` (P7) | DG-SEM states and proves, DG-ACC consumes | DG-SEM |
| `genSem_decl`, `genSem_d` | request to DG-SEM (Q1) | by cases on the arm | DG-SEM |
| `GeneratedAtK` (§4, def here) | `GeneratedAt` of `[M5]` §2.1 | **`Iff.rfl`/`rfl`** (§4 states it) | DG-SEM |

## 3. (A) DG-ASSIGN — full types

```lean
variable {env₀ : Environment} (K : AssignKit ι dom env₀)

/-- C1. The entry constant of `X` exactly as `T1Hyp.defines`/the run reads it. -/
def entry₀ (env₀ : Environment) (X : Name) : Option ConstantInfo :=
  (env₀.find? X).map fun ci =>
    entryConst true false [] ci (instancePredicate env₀) (userInliner env₀) (structEnv env₀)

/-- C1. The reader data of `X`'s entry. (`dataOf₀` uses the kit's `dataOf`.) -/
def dataOf₀ (X : Name) : Option MachineData :=
  (entry₀ env₀ X).bind fun E => (machineShape? false [] E (structEnv env₀)).bind (K.dataOf E (structEnv env₀))

theorem dataOf₀_of_genData₀ {X E g} (hE : entry₀ env₀ X = some E) (hg : K.genData₀ E = some g) :
    dataOf₀ K X = some (K.dOf g)                                  -- from K.genData₀_dataOf; `simp [dataOf₀, hE]`

/-- C2. Static call edge: ordinary (non-memory-origin) instances only. -/
def CallEdge (X c : Name) : Prop :=
  ∃ d, dataOf₀ K X = some d ∧ ∃ k, ∃ hk : k < d.shape.insts.length,
    (d.shape.instOrigins.getD k .ord).child? = none ∧ (d.shape.insts[k]'hk).1 = c

theorem callEdge_of_ord {X E g} (hE : entry₀ env₀ X = some E) (hg : K.genData₀ E = some g) :
    ∀ k ∈ K.ordCallees (K.dOf g), CallEdge K X ((K.dOf g).shape.insts[k]).1
-- dataOf₀_of_genData₀ + K.mem_ordCallees (the `Fin` index gives `hk`).

/-- `R c X := CallEdge X c`: `Acc R X` means every ordinary static callee chain below `X` is well-founded. -/
abbrev CallRel : Name → Name → Prop := flip (CallEdge K)
```

### 3.1 `genS` (C3: `Acc.rec`, callee-restricted `Q`, strict) — and why unfolding is propositional

```lean
open Classical in
/-- The step at `X` given the direct callees' values. `Qx c := if h : CallEdge K X c then ih c h else none`
(NOT `genS` outside the direct callees: the construction never reads it). Strict: every ordinary callee is `some`. -/
noncomputable def genStep (X : Name) (ih : ∀ c, CallEdge K X c → Option (SemPkg ι dom)) : Option (SemPkg ι dom) :=
  let Qx : Name → Option (SemPkg ι dom) := fun c => if h : CallEdge K X c then ih c h else none
  match entry₀ env₀ X with
  | none => none
  | some E =>
    match K.genData₀ E with
    | none => none
    | some g =>
      if ∀ k ∈ K.ordCallees (K.dOf g), (Qx ((K.dOf g).shape.insts[k]).1).isSome
      then some (K.genSem Qx X g) else none

/-- Acc.rec, with `motive := fun _ _ => Option (SemPkg ι dom)`. -/
noncomputable def genSAcc : ∀ X, Acc (CallRel K) X → Option (SemPkg ι dom) :=
  fun X h => Acc.rec (motive := fun _ _ => Option (SemPkg ι dom)) (fun X _ ih => genStep K X (fun c hc => ih c hc)) h

open Classical in
noncomputable def genS (X : Name) : Option (SemPkg ι dom) := if h : Acc (CallRel K) X then genSAcc K X h else none

theorem genSAcc_intro (X) (hs : ∀ y, CallRel K y X → Acc (CallRel K) y) :
    genSAcc K X (Acc.intro X hs) = genStep K X (fun c hc => genSAcc K c (hs c hc))       -- `rfl`
theorem genSAcc_irrel (X) (h h' : Acc (CallRel K) X) : genSAcc K X h = genSAcc K X h'    -- proof irrelevance
theorem genS_of_acc (X) (h : Acc (CallRel K) X) : genS K X = genSAcc K X h               -- `dif_pos`
theorem genS_of_not_acc (X) (h : ¬ Acc (CallRel K) X) : genS K X = none                  -- `dif_neg`
theorem genS_step (X) (h : Acc (CallRel K) X) :
    genS K X = genStep K X (fun c _ => genS K c)                                         -- Acc.inv + genSAcc_irrel
```
**Why a lemma and not `rfl`:** `Acc.rec` reduces only on a literal `Acc.intro`; for an arbitrary proof `h` the unfolding is obtained by `cases h`
(large elimination into data is allowed for `Acc`) and `genSAcc_irrel`. This route is the audit target of the TYPE check, not an assumption.

```lean
theorem genS_unfold {X E g} (hacc : Acc (CallRel K) X) (hE : entry₀ env₀ X = some E) (hg : K.genData₀ E = some g) :
    genS K X =
      if (∀ k ∈ K.ordCallees (K.dOf g), (genS K ((K.dOf g).shape.insts[k]).1).isSome)
      then some (K.genSem (genS K) X g) else none
```
Proof: `genS_step`; unfold `genStep` at `hE`, `hg`; **(i)** `Qx c = genS K c` for every direct callee `c` (`dif_pos`), so the `isSome` guard agrees by
`callEdge_of_ord`; **(ii)** `K.genSem Qx X g = K.genSem (genS K) X g` by `K.genSem_local` with the same `(i)` (`hQ` only asks the ordinary callees).

```lean
theorem genS_some_inv {X s} (hs : genS K X = some s) :
    ∃ (E : ConstantInfo) (g : K.GD E), entry₀ env₀ X = some E ∧ K.genData₀ E = some g ∧ Acc (CallRel K) X ∧
      (∀ k ∈ K.ordCallees (K.dOf g), ∃ sc, genS K ((K.dOf g).shape.insts[k]).1 = some sc) ∧
      s = K.genSem (genS K) X g
```
Proof: `by_cases Acc` (`none` otherwise contradicts `hs`); case-split `entry₀`/`genData₀`/guard via `genS_step`; `isSome` ⇒ `∃ sc`; `genS_unfold`.
**Overlap with DG-SEM (rev2 §7):** DG-SEM owns `genS_some_inv_of_unfold`, abstract in `G` and `hunf`. This unit's `genS_some_inv` is its instance at
`G := genS K`, `hunf := genS_unfold`; the proof body may be a one-line `genS_some_inv_of_unfold` call once that exists (Q2), else proved directly here
(same text; no second statement is exported to DG-SEM).

## 4. (B) DG-GENP — self-consistency (C5-C6)

`genS_facts` is **not** proved here. It is a *premise form*, the result of DG-FACTS/DG-CAUSAL (`genFacts`, `genSem_srcCausal`, `genS_srcCausal_acc`):

```lean
/-- INTERMEDIATE FORM: the facts supply, as one named premise. Producer: DG-FACTS + DG-CAUSAL (`genFacts` + `genS_srcCausal`); not this unit. -/
def GenSFacts : Prop := ∀ X s, genS K X = some s → FactsOf s

noncomputable def genP (hF : GenSFacts K) (X : Name) : Option (Pkg ι dom) :=
  match h : genS K X with
  | some s => some (genPkg s (hF X s h))
  | none => none

theorem semOf_genP (hF : GenSFacts K) : semOf (genP K hF) = genS K        -- funext; cases `genS K X`; `toSem_genPkg`

/-- `GeneratedAt` of [M5] §2.1 at the kit (replacement: `Iff.rfl` against DG-SEM's `GeneratedAt`). -/
def GeneratedAtK (P : Pkgs ι dom) (X : Name) (E : ConstantInfo) (p : Pkg ι dom) : Prop :=
  ∃ g : K.GD E, p.toSem = K.genSem (semOf P) X g

theorem genP_generated (hF : GenSFacts K) {X p} (hp : genP K hF X = some p) :
    ∃ E, entry₀ env₀ X = some E ∧ GeneratedAtK K (genP K hF) X E p
```
Proof: `semOf_genP` turns `hp` into `genS K X = some p.toSem`; `genS_some_inv` gives `E g`, `p.toSem = K.genSem (genS K) X g`, and `genS K = semOf (genP K hF)`
rewrites it to `K.genSem (semOf (genP K hF)) X g`.
`GeneratedAtK` carries the evidence `g` (the reader's actual data) inside; nothing is quantified over an arbitrary `d`.

Derived pure facts used by §6 (all from `genS_some_inv`, `genSem_d`, `genSem_decl`):
```lean
theorem genP_decl (hF) (hp : genP K hF X = some p) : p.decl = X
theorem genP_d_edges (hF) (hp : genP K hF X = some p) : ∃ d, dataOf₀ K X = some d ∧ p.d = d
```

## 5. (C) DG-ACC — `CacheAcc`, `acc_of_run`

### 5.1 `CacheAcc` (restricted to `Reach`, as `CacheShips`; the [REACH] §3.4 recommendation)
```lean
open Tools.ShippingChildBndCore (cv dv)
open Tools.ShippingChildInv (Res)
def CacheAcc (Reach : Name → Prop) (m : Std.HashMap Name Res) : Prop :=
  ∀ c r, Reach c → m.get? c = some r → Acc (CallRel K) c

/-- Mirror of `cacheShips_insert` (KeepChild:255): an unreached key needs nothing. -/
theorem cacheAcc_insert {Reach m n r} (h : CacheAcc K Reach m) (hr : Reach n → Acc (CallRel K) n) :
    CacheAcc K Reach (m.insert n r)
theorem cacheAcc_empty (Reach) : CacheAcc K Reach {}
```
Restriction to `Reach` is deliberate: translator-internal calls and route 4/5 children cache names outside the static `insts` ([REACH] §2, §3.4); an unrestricted
`CacheAcc` would need "every cached key is reached", for which this investigation found no supplier (not claimed false).

### 5.2 The invariant and the one-level statements (mirrors of `IHAt`/`ChildKeepsInv`/`KeepChildStmt`/`ServedShips0Stmt`, conclusion `Acc`)
```lean
open Tools.ShippingChildCacheA (JQC RealChildA)
def AccInvAt {mref cref} (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) : Void IO.RealWorld → Prop :=
  fun w => JQC L.O D w ∧ CacheAcc K Reach (cv w)

/-- success half at depth `D`: every successful run of a REACHED name's entry from an `AccInvAt D` world has `Acc`. -/
def AccIHAt {mref cref} (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) : Prop :=
  ∀ c, Reach c → ∀ mctx cctx (u u' : Void IO.RealWorld) (r : Res), AdmCtx L.O.quiet mctx cctx → AccInvAt K L Reach D u →
    RunsTo (synthesizeCombinational c) mctx mref cctx cref u r u' → Acc (CallRel K) c

/-- all-outcome keep of the child entry (generic in the invariant: `ChildSynthA`, ChildFrontCP:240, takes `I`). -/
def AccChildKeeps {mref cref} (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) : Prop :=
  Tools.ShippingChildFrontCP.ChildSynthA L.O (AccInvAt K L Reach D)

/-- G-KEEP-CHILD for `Acc` (mirror of `KeepChildStmt`; the insertion of a REACHED name's result uses `AccIHAt` of that run + `cacheAcc_insert`). -/
def AccKeepChildStmt {mref cref} (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ D, 1 ≤ D → (D < sparkleSynthDepthLimit → AccBodyKeeps K L Reach (D + 1)) → AccIHAt K L Reach D → AccChildKeeps K L Reach D
-- AccBodyKeeps := `BodyKeepsInv` with `InvAt` replaced by `AccInvAt` (same text, `Keeps … (AccInvAt …)`).

/-- THE G-REACH INPUT, exact (named premise; mirror of `ServedShips0Stmt`). In a successful run of a reached `X` from an
`AccInvAt (dv w)` world, under both halves one level deeper, EVERY static ordinary callee of `X` is `Acc`:
the static edge `X → c` is served either by a nested successful run of `c`'s entry one level deeper (`AccIHAt (dv w + 1)`) or by a
cache hit (`CacheAcc` of the serving world); the match "static edge = served callee" is [REACH] S3 (`childrenShips_reached`
with `RealChildA (insts[k]).1 y`) composed with `T1Hyp.defines` (`shape = q.d.shape`, [REACH] §2). -/
def AccServedStmt {mref cref} (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ X, Reach X → ∀ mctx cctx (w w' : Void IO.RealWorld) (r : Res), AdmCtx L.O.quiet mctx cctx →
    AccInvAt K L Reach (dv w) w → AccIHAt K L Reach (dv w + 1) → AccChildKeeps K L Reach (dv w + 1) →
    RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w r w' →
    ∀ c, CallEdge K X c → Acc (CallRel K) c
```
(`dv w` and `JQ`'s `dv w = D` field: `JQ quiet D w := quiet w ∧ sv w = some synthesizeChild ∧ dv w = D`, ChildVCA:53 `[S]`.)

### 5.3 `acc_of_run` (proved from the premises; the induction is `ih_allPF`'s shape, on `sparkleSynthDepthLimit − D`)
```lean
theorem accIHAt_limit {L Reach D} (hL : LimitStmt L) (hD : sparkleSynthDepthLimit ≤ D) : AccIHAt K L Reach D     -- copy of ihAt_limit

theorem accIHAt_step {L Reach} (hS : AccServedStmt K L Reach) (D : Nat) :
    AccIHAt K L Reach (D + 1) → AccChildKeeps K L Reach (D + 1) → AccIHAt K L Reach D
-- intro c hc mctx cctx u u' r hA hu hr; RunsTo (synthesizeCombinational c) ⇒ the core run (designTop, as ihAt_stepPF);
-- hS gives ∀ c', CallEdge K c c' → Acc; `Acc.intro c` (CallRel K c' c := CallEdge K c c').

theorem acc_of_run {L Reach} (hLim : LimitStmt L) (hS : AccServedStmt K L Reach) (hKC : AccKeepChildStmt K L Reach) :
    ∀ D, 1 ≤ D → AccIHAt K L Reach D ∧ AccChildKeeps K L Reach D
-- exactly ih_allPF's `key`: zero: accIHAt_limit + hKC; succ: accIHAt_step with the IH at D+1, hKC D.
```
The top-level use (not a separate theorem here): the outermost run starts at `dv w = 0` with an empty cache, `AccInvAt K L Reach 0 w` follows from `JQC L.O 0 w` and `cacheAcc_empty`
(T1's top-level shape, `t1_of_stepPF`: `hj0.1.2.2 : dv w = 0`; the cache disjunct `dv w = 0 ∨ …` becomes `cv w = {}`-or-`CacheAcc`, **to be fixed
exactly at implementation against `ServedShips0Stmt`'s `dv w = 0 ∨ CacheShips`; if the start world has a non-empty cache (not excluded by `JQC L.O 0 w`),
the top-level start needs `CacheAcc` as a premise — recorded, not assumed away**).

### 5.4 The cases of the induction, and where each input comes from (the "real-call-edge" supply path)

| case in `accIHAt_step` for the edge `X → c` | what is needed | supplier today |
|---|---|---|
| nested run | the callee is run one level deeper, `dv = D+1`, from an `AccInvAt (D+1)` world, and the run returns `r` | `AccServedStmt` (G-REACH S3: `RealChildA (insts[k]).1 y` is `.run … hr : RunsTo (synthesizeCombinational c) …`); `AccIHAt (D+1)`; world invariant along the closing = `AccChildKeeps (D+1)` |
| cache hit | `(cv u).get? c = some r'` at the serving world `u`, `Reach c`; `Acc c` from `CacheAcc` | `CacheAcc` at `u` ← keeps through the run: `AccBodyKeeps`/`AccChildKeeps` |
| `Reach c` for the served callee | `closed` of `T1Hyp` for the package of `X` (`P := genP`), i.e. §6; or `Reach := ReachFrom`/`ReachEdge` | [REACH] S1/S2 (design only); §6 |
| insertion of `X` (own result) keeps `CacheAcc` | `Reach X → Acc X`: the result of the run whose `Acc` we are proving, available by `AccIHAt` of that nested run | `cacheAcc_insert` (pure, §5.1) |
| depth ≥ limit | run does not return | `limitStmt_proved` (proved, `[B]`) |
| memory-origin entries | not `CallEdge`; origin-built, no cache entry | not needed (`child? = some`) |
| translator-internal calls (inlined/hardware_module callee met in the body) | would cache names outside `insts`; unconstrained because `CacheAcc` is on `Reach` | nothing needed (restriction to `Reach`); that route 3 makes none is `hrows`/P3 (unsupplied), separate |

**What is real and what is premise:** the induction skeleton, the limit base, `cacheAcc_insert`, the `Acc.intro` assembly are real Lean. `AccServedStmt` and
`AccKeepChildStmt` are the exact analogues of `ServedShips0Stmt` and `KeepChildStmt`/`KeepBodyStmt` (each is hundreds of lines of translator-run analysis
in M3: ServedRun.lean, ChildPinC/KeepChild). **Whether their analogues for `Acc` are routine copies, or can be obtained from the shipped statements by a
generic transport (invariant-parametric `Keeps` lemmas, `ChildSynthA` is already generic in `I`), is the main open question (Q3).** Counting the abstract
Acc lemma alone as "ACC supplied" would be wrong; it is not counted.

## 6. (D) DG-PKGASSIGN — `T1Hyp.pkg`/`closed` for `P := genP`

Fix `hF : GenSFacts K`, `P := genP K hF`.

```lean
/-- The least CallEdge-closed `Reach` over a top predicate (pure; the `Reach := ReachFrom P Top` of [REACH] S1, here over static edges directly). -/
inductive ReachEdge (Top : Name → Prop) : Name → Prop
  | top {c} : Top c → ReachEdge Top c
  | edge {X c} : ReachEdge Top X → CallEdge K X c → ReachEdge Top c

/-- COVERAGE premise (DG-COVER + DG-WFCOVER + DG-ENV), exact: every name of `Reach` has an entry and reader data with `GenWF`. -/
def CoverAt (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∃ E g, entry₀ env₀ c = some E ∧ K.genData₀ E = some g

/-- (pure) strictness closes: the ordinary callees of reached names are reached, so `genS` exists on all of `Reach`. -/
theorem genS_isSome_of_cover {Reach} (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c) (hacc : ∀ c, Reach c → Acc (CallRel K) c)
    (hcov : CoverAt K Reach) : ∀ c, Reach c → ∃ s, genS K c = some s
-- Acc.rec on `hacc c`: genS_unfold; the guard holds by IH at each ordinary callee (callEdge_of_ord, hcl); `genSem` is `some`.

theorem genP_pkg {Reach DataOk} (hF) (hcl) (hacc) (hcov)
    (hOk : ∀ c, Reach c → ∀ q, genP K hF c = some q → DataOk q) :
    ∀ c, Reach c → ∃ q, genP K hF c = some q ∧ q.decl = c ∧ DataOk q                  -- = T1Hyp.pkg's type for P := genP K hF

theorem genP_closed {Reach} (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c) :
    ∀ c, Reach c → ∀ q, genP K hF c = some q → ∀ k (hk : k < q.d.shape.insts.length),
      (q.d.shape.instOrigins.getD k .ord).child? = none → Reach (q.d.shape.insts[k]).1  -- = T1Hyp.closed's type; genP_d_edges
```
Their conjunction is exactly the `pkg` and `closed` fields of `T1Hyp`/`T1HypND` at `P := genP K hF` (checked by TYPE against the field types, not by `T1Hyp`
construction, since `defines/closes/dec` are other units' fields: G3-SHAPE, G-CLOSES, G-CALLDEC).

**Supply path (the ACC+COVER+WFCOVER composition requested):**
1. `Reach := ReachEdge K Top`; `hcl` is the constructor `edge` (pure).
2. `hacc`: `acc_of_run` (§5.3, conditional) gives `Acc` for names of successful runs; each `c ∈ ReachEdge Top` is the root, or a CallEdge-successor of one,
   i.e. a callee served by the run of its parent (the §5.4 table), whose `Acc` is the premise.
3. `hcov`: DG-COVER's "every successful run gives `dataOf`/`GenWF`" (+ DG-ENV C0 for `entry₀`), at each name of `Reach` — **only for names that a successful run
   reaches**. That every `ReachEdge` name is such a name is the same G-REACH match as step 2. Not supplied.
4. `hOk`: DG-COVER/WFCOVER (`DataOk` is U0's placeholder; no unit may instantiate it so a statement becomes vacuous).
5. `GenSFacts K`: DG-FACTS/CAUSAL.
No step is claimed supplied; steps 2-5 are named premises with the owners above.

## 7. Audit plan (TYPE / MUTANT / AXIOMS / CLOSURE) for `Tests/Gen5/AccCheck.lean`

* **TYPE.** Independently-written `Expected…` statements (not by unfolding) for: `genS_unfold`, `genS_some_inv`, `genStep`'s guard shape, `callEdge_of_ord`,
  `semOf_genP`, `genP_generated`, `cacheAcc_insert`, `accIHAt_limit`, `acc_of_run`, `genS_isSome_of_cover`, `genP_pkg`, `genP_closed`; plus the definitions
  `CacheAcc`, `AccServedStmt`, `CallEdge` compared to `Prop`-typed independent re-statements (`example : T = T' := rfl`).
  `genP_pkg`/`genP_closed` are additionally compared against the *field types* of `T1Hyp.pkg`/`closed` at `P := genP K hF` (`example : (∀ c, …) = (…) := rfl` via
  `T1Hyp.pkg`'s `fun H => H.pkg` type ascription).
* **MUTANT** (well-typed, one point changed; rejected by signature / defeq, **not** semantic counterexamples): (a) `genStep` without the strictness guard;
  (b) `Qx` replaced by the global `genS` (the unrestricted form); (c) `CallEdge` without `child? = none` (memory entries become edges); (d) `CacheAcc` without the
  `Reach c →` antecedent; (e) `genS_unfold` with `genSem Qx` (not `genS K`); (f) `acc_of_run` without `hLim`; (g) `genP` ignoring `hF` (using a fixed fact);
  (h) `genP_closed` without `child? = none`.
* **AXIOMS.** `Lean.collectAxioms` on every theorem: only `propext`, `Classical.choice`, `Quot.sound` (the `classical` splits in `genS`/`genStep`); no `sorryAx`.
* **CLOSURE.** No `sorryAx` in any collected axiom list; the `AssignKit` fields appear only as hypotheses (`K`), never as `axiom`/`opaque` constants;
  `AccServedStmt`/`AccKeepChildStmt`/`GenSFacts`/`CoverAt` appear only as binders.
* **Vacuity witnesses** (honest scope): a *concrete* `AssignKit` (e.g. `GD := fun _ => Unit`, a constant `dataOf`, an `genSem` returning a fixed `SemPkg` from a
  fixed `Q`-independent value) on which `genS` is `some` at one name and `none` at a name with a self-edge, to show the statements are neither trivially true
  nor trivially false. This witness is a test of the statements, **not** of the real DG-SEM/DG-DATAOF.

## 8. Units, order, and the delivery gates

| unit | content | needs | state after |
|---|---|---|---|
| **A1 (pure, kit only)** | `AssignKit`, `entry₀`, `dataOf₀`, `CallEdge`, `callEdge_of_ord`, `genStep`, `genSAcc`, `genS`, `genSAcc_irrel`, `genS_step`, `genS_unfold`, `genS_some_inv` | imports `Tools.ShippingGen5SemPkg`, `Sparkle.Compiler.Elab` (for `entryConst`, `machineShape?`) | proved + checked at the kit; not DG-SEM's real `genSem` |
| **A2 (pure)** | `CacheAcc`, `cacheAcc_insert`, `cacheAcc_empty`, `ReachEdge`, `genS_isSome_of_cover` | A1; `Tools.ShippingGen2Defs` (`Res` via `ShippingChildInv`) | proved + checked |
| **A3 (conditional on `GenSFacts`)** | `GenSFacts`, `genP`, `semOf_genP`, `GeneratedAtK`, `genP_generated`, `genP_decl`, `genP_d_edges`, `genP_pkg`, `genP_closed` | A1, A2, `Tools.ShippingGen5SemPkg` | proved; conditional on named premises |
| **A4 (conditional on `AccServedStmt`, `AccKeepChildStmt`)** | `AccInvAt`, `AccIHAt`, `AccChildKeeps`, `AccBodyKeeps`, `accIHAt_limit`, `accIHAt_step`, `acc_of_run` | A2; `Tools.ShippingGen2T1` (`LimitStmt`), `Tools.ShippingGen5T1ND`, `ChildFrontCP` | proved; conditional (Q3) |
| A5 (not started) | producers of `AccServedStmt`, `AccKeepChildStmt` | G-REACH Lean (S1-S3), translator-run analysis | **unsupplied** |
| A6 (waits) | replacement of every kit field by the owner's constant; `Iff.rfl` check of `GeneratedAtK` | DG-SEM P11/P12, DG-DATAOF built | waits |

Files: `Tools/ShippingGen5Acc.lean` (A1-A4), `Tests/Gen5/AccCheck.lean`; `lakefile.lean`: two `lean_lib` entries. After approval, A1-A2 first (no dependence on any
unbuilt owner), A3-A4 as the same file's second half. Builds in the Pod, one target at a time, SHA recorded as a comment-only commit; per the brief the
Lean-containing commit stays `doing` with "clean build is the coder's".

## 9. Questions for the reviewer (decisions that change the Lean)

* **Q1 (DG-SEM request).** DG-SEM to add `genSem_decl`/`genSem_d` (both definitional for `genSemGenE`; `.comb` is `[F]`). Without them, `genP_pkg`'s `q.decl = c` and `genP_closed` need another supplier.
* **Q2 (overlap).** `mem_ordCallees` and `genS_some_inv`: proved here (A1) or taken from DG-SEM when it exists? Default: here, as the kit's spec field and the instance of `genS_some_inv_of_unfold`; no change of ownership.
* **Q3 (cost/shape of `AccServedStmt`/`AccKeepChildStmt`).** (a) copy the M3 machinery for `AccInvAt` (large, mechanical); (b) a generic transport "any invariant `I` that is a `JQC`-conjunct and a `Reach`-restricted cache predicate preserved by `m.insert n r` given `Reach n → φ n`" — needs an `I`-generic `BodyKeeps`/`KeepChild`, which M3's files are not (they are `InvAt`-specific, and editing them is forbidden); (c) strengthen `CacheShips`' payload to include `Acc` — a shared-definition change, **forbidden without user approval**. Recommendation: (a), scoped as its own issue after A1-A3, because only A4 depends on it. Reversible (it is additive Lean). If not decided, A1-A3 proceed and `acc_of_run` stays conditional.
* **Q4 (top-level start world).** `JQC L.O 0 w` does not by itself give `CacheAcc … (cv w)` (non-empty start cache is not excluded). Is the premise "start cache is empty / `CacheAcc`" to be recorded as a top-level hypothesis of FG, or is it already supplied by the start-world invariant (`dv w = 0 ∨ CacheShips`)? Recorded in §5.3; no change made.

## 10. Not claimed / open

* No Lean was elaborated for this document; every proof sketch is untested. The kit is a design, with `GD : Type` and `genSem` as parameters: that a `GenData`-typed
  `genSem` fits the signature `(Q) (X) {E} (g : GD E)` is DGEN §2.1's text, not a built fact.
* `AccServedStmt`, `AccKeepChildStmt`, `GenSFacts`, `CoverAt`, `ReadsAt`-coverage have no producer in this investigation. DG-ACC is **not** done when A4's `acc_of_run` is
  proved; it is done only when those premises are discharged for real runs.
* The condition "route 3 makes no translator-internal child call" ([REACH] §3.4) is not used and not supplied; `CacheAcc` is on `Reach` to avoid needing it.
* No change to FG, T1/T1HypND, a law, a TRUSTED boundary, or the compiler.
