# G-POST: (A) transport under the full entry's design map vs (B) `InstClosed` in `ShipsRes` (FOR REVIEW)

- **Issue:** `sparkle-gen3-post`. **Branch:** `par/gen3-induct`, base f7fb323c.
- **Status:** read-only comparison plus one pure Lean file, `Tools/ShippingGen2InstKeep.lean`. The file is NOT BUILT
  and is not in the lakefile. No Defs change.
- **Context:** KEEPCHILD_POST_FREEZE.md §A (the `NoTopStmt` stop-report). The step-7 risk named there is settled below
  (§0): it holds, so there is no stop.

## 0. Step 7 (post-pass preservation): HOLDS, written as Lean (not built)

`Tools/ShippingGen2InstKeep.lean`, namespace `Tools.ShippingGen2InstKeep`. It is pure and imports only
`Sparkle.IR.ZeroWidth` and `Tools.ShippingMergeKeepsBridge`, not the Defs.

| lemma | statement (target occurrence only; connections rewritten) | uses |
|---|---|---|
| `dzStmt_inst` | `dzStmt wm (inst n i cs) = some (inst n i (cs.map …))`, by `rfl` | ZeroWidth.lean:91, `.inst` arm :102 |
| `inst_target_dropZW` | `(∃ i cs, inst n i cs ∈ m.body) → ∃ i cs, inst n i cs ∈ (dropZeroWidthModule m).body` | `dropZeroWidthModule` :113 (both branches of `allConcrete`), `List.mem_filterMap` |
| `rewriteStmt_inst` | `rewriteStmt s (inst …) = mapStmtExprs (renameRefs s) (inst …)`, by `rfl` (`definedNode (inst …) = none`, RegDedup.lean:64-74) | ShippingMergeKeeps.lean:647; Optimize.lean:691 (only the conns change) |
| `inst_target_rewrite` | the instance occurrence is kept by `body.map (rewriteStmt s)` | `List.mem_map` |
| `parts_shape` (copy) | `(mergeDuplicatesParts m).1 = m.body ∨ ∃ s, … = m.body.map (rewriteStmt s)` | copy of ShippingSrm17Body.lean:221, via `parts_eq_model` (MergeKeepsBridge:254), `model_eq_rec` (:282), `partsRec`/`afterClasses`/`finish` (MergeKeeps:786/779/669) |
| `mergeDuplicates_body` (copy) | `(mergeDuplicates X).body = X.body ∨ = (mergeDuplicatesParts X).1` | copy of ShippingSrm17Body.lean:210; RegDedup.lean:305 |
| `inst_target_mergeDuplicates`, `inst_target_mergeChecked` | the same, for `mergeDuplicates` and then `mergeChecked` | `mergeChecked_cases` (RefineCheck.lean:280) |
| `inst_target_post`, `inst_target_full` | for `mergeChecked (dropZeroWidthModule m)`, and for the disjunction `b = dropZW raw ∨ b = mergeChecked (dropZW raw)` that StepStmt and `fullEntry_name` use | Elab.lean:5600-5606 |

**Why no instance is deleted.** The merge body is one of two things:
- `m.body` itself (the early returns and the validator fall-backs);
- `m.body.map (rewriteStmt s)`, which is a `map`, not a `filter`. An instance has no defining node, so it takes the
  `mapStmtExprs` arm. That arm keeps the module name and the instance name, and renames only the connection
  expressions.

`dzStmt` returns `some` on `.inst`. The two copies are kept local so that this file does not import the SRM17 chain
(ShippingKidsResetSat …). The originals are BUILT, so the copies should elaborate verbatim.

## 1. (A) Transport under the design map: NOT available as a transport

**The map.** `synthesizeCombinationalWith` (Elab.lean:5592-5606) returns
`D' := top f D`, where `top f D := {D with modules := D.modules.map (fun x => if x.name == m.name then f x else x)}`
and `f` is `dropZeroWidthModule`, then (unless `SPARKLE_NO_REGDEDUP` is set) `mergeChecked`.
`synthesizeCombinational_designTop` (ShippingDesignWriterRun.lean:69) exports only the identity case,
`(∀ x ∈ D.modules, x.name ≠ M.name) → D'.modules = D.modules`. Only modules named like the top change, and `f` keeps
names (`dropZeroWidth_name`, `mergeChecked_name`; `fullEntry_name` :116).

**What `ihAt_step` (Gen2T1.lean:162-186) needs.** It needs `ChildShips q n M' D'` from StepStmt's
`ChildShips q n M' D` (core design `D`). `ChildShips` (Defs:87) is
`∀ dsn, (∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g) → moduleByName dsn.modules mc.name = some mc → …`.
It is antitone in `Dc`: from `ChildShips … D`, you get `ChildShips … D'` exactly when every `dsn` that contains `D'`
and `M'` also contains `D`.

**The case the map matters for.** Let `x ∈ D` have `x.name = M.name`. Then `D'` has `f x` at that name, and
`M'.name = M.name`. `moduleByName` is a function (`List.find?`, Machine.lean:359), so:
- `ChildShips q n M' D` has a usable `dsn` only if `x = M'`. Otherwise **it is vacuous**: no `dsn` finds both `x` and
  `M'` under one name.
- `ChildShips q n M' D'` has content only if `f x = M'`, for example `x = raw`, since `M' = f raw` uses the same branch
  of the environment variable.
- So in exactly the case where the map changes something, the source statement is vacuous and the target is not. No
  transport from `ChildShips … D` can give it. **(A) is impossible as a congruence or transport lemma**, whatever the
  map's "only top-named modules" property. The `∀ dsn ⊇ Dc` quantifier does not help: it fixes `dsn ⊇ D'`, which
  already contains `M'` at the contested name.

**What (A) would have to become instead.** Restate StepStmt so that it concludes `ChildShips` at `D'` directly, and
prove inside StepStmt that the top-named `x ∈ D` is never read by the child run (a dead-module frame lemma).
- **Run-locality frame (missing).** Such a lemma needs run locality: `RunOn`/`KSn` over `childMap dsn.modules` read
  only the names reachable by instance edges from `mc`. Nothing like this exists.
- **Reachability, not one incoming edge.** It also needs "`x.name` is not reachable from `M'` in `dsn`". That is a
  reachability fact. A per-module incoming-edge property is not enough: a dead cycle `g1 ↔ g2` has incoming edges and
  is unreachable.
- **Net effect.** This changes StepStmt, a frozen M2 statement with four built producers. It needs a new semantic
  frame lemma and a reachability invariant, which is strictly more than (B).

## 2. (B) `InstClosed` in `ShipsRes` (with `NoTopStmt'` of KEEPCHILD_POST_FREEZE §A(a))

### 2.1 Complete type
```lean
/-- every module of the result's design has an instantiating statement in the result
(its top or one of its design's modules); an incoming-edge property per module, NOT reachability -/
def InstClosed (r : Res) : Prop :=
  ∀ g ∈ r.2.modules, ∃ h ∈ r.1 :: r.2.modules, ∃ (i : String) (cs : List (String × Expr)),
    Stmt.inst g.name i cs ∈ h.body

def ShipsRes {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (c : Name) (r : Res) : Prop :=
  RealChildA L.O c r ∧ (∃ q n, P c = some q ∧ q.decl = c ∧ ChildShips q n r.1 r.2) ∧ InstClosed r
```
- **Placement.** Add `InstClosed` as a new THIRD conjunct, not appended inside the existential. Then `h.1` still works
  (`shipsRes_real`, Gen2Connect.lean:86), and so does `h.2.1`. Any existing `h.2` that expects the `∃` must become
  `h.2.1`; grep finds no such use outside `ihAt_step`'s anonymous constructor (Gen2T1.lean:186).
- **Old to new.** `ShipsResOld r := RealChildA ∧ ∃ …` is recovered by `⟨h.1, h.2.1⟩`.
- **No Defs change here.** This is a proposal. An alternative that needs no Defs change, a side invariant, is in §2.8.

### 2.2 Projection to the old `ShipsRes`
`shipsRes_old : ShipsRes' L P c r → ShipsRes L P c r := fun h => ⟨h.1, h.2.1⟩`.

`ServedP Q` (Defs:235) is monotone in `Q`: `Q` occurs only in the right disjunct, positively. So
`ServedP (ShipsRes') → ServedP (ShipsRes)` follows by `machineTraceLBX_mono` (Gen2Connect.lean:47) plus a
`servedP_mono`, which is not yet written and is a few lines.

### 2.3 StepStmt's extra conclusion: none is needed (a correction to the freeze §A(b))
- StepStmt (Defs:293) has `ShipsRes` only in its PREMISE, inside `ServedP`. Strengthening it makes StepStmt weaker,
  so the old statement implies the new one by `servedP_mono`.
- StepStmt's conclusion is `TopShips ∧ ChildShips` over the core design. It produces no `ShipsRes`, so StepStmt needs
  no `InstClosed` conclusion.
- `InstClosed` of a result is a STRUCTURAL fact of the run (the closing and the post-passes), not a fact about
  semantics. It is supplied in `ihAt_step` (§2.4), not by the producers.

### 2.4 How `ihAt_step` supplies `InstClosed` for its own result `(M', D')`
Order inside the step, with `T1Hyp`, `IHAt' (D+1)` and `ChildKeepsInv' (D+1)` in scope:
1. **Per-child results.** Freeze §A steps 1-2 (`machineRunInv_of_closes`, `synthesizeMachineCertified_runsInv` with
   KeepChild #13 at `D+1`): every non-memory child `k` of the run's `closeInstsG` children list is a returned
   `synthesizeChild` result of a REACHED name, so `ShipsRes' k`, hence `InstClosed k`. Reach comes from
   `T1Hyp.closed`, modulo G-REACH (§3).
2. **The run's closing facts.** Freeze §A steps 3-5:
   - `closedBody_kinds_of_run` (ClosedKinds.lean:162): `d₀.modules = []` and `m0.name = ofDecl c`;
   - `closeInstsG_name_design` (TopShareNoParent.lean:38): `D = designWith kids d₀`;
   - the `closeInstsG` checks (MachineInstG.lean:128-143), specifically:
     - every `k.1` and every `g ∈ k.2.modules` is found in `D` as itself (`moduleByName D.modules _ = some _`, so it is
       a member of `D`);
     - `noInstOfB m0.name body`;
     - `D.modules.all (noInstOfB m0.name ·.body)`;
     - every child is instantiated in the closed body, via `stmtsG` (:56-68), `callGroups` coverage and `isPermOf`
       (MISSING, freeze step 5).
   - The one-output `closeInsts` (Machine.lean:396-425) has the same checks; its analogue of
     `closeInstsG_name_design` is MISSING (freeze step 4).
3. **`NoTopStmt'` for this run.** Case split by `mem_designWith` (SharedLeafExt.lean:150):
   - `g = k.1`: it is instantiated in `body`, so `noInstOfB` gives `g.name ≠ m0.name`;
   - `g ∈ k.2.modules`: `InstClosed k` gives `h ∈ k.1 :: k.2.modules` instantiating `g.name`. Then `h ∈ D` by the
     "found as itself" check, so `noInstOfB m0.name h.body` gives `g.name ≠ m0.name`.
   - Memory children: `ofDecl_ne_ofMem`, or the same argument if their designs are non-empty (§3).

   Then `D'.modules = D.modules` (`synthesizeCombinational_designTop` + `map_other`, KidsChildIface.lean:44).
   Incoming-edge `InstClosed` is ENOUGH here: the argument never needs reachability.
4. **`InstClosed (M', D)`.** For `g ∈ D`:
   - `g = k.1`: there is an instance of `g.name` in `raw.body` (as in 3), and `inst_target_full`
     (InstKeep, this unit) moves it to `M'.body`. Take `h := M'`.
   - `g ∈ k.2.modules`: the `h` from `InstClosed k`, which is in `D` as itself (as in 3). Take `h ∈ D.modules`.

   With `D' = D` this is `InstClosed (M', D')`.
5. `ShipsRes'` is `⟨hreal, ⟨q, n, …⟩, step 4⟩`. The `ChildShips` part is as today, via `childShips_congr` and step 3.

### 2.5 Cache: initial state, hit, insert
- **Initial state.** At depth 0 the core entry clears `sparkleChildCache` (Elab:5536-5541). `Start` gives `JQC 0`, and
  `ServedShips0Stmt` already carries `dv w = 0 ∨ CacheShips`. `CacheShips'` of the empty map is trivial. Nothing is new.
- **Hit.** `CacheShips' (cv w)` gives `ShipsRes'` directly (KeepChild #10, hit branch). This is unchanged in form.
- **Insert.** KeepChild #8/#9 (`cacheShips_insert`, `invAt_insert_runs`, Gen2KeepChild.lean:255/272) take
  `Reach n → ShipsRes L P n r` as an argument and are generic in `ShipsRes`. With the Defs change the argument is
  `ShipsRes'`, supplied by `IHAt' D` at the run (#10 miss branch, KeepChild:319). The proof text is unchanged.

### 2.6 Producers: no new obligation
- `memParent_ships` (Gen2MemShips.lean:87), `leaf_ships` (Gen2Leaf.lean:271), `slotlessLeaf_ships`
  (par/gen2-spec: Gen2SlotlessLeaf.lean:438) and `gate_combChildRunN` (par/gen4-gate: Gen4GateLeaf.lean:221) all
  conclude `TopShips`/`ChildShips`/`ChildRunN` over the core design. None of them builds a `ShipsRes`. With (B) they
  are UNCHANGED.
- The freeze §A(b) says they "must supply it". That is not so if `InstClosed` is supplied in `ihAt_step` (§2.4).
- If instead one wants `InstClosed` from StepStmt (a new conclusion `InstClosed (b, D)`), then each producer must
  prove it from its own run:
  - leaves: `D.modules = []`, trivial;
  - memory parents: each memory submodule is instantiated in `raw.body`, then `inst_target_full`;
  - the step: §2.4.

  That route duplicates §2.4 four times. Not recommended.

### 2.7 Order (no circularity) and the negative-position classification
**Where `ShipsRes` occurs:**

| statement | occurrence | effect of the stronger `ShipsRes'` |
|---|---|---|
| `IHAt` (Defs:151) | conclusion (+) and inside `InvAt` hypothesis (−) | incomparable with the old one: neither implies the other |
| `CacheShips` / `InvAt` | inside the invariant (±; pre and post of `Keeps`) | the invariant is stronger; it is preserved iff every insert supplies `InstClosed` (§2.5): YES, generic |
| `BodyKeepsInv`/`ChildKeepsInv`/`KeepBodyStmt`/`KeepChildStmt` | the invariant `InvAt` | proofs are generic in the cache predicate (`stableA_invAt` reads only `cv`, Gen2Connect.lean:41; `keepBody`, Gen2Keep.lean:54); they re-elaborate unchanged |
| `ServedShipsStmt`/`ServedShips0Stmt` | premises `InvAt`, `IHAt`, `ChildKeepsInv` (−); conclusion `ServedP (ShipsRes)` (+) | must be re-proved at the stronger invariant, which is the same proof: hit/insert of the cache already go through `CacheShips`. The old one is NOT derivable from the new one |
| `StepStmt` | premise `ServedP (ShipsRes)` (−) | old ⇒ new by `servedP_mono`; COMPATIBLE |
| `T1Stmt` | no `ShipsRes` | the goal is unchanged |

**Classification.** Compatibility is not automatic for:
- `IHAt` and `InvAt`: incomparable;
- the G-SERVED statements: a new proof is needed, which is a textual copy.

It is automatic for:
- StepStmt and the producers: monotone, or untouched;
- KeepBody/KeepChild: generic.

There is no circularity, because the whole depth induction (`ih_all`) runs at the new invariant, and T1 uses only
`IHAt'` at depth 1 from a cleared cache.

**Order:**
1. Build this unit's `InstKeep`. It has no dependencies.
2. Approve the Defs change (`InstClosed` as the 3rd conjunct). Re-elaborate Defs/Connect/Keep/KeepChild unchanged, and
   fix `ihAt_step`'s constructor.
3. Freeze §A steps 1-2, shared with G-SERVED: per-child `ShipsRes'`.
4. Freeze §A steps 4-5: the `closeInstsG` facts (MISSING) and the one-output analogue.
5. `NoTopStmt'` for the run (§2.4 step 3). Step 6 of the freeze case split.
6. `InstClosed (M', D')` (§2.4 step 4). It uses `inst_target_full`.
7. `ihAt_step` at `ShipsRes'`; `servedP_mono` for StepStmt.

### 2.8 Variant without a Defs change: a side invariant
- **The variant.** `CacheIC Reach m := ∀ c r, Reach c → m.get? c = some r → InstClosed r`, carried next to `InvAt`, with
  an `ICAt D` success half beside `IHAt D`.
- **The cost.**
  - `KeepChild` (13 lemmas, written at `InvAt`) must be copied again at `InvAt ∧ CacheIC`;
  - `ServedShips0Stmt` must be restated;
  - `ihAt_step`/`ih_all` must carry two IHs.
- The mathematics is identical. The cost is about twice the proof text, and two parallel invariant families.

## 3. Uncertain spots
- **Lean not built.** `InstKeep` was written without elaboration:
  - `split` on the `dropZeroWidthModule` `ite`, and the `let wm` that `exact` must zeta-reduce;
  - `inst_target_rewrite` relies on unification assigning `cs'` through `rfl`. A `first` fallback with `simp only
    [mapStmtExprs]` is included.
  - The two copied lemmas are verbatim copies of BUILT ones. Add a `lean_lib «Tools.ShippingGen2InstKeep»` entry
    before building; that lakefile edit was not made.
- **Memory children's designs.** Whether a memory child (origin `child? = some md`) has `md.2.modules = []`, or else
  satisfies `InstClosed`, was not checked. Only `ofDecl_ne_ofMem` is cited for the name.
- **G-REACH.** "Every cached child of the run is a reached name" relies on `T1Hyp.closed` matching the translator's
  actual calls (the existing G-REACH gap). A non-reached cached child has no `InstClosed` from `CacheShips'`.
- **The core module and `closeInstsG`.** That `raw.body` is (a permutation of) the `closeInstsG` body, with no
  instance-dropping pass between `closeInstsG` and the core entry's return, was not re-read in this unit (freeze
  steps 3-5).
- **(A) frame lemma.** The impossibility in §1 is an argument about `ChildShips`'s quantifier and `find?`
  functionality, not a kernel counterexample.

## 4. Recommendation: (B), as the Defs conjunct of §2.1 (after approval), with `NoTopStmt'`
**Reasons for (B):**
- (A) cannot be a transport (§1, the vacuity of the source). As a restated StepStmt it needs a semantic frame lemma
  plus reachability. Both are absent, and the change would reopen four built producers.
- (B) needs only structural facts:
  - the `closeInstsG` checks that already exist (`noInstOfB` on the body and the design, "found as itself");
  - post-pass preservation, which this unit settles (§0).
- In (B), incoming-edge `InstClosed` is enough, so no reachability is needed (§2.4 step 3).
- (B) leaves StepStmt and every producer unchanged (§2.6). The KeepBody/KeepChild proofs are generic.

**Remaining cost of (B):** the MISSING `closeInstsG` coverage lemmas (freeze steps 4-5), and re-proving G-SERVED at the
stronger invariant, which is the same text. Prefer the Defs-conjunct form over the side invariant (§2.8): it costs
half as much proof text.
