# M3: G-KEEP-CHILD freeze rev1, and a G-POST stop-report with a spec-change proposal (FOR REVIEW)

- **Issues:** `sparkle-gen3-keepchild`, `sparkle-gen3-post`.
- **Branch:** `par/gen3-induct`, at the approved skeleton 6a21b480.
- **Status:** read-only survey; no Lean. `Inv(D)` := `InvAt L P Reach D`; `E(D) := fun e w => Inv(D) w ∧ OkExc e`.

## B. G-KEEP-CHILD: `keepChild_proved : KeepChildStmt L P Reach` (no spec change)
**Route.** A copy of `childKeepsP_of_body` (ChildPinC.lean:346) with `JQP O D L` replaced by `Inv(D)`.
- **Reused:** `stableA_invAt` (Gen2Connect.lean:41).
- **Why the copy is safe:** `InvAt = JQC ∧ CacheShips (cv w)` (Defs:144), and every framed or diagnostic step keeps `cv`.

New lemmas, each the copy named:
| # | lemma (exact shape) | copy of |
|---|---|---|
| 1 | macros `iset`/`iget` with `stableA_invAt L P Reach D` | `psset`/`psget` (PinC:62-72) |
| 2 | `tripleInv_depthSet D v : Triple … (Inv D) (ST.Ref.set sparkleSynthDepth v) (fun _ => Inv v) R` | PinC:75 (`CacheShips` half: `O.depthSet` leaves `cv`) |
| 3 | `tripleInv_depthModify D f`, with post `Inv (f D)` | PinC:86 |
| 4 | `finInv`, `Inv(d+1)` → `Inv d` / `E d` | `finP` (PinC:104) |
| 5 | `core_tripleAInv (hA) (D) (hD : 1 ≤ D) (c) (hbody : ∀ {tenv}, D < sparkleSynthDepthLimit → ∀ b ci isInst, Keeps … (Inv (D+1)) (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b) c [] false true ci isInst)) : Triple … (Inv D) (synthesizeCombinationalCore c [] false) (fun _ => Inv D) (E D)` | `core_tripleAP` (PinC:133); the cache clear (Elab:5536-5541) is excluded by `1 ≤ D`, as `h0` does (PinC:195) |
| 6 | `full_tripleAInv` | PinC:207 |
| 7 | `tripleInv_cacheGet`, with post `fun m w => Inv D w ∧ m = cv w` | PinC:222 |
| 8 | `cacheShips_insert (h : CacheShips L P Reach m) (hr : Reach n → ShipsRes L P n r) : CacheShips L P Reach (m.insert n r)` | `cacheInvA_insert` (ChildCacheA:134) |
| 9 | `invAt_insert_runs (hA) (hw : Inv D w) (hr : RealChildA L.O n r) (hs : Reach n → ShipsRes L P n r) (h : RunsTo (sparkleChildCache.modify (·.insert n r)) … w u w') : Inv D w'` | `jqc_insert_runs` (ChildCacheA:263) + `cacheModify'` (PinC:246) + #8 |
| 10 | `synthesizeChild_tripleInv (hA) (hIH : IHAt L P Reach D) (hentryT : Triple … (Inv D) (synthesizeCombinational n) (fun _ => Inv D) (E D)) : Triple … (Inv D) (synthesizeChild n) (fun r w => RealChildA L.O n r ∧ (Reach n → ShipsRes L P n r) ∧ Inv D w) (E D)` | `synthesizeChild_tripleP` (PinC:255), without the pin/absence split. **Hit:** `RealChildA` from `hw.1.2`, `ShipsRes` from `hw.2`. **Miss:** `triple_withRun hentryT` (ChildCacheA:337) gives `w0` with `Inv D w0`; then `IHAt D` at that run, then #9 |
| 11 | `hentryT_of_bodyInv`, as `full_tripleAInv (core_tripleAInv …)` | PinC:292 |
| 12 | `keepChild_proved : KeepChildStmt L P Reach` | PinC:346, with #10 and #11 |
| 13 | `synthesizeChild_shipsRes (hw : Inv D w) (hIH : IHAt L P Reach D) (h : RunsTo (synthesizeChild n) … w r w') : Reach n → ShipsRes L P n r` (returning-run form, used by G-SERVED and G-POST) | the hit/miss read of #10 |

- **The `ServedP`-free `IHAt D` is enough for the insert.** The inserted value is the full entry's result `r`, run from the `Inv D` world `w0` that `triple_withRun` gives. That is exactly `IHAt D`'s quantifier. Names that are not reached need nothing.
- **Stop conditions:**
  - the core walk at `1 ≤ D` turns out to need a cache write other than the child insert;
  - a copied step does not elaborate with the extra `CacheShips` conjunct.
- **Acceptance:**
  - `keepChild_proved` (and #13) built with standard axioms;
  - `t1_of_step`'s `hKC` premise discharged in a corollary `t1_of_step_kc`.

## A. G-POST (`NoTopStmt`): STOP-REPORT — not provable as frozen
**Why** (a read-only argument; not a kernel counterexample):
- **`Reach` is arbitrary in `NoTopStmt`,** with no `T1Hyp`. A reached `c` may be on any route; `JQC`/`RealChildA` say nothing about module names (ChildCacheA:102-121).
- **The old analogue rests on an assumption.** `fresh_post` (CacheCoherentRun.lean:219) holds under `Prov` (:96), which comes from `CoreFresh`, a statement, not a theorem (:348).
- **Even on the machine route, the closing checks exclude only INSTANTIATED modules named like the top.** `noInstOfB m0.name …` is checked on the body and the design (Machine.lean:395-425; MachineInstG.lean:115-146). A dead module of that name inside a child's design is not excluded.

**Proposed fix (spec change; needs approval before any code):**
- **(a) `NoTopStmt'`.** Add `T1Hyp L P Reach DataOk →`, replace `JQC (dv w) w` with `InvAt L P Reach (dv w) w`, and add `IHAt L P Reach (dv w + 1) → ChildKeepsInv L P Reach (dv w + 1)`. All of these are in scope at the only use site, `ihAt_step` (Gen2T1.lean:178-185), so the skeleton's type would change only in this premise.
- **(b) A new conjunct of `ShipsRes`:**
  ```lean
  InstClosed (r : Res) : Prop := ∀ g ∈ r.2.modules, ∃ h ∈ r.1 :: r.2.modules, ∃ i cs, Stmt.inst g.name i cs ∈ h.body
  ```
  It flows through `CacheShips`/`IHAt` automatically. `ihAt_step` then also supplies `InstClosed` for `c`'s own result.
  - This weakens nothing; it adds a guarantee. But it changes `ShipsRes`, so the M2 producers (`memParent_ships`, `leaf_ships`, `slotlessLeaf_ships`, and `StepStmt`'s conclusion) must supply it too. Those are memory children, leaves with `D.modules = []`, and the step.

**Route for `NoTopStmt'` (after approval):**
1. `machineRunInv_of_closes`, a copy of `machine_run_of_coreA` (ChildRunA:225) + `machineRunJQC_of_closesA` (ServedRealA:97) at `InvAt`. It is shared with G-SERVED.
2. `synthesizeMachineCertified_runsInv`, with #13 at `D+1`, also shared with G-SERVED.
3. `closedBody_kinds_of_run` (ClosedKinds.lean:162): `m0.name = ofDecl c`, `d₀ = []`.
4. `closeInstsG_name_design` (TopShareNoParent:38). A one-output `closeInsts` analogue is MISSING.
5. `closeInstsG_checks_noTop`, MISSING: `noInstOfB` on the body and the design, children in `d'`, and every child instantiated in `raw.body`, via `callGroups` coverage + `isPermOf`.
6. `mem_designWith` (SharedLeafExt:150) case split:
   - a memory child: `ofDecl_ne_ofMem`;
   - a child top: instantiated, so `noInstOfB` applies;
   - a child's design module: by `InstClosed`, then `noInstOfB`.
7. **Post-pass preservation of instances, MISSING and a real risk:** an instance of target `n` in `raw.body` remains in `dropZeroWidthModule` (`dzStmt` keeps instances, ZeroWidth.lean:102) and in `mergeChecked` (`mergeDuplicates` merges nodes, RegDedup.lean:234-309). If this lemma is false, I stop and report.

**Counterexample risks under `T1Hyp`.**
- **A child named like the parent** means `c' = c` (`ofDecl_injective`), i.e. a self-call. It is either rejected by the parent's `noInstOfB` check (cached), or reaches the depth limit (`core_limit_triple`).
- **What remains:** only dead modules, which the machine route does not create except possibly through `mergeChecked` dropping an instance target (step 7).

## Order
1. B (`sparkle-gen3-keepchild`), now: no spec change.
2. A steps 1-2, shared with G-SERVED (`sparkle-gen3-served`): no spec change.
3. A (a)+(b), only after approval; then A steps 3-7.
