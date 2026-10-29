# S2-c: read-closedness of the slotless leaf's shipped module — freeze rev1, FOR REVIEW

Issue `sparkle-gen2-step`.
- **Branch:** `par/gen2-spec`.
- **Route:** approved at 972782bc (plan only).
- **This document:** the full types. Every premise's supplier is listed in §3, with nothing left provisional. No Lean change yet.

## 1. Pure lemma (no boundary)
```lean
theorem slotless_closed_full {t t' M b : Sparkle.IR.AST.Module} {lay : Layout} {K : Nat}
    (hcl : closeLets K t = some t')
    (hclosed : readsClosedB (t.inputs.map (·.name)) t.body = true)
    (hassign : ∀ stmt ∈ t.body, ∃ l r, stmt = Stmt.assign l r)
    (hslots : lay.slots = [])
    (hM : M = closeMachine lay t')
    (hzb : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body = M.body)
    (hzi : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).inputs = M.inputs)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) :
    readsClosedB (b.inputs.map (·.name)) b.body = true ∧ b.body.all Sparkle.IR.RegDedup.isAssign = true
```
Internal pure steps, each a separate lemma:
- **`closeLets_closed`** (`t → t'`).
  - **K = 0:** `closeLets 0 t = some t` (Machine.lean:180), so `t' = t`, as in `closeLets_eq'` (CallsParent.lean:61-65).
  - **K ≠ 0:** `closeLets_eq` (CallsParent.lean:23) gives the closed body and `assignmentOrderCheck`. Then `assignmentOrderCheck_iff` (AssignmentOrder.lean:101) gives `Acyclic`, and `closed_of_acyclic` (MachineChildComb.lean:68) applies.
  - **Reads of the K ≠ 0 body:**
    - prefix statements: `readsClosedB_append` (HarnessClosed.lean:45) and `reads_of_closed` (MachineChildComb.lean:49);
    - let ports: driven by their alias, via `alias_mem_of_assign` (a copy of `alias_mem`, CallsAssembly.lean:45, whose `mem_of_writes` step uses `hassign` instead of `Acyclic.assign`) and `letOperands_chain` (MachineClose.lean:701-704);
    - `core`: `letOperands_core` (:93), or `core = w`.
  - **Assign-only:** `acyclic_isAssign` (GateChildComb.lean:47).
- **`closeMachine_slotless_closed`** (`t' → M`). With `slots = []`:
  - if `packedWire? t'.body = none`, then `M = t'`;
  - otherwise `M.inputs = t'.inputs` and `M.body = t'.body.dropLast ++ outAssigns w lay.outs`, using `nextAssigns_nil`/`registers_nil` (MachineChildComb.lean:117, 121).
  - The prefix is closed by `readsClosedB_append`, and `w ∈ S ++ writesOf dropLast`.
  - Every out assignment reads only `w`, so `readsClosedB_of_all` (LeafOneOut.lean:142) closes them.
- **Merge:**
  - closedness: `mergeChecked_closed` (MergeClosed.lean:147-149; premises `body.all isAssign` and `readsClosedB S body`);
  - inputs: `mergeChecked_ports .1` (RefineCheck.lean:291);
  - assign-only: `mergeChecked_assign` (CombKidText.lean:198) and `mergeDuplicates_assign` (LeafOneOut.lean:159).

**Premises deliberately NOT taken** (review request: name/order/packed-tail/reads):
- **Name freshness and Nodup of the out names, `outNameOk`, `Allocated`:** not needed. Closedness only grows `S`, and every out assignment reads only `w`. They were used by `slotless_childComb` only for the non-closedness fields of `ChildComb` (`named'`, `outputs`, `outDriven`, `inputNames`).
- **Packed tail `t.body = bodyB.reverse ++ [.assign "out" (.ref w)]`:** not taken as a premise. The case split on `packedWire? t'.body` covers both outcomes, and the `some w` case reads its own tail.
- **Order:** `Acyclic t.body` is not taken. For K ≠ 0 the order is `closeLets`' own `assignmentOrderCheck`; for K = 0 it is `hclosed` itself.
- **Reads:** exactly `hclosed`.

**All outputs and all K.** `lay.outs = []` gives just the prefix. Several or clashing out names need nothing. `K = 0` has no `K ≠ 0` premise; the old `hK` is dropped.

## 2. Run-level supplier (A boundary)
```lean
theorem slotless_closed_ofRun (L : Laws mref cref) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : LeafDataOk p) (hnoI : p.d.shape.insts = []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D) :
    readsClosedB (b.inputs.map (·.name)) b.body = true ∧ b.body.all Sparkle.IR.RegDedup.isAssign = true
```
Derivation, the same run throughout:
1. **The successful run.** `ran` is `MachineRunJQC` (ServedRealA.lean:90-95): `∃ tenv bb w9 w10, RunsTo (synthesizeMachineCertified … c shape) … w9 (some (raw, D)) w10 ∧ JQC …`.
   - **The `none` case is excluded by `ran` itself** (the result is `some`). No `MachineCloses` is used.
2. **Closing facts.** `synthesizeMachineCertified_leaf_runs hnoI hrun9` (CallWidthsChildRealA.lean:90-100) gives `t, t', run, hcl : closeLets p.d.shape.layout.lets t = some t'` and `hMeq : raw = closeMachine p.d.shape.layout t'`. It holds for `insts = []` only (see §4).
3. **The translator run.** `synthesizeMixedCertified_returns run` (MixedEntrySoundness.lean:434-442) gives `nd, len, hrun, hm, nameLegal`.
4. **Binder facts from `ok`.** `Pkg.ok p` (Gen2Pkg.lean:78) is destructured as in SeqChildIfaceA.lean:58-84 into `hposv`, `hwf`, `hb'` and `hv'`.
5. **Closedness of the transition module.** `transition_closed nd len hrun hm nameLegal hposv p.d.packed hwf hb' hv' (Pkg.body_eq p)` (TransitionClosed.lean:35-56) gives `hclosed` and `hassign`.
   - `Pkg.body_eq` (Gen2Pkg.lean:84-88) is proved by cases: `gen` from `GenFacts.body_eq`, `loop` from `LoopFacts.hbody`. So both package kinds are connected.
6. **Cleanup identity.** `Pkg.trace L.O L.T hA p ran` (Gen2Pkg.lean:103) gives the `MachineWired` cleanup conjunct (MachineEntry.lean:686-690) under `hnoI` and `outTy` from `hdata.rows`: `hzb` and `hzi`.
7. **Assembly.** `slotless_closed_full hcl hclosed hassign hsl0 hMeq hzb hzi hpost`.

## 3. Premise ↔ supplier table
| premise | supplier |
|---|---|
| `hcl`, `hM` | `synthesizeMachineCertified_leaf_runs` on `ran`'s run (step 2) |
| `hclosed`, `hassign` | `transition_closed` (step 5) with `Pkg.body_eq` |
| `hslots` | the S2 case binder `slots = []` |
| `hzb`, `hzi` | `MachineWired` via `Pkg.trace` (step 6) |
| `hpost` | the statement binder |
| `ok`-derived binder facts | `Pkg.ok` (step 4) |

- **No premise without a supplier.**
- **No new premise for `LeafStmt'` or `StepStmt`.** S2's slotless statement uses `LeafStmt'`'s binders. `JQC`, the core `RunsTo` and `MachineDefines` stay as unused binders where the statement has them, as in `leaf_ships`.
- **If the build shows a needed fact the run does not give, I stop and report.**

## 4. Scope limits (recorded)
- **Instance-free modules only.** `synthesizeMachineCertified_leaf_runs` covers `insts = []` only. A slotless PARENT with instances (S5) does not get S2-c's result. It needs a separate transport through `closeInsts`/`closeInstsG`, which stays in the S5 freeze.
- **What S2-c gives.** Closedness and assign-only. S2 then uses them for S1's reset irrelevance, `TopShips` and `CombChildRunN` (right disjunct) of the slotless leaf, as in rev3 §4 S2.

## 5. Build plan
- **Target file:** `Tools/ShippingGen2SlotlessClosed.lean` (pure lemmas + `slotless_closed_ofRun`).
- **Build:** an issue-linked, exact-head focused build.
- **Axiom audit:** in the S2 assembly test.
