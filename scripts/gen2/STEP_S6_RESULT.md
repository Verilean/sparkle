# M2-step S6 (A-COMB) + S1: result

Issue `sparkle-gen2-step`.
- **Plan:** STEP_IFACE_FREEZE.md rev3 (02b0918f, approved).
- **Review:** scoped-approved at 1fdbc18d.

## Build `g2st-s6-1fdbc18d` (head = base_head = 1fdbc18d)
- **Result:** exit 0, 973 jobs, output log SHA-256 prefix `091f13c2e08d2355`, no `sorryAx`.
- **Newly Built** (changed modules and their dependents):
  - `Tools.ShippingGen2{Comb, Defs, AComb, Data, Consumer, Connect, CallDec, Keep, MemFacts, Adapt, MemParent, MemData, MemTop, MemShips, Leaf}`;
  - the seven tests `Tests.Gen2.{U0Check, CallDecInstance, AdaptInstance, MemParentInstance, PkgCompat, QuantInstance, LeafInstance}`.
- **Replayed** (not rebuilt): `Tools.ShippingGen2MemBd`, `Tools.ShippingGen2MemKids`, `Tests.Gen2.QuantEndpoint`.
- **Up to date, with no log line:** the other upstream gen2 modules (`SrcPkg`, `Pkg`, `Loop`, `LoopRestrict`, `C6`, `LeafSeq`).
- **Axioms:** every printed root depends on standard axioms only. Two of them (`quant_hcausal`, `callArgsOkAt_width`) depend on a subset, `[propext, Quot.sound]`.

## What is in it
- **A-COMB** in `Tools/ShippingGen2Defs.lean`: `CombChildRunN`, `ChildRunN`, and `ChildShips` using `ChildRunN`. `scripts/gen2/GEN2_DEFS.lean.txt` is cmp-identical.
- **C1-C3** (`Tools/ShippingGen2AComb.lean`): `childRunN_of_seq`, `childRunN_iff_seq`, `not_seq_and_comb`.
- **`memParent_childShips` / `leaf_childShips_of_LB`:** one `Or.inl` each.
- **`Tests/Gen2/PkgCompat.lean`:** reclassified per rev3 §3.
  - `Old.*` is kept.
  - Unaffected `rfl` checks, `t1Hyp_iff` and `t1Stmt_compat` are unchanged.
  - Positive positions become `Old → new`: `childShips_gen`, `shipsRes_lift`, `shipsAt_lift`, `cacheShips_lift`, `invAt_lift`.
  - `.gen`-restricted forms: `memParentStmt'_gen`, `memParentStmt_gen`, `leafStmt_gen`.
  - The seven mixed-position checks are withdrawn, with a comment.
- **S1** `runModule_seed_local` (`Tools/ShippingGen2Comb.lean`), the frozen type. `g2st-s1-b46f33a5` was a failed diagnostic (structural recursion of `memFree_of_assigns`), fixed before this build.
- **Consequence not listed in the freeze; approved as a sequential-only restriction.** `seqFactsRN_of_callDec` takes `hseq : ∀ mc, ServedPC (ShipsAt L P n) dsn c mc → "clk" ∈ mc.inputs.map (·.name)` and uses C2.
  - `hseq` is not generally supplied, and is NOT a T1/FG premise.
  - **S3 obligation:** branch per actual served `mc`, or with a `PC` restricted by the branch. A case split on one `mc` does not give the universal `hseq`.

## Not claimed
- Not claimed: preservation of the final guarantee over A-COMB (open until S3-S5).
- Not done: G-SLOTLESS, G-ONEOUT, StepStmt, the M2 milestone.
