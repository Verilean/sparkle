# G-SERVED integration result at the S1 combined SHA (SERVED_FREEZE rev1 §4.4)

**Branch / SHA:** `par/gen3-combined` 02e828fc8b83cf1bcaddaa797b2db200221acb0c (= merge 31a3fdfa of `par/gen2-spec`
d0ddc50b and `par/gen3-induct` 26f5d72a, plus the S1 fixes). Issue `sparkle-gen3-s1-combined`.

## §4.4 steps
1. **D2 unify.** One-off check `Tests/Gen3/DataBridgeUnifyCheck.lean` at b806845e: `noMemRowS` and `OneOutNoMemRow`
   equal by `rfl`; the statements of `OneOutNoMemRow_eq`, `hord_of_rowS`, `hord_of_row` definitionally equal
   (`UNIFY OK` ×3). Build `s1u2-b806845e`: clean detached worktree, source=base=end=b806845e, dirty=false, exit 0,
   736 jobs, standard axioms. Then (c3b2e98a) the copy `Tools/ShippingGen2ServedDataBridgeCopy.lean` and the one-off
   check were deleted; Served/PostFacts and their checks use `Tools.ShippingGen2DataBridge`.
2. **`.comb`.** `machine_traceL_of_comb_callsX` (§1.6 (i)) and the `comb` case of `Pkg.traceX` (§1.6 (ii)), 3ee5132a;
   namespace/layout fix 02e828fc (`letObsComb` is `Tools.ShippingMachineCausal.letObsComb`).
3. **Post.** Post already imports F1 (`Tools.ShippingGen2ServedRun`) and uses its P1/P2; no second copy exists.
   The identical local copies of the expected-type helper (`Tests.Gen3.ServedExpectedType`,
   `Tests.Gen3.PostExpectedType`) were deleted; both checks import `Tests.Gen3.ExpectedType` (3ee5132a).
4. **Re-elaborate at the exact SHA.** Build `s1c-02e828fc`: clean detached worktree `gen3-combined-v3`,
   source=base=end=02e828fc, dirty=false, ancestry verified, exit 0, `Build completed successfully (1074 jobs)`.
   Targets: `sparkle_barrier`, `sparkle_jit` and every lakefile `lean_lib` whose module imports
   `Tools.ShippingGen2Defs` transitively (96). Newly Built in this job (not replayed) include `Tools.ShippingGen2Defs`,
   `Tools.ShippingGen2Served`, `Tests.Gen3.ServedCheck`, `Tests.Gen3.PostFactsCheck`, `Tests.Gen3.T1Check`,
   `Tools.ShippingGen2KeepChild`, `Tests.Gen2.DataBridgeCheck`, `Tools.ShippingGen5T2Tie`, `Tools.ShippingGen5T2Conn`,
   `Tools.ShippingGen2FitChain`, `Tools.ShippingGen2OneOutTopO`, `Tools.ShippingGen3Arity`.
5. **Axioms.** In the full log (`~/git/.kjob-state/namespaces/sparkle-dev/s1c-02e828fc/output.log`, 236403 lines,
   sha256 prefix 28655b1b91be16af): 791 `depends on axioms` lines, none outside `propext`, `Classical.choice`,
   `Quot.sound`; `sorryAx` 0; `GEN3 AXIOMS OK` 396; `CHECK FAILED` / `MUTANT ACCEPTED` / `UNIFY MISMATCH` 0.

## Earlier failed attempt (kept for the record)
`s1b-9d26005c` (9d26005c) exit 1: wrong namespace for `letObsComb` and the comb-arm indentation in Served; a sixth
two-part `ShipsRes` destructuring at `Tools/ShippingGen5T2Tie.lean:221` (and `Gen5T2Conn.lean:113`, downstream) that
the first grep missed. Fixed in 02e828fc.

## Not claimed
`servedShips0_proved` and `t1_of_stepPF_served` stay CONDITIONAL (`hrow`, `StepStmt`, `PostFactsStmt`). G-SERVED,
G-POST, T1/M3 and FG are not complete. The next shared edits are S2 (TopShips R-G) and S3 (ChildPortWidths).
