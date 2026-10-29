# `CallField` (G-ONEOUT decoding): result

- **Issue:** `sparkle-gen2-callfield`.
- **Freeze:** CALLFIELD_FREEZE.md rev1, accepted at d9e29568; §5 synced at 1213ac7b.
- **Branch:** `par/gen2-spec`.

## Builds
| job | head | result |
|---|---|---|
| `g2cf-b213b3b4` | b213b3b4 | failed diagnostic: only `Tests/Gen2/OneOutCallField.lean:85`, an unqualified `OutField`. Everything else built |
| `g2cf-3b702f15` | 3b702f15 | **exit 0, 981 jobs**, log `7f94a7731925a5ae`, no `sorryAx` |

**What was rebuilt.**
- Newly Built: `Tools.ShippingGen2{Defs, Connect, CallDec, Adapt, CallField, …}` and every dependent proof file. Also `Tests.Gen2.{OneOutCallField, CallDecInstance, AdaptInstance, PkgCompat, U0Check, LeafInstance, MemParentInstance, QuantInstance, SlotlessCheck, SlotlessLeafInstance}`.
- Replayed: `QuantEndpoint`, `CombPkg`, `MemBd`, `MemKids`.
- **Axioms.** No root outside `[propext, Classical.choice, Quot.sound]` or a subset. `callerL_noFields` has no axioms.

## What is proved
- **`CallField` / `CallDec`.** `CallField` is in Defs, and `CallDec` uses it; only the name conjunct changed. `scripts/gen2/GEN2_DEFS.lean.txt` is cmp-identical.
- **`callField_group` / `callField_one`:** rewrites UNDER `instFields ≠ []` / `instFields = []`, not `rfl`.
- **Group compatibility.** `CallDecOld` (the old text), with `callDec_group_old` / `callDecOld_group`. These lemmas take `hG`: `seqFactsRN_of_callDec`, `callDec_of_callFactF`, `callDec_of_hPointAt_at`. Every existing (group) instance supplies `hG` by `decide`.
- **Route-aware per-call facts.** `HPointG`/`CallOutG`, the four group adapters to/from `HPointAt`/`CallFactF`, and `callDec_of_hPointG_at`. The existing `HPointAt`/`CallFactF`/`SeqFactsRN` are UNCHANGED.
- **One-output data.** `OneOutCall` and `oneOutCall_of_callDec` give `k' = 0`, `hS` from `Pkg.src_get`, and the `posEnc` equation. `oneOut_outputs` gives the OUTPUT SHAPE only.
- **PkgCompat.**
  - The `CallDec` `rfl` check is withdrawn and replaced by `callDec_gen_group`, an iff under `hG`.
  - `Old.CallDec p q k = CallDecOld (.gen p) (.gen q) k` is `rfl`; the stop condition was not hit.
  - `t1Hyp_iff`/`t1Stmt_compat` take `GroupOnly P Reach`. It is used ONLY by these compatibility tests and is never a T1/FG restriction.
- **Real-data test** (`Tests/Gen2/OneOutCallField.lean`):
  - `callerL_noFields`: `instFields = []`;
  - `callerL_calls_pbh`: call 0 is `pickByteH`;
  - `pbh_outs_single`: the callee outputs are a singleton;
  - `callerL_callField_data`: `CallField`'s one-output branch holds on the data;
  - controls: the OLD name conjunct fails (`oneout_old_name_fails`, `callerL_old_conjunct_fails`).

## Limits (not claimed)
- **No `callerL` package.** It has a register, and no `GenFacts` bundle of it exists. `callerL_callField` takes `hp : p.d = callerL.machineData`, which is NOT shown satisfiable.
- **`CallField` satisfiability is not the whole `CallDec`** (the argument, range and output-equation conjuncts), and not run existence.
- **The comb choice is not selected here.** The S4 consumer must get the comb branch from `instStmt`'s successful no-clk/rst check plus C3 (`not_seq_and_comb`); `oneOut_outputs` does not select it.
- **Integration.** With M3 `InstClosed` (par/gen3-induct) and M5 t2 (par/gen5-t2), the `CallDec`/`HPointAt` uses and a combined-SHA regression must be checked.
