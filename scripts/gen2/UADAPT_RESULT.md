# U-ADAPT: result

Issue `sparkle-gen2-uadapt`. Plan: scripts/gen2/G3GEN_CALL_PLAN.md rev1 §1 (approved 508b365e).
Changes: new proof/test files (`Tools/ShippingGen2Adapt.lean`, `Tests/Gen2/AdaptInstance.lean`) plus lakefile
registrations. No production change.

## Builds
| job | head = base | result |
|---|---|---|
| `g2ua-b4e85f8d` | b4e85f8d | exit 0: `Tools.ShippingGen2Adapt` |
| `g2ua-121c09fe` | 121c09fe | **exit 0, 925 jobs**: `Tests.Gen2.AdaptInstance`; log SHA-256 prefix `3db4d6b1908e2df3` |
| `g2ua-0c47ec08`, `g2ua-ab163330`, `g2ua-b71e6810`, `g2ua-cf66b479` | — | failed diagnostics: `open` syntax and the `p.lsrc` observation step; `interval_cases` unavailable (no Mathlib); arity rows not closed by `decide`; `quadNk` not opened. The last log's `sorryAx` came from that elaboration error |

**Axioms** (`g2ua-121c09fe`):
- `callArgsOkAt_width`: `[propext, Quot.sound]`;
- `call_inRange_at`, `callDec_of_hPointAt_at`, `hPointAt_of_callFactF_at`, `tm2_callDec_at`:
  `[propext, Classical.choice, Quot.sound]`.

No `sorry` in the two files. `Tests/Gen2/AdaptInstance.lean` sets `maxHeartbeats 4000000` at file scope, as
CallDecInstance does. It is an elaboration budget for the per-call `decide` only.

## Proved (exact frozen interfaces)
- `callArgsOkAt`, `SrcPkg.portWidths`;
- `callArgsOkAt_width`, the k-local form of `callArgs_width`;
- **`call_inRange_at`:** local `InRange`, from `ok`, the GLOBAL syntactic check `callsOk p.kD`, the slot count and
  the k-local rows `callArgsOkAt p.d p.kD k q.portWidths` and arity;
- **`callDec_of_hPointAt_at`:** one ordinary call's COMPLETE `HPointAt` plus the same data give `CallDec p q k`;
- **`hPointAt_of_callFactF_at`:** call `k`'s `HPointAt` from call `k`'s body of `CallFactF` only (the decoded-family
  witnesses, the output relation through `pkgS_dispatch`).

**Data hypotheses of the adapter, stated as they are:**
- `ok`;
- `callsOk p.kD` (global, syntactic, whole parent);
- the slot count;
- the k-local `callArgsOkAt` row;
- the k-local arity row.

The adapter does NOT use the `HPointAt`, the package, or the width/arity table of any other call.

## Pointwise re-derivation of topshare2 (`tm2_callDec_at`)
For each of the 4 calls separately, `CallDec tm2Pkg q k` comes from:
- that call's `HPointAt` (`hPointAt_of_callFactF_at` on call k's body of `tm2_hF`);
- the k-local `callArgsOkAt` row, by `decide` per k;
- the arity row, from `b_quadAll`'s `argsN` and the callee's `hNIn`.

**Not claimed:** `tm2_hF` itself comes from the existing generated `b_topshare2_hFP`. That is an instance supplier,
not generic coverage.

## Status
- G-CALLDEC is UNSUPPLIED in general.
- The adapter removes the dependence of a mixed parent's `CallDec` on other calls' facts.
- The generic supplies of `HPointAt`, `callArgsOkAt` and arity are G3-GEN-CALL (M5) and G-DATA-CALL (M3), as planned.
