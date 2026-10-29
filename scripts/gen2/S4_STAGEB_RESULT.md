# S4 stage B (one-output parents: `TopShips`): result

- **Issue:** `sparkle-gen2-step`.
- **Freezes:** S4_STAGEB_FREEZE.md rev1 (design-approved at a66699bb; full telescopes at eb60056f); S4_CONSUMER_FREEZE rev2 stage B; S4_FIT_FREEZE rev2.

## Builds
| job | head | result |
|---|---|---|
| `g2nm-eb60056f` | eb60056f | exit 0, 311 jobs: `Tools.ShippingGen2OneOutNames` (`machPorts_names_indep`, `ranA_inputs_machPorts`) |
| `g2sb-93e9994c` | 93e9994c | **exit 0, 736 jobs**, log `59496cd390f62522`, no sorryAx; `Tools.ShippingGen2OneOutTop` + `Tests.Gen2.S4StageBCheck` Built |

**Axioms.** All six roots depend on `[propext, Classical.choice, Quot.sound]`: `machPorts_names_indep`, `ranA_inputs_machPorts`, `core_callPorts_oneA`, `oneOutWidthAt`, `core_instOutWidthsOk_oneA`, `oneOut_topShips`.

## What is proved
- **`oneOut_topShips`:** for a one-output parent (`instFields = []`), `∀ n, TopShips p (n+1) p.decl b raw D`. The premises are the stage-A ones plus `hW : ∀ k, OneOutWidth P p k`; there is NO `hBd`.
  - **Route:** `machine_linked_callsServed1F` → `composedNWn_of_HBF` → `composedNWRegsF_of_composedNWF` → `machine_ships_hierC_run` (the run-local fit consumer).
  - **`RunFacts`:** `core_runFactsHA` + `core_linkedWF_ranA`, and `wid` from `core_instOutWidthsOk_oneA`.
- **Call `k` is identified by the SAME instance statement** of `b.body`. `core_callPorts_oneA` reads the closing's `CallStmt` in the trace's port names, via `NamesEq` = `ranA_inputs_machPorts` + `machPorts_names_indep`: names depend only on the allocator state. `Served1P` is applied at that `k`/`st`/`mc`. No instance name and no `RealChildA` identification is used.
- **`oneOutWidthAt`** is local to the served child: `Served1P` → `ShipsRes` → `ChildShips`' output conjunct (both `ChildRunN` branches) at `i0` → the single output, then `hW`.
- **Empty `ι`.** `oneOut_topShips` splits on `Classical.em (Nonempty ι)`; `isEmpty_or_nonempty` is Mathlib-only. The empty branch keeps `h`'s existing `ids`/`cache`/`regs` and closes `∀ i` vacuously. No `Nonempty ι` premise is added, and `machine_ships_hierC_run` is unchanged.

## Open (not claimed)
- **`hW`** (G-ONEOUT-WID): no supplier.
- **G-SERVED:** the trace with `ServedP (ShipsRes …)`.
- **The ordinary-only `hdec`:** S4-MEM case restriction; stage C.
- **Not claimed:** G-ONEOUT, M2, FG.
- **Group parents:** an unverified planned route.
- **Integration with M3 `InstClosed`:** re-verify at the combined SHA.
