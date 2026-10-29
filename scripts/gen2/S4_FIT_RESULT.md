# S4 run-local fit consumer (chain): result

- **Issue:** `sparkle-gen2-step`.
- **Freeze:** S4_FIT_FREEZE.md rev2, approved in design scope at bbca065d (incl. the `…F` chain and `hW`); wording at 99c86ac7, notes at c6951eb8.

## Builds
| job | head | result |
|---|---|---|
| `g2fit-bbca065d` | bbca065d | exit 0, 318 jobs: `Tools.ShippingGen2Fit` (`KSBoundedRun`, `fitX_of_runR`, `posEnc_lt`) |
| `g2fc-c6951eb8` | c6951eb8 | **exit 0, 734 jobs**, log `979993f304b48246`, no sorryAx; `Tools.ShippingGen2FitChain` + `Tests.Gen2.S4FitCheck` Built |

**Axioms (audit), 16 roots, all standard or a subset:**
- `fitX_of_runR` `[propext, Quot.sound]`;
- `posEnc_lt` `[propext]`;
- `ksBoundedRun_of_In` `[propext, Quot.sound]`;
- `machine_linked_ofBV`, `machine_linked_ofB_viaV`;
- `ComposedHBF.toHB`, `composedNWn_of_HBF`, `ComposedNWF.toNW`, `composedNWRegsF_of_composedNWF`, `ComposedNWRegsF.toRegs`;
- `oneOut_lookup_callWire`, `oneOut_ksBoundedRun`, `binders_drop_at`, `composedNWRegsF_of_In`;
- `machine_linked_callsServed1F`, `machine_ships_hierC_run`.

**Projection checks (in the test, elaborated):**
- P1: `type_of% @machine_linked_ofB_viaV = type_of% @machine_linked_ofB` by `rfl`;
- P2/P3: `(composedNWn_of_HBF …).toNW` and `composedNWn_of_HB … hC.toHB …` are both `ComposedNW`;
- P4: `.toRegs` of `composedNWRegsF_of_composedNWF` / `composedNWRegsF_of_In` gives `ComposedNWRegs`;
- the `example` reproducing `machine_linked_callsServed1`'s conclusion via projections.

## What is proved
- **The run-local fit replaces `hKSb`'s single use.** `machine_ships_hierC_run` is consumer 1 (Srm33Core:24 at f51e68a4) with exactly the freeze's line table: `Bd`/`Inv`/`hBd`/`hRI` dropped, :124 deleted, :145/:176-178 changed. Fit comes from `KSBoundedRun` in `ComposedNWRegsF` via `fitX_of_runR`.
- **The source of the bound.** On the SAME witness (one `obtain`; the same ids/cache/envs/seed/time index), `machine_linked_ofBV` exposes each call wire's value. That value is the parent's call-result binder `posEnc`, bounded by `posEnc_lt`. `machine_linked_callsServed1F` turns it, after `intro i`, into `KSBoundedRun`, using the served child's single output (`oneOutCall_of_callDec`) and `hW`. The parent's fit is never assumed.
- **Reverse lemma.** `ksBoundedRun_of_In` (real run, `linkedWF`, distinct instance names, initial `Inv`) and `composedNWRegsF_of_In`. The memory path stays on consumer 1; the single-consumer alternative is not used.

## Open
- **`hW : ∀ k, OneOutWidth P p k`** (G-ONEOUT-WID): no supplier; needed also for `RunFacts.wid`.
- **G-SERVED:** the trace with `ServedP (ShipsRes …)`.
- **The ordinary-only `hdec`:** S4-MEM (case restriction).
- **Group parents:** an unverified planned route.
- **Stage B** (`oneOut_topShips`, assembling this with `RunFacts`) is NOT yet done. Stage C, G-ONEOUT, M2 and FG are not claimed.
- **Integration with M3 `InstClosed`:** re-verify at the combined SHA.
