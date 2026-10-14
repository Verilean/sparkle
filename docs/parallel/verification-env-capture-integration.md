# Environment capture, option (a) — INTEGRATED on poc (2026-10-14, ruling item 3 of the second message)

poc HEAD after integration has tree `d6136b112e71e639169683359c64816de6a1e2d2`, IDENTICAL to the candidate
tree verified in the isolated worktree `~/sparkle-work/wt-cachefix` (branch `fix/env-capture-build`):
poc a61d894b + worker M's eight commits (cherry-picked without conflict) + one `lean_lib` + two commits of
integrator fixes. cgrun 3 GiB swap 0, one job at a time. GitHub CI: 0 runs.
Design, inventory and statement changes: `docs/parallel/M-env-capture-a.md`.

What changed: ONE entry. The translator functions take the environment; the entry reads it once and hands
the same value to the translator, the instance predicate, the inliner and the structure view; the
instance arm no longer reads the environment again (`instArmEnv` is gone). Every declaration's entry —
a command's and a nested child's — captures its own read. No second entry, no environment law or axiom.
`projFieldName?` and the legacy handlers still read the environment; their obligations are the existing
premises (table in M's doc §0c).

## Build rounds on the candidate (integrator)
`env-a1` … `env-a3`, five runs of an automated build-and-patch loop (`env-loop*`), `env-all2`.
Fixes (26 files, no statement changed): the implicit environment given explicitly at untyped bindings
(`fuel_contract` 12, `translateExprToWire_bool_contract` 4, others 6); typed bindings for
`BodyRel` / `HarnessRel` / `MachineClosesAt` hypotheses (12 files); one missed `henvT` argument;
`intro tenv` in one prover and before one `refine`; one destructuring with the environment component.
The loop twice pinned the argument on a hypothesis where no such variable is in scope; the next build
caught it and the binding was typed instead.
Result: `Tests.AllTests` green; `env-all2`: 832 targets (every `Tools/` module and every
`Tests/Compiler/` module except the Keccak / sponge / SHA / Fp12 tests, `Tools.DeepElab`,
`Tools.ConeFoldProbes`, and the logging censuses / probes) — exit 0, no error.

## Integration criteria (runs `envcrit-cand2` on the candidate, `envcrit-poc` on poc a61d894b)
* Digest probe (`EnvCaptureDigestProbe`: the 8 gate-route parents, 2 legacy controls, 15 named
  declarations, 30 tagged test declarations — 44 `ENVCAPTURE DIGEST` lines): poc vs candidate diff EMPTY.
* Real writer simulation of the 8 gate parents (`gate_parents_sim.sh`, iverilog, 94 cycles each):
  `command==source T` for all eight on BOTH trees.
* Endpoint statement audit (`EndpointStatementAudit`, 2949 endpoint theorems of the AllTests
  environment): 2820 lines identical (hash included). 128 differ by exactly one more binder and one more
  `Environment` binder with the SAME premise heads and conclusion head: `machine_closes` 89,
  `machine_closes_at` 23, `closes_deep` 7, `machine_closes_at_memkid` 2 (statement text and hash
  unchanged — the binder is the `∀ {tenv}` inside the definition they state), and 7 that mention the
  translator (`leaf_*` legacy theorems, `machine_keeps`; hash differs). 1 other: the general theorem
  `machine_run_of_core` (picked up by name; its conclusion now exposes the environment existentially).
  NO `machine_design_*`, `gate_design*`, `machine_sound` or `machine_ships_*` line differs: no
  design-level endpoint gained or lost a premise or changed its conclusion.
* Census: 134 declarations, 133 covered — unchanged. Pin tests, the outermost endpoint test,
  `SlotlessParentProbeTest`, `Tools.ShippingInstArmGrow`: build. `tagged-jit-e2e-test`: runs, exit 0.
  Sims writer, module_name, nested_let, subinst_key, optprint: exit 0.

## What is NOT claimed
* Equivalence with the old two-read entry on all inputs. Equality of the reads in real runs is by AUDIT
  (reading; `docs/parallel/ENV-audit.md` on the candidate branch); the measured part is the digest and
  simulation comparison above.
* `gate_parent_run` — NOT written. Gate-route parents (no generated data) are still OPEN. What exists:
  `instanceArm_grow` / `instanceArm_grow_of_root` about the real instance arm, with the tag from the
  entry's read and no pinned-child premise.
* The heavy targets excluded from `env-all2` were not rebuilt on the candidate; the poc confirmation
  build after integration covers `Tests.AllTests` and the Keccak sponge target (recorded below when run).
* `HardwareTagged childAdd` in the S6 capstones is now derivable from their `tag` premise; it was left in
  place (dropping a capstone premise is the reviewer's call).
