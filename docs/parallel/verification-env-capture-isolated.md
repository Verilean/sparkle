# Environment-capture PROPOSAL — verified in isolation, NOT integrated (2026-10-14, ruling item 4)

Candidate: branch `fix/inst-arm-env-build` in `~/sparkle-work/wt-cachefix` = poc 826418d3 + worker F's
`fix/inst-arm-env` (audit f3438bd5, proposal e0c0b655; cherry-picked without conflict) + one `lean_lib`.
`poc/roundtrip-proof` does NOT contain it. Records on the candidate branch: `docs/parallel/ENV-audit.md`,
`docs/parallel/ENV-capture-proposal.md`. cgrun 3 GiB swap 0. GitHub CI: 0 runs.

What the proposal is: a SECOND, capturing entry (`synthesizeCombinationalE`, `translateInstanceArmWith env`)
beside the existing one (+113 −3 in `Elab.lean`); the instance arm of the capturing entry tests the tag on
the environment read at the entry instead of reading again. No command uses it; the commands run the
same term as on poc (`entryTranslate T env none` unfolds to `T`).

| run | what | result |
|---|---|---|
| `env-iso` | `lake build Sparkle` | exit 0 |
| `env-iso` | `lake build Tests.AllTests` (incl. the seven proofs that unfold the entry: they went through unchanged) | exit 0; peak 2.74 GB |
| `env-iso` | `Tools.ShippingInstArmGrow` (`spine_tag`, `spineRoot_tag`, the keeps lemmas, `instanceArm_grow`, `instanceArm_grow_of_root`) | exit 0, first attempt, worker's file unchanged |
| `env-iso` | `EnvCaptureDigestProbe`, `EnvCaptureCompareTest` | exit 0 |
| `env-digest` | `EnvCaptureDigestProbe` on poc df990315 (file copied for the run, not committed) | exit 0 |

Measured:
* `ENVCAPTURE DIGEST` lines (the commands' entry) for the eight gate-route parents plus `okW`, `kSD`:
  the 10 lines are IDENTICAL on poc and on the candidate.
* `ENVCAPTURE COMPARE` (candidate): for each of the eight parents the existing entry and the capturing
  entry both return and their (module, design) are equal; 1–2 instance statements.
Not run: sims and the sampled text comparison (the commands' term is unchanged by construction; the
digest lines above are the measured part of that).

By the audit (reading, not a theorem): no environment write on a synthesis path in the compiler; none of
Lean 4.32.1's environment writers is called by the Meta operations the compiler uses, as far as the
defining files were read (not their transitive closure); no cache is keyed by the environment; a child
reads the same value. No can-differ case was found.

STATE: with the capturing entry, the tag premise of the instance arm is a fact about the entry's read
(`spineRoot_tag`: no environment premise for a constant applied to input binders), and
`instanceArm_grow` is a theorem with no pinned-child premise. `gate_parent_run` is NOT written. It would
be a theorem about `synthesizeCombinationalE`, which no command runs.

DECISION for the reviewer: to make it a statement about what the commands run, the commands must be
switched to the capturing translator. The built proofs are stated on the literal translator
(195 lines in 76 `Tools/` files, incl. the entry-bridge lemmas, `BodyRel`, `HarnessRel`), so the switch is
a re-base of every theorem connecting an entry run to a translator-specific statement. Alternatives: keep
the capturing entry as a parallel, non-command entry (what exists now); or leave gate-route parents open.
