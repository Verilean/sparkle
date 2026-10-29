# M2-a2 LeafStmt' (register leaf): result

Issue `sparkle-gen2-leaf`.
- **Plan:** scripts/gen2/LEAF_FREEZE.md rev2 (d91c9c3d). §3 was approved at 1ddb25c6; R1/R2 were fixed in rev2.
- **Branch:** `par/gen2-spec`.
- **Changes:** new files only (`Tools/ShippingGen2LeafSeq.lean`, `Tools/ShippingGen2Leaf.lean`, `Tests/Gen2/LeafInstance.lean`) plus their lakefile registrations. No production or compiler change, and no existing file edited.

## Builds
| job | head = base | result |
|---|---|---|
| `g2lf-b60fef2d` | b60fef2d | exit 0, 725 jobs: `Tools.ShippingGen2LeafSeq`, `Tools.ShippingGen2Leaf` |
| `g2lf-6571cd1d` | 6571cd1d | failed diagnostic, instance file only: no `Inhabited (HList (tys leaf16.machineData.ss))`. The same log shows standard axioms for every proof lemma |
| `g2lf-d9fac18c` | d9fac18c | **exit 0, 927 jobs**: `Tests.Gen2.LeafInstance`. Output log SHA-256 prefix `34ee2eef7be4aa0c`; no `sorry` |

**Axioms** (`g2lf-d9fac18c`): `leaf_ships`, `leaf_topShips_of_LB`, `leaf_childShips_of_LB`, `traceL_of_LB`, `seqStream_of_L`, `seqChildRun_of_L` and `leaf16_ships` each depend only on `[propext, Classical.choice, Quot.sound]`.

## What is proved
- **`Tools.ShippingGen2.leaf_ships : LeafStmt' L`.** The type is exactly the frozen rev2 §3 text. Against `LeafStmt` it differs in the three listed points only:
  - `DataOk := LeafDataOk`;
  - `ExtInS p`;
  - `slots ≠ []`.
- **Its proof.**
  - Its input is the A-boundary trace `(Pkg.trace L.O L.T hA p ran).toLB`. `JQC (dv w) w`, the run and `MachineDefines` are unused binders.
  - **Step 1, `leaf_topShips_of_LB`** (pure, no `ExtInS`): the run part of `machine_ships` on the trace as given. It has two `refineCheck_transfer` steps (merge, optimizer) and register fits from `MachineWired` + `hinitW_of_ok` + `refineCheck_regWidth`. It reaches every height through `runModuleTG_instFree`.
  - **Step 2, `leaf_childShips_of_LB`** (pure). `traceL_of_LB` moves the trace to the identity extension, by `ExtInS` and `bsIn.take kD = bsIn` (`leaf_take`, from `LeafDataOk`). It then applies `seqChildRun_of_L` and `seqChildRunN_of_flat` for every extending `dsn` and every `n`.
  - **`seqStream_of_L` / `seqChildRun_of_L`** (`Tools/ShippingGen2LeafSeq.lean`): mechanical copies of `seqStream_full` / `seqChildRun_full`. The proof bodies are the originals' text after `have h := sound hcore entry closes`. The old-boundary inputs are replaced by the trace `h` and `hpost`.
- **Instance `Tests.Gen2.LeafInstance.leaf16_ships`** (conditional; the run premises stay hypotheses). It applies `leaf_ships` to `leaf16Pkg := .gen leaf16Src`, with every supplier fixed as in freeze §5:
  - `GenFacts` comes from `leaf16.machine_{ok,body,inits,writes,result,source}`, with the identity extension. Causality is `rfl`. It is restricted to `Unit` by `genFacts_restrict`.
  - `LeafDataOk` by `decide`; `ExtInS` by `rfl`; `insts = []` and `slots ≠ []` by `decide`.
  - **Mechanical additions (recorded):**
    - The `Inhabited` state instance is `⟨leaf16.machineInits⟩`; the generator registers none for a callless leaf.
    - `ext`/`extB` are written as the identity lambdas, since a callless leaf has no `machineExt`.

  No semantic premise was added.

## Not claimed
- **The old all-leaf `LeafStmt` is not discharged.** The slotless leaf is the mandatory obligation G-SLOTLESS (`sparkle-gen2-step`). There a comb child interface/consumer or a `ChildShips` revision, its compatibility and its connection to ShipsRes/CacheShips/ServedP/StepStmt/T1 are decided first.
- **No generic supply** of `ExtInS`/`LeafDataOk` (M5 G3-GEN / G-DATA).
- **No run existence.** The instance is satisfiability of package and data, not evidence of a successful compiler run.
- **No change to the FG/M2 acceptance conditions.**
