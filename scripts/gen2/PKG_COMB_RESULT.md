# `Pkg.comb` (G-SLOTLESS package): result

- **Issue:** `sparkle-gen2-step`.
- **Freeze:** PKG_COMB_FREEZE.md rev1, accepted for implementation at f9a8312d.
- **Branch:** `par/gen2-spec`.

## Builds
| job | head | result |
|---|---|---|
| `g2cp-682dbb1c` | 682dbb1c | mkvs-dell: never scheduled (no node, no output); NOT cancelled, left as is |
| `g2cp-h-682dbb1c` | 682dbb1c | **step 1:** exit 0, 697 jobs, log `8d13116a42b6ce72`; `Tools.ShippingGen2CombPkg` Built |
| `g2cp2-698be477` | 698be477 | **step 2 re-verification:** exit 0, 978 jobs, log `fc7afd16dc55f92c`, no sorryAx |
| `g2cp3-22417406` | 22417406 | **step 3 instance:** exit 0, 746 jobs, log `f55015aebc07afab`; `Tests.Gen2.SlotlessLeafInstance` Built |

**What step 2 rebuilt.** Every package-quantified proof, plus the gen/loop regression and compatibility tests:
- Newly Built: `Tools.ShippingGen2{Pkg, Defs, Connect, Consumer, Keep, Data, CallDec, Adapt, AComb, Comb, CombKid, Leaf, LeafSeq, SlotlessClosed, SlotlessLeaf, MemData, MemFacts, MemParent, MemShips, MemTop}` and `Tests.Gen2.{SlotlessCheck, LeafInstance, MemParentInstance, QuantInstance, PkgCompat, U0Check, CallDecInstance, AdaptInstance}`.
- Replayed: `QuantEndpoint`, `CombPkg`, `MemBd`, `MemKids`.

**Axioms.**
- Every root: `[propext, Classical.choice, Quot.sound]` or a subset.
- `machine_traceL_of_comb_callsRA_ranA`, `combTrace`, `pbh_dataOk`, `pbh_ships`: standard.
- `pbh_ls_ne`: no axioms.

## What is proved
- **Step 1** (`Tools/ShippingGen2CombPkg.lean`, the freeze §2-§3 types):
  - `CombFacts`/`CombPkg`, with no `slots`/`insts` field;
  - `extS`/`extBS` = identity, `lsrc = letObsComb`, `CombPkg.lsrc_hl`, `CombPkg.src_length`;
  - the A-boundary adapter `machine_traceL_of_comb_callsRA_ranA` on the SAME `MachineRunJQC`;
  - `combTrace`.
- **Step 2.** `Pkg := gen | loop | comb`, with `.comb` cases of the accessors, `Pkg.ok`, `Pkg.body_eq`, `Pkg.lsrc_hl`, `Pkg.trace` (= `combTrace`) and `Pkg.src_length`. `DataOkLiftCompat` is `False` on `.comb` (test-only).
- **Step 3.** `pbh_ships`: `slotlessLeaf_ships` applied to `.comb pbhC` for the REAL slotless declaration `pickByteH`.
  - `pbhC`'s facts are `pickByteH.machine_ok/body/inits/next/result`. `machine_result` is the kernel-checked tie of `machineSource` (the declaration's own observations) to the IR.
  - Data and case premises are decided: `LeafDataOk`, `ExtInS` (`rfl`), `insts = []`, `slots = []`, and `ls ≠ []` (so `lsrc` is not vacuous).
  - The run/reflection/route premises (`AdmCtx`, `JQC`, the core run, `hpost`, `MachineDefines`, `MachineTaken`) remain HYPOTHESES. No run existence is claimed.

## Not claimed / open
- **S2's slotless lemmas** (`slotlessLeaf_ships` etc.) themselves are not yet accepted. This unit only gives them a real package.
- **`CombFacts` does not imply slots = [] / insts = [].** `pbh_ships` checks those as data.
- **Sign-normalised comb declarations** (`machineSourceDecl`) are an OPEN coverage gap, not an FG exclusion.
- **Open obligations:** the parents' consumers of comb children (S3/S5), G-SLOTLESS completion, `MachineClosesAtA` for comb names, and the closing/reflection premises.
- **The `InstClosed` change on par/gen3-induct** (`ShipsRes`) is not in this branch. These results must be re-verified at the integration SHA.
