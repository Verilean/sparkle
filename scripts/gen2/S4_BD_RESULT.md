# S4-BD risk check: result (FOR REVIEW)

- **Issue:** `sparkle-gen2-step`.
- **Freeze:** S4_CONSUMER_FREEZE.md rev2 §6 (approved at 4ff583e9).
- **Probe:** `Tests/Gen2/S4BdProbe.lean`.

## Builds
| job | head | result |
|---|---|---|
| `g2bd-99020776` | 99020776 | failed diagnostic: a codegen error on the `pbhSkeleton` def (needs `noncomputable`) and an unqualified `logInfo`. The decided theorems kernel-checked |
| `g2bd-323d0501` | 323d0501 | **exit 0, 387 jobs**, log `fdcbf2ea763765f6` |

## Results
**Decided** (kernel, `[propext]`): `pbh_skeleton_masked`, `pick_skeleton_ref_masked`, `idH_masked`, `idHSlice_masked`. These are skeletons built with the compiler's own `closeMachine`, plus hand-written modules. They show that the check is syntactic: `y := x` fails and `y := x[7:0]` passes.

**Real compiler runs, LOGGED** (`run_cmd` through `synthesizeCombinational`; observations, not theorems):
| parent (real successful compilation) | served child | child `outsMaskedN` | parent `kidsMaskedN D.modules b.body` |
|---|---|---|---|
| `callerL` | `pickByteH` (machine route, slotless) | **true** | **true** |
| `caller` | `pick` (gate leaf) | **false** | **false** |
| `callerIdH` (probe-local) | `idHSrc` (compiled `:= x`) | **false** | **false** |

## Interpretation (per the freeze's rules)
- **Where the existing supplier applies.** `KSn_boundedIn`, via `kidsMaskedN`, applies to the machine-route slotless child `pickByteH` in its real parent. It does NOT apply to the real gate-leaf child of `caller` or to the compiled pass-through child.
- **What a false result means.** It says only that the existing syntactic supplier does not apply. It does NOT refute `KSBoundedIn`. These are successful compilations; the hand-written `idH` is not a counterexample.
- **Consequence for stage B.** One-output parents with gate-leaf (or pass-through) children need ANOTHER range supplier. The recommended one, though not shown to be the only possible one, is the run-local range-propagating consumer: replace consumer 1's `hKSb` use (Srm33Core:124/:176) by input fit + the child's meaning ⇒ output fit.
  - **Its suppliers** (none realised): input fit, the width correspondence (`OneOutWidth`/`callArgsOkAt`), per-step fit, and a source-output range lemma (none exists; the alternative is a `posEnc` bound from CallDec's equation).
  - **Not done:** no compiler mask, no FG premise.
- **Stage B may still use `KSn_boundedIn`** for parents whose served children are all machine-route slotless with the slice output, such as `callerL`. That is a case, not coverage.

## Not claimed
- `KSBoundedIn` false or true for any real child.
- That every machine-route slotless child is masked. Only `pickByteH` was observed.

## Review of 680f3316 (accepted as a risk check)
- **Kernel proofs** cover only the skeletons and the hand-written modules. The real runs are OBSERVATIONS; a "true" there is not a kernel-supplied fact about the real run.
- **`callerIdH`** goes through `try/catch`, but its run logged success, so it counts as a successful-run observation.
- **Job metadata.** For `g2bd-323d0501`, source = head = base = 323d0501. The result's `dirty=true`/end head were observed later and include the then-untracked `Tools/ShippingMachineExtB.lean`. The start was not recorded as `dirty=false`.
- **Next (approved direction).** A complete-type freeze of the run-local fit consumer with a supplier table, wired without circularity: input fit → the arguments' `InRange` (width correspondence) → the child's meaning/output range → the parent's fit. It is passed to consumer 1's `hKSb` use. No compiler mask, no FG premise.
