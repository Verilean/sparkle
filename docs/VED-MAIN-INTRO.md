# `#verify_elab_deep` on main: initial introduction

This branch (`ved/main-intro`, based on main `1614cee8`) brings `#verify_elab_deep` and a strict axiom audit to main. It is the **initial introduction** only. Extending coverage is separate work, and so is the release decision.

## What is added

- **The deep route, as of `df5f0b09` (2026-09-24).** This is the last commit where its regression files were confirmed to pass. The import closure of `Tools.DeepElab` is 41 modules; this branch applies their diff since main's base `6eee2ecb`, and nothing else:
  - **New files:**
    - `Tools/DeepElab.lean`, `Tools/VerifyElab.lean`, `Tools/ConcatNorm.lean`, `Tools/ConeFold{,Slices,Opt,Mem,RT}.lean`;
    - `Tools/SVParser/{EmitAst,EmitSem,RoundtripProof,SVSemantics}.lean`;
    - `Sparkle/IR/{Semantics,ReorderInvariance,ZeroWidth,RegDedup}.lean`.
  - **Changed files:**
    - `Sparkle/Compiler/Elab.lean` (+131), `Sparkle/Core/Signal.lean` (+200, merged with main's #135), `Sparkle/Backend/CSim.lean` (+104), `Sparkle/Backend/Verilog.lean` (+41), `Sparkle/IR/Optimize.lean` (+12);
    - `Tools/SVParser/{Lower,Parser}.lean`;
    - `lakefile.lean`: `lean_lib` entries for the closure only, none of them a default target.
- **The strict audit.** `Tools/VedStrictAudit.lean` (`#ved_strict_audit`, `#ved_axioms_raw`, …) checks a declaration's reachable axiom closure against `{propext, Classical.choice, Quot.sound}`. Anything else is rejected, including `Lean.ofReduceBool`, i.e. `native_decide`. Name patterns are never allowed through. `Tests/Ved/StrictAuditCheck.lean` holds its accept and reject controls.
- **The regression files, as of `df5f0b09`.** `Tests/Verification/{ValueParamInitRepro,ConeSharingGen,DeepElabReifyDemo,ConeSharingCrc16,DeepElabRealIP}.lean`. The IP sources they import (`IP/Net/{CRC32,UART}`, `IP/Crypto/EcdsaSignSmall`, `IP/Bus/{DroneCANHW,SBUSHW,SPIHW}`) are identical on main and at `df5f0b09`.
- **CI.** `.github/workflows/ved.yml` has two jobs, `ved-pr` and `ved-full` (see "CI" below).

## What it guarantees, and what it does not

- `#verify_elab_deep f` reifies the `circuit do` body of `f` into a deep embedding (`Cdo`, `CdoM` or `CdoW`). It proves `{f}_deep_trace`: the Signal output of `f` equals the compiled deep expression under the IR semantics, for every input stream and cycle (`Cdo.elab_general`). That theorem uses the standard axioms only.
- **The link to the IR the compiler emitted is not strict.**
  - The IR replay `{f}_deep_signal_run` and its lemmas (`_deep_coneEval_*`, `_deep_regstep`, `_deep_state_trace`, …) are discharged with `native_decide`. `ValueParamInitRepro` records this as `replay=[std + 23 native_decide aux]`.
  - These results trust the compiled evaluation of the checkers, not the kernel. Under the strict audit they are rejected, and they are never counted as strict.
  - The command also re-synthesises with `synthesizeHierarchical`. It therefore does not prove anything about the artifact that `#synthesizeVerilog` printed.
- **What it does not cover:**
  - single-module designs only, so hierarchy and instances are refused;
  - the optimised IR and the printed SV;
  - the fixed list of 327 required IP commands.

  A U0 observation on the `poc` branch counted 0 strict-counted rows out of 79. Nothing here is "327 supported" or "strict complete".
- **Not included:** the U1 strict entry, which returns only the module it verified. That is `Tools/VedU1{Contract,Entry,Deep}.lean` on `par/ved-plan` `e2186481`. It relies on the `poc` compiler's `synthesizeEntry`, and it is a follow-up PR.

## Measured (cluster node mkvs-dell, `-c 8 -m 24Gi`, no cache, one run, job `ved-main-93c2` at `93c2f811`)

| Target | Wall |
|---|---|
| `Tools.DeepElab` (with its closure) | 498 s |
| `Tools.VedStrictAudit` | 8 s |
| `Tests.Ved.StrictAuditCheck` | 9 s |
| `Tests.Verification.ValueParamInitRepro` | 15 s |
| `Tests.Verification.ConeSharingGen` | 39 s |
| `Tests.Verification.DeepElabReifyDemo` | 77 s |
| `Tests.Verification.ConeSharingCrc16` | 110 s |
| `Tests.Verification.DeepElabRealIP` | 298 s |

- All five regression files pass on this branch.
- On `poc` (`09621708`), four of them fail: `DeepElabReifyDemo`, `ConeSharingGen`, `ConeSharingCrc16` and `DeepElabRealIP`. `Tools/DeepElab.lean` is unchanged since `df5f0b09`, so those failures come from later `poc` compiler changes. They must be fixed, or explicitly decided, before the `poc` compiler is brought to main.

## Generated output changes against main

The backend files in the closure carry two fixes from `poc`. They change generated output, deliberately. Measured by building `main`'s CI generators on both commits and comparing byte for byte (jobs `ved-cap-main-1614` and `ved-cap-br-b927`, each also reproducing its earlier hash run):

- **Unchanged:** 13 of the 43 files in `.lake/build/gen`. `cuda/symbolic_xor_w17_command.cu` is written only by the CUDA step.
- **`.sv`, 10 files.** The only changes:
  - the NOT mask is printed as a sized literal (`1'd1` instead of `1'(1)`);
  - temporaries are renumbered in `cavlc_synth`, `frame_encoder` and `mp4_encoder`;
  - in those three, two assignments of a narrower value to a 6-bit net gain an explicit zero-extension cast (`6'(_gen_zlMinus1)`).

  None of these changes the circuit's function.
- **C simulator models (`*_cppsim.h`, `*_jit.c`), 20 files.** Two behaviour fixes:
  - **Per-cycle reset.** The simulator now applies the register's synchronous reset (`if (rst) q = init`), which the SV always emitted. Before, the C model ignored it.
  - **Exact-width operands.** Operands are masked to their exact width in compare, shift, index and truthiness positions, so an unmasked carry no longer leaks into them. This adds one extra mask on a shift operand in the three CAVLC designs.

  The rest is the same renumbering.

Both fixes bring the C simulator closer to the SV. `main`'s `build.yml` steps pass on this branch. The per-IP function, area and speed comparison belongs to the release gate.

## CI

- **`ved-pr`** runs on pull requests that touch the compiler, the VED tools or their tests. It builds `Tests.Ved.StrictAuditCheck`, `ValueParamInitRepro`, `ConeSharingGen` and `DeepElabReifyDemo`.
- **`ved-full`** runs weekly and on demand. It builds everything in `ved-pr` plus `ConeSharingCrc16` and `DeepElabRealIP`.
- **The release gate is separate** (Issue `sparkle-ved-release-gate`). Release needs per-IP compile and strict-proof results over the fixed 327, timing, memory, circuit size and output identity. It also needs acceptance thresholds agreed with the user. It is not part of either CI job, and this branch is not a release.

## Where the rest is

Nothing below is in this branch, the default build, CI or any import:

| What | Where |
|---|---|
| The shipping-compiler proof work, the FG/general-theorem exploration, and the certified/machine compiler route | `poc/roundtrip-proof` `09621708` (PR #134) |
| The U1 strict entry, the U0 harness and the strict-audit design | `par/ved-plan` `e2186481` |
| The FG certificate-route pilot and its retrospective | `par/fgc-s1` `8cf6beef`, `par/fgc-s3w` `aa46093f`, `par/fgc-retro` `7423e4e1` |
