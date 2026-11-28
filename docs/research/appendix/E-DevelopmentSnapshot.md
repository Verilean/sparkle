# Appendix E: development snapshot `d361bf3e` (unmerged, not in the release)

[Back to the research README](../README.md). Generated file; do not edit. Source:
[`data/coverage-327.tsv`](../data/coverage-327.tsv) and
[`data/dev-snapshot-d361.tsv`](../data/dev-snapshot-d361.tsv); generator:
[`scripts/research/coverage_table.py`](../../../scripts/research/coverage_table.py).

> **Status of this page.** Everything here concerns a line of development that is **not merged
> and not part of the first release**. The release is the code `2bcf256b` with the counts of
> [appendix F](F-AllCommandRows.md) (243 / 327). The numbers on this page are never added to,
> or substituted for, those counts. If this snapshot is revised, only this page changes.

## What this snapshot is

| Item | Value |
|---|---|
| Code / harness SHA | `d361bf3eb68a84234989ac7447293706e97313c1` (`d361bf3e`), branch `meas/ved-route-compose` on the public repository. The branch tip is a later commit (`f4195b98`) that changes only a comment in `scripts/ved/u1_run.py`; the measurement is of `d361bf3e` |
| Position | `d361bf3e` is 189 commits beyond the release code `2bcf256b`; it is in no pull request |
| Ledger | `pr20-d361`; the fixed 327 rows x 8 routes (the release measurement has 7 routes; the new one is `u2_hier_compose`) |
| Result | **252 / 327** strict (real IP 177 / 220, regression 75 / 107) |
| Toolchain, inventory | `leanprover/lean4:v4.32.1`; inventory pin `f694355f` (blob `4a5b801f`), as for the release |

## Measurement approval is not implementation acceptance

The project reviewer accepted the 252 / 327 ledger on 2026-11-24 **as a measurement**: the
records are complete (every row on every route has a result line) and the counting rule was
applied as fixed. That acceptance says the *numbers describe what that code and harness did*. It
does **not** accept the implementation (the compose route and its lemmas have not been reviewed
as a pull request), nor performance, nor any optimiser or SystemVerilog guarantee (the ledger
columns read `not-evaluated`). It is also not a release approval. Until the implementation is
reviewed and merged, none of these rows is a result of Sparkle's release.

## The comparison: 243 -> 252 = +9

The two ledgers (`pr16-fb71` at `fb7124fc` and `pr20-d361`) have the same 327 rows. Comparing
them row by row: 243 rows are strict in both; **nine rows are strict only in `pr20-d361`**;
no row that is strict in `pr16-fb71` is lost (`+9 -0`). Hence 243 + 9 = 252; real IP
168 + 9 = 177; regression 75 unchanged. The nine rows include **R34**. The comparison is
243 -> 252 = +9; it is not 244 -> 252 = +8, which starts from a different base.

| Row | Kind | File:line | Declaration | In the release (`2bcf256b`) | Route | Options | Statement | s | MB |
|---|---|---|---|---|---|---|---|---|---|
| R34 | real-ip | `IP/Video/H264/IDCTSynth.lean:269` | `Sparkle.IP.Video.H264.IDCTSynth.idctModule` | refused (u1:multi-output) | `u1_mem_packed` | - | - | 542.4 | 9867 |
| R193 | real-ip | `Tests/IP/Crypto/SHA512BlockHWTest.lean:153` | `synth_sha512Block_out0` | refused (u1:order) | `u2_hier_compose` | `ved.compose.step true`, `ved.compose.connect true`, `sparkle.deepExportState true`, `ved.compose.multiCircuit true` | U2HRStmt registers=true | 247.1 | 8005 |
| R194 | real-ip | `Tests/IP/Crypto/SHA512BlockHWTest.lean:164` | `synth_sha512Block_done` | refused (u1:order) | `u2_hier_compose` | `ved.compose.step true`, `ved.compose.connect true`, `sparkle.deepExportState true`, `ved.compose.multiCircuit true` | U2HRStmt registers=true | 241.8 | 8075 |
| R220 | real-ip | `Tests/IP/Net/HFTStrategyTest.lean:96` | `synth_hftOutByte` | refused (u1:order) | `u2_hier_compose` | `ved.compose.step true`, `ved.compose.connect true`, `sparkle.deepExportState true`, `ved.compose.multiCircuit true` | U2HRStmt registers=true | 26.2 | 2127 |
| R227 | real-ip | `Tests/IP/Net/ICMPTest.lean:148` | `synth_icmpResponderByte` | refused (u1:order) | `u2_hier_compose` | `ved.compose.step true`, `ved.compose.connect true`, `sparkle.deepExportState true`, `ved.compose.multiCircuit true` | U2HRStmt registers=true | 55.3 | 3729 |
| R230 | real-ip | `Tests/IP/Net/IPv4Test.lean:153` | `synth_ipv4TxByte` | refused (u1:order) | `u2_hier_compose` | `ved.compose.step true`, `ved.compose.connect true`, `sparkle.deepExportState true`, `ved.compose.multiCircuit true` | U2HRStmt registers=true | 71.3 | 2879 |
| R231 | real-ip | `Tests/IP/Net/IPv4Test.lean:161` | `synth_ipv4RxSrcIp` | refused (u1:order) | `u2_hier_compose` | `ved.compose.step true`, `ved.compose.connect true`, `sparkle.deepExportState true`, `ved.compose.multiCircuit true` | U2HRStmt registers=true | 44.7 | 2783 |
| R232 | real-ip | `Tests/IP/Net/IPv4Test.lean:169` | `synth_ipv4RxHeaderOk` | refused (u1:order) | `u2_hier_compose` | `ved.compose.step true`, `ved.compose.connect true`, `sparkle.deepExportState true`, `ved.compose.multiCircuit true` | U2HRStmt registers=true | 53.7 | 2779 |
| R246 | real-ip | `Tests/IP/Net/UsbWebServerSynth.lean:22` | `Sparkle.Tests.IP.Net.UsbWebServerSynth.synth_usbWebServer` | refused (u1:order) | `u2_hier_compose` | `maxHeartbeats 4000000`, `ved.compose.step true`, `ved.compose.connect true`, `sparkle.deepExportState true`, `ved.compose.multiCircuit true` | U2HRStmt registers=true | 192.4 | 4157 |

How to read the columns. *Route* is the route whose run proved the row. *Options* are the Lean
options that must be set for that run (`-` means none; R34 needs no option, it is proved by an
existing route at the later code). *Statement* is the statement kind the route expected.
*Time* and *Peak MB* are those of the proving route's single run, including loading imports.
The eight `u2_hier_compose` rows use the route's four options; R246 additionally needs a raised
`maxHeartbeats` (4000000). The options turn on the compose route; the defaults are unchanged.
All nine rows are **refused** in the release table ([appendix F](F-AllCommandRows.md)), which
is correct for `2bcf256b`.

## Harness and options

* Harness: `scripts/ved/u1_run.py` and `u1_gen.py` of `meas/ved-route-compose` (route
  `u2_hier_compose`, base route `u2_hier`, `VED_STAGE_STAMPS=1`); the compose options are set
  only on the `u2_hier_compose` records.
* Options used by the eight compose rows: `ved.compose.step`, `ved.compose.connect`,
  `sparkle.deepExportState`, `ved.compose.multiCircuit`, all `true`.
* Each row's result record carries the source SHA, the harness hash and the case hash; the
  ledger's per-row evidence is not part of this tree.

## Reproduction path

1. `git fetch origin meas/ved-route-compose` and check out `d361bf3e` (or the branch tip; the
   difference is one comment).
2. Run the harness as in [C-Reproduction.md](C-Reproduction.md), using the rows and route of the
   table above (`u1_mem_packed` for R34; `u2_hier_compose` with the options for the others).
   The nine cases take from under one minute to about nine minutes each (table), at up to
   10 GB peak memory; they were not re-run for this page.
3. Compare with the ledger rows: strict means the same declaration, the same run's returned IR,
   the exact statement type, only the three standard axioms, and all outputs.

The ledger generator and its directory are not in this tree; the TSV above is derived from
them (see [C-Reproduction.md](C-Reproduction.md)).

## What this page does not say

* It does not say the release contains these nine rows: it does not.
* It does not say that the compose route is correct or reviewed.
* It says nothing about the single local runs of the nested-hierarchy route (rows R163, R164):
  those are not ledger rows and are described only in
  [PerCircuitVerification.md](../PerCircuitVerification.md#6-not-in-this-release-not-counted).
