#!/usr/bin/env python3
"""Generate docs/research/Coverage327.md (summary by circuit family),
docs/research/appendix/F-AllCommandRows.md (all 327 rows) and docs/research/appendix/E-DevelopmentSnapshot.md.

Coverage327.md comes from docs/research/data/coverage-327.tsv and describes the release
snapshot only (code 2bcf256b, measured at fb7124fc). appendix/E-DevelopmentSnapshot.md comes
from the same TSV plus docs/research/data/dev-snapshot-d361.tsv (the nine rows that the
unmerged development snapshot d361bf3e adds) and is kept apart so that its counts never enter
the main table.

Run from anywhere:  python3 -I scripts/research/coverage_table.py [--check]

Writes both pages. With --check it writes nothing and exits 1 when either file on disk differs
from what would be generated (used by the checks in
docs/research/appendix/C-Reproduction.md). The summary counts are computed from the TSV, not
typed in; they must equal LEDGER.md of the approved ledger (243 / 168 / 75).
"""
import csv
import os
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
TSV = os.path.join(ROOT, "docs", "research", "data", "coverage-327.tsv")
OUT = os.path.join(ROOT, "docs", "research", "Coverage327.md")
ALL_OUT = os.path.join(ROOT, "docs", "research", "appendix", "F-AllCommandRows.md")
DEV_TSV = os.path.join(ROOT, "docs", "research", "data", "dev-snapshot-d361.tsv")
DEV_OUT = os.path.join(ROOT, "docs", "research", "appendix", "E-DevelopmentSnapshot.md")

# Provenance of the table (facts re-checked against the ledger VERSIONS.txt / LEDGER.md).
SNAPSHOT = "2bcf256b"
MEASURED = "fb7124fc6620951f00e84d861da759231704b276"
DEV_SNAPSHOT = "d361bf3eb68a84234989ac7447293706e97313c1"
DEV_EXPECT = {"strict": 252, "real-ip": 177, "regression": 75, "added": 9}
EXPECT = {"strict": 243, "real-ip": (168, 220), "regression": (75, 107), "total": 327}

FAMILIES = [
    ("Finite-field and modular arithmetic",
     "multipliers, modular inverse and field towers for the P-256, secp256k1, Ed25519, BLS12-381 and Goldilocks fields"),
    ("Elliptic-curve point operations and pairings",
     "one point double-or-add, scalar multiplication, pairing steps"),
    ("Signature engines and signing demos",
     "ECDSA and Ed25519 signers, BIP-32 key derivation, signing demos"),
    ("Hash functions, MACs and key derivation",
     "SHA-256, SHA-512, Keccak-256, HMAC, HKDF, Merkle trees"),
    ("Block cipher and authenticated encryption",
     "AES, AES-GCM, GHASH"),
    ("Blockchain transaction encoding",
     "RLP, EIP-1559 envelope, transaction policy"),
    ("Network packet parsers and protocol state machines",
     "Ethernet, ARP, IPv4, ICMP, TCP, HTTP, SLIP, CRC-32, UART, market-data quote and strategy blocks"),
    ("Field buses and serial links",
     "CAN, CANopen, DroneCAN, I2C, SPI, LIN, MIL-STD-1553, SBUS, CRSF, PCIe, USB"),
    ("Controllers and filters",
     "PID, LQR, observer, IIR biquad, precision sweeps"),
    ("Processor and SoC building blocks",
     "RV32 core, pipeline, CSR, MMU, CLINT, UART, divider, AXI4-Lite, arbiter, SoC top"),
    ("Video codec (H.264)",
     "DCT, quantisation, entropy coding, NAL packing, encoder and decoder tops"),
    ("Neural-network accelerator (YOLOv8)",
     "convolution engine, activation, pooling, residual blocks, backbone, neck, head, top"),
    ("Language, compiler and example regressions",
     "tests of the Signal DSL and the compiler, tutorial and example circuits"),
]


def family(file):
    base = file.split("/")[-1]
    if file.startswith("Tests/IP/Crypto/") or file.startswith("IP/Crypto/"):
        for key, fam in (("Eip1559", 5), ("RLP", 5), ("TxPolicy", 5),
                         ("AES", 4), ("GHASH", 4),
                         ("PointOp", 1), ("ScalarMul", 1), ("BLS12", 1),
                         ("SignDemo", 2), ("ECDSA", 2), ("Ed25519Sign", 2), ("BIP32", 2),
                         ("SHA", 3), ("HMAC", 3), ("HKDF", 3), ("Keccak", 3), ("Merkle", 3),
                         ("Field", 0), ("Order", 0), ("ModInv", 0), ("Goldilocks", 0),
                         ("Fp", 0)):
            if key in base:
                return fam
        raise ValueError(file)
    if file.startswith("Tests/IP/Net/"):
        return 6
    if file.startswith("Tests/IP/Bus/") or file.startswith("Tests/IP/USB/"):
        return 7
    if file.startswith("Tests/IP/Control/"):
        return 8
    if file.startswith("IP/RV32/") or file.startswith("IP/Bus/") or file.startswith("IP/Arbiter/"):
        return 9
    if file.startswith("IP/Video/"):
        return 10
    if file.startswith("IP/YOLOv8/"):
        return 11
    return 12


COMMON = """\
**What a row is.** The fixed inventory contains **327 command rows**: `#synthesizeVerilog`,
`#writeDesign` and similar commands in 136 files. They are **not 327 IPs**: one IP can own
several rows, and a row counts once however many routes prove it. A child leaf proof is never
added to its wrapper row. "Real IP" means the file lives under `IP/` or `Tests/IP/` (220 rows);
every other row is a "regression" row (107 rows: examples, tests, tutorial files).

**What "strict" means.** The original declaration, the *same run's returned IR*, the exact
statement type, only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and all
outputs. It is rung 2 of the [guarantee ladder](README.md#the-guarantee-ladder): it says
nothing about the optimiser, the printed SystemVerilog or performance (those columns of the
ledger read "not-evaluated").
"""

HEADER = """\
# What is covered: results by circuit family (release snapshot)

> Generated file. Do not edit. Source: [`data/coverage-327.tsv`](data/coverage-327.tsv);
> generator: [`scripts/research/coverage_table.py`](../../scripts/research/coverage_table.py).
> Regenerate with `python3 -I scripts/research/coverage_table.py`. The complete row-by-row
> table, with row numbers, files and every condition, is
> [appendix F](appendix/F-AllCommandRows.md).

""" + COMMON + """
## Results by circuit family

A row is *strict* when the checker returned a kernel-checked theorem for it, and *not strict*
when it refused (no claim) or could not be run. The last column is the stage at which the most
rows of the family were stopped on the main route; the stage names are explained below.

{families}

## Summary (computed from the TSV)

{summary}

## How to read the stage names

The stage is the point of the entry's refusal pipeline at which the entry stopped. `proof`: the
generated proof did not check within the fixed budgets (the common case for large arithmetic
cones). `multi-output` and `packed`: the result shape (several outputs, a tuple) is not one the
route handles. `table`: the declaration shape is not one the port table can read. `order`: no
well-ordered arrangement of the body exists (for example a combinational cycle). `hier-shape`,
`scope`, `conns`, `open`: obligations of hierarchies (instances) that the route does not cover.
`shape`: a memory shape that is not supported. `signal`: the process ended by a signal.
`prep`: the preparation command of the deep route did not succeed. `external-timeout`: the harness
time limit. `case-error`, `unsupported-invocation`, `source-missing`: the row could not be driven
by the route (a Lean error outside the checked block, a command form the route cannot drive, a
declaration that cannot be resolved). The complete definitions are
in [appendix F](appendix/F-AllCommandRows.md#how-to-read-the-table).

## Which code these numbers are for

The commits (code, measurement, earlier baseline, `main`) are listed in the
[snapshot box](README.md#snapshot-box) of the overview and in the provenance table of
[appendix F](appendix/F-AllCommandRows.md#provenance).

A later, unmerged development snapshot is kept on its own page,
[appendix/E-DevelopmentSnapshot.md](appendix/E-DevelopmentSnapshot.md). Nothing from it is counted
in this page, and nothing on this page changes if it is revised.
"""

ALL_HEADER = """\
# Appendix F: all 327 command rows (snapshot `{snap}`)

[Back to the family summary](../Coverage327.md). Generated file; do not edit. Source:
[`data/coverage-327.tsv`](../data/coverage-327.tsv); generator:
[`scripts/research/coverage_table.py`](../../../scripts/research/coverage_table.py).
Regenerate with `python3 -I scripts/research/coverage_table.py`. Search this page for a file
name, a declaration or a row number (`R178`).

""" + COMMON.replace("](README.md", "](../README.md") + """
## Provenance

| Item | Value |
|---|---|
| Code SHA | `{snap}`: PR #163 head (branch `ved/consolidated-1`). This is the code the release contains |
| Measured SHA | `{measured}` (`fb7124fc`), branch `meas/ved-pr16-fb71`. This is the commit the harness ran on. It is **a different commit** from the code SHA |
| Relation | `git diff --stat 2bcf256b fb7124fc` touches 27 files, all under `scripts/ved/` (the measurement harness, commit `ffea8b85`); nothing under `Sparkle/`, `Tools/`, `Tests/`, `IP/` or the lakefile. The numbers are therefore read as numbers for the code `2bcf256b`. If any later change enters the release candidate, its diff must be checked: a change of meaning or of proof generation does not inherit this coverage, only a change that leaves what a route accepts untouched (documentation, harness, CI scripts) can |
| Ledger | `pr16-fb71`, the approved ledger of the measurement at `fb7124fc`; generator `gen_ledger.py`, sha256 `6eb49c7e...` (not in this tree) |
| Inventory | pin `f694355f` (blob `4a5b801f`) |
| Toolchain | `leanprover/lean4:v4.32.1` |
| Routes | `u1`, `u1_deep`, `u1_deep_ns`, `u1_hier`, `u1_packed`, `u2_hier`, `u1_mem_packed` (7) |
| Approval | the count was approved by the project reviewer in the measurement issue (2026-11-19); the reviewer noted that the checksum list could not be re-checked independently |

The harness and the ledger generator are not part of this release tree. How to regenerate the
data from the public measurement branch is described in
[C-Reproduction.md](C-Reproduction.md); the approval records are summarised in
[D-Evidence.md](D-Evidence.md).

## Other columns, kept separate

These are **not** part of the numbers of the summary page.

| Column | Code | Result | Status |
|---|---|---|---|
| This release | code `{snap}`, measured at `fb7124fc` | 243 / 327 | approved ledger (reviewer, 2026-11-19) |
| Earlier baseline | `d331ff24` (an earlier VED candidate, not `main`) | 43 / 327 | approved baseline of the ledger |
| `main` before the release | `6c29b9b8` | no same-SHA row-by-row measurement in this release | that `main` had the deep route and the basic `#ved_u1` entry; it lacked the packed, hierarchy and `#ved_write_checked` entries of this snapshot. Current `main` contains them and is not measured here |

{routes}

## How to read the table

* **Status.** `strict`: proved on at least one route. `refused`: every route that ran refused or
  failed; the row carries **no claim**. `unmeasured`: the row could not be run on any route
  (listed separately below); it stays in the denominator.
* **Route.** For a strict row, the first route that proved it. For a refused row, the first route
  that ran; its time and memory are in the last two columns. Time and memory are those of one
  route's run (including loading imports), not of the proof alone.
* **Conditions.** The statement kind a route expected, when the ledger records one (`U2HRStmt`,
  `U2HStmt`); `-` means none recorded. The ledger of this snapshot records no non-default Lean
  options.
* **First blocker per route.** `route:cause` for each of the 7 routes, shown for refused and
  unmeasured rows. The causes are the harness's classification of the first thing that stopped
  that route. Informally: `prep` the preparation command `#verify_elab_deep` did not succeed (deep
  routes only); `table`, `multi-output`, `packed`, `hier-shape`, `shape`, `order`, `scope`,
  `conns`, `open`, `deep`, `proof` are the stage of the entry's refusal pipeline at which the
  entry refused (`VED U1 REFUSED f [stage]`); `signal` the process ended by a signal without
  recorded evidence of memory exhaustion; `external-timeout` the harness time limit; `case-error`
  Lean errors outside the checked block; `unsupported-invocation` the command form cannot be
  driven by the route; `source-missing` the row's declaration cannot be resolved at this SHA.
  The authoritative list is the pipeline in `scripts/ved/u1_gen.py` on `fb7124fc`.
* **Provenance of a strict row.** `baseline-strict`: strict already at the earlier baseline
  `d331ff24`; `approved-earlier-sha`: a reviewer-approved measurement of an earlier SHA exists;
  `measured-only`: strict in this measurement, with no separate review record of the row.

## Unmeasured rows ({n_unm})

{unmeasured}

## All 327 rows

{table}
"""


def load():
    with open(TSV, newline="") as f:
        return list(csv.DictReader(f, delimiter="\t"))


def md(s):
    return s.replace("|", "\\|")


def summary(rows):
    n = len(rows)
    st = [r for r in rows if r["status"] == "strict"]
    ref = [r for r in rows if r["status"] == "refused"]
    unm = [r for r in rows if r["status"] == "unmeasured"]
    out = ["| | strict | refused | unmeasured | total |", "|---|---|---|---|---|"]
    for label, pred in (("real IP", lambda r: r["kind"] == "real-ip"),
                        ("regression", lambda r: r["kind"] == "regression"),
                        ("**all**", lambda r: True)):
        sub = [r for r in rows if pred(r)]
        c = Counter(r["status"] for r in sub)
        out.append(f"| {label} | {c['strict']} | {c['refused']} | {c['unmeasured']} | {len(sub)} |")
    out += ["", "Stage that stopped the main route first, for the not-strict rows:", "",
            "| cause | rows |", "|---|---|"]
    cause = Counter()
    for r in ref + unm:
        first = r["blockers"].split(";")[0]
        cause[first.split(":", 1)[1]] += 1
    for k, v in sorted(cause.items(), key=lambda kv: (-kv[1], kv[0])):
        out.append(f"| `{k}` | {v} |")
    assert n == EXPECT["total"], n
    assert len(st) == EXPECT["strict"], len(st)
    for kind in ("real-ip", "regression"):
        s = sum(1 for r in st if r["kind"] == kind)
        t = sum(1 for r in rows if r["kind"] == kind)
        assert (s, t) == EXPECT[kind], (kind, s, t)
    return "\n".join(out)


def route_detail(rows):
    st = [r for r in rows if r["status"] == "strict"]
    out = ["Strict rows by the proof routes that proved them (route names are the harness's):", "",
           "| routes | rows |", "|---|---|"]
    for k, v in sorted(Counter(r["strict_routes"] for r in st).items(), key=lambda kv: (-kv[1], kv[0])):
        out.append(f"| `{k}` | {v} |")
    out += ["", "Strict rows by provenance:", "", "| provenance | rows |", "|---|---|"]
    for k, v in sorted(Counter(r["provenance"] for r in st).items()):
        out.append(f"| {k} | {v} |")
    return "\n".join(out)


def families(rows):
    out = ["| Circuit family | What is in it | Rows | Strict | Not strict | Most common stopping stage |",
           "|---|---|---|---|---|---|"]
    for i, (name, what) in enumerate(FAMILIES):
        sub = [r for r in rows if family(r["file"]) == i]
        st = sum(1 for r in sub if r["status"] == "strict")
        cause = Counter(r["blockers"].split(";")[0].split(":", 1)[1] for r in sub if r["status"] != "strict")
        top = ", ".join(f"`{k}` ({v})" for k, v in cause.most_common(2)) or "-"
        out.append(f"| {name} | {what} | {len(sub)} | {st} | {len(sub) - st} | {top} |")
    assert sum(1 for r in rows) == EXPECT["total"]
    return "\n".join(out)


def short(decl):
    return decl.replace("_private._stdin.0.", "")


def unmeasured(rows):
    out = ["| Row | File:line | Why |", "|---|---|---|"]
    for r in rows:
        if r["status"] == "unmeasured":
            why = r["blockers"].split(";")[0].split(":", 1)[1]
            out.append(f"| R{r['row']} | `{r['file']}:{r['line']}` | `{why}` on all routes |")
    return "\n".join(out)


def table(rows):
    out = ["| Row | Kind | File:line | Command | Declaration | Status | Route | Conditions | "
           "First blocker per route | s | MB |",
           "|---|---|---|---|---|---|---|---|---|---|---|"]
    for r in rows:
        bl = "" if r["status"] == "strict" else md(r["blockers"].replace(";", "; "))
        route = r["route"]
        if r["status"] == "strict":
            route = r["strict_routes"] if "+" in r["strict_routes"] else route
        out.append("| " + " | ".join([
            f"R{r['row']}", r["kind"], f"`{r['file']}:{r['line']}`", f"`{r['command']}`",
            f"`{short(r['declaration'])}`" if r["declaration"] else "", r["status"],
            f"`{route}`" if route else "", md(r["conditions"]), bl,
            r["wall_s"], r["peak_rss_mb"]]) + " |")
    return "\n".join(out)


def render():
    rows = load()
    return HEADER.format(snap=SNAPSHOT, families=families(rows), summary=summary(rows))


def render_all():
    rows = load()
    return ALL_HEADER.format(snap=SNAPSHOT, measured=MEASURED, routes=route_detail(rows),
                             unmeasured=unmeasured(rows),
                             n_unm=sum(1 for r in rows if r["status"] == "unmeasured"),
                             table=table(rows))


DEV_HEADER = """\
# Appendix E: development snapshot `d361bf3e` (unmerged, not in the release)

[Back to the research README](../README.md). Generated file; do not edit. Source:
[`data/coverage-327.tsv`](../data/coverage-327.tsv) and
[`data/dev-snapshot-d361.tsv`](../data/dev-snapshot-d361.tsv); generator:
[`scripts/research/coverage_table.py`](../../../scripts/research/coverage_table.py).

> **Status of this page.** Everything here concerns a line of development that is **not merged
> and not part of the first release**. The release is the code `{snap}` with the counts of
> [appendix F](F-AllCommandRows.md) (243 / 327). The numbers on this page are never added to,
> or substituted for, those counts. If this snapshot is revised, only this page changes.

## What this snapshot is

| Item | Value |
|---|---|
| Code / harness SHA | `{dev}` (`d361bf3e`), branch `meas/ved-route-compose` on the public repository. The branch tip is a later commit (`f4195b98`) that changes only a comment in `scripts/ved/u1_run.py`; the measurement is of `d361bf3e` |
| Position | `d361bf3e` is 189 commits beyond the release code `{snap}`; it is in no pull request |
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

{table}

How to read the columns. *Route* is the route whose run proved the row. *Options* are the Lean
options that must be set for that run (`-` means none; R34 needs no option, it is proved by an
existing route at the later code). *Statement* is the statement kind the route expected.
*Time* and *Peak MB* are those of the proving route's single run, including loading imports.
The eight `u2_hier_compose` rows use the route's four options; R246 additionally needs a raised
`maxHeartbeats` (4000000). The options turn on the compose route; the defaults are unchanged.
All nine rows are **refused** in the release table ([appendix F](F-AllCommandRows.md)), which
is correct for `{snap}`.

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
  [PerCircuitVerification.md](../PerCircuitVerification.md#6-in-progress-not-in-this-release-not-reviewed).
"""


def dev_render():
    rows = load()
    byrow = {int(r["row"]): r for r in rows}
    with open(DEV_TSV, newline="") as f:
        dev = list(csv.DictReader(f, delimiter="\t"))
    assert len(dev) == DEV_EXPECT["added"], len(dev)
    # the d361 total is the release total plus exactly these rows, all refused in the release table
    st = sum(1 for r in rows if r["status"] == "strict")
    assert st + len(dev) == DEV_EXPECT["strict"], st
    nreal = sum(1 for r in rows if r["status"] == "strict" and r["kind"] == "real-ip")
    assert nreal + sum(1 for d in dev if byrow[int(d["row"])]["kind"] == "real-ip") == DEV_EXPECT["real-ip"]
    out = ["| Row | Kind | File:line | Declaration | In the release (`" + SNAPSHOT + "`) | Route | Options | Statement | s | MB |",
           "|---|---|---|---|---|---|---|---|---|---|"]
    for d in dev:
        n = int(d["row"])
        r = byrow[n]
        assert r["status"] == "refused", n
        out.append(f"| R{n} | {r['kind']} | `{r['file']}:{r['line']}` | `{short(r['declaration'])}` | "
                   f"refused ({r['blockers'].split(';')[0]}) | `{d['route']}` | "
                   f"{'`' + d['lean_options'].replace(';', '`, `') + '`' if d['lean_options'] else '-'} | "
                   f"{d['statement']} | {d['wall_s']} | {d['peak_rss_mb']} |")
    return DEV_HEADER.format(snap=SNAPSHOT, dev=DEV_SNAPSHOT, table="\n".join(out))


def main():
    outs = [(OUT, render()), (ALL_OUT, render_all()), (DEV_OUT, dev_render())]
    if "--check" in sys.argv:
        for path, text in outs:
            try:
                with open(path, newline="") as f:
                    if f.read() != text:
                        sys.exit(1)
            except FileNotFoundError:
                sys.exit(1)
        sys.exit(0)
    for path, text in outs:
        with open(path, "w", newline="") as f:
            f.write(text)


if __name__ == "__main__":
    main()
