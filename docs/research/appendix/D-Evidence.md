# Appendix D: evidence behind the numbers

[Back to the research README](../README.md).

## Which approved measurement backs which number

| Number | Code | Measurement | Approval |
|---|---|---|---|
| **243 / 327** (real IP 168 / 220, regression 75 / 107) | `2bcf256b` (PR #163 head) | ledger `pr16-fb71`, measured at `fb7124fc`, which is `2bcf256b` plus the harness only (`git diff --stat 2bcf256b fb7124fc` touches only `scripts/ved/`), 7 routes | approved 2026-11-19 in the measurement issue `sparkle-ved-cand-measure14` of the project tracker: "approved: same-SHA measurement of pr16, 243/327 (real IP 168/220, regression 75/107), +9 −0" (translated). Caveat recorded there: the reviewer could not re-check the checksum list independently |
| 43 / 327 | `d331ff24` (earlier candidate) | full baseline, 6 routes | the baseline of the ledger |

The code SHA and the measured SHA are two commits: `fb7124fc` is `2bcf256b` plus the harness
(27 files, all under `scripts/ved/`). The approval is of the measurement taken at `fb7124fc`; it
applies to the release code `2bcf256b` because the diff between the two is the harness only.

The "+9 −0" in the quoted approval is that issue's own comparison with its earlier measurement.
It is **not** the 243 -> 252 = +9 comparison of the development snapshot, which is a different
measurement of different code; that snapshot (`d361bf3e`, unmerged, 252 / 327), its approval
as a *measurement only*, and its row-by-row check are in
[E-DevelopmentSnapshot.md](E-DevelopmentSnapshot.md). Nothing from it is counted here.

## The 243 strict rows by review record

| Record | Rows |
|---|---|
| already strict at the earlier baseline `d331ff24` | 43 |
| a separate reviewer-approved measurement of an earlier SHA exists | 42 |
| strict in this measurement only, with no separate review record of the row | 158 |

The 42 rows with an earlier approval come from these tracker issues (internal names; number of
rows): `sparkle-ved-u1-multiloop` 26, `sparkle-ved-eq-wide` 11, `sparkle-ved-u1-multiloop-rest` 2,
`sparkle-ved-hier-evalbudget` 1, `sparkle-ved-hier2-h2c` 1, `sparkle-ved-hier-budget` 1. The
`provenance` column of [data/coverage-327.tsv](../data/coverage-327.tsv) gives the class per row.

## What the ledger does not evaluate

The columns "optimiser / SV guarantee" and "performance accepted" read `not-evaluated` for every
row. The ledger counts a row once however many routes prove it, never adds a child's leaf proof
to its wrapper row, and fixes "real IP" to files under `IP/` or `Tests/IP/` (220 rows); an earlier
225 / 102 split could not be reproduced from the records.

Ten records resolved a command name to a declaration in another namespace (rows R33 and R35 on
five routes each); these are never counted as strict.

## Work in progress (not evidence for any number)

Single local runs (nested-hierarchy rows, P-256 point-operation traces) are not ledger rows and
have no review record. They are described, with their labels, only in
[PerCircuitVerification.md, section 6](../PerCircuitVerification.md#6-in-progress-not-in-this-release-not-reviewed).
