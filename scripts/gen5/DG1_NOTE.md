# C.DG-1 (Issue sparkle-ledger-dg1): the GeneratedAt requirement after GPFIX

Base f9dbc699 (par/cr4). Ledger: FG 77 / T1 57 (this issue: FG -0 +0 / T1 -0 +0; the reviewer decides any subtraction).

## Result
C.DG-1 = (i) `dataOf` succeeds, (ii) `GenWF d = true`, (iii) `P = genP env₀`; `GeneratedAt` is design text only.
* (iii) holds by definition in every final root that has `P := genGP lvl hs genData₀ env` (GPFIX).
* (i)(ii) are the fields `hdata` / `wf` (and `hshape`) of the `GenData` that C.AC-4 supplies: `genGP_fields` (`Tools/ShippingGen5DG1.lean`)
  gives, from `genGP … c = some p`, the `g` with `genData₀ env E = some g`, `GenWF g.d = true`, `hshape`, `hdata`, `Acc (CallRel K) c`
  and `GeneratedAtK`. So (i)(ii) are not a separate obligation: they are what `ReachCover` (C.AC-4) means.
* No final root has a `GeneratedAt` binder or any of `GeneratedAtK / GenSFacts / GenPGeneratedStmt / GenPPkgStmt / ReachCover /
  ReachEdge` in its statement (scan through `Tools.`/`Sparkle.` definitions, stopping at `genGP`/`genKit`). Nothing in the roots is
  "replaced"; the requirement only shows as the coverage-shaped rows `hpkg` (`T1HypND.pkg`), `hDG_PKGASSIGN` (`stepDec_of_ties`)
  and the conclusion `∃ p, genGP … declName = some p`.
* Glue: `hpkg_tgtRun_of_cover` (hpkg at `Reach := TgtRun genGP declName` from `ReachCover` over the least call-closed set, `Acc`, `DataOk`),
  `pkgAssign_of_cover` (`hDG_PKGASSIGN` from the same coverage). C.AC-4 stays as the premise `hcov`; C.AC-8 (`hacc`) is still a binder
  of the glue (it is derivable only for names where `genGP` is already `some`, via `genS_some_inv`).

## Consequence for the ledger
C.DG-1 collapses into C.AC-4 (+ C.AC-8 and the DataOk row), as GENDATA_COVER_SURVEY §1.1 said. Whether to count that as -1 is the
reviewer's judgment; this issue does not subtract. The coverage itself (C.AC-4) is not supplied: no theorem here produces
`genData₀ E = some g` from a run.

## Check
`Tests/Gen5/DG1Check.lean`: 19 roots listed explicitly (FGLedgerPremisesStmtR/G, fgLedgerPremisesStmtG_of_R, hDT1_of_genGP, the 6 ND
roots + audit, 7 CR4 row roots, hT2Tie_of_genGP, stepDec_of_ties); controls: generic P rejected, hcov-less glue type rejected,
pkg row vs `closes` rejected, scanner sees the vocabulary where it is.
