# SRM6 B1 — consumers of `designCheck` / `kidsPass` / `kidCheck`: classification

Machine part: `python3 -I scripts/srm6/inventory.py Tools > scripts/srm6/inventory.tsv` (text-level scan of `Tools/*.lean` minus Srm5/Srm6 files;
output committed: `inventory.tsv`, `inventory.summary`: 91 files, 184 declarations). NOT elaborated: it sees syntactic mentions only. Its rule-based class
column is: A (restatable: only text/inst/leaf facts of ONE level, no depth tie), B (needs the uniform depth: mentions `KSn`/`DesignSV`/`SVBounds`/`InvN`/`induction`),
C (rule cannot decide), P (producer: concludes a uniform check; the SRM5 producers `topshare*_hcheck` replace them, they are not consumers).
Counts (see inventory.summary): CONSUMER A 6 / B 31 / C 14; TRANSFORMER A 11 / B 2 / C 43; PRODUCER 28; DEF 49.

Hand reading of the semantic chain (this is the ONLY part that is hand-written; each line was read in the source):

| declaration (Tools/…) | what it USES of the uniform check | class |
|---|---|---|
| `ShippingDesignSV.kidsPass_at` | one instance edge: `kidsPass C f body = true` ⟹ `f child = true` | A (`hcheck_succ_iff` gives the same edge fact) |
| `ShippingDesignSV.textCheckI_sound` | text conjunct only | A (`hcheck` contains `textCheckI` at every positive rank) |
| `ShippingDesignSV.design_sv_runN` | text conjunct (`hchk.1`), instance resolution (`Resolved`), kid edge (`kidsPass_at hchk.2`) fed to the IH at depth `n-1`, and at depth 0 `leafCheck` of the kid | **B**: the IH is at `n-1` for EVERY kid (`DesignSV C n` ↔ `designCheck C n`, `KSn C n`), and `DesignSV C 0` wants `LeafRun` for every kid, `DesignSV C (m+1)` wants `TextRun` of the kid (false for a built memory module: `kidCheck_memModule_succ`). **Restated here as `design_sv_runH`** (ShippingSrm6Sem). |
| `ShippingDesignSVBounds.svBounds_of_checks`, `moduleStepBound` | text conjunct + kid edge at depth `n-1` to derive `SVBounds` from the checks | B (same recursion). NOT restated: `SVBoundsH` stays a PREMISE of `design_sv_runH`. |
| `ShippingDesignSVBack.design_sv_backN`, `design_sv_unique`, `design_sv_all` | converse simulation (`outsCheck` + `designCheck`) | B. NOT restated (OPEN). |
| `ShippingShipsDesignSV.ships_design_svN/svH(_all)` | `designCheck … n (checkedOptimize b)` hypothesis + `InvN` at depth `n` + `design_sv_runN` | B (calls `design_sv_runN`; `InvN`/`Reset` are uniform-depth state invariants). NOT restated (OPEN). |
| `ShippingOneOutHead.machine_design_svH_free`, `ShippingNoPorts*.machine_design_noPorts*`, `ShippingShipsNoOuts.*`, `ShippingSeqParent*.machine_design_*`, `ShippingGateDesign*` | the endpoint family: one `designCheck … n` hypothesis then `ships_design_sv*` | B (endpoint; every one passes through `design_sv_runN` and `InvN C n`). NOT restated (OPEN). |
| `ShippingChecksDesign.designCheck_eq`, `core_designCheck_rest`, `ShippingTextShipped.core_designCheck_rest2/run(_ran)`, `ShippingOneOutKid*.core_designCheck_in*`, `ShippingParentDesignA.core_designCheckHA`, `ShippingSeqChildDeep*` | PRODUCERS/TRANSFORMERS of the uniform check from the run's facts (`kidCheck C n`) | P: replaced for the instances by `topshareM_hcheck`/`topshareQ_hcheck` (SRM5), not consumers. |
| `ShippingDesignSVMem.designCheck_memKids`, `kidsPass_memKids` | a parent whose kids are ALL built memory modules | A/P; SRM5's `hcheck_memKids` is its height analogue. |

Smallest chain from the parent check to the semantic statement used by the memory parents: `design_sv_runN` only (everything else in the table is a producer, a
bounds derivation, a converse, or an endpoint wrapper that calls it). Chosen for restatement: `design_sv_runN` → `design_sv_runH`.
