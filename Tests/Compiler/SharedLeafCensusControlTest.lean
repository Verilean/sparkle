import Tools.ShippingSharedLeafCensus
import Tests.Compiler.SharedLeafMemKidTest

/-! # G8 census controls (scripts/gaps/G8_CENSUS_FREEZE.md, file 2)

The known class members' tops (NOT in the corpus) and their callees, through the same `censusOne` the corpus
chunks use. Every expectation is an assertion: a mismatch is an elaboration error. -/

namespace Tests.Compiler.SharedLeafCensusControlTest
open Lean Meta Elab Command
open Tools.ShippingSharedLeafCensus

/-- Assert one control row: `cls` exactly, and `M` / `Q` verdicts by prefix. -/
def expectRow (c : Name) (cls m q : String) : MetaM Unit := do
  let cache ← newCache
  let r ← censusOne cache c
  logInfo m!"CONTROL {r.text}"
  unless r.cls == cls && r.m.startsWith m && r.q.startsWith q do
    throwError "CONTROL MISMATCH {c}: got {r.text}, expected class {cls}, M:{m}…, Q:{q}…"

run_meta do
  -- positive: each top passes its own class
  expectRow `Tests.Compiler.SharedLeafMemKidTest.topshareM "PARENT" "PASS" "FAIL"
  expectRow `Tests.Compiler.SharedLeafMemKidTest.topshareQ "PARENT" "FAIL" "PASS"

-- Wrappers taken as tops (freeze Amendment 2): `M:FAIL`, and `Q` is `FAIL` or `PASS-noleafcall` (candidate-only, since
-- no class field requires a wrapper to call the shared leaf).
run_meta do
  for c in [`Tests.Compiler.SharedLeafMemKidTest.wrapM, `Tests.Compiler.SharedLeafMemKidTest.wrapM3,
            `Tests.Compiler.SharedLeafMemKidTest.wrapP, `Tests.Compiler.SharedLeafMemKidTest.wrapQ] do
    let cache ← newCache
    let r ← censusOne cache c
    logInfo m!"CONTROL {r.text}"
    unless r.cls == "PARENT" && r.m.startsWith "FAIL" && (r.q.startsWith "FAIL" || r.q == "PASS-noleafcall") do
      throwError "CONTROL MISMATCH {c}: got {r.text}, expected PARENT, M:FAIL…, Q:FAIL… or Q:PASS-noleafcall"

-- The leaves: a LEAF row, a READ-FAIL, or a parent failing both.
run_meta do
  for c in [`Tests.Compiler.SharedLeafMemKidTest.leafM, `Tests.Compiler.SharedLeafMemKidTest.leafP] do
    let cache ← newCache
    let r ← censusOne cache c
    logInfo m!"CONTROL {r.text}"
    unless r.cls == "LEAF" || r.cls == "READ-FAIL" || (r.m.startsWith "FAIL" && r.q.startsWith "FAIL") do
      throwError "CONTROL MISMATCH {c}: got {r.text}, expected LEAF, READ-FAIL or FAIL/FAIL"

end Tests.Compiler.SharedLeafCensusControlTest
