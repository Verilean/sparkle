import Tests.AllTests
import Tools.ShippingDesignCoverage

/-! # The design-level coverage census of `Tests.AllTests`' environment (round par/b-34)

WRITTEN, NOT BUILT. TARGET-ONLY — never in `Tests/AllTests.lean` (it imports it).

`#design_coverage` (`Tools/ShippingDesignCoverage.lean`) scans this file's
environment — everything `Tests.AllTests` imports — and LOGS, per
declaration with a machine / gate artifact, whether a check-free
design-level endpoint exists (re-checked on its stored statement) or why
not. It adds nothing, asserts nothing and expects nothing: the predictions
are in `docs/parallel/B-coverage-census.md`, labelled PREDICTED.

    grep -E "DESIGN COVERAGE (START|SCAN|TOTALS)|COVERAGE ROW"

Declarations whose endpoints are generated only in target-only files (not
imported by `Tests.AllTests`) are NOT in this census: import those files
here as well to include them (mind name clashes between a generator file
and the hand test of the same declaration). -/

set_option maxHeartbeats 0 in
#design_coverage
