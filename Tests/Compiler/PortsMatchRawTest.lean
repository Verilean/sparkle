import Tools.ShippingPortsMatchRaw

/-! # `portsMatchB` of the raw full-entry module: axiom audit (G1, round optfb-7)

The general theorems of `Tools/ShippingPortsMatchRaw.lean` use the standard
axioms only (an error otherwise). The instance on `parent`, with its data
condition decided, is in `Tests/Compiler/PortsMatchRawParentTest.lean` (a
separate file: a failing `decide` there does not hide this audit).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.PortsMatchRawTest

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in [``Tools.ShippingPortsMatchRaw.callStmtG_conn,
      ``Tools.ShippingPortsMatchRaw.callArgs_width,
      ``Tools.ShippingPortsMatchRaw.core_callConns,
      ``Tools.ShippingPortsMatchRaw.core_portsMatch_raw] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"PORTSMATCHRAW: callStmtG_conn, callArgs_width, core_callConns, core_portsMatch_raw — standard axioms only"

end Tests.Compiler.PortsMatchRawTest
