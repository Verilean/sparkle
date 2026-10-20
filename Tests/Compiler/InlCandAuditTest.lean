import Tools.ShippingP5Forall
import Tests.Compiler.NoPortsTest

/-! # Audit of the ISOLATED inliner candidate (review a230f9d1: U1c + U3 + L2 + U5a)

No production change: `userInlinerC` is a Tools-only copy; production `userInliner` is untouched.
Asserted: the forward one-Signal result-kind preservation (L2) and `P5AtC` (U5a) use only the standard
axioms. Their premises are explicit: `ReadConstsPlain` / `ReadConstsAt` (six `userAbbrev? env c = none`
facts — LOCALISED, not proved) and `ResDeclFAt` (callee type is a `∀`; zero-binder callees NOT covered).
OPEN, not claimed: `passF 0` = production `passM` is a runtime-compatibility argument (same body by
source review), not a kernel equivalence; `replaceNoCache` vs the cached extern `Expr.replace` agreement
and performance; `SwitchF` (production `P5At` from `P5AtC`) holds only after a switch ruling. -/

open Lean in
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Tools.ShippingInlTypeReads.resKind_userInlinerC,
      ``Tools.ShippingInlTypeFacts.passT_forallE,
      ``Tools.ShippingInlTypeFacts.roundsC_forallE,
      ``Tools.ShippingP5Forall.p5AtC_of_resDeclF,
      ``Tools.ShippingP5Forall.p5At_of_switch,
      ``Tools.ShippingP5Forall.childLink_realF] do
    Tests.Compiler.NoPortsTest.stdAxioms n
  Lean.logInfo m!"INLCAND: L2 / P5AtC / passT / roundsC on standard axioms"
