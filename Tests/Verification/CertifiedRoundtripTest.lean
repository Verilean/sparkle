import Tools.CertifyShared
import Tests.Verification.ConeSharingGen

open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.CertifiedRoundtrip

set_option linter.defProp false

namespace Sparkle.Tests.ConeSharingGen

#seal_shared_roundtrip shareX4 => shareX4_certified
#seal_shared_roundtrip shareX8 => shareX8_certified

-- This statement mentions the exact text, its parser, execution, and source.
-- Unlike signal_runRT alone, its axiom dependencies include the parse equality.
theorem shareX4_certified_sound (i : Signal defaultDomain (BitVec 8)) (K : Nat) :
    ∃ envs,
      runText (shareX4_certified i).text (shareX4_certified i).widths
        (shareX4_certified i).seed (shareX4_certified i).initial K = .ok envs ∧
      ∀ t, t < K → ∃ env, envs[t]? = some env ∧
        ((shareX4 i).val t).toNat = env (shareX4_certified i).port :=
  (shareX4_certified i).sound K

-- The byte string in the certificate is the generator's text, not a new
-- serialization of the reparsed body.
example (i : Signal defaultDomain (BitVec 8)) :
    (shareX4_certified i).text = shareX4_sdeep_text := rfl

-- A valid proof for one text cannot certify different bytes.
example (_i : Signal defaultDomain (BitVec 8)) : True := by
  fail_if_success
    have bad := ofReplay "different bytes" shareX4_sdeep_text_parses
      (shareX4_sdeep_signal_run _i) (shareX4_sdeep_signal_runOpt _i)
      (shareX4_sdeep_signal_runRT _i)
  trivial

end Sparkle.Tests.ConeSharingGen

namespace Sparkle.Tests.CertifiedRoundtripTest

open Sparkle.Tests.ConeSharingGen

namespace MissingParse
def design := shareX4
def design_sdeep_trace := @shareX4_sdeep_trace
/-- error: roundtrip certification: missing required link design_sdeep_text_parses; a partial PROVEN chain is not accepted -/
#guard_msgs in
#seal_shared_roundtrip design => refused
end MissingParse

namespace MissingReplay
def design := shareX4
def design_sdeep_trace := @shareX4_sdeep_trace
def design_sdeep_text_parses := shareX4_sdeep_text_parses
def design_sdeep_signal_run := @shareX4_sdeep_signal_run
def design_sdeep_signal_runOpt := @shareX4_sdeep_signal_runOpt
/-- error: roundtrip certification: missing required link design_sdeep_signal_runRT; a partial PROVEN chain is not accepted -/
#guard_msgs in
#seal_shared_roundtrip design => refused
end MissingReplay

namespace MissingOptimizer
def design := shareX4
def design_sdeep_trace := @shareX4_sdeep_trace
def design_sdeep_text_parses := shareX4_sdeep_text_parses
def design_sdeep_signal_run := @shareX4_sdeep_signal_run
def design_sdeep_signal_runRT := @shareX4_sdeep_signal_runRT
/-- error: roundtrip certification: missing required link design_sdeep_signal_runOpt; a partial PROVEN chain is not accepted -/
#guard_msgs in
#seal_shared_roundtrip design => refused
end MissingOptimizer

namespace Untrusted
def design := shareX4
axiom unsupported : False
def design_sdeep_trace : True := False.elim unsupported
def design_sdeep_text_parses := shareX4_sdeep_text_parses
def design_sdeep_signal_run := @shareX4_sdeep_signal_run
def design_sdeep_signal_runOpt := @shareX4_sdeep_signal_runOpt
def design_sdeep_signal_runRT := @shareX4_sdeep_signal_runRT
def design_sdeep_text := shareX4_sdeep_text
/-- error: roundtrip certification: Sparkle.Tests.CertifiedRoundtripTest.Untrusted.design_sdeep_trace depends on disallowed axiom Sparkle.Tests.CertifiedRoundtripTest.Untrusted.unsupported -/
#guard_msgs in
#seal_shared_roundtrip design => refused
end Untrusted

namespace WrongSource
def shareX4 (_ : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.pure 0
/-- error: roundtrip certification: replay does not certify the requested source Sparkle.Tests.CertifiedRoundtripTest.WrongSource.shareX4 -/
#guard_msgs in
#seal_shared_roundtrip shareX4 => refused
end WrongSource

open Lean Elab Command in
run_cmd do
  for n in [``Certificate.sound, ``accepted_sound] do
    for a in (← liftCoreM <| collectAxioms n) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "generic certification theorem {n} has unexpected axiom {a}"
  for n in [`Sparkle.Tests.CertifiedRoundtripTest.MissingParse.refused,
      `Sparkle.Tests.CertifiedRoundtripTest.MissingReplay.refused,
      `Sparkle.Tests.CertifiedRoundtripTest.MissingOptimizer.refused,
      `Sparkle.Tests.CertifiedRoundtripTest.Untrusted.refused,
      `Sparkle.Tests.CertifiedRoundtripTest.WrongSource.refused] do
    if (← getEnv).contains n then throwError "failed certification emitted {n}"
  -- Composition must actually use both links: RT replay on its own does not
  -- have the parse oracle among its axioms, but the text soundness theorem does.
  let axs ← liftCoreM <| collectAxioms ``shareX4_certified_sound
  unless axs.contains `Sparkle.Tests.ConeSharingGen.shareX4_sdeep_text_parses._native.native_decide.ax_1 do
    throwError "text soundness did not include the parse link"
  if axs.contains ``sorryAx then throwError "certificate soundness uses sorryAx"
  logInfo "CERTIFICATION TEST OK: named artifacts, general soundness, mandatory links, source identity, parse dependency"

end Sparkle.Tests.CertifiedRoundtripTest
