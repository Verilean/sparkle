import Sparkle
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo
import Tools.CertifyShared

open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core
open Tools.CertifiedRoundtrip

namespace Sparkle.Tests.CertifySharedCommandTest

def counter (input : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (0#8)
    let a := (r : Signal defaultDomain (BitVec 8))
    let w0 := a + input
    let w1 := (w0 + w0) ^^^ input
    r <~ w1 + w0
    return w1

-- Exercise the public entry point, including generation, not just sealing
-- imported proofs. No sparkle.deepShare option is needed at the call site.
#certify_shared_roundtrip counter => certifiedCounter

example (enable : Signal defaultDomain (BitVec 8)) (K : Nat) :
    ∃ envs,
      runText (certifiedCounter enable).text (certifiedCounter enable).widths
        (certifiedCounter enable).seed (certifiedCounter enable).initial K = .ok envs ∧
      ∀ t, t < K → ∃ env, envs[t]? = some env ∧
        ((counter enable).val t).toNat = env (certifiedCounter enable).port :=
  (certifiedCounter enable).sound K

end Sparkle.Tests.CertifySharedCommandTest
