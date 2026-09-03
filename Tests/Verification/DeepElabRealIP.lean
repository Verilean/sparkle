import Sparkle
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo
import IP.Net.CRC32
import Tools.DeepElab

/-!
  `#verify_elab_deep` on REAL shipping IP — not demo circuits.

  Each success here is an instance of the general Signal↔IR theorem
  (`Cdo.elab_general`) on a production circuit: the cycle-by-cycle
  Signal semantics of the shipped DSL definition equals the proven
  IR evaluator on its compiled next-state/output cones.

  Current real-IP coverage:
  * `crc32Engine` — CRC-32 byte engine (IP/Net): xor/shr/and/sub/
    concat/mux over 32 bits, a private two-level helper chain
    (`crc32StepSig` → 8 × `crc32BitSig`) unfolded via the collected-
    helper mechanism.

  Known boundaries (each is a worklist item, not a silent skip):
  * nested `circuit do` composition (e.g. `closedLoopCircuit` embeds
    `demoPID`'s own 2-register circuit) — the Signal bridge assumes
    a single top-level `runCircuitH`;
  * struct outputs (`TxOut`, `FramerOut`) — the command requires
    exactly one output;
  * non-Signal value parameters (`biquad`'s `lim`, `mulQSig`'s
    `w f`) — need a specialized wrapper def, as for synthesis.
-/

namespace Sparkle.Tests.DeepElabRealIP

open Sparkle.IP.Net.CRC32

#verify_elab_deep crc32Engine

/-- The theorems above are build-time facts; the exe is a formality
    so `lake build` has an anchor. -/
def main : IO Unit := do
  IO.println "deep-elab real-IP: crc32Engine PROVEN (build-time)"

end Sparkle.Tests.DeepElabRealIP
