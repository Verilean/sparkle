import Tools.VedU1Deep
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

namespace Tests.Ved.H2OpenParentProbe

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Deep

abbrev S8 := Signal defaultDomain (BitVec 8)

/-- Child with one register: an accumulator with an input. -/
def accMod (x : S8) : S8 :=
  circuit do
    let r ← Signal.reg (0#8)
    let a := (r : S8)
    r <~ a + x
    return a

/-- Register-free parent: two instances of `accMod` on different inputs,
combined asymmetrically (`p - q + a`). -/
def parTwo (a b : S8) : S8 :=
  let p := accMod a
  let q := accMod b
  p - q + a

/-- The open parent: the child calls are free signals `p q`. -/
def parentOpen (a b p q : S8) : S8 := p - q + a

#guard_msgs (drop info) in
#verify_elab_deep parTwo
#guard_msgs (drop info) in
#verify_elab_deep parentOpen
