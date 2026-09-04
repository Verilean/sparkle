import Tools.ConeFoldSlices
import Tools.VerifyElab

/-!
  Twin-fidelity probes: `resolveSlicesT` (Tools/ConeFold.lean) against
  the shipping `Tools.VerifyElab.resolveSlicesW`, on the shapes the
  pack/cone pipeline actually produces.  Lives in its own leaf module
  so Tools/ConeFoldSlices.lean need not import the goal generator —
  the generator imports the THEOREMS instead (per-instance bridge
  lemma emission).
-/

open Sparkle.IR.AST

namespace Tools.ConeFold

-- Fidelity probes against the shipping function, on the shapes the
-- pack/cone pipeline actually produces.
section FidelityProbes
private def wtP : Std.HashMap String Nat :=
  (({} : Std.HashMap String Nat).insert "a" 8).insert "b" 4 |>.insert "c" 1

private def chk (e : Expr) : Bool :=
  decide (resolveSlicesT wtP 100 e = Tools.VerifyElab.resolveSlicesW wtP e)

-- exact window on a pack slice (MSB part and LSB part)
#guard chk (.slice (.concat [.ref "a", .ref "b"]) 11 4)
#guard chk (.slice (.concat [.ref "a", .ref "b"]) 3 0)
-- contained window inside one part
#guard chk (.slice (.concat [.ref "a", .ref "b"]) 9 6)
-- nested concat flattening
#guard chk (.slice (.concat [.concat [.ref "c", .ref "a"], .ref "b"]) 12 4)
-- identity-slice collapse
#guard chk (.slice (.ref "a") 7 0)
-- non-identity slice stays
#guard chk (.slice (.ref "a") 6 1)
-- slice-of-slice fusion (in-range)
#guard chk (.slice (.slice (.ref "a") 6 1) 3 1)
-- recursion through ops and window falling across the general arm
#guard chk (.op .add [.slice (.concat [.ref "b", .ref "b"]) 7 4, .ref "b"])
-- straddling window: unresolved on both sides
#guard chk (.slice (.concat [.ref "a", .ref "b"]) 8 2)
end FidelityProbes

end Tools.ConeFold
