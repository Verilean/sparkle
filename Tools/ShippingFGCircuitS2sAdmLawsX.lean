import Tools.ShippingGen2Defs
import Tools.ShippingFGCircuitS2sAdmChildCacheA
import Tools.ShippingFGCircuitS2sAdmChildInvA
set_option autoImplicit false
-- FG circuit pilot S2s4: `LawsX` / `StartX`, the context-predicate versions of `Laws` / `Start` (ShippingGen2Defs). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §44.

namespace Tools.ShippingGen2
open Lean Meta Sparkle.Compiler.Elab
open Tools.ShippingChildInvA Tools.ShippingChildCacheA

/-- the uniform runtime laws with the CONTEXT PREDICATE `O.adm` separated from `quiet` -/
structure LawsX (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State) where
  O : RefLawsAOpsX Tools.ShippingChildFresh.MkRefd mref cref
  T : RefLawsATeleX O.quiet O.adm mref cref

/-- the start conditions of an outermost compilation: an `O.adm` context pair and the depth-0 world with its cache invariant -/
def StartX {mref cref} (L : LawsX mref cref) (mctx : Meta.Context) (cctx : Core.Context)
    (w : Void IO.RealWorld) : Prop :=
  L.O.adm mctx cctx ∧ JQCX L.O 0 w

end Tools.ShippingGen2
