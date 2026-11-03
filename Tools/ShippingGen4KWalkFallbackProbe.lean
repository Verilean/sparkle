import Tools.ShippingGen4KWalkTranslate
import Tools.ShippingChildKWalk
import Tools.ShippingChildFallbackA
-- BUILT: kjob lake build Tools.ShippingGen4KWalkFallbackProbe exit 0 (326 jobs, rt166). S3 PROBE (rt166): can the existing `kwalk` tactic (Tools/ShippingChildKWalk.lean) drive K-version handler
-- proofs? A few leaf emitters of FallbackA, redone for `StableK`. Not a deliverable; no new premise, no sorry/axiom.

namespace Tools.ShippingGen4KWalkFallbackProbe
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildTranslateA
open Tools.ShippingChildPathA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4KWalkTranslate

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

section Emit
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I)
include M hA hS

theorem emitBoolResultK (rhs : Sparkle.IR.AST.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (emitBoolResult rhs hint named) := by
  unfold emitBoolResult
  kwalk [makeWirePK M hA hS, emitAssignP]

theorem emitSliceResultK (rhs : Sparkle.IR.AST.Expr) (len : Nat) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (emitSliceResult rhs len hint named) := by
  unfold emitSliceResult
  kwalk [makeWirePK M hA hS, emitAssignP]

theorem emitMuxResultK (c t el hint : String) (named : Bool) (ty : Sparkle.IR.Type.HWType) :
    KeepsCP mctx mref cctx cref I (emitMuxResult c t el hint named ty) := by
  unfold emitMuxResult
  kwalk [makeWirePK M hA hS, emitAssignP]

end Emit

end Tools.ShippingGen4KWalkFallbackProbe
