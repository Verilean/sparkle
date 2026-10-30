import Tools.ShippingGen2Defs
import Tools.ShippingMachineOutcomeA
set_option autoImplicit false
-- BUILT (unit FB-1) at b9acd902: kjob lake build Tests.Gen4.FbTailCheck exit 0 (703 jobs). Intermediate definition, not a supply result.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. Definition only; not a supply result.

/-! # `LegacyTailRunExists` (existence predicate)

There are an environment, a constant and two worlds with a run of `legacyTail` returning `(raw, D)`, with
`JQC O n` at the start world. The worlds are NOT linked to any core run, so this is NOT evidence that a given
run took the tail. It is an intermediate definition; it supplies no legacy or memo condition. -/

namespace Tools.ShippingGen4FbTail
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInvA (RefLawsAOps)
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingChildCacheA (JQC)
open Tools.ShippingChildInv (profLogIO)
open Tools.ShippingMachineOutcomeA (legacyTail)

def LegacyTailRunExists {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref)
    (mctx : Meta.Context) (cctx : Core.Context) (n : Nat) (c : Name)
    (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) : Prop :=
  ∃ (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo) (w9 w10 : Void IO.RealWorld),
    RunsTo (legacyTail (fun e hint top named => translateExprToWire tenv e hint top named)
      (profLogIO b) c [] false ci) mctx mref cctx cref w9 (raw, D) w10 ∧ JQC O n w9

end Tools.ShippingGen4FbTail
