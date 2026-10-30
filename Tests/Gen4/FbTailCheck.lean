import Tools.ShippingGen4FbTail
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT (unit FB-1 check).
/-! # Checks for `LegacyTailRunExists` (scripts/gen4/FALLBACK_SUPPLY_FREEZE.md rev3 §5.2)
1. TYPE: against an independent copy of the frozen statement. 2. MUTANT: signature/defeq rejections, NOT semantic
counterexamples. 3. AXIOMS. -/
namespace Tests.Gen4.FbTailCheck
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInvA (RefLawsAOps)
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingChildCacheA (JQC)
open Tools.ShippingMachineOutcomeA (legacyTail)
open Tools.ShippingGen4FbTail
open Tests.Gen3.ExpectedType

def ExpLegacyTailRunExists {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref)
    (mctx : Meta.Context) (cctx : Core.Context) (n : Nat) (c : Name)
    (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) : Prop :=
  ∃ (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo) (w9 w10 : Void IO.RealWorld),
    RunsTo (legacyTail (fun e hint top named => translateExprToWire tenv e hint top named)
      (profLogIO b) c [] false ci) mctx mref cctx cref w9 (raw, D) w10 ∧ JQC O n w9

/-- mutant: no `JQC` conjunct. -/
def MutNoJQC {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref)
    (mctx : Meta.Context) (cctx : Core.Context) (n : Nat) (c : Name)
    (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) : Prop :=
  ∃ (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo) (w9 w10 : Void IO.RealWorld),
    RunsTo (legacyTail (fun e hint top named => translateExprToWire tenv e hint top named)
      (profLogIO b) c [] false ci) mctx mref cctx cref w9 (raw, D) w10

/-- mutant: `JQC` at the end world. -/
def MutJQCEnd {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref)
    (mctx : Meta.Context) (cctx : Core.Context) (n : Nat) (c : Name)
    (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) : Prop :=
  ∃ (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo) (w9 w10 : Void IO.RealWorld),
    RunsTo (legacyTail (fun e hint top named => translateExprToWire tenv e hint top named)
      (profLogIO b) c [] false ci) mctx mref cctx cref w9 (raw, D) w10 ∧ JQC O n w10

/-- mutant: symbolic mode `true` instead of `false`. -/
def MutSymbolic {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref)
    (mctx : Meta.Context) (cctx : Core.Context) (n : Nat) (c : Name)
    (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) : Prop :=
  ∃ (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo) (w9 w10 : Void IO.RealWorld),
    RunsTo (legacyTail (fun e hint top named => translateExprToWire tenv e hint top named)
      (profLogIO b) c [] true ci) mctx mref cctx cref w9 (raw, D) w10 ∧ JQC O n w9

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``LegacyTailRunExists ``ExpLegacyTailRunExists
  checkMutant ``LegacyTailRunExists ``MutNoJQC
  checkMutant ``LegacyTailRunExists ``MutJQCEnd
  checkMutant ``LegacyTailRunExists ``MutSymbolic
  checkAxioms ``LegacyTailRunExists

end Tests.Gen4.FbTailCheck
