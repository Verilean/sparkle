import Tools.ShippingCallWidthsChildRealAMain
import Tools.ShippingChildTeleMainA
-- BUILT (integrator, par/u-pw-tl): audit pwtl-a exit 0 (535 jobs; closure 17285, no RefLaws/RefLawsCore/toAOps/toA). No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # `parent_children_widths_realA_main` with the external laws as T2's two items

The same statement as `parent_children_widths_realA_main` with `T` replaced by `htel`/`hlam`
(`RefLawsATele.ofTeleLam`, `localDecl`/`letDecl` PROVED from `O`). Not a logical-strength claim: under
`O`, the full `T` and the two remaining fields are equivalent. Aligns this endpoint with the `_tl`
endpoints of Tools/ShippingChildTeleMainA.lean (externally required laws: `telescope`, `lamTelescope`,
an ADDED unproved boundary). Other premises and scope unchanged (port widths of non-memory LEAF children;
`MachineClosesAtA` UNRESOLVED; not runtime fit). -/

namespace Tools.ShippingCallWidthsChildRealATl
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildTranslateA Tools.ShippingChildDepthC Tools.ShippingChildFrontCP
open Tools.ShippingChildCacheA Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildLinkA
open Tools.ShippingCallWidthsStrict Tools.ShippingCallWidthsDeclared Tools.ShippingCallWidthsEntry
open Tools.ShippingCallWidthsChildReal
open Tools.ShippingPortsMatchRawLeaf (LeafKid)
open Tools.ShippingChildIfaceTy (ChildOutTys)
open Tools.ShippingMixedEntrySoundness Tools.ShippingGateChildComb
open Tools.ShippingChildWalkA Tools.ShippingChildTeleMainA
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge Tools.ShippingMachineClosesData Tools.ShippingMachineCloses

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `parent_children_widths_realA_main` with `T := RefLawsATele.ofTeleLam O htel hlam`. -/
theorem parent_children_widths_realA_main_tl (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (htel : ForallTelescopeLawA O.quiet mref cref) (hlam : LamTelescopeLawA O.quiet mref cref)
    {d : MachineData} {declName : Name} {D₀ : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {D : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, D) w')
    (entryP : MachineDefines mctx mref cctx cref declName d.shape)
    (closesP : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx declName d.shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w)) (hi : d.shape.insts ≠ [])
    (kid : Nat → MachineData) (res : Nat → MixedGateBinder)
    (hnomem : ∀ o ∈ d.shape.instTagged, o.2.child?.isNone = true)
    (hkid : ∀ k (hk : k < d.shape.insts.length),
      LeafKid mctx mref cctx cref (d.shape.insts[k]).1 (kid k))
    (ResD : ∀ k (hk : k < d.shape.insts.length), ResDeclAt mref cref (d.shape.insts[k]).1 (res k))
    (P5 : ∀ k (hk : k < d.shape.insts.length), P5At mref cref (d.shape.insts[k]).1 (res k))
    (PB : ∀ k (hk : k < d.shape.insts.length),
      (d.shape.binders[closingNDecl d.shape + k]?).map (fun bn => kindTy bn.2) =
        some (machHWType (res k))) :
    callWidthsStrict d (closingNDecl d.shape) (fun k => (kid k).shape.layout.outs) = true ∧
    ∃ t t' d₀ children,
      Sparkle.IR.Machine.closeLets d.shape.layout.lets t = some t' ∧
      CloseCalls d.shape t (Sparkle.IR.Machine.closeMachine d.shape.layout t') d₀ children m D ∧
      ∀ k (hk : k < d.shape.insts.length) (y : Res), children[k]? = some y →
        ChildOutTys (kid k).shape.layout.outs y.1 ∧
        ∀ p ∈ y.1.outputs, (∀ f, d.shape.instFields[k]? = some f → p.name = f) →
          (d.shape.binders[closingNDecl d.shape + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
            some p.ty.bitWidth :=
  Tools.ShippingCallWidthsChildRealAMain.parent_children_widths_realA_main O hA
    (RefLawsATele.ofTeleLam O htel hlam) hr entryP closesP hw hc hi kid res hnomem hkid ResD P5 PB

end Tools.ShippingCallWidthsChildRealATl
