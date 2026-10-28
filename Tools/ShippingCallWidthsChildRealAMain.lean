import Tools.ShippingCallWidthsChildRealA
import Tools.ShippingChildRunAMain
-- BUILT (integrator, par/int-r6): audit int-r6a exit 0 (534 jobs; closure 17278, no RefLaws/RefLawsCore/toAOps/toA). No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # `parent_children_widths_realA_of_run` with `BodyStepC` / `htr` discharged

Unit L2's `parent_children_widths_realA_of_run` (Tools/ShippingCallWidthsChildRealA.lean) takes G's
`machine_children_realA'` premises `hB : BodyStepC O` and `htr` (restricted translator keeps
`JQC O (D₀ + 1)`). Here they come from unit G2's `machine_children_realA_main` (both PROVED from `O`, `T`):
the run's children are taken from that theorem and fed to `parent_children_widths_realA`.

Premises of `parent_children_widths_realA_main`:
  removed : `BodyStepC O`, `htr`
  remaining: `O`, `hA`, `T : RefLawsATele` (ADDED, unproved; under `O` equivalent to its two fields
    `telescope`/`lamTelescope`, `RefLawsATele.ofTeleLam`), the run `hr`, `MachineDefines`,
    `MachineClosesAtA` (UNRESOLVED premise), the start world (`JQ`, `D₀ = 0 ∨ CacheInvA`),
    `shape.insts ≠ []`, non-memory children (`hnomem`), `LeafKid` per child (its `closes` field and the
    reflection facts it carries are premises), `ResDeclAt`, `P5At`, the binder-type facts `PB`.
Scope: the PORT WIDTHS of non-memory LEAF children of one real compile. NOT general hierarchical
semantic preservation, NOT runtime fit; `ChildrenRealA` is a history of past synthesis results. -/

namespace Tools.ShippingCallWidthsChildRealAMain
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
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge Tools.ShippingMachineClosesData Tools.ShippingMachineCloses

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **Port widths of the leaf children of one real compile**, `BodyStepC`/`htr` discharged (G2). -/
theorem parent_children_widths_realA_main (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (T : RefLawsATele O.quiet mref cref)
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
  Tools.ShippingCallWidthsChildRealA.parent_children_widths_realA
    (Tools.ShippingChildRunAMain.machine_children_realA_main O hA T hr entryP closesP hw hc hi)
    kid res hnomem hkid ResD P5 PB

end Tools.ShippingCallWidthsChildRealAMain
