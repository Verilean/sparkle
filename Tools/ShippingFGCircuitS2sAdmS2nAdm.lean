import Tools.ShippingFGCircuitS2sAdmLawsX
import Tools.ShippingFGCircuitS2sAdmS2hHist
import Tools.ShippingFGCircuitS2sAdmS2hHist2
import Tools.ShippingFGCircuitS2sAdmChildCacheA
import Tools.ShippingFGCircuitS2sAdmChildCanonKeyA
import Tools.ShippingFGCircuitS2sAdmChildComposeA
import Tools.ShippingFGCircuitS2sAdmChildComposeC
import Tools.ShippingFGCircuitS2sAdmChildCoreC
import Tools.ShippingFGCircuitS2sAdmChildDepthA
import Tools.ShippingFGCircuitS2sAdmChildDepthC
import Tools.ShippingFGCircuitS2sAdmChildFallbackA
import Tools.ShippingFGCircuitS2sAdmChildFrontA
import Tools.ShippingFGCircuitS2sAdmChildFrontCP
import Tools.ShippingFGCircuitS2sAdmChildInvA
import Tools.ShippingFGCircuitS2sAdmChildLegacyCachedA
import Tools.ShippingFGCircuitS2sAdmChildLegacyHandlersA
import Tools.ShippingFGCircuitS2sAdmChildLegacyHelpersA
import Tools.ShippingFGCircuitS2sAdmChildLegacyImplA
import Tools.ShippingFGCircuitS2sAdmChildLegacyTailA
import Tools.ShippingFGCircuitS2sAdmChildMainA
import Tools.ShippingFGCircuitS2sAdmChildPathA
import Tools.ShippingFGCircuitS2sAdmChildPinC
import Tools.ShippingFGCircuitS2sAdmChildProjFieldA
import Tools.ShippingFGCircuitS2sAdmChildRunA
import Tools.ShippingFGCircuitS2sAdmChildRunAKids
import Tools.ShippingFGCircuitS2sAdmChildRunAMain
import Tools.ShippingFGCircuitS2sAdmChildTeleCP
import Tools.ShippingFGCircuitS2sAdmChildTeleLocalA
import Tools.ShippingFGCircuitS2sAdmChildTeleMainA
import Tools.ShippingFGCircuitS2sAdmChildTranslateA
import Tools.ShippingFGCircuitS2sAdmChildTranslatePathA
import Tools.ShippingFGCircuitS2sAdmChildVCA
import Tools.ShippingFGCircuitS2sAdmChildVertA
import Tools.ShippingFGCircuitS2sAdmChildWalkA
import Tools.ShippingFGCircuitS2sAdmKWalk
import Tools.ShippingChildRunAKids
import Tools.ShippingChildComposeC
import Tools.ShippingFGCircuitS2sAdmCallsGatePinned
import Tools.ShippingFGCircuitS2sAdmRunLocal
import Tools.ShippingFGCircuitS2sAdmLinked
import Tools.ShippingFGCircuitS2sAdmRunReads
import Tools.ShippingFGCircuitS2sAdmServedRealA
import Tools.ShippingFGCircuitS2sAdmParentRanA
import Tools.ShippingFGCircuitS2sAdmParentTailsA
import Tools.ShippingFGCircuitS2sAdmParentDesignA
import Tools.ShippingFGCircuitS2sAdmS1qLinked
import Tools.ShippingFGCircuitS2sAdmS1tFinal
import Tools.ShippingFGCircuitS2sAdmS1uSrc
import Tools.ShippingFGCircuitS2sAdmS1zClose
import Tools.ShippingFGCircuitS2sAdmS2dKids
import Tools.ShippingFGCircuitS2sAdmS2hHist3
import Tools.ShippingFGCircuitS2sAdmS2mReach
import Tools.ShippingFGCircuitS2sAdmS2mReach2
import Tools.ShippingFGCircuitS2sAdmS2mReach3
import Tools.ShippingStartWorldA
set_option autoImplicit false
-- FG circuit pilot S2s5: the goal `hftCoreCloses_of_kidsR''` (S2m's `hftCoreCloses_of_kidsR` WITHOUT `hdown`, and without `hadm`), on the context-predicate bundles `LawsX`/`RefLawsAOpsX`. The root `mkMetaContext` evidence is tied to the actual run's contexts: `AdmRootX O` (the predicate `O.adm` holds at the command's Meta context, every Core context), from which `StartX L mkMetaContext cctx w` follows from the cache invariant alone. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §44.

namespace Tools.ShippingFGCircuitS2sAdmS2nAdm
open Lean Meta Sparkle.Compiler.Elab
open Tools.ShippingChildInvA Tools.ShippingChildCacheA
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingFGCircuitS2mReach
open Tools.ShippingGen2 (LawsX StartX)
open Tools.ShippingFGCircuitS1zClose (HftCoreCloses)
open Tools.ShippingFGCircuitCover (RootReader)
open Tools.ShippingFGCircuitS2dKids (HftKidsGates)
open Tools.ShippingFGCircuitS1kStmt (hftHttp hftTlp)
open Sparkle.IP.Net.HTTP Sparkle.IP.Bus.PCIe

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The root-context evidence**: the context predicate of the bundle holds at the command's Meta context `mkMetaContext` (it has no `canUnfold?` callback), for every Core context. This is what `mkMetaContext` supplies at the root of the compile; it is stated here about `adm` itself, no `AdmDownR`. -/
def AdmRootX (O : RefLawsAOpsX MkRefd mref cref) : Prop :=
  ∀ cctx : Core.Context, O.adm Lean.Elab.Command.mkMetaContext cctx

/-- the existing bundle, as a `RefLawsAOpsX` at `adm := AdmCtx quiet`, has the root evidence (`mkMetaContext_canUnfold`) -/
theorem admRootX_toX (O : RefLawsAOps MkRefd mref cref) : AdmRootX O.toX :=
  fun c => admCtx_none (cctx := c) Tools.ShippingStartWorldA.mkMetaContext_canUnfold

/-- any bundle whose predicate admits every context without a `canUnfold?` callback has the root evidence -/
theorem admRootX_of_none (O : RefLawsAOpsX MkRefd mref cref)
    (h : ∀ (m : Meta.Context) (c : Core.Context), m.canUnfold? = none → O.adm m c) : AdmRootX O :=
  fun _ => h _ _ Tools.ShippingStartWorldA.mkMetaContext_canUnfold

/-- the start conditions at the root context: the evidence `AdmRootX` plus the depth-0 cache invariant -/
theorem startX_of_root (L : LawsX mref cref) (hroot : AdmRootX L.O) (cctx : Core.Context)
    {w : Void IO.RealWorld} (hj : JQCX L.O 0 w) :
    StartX L Lean.Elab.Command.mkMetaContext cctx w := ⟨hroot cctx, hj⟩

/-- **`hftCoreCloses_of_kidsR''`: `hftCoreCloses_of_kidsR` (S2m) WITHOUT `hdown` and WITHOUT `hadm`.** The context predicate `L.O.adm` is a field of the bundle, kept in every context update (`CtxClosed`), so the strengthened quiet predicate (`quietRX`) no longer needs `AdmDownR`; the root context is `hstart.1`. Remaining named premises: `hD` (class-D rows), `hG` (diagnostic rows), `hT` (telescope rows), `hs` (profile lookup along leaf steps), `h0` (profile lookup unset at the root start world). -/
theorem hftCoreCloses_of_kidsR'' (L : LawsX mref cref) {w : Void IO.RealWorld}
    (hstart : StartX L mctx cctx w) (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat}
    (hrH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hrT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hg : HftKidsGates (envAt cref w))
    (hD : DRowEnvRX L.O (envAt cref w) w)
    (hG : DiagEnvRX L.O (envAt cref w) w) (hT : TeleRX L.O (envAt cref w) w)
    (hs : ProfStepRX L.O w) (h0 : ProfOffW mref cref w) :
    HftCoreCloses mctx mref cctx cref w :=
  hftCoreCloses_of_kidsRX L hstart hcell hrH hrT hg hstart.1 hD hG hT hs h0

/-- **At the actual root context** `mkMetaContext`: the context evidence is `AdmRootX` (not an assumption about the strengthened predicate, not `hdown`), the cache invariant at depth 0 is the start world's. -/
theorem hftCoreCloses_of_root (L : LawsX mref cref) (hroot : AdmRootX L.O) (cctx : Core.Context)
    {w : Void IO.RealWorld} (hj : JQCX L.O 0 w) (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat}
    (hrH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hrT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hg : HftKidsGates (envAt cref w))
    (hD : DRowEnvRX L.O (envAt cref w) w)
    (hG : DiagEnvRX L.O (envAt cref w) w) (hT : TeleRX L.O (envAt cref w) w)
    (hs : ProfStepRX L.O w) (h0 : ProfOffW mref cref w) :
    HftCoreCloses Lean.Elab.Command.mkMetaContext mref cctx cref w :=
  hftCoreCloses_of_kidsR'' L (startX_of_root L hroot cctx hj) hcell hrH hrT hg hD hG hT hs h0

end Tools.ShippingFGCircuitS2sAdmS2nAdm

#print axioms Tools.ShippingFGCircuitS2sAdmS2nAdm.admRootX_toX
#print axioms Tools.ShippingFGCircuitS2sAdmS2nAdm.hftCoreCloses_of_kidsR''
#print axioms Tools.ShippingFGCircuitS2sAdmS2nAdm.hftCoreCloses_of_root
