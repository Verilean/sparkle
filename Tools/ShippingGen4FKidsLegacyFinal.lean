import Tools.ShippingGen4FKidsLegacyH11
import Tools.ShippingGen4KWalkDiag
import Tools.ShippingGen4FKidsFallback
-- F-kids Final: `LegacyImplKS` from the child entry (the K walk's `legacyImplK_of_entry`, state tracked).
-- Takes `MemoFamily` and `MsgMvK` as HYPOTHESES; adds NO premise, NO axiom. No `sorry`.
namespace Tools.ShippingGen4FKidsLegacyFinal
open Lean Meta
open Tools.ShippingGen4FKidsLegacyH11
open Tools.ShippingGen4FKidsFallback
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildPathA
open Tools.ShippingChildTranslateA
open Tools.ShippingGen4KWalkTac2
open Tools.ShippingChildWalkA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4KWalkHelpers
open Tools.ShippingGen4FKidsHelpers
open Tools.ShippingChildLegacyHelpersA
open Tools.ShippingGen4KWalkLegacyH1
open Tools.ShippingGen4FKidsLegacyH1
open Tools.ShippingGen4KWalkLegacyH2
open Tools.ShippingGen4FKidsLegacyH2
open Tools.ShippingGen4KWalkEmit
open Tools.ShippingGen4FKidsEmit
open Tools.ShippingGen4KWalkLegacyRules
open Tools.ShippingGen4FKidsLegacyRules
open Tools.ShippingGen4KWalkLegacyH4
open Tools.ShippingGen4FKidsLegacyH4
open Tools.ShippingGen4KWalkCanon
open Tools.ShippingGen4FKidsCanon
open Tools.ShippingGen4KWalkLegacyH7
open Tools.ShippingGen4FKidsLegacyH7
open Tools.ShippingGen4KWalkLegacyH1
open Tools.ShippingGen4FKidsLegacyH1
open Tools.ShippingGen4KWalkLegacyH2
open Tools.ShippingGen4FKidsLegacyH2
open Tools.ShippingGen4KWalkProjField
open Tools.ShippingGen4FKidsProjField
open Tools.ShippingGen4KWalkDiag
open Tools.ShippingGen4FKidsDiag
open Tools.ShippingGen4KWalkLegacyH8a
open Tools.ShippingGen4FKidsLegacyH8a
open Tools.ShippingGen4KWalkLegacyH8d
open Tools.ShippingGen4FKidsLegacyH8d
open Tools.ShippingGen4KWalkLegacyH8
open Tools.ShippingGen4FKidsLegacyH8
open Tools.ShippingGen4KWalkLegacyH3
open Tools.ShippingGen4FKidsLegacyH3
open Tools.ShippingGen4KWalkLegacyH5
open Tools.ShippingGen4FKidsLegacyH5
open Tools.ShippingGen4KWalkLegacyH6
open Tools.ShippingGen4FKidsLegacyH6
open Tools.ShippingGen4KWalkLegacyH9
open Tools.ShippingGen4FKidsLegacyH9
open Tools.ShippingGen4KWalkLegacyH10a
open Tools.ShippingGen4FKidsLegacyH10a
open Tools.ShippingGen4KWalkLegacyH10b
open Tools.ShippingGen4FKidsLegacyH10b
open Tools.ShippingGen4KWalkLegacyH7
open Tools.ShippingGen4FKidsLegacyH7
open Tools.ShippingGen4KWalkTranslate
open Tools.ShippingGen4FKidsTranslate
open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele
open Tools.ShippingGen4FKidsEntry

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`LegacyImplKS` from the child entry**: the main body keeps `I` for every stable `I`, given `MsgMvK`. -/
theorem legacyImplKS_of_entry {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hmsg : MsgMvK O)
    {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I) (hchild : ChildEntryKS O I) :
    LegacyImplKS O I := by
  intro rec hrec mctx cctx hA e hint top named
  exact legacyImplKcoreS M (ppMvK_of M) hS hmsg rec (fun mctx cctx hA => hrec mctx cctx hA) hchild hA e hint top named

end Tools.ShippingGen4FKidsLegacyFinal

#print axioms Tools.ShippingGen4FKidsLegacyFinal.legacyImplKS_of_entry
