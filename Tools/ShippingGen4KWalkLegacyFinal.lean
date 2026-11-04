import Tools.ShippingGen4KWalkLegacyH11
import Tools.ShippingGen4KWalkLegacyInduct2
-- BUILT (rt180): kjob lake build Tools.ShippingGen4KWalkLegacyFinal exit 0 (axioms propext, Classical.choice, Quot.sound); clean build is the coder's. LegacyImplK part 12: `LegacyImplK` from the main body (H11) and the child entry, and the K-walk top entry with `MsgMvK` as the only hypothesis (besides the family `M`).
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkLegacyFinal
open Lean Meta
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
open Tools.ShippingGen4KWalkHelpers
open Tools.ShippingChildLegacyHelpersA
open Tools.ShippingGen4KWalkLegacyH1
open Tools.ShippingGen4KWalkLegacyH2
open Tools.ShippingGen4KWalkEmit
open Tools.ShippingGen4KWalkLegacyRules
open Tools.ShippingGen4KWalkLegacyH4
open Tools.ShippingGen4KWalkCanon
open Tools.ShippingGen4KWalkLegacyH7
open Tools.ShippingGen4KWalkLegacyH1
open Tools.ShippingGen4KWalkLegacyH2
open Tools.ShippingGen4KWalkProjField
open Tools.ShippingGen4KWalkDiag
open Tools.ShippingGen4KWalkLegacyH8a
open Tools.ShippingGen4KWalkLegacyH8d
open Tools.ShippingGen4KWalkLegacyH8
open Tools.ShippingGen4KWalkLegacyH3
open Tools.ShippingGen4KWalkLegacyH5
open Tools.ShippingGen4KWalkLegacyH6
open Tools.ShippingGen4KWalkLegacyH9
open Tools.ShippingGen4KWalkLegacyH10a
open Tools.ShippingGen4KWalkLegacyH10b
open Tools.ShippingGen4KWalkLegacyH7
open Tools.ShippingGen4KWalkTranslate

open Tools.ShippingGen4KWalkLegacyH11
open Tools.ShippingGen4KWalkLegacyInduct2
open Tools.ShippingGen4KWalkDepth
open Tools.ShippingGen4KWalkFallback
open Tools.ShippingGen4KWalkEntry

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`LegacyImplK` from the child entry**: the main body keeps `I` for every stable `I`, given `MsgMvK`. -/
theorem legacyImplK_of_entry {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hmsg : MsgMvK O)
    {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I) (hchild : ChildEntryK O I) :
    LegacyImplK O I := by
  intro rec hrec mctx cctx hA e hint top named
  exact legacyImplKcore M (ppMvK_of M) hS hmsg rec (fun mctx cctx hA => hrec mctx cctx hA) hchild hA e hint top named

section Top
variable {mctx : Meta.Context} {cctx : Core.Context}
  {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hmsg : MsgMvK O)
  (hA : AdmCtx O.quiet mctx cctx)

include M hmsg hA

/-- **The K-walk top entry with `LegacyImplK` discharged**: the only hypothesis is `MsgMvK` (and the family `M`). -/
theorem topEntry_K_of_family3 (declName : Name) :
    Triple mctx mref cctx cref (KWD O (fun _ _ => True) 0)
      (synthesizeCombinationalCoreWith (fun env e h t n => translateExprToWire env e h t n) declName [] false true)
      (fun _ => KWD O (MemoKeysExc declName) 0) (fun e w => KW O (fun _ _ => True) w ∧ OkExc e) :=
  topEntry_K_of_family2 M
    (fun D _ hEntry => legacyImplK_of_entry M hmsg (stableK_KWD O MemoKeysInChild D) hEntry) hA declName

end Top

end Tools.ShippingGen4KWalkLegacyFinal

#print axioms Tools.ShippingGen4KWalkLegacyFinal.legacyImplK_of_entry
#print axioms Tools.ShippingGen4KWalkLegacyFinal.topEntry_K_of_family3
