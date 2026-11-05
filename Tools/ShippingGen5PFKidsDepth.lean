-- Gen5 port of Tools.ShippingGen4FKidsDepth (scripts/gen4/PARAM_ASSEMBLY.md §Gen5): copy for the gen5 Elab; only the marked parts differ.
import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4FKidsTele
import Tools.ShippingGen4KWalkEntry
import Tools.ShippingGen4FKidsEntry
import Tools.ShippingGen5PKWalkDepth
namespace Tools.ShippingGen4FKidsDepth
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildVertA
open Tools.ShippingChildPathA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildFrontA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4KWalkEntry
open Tools.ShippingGen4FKidsEntry

open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele

open Tools.ShippingGen4KWalkDepth
open Tools.Assume.FramedACases
-- F-kids StatePF walk: the depth-pinned PF world. `KWD O P D` is generic in `P`; the PF world is `P := PPF`. No sorry.

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- the key relation of the PF world: K and both caches `PairPF` -/
def PPF (m c : Std.HashMap Name Res) : Prop := MemoKeysInChild m c ∧ CachePF m ∧ CachePF c

/-- the key relation of the PF world with the in-flight name `n` -/
def PPFX (n : Name) (m c : Std.HashMap Name Res) : Prop := MemoKeysExc n m c ∧ CachePF m ∧ CachePF c

/-- the PF world at depth `D` -/
@[reducible] def WPF (O : RefLawsAOps MkRefd mref cref) (D : Nat) : Void IO.RealWorld → Prop := KWD O PPF D

/-- the PF world at depth `D` with the in-flight name `n` -/
@[reducible] def WPFX (O : RefLawsAOps MkRefd mref cref) (n : Name) (D : Nat) : Void IO.RealWorld → Prop :=
  KWD O (PPFX n) D

/-- the world half of the invariant, as frozen in FKIDS_FREEZE.md §2 -/
def WorldPF (O : RefLawsAOps MkRefd mref cref) (D : Nat) (w : Void IO.RealWorld) : Prop :=
  KWD O MemoKeysInChild D w ∧ CachePF (cv w) ∧ CachePF (mv w)

theorem worldPF_iff (O : RefLawsAOps MkRefd mref cref) (D : Nat) (w : Void IO.RealWorld) :
    WorldPF O D w ↔ WPF O D w := by
  constructor
  · rintro ⟨⟨⟨hq, hs, hk⟩, hd⟩, hc, hm⟩
    exact ⟨⟨hq, hs, hk, hm, hc⟩, hd⟩
  · rintro ⟨⟨hq, hs, hk, hm, hc⟩, hd⟩
    exact ⟨⟨⟨hq, hs, hk⟩, hd⟩, hc, hm⟩

section Depth
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
include M hA

/-- The memo write of a `PairPF` result opens the window at depth `D`. -/
theorem triple_memoInsertDP (D : Nat) (n : Name) (r : Res) (hr : PairPF r)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (WPF O D)
      (sparkleSubModuleCache.modify (·.insert n r) : MetaM Unit)
      (fun _ => WPFX O n D) R :=
  Triple.of_runs (refModify_runs _ _) fun w u w' hw hr' => by
    have hp : FramedA MkRefd (sparkleSubModuleCache.modify (·.insert n r) : MetaM Unit) :=
      framedA_of_memoAccess (MemoAccess.modify _)
    have hf := O.frame hA _ hp w hw.1.1
    rw [endW_of_runs hr'] at hf
    obtain ⟨hq, hc, hs, hm⟩ := memoModify_ctx M hA _ hr' hw.1.1
    refine ⟨⟨hq, hs.trans hw.1.2.1, ?_⟩, by rw [hf.2.2]; exact hw.2⟩
    obtain ⟨h1, h2, h3⟩ := hw.1.2.2
    rw [hm, hc]
    exact ⟨memoKeysExc_insert n r h1, cachePF_insert n r h2 hr, h3⟩

/-- The child-cache write of a `PairPF` result closes the window at depth `D`. -/
theorem triple_childInsertDP (D : Nat) (n : Name) (r : Res) (hr : PairPF r)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (WPFX O n D)
      (sparkleChildCache.modify (·.insert n r) : MetaM Unit)
      (fun _ => WPF O D) R :=
  Triple.of_runs (refModify_runs _ _) fun w u w' hw hr' => by
    have hk := O.cacheModify' hA (·.insert n r) hw.1.1 hr'
    obtain ⟨hq, hc, hs, hm⟩ := childModify_ctx M hA _ hr' hw.1.1
    refine ⟨⟨hq, hs.trans hw.1.2.1, ?_⟩, by rw [hk.2.2]; exact hw.2⟩
    obtain ⟨h1, h2, h3⟩ := hw.1.2.2
    rw [hm, hc]
    exact ⟨memoKeysInChild_of_exc_insert n r h1, h2, cachePF_insert n r h3 hr⟩

end Depth

end Tools.ShippingGen4FKidsDepth

#print axioms Tools.ShippingGen4FKidsDepth.triple_memoInsertDP
#print axioms Tools.ShippingGen4FKidsDepth.triple_childInsertDP
#print axioms Tools.ShippingGen4FKidsDepth.worldPF_iff
