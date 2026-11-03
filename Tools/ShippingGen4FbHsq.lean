import Tools.ShippingGen4FbFragRun
import Tools.ShippingGen4FirstLeafR
set_option autoImplicit false
-- NOT BUILT (unit B.F-4 hS -> hQ bridge): written against scripts/gen4/FB_HSQ_SCRATCH.md §3/§5 (reviewer-approved at e2186f49). Rename: §3 `bridge` is `firstLeaf_childRunN`... see below.
-- BUILT (unit B.F-4 hS -> hQ bridge): `kjob lake build Tools.ShippingGen4FbHsq` exit 0 (713 jobs) in the Pod (Lean commit b3e37699; comment-only header edit after); NOT a clean issue-linked build (coder). Written against scripts/gen4/FB_HSQ_SCRATCH.md §3/§5 (approved e2186f49).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field / hypothesis (only `RealChildA` and `EntryDefines`, as in the scratch).

/-! # B.F-4: the fragment-limited `hS` -> `hQ` bridge

First-gate fragment (`FirstLeaf`) only. `hS_ifaceOf`: the gate-side `f.ifaceOf.S i` satisfies FB-22's pointwise `hS`.
`firstLeaf_childRunN`: from `RealChildA O f.decl y` and `EntryDefines`, `ChildRunN … y.1 … (f.ifaceOf.S i)` without `hS`.
Says nothing about non-fragment `Pkg` / `q.S`, legacy, memo, or the ledger. -/

namespace Tools.ShippingGen4FbHsq
open Tools.ShippingGen2
open Tools.ShippingChildCacheA (RealChildA)
open Tools.ShippingChildInv (Res)
open Tools.ShippingEntrySoundness (RunsTo quoteDecl)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingChildInvA (RefLawsAOps)
open Tools.ShippingChildFresh (MkRefd)

theorem hS_ifaceOf {ι : Type} (f : FirstLeaf ι) (i : ι) :
    ∀ (vals : Nat → List Nat) (g : Nat → Nat), ((f.ifaceOf.S i) vals)[0]? = some g →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j)
          ((Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n).filter fun x => x.2 != .domain) →
        g j = Tools.ShippingFirstGateChild.firstFn f.dn f.names f.n f.fe (vals j) := by
  intro vals g hg j _
  have h0 := gateS_get0 (Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n)
    (Tools.ShippingUnifiedSource.ofF f.n f.fe) (fun _ => 0) (fun j => j + 1) vals
  have : g = _ := (Option.some.inj (hg.symm.trans h0))
  subst this
  rfl

theorem firstLeaf_childRunN {ι : Type} {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (f : FirstLeaf ι)
    (entry : EntryDefines mctx mref cctx cref f.decl (quoteDecl f.dn f.names f.n f.fe))
    {y : Res} (h : RealChildA O f.decl y) (n : Nat) (i : ι) (dsn : Sparkle.IR.AST.Design) :
    ChildRunN (Tools.ShippingMachineLinked.childMap dsn.modules) dsn n y.1
      (Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n)
      [({ name := "out", lo := 0, width := f.n, ty := .bitVector f.n } : Sparkle.IR.Machine.OutField)]
      (f.ifaceOf.S i) := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    have entry' := Tools.ShippingReflectCtx.EntryDefines.ctx (mctx' := mctx') (cctx' := cctx') entry
    exact Tools.ShippingGen4FbFragRun.synthesizeCombinational_fragment_childRunN hr entry' f.hwf f.hn
      (hS_ifaceOf f i)

end Tools.ShippingGen4FbHsq
