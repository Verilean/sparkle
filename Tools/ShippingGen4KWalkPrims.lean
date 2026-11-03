import Tools.ShippingGen4KWalk
import Tools.ShippingChildTranslateA
-- NOT BUILT: S1 of scripts/gen4/KWALK_PLAN.md. `StableK` and the K versions of the T1/T2 primitives
-- (copies of `makeWireA` ... `recordTranslationA`, taking `StableK` instead of `StableA`).
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom.
-- No `sorry`, no `axiom`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.

namespace Tools.ShippingGen4KWalkPrims
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildHarness
open Tools.ShippingChildTranslateA
open Tools.ShippingChildPathA
open Tools.Assume.MemoFamily
open Tools.Assume.FramedACases
open Tools.ShippingGen4KWalk

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `StableA` with the memo added to the transport condition: an invariant that may depend on the memo
(`KW O P`) survives every world change that leaves the child cache, the synthesis ref, the depth and the memo,
and quietness. -/
def StableK (quiet : Void IO.RealWorld → Prop) (I : Void IO.RealWorld → Prop) : Prop :=
  (∀ w, I w → quiet w) ∧
  (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w →
    (quiet w → quiet w') → I w → I w')

/-- `KW O P` is `StableK`, for every `P`. -/
theorem stableK_KW (O : RefLawsAOps MkRefd mref cref) (P : Std.HashMap Name Res → Std.HashMap Name Res → Prop) :
    StableK O.quiet (KW O P) :=
  ⟨fun _ h => h.1, fun _ _ hc hs _ hm hq h => kw_transfer hc hs hm hq h⟩

/-- A `FramedNM` step keeps a `StableK` invariant (exceptions in the class): `keepsA_framed` for `StableK`. -/
theorem keepsK_framedNM (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I) {α : Type} {p : MetaM α}
    (hp : FramedNM MkRefd p) : Keeps mctx mref cctx cref I p := by
  intro w hw
  have hq := hS.1 w hw
  have hk := O.frame hA p (framedNM_toA hp) w hq
  have hq' := O.frameQ hA p (framedNM_toA hp) w hq
  have hm := M.frame hA p hp w hq
  refine ⟨hS.2 w _ hk.1 hk.2.1 hk.2.2 hm (fun _ => hq') hw, ?_⟩
  unfold ErrOk
  cases hmm : p mctx mref cctx cref w with
  | ok a w1 => exact True.intro
  | error e w1 => exact O.excOk hA p (.framed (framedNM_toA hp).toFramed) w e w1 hq hmm

/-! ## The circuit-state primitives (T1) -/

section Prims
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I)
include M hA hS

/-- The wire-width cache's update, lifted: `FramedNM.sideModify .wireWidth`. -/
theorem wireWidthK (f : Std.HashMap String Nat → Std.HashMap String Nat) :
    TripleC mctx mref cctx cref I
      (CompilerM.liftMetaM (ST.Ref.modify sparkleWireWidthCache f)) (fun _ => I)
      (fun e w => I w ∧ OkExc e) :=
  TripleC.lift (keeps_iff.mp (keepsK_framedNM M hA hS (FramedNM.sideModify _ .wireWidth)))

theorem makeWireK (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) :
    TripleC mctx mref cctx cref I (CompilerM.makeWire hint ty named)
      (fun _ => I) (fun e w => I w ∧ OkExc e) := by
  unfold CompilerM.makeWire
  refine TripleC.bind TripleC.get ?_
  intro cs
  split
  refine TripleC.bind (TripleC.set _) ?_
  intro _
  dsimp only
  split
  · refine TripleC.bind (wireWidthK M hA hS _) ?_
    intro _
    exact TripleC.pure fun _ hw => hw
  · exact TripleC.pure fun _ hw => hw

theorem addInputK (name : String) (ty : Sparkle.IR.Type.HWType) :
    TripleC mctx mref cctx cref I (CompilerM.addInput name ty)
      (fun _ => I) (fun e w => I w ∧ OkExc e) := by
  unfold CompilerM.addInput
  refine TripleC.bind TripleC.get ?_
  intro cs
  split
  refine TripleC.bind (TripleC.set _) ?_
  intro _
  split
  · exact wireWidthK M hA hS _
  · exact TripleC.pure fun _ hw => hw

theorem addOutputK (name : String) (ty : Sparkle.IR.Type.HWType) :
    TripleC mctx mref cctx cref I (CompilerM.addOutput name ty)
      (fun _ => I) (fun e w => I w ∧ OkExc e) := by
  unfold CompilerM.addOutput
  refine TripleC.bind TripleC.get ?_
  intro cs
  split
  refine TripleC.bind (TripleC.set _) ?_
  intro _
  split
  · exact wireWidthK M hA hS _
  · exact TripleC.pure fun _ hw => hw

theorem makeWirePK (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) :
    KeepsCP mctx mref cctx cref I (CompilerM.makeWire hint ty named) :=
  KeepsCP.ofT (makeWireK M hA hS hint ty named)

theorem addInputPK (name : String) (ty : Sparkle.IR.Type.HWType) :
    KeepsCP mctx mref cctx cref I (CompilerM.addInput name ty) :=
  KeepsCP.ofT (addInputK M hA hS name ty)

theorem addOutputPK (name : String) (ty : Sparkle.IR.Type.HWType) :
    KeepsCP mctx mref cctx cref I (CompilerM.addOutput name ty) :=
  KeepsCP.ofT (addOutputK M hA hS name ty)

theorem emitRegisterK (hint clk rst : String) (input : Sparkle.IR.AST.Expr) (initVal : Nat)
    (ty : Sparkle.IR.Type.HWType) (named : Bool) (rk : Sparkle.IR.Type.ResetKind) :
    KeepsCP mctx mref cctx cref I (CompilerM.emitRegister hint clk rst input initVal ty named rk) := by
  refine KeepsCP.ofT ?_
  unfold CompilerM.emitRegister
  refine TripleC.bind TripleC.get ?_
  intro cs
  split
  refine TripleC.bind (TripleC.set _) ?_
  intro _
  dsimp only
  split
  · refine TripleC.bind (wireWidthK M hA hS _) ?_
    intro _
    exact TripleC.pure fun _ hw => hw
  · exact TripleC.pure fun _ hw => hw

theorem emitMemoryK (hint : String) (aw dw : Nat) (clk : String)
    (wa wd we ra : Sparkle.IR.AST.Expr) (named : Bool) :
    KeepsCP mctx mref cctx cref I (CompilerM.emitMemory hint aw dw clk wa wd we ra named) := by
  refine KeepsCP.ofT ?_
  unfold CompilerM.emitMemory
  refine TripleC.bind TripleC.get ?_
  intro cs
  split
  refine TripleC.bind (TripleC.set _) ?_
  intro _
  refine TripleC.bind (wireWidthK M hA hS _) ?_
  intro _
  exact TripleC.pure fun _ hw => hw

end Prims

/-! ## The translation cache (T2) -/

section Cache
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I)
include M hA hS

theorem cacheLookupValidatedK (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (cacheLookupValidated e) := by
  unfold cacheLookupValidated
  refine KeepsCP.bindCtx (fun cs hcs => ?_)
  try dsimp only
  cases hc : cs.exprCache with
  | none => exact KeepsCP.pure _
  | some r =>
    have hr := hcs r hc
    refine KeepsCP.bind (KeepsCP.lift ?_) (fun hit => ?_)
    · first
        | exact Keeps.bind (keepsK_framedNM M hA hS (FramedNM.exprCacheGetIO r hr)) fun _ => Keeps.pure _
        | exact Keeps.bind (keepsK_framedNM M hA hS (FramedNM.exprCacheGet r hr)) fun _ => Keeps.pure _
    · cases hit with
      | none => exact KeepsCP.pure _
      | some w =>
        refine KeepsCP.bind KeepsCP.get (fun s => ?_)
        split <;> exact KeepsCP.pure _

theorem recordTranslationK (e : Lean.Expr) (w : String) (cacheable : Bool) :
    KeepsCP mctx mref cctx cref I (recordTranslation e w cacheable) := by
  unfold recordTranslation
  refine KeepsCP.bind (KeepsCP.modify _) (fun _ => ?_)
  refine KeepsCP.ite (fun _ => ?_) (fun _ => KeepsCP.pure _)
  refine KeepsCP.bindCtx (fun cs hcs => ?_)
  try dsimp only
  cases hc : cs.exprCache with
  | none => exact KeepsCP.pure _
  | some r => exact KeepsCP.lift (keepsK_framedNM M hA hS (FramedNM.exprCacheModify r _ (hcs r hc)))

end Cache

end Tools.ShippingGen4KWalkPrims
