import Tools.ShippingChildWalkA
-- BUILT (unit B, round 2): lh1 exit 0 (one helper), lh2 exit 1 (the rule needed the quietness predicate from the local `O`; `DimExpr` namespace), lh3 exit 0.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / boundary field. Law witness:
-- `O : RefLawsAOps MkRefd mref cref`, `hA : AdmCtx O.quiet mctx cctx`, `hS : StableA O.quiet I`
-- (NO `RefLawsATele`: no helper runs a telescope).
--
-- # The translator's helpers under the admissible boundary
--
-- `extractWidth`, `inferHWType`, `extractDimExpr`, `inferHWTypeWithDimensions`, `extractNat`,
-- `extractBitVecLiteral`, `inferHWTypeFromSignal`, `cachedInferType`, … walked by `vca`
-- (Tools/ShippingChildWalkA.lean): the fuel induction once (`fuelFixM_keepsA`,
-- `fuelFixM_keepsCP`), then each step given its recursive argument. They change no tracked
-- ref: they use Lean's `whnf`/`inferType`/`reduce`/`ppExpr`, reads of the profile counters and
-- wire maps, and the type cache (`FramedA.sideGet/sideModify`).

namespace Tools.ShippingChildLegacyHelpersA
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildWalkA

attribute [keepsA] makeWireP addInputP addOutputP emitAssignP emitRegisterA emitMemoryA
  emitRegisterStmtA emitInstanceA addModuleToDesignA freshNameA lookupVarP bindSourceVariableP
  withVarMappingP

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## The fuel fixpoints -/

/-- `fuelFixM` in `MetaM`: a step that keeps `I` whenever its recursive argument does (in every
admissible context) gives a fixpoint that keeps it at every fuel. -/
@[keepsA] theorem fuelFixM_keepsA {q : Void IO.RealWorld → Prop} {I : Void IO.RealWorld → Prop}
    {α β : Type} (step : (α → MetaM β) → α → MetaM β)
    (hstep : ∀ rec : α → MetaM β,
      (∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx q mctx cctx → ∀ a,
        Keeps mctx mref cctx cref I (rec a)) →
      ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx q mctx cctx → ∀ a,
        Keeps mctx mref cctx cref I (step rec a)) :
    ∀ (k : Nat) (mctx : Meta.Context) (cctx : Core.Context), AdmCtx q mctx cctx → ∀ (a : α),
      Keeps mctx mref cctx cref I (fuelFixM step k a)
  | 0, mctx, cctx, _, a => by
    unfold fuelFixM
    exact Keeps.throw _ (by okmsg)
  | k + 1, mctx, cctx, hA, a => by
    unfold fuelFixM
    exact hstep _ (fun _ _ hA' a' => fuelFixM_keepsA step hstep k _ _ hA' a') mctx cctx hA a

/-- `fuelFixM` in `CompilerM`. -/
@[keepsA] theorem fuelFixM_keepsCP {q : Void IO.RealWorld → Prop} {I : Void IO.RealWorld → Prop}
    {α β : Type} (step : (α → CompilerM β) → α → CompilerM β)
    (hstep : ∀ rec : α → CompilerM β,
      (∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx q mctx cctx → ∀ a,
        KeepsCP mctx mref cctx cref I (rec a)) →
      ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx q mctx cctx → ∀ a,
        KeepsCP mctx mref cctx cref I (step rec a)) :
    ∀ (k : Nat) (mctx : Meta.Context) (cctx : Core.Context), AdmCtx q mctx cctx → ∀ (a : α),
      KeepsCP mctx mref cctx cref I (fuelFixM step k a)
  | 0, mctx, cctx, _, a => by
    unfold fuelFixM
    exact KeepsCP.throw _ (by okmsg)
  | k + 1, mctx, cctx, hA, a => by
    unfold fuelFixM
    exact hstep _ (fun _ _ hA' a' => fuelFixM_keepsCP step hstep k _ _ hA' a') mctx cctx hA a

/-- `fuelFixM2` (two arguments) in `MetaM`. -/
@[keepsA] theorem fuelFixM2_keepsA {q : Void IO.RealWorld → Prop} {I : Void IO.RealWorld → Prop}
    {α β γ : Type} (step : (α → β → MetaM γ) → α → β → MetaM γ)
    (hstep : ∀ rec : α → β → MetaM γ,
      (∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx q mctx cctx → ∀ a b,
        Keeps mctx mref cctx cref I (rec a b)) →
      ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx q mctx cctx → ∀ a b,
        Keeps mctx mref cctx cref I (step rec a b)) :
    ∀ (k : Nat) (mctx : Meta.Context) (cctx : Core.Context), AdmCtx q mctx cctx → ∀ (a : α) (b : β),
      Keeps mctx mref cctx cref I (fuelFixM2 step k a b)
  | 0, mctx, cctx, _, a, b => by
    unfold fuelFixM2
    exact Keeps.throw _ (by okmsg)
  | k + 1, mctx, cctx, hA, a, b => by
    unfold fuelFixM2
    exact hstep _ (fun _ _ hA' a' b' => fuelFixM2_keepsA step hstep k _ _ hA' a' b') mctx cctx hA a b

/-! ## Tracing, walked once -/

section Helpers
variable (O : RefLawsAOps MkRefd mref cref) {I : Void IO.RealWorld → Prop}
  (hS : StableA O.quiet I)
include O hS

@[keepsA] theorem isTracingEnabledFor_keepsA (hA : AdmCtx O.quiet mctx cctx) (cls : Name) :
    Keeps mctx mref cctx cref I (Lean.isTracingEnabledFor cls : MetaM Bool) := by
  vca

@[keepsA] theorem addTrace_keepsA (hA : AdmCtx O.quiet mctx cctx) (cls : Name) (msg : MessageData) :
    Keeps mctx mref cctx cref I (Lean.addTrace cls msg : MetaM Unit) := by
  vca

@[keepsA] theorem isTracingEnabledFor_keepsCP (hA : AdmCtx O.quiet mctx cctx) (cls : Name) :
    KeepsCP mctx mref cctx cref I (Lean.isTracingEnabledFor cls : CompilerM Bool) := by
  vca

@[keepsA] theorem addTrace_keepsCP (hA : AdmCtx O.quiet mctx cctx) (cls : Name) (msg : MessageData) :
    KeepsCP mctx mref cctx cref I (Lean.addTrace cls msg : CompilerM Unit) := by
  vca

@[keepsA] theorem extractWidth_keepsA (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    Keeps mctx mref cctx cref I (extractWidth e) := by
  vca

@[keepsA] theorem inferHWType_keepsA (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    Keeps mctx mref cctx cref I (inferHWType e) := by
  vca

@[keepsA] theorem extractDimExpr_keepsCP (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (extractDimExpr e) := by
  vca

@[keepsA] theorem inferHWTypeWithDimensions_keepsCP (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (inferHWTypeWithDimensions e) := by
  vca

@[keepsA] theorem extractNat_keepsCP (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (extractNat e) := by
  vca

@[keepsA] theorem extractBitVecLiteral_keepsCP (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (extractBitVecLiteral e) := by
  vca

@[keepsA] theorem extractNatLiteral_keepsCP (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (extractNatLiteral e) := by
  vca

@[keepsA] theorem extractBitVecList_keepsCP (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (extractBitVecList e) := by
  vca

@[keepsA] theorem extractBitVecArray_keepsCP (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (extractBitVecArray e) := by
  vca

@[keepsA] theorem inferHWTypeFromSignal_keepsCP (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (inferHWTypeFromSignal e) := by
  vca

@[keepsA] theorem cachedInferType_keepsCP (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (cachedInferType e) := by
  vca

@[keepsA] theorem getWireWidth_keepsCP (hA : AdmCtx O.quiet mctx cctx) (w : String) :
    KeepsCP mctx mref cctx cref I (CompilerM.getWireWidth w) := by
  vca

@[keepsA] theorem getWireWidthDim_keepsCP (hA : AdmCtx O.quiet mctx cctx) (w : String) :
    KeepsCP mctx mref cctx cref I (CompilerM.getWireWidthDim w) := by
  vca

@[keepsA] theorem lowerZeroExtendWire_keepsCP (hA : AdmCtx O.quiet mctx cctx) (hint src : String) (t : Sparkle.IR.Type.DimExpr) (named : Bool) :
    KeepsCP mctx mref cctx cref I (lowerZeroExtendWire hint src t named) := by
  vca

end Helpers

end Tools.ShippingChildLegacyHelpersA
