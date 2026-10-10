import Tools.ShippingChildVC

/-! # The translator's helpers keep the child invariant

The helpers the translator calls to read widths, literals, hardware types and
canonical keys used to be `partial` (opaque). They are now fuel-bounded
fixpoints of ordinary steps (`fuelFixM`, in `Sparkle/Compiler/Elab.lean`),
and each is walked here (`vc`), on every outcome: the fuel induction once
(`fuelFixM_keeps` / `fuelFixM_keepsC` / `fuelFixM2_keeps`), then each step
given its recursive argument. They change no tracked ref: what they need is
only generic — Lean's `whnf`, `inferType`, `reduce`, `ppExpr`, the Meta
context's `withReader`, reads of the profile counters and wire maps. -/
namespace Tools.ShippingChildInv
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `fuelFixM` in `MetaM`: a step that keeps `I` whenever its recursive
argument does (in every context) gives a fixpoint that keeps it at every fuel. -/
@[keeps] theorem fuelFixM_keeps {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} {I : Void IO.RealWorld → Prop} {α β : Type}
    (step : (α → MetaM β) → α → MetaM β)
    (hstep : ∀ rec : α → MetaM β,
      (∀ (mctx : Meta.Context) (cctx : Core.Context) a, Keeps mctx mref cctx cref I (rec a)) →
      ∀ (mctx : Meta.Context) (cctx : Core.Context) a, Keeps mctx mref cctx cref I (step rec a)) :
    ∀ (k : Nat) (mctx : Meta.Context) (cctx : Core.Context) (a : α),
      Keeps mctx mref cctx cref I (fuelFixM step k a)
  | 0, mctx, cctx, a => by
    unfold fuelFixM
    exact Keeps.throw _
  | k + 1, mctx, cctx, a => by
    unfold fuelFixM
    exact hstep _ (fuelFixM_keeps step hstep k) mctx cctx a

/-- `fuelFixM` in `CompilerM`. -/
@[keeps] theorem fuelFixM_keepsC {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} {I : Void IO.RealWorld → Prop} {α β : Type}
    (step : (α → CompilerM β) → α → CompilerM β)
    (hstep : ∀ rec : α → CompilerM β,
      (∀ (mctx : Meta.Context) (cctx : Core.Context) a, KeepsC mctx mref cctx cref I (rec a)) →
      ∀ (mctx : Meta.Context) (cctx : Core.Context) a, KeepsC mctx mref cctx cref I (step rec a)) :
    ∀ (k : Nat) (mctx : Meta.Context) (cctx : Core.Context) (a : α),
      KeepsC mctx mref cctx cref I (fuelFixM step k a)
  | 0, mctx, cctx, a => by
    unfold fuelFixM
    exact KeepsC.throw _
  | k + 1, mctx, cctx, a => by
    unfold fuelFixM
    exact hstep _ (fuelFixM_keepsC step hstep k) mctx cctx a

/-- `fuelFixM2` (two arguments) in `MetaM`. -/
@[keeps] theorem fuelFixM2_keeps {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} {I : Void IO.RealWorld → Prop} {α β γ : Type}
    (step : (α → β → MetaM γ) → α → β → MetaM γ)
    (hstep : ∀ rec : α → β → MetaM γ,
      (∀ (mctx : Meta.Context) (cctx : Core.Context) a b, Keeps mctx mref cctx cref I (rec a b)) →
      ∀ (mctx : Meta.Context) (cctx : Core.Context) a b,
        Keeps mctx mref cctx cref I (step rec a b)) :
    ∀ (k : Nat) (mctx : Meta.Context) (cctx : Core.Context) (a : α) (b : β),
      Keeps mctx mref cctx cref I (fuelFixM2 step k a b)
  | 0, mctx, cctx, a, b => by
    unfold fuelFixM2
    exact Keeps.throw _
  | k + 1, mctx, cctx, a, b => by
    unfold fuelFixM2
    exact hstep _ (fuelFixM2_keeps step hstep k) mctx cctx a b

variable (L : RefLaws mref cref) (D : Nat)
set_option maxHeartbeats 1000000

/-! ## Tracing (`trace[cls] …`), walked once -/

@[keeps] theorem isTracingEnabledFor_keepsC (cls : Name) :
    KeepsC mctx mref cctx cref (J L D) (Lean.isTracingEnabledFor cls : CompilerM Bool) := by
  vc

@[keeps] theorem addTrace_keepsC (cls : Name) (msg : MessageData) :
    KeepsC mctx mref cctx cref (J L D) (Lean.addTrace cls msg : CompilerM Unit) := by
  vc

@[keeps] theorem isTracingEnabledFor_keeps (cls : Name) :
    Keeps mctx mref cctx cref (J L D) (Lean.isTracingEnabledFor cls : MetaM Bool) := by
  vc

@[keeps] theorem addTrace_keeps (cls : Name) (msg : MessageData) :
    Keeps mctx mref cctx cref (J L D) (Lean.addTrace cls msg : MetaM Unit) := by
  vc

/-! ## The helpers -/

@[keeps] theorem extractWidth_keeps (e : Lean.Expr) :
    Keeps mctx mref cctx cref (J L D) (extractWidth e) := by
  vc

@[keeps] theorem inferHWType_keeps (e : Lean.Expr) :
    Keeps mctx mref cctx cref (J L D) (inferHWType e) := by
  vc

@[keeps] theorem extractDimExpr_keeps (e : Lean.Expr) :
    KeepsC mctx mref cctx cref (J L D) (extractDimExpr e) := by
  vc

@[keeps] theorem inferHWTypeWithDimensions_keeps (e : Lean.Expr) :
    KeepsC mctx mref cctx cref (J L D) (inferHWTypeWithDimensions e) := by
  vc

@[keeps] theorem extractNat_keeps (e : Lean.Expr) :
    KeepsC mctx mref cctx cref (J L D) (extractNat e) := by
  vc

@[keeps] theorem extractBitVecLiteral_keeps (e : Lean.Expr) :
    KeepsC mctx mref cctx cref (J L D) (extractBitVecLiteral e) := by
  vc

@[keeps] theorem extractBitVecList_keeps (e : Lean.Expr) :
    KeepsC mctx mref cctx cref (J L D) (extractBitVecList e) := by
  vc

@[keeps] theorem extractBitVecArray_keeps (e : Lean.Expr) :
    KeepsC mctx mref cctx cref (J L D) (extractBitVecArray e) := by
  vc

@[keeps] theorem canonHardwareExpr_keeps (e : Lean.Expr) :
    KeepsC mctx mref cctx cref (J L D) (canonHardwareExpr e) := by
  vc

@[keeps] theorem canonHardwareKey_keeps (e : Lean.Expr) :
    KeepsC mctx mref cctx cref (J L D) (canonHardwareKey e) := by
  vc

@[keeps] theorem inferHWTypeFromSignal_keeps (e : Lean.Expr) :
    KeepsC mctx mref cctx cref (J L D) (inferHWTypeFromSignal e) := by
  vc

@[keeps] theorem cachedInferType_keeps (e : Lean.Expr) :
    KeepsC mctx mref cctx cref (J L D) (cachedInferType e) := by
  vc

end Tools.ShippingChildInv
