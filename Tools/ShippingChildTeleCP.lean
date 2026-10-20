import Tools.ShippingChildTranslateA
-- UNBUILT (unit C, round par/u-c): builds tc1 (this file) — see REPORT-C.md for the exit.
-- No `sorry`, no `axiom`, no `native_decide`, no new law. The ONLY assumption beyond the
-- operations bundle is `T : RefLawsATele O.quiet mref cref` (a SEPARATE assumption family;
-- using it widens the boundary; logical inconsistency of it is NOT PROVEN).
-- Writing-time guesses:
--  C1 `T.telescope I hA hS.1 hS.2 ty k (fun m c xs b h => hk m c xs b h)` has exactly the shape
--     of `RefLawsATele.telescope_old` (the side conditions are `StableA`'s two components).

/-! # Telescope combinators, for a stable invariant

`Keeps` forms (MetaM) straight from `RefLawsATele`, with the two side conditions of the law
discharged by `StableA` (`hS.1`: `I → quiet`; `hS.2`: the frame condition). The continuation
need keep `I` only in ADMISSIBLE contexts. `KeepsCP` forms: the MetaM telescope lifted into
`CompilerM` (`KeepsCP.lift`). -/

namespace Tools.ShippingChildTeleCP
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildTranslateA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
  {I : Void IO.RealWorld → Prop} {quiet : Void IO.RealWorld → Prop}

theorem keeps_forallTelescopeReducing (T : RefLawsATele quiet mref cref)
    (hA : AdmCtx quiet mctx cctx) (hS : StableA quiet I) {α : Type} (ty : Lean.Expr)
    (k : Array Lean.Expr → Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) :
    Keeps mctx mref cctx cref I (Lean.Meta.forallTelescopeReducing ty k) :=
  T.telescope I hA hS.1 hS.2 ty k hk

theorem keeps_lambdaTelescope (T : RefLawsATele quiet mref cref)
    (hA : AdmCtx quiet mctx cctx) (hS : StableA quiet I) {α : Type} (e : Lean.Expr)
    (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) :
    Keeps mctx mref cctx cref I (Lean.Meta.lambdaTelescope e k cleanup) :=
  T.lamTelescope I hA hS.1 hS.2 e k cleanup hk

theorem keeps_withLocalDeclD (T : RefLawsATele quiet mref cref)
    (hA : AdmCtx quiet mctx cctx) (hS : StableA quiet I) {α : Type} (n : Name) (ty : Lean.Expr)
    (k : Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) :
    Keeps mctx mref cctx cref I (Lean.Meta.withLocalDeclD n ty k) :=
  T.localDecl I hA hS.1 hS.2 n ty k hk

theorem keeps_withLetDecl (T : RefLawsATele quiet mref cref)
    (hA : AdmCtx quiet mctx cctx) (hS : StableA quiet I) {α : Type} (n : Name)
    (ty v : Lean.Expr) (k : Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) :
    Keeps mctx mref cctx cref I (Lean.Meta.withLetDecl n ty v k) :=
  T.letDecl I hA hS.1 hS.2 n ty v k hk

/-! ## Lifted into `CompilerM` -/

theorem keepsCP_forallTelescopeReducing (T : RefLawsATele quiet mref cref)
    (hA : AdmCtx quiet mctx cctx) (hS : StableA quiet I) {α : Type} (ty : Lean.Expr)
    (k : Array Lean.Expr → Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) :
    KeepsCP mctx mref cctx cref I
      (CompilerM.liftMetaM (Lean.Meta.forallTelescopeReducing ty k)) :=
  KeepsCP.lift (keeps_forallTelescopeReducing T hA hS ty k hk)

theorem keepsCP_lambdaTelescope (T : RefLawsATele quiet mref cref)
    (hA : AdmCtx quiet mctx cctx) (hS : StableA quiet I) {α : Type} (e : Lean.Expr)
    (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) :
    KeepsCP mctx mref cctx cref I (CompilerM.liftMetaM (Lean.Meta.lambdaTelescope e k cleanup)) :=
  KeepsCP.lift (keeps_lambdaTelescope T hA hS e k cleanup hk)

theorem keepsCP_withLocalDeclD (T : RefLawsATele quiet mref cref)
    (hA : AdmCtx quiet mctx cctx) (hS : StableA quiet I) {α : Type} (n : Name) (ty : Lean.Expr)
    (k : Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) :
    KeepsCP mctx mref cctx cref I (CompilerM.liftMetaM (Lean.Meta.withLocalDeclD n ty k)) :=
  KeepsCP.lift (keeps_withLocalDeclD T hA hS n ty k hk)

theorem keepsCP_withLetDecl (T : RefLawsATele quiet mref cref)
    (hA : AdmCtx quiet mctx cctx) (hS : StableA quiet I) {α : Type} (n : Name)
    (ty v : Lean.Expr) (k : Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) :
    KeepsCP mctx mref cctx cref I (CompilerM.liftMetaM (Lean.Meta.withLetDecl n ty v k)) :=
  KeepsCP.lift (keeps_withLetDecl T hA hS n ty v k hk)

end Tools.ShippingChildTeleCP
