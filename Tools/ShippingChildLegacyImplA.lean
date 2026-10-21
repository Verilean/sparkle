import Tools.ShippingChildLegacyHandlersA
import Tools.ShippingChildFallbackA
-- BUILT (unit B, round 2, worktree wt-u-b, base 0054b6b2): li1-li7 trials, li8 exit 0 (core), li10 exit 0
-- (exports); axioms of `legacyImplA_of_handlers`: propext, Classical.choice, Quot.sound.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / boundary field. Law witness:
-- `O : RefLawsAOps MkRefd mref cref`, `hS : StableA O.quiet I`, and the three telescope laws the
-- walk reaches (`LocalDeclLawA`, `LetDeclLawA`, `ForallTelescopeLawA`: fields of `RefLawsATele`,
-- Tools/ShippingChildInvA.lean:301 — a SEPARATE assumption family, see REPORT-B.md); premises
-- `CanonKeyA` (`canonHardwareKey`) and `ChildEntryA` (`childSynthEntry`).
--
-- # `LegacyImplA`: the legacy translator's main body (`Rec.translateExprToWireImpl`)
--
-- PROVED by the walker `vca` (Tools/ShippingChildWalkA.lean), with the helpers
-- (Tools/ShippingChildLegacyHelpersA.lean) and every handler `translateExprToWireApp` reaches
-- (Tools/ShippingChildLegacyHandlersA.lean) walked first. The remaining premises are NOT
-- handler lumps: `CanonKeyA` is `canonHardwareKey`, `ChildEntryA` is `childSynthEntry`, and the
-- three laws are the telescope primitives the code runs (`withLocalDeclD` in `CompilerM.withLocalDecl`,
-- `withLetDecl`, `forallTelescopeReducing` in `handleDefinitionUnfold`).

namespace Tools.ShippingChildLegacyImplA
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
open Tools.ShippingChildFallbackA
open Tools.ShippingChildLegacyHelpersA
open Tools.ShippingChildLegacyHandlersA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000

section Impl
variable (O : RefLawsAOps MkRefd mref cref) {I : Void IO.RealWorld → Prop}
  (hS : StableA O.quiet I)
include O hS

/-- The applicative `map`'s inline mini-translator, recursive on the two operands of an
application: by induction on a bound of the expression's size, in every admissible context
(it runs under `withLocalDecl`). -/
theorem toIR_keepsCP_bound (wireS : String) (fvarId : FVarId) :
    ∀ (n : Nat) (e : Lean.Expr), sizeOf e < n →
      ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
        KeepsCP mctx mref cctx cref I (Rec.translateExprToWireImpl.toIR wireS fvarId e)
  | 0, _, h => by omega
  | n + 1, e, h => by
    intro mctx cctx hA
    have ih := fun e' (h' : sizeOf e' < n) (mctx : Meta.Context) (cctx : Core.Context)
      (hA : AdmCtx O.quiet mctx cctx) => toIR_keepsCP_bound wireS fvarId n e' h' mctx cctx hA
    unfold Rec.translateExprToWireImpl.toIR
    vca

@[keepsA] theorem toIR_keepsCP (wireS : String) (fvarId : FVarId) (e : Lean.Expr)
    (hA : AdmCtx O.quiet mctx cctx) :
    KeepsCP mctx mref cctx cref I (Rec.translateExprToWireImpl.toIR wireS fvarId e) :=
  toIR_keepsCP_bound O hS wireS fvarId (sizeOf e + 1) e (Nat.lt_succ_self _) mctx cctx hA

@[keepsA] theorem getPrim_keepsCP (e : Lean.Expr) (hA : AdmCtx O.quiet mctx cctx) :
    KeepsCP mctx mref cctx cref I (Rec.getPrimitiveNameFromLambda e) := by
  induction e with
  | lam _ _ body _ _ ih => unfold Rec.getPrimitiveNameFromLambda; exact ih
  | _ => unfold Rec.getPrimitiveNameFromLambda; vca

end Impl

section Main
variable (O : RefLawsAOps MkRefd mref cref) {I : Void IO.RealWorld → Prop}
  (hS : StableA O.quiet I)
  (TL : LocalDeclLawA O.quiet mref cref) (TLet : LetDeclLawA O.quiet mref cref)
  (TF : ForallTelescopeLawA O.quiet mref cref)
  (hcanon : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ a, KeepsCP mctx mref cctx cref I (canonHardwareKey a))
  (hchild : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ c, Keeps mctx mref cctx cref I (childSynthEntry c))
include O hS TL TLet TF hcanon hchild

/-- **The legacy translator's main body keeps `I`** (`LegacyImplA`), given the telescope laws
of `withLocalDeclD`/`withLetDecl`/`forallTelescopeReducing`, `canonHardwareKey` (premise
`CanonKeyA`) and `childSynthEntry` (premise `ChildEntryA`). -/
theorem legacyImplA_core : LegacyImplA O I := by
  intro rec hrec mctx cctx hA e hint top named
  have hr : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
      ∀ e hint top named, KeepsCP mctx mref cctx cref I (rec e hint top named) := hrec
  show KeepsCP mctx mref cctx cref I
    (Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e hint top named)
  unfold Rec.translateExprToWireImpl
  vca

end Main

/-- **`LegacyImplA`**, exported with the premises named by what they cover: the three telescope
laws, `canonHardwareKey` (`CanonKeyA`) and `childSynthEntry` (`ChildEntryA`). -/
theorem legacyImplA_of_handlers (O : RefLawsAOps MkRefd mref cref) {I : Void IO.RealWorld → Prop}
    (hS : StableA O.quiet I)
    (TL : LocalDeclLawA O.quiet mref cref) (TLet : LetDeclLawA O.quiet mref cref)
    (TF : ForallTelescopeLawA O.quiet mref cref)
    (hcanon : CanonKeyA O I) (hchild : ChildEntryA O I) : LegacyImplA O I :=
  legacyImplA_core O hS TL TLet TF hcanon hchild

/-- The same, from the whole telescope family `RefLawsATele` (all four fields; the proof uses
the three above). -/
theorem legacyImplA_of_tele (O : RefLawsAOps MkRefd mref cref) {I : Void IO.RealWorld → Prop}
    (hS : StableA O.quiet I) (T : RefLawsATele O.quiet mref cref)
    (hcanon : CanonKeyA O I) (hchild : ChildEntryA O I) : LegacyImplA O I :=
  legacyImplA_of_handlers O hS (Tools.ShippingChildWalkA.RefLawsATele.localDeclLaw T)
    (Tools.ShippingChildWalkA.RefLawsATele.letDeclLaw T)
    (Tools.ShippingChildWalkA.RefLawsATele.forallTelescopeLaw T) hcanon hchild

end Tools.ShippingChildLegacyImplA

#print axioms Tools.ShippingChildLegacyImplA.legacyImplA_of_handlers
#print axioms Tools.ShippingChildLegacyImplA.legacyImplA_of_tele
