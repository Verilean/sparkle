import Tools.ShippingChildInvA
set_option autoImplicit false
-- FG circuit pilot S2s (leaves): the operations / telescope laws with the CONTEXT PREDICATE separated from `quiet`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §44.
-- `RefLawsAOpsX`/`RefLawsATeleX` are `RefLawsAOps`/`RefLawsATele` with the context quantifier `AdmCtx quiet mctx cctx` replaced by a predicate `adm` carried by the bundle (closed under the context updates the compile performs). The existing bundles are SPECIALISATIONS (`RefLawsAOps.toX`: `adm := AdmCtx O.quiet`). Names of the ported development are the original ones with the suffix `X`.

namespace Tools.ShippingChildInvA
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndCore

/-- a predicate on the pair of contexts a law is stated at -/
abbrev CtxPred := Meta.Context → Core.Context → Prop

/-- the context updates the compile performs (`withLocalDecl*`/`withLetDecl`/telescopes: `lctx`, `localInstances`; `withTransparency`: `keyedConfig`; `withIncRecDepth`: the Core context) keep the predicate -/
structure CtxClosed (C : CtxPred) : Prop where
  lctx : ∀ {mctx : Meta.Context} {cctx : Core.Context}, C mctx cctx → ∀ l : LocalContext, C { mctx with lctx := l } cctx
  localInsts : ∀ {mctx : Meta.Context} {cctx : Core.Context}, C mctx cctx → ∀ li : LocalInstances,
    C { mctx with localInstances := li } cctx
  lctx_insts : ∀ {mctx : Meta.Context} {cctx : Core.Context}, C mctx cctx → ∀ (l : LocalContext) (li : LocalInstances),
    C { mctx with lctx := l, localInstances := li } cctx
  config : ∀ {mctx : Meta.Context} {cctx : Core.Context}, C mctx cctx → ∀ c : ConfigWithKey,
    C { mctx with keyedConfig := c } cctx
  coreCtx : ∀ {mctx : Meta.Context} {cctx : Core.Context}, C mctx cctx → ∀ cctx' : Core.Context, C mctx cctx'

theorem admCtx_closed (quiet : Void IO.RealWorld → Prop) : CtxClosed (AdmCtx quiet) where
  lctx := fun h l => admCtx_lctx h l
  localInsts := fun h li => admCtx_localInsts h li
  lctx_insts := fun h l li => admCtx_lctx_insts h l li
  config := fun h c => admCtx_config h c
  coreCtx := fun h c => admCtx_cctx h c

/-- `RefLawsAOps` with the context predicate `adm` in place of `AdmCtx quiet` -/
structure RefLawsAOpsX (Fresh : (σ : Type) → IO.Ref σ → Prop)
    (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State) where
  quiet : Void IO.RealWorld → Prop
  adm : CtxPred
  adm_closed : CtxClosed adm
  diag : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, adm mctx cctx →
    ∀ (p : MetaM α), Diag p → ∀ w, quiet w →
    (cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w) ∧ quiet (endW mctx mref cctx cref p w)
  frameT : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, adm mctx cctx →
    ∀ (p : MetaM α), Throws p → ∀ w, quiet w →
    (cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w) ∧ quiet (endW mctx mref cctx cref p w)
  excOk : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, adm mctx cctx →
    ∀ (p : MetaM α), Op p →
    ∀ w e w', quiet w → p mctx mref cctx cref w = .error e w' → OkExc e
  frameQ : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, adm mctx cctx →
    ∀ (p : MetaM α), FramedA Fresh p → ∀ w,
    quiet w → quiet (endW mctx mref cctx cref p w)
  cacheSetQ : ∀ {mctx : Meta.Context} {cctx : Core.Context}, adm mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → quiet w → quiet w'
  depthSetQ : ∀ {mctx : Meta.Context} {cctx : Core.Context}, adm mctx cctx → ∀ v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' →
    quiet w → quiet w'
  frame : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, adm mctx cctx →
    ∀ (p : MetaM α), FramedA Fresh p → ∀ w, quiet w →
    cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w
  cacheSet : ∀ {mctx : Meta.Context} {cctx : Core.Context}, adm mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → quiet w →
    cv w' = v ∧ sv w' = sv w ∧ dv w' = dv w
  depthSet : ∀ {mctx : Meta.Context} {cctx : Core.Context}, adm mctx cctx → ∀ v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' → quiet w →
    cv w' = cv w ∧ sv w' = sv w ∧ dv w' = v

/-- `RefLawsATele` with the context predicate `adm` in place of `AdmCtx quiet` (the continuation is asked to keep `I` ONLY in `adm` contexts) -/
structure RefLawsATeleX (quiet : Void IO.RealWorld → Prop) (adm : CtxPred)
    (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State) : Prop where
  telescope : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), adm mctx cctx → (∀ w, I w → quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (ty : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, adm mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.forallTelescopeReducing ty k)
  lamTelescope : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), adm mctx cctx → (∀ w, I w → quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, adm mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.lambdaTelescope e k cleanup)
  localDecl : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), adm mctx cctx → (∀ w, I w → quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (n : Name) (ty : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, adm mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLocalDeclD n ty k)
  letDecl : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), adm mctx cctx → (∀ w, I w → quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (n : Name) (ty v : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, adm mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLetDecl n ty v k)

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
  {mctx : Meta.Context} {cctx : Core.Context}

/-- **The existing operations bundle is a specialisation**: `adm := AdmCtx O.quiet` -/
def RefLawsAOps.toX {Fresh : (σ : Type) → IO.Ref σ → Prop} (O : RefLawsAOps Fresh mref cref) :
    RefLawsAOpsX Fresh mref cref where
  quiet := O.quiet
  adm := AdmCtx O.quiet
  adm_closed := admCtx_closed O.quiet
  diag := O.diag
  frameT := O.frameT
  excOk := O.excOk
  frameQ := O.frameQ
  cacheSetQ := O.cacheSetQ
  depthSetQ := O.depthSetQ
  frame := O.frame
  cacheSet := O.cacheSet
  depthSet := O.depthSet

/-- the existing telescope laws are a specialisation at `adm := AdmCtx quiet` -/
theorem RefLawsATele.toX {quiet : Void IO.RealWorld → Prop} (T : RefLawsATele quiet mref cref) :
    RefLawsATeleX quiet (AdmCtx quiet) mref cref :=
  ⟨T.telescope, T.lamTelescope, T.localDecl, T.letDecl⟩

theorem RefLawsAOpsX.cacheModify' {Fresh : (σ : Type) → IO.Ref σ → Prop}
    (O : RefLawsAOpsX Fresh mref cref) (hA : O.adm mctx cctx)
    (f : Std.HashMap Name Res → Std.HashMap Name Res) {w : Void IO.RealWorld}
    {u : Unit} {w' : Void IO.RealWorld} (hq : O.quiet w)
    (h : RunsTo (sparkleChildCache.modify f : MetaM Unit) mctx mref cctx cref w u w') :
    cv w' = f (cv w) ∧ sv w' = sv w ∧ dv w' = dv w := by
  obtain ⟨w1, hg, hs⟩ := modify_split sparkleChildCache f h
  have h1 := O.frame hA _ FramedA.cacheGet w hq
  have hq1 := O.frameQ hA _ FramedA.cacheGet w hq
  rw [endW_of_runs hg] at h1 hq1
  have h2 := O.cacheSet hA _ _ _ _ hs hq1
  exact ⟨h2.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem RefLawsAOpsX.depthModify' {Fresh : (σ : Type) → IO.Ref σ → Prop}
    (O : RefLawsAOpsX Fresh mref cref) (hA : O.adm mctx cctx)
    (f : Nat → Nat) {w : Void IO.RealWorld} {u : Unit} {w' : Void IO.RealWorld}
    (hq : O.quiet w)
    (h : RunsTo (ST.Ref.modify sparkleSynthDepth f : MetaM Unit) mctx mref cctx cref w u w') :
    cv w' = cv w ∧ sv w' = sv w ∧ dv w' = f (dv w) := by
  obtain ⟨w1, hg, hs⟩ := modify_split sparkleSynthDepth f h
  have h1 := O.frame hA _ FramedA.depthGet w hq
  have hq1 := O.frameQ hA _ FramedA.depthGet w hq
  rw [endW_of_runs hg] at h1 hq1
  have h2 := O.depthSet hA _ _ _ _ hs hq1
  exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2⟩

end Tools.ShippingChildInvA
