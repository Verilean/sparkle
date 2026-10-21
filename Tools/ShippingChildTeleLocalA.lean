import Tools.ShippingChildTeleCP
-- BUILT (unit T1): t1p/t1s exit 0 (withLocalDeclD / withLetDecl), t1t final. No sorry, no axiom, no
-- native_decide, no new law/field. Result: `RefLawsATele.localDecl` and `.letDecl` are PROVED from
-- `O : RefLawsAOps Fresh mref cref` and the Lean definitions (`localDecl_of_O`, `letDecl_of_O`).
-- The probe of unit C2 (ShippingChildTeleProbe) said `localDecl` was stuck at the opaque
-- `withNewLocalInstancesImp`/`isClassExpensive?` workers and at `mkFreshFVarId`: that was WRONG for
-- these two combinators. `withLocalDeclImp`/`withLetDeclImp` -> `withNewFVar` -> `isClass?` (the
-- public wrapper, `FramedA.isClass?`) / `withNewLocalInstance` -> `withNewLocalInstanceImp` (safe defs;
-- the opaque PLURAL `withNewLocalInstancesImp` is not on this path), and `mkFreshFVarId` IS a
-- `FramedA` constructor (`freshFVar`). The telescope fields (`telescope`, `lamTelescope`) are NOT
-- covered here: their workers (`forallTelescopeReducingAux`, `lambdaTelescopeImp.process`) are opaque.
-- Scope: statement-level (model) derivation; nothing about runtime fit of `O` itself.
namespace Tools.ShippingChildTeleLocalA
open Lean Meta
open Tools.ShippingChildInv
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
  {Fresh : (σ : Type) → IO.Ref σ → Prop}

-- unfold (delta+beta) every application of a constant whose name ends with one of the given
-- last components, including PRIVATE ones that cannot be written.
open Lean Elab Tactic Meta in
elab "unfold_suffix " id:ident : tactic => do
  let sufs := #[id.getId.toString]
  liftMetaTactic1 fun g => do
    let t ← g.getType
    let t' ← Core.transform t (post := fun e => do
      let f := e.getAppFn
      if let .const nm _ := f then
        let s := nm.toString
        if sufs.any (fun p => s.endsWith ("." ++ p)) then
          if let some e' ← unfoldDefinition? e then
            return .done e'.headBeta
      return .continue)
    g.replaceTargetDefEq t'

theorem keeps_read_bind {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    {I : Void IO.RealWorld → Prop} {g : Meta.Context → MetaM α}
    (h : Keeps mctx mref cctx cref I (g mctx)) :
    Keeps mctx mref cctx cref I (read >>= g) := fun w hw => h w hw

/-- `withReader` on the Meta context by an update that keeps the unfolding callback. -/
theorem keeps_withReaderA {mctx : Meta.Context} {cctx : Core.Context} {q : Void IO.RealWorld → Prop}
    {I : Void IO.RealWorld → Prop} (hA : AdmCtx q mctx cctx)
    {α : Type} {x : MetaM α} (f : Meta.Context → Meta.Context)
    (hf : ∀ m, (f m).canUnfold? = m.canUnfold?)
    (h : AdmCtx q (f mctx) cctx → Keeps (f mctx) mref cctx cref I x) :
    Keeps mctx mref cctx cref I (withReader f x) :=
  fun w hw => h (fun g hg => hA g ((hf mctx).symm.trans hg)) w hw


section
variable {mctx : Meta.Context} {cctx : Core.Context} {α : Type}

/-- **`RefLawsATele.localDecl`, derived.** The field's statement for `withLocalDeclD`, from
`O : RefLawsAOps` alone (any `Fresh`): no `RefLawsATele`. Uses `FramedA.freshFVar`
(`mkFreshFVarId`), `FramedA.isClass?`, `FramedA.fvarThrowUnknown`, and pure context reads/updates
(AdmCtx kept: `lctx` / `localInstances` updates leave `canUnfold?`). -/
theorem localDecl_of_O (O : RefLawsAOps Fresh mref cref) {I : Void IO.RealWorld → Prop}
    (hA : AdmCtx O.quiet mctx cctx) (hIq : ∀ w, I w → O.quiet w)
    (hI : ∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (O.quiet w → O.quiet w') →
      I w → I w')
    (n : Name) (ty : Lean.Expr) (k : Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) :
    Keeps mctx mref cctx cref I (Lean.Meta.withLocalDeclD n ty k) := by
  have hS : StableA O.quiet I := ⟨hIq, hI⟩
  unfold Lean.Meta.withLocalDeclD Lean.Meta.withLocalDecl Lean.Meta.map1MetaM
  unfold controlAt
  unfold_suffix withLocalDeclImp
  refine Keeps.bind ?_ (fun a => Keeps.pure a)
  dsimp only [liftWith, instMonadControlTOfPure]
  refine Keeps.bind (keepsA_framed O hA hS FramedA.freshFVar) (fun fvarId => ?_)
  refine keeps_read_bind ?_
  refine keeps_withReaderA hA _ (fun m => rfl) (fun hA' => ?_)
  unfold_suffix withNewFVar
  refine Keeps.bind (keepsA_framed O hA' hS (FramedA.isClass? _)) (fun cc => ?_)
  cases cc with
  | none => exact hk _ cctx _ hA'
  | some c =>
    show Keeps _ mref cctx cref I (withNewLocalInstance c (mkFVar fvarId) (k (mkFVar fvarId)))
    unfold Lean.Meta.withNewLocalInstance Lean.Meta.mapMetaM
    unfold controlAt
    unfold_suffix withNewLocalInstanceImp
    refine Keeps.bind ?_ (fun a => Keeps.pure a)
    dsimp only [liftWith, instMonadControlTOfPure]
    unfold Lean.Meta.getFVarLocalDecl Lean.FVarId.getDecl
    refine Keeps.bind (Keeps.bind (Keeps.of_ok fun w => ⟨_, rfl⟩) (fun l => ?_)) (fun d => ?_)
    · split
      · exact Keeps.pure _
      · exact keepsA_framed O hA' hS (FramedA.fvarThrowUnknown _)
    · split
      · exact hk _ cctx _ hA'
      · exact keeps_withReaderA hA' _ (fun m => rfl) (fun h => hk _ cctx _ h)

/-- **`RefLawsATele.letDecl`**: same derivation for `withLetDecl` (see the header). -/
theorem letDecl_of_O (O : RefLawsAOps Fresh mref cref) {I : Void IO.RealWorld → Prop}
    (hA : AdmCtx O.quiet mctx cctx) (hIq : ∀ w, I w → O.quiet w)
    (hI : ∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (O.quiet w → O.quiet w') →
      I w → I w')
    (n : Name) (ty v : Lean.Expr) (k : Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) :
    Keeps mctx mref cctx cref I (Lean.Meta.withLetDecl n ty v k) := by
  have hS : StableA O.quiet I := ⟨hIq, hI⟩
  unfold Lean.Meta.withLetDecl Lean.Meta.map1MetaM
  unfold controlAt
  unfold_suffix withLetDeclImp
  refine Keeps.bind ?_ (fun a => Keeps.pure a)
  dsimp only [liftWith, instMonadControlTOfPure]
  refine Keeps.bind (keepsA_framed O hA hS FramedA.freshFVar) (fun fvarId => ?_)
  refine keeps_read_bind ?_
  refine keeps_withReaderA hA _ (fun m => rfl) (fun hA' => ?_)
  unfold_suffix withNewFVar
  refine Keeps.bind (keepsA_framed O hA' hS (FramedA.isClass? _)) (fun cc => ?_)
  cases cc with
  | none => exact hk _ cctx _ hA'
  | some c =>
    show Keeps _ mref cctx cref I (withNewLocalInstance c (mkFVar fvarId) (k (mkFVar fvarId)))
    unfold Lean.Meta.withNewLocalInstance Lean.Meta.mapMetaM
    unfold controlAt
    unfold_suffix withNewLocalInstanceImp
    refine Keeps.bind ?_ (fun a => Keeps.pure a)
    dsimp only [liftWith, instMonadControlTOfPure]
    unfold Lean.Meta.getFVarLocalDecl Lean.FVarId.getDecl
    refine Keeps.bind (Keeps.bind (Keeps.of_ok fun w => ⟨_, rfl⟩) (fun l => ?_)) (fun d => ?_)
    · split
      · exact Keeps.pure _
      · exact keepsA_framed O hA' hS (FramedA.fvarThrowUnknown _)
    · split
      · exact hk _ cctx _ hA'
      · exact keeps_withReaderA hA' _ (fun m => rfl) (fun h => hk _ cctx _ h)

/-- The bundle with `localDecl`/`letDecl` taken from `O` instead of `T`: the statements of the two
fields are exactly those of `localDecl_of_O` / `letDecl_of_O` (checked by the type ascription). -/
theorem RefLawsATele.withDerived (O : RefLawsAOps Fresh mref cref)
    (T : RefLawsATele O.quiet mref cref) : RefLawsATele O.quiet mref cref :=
  { T with
    localDecl := fun _ hA hIq hI n ty k hk => localDecl_of_O O hA hIq hI n ty k hk
    letDecl := fun _ hA hIq hI n ty v k hk => letDecl_of_O O hA hIq hI n ty v k hk }

end
end Tools.ShippingChildTeleLocalA

#print axioms Tools.ShippingChildTeleLocalA.localDecl_of_O
#print axioms Tools.ShippingChildTeleLocalA.letDecl_of_O

