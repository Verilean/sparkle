import Tools.ShippingGen4FKidsPrims
import Tools.ShippingChildTeleLocalA
set_option autoImplicit false
-- F-kids StatePF walk, part 4: `CompilerM.withLocalDecl` / `withLetDecl` for `KeepsCS`. The RESULT of `withLocalDeclD` is the result of its
-- continuation; this is derived from the Lean definitions (as `localDecl_of_O` does for `Keeps`, Tools/ShippingChildTeleLocalA.lean), with
-- `Triple` in place of `Keeps`. Uses only `FramedNM` steps of `MemoFamily` (`M`), no new law. No sorry / axiom / native_decide.

namespace Tools.ShippingGen4FKidsTele
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildTranslateA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Sparkle.IR.Builder (CircuitState)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

theorem triple_read_bind {α : Type} {I : Void IO.RealWorld → Prop} {Q : α → Void IO.RealWorld → Prop}
    {R : Exception → Void IO.RealWorld → Prop} {g : Meta.Context → MetaM α}
    (h : Triple mctx mref cctx cref I (g mctx) Q R) :
    Triple mctx mref cctx cref I (read >>= g) Q R := fun w hw => h w hw

theorem triple_withReaderA {q : Void IO.RealWorld → Prop} {I : Void IO.RealWorld → Prop}
    {α : Type} {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    (hA : AdmCtx q mctx cctx) {x : MetaM α} (f : Meta.Context → Meta.Context)
    (hf : ∀ m, (f m).canUnfold? = m.canUnfold?)
    (h : AdmCtx q (f mctx) cctx → Triple (f mctx) mref cctx cref I x Q R) :
    Triple mctx mref cctx cref I (withReader f x) Q R :=
  fun w hw => h (fun g hg => hA g ((hf mctx).symm.trans hg)) w hw

theorem triple_of_ok {α : Type} {I : Void IO.RealWorld → Prop} {m : MetaM α}
    {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    (h : ∀ w, ∃ a, m mctx mref cctx cref w = .ok a w) (hQ : ∀ a w, I w → Q a w) :
    Triple mctx mref cctx cref I m Q R := by
  intro w hw
  obtain ⟨a, ha⟩ := h w
  rw [ha]
  exact hQ a w hw

/-- **A lifted `MetaM` action whose result carries a fact** (`φ`), followed by the rest: the lift leaves the state, and the rest is asked
only for results with the fact. (The first premise may use `StatePF st`.) -/
theorem KCS.bindLiftQ {α β : Type} {I : Void IO.RealWorld → Prop} {st : CircuitState} {m : MetaM α} {φ : α → Prop}
    {f : α → CompilerM β}
    (h1 : StatePF st → Triple mctx mref cctx cref I m (fun a w => I w ∧ φ a) (fun e w => I w ∧ OkExc e))
    (h2 : ∀ a, φ a → KCS mctx mref cctx cref I st (f a)) :
    KCS mctx mref cctx cref I st (CompilerM.liftMetaM m >>= f) := by
  intro ctx hc hs
  refine Triple.bind (Q := fun p w => I w ∧ p.2 = st ∧ φ p.1) ?_ (fun p => ?_)
  · exact Triple.bind (h1 hs) fun a => Triple.pure (a := (a, st)) fun w hw => ⟨hw.1, rfl, hw.2⟩
  · obtain ⟨a, s0⟩ := p
    intro w hw
    obtain ⟨hI, hst, hφ⟩ := hw
    have hst' : s0 = st := hst
    subst hst'
    exact (h2 a hφ ctx hc hs) w hI

/-- the unpointed form of `KCS.bindLiftQ` -/
theorem KeepsCS.bindLiftQ {α β : Type} {I : Void IO.RealWorld → Prop} {m : MetaM α} {φ : α → Prop}
    {f : α → CompilerM β}
    (h1 : Triple mctx mref cctx cref I m (fun a w => I w ∧ φ a) (fun e w => I w ∧ OkExc e))
    (h2 : ∀ a, φ a → KeepsCS mctx mref cctx cref I (f a)) :
    KeepsCS mctx mref cctx cref I (CompilerM.liftMetaM m >>= f) :=
  fun st => KCS.bindLiftQ (fun _ => h1) (fun a ha => h2 a ha st)

section Laws
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I)
include M hA hS

/-- **`withLocalDeclD` returns what its continuation returns** (derived from the Lean definitions; the postcondition `Q` of the
continuation is the postcondition of the whole). -/
theorem withLocalDeclT {α : Type} {Q : α → Void IO.RealWorld → Prop} (n : Name) (ty : Lean.Expr)
    (k : Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx O.quiet mctx' cctx' →
      Triple mctx' mref cctx' cref I (k x) Q (fun e w => I w ∧ OkExc e)) :
    Triple mctx mref cctx cref I (Lean.Meta.withLocalDeclD n ty k) Q (fun e w => I w ∧ OkExc e) := by
  unfold Lean.Meta.withLocalDeclD Lean.Meta.withLocalDecl Lean.Meta.map1MetaM
  unfold controlAt
  unfold_suffix withLocalDeclImp
  refine Triple.bind (Q := Q) ?_ (fun a => Triple.pure (fun w hw => hw))
  dsimp only [liftWith, instMonadControlTOfPure]
  refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA hS FramedNM.freshFVar)) (fun fvarId => ?_)
  refine triple_read_bind ?_
  refine triple_withReaderA hA _ (fun m => rfl) (fun hA' => ?_)
  unfold_suffix withNewFVar
  refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA' hS (FramedNM.isClass? _))) (fun cc => ?_)
  cases cc with
  | none => exact hk _ cctx _ hA'
  | some c =>
    show Triple _ mref cctx cref I (withNewLocalInstance c (mkFVar fvarId) (k (mkFVar fvarId))) Q _
    unfold Lean.Meta.withNewLocalInstance Lean.Meta.mapMetaM
    unfold controlAt
    unfold_suffix withNewLocalInstanceImp
    refine Triple.bind (Q := Q) ?_ (fun a => Triple.pure (fun w hw => hw))
    dsimp only [liftWith, instMonadControlTOfPure]
    unfold Lean.Meta.getFVarLocalDecl Lean.FVarId.getDecl
    refine Triple.bind (Q := fun _ => I) (Triple.bind (Q := fun _ => I) (triple_of_ok (fun w => ⟨_, rfl⟩) (fun _ _ h => h))
      (fun l => ?_)) (fun d => ?_)
    · split
      · exact Triple.pure (fun w hw => hw)
      · exact keeps_iff.mp (keepsK_framedNM M hA' hS (FramedNM.fvarThrowUnknown _))
    · split
      · exact hk _ cctx _ hA'
      · exact triple_withReaderA hA' _ (fun m => rfl) (fun h => hk _ cctx _ h)

theorem withLetDeclT {α : Type} {Q : α → Void IO.RealWorld → Prop} (n : Name) (ty v : Lean.Expr)
    (k : Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx O.quiet mctx' cctx' →
      Triple mctx' mref cctx' cref I (k x) Q (fun e w => I w ∧ OkExc e)) :
    Triple mctx mref cctx cref I (Lean.Meta.withLetDecl n ty v k) Q (fun e w => I w ∧ OkExc e) := by
  unfold Lean.Meta.withLetDecl Lean.Meta.map1MetaM
  unfold controlAt
  unfold_suffix withLetDeclImp
  refine Triple.bind (Q := Q) ?_ (fun a => Triple.pure (fun w hw => hw))
  dsimp only [liftWith, instMonadControlTOfPure]
  refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA hS FramedNM.freshFVar)) (fun fvarId => ?_)
  refine triple_read_bind ?_
  refine triple_withReaderA hA _ (fun m => rfl) (fun hA' => ?_)
  unfold_suffix withNewFVar
  refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA' hS (FramedNM.isClass? _))) (fun cc => ?_)
  cases cc with
  | none => exact hk _ cctx _ hA'
  | some c =>
    show Triple _ mref cctx cref I (withNewLocalInstance c (mkFVar fvarId) (k (mkFVar fvarId))) Q _
    unfold Lean.Meta.withNewLocalInstance Lean.Meta.mapMetaM
    unfold controlAt
    unfold_suffix withNewLocalInstanceImp
    refine Triple.bind (Q := Q) ?_ (fun a => Triple.pure (fun w hw => hw))
    dsimp only [liftWith, instMonadControlTOfPure]
    unfold Lean.Meta.getFVarLocalDecl Lean.FVarId.getDecl
    refine Triple.bind (Q := fun _ => I) (Triple.bind (Q := fun _ => I) (triple_of_ok (fun w => ⟨_, rfl⟩) (fun _ _ h => h))
      (fun l => ?_)) (fun d => ?_)
    · split
      · exact Triple.pure (fun w hw => hw)
      · exact keeps_iff.mp (keepsK_framedNM M hA' hS (FramedNM.fvarThrowUnknown _))
    · split
      · exact hk _ cctx _ hA'
      · exact triple_withReaderA hA' _ (fun m => rfl) (fun h => hk _ cctx _ h)

/-- **`CompilerM.withLocalDecl` for `KeepsCS`**: the continuation's final state is the whole's (`set newS`). -/
theorem withLocalDeclPS {α : Type} (n : Name) (ty : Lean.Expr) (k : Lean.Expr → CompilerM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' → ∀ x,
      KeepsCS mctx' mref cctx' cref I (k x)) :
    KeepsCS mctx mref cctx cref I (CompilerM.withLocalDecl n ty k) := by
  intro st
  unfold CompilerM.withLocalDecl
  refine KCS.bindRead (fun cs hcs => ?_)
  refine KCS.bindGet ?_
  refine KCS.bindLiftQ (φ := fun p => GoodS st p.2) (fun hs => ?_) (fun p hp => ?_)
  · exact withLocalDeclT M hA hS n ty _ (fun mctx' cctx' x hA' => hk mctx' cctx' hA' x st cs hcs hs)
  · obtain ⟨res, newS⟩ := p
    exact KCS.bind (KCS.set newS (fun _ => hp)) (fun _ _ _ => KCS.pure res)

theorem withLetDeclPS {α : Type} (n : Name) (ty v : Lean.Expr) (k : Lean.Expr → CompilerM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' → ∀ x,
      KeepsCS mctx' mref cctx' cref I (k x)) :
    KeepsCS mctx mref cctx cref I (CompilerM.withLetDecl n ty v k) := by
  intro st
  unfold CompilerM.withLetDecl
  refine KCS.bindRead (fun cs hcs => ?_)
  refine KCS.bindGet ?_
  refine KCS.bindLiftQ (φ := fun p => GoodS st p.2) (fun hs => ?_) (fun p hp => ?_)
  · exact withLetDeclT M hA hS n ty v _ (fun mctx' cctx' x hA' => hk mctx' cctx' hA' x st cs hcs hs)
  · obtain ⟨res, newS⟩ := p
    exact KCS.bind (KCS.set newS (fun _ => hp)) (fun _ _ _ => KCS.pure res)

end Laws

end Tools.ShippingGen4FKidsTele
