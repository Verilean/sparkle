import Tools.ShippingChildFrontCP
import Tools.ShippingMixedSourceBridge
-- UNBUILT (unit SR6, L8al part B): see REPORT-SR6.md for run names / exits at the final committed SHA.
-- No `sorry`, no `axiom`, no `native_decide`, no new RefLawsAOps/RefLawsATele field.

/-! # `KeepsCP` restricted to compiler contexts that bind given fvars (unit SR6)

`KeepsCQ P I c`: for every compiler context `ctx` with `CtxOk ctx` AND `P ctx`, `c` keeps `I`. The combinators
mirror `KeepsCP`'s (`Tools.ShippingChildTranslateA`); `ofCP` embeds a `KeepsCP`. `P` is used for ONE thing: the
fvars of the leaf expression are bound in the reader context (`BoundIn`), so `lookupVar` returns `some _` and
the core of the translator does not fall through to the instance arm. -/

namespace Tools.ShippingLeafCtxQ
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildTranslateA
open Tools.ShippingChildFallbackA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildPathA
open Tools.ShippingChildFrontA Tools.ShippingChildFrontCP Tools.ShippingChildTranslatePathA
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `KeepsCP` restricted to the compiler contexts satisfying `P` (here: the fvars of the leaf are bound). -/
def KeepsCQ (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (P : CompilerState → Prop)
    {α : Type} (I : Void IO.RealWorld → Prop) (c : CompilerM α) : Prop :=
  ∀ (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx → P ctx →
    Keeps mctx mref cctx cref I (c ctx st)

/-- `KeepsCQ` for an action that also returns `some _`. -/
def SomeCQ (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (P : CompilerState → Prop)
    {β : Type} (I : Void IO.RealWorld → Prop) (c : CompilerM (Option β)) : Prop :=
  ∀ (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx → P ctx →
    Triple mctx mref cctx cref I (c ctx st) (fun p w => I w ∧ ∃ x, p.1 = some x)
      (fun e w => I w ∧ OkExc e)

section CQ
variable {P : CompilerState → Prop} {I : Void IO.RealWorld → Prop}

theorem KeepsCQ.ofCP {α : Type} {c : CompilerM α} (h : KeepsCP mctx mref cctx cref I c) :
    KeepsCQ mctx mref cctx cref P I c := fun ctx st hc _ => h ctx st hc

theorem KeepsCQ.pure {α : Type} (a : α) : KeepsCQ mctx mref cctx cref P I (Pure.pure a : CompilerM α) :=
  KeepsCQ.ofCP (KeepsCP.pure a)

theorem KeepsCQ.bind {α β : Type} {c : CompilerM α} {f : α → CompilerM β}
    (h1 : KeepsCQ mctx mref cctx cref P I c) (h2 : ∀ a, KeepsCQ mctx mref cctx cref P I (f a)) :
    KeepsCQ mctx mref cctx cref P I (c >>= f) :=
  fun ctx st hc hp => keeps_iff.mpr (Triple.bind (keeps_iff.mp (h1 ctx st hc hp)) fun p => by
    obtain ⟨a, s⟩ := p
    exact keeps_iff.mp (h2 a ctx s hc hp))

theorem KeepsCQ.ite {α : Type} {c : Prop} [Decidable c] {a b : CompilerM α}
    (ha : c → KeepsCQ mctx mref cctx cref P I a) (hb : ¬c → KeepsCQ mctx mref cctx cref P I b) :
    KeepsCQ mctx mref cctx cref P I (if c then a else b) := by
  by_cases hc : c
  · rw [if_pos hc]; exact ha hc
  · rw [if_neg hc]; exact hb hc

/-- A bind whose first action returns `some _`: the `none` continuation is not asked for. -/
theorem KeepsCQ.bindSome {β γ : Type} {c : CompilerM (Option β)} {f : Option β → CompilerM γ}
    (h1 : SomeCQ mctx mref cctx cref P I c)
    (h2 : ∀ x, KeepsCQ mctx mref cctx cref P I (f (some x))) :
    KeepsCQ mctx mref cctx cref P I (c >>= f) :=
  fun ctx st hc hp => keeps_iff.mpr (Triple.bind (h1 ctx st hc hp) fun p => by
    obtain ⟨a, s⟩ := p
    intro w hw
    obtain ⟨hI, x, hx⟩ := hw
    have hx' : a = some x := hx
    subst hx'
    exact keeps_iff.mp (h2 x ctx s hc hp) w hI)

theorem SomeCQ.pure {β : Type} (x : β) :
    SomeCQ mctx mref cctx cref P I (Pure.pure (some x) : CompilerM (Option β)) :=
  fun _ st _ _ => Triple.pure (a := (some x, st)) (fun _ hw => ⟨hw, x, rfl⟩)

theorem SomeCQ.bindK {α β : Type} {c : CompilerM α} {f : α → CompilerM (Option β)}
    (h1 : KeepsCQ mctx mref cctx cref P I c) (h2 : ∀ a, SomeCQ mctx mref cctx cref P I (f a)) :
    SomeCQ mctx mref cctx cref P I (c >>= f) :=
  fun ctx st hc hp => Triple.bind (keeps_iff.mp (h1 ctx st hc hp)) fun p => by
    obtain ⟨a, s⟩ := p
    exact h2 a ctx s hc hp



theorem KeepsCQ.weaken {Q : CompilerState → Prop} {α : Type} {c : CompilerM α}
    (h : KeepsCQ mctx mref cctx cref Q I c) (hPQ : ∀ ctx, P ctx → Q ctx) :
    KeepsCQ mctx mref cctx cref P I c := fun ctx st hc hp => h ctx st hc (hPQ ctx hp)

theorem KeepsCQ.lift {α : Type} {m : MetaM α} (h : Keeps mctx mref cctx cref I m) :
    KeepsCQ mctx mref cctx cref P I (CompilerM.liftMetaM m) := KeepsCQ.ofCP (KeepsCP.lift h)

theorem KeepsCQ.get : KeepsCQ mctx mref cctx cref P I
    (get : CompilerM Sparkle.IR.Builder.CircuitState) := KeepsCQ.ofCP KeepsCP.get

theorem KeepsCQ.throwBind {α β : Type} (e : Exception) (he : OkExc e) (k : α → CompilerM β) :
    KeepsCQ mctx mref cctx cref P I ((MonadExcept.throw e : CompilerM α) >>= k) :=
  KeepsCQ.ofCP (KeepsCP.throwBind e he k)

end CQ

/-! ## The binder walk under `BoundIn` -/

/-- The non-domain binders of `l` are bound in the reader context. -/
def BoundIn (l : List ((Name × MixedGateBinder) × FVarId)) (ctx : CompilerState) : Prop :=
  ∀ p ∈ l, p.1.2 ≠ MixedGateBinder.domain → ∃ w, ctx.varMap.lookup p.2 = some w

theorem lookup_cons_isSome (q fv : FVarId) (wn : String) (m : List (FVarId × String))
    (h : ∃ w, m.lookup q = some w) : ∃ w, ((fv, wn) :: m).lookup q = some w := by
  obtain ⟨w, hw⟩ := h
  by_cases hq : q = fv
  · subst hq
    exact ⟨wn, by simp [List.lookup_cons, (fvarId_beq_iff q q).mpr rfl]⟩
  · refine ⟨w, ?_⟩
    have hb : (q == fv) = false := by
      cases h : (q == fv)
      · rfl
      · exact absurd ((fvarId_beq_iff _ _).mp h) hq
    simp [List.lookup_cons, hb, hw]

theorem boundIn_extend (pre : List ((Name × MixedGateBinder) × FVarId))
    (p : (Name × MixedGateBinder) × FVarId) (wn : String) (ctx : CompilerState)
    (h : BoundIn pre ctx) :
    BoundIn (pre ++ [p]) { ctx with varMap := (p.2, wn) :: ctx.varMap } := by
  intro q hq hne
  rcases List.mem_append.mp hq with hq | hq
  · exact lookup_cons_isSome q.2 p.2 wn ctx.varMap (h q hq hne)
  · have : q = p := List.mem_singleton.mp hq
    subst this
    exact ⟨wn, by simp [List.lookup_cons, (fvarId_beq_iff q.2 q.2).mpr rfl]⟩

section Bind
variable {P Q : CompilerState → Prop} {I : Void IO.RealWorld → Prop}

theorem withVarMappingQ {α : Type} (fv : FVarId) (wn : String) {k : CompilerM α}
    (hk : KeepsCQ mctx mref cctx cref Q I k)
    (hPQ : ∀ ctx, P ctx → Q { ctx with varMap := (fv, wn) :: ctx.varMap }) :
    KeepsCQ mctx mref cctx cref P I (CompilerM.withVarMapping fv wn k) := by
  unfold CompilerM.withVarMapping
  intro ctx st hc hp
  exact hk { ctx with varMap := (fv, wn) :: ctx.varMap } st (fun r h => hc r h) (hPQ ctx hp)

variable (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
  (hS : StableA O.quiet I)
include O hA hS

theorem bindInputPortQ {α : Type} (fv : FVarId) (bn : String) (ty : Sparkle.IR.Type.HWType)
    {k : CompilerM α} (hk : KeepsCQ mctx mref cctx cref Q I k)
    (hPQ : ∀ ctx wn, P ctx → Q { ctx with varMap := (fv, wn) :: ctx.varMap }) :
    KeepsCQ mctx mref cctx cref P I (bindInputPort fv bn ty k) := by
  unfold bindInputPort
  refine KeepsCQ.bind (KeepsCQ.ofCP (makeWireP O hA hS _ _ _)) (fun w => ?_)
  refine KeepsCQ.bind (KeepsCQ.ofCP (addInputP O hA hS _ _)) (fun _ => ?_)
  exact withVarMappingQ fv w hk (fun ctx => hPQ ctx w)

/-- **The mixed binder walk under `BoundIn`**: if the continuation keeps `I` in contexts that bind ALL the
non-domain binders of `pre ++ l`, the walk of `l` keeps `I` in contexts that bind those of `pre`. -/
theorem bindMixedQ {α : Type} (k : CompilerM α) :
    ∀ (l pre : List ((Name × MixedGateBinder) × FVarId)),
      KeepsCQ mctx mref cctx cref (BoundIn (pre ++ l)) I k →
      KeepsCQ mctx mref cctx cref (BoundIn pre) I (bindMixedCertifiedInputs k l)
  | [], pre, hk => by
    unfold bindMixedCertifiedInputs
    simpa using hk
  | ((nm, .domain), fv) :: rest, pre, hk => by
    unfold bindMixedCertifiedInputs
    refine KeepsCQ.weaken (bindMixedQ k rest (pre ++ [((nm, .domain), fv)]) ?_) ?_
    · simpa using hk
    · intro ctx h q hq hne
      rcases List.mem_append.mp hq with hq | hq
      · exact h q hq hne
      · have := List.mem_singleton.mp hq
        subst this
        exact absurd rfl hne
  | ((nm, .bool), fv) :: rest, pre, hk => by
    unfold bindMixedCertifiedInputs
    refine bindInputPortQ O hA hS fv _ _ (bindMixedQ k rest (pre ++ [((nm, .bool), fv)]) ?_) ?_
    · simpa using hk
    · intro ctx wn h
      exact boundIn_extend pre ((nm, .bool), fv) wn ctx h
  | ((nm, .bits n), fv) :: rest, pre, hk => by
    unfold bindMixedCertifiedInputs
    refine bindInputPortQ O hA hS fv _ _ (bindMixedQ k rest (pre ++ [((nm, .bits n), fv)]) ?_) ?_
    · simpa using hk
    · intro ctx wn h
      exact boundIn_extend pre ((nm, .bits n), fv) wn ctx h

end Bind

end Tools.ShippingLeafCtxQ
