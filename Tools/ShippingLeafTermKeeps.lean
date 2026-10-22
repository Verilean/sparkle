import Tools.ShippingLeafBodyCi
import Tools.ShippingUnifiedRecursion
import Tools.ShippingVectorMuxRecursion
import Tools.ShippingUnifiedMeaning
-- UNBUILT (unit SR6, L8al part B): see REPORT-SR6.md.

namespace Tools.ShippingLeafTermKeeps
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildTranslateA
open Tools.ShippingChildFallbackA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildPathA Tools.ShippingChildFrontA Tools.ShippingChildFrontCP

open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge Tools.ShippingBoolSourceSoundness
open Tools.ShippingUnifiedRecursion (setw_step setwUncached_setwE slice_step sliceUncached_sliceE
  zextMap_step setwUncached_zextMapE sliceF_step sliceFUncached_sliceFE concat_step
  concatUncached_concatE concatLitHi_step concatLitLo_step concatLitUncached_hiE
  concatLitUncached_loE appCompare_step appBool_step appBool2_step isBoolControl_appCompareE
  isBoolControl_appBoolE isBoolControl_appBool2E translateBoolUncachedWith_appCompare
  translateBoolUncachedWith_appBool translateBoolUncachedWith_appBool2)
open Tools.ShippingMixedRecursion (compare_step boolBin_step boolEq_step boolNot_step
  translateBoolUncachedWith_boolBin)
open Tools.ShippingBoolMuxSoundness (boolMux_step boolMux_uncached boolMuxE)
open Tools.ShippingVectorMuxRecursion (vector_step vectorMuxUncached_muxE)
open Tools.ShippingCompareLoweringSoundness (translateBoolUncachedWith_compare)
open Tools.ShippingBoolLiteralSoundness (literal_core literal_uncached literalE)
open Tools.ShippingMuxTypeSoundness (muxE bitVecE)

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

end CQ

section Walk
variable (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I) {P : CompilerState → Prop}
include O hA hS

/-- **One step of the knot at a node whose core returns `some _`**: the validated lookup, the core, the record. -/
theorem stepQ (fallback : TranslateFn → TranslateFn) (rec : TranslateFn) (e : Lean.Expr)
    (hint : String) (top named : Bool)
    (hcore : SomeCQ mctx mref cctx cref P I (translateCore rec e hint top named)) :
    KeepsCQ mctx mref cctx cref P I (translateStepWith fallback rec e hint top named) := by
  unfold translateStepWith
  dsimp only
  refine KeepsCQ.ite (fun _ => ?_) (fun _ => ?_)
  · refine KeepsCQ.bind (KeepsCQ.ofCP (cacheLookupValidatedA O hA hS _)) (fun x => ?_)
    cases x with
    | some w => exact KeepsCQ.pure _
    | none =>
      refine KeepsCQ.bindSome hcore (fun w => ?_)
      exact KeepsCQ.ite (fun _ => KeepsCQ.pure _)
        (fun _ => KeepsCQ.bind (KeepsCQ.ofCP (recordTranslationA O hA hS _ _ _))
          (fun _ => KeepsCQ.pure _))
  · refine KeepsCQ.bindSome hcore (fun w => ?_)
    exact KeepsCQ.ite (fun _ => KeepsCQ.pure _)
      (fun _ => KeepsCQ.bind (KeepsCQ.ofCP (recordTranslationA O hA hS _ _ _))
        (fun _ => KeepsCQ.pure _))

/-- The validated-cache wrapper at one node, given its lowering at that node. -/
theorem controlCachedQ (lower : TranslateFn) (e : Lean.Expr) (hint : String) (top named : Bool)
    (hlow : KeepsCQ mctx mref cctx cref P I (lower e hint top named)) :
    KeepsCQ mctx mref cctx cref P I (translateControlCachedWith lower e hint top named) := by
  unfold translateControlCachedWith
  dsimp only
  refine KeepsCQ.ite (fun _ => ?_) (fun _ => ?_)
  · refine KeepsCQ.bind (KeepsCQ.ofCP (cacheLookupValidatedA O hA hS _)) (fun x => ?_)
    cases x with
    | some w => exact KeepsCQ.pure _
    | none =>
      exact KeepsCQ.bind hlow (fun w => KeepsCQ.bind
        (KeepsCQ.ofCP (recordTranslationA O hA hS _ _ _)) (fun _ => KeepsCQ.pure _))
  · exact KeepsCQ.bind hlow (fun w => KeepsCQ.bind
      (KeepsCQ.ofCP (recordTranslationA O hA hS _ _ _)) (fun _ => KeepsCQ.pure _))


/-- The recursive translator keeps `I` (in `P`-contexts) at the expression `a`, at every hint/flag. -/
def KidQ (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (P : CompilerState → Prop)
    (I : Void IO.RealWorld → Prop) (rec : TranslateFn) (a : Lean.Expr) : Prop :=
  ∀ hint top named, KeepsCQ mctx mref cctx cref P I (rec a hint top named)

theorem muxWithQ (rec : TranslateFn) (resultType : CompilerM Sparkle.IR.Type.HWType)
    (hres : KeepsCQ mctx mref cctx cref P I resultType) {c t el : Lean.Expr}
    (hc : KidQ mctx mref cctx cref P I rec c) (ht : KidQ mctx mref cctx cref P I rec t)
    (he : KidQ mctx mref cctx cref P I rec el) (hint : String) (named : Bool) :
    KeepsCQ mctx mref cctx cref P I (translateMuxWith rec resultType c t el hint named) := by
  unfold translateMuxWith
  refine KeepsCQ.bind (hc _ _ _) (fun _ => ?_)
  refine KeepsCQ.bind (ht _ _ _) (fun _ => ?_)
  refine KeepsCQ.bind (he _ _ _) (fun _ => ?_)
  refine KeepsCQ.bind hres (fun _ => ?_)
  exact KeepsCQ.ofCP (emitMuxResultA O hA hS _ _ _ _ _ _)

theorem boolBinaryQ (rec : TranslateFn) (kind : SignalBoolBinKind) {a b : Lean.Expr}
    (ha : KidQ mctx mref cctx cref P I rec a) (hb : KidQ mctx mref cctx cref P I rec b)
    (hint : String) (named : Bool) :
    KeepsCQ mctx mref cctx cref P I (translateBoolBinary rec kind a b hint named) := by
  unfold translateBoolBinary
  refine KeepsCQ.bind (ha _ _ _) (fun _ => ?_)
  refine KeepsCQ.bind (hb _ _ _) (fun _ => ?_)
  exact KeepsCQ.ofCP (emitBoolResultA O hA hS _ _ _)

theorem signalCompareQ (rec : TranslateFn) (le : SignalCompareKind) {a b : Lean.Expr}
    (ha : KidQ mctx mref cctx cref P I rec a) (hb : KidQ mctx mref cctx cref P I rec b)
    (hint : String) (named : Bool) :
    KeepsCQ mctx mref cctx cref P I (translateSignalCompare rec le a b hint named) := by
  unfold translateSignalCompare
  refine KeepsCQ.bind (ha _ _ _) (fun _ => ?_)
  refine KeepsCQ.bind (hb _ _ _) (fun _ => ?_)
  exact KeepsCQ.ofCP (emitCompareResultA O hA hS _ _ _ _ _)

theorem appCompareQ (rec : TranslateFn) (le : SignalCompareKind) {a b : Lean.Expr}
    (ha : KidQ mctx mref cctx cref P I rec a) (hb : KidQ mctx mref cctx cref P I rec b)
    (hint : String) (named : Bool) :
    KeepsCQ mctx mref cctx cref P I (translateAppCompare rec le a b hint named) := by
  unfold translateAppCompare
  refine KeepsCQ.bind (ha _ _ _) (fun _ => ?_)
  refine KeepsCQ.bind (hb _ _ _) (fun _ => ?_)
  exact KeepsCQ.ofCP (emitCompareResultA O hA hS _ _ _ _ _)

theorem appBoolBinaryQ (rec : TranslateFn) (kind : SignalBoolBinKind) {a b : Lean.Expr}
    (ha : KidQ mctx mref cctx cref P I rec a) (hb : KidQ mctx mref cctx cref P I rec b)
    (hint : String) (named : Bool) :
    KeepsCQ mctx mref cctx cref P I (translateAppBoolBinary rec kind a b hint named) := by
  unfold translateAppBoolBinary
  refine KeepsCQ.bind (ha _ _ _) (fun _ => ?_)
  refine KeepsCQ.bind (hb _ _ _) (fun _ => ?_)
  exact KeepsCQ.ofCP (emitBoolResultA O hA hS _ _ _)

theorem appBool2Q (rec : TranslateFn) (f : AppBool2) {a b : Lean.Expr}
    (ha : KidQ mctx mref cctx cref P I rec a) (hb : KidQ mctx mref cctx cref P I rec b)
    (hint : String) (named : Bool) :
    KeepsCQ mctx mref cctx cref P I (translateAppBool2 rec f a b hint named) := by
  unfold translateAppBool2
  refine KeepsCQ.bind (ha _ _ _) (fun _ => ?_)
  refine KeepsCQ.bind (hb _ _ _) (fun _ => ?_)
  refine KeepsCQ.bind (KeepsCQ.ofCP (emitBoolResultA O hA hS _ _ _)) (fun _ => ?_)
  exact KeepsCQ.ofCP (emitBoolResultA O hA hS _ _ _)

theorem concatActsQ (w : Nat) {hiAct loAct : CompilerM String}
    (hhi : KeepsCQ mctx mref cctx cref P I hiAct) (hlo : KeepsCQ mctx mref cctx cref P I loAct)
    (hint : String) (named : Bool) :
    KeepsCQ mctx mref cctx cref P I (translateConcatActs w hiAct loAct hint named) := by
  unfold translateConcatActs
  refine KeepsCQ.bind (KeepsCQ.ofCP (makeWireP O hA hS _ _ _)) (fun _ => ?_)
  refine KeepsCQ.bind hhi (fun _ => ?_)
  refine KeepsCQ.bind hlo (fun _ => ?_)
  refine KeepsCQ.bind (KeepsCQ.ofCP (emitAssignP _ _)) (fun _ => ?_)
  exact KeepsCQ.pure _

/-! ### The nodes (step equations of `Tools.ShippingUnifiedRecursion` / `ShippingMixedRecursion`) -/

variable {tenv : Lean.Environment}

theorem node_setw (rec : TranslateFn) (dom ae : Lean.Expr) (ws wt : Nat) (hws : 0 < ws) (hwt : 0 < wt)
    (ha : KidQ mctx mref cctx cref P I rec ae) (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I
      (translateStepWith (translateFallback tenv) rec (setwE dom ws wt ae) hint top named) := by
  rw [setw_step rec dom ae ws wt hws hwt hint top named]
  refine controlCachedQ O hA hS _ _ _ _ _ ?_
  rw [setwUncached_setwE]
  exact KeepsCQ.bind (ha _ _ _) (fun _ => KeepsCQ.ofCP (emitCastResultA O hA hS _ _ _ _))

theorem node_slice (rec : TranslateFn) (dom ae : Lean.Expr) (nm : Lean.Name) (ws start len : Nat)
    (hlen : 0 < len) (hr : start + len ≤ ws)
    (ha : KidQ mctx mref cctx cref P I rec ae) (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I
      (translateStepWith (translateFallback tenv) rec (sliceE dom nm ws start len ae) hint top named) := by
  rw [slice_step rec dom ae nm ws start len hint top named hlen hr]
  refine controlCachedQ O hA hS _ _ _ _ _ ?_
  rw [sliceUncached_sliceE]
  exact KeepsCQ.bind (ha _ _ _) (fun _ => KeepsCQ.ofCP (emitSliceResultA O hA hS _ _ _ _))

theorem node_zextMap (rec : TranslateFn) (dom ae : Lean.Expr) (nm : Lean.Name) (k n : Nat)
    (hk : 0 < k) (hn : 0 < n)
    (ha : KidQ mctx mref cctx cref P I rec ae) (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I
      (translateStepWith (translateFallback tenv) rec (zextMapE dom nm k n ae) hint top named) := by
  rw [zextMap_step rec dom nm ae k n hint top named hk hn]
  refine controlCachedQ O hA hS _ _ _ _ _ ?_
  rw [setwUncached_zextMapE]
  exact KeepsCQ.bind (ha _ _ _) (fun _ => KeepsCQ.ofCP (emitCastResultA O hA hS _ _ _ _))

theorem node_sliceF (rec : TranslateFn) (dom ae : Lean.Expr) (nm : Lean.Name) (w start len : Nat)
    (hlen : 0 < len) (hr : start + len ≤ w)
    (ha : KidQ mctx mref cctx cref P I rec ae) (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I
      (translateStepWith (translateFallback tenv) rec (sliceFE dom nm w start len ae) hint top named) := by
  rw [sliceF_step rec dom nm ae w start len hint top named hlen hr]
  refine controlCachedQ O hA hS _ _ _ _ _ ?_
  rw [sliceFUncached_sliceFE]
  exact KeepsCQ.bind (ha _ _ _) (fun _ => KeepsCQ.ofCP (emitSliceResultA O hA hS _ _ _ _))

theorem node_concat (rec : TranslateFn) (dom ae be : Lean.Expr) (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (ha : KidQ mctx mref cctx cref P I rec ae) (hb : KidQ mctx mref cctx cref P I rec be)
    (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I
      (translateStepWith (translateFallback tenv) rec (concatE dom m n ae be) hint top named) := by
  rw [concat_step rec dom ae be m n hint top named hm hn]
  refine controlCachedQ O hA hS _ _ _ _ _ ?_
  rw [concatUncached_concatE]
  unfold translateConcatWith
  exact concatActsQ O hA hS _ (ha _ _ _) (hb _ _ _) _ _

theorem node_concatLitHi (rec : TranslateFn) (dom be : Lean.Expr) (k v n : Nat) (hk : 0 < k)
    (hv : v < 2 ^ k) (hn : 0 < n)
    (hb : KidQ mctx mref cctx cref P I rec be) (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I
      (translateStepWith (translateFallback tenv) rec (concatLitHiE dom k v n be) hint top named) := by
  rw [concatLitHi_step rec dom be k v n hint top named hk hv hn]
  refine controlCachedQ O hA hS _ _ _ _ _ ?_
  rw [concatLitUncached_hiE]
  exact concatActsQ O hA hS _ (KeepsCQ.ofCP (emitConcatConstA O hA hS _ _)) (hb _ _ _) _ _

theorem node_concatLitLo (rec : TranslateFn) (dom ae : Lean.Expr) (m k v : Nat) (hk : 0 < k)
    (hv : v < 2 ^ k) (hm : 0 < m)
    (ha : KidQ mctx mref cctx cref P I rec ae) (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I
      (translateStepWith (translateFallback tenv) rec (concatLitLoE dom m k v ae) hint top named) := by
  rw [concatLitLo_step rec dom ae m k v hint top named hk hv hm]
  refine controlCachedQ O hA hS _ _ _ _ _ ?_
  rw [concatLitUncached_loE]
  exact concatActsQ O hA hS _ (ha _ _ _) (KeepsCQ.ofCP (emitConcatConstA O hA hS _ _)) _ _

theorem node_compare (rec : TranslateFn) (dom ae be : Lean.Expr) (n : Nat) (le : SignalCompareKind)
    (ha : KidQ mctx mref cctx cref P I rec ae) (hb : KidQ mctx mref cctx cref P I rec be)
    (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I
      (translateStepWith (translateFallback tenv) rec (compareE le dom n ae be) hint top named) := by
  rw [compare_step rec dom ae be n le hint top named,
    translateFallback_bool rec _ hint top named (by cases le <;> rfl)]
  refine controlCachedQ O hA hS _ _ _ _ _ ?_
  rw [translateBoolUncachedWith_compare]
  exact signalCompareQ O hA hS rec le ha hb _ _

theorem node_boolBin (rec : TranslateFn) (kind : SignalBoolBinKind) (dom ae be : Lean.Expr)
    (ha : KidQ mctx mref cctx cref P I rec ae) (hb : KidQ mctx mref cctx cref P I rec be)
    (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I
      (translateStepWith (translateFallback tenv) rec (boolBinE kind dom ae be) hint top named) := by
  rw [boolBin_step rec kind dom ae be hint top named,
    translateFallback_bool rec _ hint top named (by cases kind <;> rfl)]
  refine controlCachedQ O hA hS _ _ _ _ _ ?_
  rw [translateBoolUncachedWith_boolBin]
  exact boolBinaryQ O hA hS rec kind ha hb _ _

theorem node_boolEq (rec : TranslateFn) (dom ae be : Lean.Expr)
    (ha : KidQ mctx mref cctx cref P I rec ae) (hb : KidQ mctx mref cctx cref P I rec be)
    (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I
      (translateStepWith (translateFallback tenv) rec (boolEqE dom ae be) hint top named) := by
  rw [boolEq_step rec dom ae be hint top named, translateFallback_bool rec _ hint top named rfl]
  refine controlCachedQ O hA hS _ _ _ _ _ ?_
  change KeepsCQ mctx mref cctx cref P I (translateSignalCompare rec .eq ae be hint named)
  exact signalCompareQ O hA hS rec .eq ha hb _ _

theorem node_boolNot (rec : TranslateFn) (dom ae : Lean.Expr)
    (ha : KidQ mctx mref cctx cref P I rec ae)
    (hb : KidQ mctx mref cctx cref P I rec
      (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (.const ``Bool [])
        (.const ``Bool.false [])))
    (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I
      (translateStepWith (translateFallback tenv) rec (boolNotE dom ae) hint top named) := by
  rw [boolNot_step rec dom ae hint top named, translateFallback_bool rec _ hint top named rfl]
  refine controlCachedQ O hA hS _ _ _ _ _ ?_
  change KeepsCQ mctx mref cctx cref P I (translateSignalCompare rec .eq ae
    (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (.const ``Bool [])
      (.const ``Bool.false [])) hint named)
  exact signalCompareQ O hA hS rec .eq ha hb _ _

theorem node_boolMux (rec : TranslateFn) (dom ce ae be : Lean.Expr)
    (hc : KidQ mctx mref cctx cref P I rec ce) (ha : KidQ mctx mref cctx cref P I rec ae)
    (hb : KidQ mctx mref cctx cref P I rec be) (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I
      (translateStepWith (translateFallback tenv) rec (boolMuxE dom ce ae be) hint top named) := by
  rw [boolMux_step rec dom ce ae be hint top named, translateFallback_bool rec _ hint top named rfl]
  refine controlCachedQ O hA hS _ _ _ _ _ ?_
  rw [boolMux_uncached]
  exact muxWithQ O hA hS rec _ (KeepsCQ.pure _) hc ha hb _ _

theorem node_vectorMux (rec : TranslateFn) (dom ce ae be : Lean.Expr) (n : Nat)
    (hc : KidQ mctx mref cctx cref P I rec ce) (ha : KidQ mctx mref cctx cref P I rec ae)
    (hb : KidQ mctx mref cctx cref P I rec be) (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I
      (translateStepWith (translateFallback tenv) rec (muxE dom (bitVecE n) ce ae be) hint top named) := by
  rw [vector_step rec dom ce ae be n hint top named]
  refine controlCachedQ O hA hS _ _ _ _ _ ?_
  show KeepsCQ mctx mref cctx cref P I (translateVectorMuxUncachedWith rec n
    (muxE dom (bitVecE n) ce ae be) hint top named)
  rw [vectorMuxUncached_muxE]
  exact muxWithQ O hA hS rec _ (KeepsCQ.pure _) hc ha hb _ _

theorem node_appCompare (rec : TranslateFn) (dom ae be : Lean.Expr) (n : Nat) (le : SignalCompareKind)
    (ha : KidQ mctx mref cctx cref P I rec ae) (hb : KidQ mctx mref cctx cref P I rec be)
    (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I
      (translateStepWith (translateFallback tenv) rec (appCompareE le dom n ae be) hint top named) := by
  rw [appCompare_step rec dom ae be n le hint top named,
    translateFallback_bool rec _ hint top named (isBoolControl_appCompareE dom ae be n le)]
  refine controlCachedQ O hA hS _ _ _ _ _ ?_
  rw [translateBoolUncachedWith_appCompare]
  exact appCompareQ O hA hS rec le ha hb _ _

theorem node_appBool (rec : TranslateFn) (kind : SignalBoolBinKind) (dom ae be : Lean.Expr)
    (ha : KidQ mctx mref cctx cref P I rec ae) (hb : KidQ mctx mref cctx cref P I rec be)
    (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I
      (translateStepWith (translateFallback tenv) rec (appBoolE kind dom ae be) hint top named) := by
  rw [appBool_step rec kind dom ae be hint top named,
    translateFallback_bool rec _ hint top named (isBoolControl_appBoolE dom ae be kind)]
  refine controlCachedQ O hA hS _ _ _ _ _ ?_
  rw [translateBoolUncachedWith_appBool]
  exact appBoolBinaryQ O hA hS rec kind ha hb _ _

theorem node_appBool2 (rec : TranslateFn) (f : AppBool2) (dom ae be : Lean.Expr)
    (ha : KidQ mctx mref cctx cref P I rec ae) (hb : KidQ mctx mref cctx cref P I rec be)
    (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I
      (translateStepWith (translateFallback tenv) rec (appBool2E f dom ae be) hint top named) := by
  rw [appBool2_step rec f dom ae be hint top named,
    translateFallback_bool rec _ hint top named (isBoolControl_appBool2E dom ae be f)]
  refine controlCachedQ O hA hS _ _ _ _ _ ?_
  rw [translateBoolUncachedWith_appBool2]
  exact appBool2Q O hA hS rec f ha hb _ _


/-- One step of the knot at a node whose core declines (`pure none`) and whose fallback keeps. -/
theorem stepQnone (fallback : TranslateFn → TranslateFn) (rec : TranslateFn) (e : Lean.Expr)
    (hint : String) (top named : Bool)
    (hcore : translateCore rec e hint top named = pure none)
    (hfb : KeepsCQ mctx mref cctx cref P I (fallback rec e hint top named)) :
    KeepsCQ mctx mref cctx cref P I (translateStepWith fallback rec e hint top named) := by
  unfold translateStepWith
  dsimp only
  rw [hcore]
  refine KeepsCQ.ite (fun _ => ?_) (fun _ => ?_)
  · refine KeepsCQ.bind (KeepsCQ.ofCP (cacheLookupValidatedA O hA hS _)) (fun x => ?_)
    cases x with
    | some w => exact KeepsCQ.pure _
    | none =>
      refine KeepsCQ.bind (KeepsCQ.pure _) (fun y => ?_)
      cases y with
      | none => exact hfb
      | some w =>
        exact KeepsCQ.ite (fun _ => KeepsCQ.pure _)
          (fun _ => KeepsCQ.bind (KeepsCQ.ofCP (recordTranslationA O hA hS _ _ _))
            (fun _ => KeepsCQ.pure _))
  · refine KeepsCQ.bind (KeepsCQ.pure _) (fun y => ?_)
    cases y with
    | none => exact hfb
    | some w =>
      exact KeepsCQ.ite (fun _ => KeepsCQ.pure _)
        (fun _ => KeepsCQ.bind (KeepsCQ.ofCP (recordTranslationA O hA hS _ _ _))
          (fun _ => KeepsCQ.pure _))

omit O hA hS in
theorem translateCore_pure (rec : TranslateFn) (e : Lean.Expr) (us : List Level) (hint : String)
    (top named : Bool) (fn : e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us) :
    translateCore rec e hint top named = translateSignalPureLiteral? e.getAppArgs hint named := by
  unfold translateCore
  split
  · simp [Lean.Expr.getAppFn] at fn
  · rw [fn]
    simp only [beq_self_eq_true, if_true]

omit O hA hS in
theorem translateCore_binary (rec : TranslateFn) (e : Lean.Expr) (m : Name) (us : List Level)
    (op : Sparkle.IR.AST.Operator) (n : Nat) (hint : String) (top named : Bool)
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n) :
    translateCore rec e hint top named =
      (do let w ← translateCanonicalSignalBinary rec e op e.getAppArgs true true hint named
          pure (some w)) := by
  have ne : m ≠ ``Sparkle.Core.Signal.Signal.pure := by
    intro eq; subst m; simp [signalBinOpOf] at hop
  unfold translateCore
  split
  · simp [Lean.Expr.getAppFn] at fn
  · rw [fn]
    simp only [beq_eq_false_iff_ne.mpr ne, Bool.false_eq_true, if_false, hop, kinds, width]

theorem someCQ_pureLit (args : Array Lean.Expr) (hint : String) (named : Bool) {c : Lean.Expr}
    {n v : Nat} (hback : args.back? = some c) (hlit : bitVecLitValue? c = some (n, v)) :
    SomeCQ mctx mref cctx cref P I (translateSignalPureLiteral? args hint named) := by
  unfold translateSignalPureLiteral?
  rw [hback]
  simp only [Option.bind_some, hlit]
  refine SomeCQ.bindK (KeepsCQ.ofCP (makeWireP O hA hS _ _ _)) (fun w => ?_)
  refine SomeCQ.bindK (KeepsCQ.ofCP (emitAssignP _ _)) (fun _ => ?_)
  exact SomeCQ.pure _

omit O hA hS in
theorem someCQ_lookupVar (id : FVarId) (hP : ∀ ctx, P ctx → ∃ w, ctx.varMap.lookup id = some w) :
    SomeCQ mctx mref cctx cref P I (CompilerM.lookupVar id) := by
  intro ctx st hc hp
  obtain ⟨w, hw⟩ := hP ctx hp
  unfold CompilerM.lookupVar
  show Triple mctx mref cctx cref I
    (Pure.pure (Sparkle.IR.Builder.CircuitM.lookupSourceBinding (ctx.varMap.lookup id) id.name st) : MetaM _) _ _
  rw [hw]
  exact Triple.pure (fun _ hw' => ⟨hw', w, rfl⟩)

theorem canonicalBinaryQ (rec : TranslateFn) (e : Lean.Expr) (op : Sparkle.IR.AST.Operator) (args : Array Lean.Expr)
    (n : Nat) (hw : canonicalSignalBitVecWidth args = some n) (hint : String) (named : Bool)
    (ha : KidQ mctx mref cctx cref P I rec args[args.size - 2]!)
    (hb : KidQ mctx mref cctx cref P I rec args[args.size - 1]!) :
    KeepsCQ mctx mref cctx cref P I
      (translateCanonicalSignalBinary rec e op args true true hint named) := by
  unfold translateCanonicalSignalBinary
  first | rw [hw] | simp only [hw]
  refine KeepsCQ.bind (KeepsCQ.pure _) (fun _ => ?_)
  refine KeepsCQ.bind (KeepsCQ.ofCP (makeWireP O hA hS _ _ _)) (fun _ => ?_)
  first
    | refine KeepsCQ.bind (KeepsCQ.ite (fun _ => ha _ _ _) (fun h => (h rfl).elim)) (fun _ => ?_)
    | refine KeepsCQ.bind (ha _ _ _) (fun _ => ?_)
  first
    | refine KeepsCQ.bind (KeepsCQ.ite (fun _ => hb _ _ _) (fun h => (h rfl).elim)) (fun _ => ?_)
    | refine KeepsCQ.bind (hb _ _ _) (fun _ => ?_)
  refine KeepsCQ.bind (KeepsCQ.ofCP (emitAssignP _ _)) (fun _ => ?_)
  exact KeepsCQ.pure _


theorem node_fvar (fallback : TranslateFn → TranslateFn) (rec : TranslateFn) (id : FVarId)
    (hP : ∀ ctx, P ctx → ∃ w, ctx.varMap.lookup id = some w) (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I (translateStepWith fallback rec (.fvar id) hint top named) :=
  stepQ O hA hS fallback rec _ hint top named (someCQ_lookupVar id hP)

theorem node_pureLit (fallback : TranslateFn → TranslateFn) (rec : TranslateFn) (e : Lean.Expr)
    (us : List Level) (fn : e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us)
    {c : Lean.Expr} {n v : Nat} (hback : e.getAppArgs.back? = some c)
    (hlit : bitVecLitValue? c = some (n, v)) (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I (translateStepWith fallback rec e hint top named) := by
  refine stepQ O hA hS fallback rec e hint top named ?_
  rw [translateCore_pure rec e us hint top named fn]
  exact someCQ_pureLit O hA hS e.getAppArgs hint named hback hlit

theorem node_binary (fallback : TranslateFn → TranslateFn) (rec : TranslateFn) (e : Lean.Expr)
    (m : Name) (us : List Level) (op : Sparkle.IR.AST.Operator) (n : Nat)
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (ha : KidQ mctx mref cctx cref P I rec e.getAppArgs[e.getAppArgs.size - 2]!)
    (hb : KidQ mctx mref cctx cref P I rec e.getAppArgs[e.getAppArgs.size - 1]!)
    (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I (translateStepWith fallback rec e hint top named) := by
  refine stepQ O hA hS fallback rec e hint top named ?_
  rw [translateCore_binary rec e m us op n hint top named fn hop kinds width]
  exact SomeCQ.bindK (canonicalBinaryQ O hA hS rec e op e.getAppArgs n width hint named ha hb)
    (fun w => SomeCQ.pure w)

theorem node_boolLit (rec : TranslateFn) (dom : Lean.Expr) (b : Bool) (hint : String) (top named : Bool) :
    KeepsCQ mctx mref cctx cref P I
      (translateStepWith (translateFallback tenv) rec (literalE dom b) hint top named) := by
  refine stepQnone O hA hS _ rec _ hint top named (literal_core rec dom b hint top named) ?_
  rw [translateFallback_bool rec _ hint top named (by cases b <;> rfl)]
  refine controlCachedQ O hA hS _ _ _ _ _ ?_
  rw [literal_uncached]
  exact KeepsCQ.ofCP (emitBoolLiteralA O hA hS _ _ _)

end Walk

end Tools.ShippingLeafTermKeeps
