import Tools.ShippingLeafBodyCi
import Tools.ShippingLeafCtxQ
import Tools.ShippingUnifiedRecursion
import Tools.ShippingVectorMuxRecursion
import Tools.ShippingUnifiedMeaning
import Tools.ShippingMachineAuto
import Tools.ShippingUnifiedExecutionSoundness
-- BUILT at the final committed SHA: see REPORT-SR6.md for run names / exits.
-- No `sorry`, no `axiom`, no `native_decide`, no new RefLawsAOps/RefLawsATele field, no existing statement changed.

/-! # The translator keeps the cache value on a quoted leaf (unit SR6, L8al, part B)

`LeafTranslatorKeeps` (`Tools.ShippingLeafBodyCi`) is PROVED for a shape whose body is the quotation of a
well-formed `Term` (the form `seqChild_of_realA` already assumes: `hbody`, `d.ok`). The proof is a fuel
induction over the 21 constructors of `Tools.ShippingUnifiedSource.Term` (`term_fuel_keeps`) in the contexts
that bind the input fvars (`KeepsCQ`/`BoundIn`, `Tools/ShippingLeafCtxQ.lean`). Each node is rewritten with the
step equations already proved for the semantic contracts (`Tools.ShippingUnifiedRecursion.*_step`,
`ShippingMixedRecursion.*_step`, `ShippingBoolMuxSoundness.boolMux_step`, `ShippingVectorMuxRecursion.vector_step`)
and walked with the existing emitter lemmas of `ShippingChildFallbackA`; the only nodes with a translator-level
effect are the core nodes (fvar lookup, `Signal.pure` literal, canonical binary) and the control-cached
fallback arms. The instance arm (`fallbackKind = .other`), the only caller of `synthesizeChild`, is never
reached: that is what "a LEAF body has no child calls" comes to at the translator level.
SCOPE: this is about the translator on the quoted fragment; the laws of `O : RefLawsAOps` (unproved boundary)
are used exactly as in `Tools.ShippingChildFallbackA`. -/


namespace Tools.ShippingLeafTermKeeps
open Tools.ShippingLeafCtxQ
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


/-- **The fuel induction: the translator keeps `I` on every quoted well-formed term**, in the contexts `P`
that bind the input fvars. The only nodes the quoted fragment reaches are the ones above; none is the
instance arm (`fallbackKind = .other`), so `synthesizeChild` is not reached. -/
theorem term_fuel_keeps (fuel : Nat) {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat}
    {bi vi : Nat → FVarId}
    (hbP : ∀ j, j < kb → ∀ ctx, P ctx → ∃ w, ctx.varMap.lookup (bi j) = some w)
    (hvP : ∀ j, j < kv → ∀ ctx, P ctx → ∃ w, ctx.varMap.lookup (vi j) = some w) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw →
      KidQ mctx mref cctx cref P I (translateFuelFix (translateStep tenv) fuel)
        (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) e) := by
  induction fuel with
  | zero =>
    intro s e he hint top named
    exact KeepsCQ.ofCP (KeepsCP.throw (Exception.error .missing "translation fuel exhausted")
      (by okmsg))
  | succ fuel ih =>
    intro s e he hint top named
    change KeepsCQ mctx mref cctx cref P I (translateStepWith (translateFallback tenv)
      (translateFuelFix (translateStep tenv) fuel) _ hint top named)
    cases e with
    | boolInput j => exact node_fvar O hA hS _ _ _ (hbP j he) hint top named
    | bitsInput w j =>
      obtain ⟨hj, hw, hpos⟩ := he
      cases hw
      exact node_fvar O hA hS _ _ _ (hvP j hj) hint top named
    | boolLit b => exact node_boolLit O hA hS _ dom b hint top named
    | bitsLit w v =>
      obtain ⟨hval, hpos⟩ := he
      exact node_pureLit O hA hS _ _ _ _ rfl (n := w) (v := v) rfl (litValue_natE w v hval)
        hint top named
    | bitsNum w v =>
      obtain ⟨hval, hpos⟩ := he
      exact node_pureLit O hA hS _ _ _ _ rfl (n := w) (v := v) rfl (litValue_numLitE w v hval)
        hint top named
    | binary op a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      have ck := op_checks op dom (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
        (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b) w
      exact node_binary O hA hS _ _ _ _ _ _ w ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1
        (by rw [ck.2.2.2.2.1]; exact ih a ha) (by rw [ck.2.2.2.2.2.1]; exact ih b hb') hint top named
    | compare op a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      exact node_compare O hA hS _ dom _ _ w op (ih a ha) (ih b hb') hint top named
    | boolBinary op a b =>
      obtain ⟨ha, hb'⟩ := he
      exact node_boolBin O hA hS _ op dom _ _ (ih a ha) (ih b hb') hint top named
    | boolNot a =>
      exact node_boolNot O hA hS _ dom _ (ih a he) (ih (.boolLit false) trivial) hint top named
    | boolEq a b =>
      obtain ⟨ha, hb'⟩ := he
      exact node_boolEq O hA hS _ dom _ _ (ih a ha) (ih b hb') hint top named
    | mux c a b =>
      obtain ⟨hc, ha, hb'⟩ := he
      cases s with
      | bool => exact node_boolMux O hA hS _ dom _ _ _ (ih c hc) (ih a ha) (ih b hb') hint top named
      | bits w => exact node_vectorMux O hA hS _ dom _ _ _ w (ih c hc) (ih a ha) (ih b hb') hint top named
    | setw w' a =>
      rename_i w
      obtain ⟨ha, hpos⟩ := he
      exact node_setw O hA hS _ dom _ w w' (a.wf_pos ha) hpos (ih a ha) hint top named
    | appCompare op a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      exact node_appCompare O hA hS _ dom _ _ w op (ih a ha) (ih b hb') hint top named
    | appBool op a b =>
      obtain ⟨ha, hb'⟩ := he
      exact node_appBool O hA hS _ op dom _ _ (ih a ha) (ih b hb') hint top named
    | appBool2 f a b =>
      obtain ⟨ha, hb'⟩ := he
      exact node_appBool2 O hA hS _ f dom _ _ (ih a ha) (ih b hb') hint top named
    | slice nm start len a =>
      rename_i w
      obtain ⟨ha, hlen, hr⟩ := he
      exact node_slice O hA hS _ dom _ nm w start len hlen hr (ih a ha) hint top named
    | concat a b =>
      rename_i m n
      obtain ⟨ha, hb'⟩ := he
      exact node_concat O hA hS _ dom _ _ m n (a.wf_pos ha) (b.wf_pos hb') (ih a ha) (ih b hb')
        hint top named
    | concatLitHi k v b =>
      rename_i n
      obtain ⟨hb', hk, hlt⟩ := he
      exact node_concatLitHi O hA hS _ dom _ k v n hk hlt (b.wf_pos hb') (ih b hb') hint top named
    | concatLitLo a k v =>
      rename_i m
      obtain ⟨ha, hk, hlt⟩ := he
      exact node_concatLitLo O hA hS _ dom _ m k v hk hlt (a.wf_pos ha) (ih a ha) hint top named
    | zextMap nm k a =>
      rename_i n
      obtain ⟨ha, hk⟩ := he
      exact node_zextMap O hA hS _ dom _ nm k n hk (a.wf_pos ha) (ih a ha) hint top named
    | sliceF nm start len a =>
      rename_i w
      obtain ⟨ha, hlen, hr⟩ := he
      exact node_sliceF O hA hS _ dom _ nm w start len hlen hr (ih a ha) hint top named

end Walk

open Tools.ShippingLeafBodyCi Tools.ShippingLeafKeepCache Tools.ShippingLeafMissCoh Tools.ShippingSharedLeafCoh
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildCoreC Tools.ShippingSeqChildIface Tools.ShippingSeqChildIfaceA Tools.ShippingGateChildComb
open Tools.ShippingMachineAuto Tools.ShippingMachineEntry Tools.ShippingMachineCloses
open Sparkle.IR.AST

section Final
variable (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
include O hA hS

/-- **The translator keeps `I` on the leaf expression of a shape whose body is the quotation of a well-formed
term** (in the contexts the binder walk hands to `emitLeaves`). Facts used: the quotation (`hbody`), the
well-formedness `he`, the binder kinds at the input positions (`hb`, `hv`). Discharges `LeafTranslatorKeeps`. -/
theorem leafTranslatorKeeps_of_quote (shape : MachineShape) {dom : Lean.Expr} {kb kv : Nat}
    {vw bpos vpos : Nat → Nat} {srt : SType} (e : Term srt) (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, shape.binders[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, shape.binders[vpos j]? = some (name, .bits (vw j)))
    (hbody : shape.body = quote dom (fun j => inputExpr shape.binders.length (bpos j))
      (fun j => inputExpr shape.binders.length (vpos j)) e) :
    LeafTranslatorKeeps (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) I shape := by
  intro tenv ids len
  have hq : instFVars (ids.map Lean.Expr.fvar).toArray 0 shape.body =
      quote (instFVars (ids.map Lean.Expr.fvar).toArray 0 dom)
        (fun j => .fvar (ids[bpos j]!)) (fun j => .fvar (ids[vpos j]!)) e := by
    rw [hbody]
    apply Tools.ShippingUnifiedExecutionSoundness.instantiated_quote _ _ e he
    · intro j hj
      obtain ⟨name, pos⟩ := hb j hj
      exact instantiated_input len (List.getElem_of_getElem? pos).choose
    · intro j hj
      obtain ⟨name, pos⟩ := hv j hj
      exact instantiated_input len (List.getElem_of_getElem? pos).choose
  rw [hq]
  exact term_fuel_keeps O hA hS (tenv := tenv) translateFuelLimit
    (fun j hj ctx hp => by
      obtain ⟨name, pos⟩ := hb j hj
      exact hp _ (zip_member len pos) (by simp))
    (fun j hj ctx hp => by
      obtain ⟨name, pos⟩ := hv j hj
      exact hp _ (zip_member len pos) (by simp)) e he "out" false true

omit O hA hS in
/-- The side conditions `leafTranslatorKeeps_of_quote` reads, from `MachineData.ok` (copy of the
extraction in `seqChild_iface`). -/
theorem machineData_ok_facts (d : MachineData) (ok : d.ok = true) :
    d.packed.WF d.kb d.kv d.vw ∧
    (∀ j, j < d.kb → ∃ name, d.shape.binders[d.bpos j]? = some (name, .bool)) ∧
    (∀ j, j < d.kv → ∃ name, d.shape.binders[d.vpos j]? = some (name, .bits (d.vw j))) := by
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, _, _, _, _, _, _, _, _⟩ := ok
  refine ⟨hwf, ?_, ?_⟩
  · intro j hj
    have := hb j hj
    cases h : d.shape.binders[d.bpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  · intro j hj
    have := hv j hj
    cases h : d.shape.binders[d.vpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩

/-- **`LeafTranslatorKeeps` for a machine datum**: from `d.ok` and the quotation `hbody` (both already
premises of `seqChild_of_realA`). -/
theorem leafTranslatorKeeps_of_machineData (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) :
    LeafTranslatorKeeps (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) I d.shape := by
  obtain ⟨hwf, hb, hv⟩ := machineData_ok_facts d ok
  exact leafTranslatorKeeps_of_quote O hA hS d.shape d.packed hwf hb hv hbody

end Final

/-! ## `hbodyK` replaced by facts about THIS leaf (no translator premise left) -/

/-- **`synthesizeChild_leafMiss_nested` with `hbodyK` replaced by facts about THIS leaf's constant.**
The body premise of `Tools.ShippingLeafKeepCache` (arbitrary `tenv`/`ci`/`isInst`) is gone, and so is the
translator premise of `synthesizeChild_leafMiss_nestedL`. Used about the real leaf: `entry`
(`MachineDefines`: the `ci`/`env` reads of this run give the machine constant `d.shape`), `closes`
(`MachineCloses`), `hno` (`insts = []`: no `closeInsts`, no `synthesizeChild` from the machine branch),
`ok`/`hbody` (the body is the quotation of the well-formed term `d.packed`: the translator reaches only the
nodes of `Tools.ShippingUnifiedSource.Term`, none of them the instance arm). -/
theorem synthesizeChild_leafMiss_nested_final (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat} (hD : D ≠ 0) {n : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref n d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref n d.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O D w)
    (hcl : CacheClosed (cv w)) (hk : KeyTop (cv w)) (hmiss : (cv w).get? n = none)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w') :
    CacheClosed (cv w') ∧ KeyTop (cv w') ∧ CohWith (cv w) y ∧ CacheCoh (cv w') :=
  synthesizeChild_leafMiss_nestedL O hA hD d ok hbody hno outTy entry closes
    (fun c0 => leafTranslatorKeeps_of_machineData O hA (stableK O (D + 1) c0) d ok hbody)
    hw hcl hk hmiss h

/-- **(b) at `D = 0`.** -/
theorem synthesizeChild_leafMiss_zero_final (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {n : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref n d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref n d.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w) (hmiss : (cv w).get? n = none)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w') :
    cv w' = ({} : Std.HashMap Name Res).insert n y ∧ CacheClosed (cv w') ∧ KeyTop (cv w') ∧
      CohWith ({} : Std.HashMap Name Res) y ∧ CacheCoh (cv w') :=
  synthesizeChild_leafMiss_zeroL O hA d ok hbody hno outTy entry closes
    (leafTranslatorKeeps_of_machineData O hA (stableK O 1 {}) d ok hbody) hw hmiss h

end Tools.ShippingLeafTermKeeps

#print axioms Tools.ShippingLeafTermKeeps.term_fuel_keeps
#print axioms Tools.ShippingLeafTermKeeps.leafTranslatorKeeps_of_quote
#print axioms Tools.ShippingLeafTermKeeps.leafTranslatorKeeps_of_machineData
#print axioms Tools.ShippingLeafTermKeeps.synthesizeChild_leafMiss_nested_final
#print axioms Tools.ShippingLeafTermKeeps.synthesizeChild_leafMiss_zero_final
