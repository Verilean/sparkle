import Tools.ShippingUnifiedRecursion
import Tools.ShippingCacheCoherentVia

variable {tenv : Lean.Environment}

/-! # The certified walk, with worlds: a returning translation of a quoted term leaves the child cache

`Tools.ShippingCacheCoherentCert.HarnessStill` / `EntryStill` say that a run
leaves the VALUE of the child cache. No frame law gives that of a program
(`docs/parallel/A-cache-coherence-4.md` §3): it has to be read off the walk.
This file does the walk's CORE — the translator on a quoted term — for a
fragment of the term language, by the same induction as the built soundness
(`Tools.ShippingUnifiedRecursion.fuel_contract_leaves`), with the built
PROGRAM EQUALITIES (`compare_step`, `vector_step`, `setw_step`, …,
`translateFallback_bool`, `…Uncached_…E`) telling which arm runs.

* `WHo L mb ctx c Q`: partial correctness in a FIXED compiler context — a
  returning run of `c ctx st` from a world satisfying `WSI L mb` (the cache
  invariant, and the cache's value is `mb`) ends in such a world, and its
  result satisfies `Q`. `WSt` is `WHo` with no result condition.
* the operations of the walk, each `WSt` (the inventory: every one is a
  pure state step, or ONE framed `MetaM` operation):
  `makeWire` (builder state; `sparkleWireWidthCache.modify` — `SideRef`),
  `emitAssign` (builder state), `cacheLookupValidated` (reader; the
  translation cache's read — `Framed.exprCacheGetIO`; builder state),
  `recordTranslation` (builder state; the translation cache's update —
  `Framed.exprCacheModify`), `lookupVar` (reader + builder state, pure);
* the wrapper `translateControlCachedWith` and the arms
  `translateSignalCompare`, `translateBoolBinary`, `translateMuxWith`,
  `translateSetWidthUncachedWith`'s body, `translateConcatWith`,
  `translateSignalPureLiteral?`, `translateCanonicalSignalBinary`: `rec` on
  the operands, then the operations above — no child synthesis;
* per constructor, `…_still`: the step on the quoted node is `WSt` when the
  recursive translator is on its operands;
* `wfrag` (a `Bool` on terms, decided by reading / by `decide`): inputs,
  `bitsLit`, `binary`, `compare`, `boolBinary`, `boolEq`, `mux` (both sorts),
  `setw`, `concat`. NOT in the fragment (the theorem says nothing of them):
  `boolLit`, `bitsNum`, `boolNot`, `slice`, `sliceF`, `zextMap`,
  `concatLitHi/Lo`, `appCompare`, `appBool`, `appBool2`;
* `fuel_still` / `walk_still`: for a well-formed term of the fragment whose
  input binders are bound in the context (`WBound`), a returning run of
  `translateExprToWire` on its quotation leaves the cache.

NOT here: the harness shell around the translator (`bindMixedCertifiedInputs`
— which is what makes the binders `WBound` —, `emitLeaves`, `finishSynth`),
hence `HarnessStill` and `EntryStill` themselves.

WRITTEN, NOT BUILT (par/a-36). -/
namespace Tools.ShippingWalkStill
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingTypedExprSoundness
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingCompareLoweringSoundness Tools.ShippingMuxRecursionSoundness
open Tools.ShippingMuxLoweringSoundness Tools.ShippingBoolLiteralSoundness
open Tools.ShippingBoolMuxSoundness Tools.ShippingEntrySoundness
open Tools.ShippingMuxTypeSoundness
open Tools.ShippingBoolSourceSoundness
open Tools.ShippingMixedRecursion (compare_step boolBin_step boolEq_step
  translateBoolUncachedWith_boolBin)
open Tools.ShippingVectorMuxRecursion (vector_step vectorMuxUncached_muxE)
open Tools.ShippingUnifiedRecursion (setw_step setwUncached_setwE concat_step
  concatUncached_concatE)
open Tools.ShippingChildInv

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-! ## The logic -/

/-- The cache invariant, and the cache's value is `mb`. -/
def WSI (L : RefLaws mref cref) (mb : Std.HashMap Lean.Name Res) (w : Void IO.RealWorld) : Prop :=
  InvV L w ∧ L.val w = mb

section Logic
variable (mctx cctx)

/-- Partial correctness in a fixed compiler context: a RETURNING run of
`c ctx st` from a `WSI` world ends in one, with a result satisfying `Q`. -/
def WHo (L : RefLaws mref cref) (mb : Std.HashMap Lean.Name Res) (ctx : CompilerState)
    {α : Type} (c : CompilerM α) (Q : α → Prop) : Prop :=
  ∀ (st : CircuitState) (w : Void IO.RealWorld) (p : α × CircuitState) (w' : Void IO.RealWorld),
    WSI L mb w → RunsTo (c ctx st) mctx mref cctx cref w p w' → WSI L mb w' ∧ Q p.1

/-- `WHo` with no condition on the result. -/
abbrev WSt (L : RefLaws mref cref) (mb : Std.HashMap Lean.Name Res) (ctx : CompilerState)
    {α : Type} (c : CompilerM α) : Prop :=
  WHo mctx cctx L mb ctx c (fun _ => True)

/-- The translator `rec` is still on the expression `e`, under every hint. -/
def WCh (L : RefLaws mref cref) (mb : Std.HashMap Lean.Name Res) (ctx : CompilerState)
    (rec : TranslateFn) (e : Lean.Expr) : Prop :=
  ∀ (hint : String) (top named : Bool), WSt mctx cctx L mb ctx (rec e hint top named)

end Logic

variable (L : RefLaws mref cref) {mb : Std.HashMap Lean.Name Res} {ctx : CompilerState}

theorem WHo.pure {α : Type} (a : α) {Q : α → Prop} (hq : Q a) :
    WHo mctx cctx L mb ctx (Pure.pure a : CompilerM α) Q := by
  intro st w p w' hw hr
  obtain ⟨hp, hww⟩ := RunsTo.pure_world (a := (a, st)) hr
  rw [hp, hww]
  exact ⟨hw, hq⟩

theorem WHo.bind {α β : Type} {c : CompilerM α} {f : α → CompilerM β} {Q1 : α → Prop}
    {Q2 : β → Prop} (h1 : WHo mctx cctx L mb ctx c Q1)
    (h2 : ∀ a, Q1 a → WHo mctx cctx L mb ctx (f a) Q2) :
    WHo mctx cctx L mb ctx (c >>= f) Q2 := by
  intro st w p w' hw hr
  obtain ⟨⟨a, s⟩, w1, r1, r2⟩ := RunsTo.bind hr
  obtain ⟨hw1, hq1⟩ := h1 st w (a, s) w1 hw r1
  exact h2 a hq1 s w1 p w' hw1 r2

/-- A lifted `MetaM` action. -/
theorem WHo.lift {α : Type} {m : Lean.Meta.MetaM α} {Q : α → Prop}
    (hm : ∀ (w : Void IO.RealWorld) (a : α) (w' : Void IO.RealWorld), WSI L mb w →
      RunsTo m mctx mref cctx cref w a w' → WSI L mb w' ∧ Q a) :
    WHo mctx cctx L mb ctx (CompilerM.liftMetaM m) Q := by
  intro st w p w' hw hr
  obtain ⟨a, w1, r1, r2⟩ := RunsTo.bind hr
  obtain ⟨hp, hww⟩ := RunsTo.pure_world r2
  rw [hp, hww]
  exact hm w a w1 hw r1

/-- An action that is a pure step of the reader and the builder state. -/
theorem WHo.ofPure {α : Type} {c : CompilerM α} {Q : α → Prop}
    (h : ∀ st : CircuitState, ∃ (a : α) (s : CircuitState),
      c ctx st = (Pure.pure (a, s) : Lean.Meta.MetaM (α × CircuitState)) ∧ Q a) :
    WHo mctx cctx L mb ctx c Q := by
  intro st w p w' hw hr
  obtain ⟨a, s, e, hq⟩ := h st
  rw [e] at hr
  obtain ⟨hp, hww⟩ := RunsTo.pure_world hr
  rw [hp, hww]
  exact ⟨hw, hq⟩

theorem WSt.get : WSt mctx cctx L mb ctx (get : CompilerM CircuitState) :=
  WHo.ofPure L fun st => ⟨st, st, rfl, trivial⟩

theorem WSt.set (s : CircuitState) : WSt mctx cctx L mb ctx (set s : CompilerM PUnit) :=
  WHo.ofPure L fun _ => ⟨PUnit.unit, s, rfl, trivial⟩

theorem WSt.modify (f : CircuitState → CircuitState) :
    WSt mctx cctx L mb ctx (modify f : CompilerM PUnit) :=
  WHo.ofPure L fun st => ⟨PUnit.unit, f st, rfl, trivial⟩

theorem WSt.getCompilerState : WSt mctx cctx L mb ctx CompilerM.getCompilerState :=
  WHo.ofPure L fun st => ⟨ctx, st, rfl, trivial⟩

/-- A throw has no returning run. -/
theorem WSt.throw {α : Type} (e : Exception) :
    WSt mctx cctx L mb ctx (throw e : CompilerM α) := by
  intro st w p w' _ hr
  have h : (EST.Out.error e w : EST.Out Exception IO.RealWorld (α × CircuitState)) =
      EST.Out.ok p w' := hr
  cases h

/-- A framed `MetaM` operation on a returning run: the invariant, and the
cache's value. -/
theorem framedM {α : Type} {m : Lean.Meta.MetaM α} (hp : Framed m)
    (w : Void IO.RealWorld) (a : α) (w' : Void IO.RealWorld) (hw : WSI L mb w)
    (h : RunsTo m mctx mref cctx cref w a w') : WSI L mb w' ∧ True := by
  refine ⟨⟨invV_framed L hp h hw.1, ?_⟩, trivial⟩
  rw [(L.same hp h).1]
  exact hw.2

/-! ## The operations of the walk -/

theorem wireWidth_S (f : Std.HashMap String Nat → Std.HashMap String Nat) :
    WSt mctx cctx L mb ctx (CompilerM.liftMetaM (ST.Ref.modify sparkleWireWidthCache f)) :=
  WHo.lift L (framedM L (Framed.sideModify _ .wireWidth))

/-- `makeWire`: the builder state, and the wire-width cache (a side ref). -/
theorem makeWire_S (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) :
    WSt mctx cctx L mb ctx (CompilerM.makeWire hint ty named) := by
  unfold CompilerM.makeWire
  refine WHo.bind L (WSt.get L) ?_
  intro cs _
  split
  refine WHo.bind L (WSt.set L _) ?_
  intro _ _
  dsimp only
  split
  · refine WHo.bind L (wireWidth_S L _) ?_
    intro _ _
    exact WHo.pure L _ trivial
  · exact WHo.pure L _ trivial

/-- `emitAssign`: the builder state only. -/
theorem emitAssign_S (lhs : String) (rhs : Sparkle.IR.AST.Expr) :
    WSt mctx cctx L mb ctx (CompilerM.emitAssign lhs rhs) := by
  unfold CompilerM.emitAssign
  refine WHo.bind L (WSt.get L) ?_
  intro cs _
  split
  exact WSt.set L _

/-- The validated lookup: the reader, the translation cache's read (a ref of
another type than the three tracked ones), the builder's record. -/
theorem cacheLookup_S (e : Lean.Expr) :
    WSt mctx cctx L mb ctx (cacheLookupValidated e) := by
  unfold cacheLookupValidated
  refine WHo.bind L (WSt.getCompilerState L) ?_
  intro cs _
  split
  · exact WHo.pure L _ trivial
  · refine WHo.bind L (WHo.lift L (Q := fun _ => True) ?_) ?_
    · intro w a w' hw h
      obtain ⟨m, w1, r1, r2⟩ := RunsTo.bind h
      obtain ⟨-, hww⟩ := RunsTo.pure_world r2
      rw [hww]
      exact framedM L (Framed.exprCacheGetIO _) w m w1 hw r1
    · intro hit _
      split
      · exact WHo.pure L _ trivial
      · refine WHo.bind L (WSt.get L) ?_
        intro s _
        split <;> exact WHo.pure L _ trivial

/-- The record of a result: the builder state, and the translation cache's
update when the call is cacheable. -/
theorem record_S (e : Lean.Expr) (w : String) (cacheable : Bool) :
    WSt mctx cctx L mb ctx (recordTranslation e w cacheable) := by
  unfold recordTranslation
  refine WHo.bind L (WSt.modify L _) ?_
  intro _ _
  split
  · refine WHo.bind L (WSt.getCompilerState L) ?_
    intro cs _
    split
    · exact WHo.lift L (framedM L (Framed.exprCacheModify _ _))
    · exact WHo.pure L _ trivial
  · exact WHo.pure L _ trivial

/-- **The cache wrapper**: still when the uncached lowering is. -/
theorem controlCached_S {lower : TranslateFn} {e : Lean.Expr} {hint : String} {top named : Bool}
    (hlower : WSt mctx cctx L mb ctx (lower e hint top named)) :
    WSt mctx cctx L mb ctx (translateControlCachedWith lower e hint top named) := by
  have rest : WSt mctx cctx L mb ctx
      (lower e hint top named >>= fun w =>
        recordTranslation e w (!named && !e.isFVar && !top) >>= fun _ => Pure.pure w) :=
    WHo.bind L hlower fun w _ => WHo.bind L (record_S L _ _ _) fun _ _ => WHo.pure L _ trivial
  unfold translateControlCachedWith
  dsimp only
  split
  · refine WHo.bind L (cacheLookup_S L e) ?_
    intro r _
    split
    · exact WHo.pure L _ trivial
    · exact rest
  · exact rest

theorem emitBool_S (rhs : Sparkle.IR.AST.Expr) (hint : String) (named : Bool) :
    WSt mctx cctx L mb ctx (emitBoolResult rhs hint named) := by
  unfold emitBoolResult
  refine WHo.bind L (makeWire_S L _ _ _) ?_
  intro w _
  refine WHo.bind L (emitAssign_S L _ _) ?_
  intro _ _
  exact WHo.pure L _ trivial

theorem emitCast_S (rhs : Sparkle.IR.AST.Expr) (wt : Nat) (hint : String) (named : Bool) :
    WSt mctx cctx L mb ctx (emitCastResult rhs wt hint named) := by
  unfold emitCastResult
  refine WHo.bind L (makeWire_S L _ _ _) ?_
  intro w _
  refine WHo.bind L (emitAssign_S L _ _) ?_
  intro _ _
  exact WHo.pure L _ trivial

theorem emitMux_S (c t e hint : String) (named : Bool) (ty : Sparkle.IR.Type.HWType) :
    WSt mctx cctx L mb ctx (emitMuxResult c t e hint named ty) := by
  unfold emitMuxResult
  refine WHo.bind L (makeWire_S L _ _ _) ?_
  intro w _
  refine WHo.bind L (emitAssign_S L _ _) ?_
  intro _ _
  exact WHo.pure L _ trivial

/-! ## The arms -/

variable {rec : TranslateFn}

theorem compare_arm {le : SignalCompareKind} {a b : Lean.Expr} {hint : String} {named : Bool}
    (ha : WSt mctx cctx L mb ctx (rec a "a" false false))
    (hb : WSt mctx cctx L mb ctx (rec b "b" false false)) :
    WSt mctx cctx L mb ctx (translateSignalCompare rec le a b hint named) := by
  unfold translateSignalCompare
  refine WHo.bind L ha ?_
  intro aw _
  refine WHo.bind L hb ?_
  intro bw _
  unfold emitCompareResult
  exact emitBool_S L _ _ _

theorem boolBin_arm {kind : SignalBoolBinKind} {a b : Lean.Expr} {hint : String} {named : Bool}
    (ha : WSt mctx cctx L mb ctx (rec a "a" false false))
    (hb : WSt mctx cctx L mb ctx (rec b "b" false false)) :
    WSt mctx cctx L mb ctx (translateBoolBinary rec kind a b hint named) := by
  unfold translateBoolBinary
  refine WHo.bind L ha ?_
  intro aw _
  refine WHo.bind L hb ?_
  intro bw _
  exact emitBool_S L _ _ _

theorem mux_arm {ty : Sparkle.IR.Type.HWType} {c a b : Lean.Expr} {hint : String} {named : Bool}
    (hc : WSt mctx cctx L mb ctx (rec c "mux_cond" false false))
    (ha : WSt mctx cctx L mb ctx (rec a "mux_then" false false))
    (hb : WSt mctx cctx L mb ctx (rec b "mux_else" false false)) :
    WSt mctx cctx L mb ctx (translateMuxWith rec (Pure.pure ty) c a b hint named) := by
  unfold translateMuxWith
  refine WHo.bind L hc ?_
  intro cw _
  refine WHo.bind L ha ?_
  intro tw _
  refine WHo.bind L hb ?_
  intro ew _
  refine WHo.bind L (WHo.pure L ty (Q := fun _ => True) trivial) ?_
  intro hty _
  exact emitMux_S L _ _ _ _ _ _

theorem concat_arm {m n : Nat} {a b : Lean.Expr} {hint : String} {named : Bool}
    (ha : WSt mctx cctx L mb ctx (rec a "concat_hi" false false))
    (hb : WSt mctx cctx L mb ctx (rec b "concat_lo" false false)) :
    WSt mctx cctx L mb ctx (translateConcatWith rec m n a b hint named) := by
  unfold translateConcatWith translateConcatActs
  refine WHo.bind L (makeWire_S L _ _ _) ?_
  intro r _
  refine WHo.bind L ha ?_
  intro hi _
  refine WHo.bind L hb ?_
  intro lo _
  refine WHo.bind L (emitAssign_S L _ _) ?_
  intro _ _
  exact WHo.pure L _ trivial

/-! ## Per constructor: the nodes the fallback lowers -/

theorem compare_still {le : SignalCompareKind} {dom ae be : Lean.Expr} {n : Nat}
    (ha : WCh mctx cctx L mb ctx rec ae) (hb : WCh mctx cctx L mb ctx rec be) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec) (compareE le dom n ae be) := by
  intro hint top named
  rw [compare_step, translateFallback_bool rec _ hint top named (by cases le <;> rfl)]
  apply controlCached_S L
  rw [translateBoolUncachedWith_compare]
  exact compare_arm L (ha _ _ _) (hb _ _ _)

theorem boolBin_still {kind : SignalBoolBinKind} {dom ae be : Lean.Expr}
    (ha : WCh mctx cctx L mb ctx rec ae) (hb : WCh mctx cctx L mb ctx rec be) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec) (boolBinE kind dom ae be) := by
  intro hint top named
  rw [boolBin_step, translateFallback_bool rec _ hint top named (by cases kind <;> rfl)]
  apply controlCached_S L
  rw [translateBoolUncachedWith_boolBin]
  exact boolBin_arm L (ha _ _ _) (hb _ _ _)

theorem boolEq_still {dom ae be : Lean.Expr}
    (ha : WCh mctx cctx L mb ctx rec ae) (hb : WCh mctx cctx L mb ctx rec be) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec) (boolEqE dom ae be) := by
  intro hint top named
  rw [boolEq_step, translateFallback_bool rec _ hint top named rfl]
  apply controlCached_S L
  show WSt mctx cctx L mb ctx (translateSignalCompare rec .eq ae be hint named)
  exact compare_arm L (ha _ _ _) (hb _ _ _)

theorem boolMux_still {dom ce ae be : Lean.Expr}
    (hc : WCh mctx cctx L mb ctx rec ce) (ha : WCh mctx cctx L mb ctx rec ae)
    (hb : WCh mctx cctx L mb ctx rec be) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec) (boolMuxE dom ce ae be) := by
  intro hint top named
  rw [boolMux_step, translateFallback_bool rec _ hint top named rfl]
  apply controlCached_S L
  show WSt mctx cctx L mb ctx (translateMuxWith rec (Pure.pure .bit) ce ae be hint named)
  exact mux_arm L (hc _ _ _) (ha _ _ _) (hb _ _ _)

theorem vector_still {dom ce ae be : Lean.Expr} {n : Nat}
    (hc : WCh mctx cctx L mb ctx rec ce) (ha : WCh mctx cctx L mb ctx rec ae)
    (hb : WCh mctx cctx L mb ctx rec be) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec)
      (muxE dom (bitVecE n) ce ae be) := by
  intro hint top named
  rw [vector_step]
  apply controlCached_S L
  rw [vectorMuxUncached_muxE]
  exact mux_arm L (hc _ _ _) (ha _ _ _) (hb _ _ _)

theorem setw_still {dom ae : Lean.Expr} {ws wt : Nat} (hws : 0 < ws) (hwt : 0 < wt)
    (ha : WCh mctx cctx L mb ctx rec ae) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec) (setwE dom ws wt ae) := by
  intro hint top named
  rw [setw_step rec dom ae ws wt hws hwt]
  apply controlCached_S L
  rw [setwUncached_setwE]
  exact WHo.bind L (ha _ _ _) fun sw _ => emitCast_S L _ _ _ _

theorem concat_still {dom ae be : Lean.Expr} {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (ha : WCh mctx cctx L mb ctx rec ae) (hb : WCh mctx cctx L mb ctx rec be) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec) (concatE dom m n ae be) := by
  intro hint top named
  rw [concat_step rec dom ae be m n hint top named hm hn]
  apply controlCached_S L
  rw [concatUncached_concatE]
  exact concat_arm L (ha _ _ _) (hb _ _ _)

/-! ## Per constructor: the nodes the core lowers (no fallback) -/

/-- **One step whose core returns a wire**: the fallback is not reached. -/
theorem step_of_core {fb : TranslateFn → TranslateFn} {e : Lean.Expr} {hint : String}
    {top named : Bool}
    (hcore : WHo mctx cctx L mb ctx (translateCore rec e hint top named) (fun r => r ≠ none)) :
    WSt mctx cctx L mb ctx (translateStepWith fb rec e hint top named) := by
  unfold translateStepWith
  dsimp only
  split
  · refine WHo.bind L (cacheLookup_S L e) ?_
    intro hit _
    split
    · exact WHo.pure L _ trivial
    · refine WHo.bind L hcore ?_
      intro r hr
      cases r with
      | none => exact absurd rfl hr
      | some w =>
        dsimp only
        split
        · exact WHo.pure L _ (Q := fun _ => True) trivial
        · exact WHo.bind L (Q1 := fun _ => True) (record_S L _ _ _)
            (fun _ _ => WHo.pure L _ (Q := fun _ => True) trivial)
  · refine WHo.bind L hcore ?_
    intro r hr
    cases r with
    | none => exact absurd rfl hr
    | some w =>
      dsimp only
      split
      · exact WHo.pure L _ (Q := fun _ => True) trivial
      · exact WHo.bind L (Q1 := fun _ => True) (record_S L _ _ _)
          (fun _ _ => WHo.pure L _ (Q := fun _ => True) trivial)

/-- The context binds `id`: the variable lookup returns a wire, whatever the
builder state. A condition on the READER alone when the reader's map has the
binder (`wbound_of_lookup`). -/
def WBound (ctx : CompilerState) (id : FVarId) : Prop :=
  ∀ st : CircuitState,
    (CircuitM.lookupSourceBinding (ctx.varMap.lookup id) id.name st).1 ≠ none

theorem wbound_of_lookup {id : FVarId} {wire : String}
    (h : ctx.varMap.lookup id = some wire) : WBound ctx id := by
  intro st
  rw [h]
  exact Option.some_ne_none wire

/-- An input binder: the core is the variable lookup. -/
theorem input_still {id : FVarId} (hb : WBound ctx id) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec) (.fvar id) := by
  intro hint top named
  apply step_of_core L
  show WHo mctx cctx L mb ctx (CompilerM.lookupVar id) (fun r => r ≠ none)
  exact WHo.ofPure L fun st =>
    ⟨(CircuitM.lookupSourceBinding (ctx.varMap.lookup id) id.name st).1,
      (CircuitM.lookupSourceBinding (ctx.varMap.lookup id) id.name st).2, rfl, hb st⟩

/-- A `Signal.pure` of a recognised `BitVec` literal: a wire and an assign. -/
theorem core_literal {e c : Lean.Expr} {us : List Level} {n v : Nat} {hint : String}
    {top named : Bool}
    (fn : e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us)
    (back : e.getAppArgs.back? = some c) (lit : bitVecLitValue? c = some (n, v)) :
    WHo mctx cctx L mb ctx (translateCore rec e hint top named) (fun r => r ≠ none) := by
  unfold translateCore
  split
  · simp [Lean.Expr.getAppFn] at fn
  · rw [fn]
    simp only [beq_self_eq_true, if_true]
    unfold translateSignalPureLiteral?
    rw [back]
    simp only [Option.bind_some, lit]
    refine WHo.bind L (makeWire_S L _ _ _) ?_
    intro w _
    refine WHo.bind L (emitAssign_S L _ _) ?_
    intro _ _
    exact WHo.pure L _ (by simp)

theorem bitsLit_still {dom : Lean.Expr} {n v : Nat} {vi : Nat → Lean.Expr} (hv : v < 2 ^ n) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec)
      (quoteF dom n vi (.lit v)) := by
  intro hint top named
  have fn : (quoteF dom n vi (.lit v)).getAppFn =
      .const ``Sparkle.Core.Signal.Signal.pure [.zero] := rfl
  have back : (quoteF dom n vi (.lit v)).getAppArgs.back? =
      some (mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v)) := rfl
  exact step_of_core L (core_literal L fn back (litValue_natE n v hv))

/-- A canonical library operator on two Signals: the result wire, the two
operands, one assign. -/
theorem core_binary {e : Lean.Expr} {m : Lean.Name} {us : List Level} {op : Operator} {n : Nat}
    {hint : String} {top named : Bool}
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op)
    (hpure : (m == ``Sparkle.Core.Signal.Signal.pure) = false)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (ha : WSt mctx cctx L mb ctx (rec e.getAppArgs[e.getAppArgs.size - 2]! "op_a" false false))
    (hb : WSt mctx cctx L mb ctx (rec e.getAppArgs[e.getAppArgs.size - 1]! "op_b" false false)) :
    WHo mctx cctx L mb ctx (translateCore rec e hint top named) (fun r => r ≠ none) := by
  unfold translateCore
  split
  · simp [Lean.Expr.getAppFn] at fn
  · rw [fn]
    simp only [hpure, Bool.false_eq_true, if_false, hop, kinds, width]
    refine WHo.bind L (Q1 := fun _ => True) ?_ (fun w _ => WHo.pure L _ (by simp))
    unfold translateCanonicalSignalBinary
    simp only [width, ↓reduceIte]
    refine WHo.bind L (WHo.pure L _ (Q := fun _ => True) trivial) ?_
    intro ty _
    refine WHo.bind L (makeWire_S L _ _ _) ?_
    intro r _
    refine WHo.bind L ha ?_
    intro wa _
    refine WHo.bind L hb ?_
    intro wb _
    refine WHo.bind L (emitAssign_S L _ _) ?_
    intro _ _
    exact WHo.pure L _ trivial

/-! ## The fragment, and the induction -/

/-- The constructors this file covers. A term outside the fragment is not
claimed anything about. -/
def wfrag : {s : SType} → Term s → Bool
  | _, .boolInput _ => true
  | _, .bitsInput _ _ => true
  | _, .bitsLit _ _ => true
  | _, .binary _ a b => wfrag a && wfrag b
  | _, .compare _ a b => wfrag a && wfrag b
  | _, .boolBinary _ a b => wfrag a && wfrag b
  | _, .boolEq a b => wfrag a && wfrag b
  | _, .mux c a b => wfrag c && wfrag a && wfrag b
  | _, .setw _ a => wfrag a
  | _, .concat a b => wfrag a && wfrag b
  | _, _ => false

/-- **The walk leaves the cache, at every fuel**, for a well-formed term of
the fragment over leaf expressions that are still at every fuel (the text of
`Tools.ShippingUnifiedRecursion.fuel_contract_leaves`). -/
theorem fuel_still (fuel : Nat) {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat}
    {bE vE : Nat → Lean.Expr}
    (hbS : ∀ j, j < kb → ∀ fuel,
      WCh mctx cctx L mb ctx (translateFuelFix (translateStep tenv) fuel) (bE j))
    (hvS : ∀ j, j < kv → ∀ fuel,
      WCh mctx cctx L mb ctx (translateFuelFix (translateStep tenv) fuel) (vE j)) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw → wfrag e = true →
      WCh mctx cctx L mb ctx (translateFuelFix (translateStep tenv) fuel) (quote dom bE vE e) := by
  induction fuel with
  | zero =>
    intro s e _ _ hint top named
    unfold translateFuelFix
    exact WSt.throw L _
  | succ fuel ih =>
    intro s e he hf
    change WCh mctx cctx L mb ctx
      (translateStepWith (translateFallback tenv) (translateFuelFix (translateStep tenv) fuel)) _
    cases e with
    | boolInput j => exact hbS j he (fuel + 1)
    | bitsInput w j =>
      obtain ⟨hj, hw, hpos⟩ := he
      cases hw
      exact hvS j hj (fuel + 1)
    | bitsLit w v =>
      obtain ⟨hval, hpos⟩ := he
      exact bitsLit_still L hval
    | binary op a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      simp only [wfrag, Bool.and_eq_true] at hf
      have ck := op_checks op dom (quote dom bE vE a) (quote dom bE vE b) w
      have ca : WSt mctx cctx L mb ctx
          ((translateFuelFix (translateStep tenv) fuel)
            ((binE dom w op (quote dom bE vE a)
              (quote dom bE vE b)).getAppArgs[(binE dom w op (quote dom bE vE a)
              (quote dom bE vE b)).getAppArgs.size - 2]!) "op_a" false false) := by
        rw [ck.2.2.2.2.1]
        exact ih a ha hf.1 _ _ _
      have cb : WSt mctx cctx L mb ctx
          ((translateFuelFix (translateStep tenv) fuel)
            ((binE dom w op (quote dom bE vE a)
              (quote dom bE vE b)).getAppArgs[(binE dom w op (quote dom bE vE a)
              (quote dom bE vE b)).getAppArgs.size - 1]!) "op_b" false false) := by
        rw [ck.2.2.2.2.2.1]
        exact ih b hb' hf.2 _ _ _
      intro hint top named
      exact step_of_core L
        (core_binary L ck.1 ck.2.1 ck.2.2.2.2.2.2 ck.2.2.1 ck.2.2.2.1 ca cb)
    | compare op a b =>
      obtain ⟨ha, hb'⟩ := he
      simp only [wfrag, Bool.and_eq_true] at hf
      exact compare_still L (ih a ha hf.1) (ih b hb' hf.2)
    | boolBinary op a b =>
      obtain ⟨ha, hb'⟩ := he
      simp only [wfrag, Bool.and_eq_true] at hf
      exact boolBin_still L (ih a ha hf.1) (ih b hb' hf.2)
    | boolEq a b =>
      obtain ⟨ha, hb'⟩ := he
      simp only [wfrag, Bool.and_eq_true] at hf
      exact boolEq_still L (ih a ha hf.1) (ih b hb' hf.2)
    | mux c a b =>
      obtain ⟨hc, ha, hb'⟩ := he
      simp only [wfrag, Bool.and_eq_true] at hf
      cases s with
      | bool => exact boolMux_still L (ih c hc hf.1.1) (ih a ha hf.1.2) (ih b hb' hf.2)
      | bits w => exact vector_still L (ih c hc hf.1.1) (ih a ha hf.1.2) (ih b hb' hf.2)
    | setw w' a =>
      obtain ⟨ha, hpos⟩ := he
      simp only [wfrag] at hf
      exact setw_still L (a.wf_pos ha) hpos (ih a ha hf)
    | concat a b =>
      obtain ⟨ha, hb'⟩ := he
      simp only [wfrag, Bool.and_eq_true] at hf
      exact concat_still L (a.wf_pos ha) (b.wf_pos hb') (ih a ha hf.1) (ih b hb' hf.2)
    | _ => simp [wfrag] at hf

/-- An input binder bound in the context is still at every fuel. -/
theorem input_fuel {id : FVarId} (hb : WBound ctx id) :
    ∀ fuel, WCh mctx cctx L mb ctx (translateFuelFix (translateStep tenv) fuel) (.fvar id)
  | 0 => by
    intro hint top named
    unfold translateFuelFix
    exact WSt.throw L _
  | fuel + 1 => by
    change WCh mctx cctx L mb ctx
      (translateStepWith (translateFallback tenv) (translateFuelFix (translateStep tenv) fuel)) _
    exact input_still L hb

/-- **The certified walk leaves the child cache.** For a well-formed term of
the fragment whose input binders are bound in the context: a returning run
of the shipping translator on its quotation, from a world satisfying the
cache invariant, ends in one with the SAME cache value. -/
theorem walk_still {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat} {bi vi : Nat → FVarId}
    (hb : ∀ j, j < kb → WBound ctx (bi j)) (hv : ∀ j, j < kv → WBound ctx (vi j))
    {s : SType} (e : Term s) (he : e.WF kb kv vw) (hf : wfrag e = true) :
    WCh mctx cctx L mb ctx (fun e hint top named => translateExprToWire tenv e hint top named)
      (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) e) :=
  fuel_still L translateFuelLimit (fun j hj => input_fuel L (hb j hj))
    (fun j hj => input_fuel L (hv j hj)) e he hf

end Tools.ShippingWalkStill
